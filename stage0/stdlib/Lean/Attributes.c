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
lean_object* v___x_699_; uint8_t v___y_710_; lean_object* v___x_716_; uint8_t v___x_717_; 
lean_inc(v_stx_695_);
v___x_699_ = l_Lean_Syntax_getKind(v_stx_695_);
v___x_716_ = ((lean_object*)(l_Lean_Attribute_Builtin_ensureNoArgs___closed__6));
v___x_717_ = lean_name_eq(v___x_699_, v___x_716_);
if (v___x_717_ == 0)
{
v___y_710_ = v___x_717_;
goto v___jp_709_;
}
else
{
lean_object* v___x_718_; lean_object* v___x_719_; uint8_t v___x_720_; 
v___x_718_ = lean_unsigned_to_nat(1u);
v___x_719_ = l_Lean_Syntax_getArg(v_stx_695_, v___x_718_);
v___x_720_ = l_Lean_Syntax_isNone(v___x_719_);
lean_dec(v___x_719_);
v___y_710_ = v___x_720_;
goto v___jp_709_;
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
v___jp_709_:
{
if (v___y_710_ == 0)
{
goto v___jp_700_;
}
else
{
lean_object* v___x_711_; lean_object* v___x_712_; uint8_t v___x_713_; 
v___x_711_ = lean_unsigned_to_nat(2u);
v___x_712_ = l_Lean_Syntax_getArg(v_stx_695_, v___x_711_);
v___x_713_ = l_Lean_Syntax_isNone(v___x_712_);
lean_dec(v___x_712_);
if (v___x_713_ == 0)
{
goto v___jp_700_;
}
else
{
lean_object* v___x_714_; lean_object* v___x_715_; 
lean_dec(v___x_699_);
lean_dec(v_stx_695_);
v___x_714_ = lean_box(0);
v___x_715_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_715_, 0, v___x_714_);
return v___x_715_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_ensureNoArgs___boxed(lean_object* v_stx_721_, lean_object* v_a_722_, lean_object* v_a_723_, lean_object* v_a_724_){
_start:
{
lean_object* v_res_725_; 
v_res_725_ = l_Lean_Attribute_Builtin_ensureNoArgs(v_stx_721_, v_a_722_, v_a_723_);
lean_dec(v_a_723_);
lean_dec_ref(v_a_722_);
return v_res_725_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0(lean_object* v_00_u03b1_726_, lean_object* v_ref_727_, lean_object* v_msg_728_, lean_object* v___y_729_, lean_object* v___y_730_){
_start:
{
lean_object* v___x_732_; 
v___x_732_ = l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg(v_ref_727_, v_msg_728_, v___y_729_, v___y_730_);
return v___x_732_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___boxed(lean_object* v_00_u03b1_733_, lean_object* v_ref_734_, lean_object* v_msg_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_){
_start:
{
lean_object* v_res_739_; 
v_res_739_ = l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0(v_00_u03b1_733_, v_ref_734_, v_msg_735_, v___y_736_, v___y_737_);
lean_dec(v___y_737_);
lean_dec_ref(v___y_736_);
lean_dec(v_ref_734_);
return v_res_739_;
}
}
static lean_object* _init_l_Lean_Attribute_Builtin_getIdent_x3f___closed__5(void){
_start:
{
lean_object* v___x_753_; lean_object* v___x_754_; 
v___x_753_ = ((lean_object*)(l_Lean_Attribute_Builtin_getIdent_x3f___closed__4));
v___x_754_ = l_Lean_stringToMessageData(v___x_753_);
return v___x_754_;
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getIdent_x3f(lean_object* v_stx_755_, lean_object* v_a_756_, lean_object* v_a_757_){
_start:
{
lean_object* v___x_767_; lean_object* v___x_768_; uint8_t v___x_769_; 
lean_inc(v_stx_755_);
v___x_767_ = l_Lean_Syntax_getKind(v_stx_755_);
v___x_768_ = ((lean_object*)(l_Lean_Attribute_Builtin_ensureNoArgs___closed__6));
v___x_769_ = lean_name_eq(v___x_767_, v___x_768_);
if (v___x_769_ == 0)
{
lean_object* v___x_770_; uint8_t v___x_771_; 
v___x_770_ = ((lean_object*)(l_Lean_Attribute_Builtin_getIdent_x3f___closed__1));
v___x_771_ = lean_name_eq(v___x_767_, v___x_770_);
if (v___x_771_ == 0)
{
lean_object* v___x_772_; uint8_t v___x_773_; 
v___x_772_ = ((lean_object*)(l_Lean_Attribute_Builtin_getIdent_x3f___closed__3));
v___x_773_ = lean_name_eq(v___x_767_, v___x_772_);
lean_dec(v___x_767_);
if (v___x_773_ == 0)
{
lean_object* v___x_774_; lean_object* v___x_775_; 
v___x_774_ = lean_obj_once(&l_Lean_Attribute_Builtin_getIdent_x3f___closed__5, &l_Lean_Attribute_Builtin_getIdent_x3f___closed__5_once, _init_l_Lean_Attribute_Builtin_getIdent_x3f___closed__5);
v___x_775_ = l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg(v_stx_755_, v___x_774_, v_a_756_, v_a_757_);
lean_dec(v_stx_755_);
return v___x_775_;
}
else
{
goto v___jp_759_;
}
}
else
{
lean_dec(v___x_767_);
goto v___jp_759_;
}
}
else
{
lean_object* v___x_776_; lean_object* v___x_777_; uint8_t v___x_778_; 
lean_dec(v___x_767_);
v___x_776_ = lean_unsigned_to_nat(1u);
v___x_777_ = l_Lean_Syntax_getArg(v_stx_755_, v___x_776_);
lean_dec(v_stx_755_);
v___x_778_ = l_Lean_Syntax_isNone(v___x_777_);
if (v___x_778_ == 0)
{
if (v___x_769_ == 0)
{
lean_dec(v___x_777_);
goto v___jp_764_;
}
else
{
lean_object* v___x_779_; lean_object* v___x_780_; uint8_t v___x_781_; 
v___x_779_ = lean_unsigned_to_nat(0u);
v___x_780_ = l_Lean_Syntax_getArg(v___x_777_, v___x_779_);
lean_dec(v___x_777_);
v___x_781_ = l_Lean_Syntax_isIdent(v___x_780_);
if (v___x_781_ == 0)
{
lean_dec(v___x_780_);
goto v___jp_764_;
}
else
{
lean_object* v___x_782_; lean_object* v___x_783_; 
v___x_782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_782_, 0, v___x_780_);
v___x_783_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_783_, 0, v___x_782_);
return v___x_783_;
}
}
}
else
{
lean_dec(v___x_777_);
goto v___jp_764_;
}
}
v___jp_759_:
{
lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; 
v___x_760_ = lean_unsigned_to_nat(1u);
v___x_761_ = l_Lean_Syntax_getArg(v_stx_755_, v___x_760_);
lean_dec(v_stx_755_);
v___x_762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_762_, 0, v___x_761_);
v___x_763_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_763_, 0, v___x_762_);
return v___x_763_;
}
v___jp_764_:
{
lean_object* v___x_765_; lean_object* v___x_766_; 
v___x_765_ = lean_box(0);
v___x_766_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_766_, 0, v___x_765_);
return v___x_766_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getIdent_x3f___boxed(lean_object* v_stx_784_, lean_object* v_a_785_, lean_object* v_a_786_, lean_object* v_a_787_){
_start:
{
lean_object* v_res_788_; 
v_res_788_ = l_Lean_Attribute_Builtin_getIdent_x3f(v_stx_784_, v_a_785_, v_a_786_);
lean_dec(v_a_786_);
lean_dec_ref(v_a_785_);
return v_res_788_;
}
}
static lean_object* _init_l_Lean_Attribute_Builtin_getIdent___closed__1(void){
_start:
{
lean_object* v___x_790_; lean_object* v___x_791_; 
v___x_790_ = ((lean_object*)(l_Lean_Attribute_Builtin_getIdent___closed__0));
v___x_791_ = l_Lean_stringToMessageData(v___x_790_);
return v___x_791_;
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getIdent(lean_object* v_stx_792_, lean_object* v_a_793_, lean_object* v_a_794_){
_start:
{
lean_object* v___x_796_; 
lean_inc(v_stx_792_);
v___x_796_ = l_Lean_Attribute_Builtin_getIdent_x3f(v_stx_792_, v_a_793_, v_a_794_);
if (lean_obj_tag(v___x_796_) == 0)
{
lean_object* v_a_797_; lean_object* v___x_799_; uint8_t v_isShared_800_; uint8_t v_isSharedCheck_810_; 
v_a_797_ = lean_ctor_get(v___x_796_, 0);
v_isSharedCheck_810_ = !lean_is_exclusive(v___x_796_);
if (v_isSharedCheck_810_ == 0)
{
v___x_799_ = v___x_796_;
v_isShared_800_ = v_isSharedCheck_810_;
goto v_resetjp_798_;
}
else
{
lean_inc(v_a_797_);
lean_dec(v___x_796_);
v___x_799_ = lean_box(0);
v_isShared_800_ = v_isSharedCheck_810_;
goto v_resetjp_798_;
}
v_resetjp_798_:
{
if (lean_obj_tag(v_a_797_) == 0)
{
lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; 
lean_del_object(v___x_799_);
v___x_801_ = lean_obj_once(&l_Lean_Attribute_Builtin_getIdent___closed__1, &l_Lean_Attribute_Builtin_getIdent___closed__1_once, _init_l_Lean_Attribute_Builtin_getIdent___closed__1);
lean_inc(v_stx_792_);
v___x_802_ = l_Lean_MessageData_ofSyntax(v_stx_792_);
v___x_803_ = l_Lean_indentD(v___x_802_);
v___x_804_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_804_, 0, v___x_801_);
lean_ctor_set(v___x_804_, 1, v___x_803_);
v___x_805_ = l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg(v_stx_792_, v___x_804_, v_a_793_, v_a_794_);
lean_dec(v_stx_792_);
return v___x_805_;
}
else
{
lean_object* v_val_806_; lean_object* v___x_808_; 
lean_dec(v_stx_792_);
v_val_806_ = lean_ctor_get(v_a_797_, 0);
lean_inc(v_val_806_);
lean_dec_ref_known(v_a_797_, 1);
if (v_isShared_800_ == 0)
{
lean_ctor_set(v___x_799_, 0, v_val_806_);
v___x_808_ = v___x_799_;
goto v_reusejp_807_;
}
else
{
lean_object* v_reuseFailAlloc_809_; 
v_reuseFailAlloc_809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_809_, 0, v_val_806_);
v___x_808_ = v_reuseFailAlloc_809_;
goto v_reusejp_807_;
}
v_reusejp_807_:
{
return v___x_808_;
}
}
}
}
else
{
lean_object* v_a_811_; lean_object* v___x_813_; uint8_t v_isShared_814_; uint8_t v_isSharedCheck_818_; 
lean_dec(v_stx_792_);
v_a_811_ = lean_ctor_get(v___x_796_, 0);
v_isSharedCheck_818_ = !lean_is_exclusive(v___x_796_);
if (v_isSharedCheck_818_ == 0)
{
v___x_813_ = v___x_796_;
v_isShared_814_ = v_isSharedCheck_818_;
goto v_resetjp_812_;
}
else
{
lean_inc(v_a_811_);
lean_dec(v___x_796_);
v___x_813_ = lean_box(0);
v_isShared_814_ = v_isSharedCheck_818_;
goto v_resetjp_812_;
}
v_resetjp_812_:
{
lean_object* v___x_816_; 
if (v_isShared_814_ == 0)
{
v___x_816_ = v___x_813_;
goto v_reusejp_815_;
}
else
{
lean_object* v_reuseFailAlloc_817_; 
v_reuseFailAlloc_817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_817_, 0, v_a_811_);
v___x_816_ = v_reuseFailAlloc_817_;
goto v_reusejp_815_;
}
v_reusejp_815_:
{
return v___x_816_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getIdent___boxed(lean_object* v_stx_819_, lean_object* v_a_820_, lean_object* v_a_821_, lean_object* v_a_822_){
_start:
{
lean_object* v_res_823_; 
v_res_823_ = l_Lean_Attribute_Builtin_getIdent(v_stx_819_, v_a_820_, v_a_821_);
lean_dec(v_a_821_);
lean_dec_ref(v_a_820_);
return v_res_823_;
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getId_x3f(lean_object* v_stx_824_, lean_object* v_a_825_, lean_object* v_a_826_){
_start:
{
lean_object* v___x_828_; 
v___x_828_ = l_Lean_Attribute_Builtin_getIdent_x3f(v_stx_824_, v_a_825_, v_a_826_);
if (lean_obj_tag(v___x_828_) == 0)
{
lean_object* v_a_829_; lean_object* v___x_831_; uint8_t v_isShared_832_; uint8_t v_isSharedCheck_849_; 
v_a_829_ = lean_ctor_get(v___x_828_, 0);
v_isSharedCheck_849_ = !lean_is_exclusive(v___x_828_);
if (v_isSharedCheck_849_ == 0)
{
v___x_831_ = v___x_828_;
v_isShared_832_ = v_isSharedCheck_849_;
goto v_resetjp_830_;
}
else
{
lean_inc(v_a_829_);
lean_dec(v___x_828_);
v___x_831_ = lean_box(0);
v_isShared_832_ = v_isSharedCheck_849_;
goto v_resetjp_830_;
}
v_resetjp_830_:
{
if (lean_obj_tag(v_a_829_) == 0)
{
lean_object* v___x_833_; lean_object* v___x_835_; 
v___x_833_ = lean_box(0);
if (v_isShared_832_ == 0)
{
lean_ctor_set(v___x_831_, 0, v___x_833_);
v___x_835_ = v___x_831_;
goto v_reusejp_834_;
}
else
{
lean_object* v_reuseFailAlloc_836_; 
v_reuseFailAlloc_836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_836_, 0, v___x_833_);
v___x_835_ = v_reuseFailAlloc_836_;
goto v_reusejp_834_;
}
v_reusejp_834_:
{
return v___x_835_;
}
}
else
{
lean_object* v_val_837_; lean_object* v___x_839_; uint8_t v_isShared_840_; uint8_t v_isSharedCheck_848_; 
v_val_837_ = lean_ctor_get(v_a_829_, 0);
v_isSharedCheck_848_ = !lean_is_exclusive(v_a_829_);
if (v_isSharedCheck_848_ == 0)
{
v___x_839_ = v_a_829_;
v_isShared_840_ = v_isSharedCheck_848_;
goto v_resetjp_838_;
}
else
{
lean_inc(v_val_837_);
lean_dec(v_a_829_);
v___x_839_ = lean_box(0);
v_isShared_840_ = v_isSharedCheck_848_;
goto v_resetjp_838_;
}
v_resetjp_838_:
{
lean_object* v___x_841_; lean_object* v___x_843_; 
v___x_841_ = l_Lean_Syntax_getId(v_val_837_);
lean_dec(v_val_837_);
if (v_isShared_840_ == 0)
{
lean_ctor_set(v___x_839_, 0, v___x_841_);
v___x_843_ = v___x_839_;
goto v_reusejp_842_;
}
else
{
lean_object* v_reuseFailAlloc_847_; 
v_reuseFailAlloc_847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_847_, 0, v___x_841_);
v___x_843_ = v_reuseFailAlloc_847_;
goto v_reusejp_842_;
}
v_reusejp_842_:
{
lean_object* v___x_845_; 
if (v_isShared_832_ == 0)
{
lean_ctor_set(v___x_831_, 0, v___x_843_);
v___x_845_ = v___x_831_;
goto v_reusejp_844_;
}
else
{
lean_object* v_reuseFailAlloc_846_; 
v_reuseFailAlloc_846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_846_, 0, v___x_843_);
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
}
else
{
lean_object* v_a_850_; lean_object* v___x_852_; uint8_t v_isShared_853_; uint8_t v_isSharedCheck_857_; 
v_a_850_ = lean_ctor_get(v___x_828_, 0);
v_isSharedCheck_857_ = !lean_is_exclusive(v___x_828_);
if (v_isSharedCheck_857_ == 0)
{
v___x_852_ = v___x_828_;
v_isShared_853_ = v_isSharedCheck_857_;
goto v_resetjp_851_;
}
else
{
lean_inc(v_a_850_);
lean_dec(v___x_828_);
v___x_852_ = lean_box(0);
v_isShared_853_ = v_isSharedCheck_857_;
goto v_resetjp_851_;
}
v_resetjp_851_:
{
lean_object* v___x_855_; 
if (v_isShared_853_ == 0)
{
v___x_855_ = v___x_852_;
goto v_reusejp_854_;
}
else
{
lean_object* v_reuseFailAlloc_856_; 
v_reuseFailAlloc_856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_856_, 0, v_a_850_);
v___x_855_ = v_reuseFailAlloc_856_;
goto v_reusejp_854_;
}
v_reusejp_854_:
{
return v___x_855_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getId_x3f___boxed(lean_object* v_stx_858_, lean_object* v_a_859_, lean_object* v_a_860_, lean_object* v_a_861_){
_start:
{
lean_object* v_res_862_; 
v_res_862_ = l_Lean_Attribute_Builtin_getId_x3f(v_stx_858_, v_a_859_, v_a_860_);
lean_dec(v_a_860_);
lean_dec_ref(v_a_859_);
return v_res_862_;
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getId(lean_object* v_stx_863_, lean_object* v_a_864_, lean_object* v_a_865_){
_start:
{
lean_object* v___x_867_; 
v___x_867_ = l_Lean_Attribute_Builtin_getIdent(v_stx_863_, v_a_864_, v_a_865_);
if (lean_obj_tag(v___x_867_) == 0)
{
lean_object* v_a_868_; lean_object* v___x_870_; uint8_t v_isShared_871_; uint8_t v_isSharedCheck_876_; 
v_a_868_ = lean_ctor_get(v___x_867_, 0);
v_isSharedCheck_876_ = !lean_is_exclusive(v___x_867_);
if (v_isSharedCheck_876_ == 0)
{
v___x_870_ = v___x_867_;
v_isShared_871_ = v_isSharedCheck_876_;
goto v_resetjp_869_;
}
else
{
lean_inc(v_a_868_);
lean_dec(v___x_867_);
v___x_870_ = lean_box(0);
v_isShared_871_ = v_isSharedCheck_876_;
goto v_resetjp_869_;
}
v_resetjp_869_:
{
lean_object* v___x_872_; lean_object* v___x_874_; 
v___x_872_ = l_Lean_Syntax_getId(v_a_868_);
lean_dec(v_a_868_);
if (v_isShared_871_ == 0)
{
lean_ctor_set(v___x_870_, 0, v___x_872_);
v___x_874_ = v___x_870_;
goto v_reusejp_873_;
}
else
{
lean_object* v_reuseFailAlloc_875_; 
v_reuseFailAlloc_875_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_875_, 0, v___x_872_);
v___x_874_ = v_reuseFailAlloc_875_;
goto v_reusejp_873_;
}
v_reusejp_873_:
{
return v___x_874_;
}
}
}
else
{
lean_object* v_a_877_; lean_object* v___x_879_; uint8_t v_isShared_880_; uint8_t v_isSharedCheck_884_; 
v_a_877_ = lean_ctor_get(v___x_867_, 0);
v_isSharedCheck_884_ = !lean_is_exclusive(v___x_867_);
if (v_isSharedCheck_884_ == 0)
{
v___x_879_ = v___x_867_;
v_isShared_880_ = v_isSharedCheck_884_;
goto v_resetjp_878_;
}
else
{
lean_inc(v_a_877_);
lean_dec(v___x_867_);
v___x_879_ = lean_box(0);
v_isShared_880_ = v_isSharedCheck_884_;
goto v_resetjp_878_;
}
v_resetjp_878_:
{
lean_object* v___x_882_; 
if (v_isShared_880_ == 0)
{
v___x_882_ = v___x_879_;
goto v_reusejp_881_;
}
else
{
lean_object* v_reuseFailAlloc_883_; 
v_reuseFailAlloc_883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_883_, 0, v_a_877_);
v___x_882_ = v_reuseFailAlloc_883_;
goto v_reusejp_881_;
}
v_reusejp_881_:
{
return v___x_882_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getId___boxed(lean_object* v_stx_885_, lean_object* v_a_886_, lean_object* v_a_887_, lean_object* v_a_888_){
_start:
{
lean_object* v_res_889_; 
v_res_889_ = l_Lean_Attribute_Builtin_getId(v_stx_885_, v_a_886_, v_a_887_);
lean_dec(v_a_887_);
lean_dec_ref(v_a_886_);
return v_res_889_;
}
}
static lean_object* _init_l_Lean_getAttrParamOptPrio___closed__1(void){
_start:
{
lean_object* v___x_891_; lean_object* v___x_892_; 
v___x_891_ = ((lean_object*)(l_Lean_getAttrParamOptPrio___closed__0));
v___x_892_ = l_Lean_stringToMessageData(v___x_891_);
return v___x_892_;
}
}
LEAN_EXPORT lean_object* l_Lean_getAttrParamOptPrio(lean_object* v_optPrioStx_893_, lean_object* v_a_894_, lean_object* v_a_895_){
_start:
{
uint8_t v___x_897_; 
v___x_897_ = l_Lean_Syntax_isNone(v_optPrioStx_893_);
if (v___x_897_ == 0)
{
lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; 
v___x_898_ = lean_unsigned_to_nat(0u);
v___x_899_ = l_Lean_Syntax_getArg(v_optPrioStx_893_, v___x_898_);
v___x_900_ = l_Lean_Syntax_isNatLit_x3f(v___x_899_);
lean_dec(v___x_899_);
if (lean_obj_tag(v___x_900_) == 0)
{
lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; 
v___x_901_ = lean_obj_once(&l_Lean_getAttrParamOptPrio___closed__1, &l_Lean_getAttrParamOptPrio___closed__1_once, _init_l_Lean_getAttrParamOptPrio___closed__1);
lean_inc(v_optPrioStx_893_);
v___x_902_ = l_Lean_MessageData_ofSyntax(v_optPrioStx_893_);
v___x_903_ = l_Lean_indentD(v___x_902_);
v___x_904_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_904_, 0, v___x_901_);
lean_ctor_set(v___x_904_, 1, v___x_903_);
v___x_905_ = l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg(v_optPrioStx_893_, v___x_904_, v_a_894_, v_a_895_);
lean_dec(v_optPrioStx_893_);
return v___x_905_;
}
else
{
lean_object* v_val_906_; lean_object* v___x_908_; uint8_t v_isShared_909_; uint8_t v_isSharedCheck_913_; 
lean_dec(v_optPrioStx_893_);
v_val_906_ = lean_ctor_get(v___x_900_, 0);
v_isSharedCheck_913_ = !lean_is_exclusive(v___x_900_);
if (v_isSharedCheck_913_ == 0)
{
v___x_908_ = v___x_900_;
v_isShared_909_ = v_isSharedCheck_913_;
goto v_resetjp_907_;
}
else
{
lean_inc(v_val_906_);
lean_dec(v___x_900_);
v___x_908_ = lean_box(0);
v_isShared_909_ = v_isSharedCheck_913_;
goto v_resetjp_907_;
}
v_resetjp_907_:
{
lean_object* v___x_911_; 
if (v_isShared_909_ == 0)
{
lean_ctor_set_tag(v___x_908_, 0);
v___x_911_ = v___x_908_;
goto v_reusejp_910_;
}
else
{
lean_object* v_reuseFailAlloc_912_; 
v_reuseFailAlloc_912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_912_, 0, v_val_906_);
v___x_911_ = v_reuseFailAlloc_912_;
goto v_reusejp_910_;
}
v_reusejp_910_:
{
return v___x_911_;
}
}
}
}
else
{
lean_object* v___x_914_; lean_object* v___x_915_; 
lean_dec(v_optPrioStx_893_);
v___x_914_ = lean_unsigned_to_nat(1000u);
v___x_915_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_915_, 0, v___x_914_);
return v___x_915_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getAttrParamOptPrio___boxed(lean_object* v_optPrioStx_916_, lean_object* v_a_917_, lean_object* v_a_918_, lean_object* v_a_919_){
_start:
{
lean_object* v_res_920_; 
v_res_920_ = l_Lean_getAttrParamOptPrio(v_optPrioStx_916_, v_a_917_, v_a_918_);
lean_dec(v_a_918_);
lean_dec_ref(v_a_917_);
return v_res_920_;
}
}
static lean_object* _init_l_Lean_Attribute_Builtin_getPrio___closed__1(void){
_start:
{
lean_object* v___x_922_; lean_object* v___x_923_; 
v___x_922_ = ((lean_object*)(l_Lean_Attribute_Builtin_getPrio___closed__0));
v___x_923_ = l_Lean_stringToMessageData(v___x_922_);
return v___x_923_;
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getPrio(lean_object* v_stx_924_, lean_object* v_a_925_, lean_object* v_a_926_){
_start:
{
lean_object* v___x_928_; lean_object* v___x_929_; uint8_t v___x_930_; 
lean_inc(v_stx_924_);
v___x_928_ = l_Lean_Syntax_getKind(v_stx_924_);
v___x_929_ = ((lean_object*)(l_Lean_Attribute_Builtin_ensureNoArgs___closed__6));
v___x_930_ = lean_name_eq(v___x_928_, v___x_929_);
lean_dec(v___x_928_);
if (v___x_930_ == 0)
{
lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; 
v___x_931_ = lean_obj_once(&l_Lean_Attribute_Builtin_getPrio___closed__1, &l_Lean_Attribute_Builtin_getPrio___closed__1_once, _init_l_Lean_Attribute_Builtin_getPrio___closed__1);
lean_inc(v_stx_924_);
v___x_932_ = l_Lean_MessageData_ofSyntax(v_stx_924_);
v___x_933_ = l_Lean_indentD(v___x_932_);
v___x_934_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_934_, 0, v___x_931_);
lean_ctor_set(v___x_934_, 1, v___x_933_);
v___x_935_ = l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg(v_stx_924_, v___x_934_, v_a_925_, v_a_926_);
lean_dec(v_stx_924_);
return v___x_935_;
}
else
{
lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; 
v___x_936_ = lean_unsigned_to_nat(1u);
v___x_937_ = l_Lean_Syntax_getArg(v_stx_924_, v___x_936_);
lean_dec(v_stx_924_);
v___x_938_ = l_Lean_getAttrParamOptPrio(v___x_937_, v_a_925_, v_a_926_);
return v___x_938_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getPrio___boxed(lean_object* v_stx_939_, lean_object* v_a_940_, lean_object* v_a_941_, lean_object* v_a_942_){
_start:
{
lean_object* v_res_943_; 
v_res_943_ = l_Lean_Attribute_Builtin_getPrio(v_stx_939_, v_a_940_, v_a_941_);
lean_dec(v_a_941_);
lean_dec_ref(v_a_940_);
return v_res_943_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__1(void){
_start:
{
lean_object* v___x_945_; lean_object* v___x_946_; 
v___x_945_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__0));
v___x_946_ = l_Lean_stringToMessageData(v___x_945_);
return v___x_946_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__3(void){
_start:
{
lean_object* v___x_948_; lean_object* v___x_949_; 
v___x_948_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__2));
v___x_949_ = l_Lean_stringToMessageData(v___x_948_);
return v___x_949_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__5(void){
_start:
{
lean_object* v___x_951_; lean_object* v___x_952_; 
v___x_951_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__4));
v___x_952_ = l_Lean_stringToMessageData(v___x_951_);
return v___x_952_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___redArg(lean_object* v_inst_953_, lean_object* v_inst_954_, lean_object* v_name_955_, uint8_t v_kind_956_){
_start:
{
lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___y_963_; 
v___x_957_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__1, &l_Lean_throwAttrMustBeGlobal___redArg___closed__1_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__1);
v___x_958_ = l_Lean_MessageData_ofName(v_name_955_);
v___x_959_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_959_, 0, v___x_957_);
lean_ctor_set(v___x_959_, 1, v___x_958_);
v___x_960_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__3, &l_Lean_throwAttrMustBeGlobal___redArg___closed__3_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__3);
v___x_961_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_961_, 0, v___x_959_);
lean_ctor_set(v___x_961_, 1, v___x_960_);
switch(v_kind_956_)
{
case 0:
{
lean_object* v___x_970_; 
v___x_970_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__0));
v___y_963_ = v___x_970_;
goto v___jp_962_;
}
case 1:
{
lean_object* v___x_971_; 
v___x_971_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__1));
v___y_963_ = v___x_971_;
goto v___jp_962_;
}
default: 
{
lean_object* v___x_972_; 
v___x_972_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__2));
v___y_963_ = v___x_972_;
goto v___jp_962_;
}
}
v___jp_962_:
{
lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; 
lean_inc_ref(v___y_963_);
v___x_964_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_964_, 0, v___y_963_);
v___x_965_ = l_Lean_MessageData_ofFormat(v___x_964_);
v___x_966_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_966_, 0, v___x_961_);
lean_ctor_set(v___x_966_, 1, v___x_965_);
v___x_967_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__5, &l_Lean_throwAttrMustBeGlobal___redArg___closed__5_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__5);
v___x_968_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_968_, 0, v___x_966_);
lean_ctor_set(v___x_968_, 1, v___x_967_);
v___x_969_ = l_Lean_throwError___redArg(v_inst_953_, v_inst_954_, v___x_968_);
return v___x_969_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___redArg___boxed(lean_object* v_inst_973_, lean_object* v_inst_974_, lean_object* v_name_975_, lean_object* v_kind_976_){
_start:
{
uint8_t v_kind_boxed_977_; lean_object* v_res_978_; 
v_kind_boxed_977_ = lean_unbox(v_kind_976_);
v_res_978_ = l_Lean_throwAttrMustBeGlobal___redArg(v_inst_973_, v_inst_974_, v_name_975_, v_kind_boxed_977_);
return v_res_978_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal(lean_object* v_m_979_, lean_object* v_inst_980_, lean_object* v_inst_981_, lean_object* v_00_u03b1_982_, lean_object* v_name_983_, uint8_t v_kind_984_){
_start:
{
lean_object* v___x_985_; 
v___x_985_ = l_Lean_throwAttrMustBeGlobal___redArg(v_inst_980_, v_inst_981_, v_name_983_, v_kind_984_);
return v___x_985_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___boxed(lean_object* v_m_986_, lean_object* v_inst_987_, lean_object* v_inst_988_, lean_object* v_00_u03b1_989_, lean_object* v_name_990_, lean_object* v_kind_991_){
_start:
{
uint8_t v_kind_boxed_992_; lean_object* v_res_993_; 
v_kind_boxed_992_ = lean_unbox(v_kind_991_);
v_res_993_ = l_Lean_throwAttrMustBeGlobal(v_m_986_, v_inst_987_, v_inst_988_, v_00_u03b1_989_, v_name_990_, v_kind_boxed_992_);
return v_res_993_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1(void){
_start:
{
lean_object* v___x_995_; lean_object* v___x_996_; 
v___x_995_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___redArg___closed__0));
v___x_996_ = l_Lean_stringToMessageData(v___x_995_);
return v___x_996_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__3(void){
_start:
{
lean_object* v___x_998_; lean_object* v___x_999_; 
v___x_998_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___redArg___closed__2));
v___x_999_ = l_Lean_stringToMessageData(v___x_998_);
return v___x_999_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__5(void){
_start:
{
lean_object* v___x_1001_; lean_object* v___x_1002_; 
v___x_1001_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___redArg___closed__4));
v___x_1002_ = l_Lean_stringToMessageData(v___x_1001_);
return v___x_1002_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___redArg(lean_object* v_inst_1003_, lean_object* v_inst_1004_, lean_object* v_attrName_1005_, lean_object* v_declName_1006_){
_start:
{
lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; uint8_t v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; 
v___x_1007_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1);
v___x_1008_ = l_Lean_MessageData_ofName(v_attrName_1005_);
v___x_1009_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1009_, 0, v___x_1007_);
lean_ctor_set(v___x_1009_, 1, v___x_1008_);
v___x_1010_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__3, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__3_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__3);
v___x_1011_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1011_, 0, v___x_1009_);
lean_ctor_set(v___x_1011_, 1, v___x_1010_);
v___x_1012_ = 0;
v___x_1013_ = l_Lean_MessageData_ofConstName(v_declName_1006_, v___x_1012_);
v___x_1014_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1014_, 0, v___x_1011_);
lean_ctor_set(v___x_1014_, 1, v___x_1013_);
v___x_1015_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__5, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__5_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__5);
v___x_1016_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1016_, 0, v___x_1014_);
lean_ctor_set(v___x_1016_, 1, v___x_1015_);
v___x_1017_ = l_Lean_throwError___redArg(v_inst_1003_, v_inst_1004_, v___x_1016_);
return v___x_1017_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule(lean_object* v_m_1018_, lean_object* v_inst_1019_, lean_object* v_inst_1020_, lean_object* v_00_u03b1_1021_, lean_object* v_attrName_1022_, lean_object* v_declName_1023_){
_start:
{
lean_object* v___x_1024_; 
v___x_1024_ = l_Lean_throwAttrDeclInImportedModule___redArg(v_inst_1019_, v_inst_1020_, v_attrName_1022_, v_declName_1023_);
return v___x_1024_;
}
}
static lean_object* _init_l_Lean_throwAttrNotInAsyncCtx___redArg___closed__1(void){
_start:
{
lean_object* v___x_1026_; lean_object* v___x_1027_; 
v___x_1026_ = ((lean_object*)(l_Lean_throwAttrNotInAsyncCtx___redArg___closed__0));
v___x_1027_ = l_Lean_stringToMessageData(v___x_1026_);
return v___x_1027_;
}
}
static lean_object* _init_l_Lean_throwAttrNotInAsyncCtx___redArg___closed__3(void){
_start:
{
lean_object* v___x_1029_; lean_object* v___x_1030_; 
v___x_1029_ = ((lean_object*)(l_Lean_throwAttrNotInAsyncCtx___redArg___closed__2));
v___x_1030_ = l_Lean_stringToMessageData(v___x_1029_);
return v___x_1030_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___redArg(lean_object* v_inst_1031_, lean_object* v_inst_1032_, lean_object* v_attrName_1033_, lean_object* v_declName_1034_, lean_object* v_asyncPrefix_x3f_1035_){
_start:
{
lean_object* v___y_1037_; 
if (lean_obj_tag(v_asyncPrefix_x3f_1035_) == 0)
{
lean_object* v___x_1050_; 
v___x_1050_ = l_Lean_MessageData_nil;
v___y_1037_ = v___x_1050_;
goto v___jp_1036_;
}
else
{
lean_object* v_val_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; 
v_val_1051_ = lean_ctor_get(v_asyncPrefix_x3f_1035_, 0);
lean_inc(v_val_1051_);
lean_dec_ref_known(v_asyncPrefix_x3f_1035_, 1);
v___x_1052_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___redArg___closed__3, &l_Lean_throwAttrNotInAsyncCtx___redArg___closed__3_once, _init_l_Lean_throwAttrNotInAsyncCtx___redArg___closed__3);
v___x_1053_ = l_Lean_MessageData_ofName(v_val_1051_);
v___x_1054_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1054_, 0, v___x_1052_);
lean_ctor_set(v___x_1054_, 1, v___x_1053_);
v___x_1055_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__5, &l_Lean_throwAttrMustBeGlobal___redArg___closed__5_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__5);
v___x_1056_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1056_, 0, v___x_1054_);
lean_ctor_set(v___x_1056_, 1, v___x_1055_);
v___y_1037_ = v___x_1056_;
goto v___jp_1036_;
}
v___jp_1036_:
{
lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; uint8_t v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; 
v___x_1038_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1);
v___x_1039_ = l_Lean_MessageData_ofName(v_attrName_1033_);
v___x_1040_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1040_, 0, v___x_1038_);
lean_ctor_set(v___x_1040_, 1, v___x_1039_);
v___x_1041_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__3, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__3_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__3);
v___x_1042_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1042_, 0, v___x_1040_);
lean_ctor_set(v___x_1042_, 1, v___x_1041_);
v___x_1043_ = 0;
v___x_1044_ = l_Lean_MessageData_ofConstName(v_declName_1034_, v___x_1043_);
v___x_1045_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1045_, 0, v___x_1042_);
lean_ctor_set(v___x_1045_, 1, v___x_1044_);
v___x_1046_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___redArg___closed__1, &l_Lean_throwAttrNotInAsyncCtx___redArg___closed__1_once, _init_l_Lean_throwAttrNotInAsyncCtx___redArg___closed__1);
v___x_1047_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1047_, 0, v___x_1045_);
lean_ctor_set(v___x_1047_, 1, v___x_1046_);
v___x_1048_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1048_, 0, v___x_1047_);
lean_ctor_set(v___x_1048_, 1, v___y_1037_);
v___x_1049_ = l_Lean_throwError___redArg(v_inst_1031_, v_inst_1032_, v___x_1048_);
return v___x_1049_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx(lean_object* v_m_1057_, lean_object* v_inst_1058_, lean_object* v_inst_1059_, lean_object* v_00_u03b1_1060_, lean_object* v_attrName_1061_, lean_object* v_declName_1062_, lean_object* v_asyncPrefix_x3f_1063_){
_start:
{
lean_object* v___x_1064_; 
v___x_1064_ = l_Lean_throwAttrNotInAsyncCtx___redArg(v_inst_1058_, v_inst_1059_, v_attrName_1061_, v_declName_1062_, v_asyncPrefix_x3f_1063_);
return v___x_1064_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1(void){
_start:
{
lean_object* v___x_1066_; lean_object* v___x_1067_; 
v___x_1066_ = ((lean_object*)(l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__0));
v___x_1067_ = l_Lean_stringToMessageData(v___x_1066_);
return v___x_1067_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__3(void){
_start:
{
lean_object* v___x_1069_; lean_object* v___x_1070_; 
v___x_1069_ = ((lean_object*)(l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__2));
v___x_1070_ = l_Lean_stringToMessageData(v___x_1069_);
return v___x_1070_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__5(void){
_start:
{
lean_object* v___x_1072_; lean_object* v___x_1073_; 
v___x_1072_ = ((lean_object*)(l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__4));
v___x_1073_ = l_Lean_stringToMessageData(v___x_1072_);
return v___x_1073_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__7(void){
_start:
{
lean_object* v___x_1075_; lean_object* v___x_1076_; 
v___x_1075_ = ((lean_object*)(l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__6));
v___x_1076_ = l_Lean_stringToMessageData(v___x_1075_);
return v___x_1076_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclNotOfExpectedType___redArg(lean_object* v_inst_1077_, lean_object* v_inst_1078_, lean_object* v_attrName_1079_, lean_object* v_declName_1080_, lean_object* v_givenType_1081_, lean_object* v_expectedType_1082_){
_start:
{
lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; uint8_t v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; 
v___x_1083_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1);
v___x_1084_ = l_Lean_MessageData_ofName(v_attrName_1079_);
lean_inc_ref(v___x_1084_);
v___x_1085_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1085_, 0, v___x_1083_);
lean_ctor_set(v___x_1085_, 1, v___x_1084_);
v___x_1086_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1, &l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1);
v___x_1087_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1087_, 0, v___x_1085_);
lean_ctor_set(v___x_1087_, 1, v___x_1086_);
v___x_1088_ = 0;
v___x_1089_ = l_Lean_MessageData_ofConstName(v_declName_1080_, v___x_1088_);
v___x_1090_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1090_, 0, v___x_1087_);
lean_ctor_set(v___x_1090_, 1, v___x_1089_);
v___x_1091_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__3, &l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__3_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__3);
v___x_1092_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1092_, 0, v___x_1090_);
lean_ctor_set(v___x_1092_, 1, v___x_1091_);
v___x_1093_ = l_Lean_indentExpr(v_givenType_1081_);
v___x_1094_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1094_, 0, v___x_1092_);
lean_ctor_set(v___x_1094_, 1, v___x_1093_);
v___x_1095_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__5, &l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__5_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__5);
v___x_1096_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1096_, 0, v___x_1094_);
lean_ctor_set(v___x_1096_, 1, v___x_1095_);
v___x_1097_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1097_, 0, v___x_1096_);
lean_ctor_set(v___x_1097_, 1, v___x_1084_);
v___x_1098_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__7, &l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__7_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__7);
v___x_1099_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1099_, 0, v___x_1097_);
lean_ctor_set(v___x_1099_, 1, v___x_1098_);
v___x_1100_ = l_Lean_indentExpr(v_expectedType_1082_);
v___x_1101_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1101_, 0, v___x_1099_);
lean_ctor_set(v___x_1101_, 1, v___x_1100_);
v___x_1102_ = l_Lean_throwError___redArg(v_inst_1077_, v_inst_1078_, v___x_1101_);
return v___x_1102_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclNotOfExpectedType(lean_object* v_m_1103_, lean_object* v_inst_1104_, lean_object* v_inst_1105_, lean_object* v_00_u03b1_1106_, lean_object* v_attrName_1107_, lean_object* v_declName_1108_, lean_object* v_givenType_1109_, lean_object* v_expectedType_1110_){
_start:
{
lean_object* v___x_1111_; 
v___x_1111_ = l_Lean_throwAttrDeclNotOfExpectedType___redArg(v_inst_1104_, v_inst_1105_, v_attrName_1107_, v_declName_1108_, v_givenType_1109_, v_expectedType_1110_);
return v___x_1111_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1___redArg(lean_object* v_constName_1112_, uint8_t v_skipRealize_1113_, lean_object* v___y_1114_){
_start:
{
lean_object* v___x_1116_; lean_object* v_env_1117_; uint8_t v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; 
v___x_1116_ = lean_st_ref_get(v___y_1114_);
v_env_1117_ = lean_ctor_get(v___x_1116_, 0);
lean_inc_ref(v_env_1117_);
lean_dec(v___x_1116_);
v___x_1118_ = l_Lean_Environment_contains(v_env_1117_, v_constName_1112_, v_skipRealize_1113_);
v___x_1119_ = lean_box(v___x_1118_);
v___x_1120_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1120_, 0, v___x_1119_);
return v___x_1120_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1___redArg___boxed(lean_object* v_constName_1121_, lean_object* v_skipRealize_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_){
_start:
{
uint8_t v_skipRealize_boxed_1125_; lean_object* v_res_1126_; 
v_skipRealize_boxed_1125_ = lean_unbox(v_skipRealize_1122_);
v_res_1126_ = l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1___redArg(v_constName_1121_, v_skipRealize_boxed_1125_, v___y_1123_);
lean_dec(v___y_1123_);
return v_res_1126_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1(lean_object* v_constName_1127_, uint8_t v_skipRealize_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_){
_start:
{
lean_object* v___x_1132_; 
v___x_1132_ = l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1___redArg(v_constName_1127_, v_skipRealize_1128_, v___y_1130_);
return v___x_1132_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1___boxed(lean_object* v_constName_1133_, lean_object* v_skipRealize_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_){
_start:
{
uint8_t v_skipRealize_boxed_1138_; lean_object* v_res_1139_; 
v_skipRealize_boxed_1138_ = lean_unbox(v_skipRealize_1134_);
v_res_1139_ = l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1(v_constName_1133_, v_skipRealize_boxed_1138_, v___y_1135_, v___y_1136_);
lean_dec(v___y_1136_);
lean_dec_ref(v___y_1135_);
return v_res_1139_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___lam__0(lean_object* v___y_1140_, uint8_t v_isExporting_1141_, lean_object* v___x_1142_, lean_object* v_a_x3f_1143_){
_start:
{
lean_object* v___x_1145_; lean_object* v_env_1146_; lean_object* v_nextMacroScope_1147_; lean_object* v_ngen_1148_; lean_object* v_auxDeclNGen_1149_; lean_object* v_traceState_1150_; lean_object* v_recordedDeps_1151_; lean_object* v_messages_1152_; lean_object* v_infoState_1153_; lean_object* v_snapshotTasks_1154_; lean_object* v___x_1156_; uint8_t v_isShared_1157_; uint8_t v_isSharedCheck_1165_; 
v___x_1145_ = lean_st_ref_take(v___y_1140_);
v_env_1146_ = lean_ctor_get(v___x_1145_, 0);
v_nextMacroScope_1147_ = lean_ctor_get(v___x_1145_, 1);
v_ngen_1148_ = lean_ctor_get(v___x_1145_, 2);
v_auxDeclNGen_1149_ = lean_ctor_get(v___x_1145_, 3);
v_traceState_1150_ = lean_ctor_get(v___x_1145_, 4);
v_recordedDeps_1151_ = lean_ctor_get(v___x_1145_, 6);
v_messages_1152_ = lean_ctor_get(v___x_1145_, 7);
v_infoState_1153_ = lean_ctor_get(v___x_1145_, 8);
v_snapshotTasks_1154_ = lean_ctor_get(v___x_1145_, 9);
v_isSharedCheck_1165_ = !lean_is_exclusive(v___x_1145_);
if (v_isSharedCheck_1165_ == 0)
{
lean_object* v_unused_1166_; 
v_unused_1166_ = lean_ctor_get(v___x_1145_, 5);
lean_dec(v_unused_1166_);
v___x_1156_ = v___x_1145_;
v_isShared_1157_ = v_isSharedCheck_1165_;
goto v_resetjp_1155_;
}
else
{
lean_inc(v_snapshotTasks_1154_);
lean_inc(v_infoState_1153_);
lean_inc(v_messages_1152_);
lean_inc(v_recordedDeps_1151_);
lean_inc(v_traceState_1150_);
lean_inc(v_auxDeclNGen_1149_);
lean_inc(v_ngen_1148_);
lean_inc(v_nextMacroScope_1147_);
lean_inc(v_env_1146_);
lean_dec(v___x_1145_);
v___x_1156_ = lean_box(0);
v_isShared_1157_ = v_isSharedCheck_1165_;
goto v_resetjp_1155_;
}
v_resetjp_1155_:
{
lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1161_; 
v___x_1158_ = lean_box(0);
v___x_1159_ = l_Lean_Environment_setExporting(v_env_1146_, v_isExporting_1141_);
if (v_isShared_1157_ == 0)
{
lean_ctor_set(v___x_1156_, 5, v___x_1142_);
lean_ctor_set(v___x_1156_, 0, v___x_1159_);
v___x_1161_ = v___x_1156_;
goto v_reusejp_1160_;
}
else
{
lean_object* v_reuseFailAlloc_1164_; 
v_reuseFailAlloc_1164_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1164_, 0, v___x_1159_);
lean_ctor_set(v_reuseFailAlloc_1164_, 1, v_nextMacroScope_1147_);
lean_ctor_set(v_reuseFailAlloc_1164_, 2, v_ngen_1148_);
lean_ctor_set(v_reuseFailAlloc_1164_, 3, v_auxDeclNGen_1149_);
lean_ctor_set(v_reuseFailAlloc_1164_, 4, v_traceState_1150_);
lean_ctor_set(v_reuseFailAlloc_1164_, 5, v___x_1142_);
lean_ctor_set(v_reuseFailAlloc_1164_, 6, v_recordedDeps_1151_);
lean_ctor_set(v_reuseFailAlloc_1164_, 7, v_messages_1152_);
lean_ctor_set(v_reuseFailAlloc_1164_, 8, v_infoState_1153_);
lean_ctor_set(v_reuseFailAlloc_1164_, 9, v_snapshotTasks_1154_);
v___x_1161_ = v_reuseFailAlloc_1164_;
goto v_reusejp_1160_;
}
v_reusejp_1160_:
{
lean_object* v___x_1162_; lean_object* v___x_1163_; 
v___x_1162_ = lean_st_ref_put(v___y_1140_, v___x_1161_);
v___x_1163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1163_, 0, v___x_1158_);
return v___x_1163_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___lam__0___boxed(lean_object* v___y_1167_, lean_object* v_isExporting_1168_, lean_object* v___x_1169_, lean_object* v_a_x3f_1170_, lean_object* v___y_1171_){
_start:
{
uint8_t v_isExporting_boxed_1172_; lean_object* v_res_1173_; 
v_isExporting_boxed_1172_ = lean_unbox(v_isExporting_1168_);
v_res_1173_ = l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___lam__0(v___y_1167_, v_isExporting_boxed_1172_, v___x_1169_, v_a_x3f_1170_);
lean_dec(v_a_x3f_1170_);
lean_dec(v___y_1167_);
return v_res_1173_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_1174_; lean_object* v___x_1175_; 
v___x_1174_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__0);
v___x_1175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1175_, 0, v___x_1174_);
return v___x_1175_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_1176_; lean_object* v___x_1177_; 
v___x_1176_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__0, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__0);
v___x_1177_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1177_, 0, v___x_1176_);
lean_ctor_set(v___x_1177_, 1, v___x_1176_);
return v___x_1177_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg(lean_object* v_x_1178_, uint8_t v_isExporting_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_){
_start:
{
lean_object* v___x_1183_; lean_object* v_env_1184_; lean_object* v___x_1185_; uint8_t v_isModule_1186_; 
v___x_1183_ = lean_st_ref_get(v___y_1181_);
v_env_1184_ = lean_ctor_get(v___x_1183_, 0);
lean_inc_ref(v_env_1184_);
lean_dec(v___x_1183_);
v___x_1185_ = l_Lean_Environment_header(v_env_1184_);
v_isModule_1186_ = lean_ctor_get_uint8(v___x_1185_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_1185_);
if (v_isModule_1186_ == 0)
{
lean_object* v___x_1187_; 
lean_dec_ref(v_env_1184_);
lean_inc(v___y_1181_);
lean_inc_ref(v___y_1180_);
v___x_1187_ = lean_apply_3(v_x_1178_, v___y_1180_, v___y_1181_, lean_box(0));
return v___x_1187_;
}
else
{
uint8_t v_isExporting_1188_; 
v_isExporting_1188_ = lean_ctor_get_uint8(v_env_1184_, sizeof(void*)*13);
lean_dec_ref(v_env_1184_);
if (v_isExporting_1179_ == 0)
{
if (v_isExporting_1188_ == 0)
{
lean_object* v___x_1240_; 
lean_inc(v___y_1181_);
lean_inc_ref(v___y_1180_);
v___x_1240_ = lean_apply_3(v_x_1178_, v___y_1180_, v___y_1181_, lean_box(0));
return v___x_1240_;
}
else
{
goto v___jp_1189_;
}
}
else
{
if (v_isExporting_1188_ == 0)
{
goto v___jp_1189_;
}
else
{
lean_object* v___x_1241_; 
lean_inc(v___y_1181_);
lean_inc_ref(v___y_1180_);
v___x_1241_ = lean_apply_3(v_x_1178_, v___y_1180_, v___y_1181_, lean_box(0));
return v___x_1241_;
}
}
v___jp_1189_:
{
lean_object* v___x_1190_; lean_object* v_env_1191_; lean_object* v_nextMacroScope_1192_; lean_object* v_ngen_1193_; lean_object* v_auxDeclNGen_1194_; lean_object* v_traceState_1195_; lean_object* v_recordedDeps_1196_; lean_object* v_messages_1197_; lean_object* v_infoState_1198_; lean_object* v_snapshotTasks_1199_; lean_object* v___x_1201_; uint8_t v_isShared_1202_; uint8_t v_isSharedCheck_1238_; 
v___x_1190_ = lean_st_ref_take(v___y_1181_);
v_env_1191_ = lean_ctor_get(v___x_1190_, 0);
v_nextMacroScope_1192_ = lean_ctor_get(v___x_1190_, 1);
v_ngen_1193_ = lean_ctor_get(v___x_1190_, 2);
v_auxDeclNGen_1194_ = lean_ctor_get(v___x_1190_, 3);
v_traceState_1195_ = lean_ctor_get(v___x_1190_, 4);
v_recordedDeps_1196_ = lean_ctor_get(v___x_1190_, 6);
v_messages_1197_ = lean_ctor_get(v___x_1190_, 7);
v_infoState_1198_ = lean_ctor_get(v___x_1190_, 8);
v_snapshotTasks_1199_ = lean_ctor_get(v___x_1190_, 9);
v_isSharedCheck_1238_ = !lean_is_exclusive(v___x_1190_);
if (v_isSharedCheck_1238_ == 0)
{
lean_object* v_unused_1239_; 
v_unused_1239_ = lean_ctor_get(v___x_1190_, 5);
lean_dec(v_unused_1239_);
v___x_1201_ = v___x_1190_;
v_isShared_1202_ = v_isSharedCheck_1238_;
goto v_resetjp_1200_;
}
else
{
lean_inc(v_snapshotTasks_1199_);
lean_inc(v_infoState_1198_);
lean_inc(v_messages_1197_);
lean_inc(v_recordedDeps_1196_);
lean_inc(v_traceState_1195_);
lean_inc(v_auxDeclNGen_1194_);
lean_inc(v_ngen_1193_);
lean_inc(v_nextMacroScope_1192_);
lean_inc(v_env_1191_);
lean_dec(v___x_1190_);
v___x_1201_ = lean_box(0);
v_isShared_1202_ = v_isSharedCheck_1238_;
goto v_resetjp_1200_;
}
v_resetjp_1200_:
{
lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1206_; 
v___x_1203_ = l_Lean_Environment_setExporting(v_env_1191_, v_isExporting_1179_);
v___x_1204_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1);
if (v_isShared_1202_ == 0)
{
lean_ctor_set(v___x_1201_, 5, v___x_1204_);
lean_ctor_set(v___x_1201_, 0, v___x_1203_);
v___x_1206_ = v___x_1201_;
goto v_reusejp_1205_;
}
else
{
lean_object* v_reuseFailAlloc_1237_; 
v_reuseFailAlloc_1237_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1237_, 0, v___x_1203_);
lean_ctor_set(v_reuseFailAlloc_1237_, 1, v_nextMacroScope_1192_);
lean_ctor_set(v_reuseFailAlloc_1237_, 2, v_ngen_1193_);
lean_ctor_set(v_reuseFailAlloc_1237_, 3, v_auxDeclNGen_1194_);
lean_ctor_set(v_reuseFailAlloc_1237_, 4, v_traceState_1195_);
lean_ctor_set(v_reuseFailAlloc_1237_, 5, v___x_1204_);
lean_ctor_set(v_reuseFailAlloc_1237_, 6, v_recordedDeps_1196_);
lean_ctor_set(v_reuseFailAlloc_1237_, 7, v_messages_1197_);
lean_ctor_set(v_reuseFailAlloc_1237_, 8, v_infoState_1198_);
lean_ctor_set(v_reuseFailAlloc_1237_, 9, v_snapshotTasks_1199_);
v___x_1206_ = v_reuseFailAlloc_1237_;
goto v_reusejp_1205_;
}
v_reusejp_1205_:
{
lean_object* v___x_1207_; lean_object* v_r_1208_; 
v___x_1207_ = lean_st_ref_put(v___y_1181_, v___x_1206_);
lean_inc(v___y_1181_);
lean_inc_ref(v___y_1180_);
v_r_1208_ = lean_apply_3(v_x_1178_, v___y_1180_, v___y_1181_, lean_box(0));
if (lean_obj_tag(v_r_1208_) == 0)
{
lean_object* v_a_1209_; lean_object* v___x_1211_; uint8_t v_isShared_1212_; uint8_t v_isSharedCheck_1225_; 
v_a_1209_ = lean_ctor_get(v_r_1208_, 0);
v_isSharedCheck_1225_ = !lean_is_exclusive(v_r_1208_);
if (v_isSharedCheck_1225_ == 0)
{
v___x_1211_ = v_r_1208_;
v_isShared_1212_ = v_isSharedCheck_1225_;
goto v_resetjp_1210_;
}
else
{
lean_inc(v_a_1209_);
lean_dec(v_r_1208_);
v___x_1211_ = lean_box(0);
v_isShared_1212_ = v_isSharedCheck_1225_;
goto v_resetjp_1210_;
}
v_resetjp_1210_:
{
lean_object* v___x_1214_; 
lean_inc(v_a_1209_);
if (v_isShared_1212_ == 0)
{
lean_ctor_set_tag(v___x_1211_, 1);
v___x_1214_ = v___x_1211_;
goto v_reusejp_1213_;
}
else
{
lean_object* v_reuseFailAlloc_1224_; 
v_reuseFailAlloc_1224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1224_, 0, v_a_1209_);
v___x_1214_ = v_reuseFailAlloc_1224_;
goto v_reusejp_1213_;
}
v_reusejp_1213_:
{
lean_object* v___x_1215_; lean_object* v___x_1217_; uint8_t v_isShared_1218_; uint8_t v_isSharedCheck_1222_; 
v___x_1215_ = l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___lam__0(v___y_1181_, v_isExporting_1188_, v___x_1204_, v___x_1214_);
lean_dec_ref(v___x_1214_);
v_isSharedCheck_1222_ = !lean_is_exclusive(v___x_1215_);
if (v_isSharedCheck_1222_ == 0)
{
lean_object* v_unused_1223_; 
v_unused_1223_ = lean_ctor_get(v___x_1215_, 0);
lean_dec(v_unused_1223_);
v___x_1217_ = v___x_1215_;
v_isShared_1218_ = v_isSharedCheck_1222_;
goto v_resetjp_1216_;
}
else
{
lean_dec(v___x_1215_);
v___x_1217_ = lean_box(0);
v_isShared_1218_ = v_isSharedCheck_1222_;
goto v_resetjp_1216_;
}
v_resetjp_1216_:
{
lean_object* v___x_1220_; 
if (v_isShared_1218_ == 0)
{
lean_ctor_set(v___x_1217_, 0, v_a_1209_);
v___x_1220_ = v___x_1217_;
goto v_reusejp_1219_;
}
else
{
lean_object* v_reuseFailAlloc_1221_; 
v_reuseFailAlloc_1221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1221_, 0, v_a_1209_);
v___x_1220_ = v_reuseFailAlloc_1221_;
goto v_reusejp_1219_;
}
v_reusejp_1219_:
{
return v___x_1220_;
}
}
}
}
}
else
{
lean_object* v_a_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1230_; uint8_t v_isShared_1231_; uint8_t v_isSharedCheck_1235_; 
v_a_1226_ = lean_ctor_get(v_r_1208_, 0);
lean_inc(v_a_1226_);
lean_dec_ref_known(v_r_1208_, 1);
v___x_1227_ = lean_box(0);
v___x_1228_ = l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___lam__0(v___y_1181_, v_isExporting_1188_, v___x_1204_, v___x_1227_);
v_isSharedCheck_1235_ = !lean_is_exclusive(v___x_1228_);
if (v_isSharedCheck_1235_ == 0)
{
lean_object* v_unused_1236_; 
v_unused_1236_ = lean_ctor_get(v___x_1228_, 0);
lean_dec(v_unused_1236_);
v___x_1230_ = v___x_1228_;
v_isShared_1231_ = v_isSharedCheck_1235_;
goto v_resetjp_1229_;
}
else
{
lean_dec(v___x_1228_);
v___x_1230_ = lean_box(0);
v_isShared_1231_ = v_isSharedCheck_1235_;
goto v_resetjp_1229_;
}
v_resetjp_1229_:
{
lean_object* v___x_1233_; 
if (v_isShared_1231_ == 0)
{
lean_ctor_set_tag(v___x_1230_, 1);
lean_ctor_set(v___x_1230_, 0, v_a_1226_);
v___x_1233_ = v___x_1230_;
goto v_reusejp_1232_;
}
else
{
lean_object* v_reuseFailAlloc_1234_; 
v_reuseFailAlloc_1234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1234_, 0, v_a_1226_);
v___x_1233_ = v_reuseFailAlloc_1234_;
goto v_reusejp_1232_;
}
v_reusejp_1232_:
{
return v___x_1233_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___boxed(lean_object* v_x_1242_, lean_object* v_isExporting_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_){
_start:
{
uint8_t v_isExporting_boxed_1247_; lean_object* v_res_1248_; 
v_isExporting_boxed_1247_ = lean_unbox(v_isExporting_1243_);
v_res_1248_ = l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg(v_x_1242_, v_isExporting_boxed_1247_, v___y_1244_, v___y_1245_);
lean_dec(v___y_1245_);
lean_dec_ref(v___y_1244_);
return v_res_1248_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2(lean_object* v_00_u03b1_1249_, lean_object* v_x_1250_, uint8_t v_isExporting_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_){
_start:
{
lean_object* v___x_1255_; 
v___x_1255_ = l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg(v_x_1250_, v_isExporting_1251_, v___y_1252_, v___y_1253_);
return v___x_1255_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___boxed(lean_object* v_00_u03b1_1256_, lean_object* v_x_1257_, lean_object* v_isExporting_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_){
_start:
{
uint8_t v_isExporting_boxed_1262_; lean_object* v_res_1263_; 
v_isExporting_boxed_1262_ = lean_unbox(v_isExporting_1258_);
v_res_1263_ = l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2(v_00_u03b1_1256_, v_x_1257_, v_isExporting_boxed_1262_, v___y_1259_, v___y_1260_);
lean_dec(v___y_1260_);
lean_dec_ref(v___y_1259_);
return v_res_1263_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0_spec__3(lean_object* v_opts_1264_, lean_object* v_opt_1265_){
_start:
{
lean_object* v_name_1266_; lean_object* v_defValue_1267_; lean_object* v_map_1268_; lean_object* v___x_1269_; 
v_name_1266_ = lean_ctor_get(v_opt_1265_, 0);
v_defValue_1267_ = lean_ctor_get(v_opt_1265_, 1);
v_map_1268_ = lean_ctor_get(v_opts_1264_, 0);
v___x_1269_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1268_, v_name_1266_);
if (lean_obj_tag(v___x_1269_) == 0)
{
uint8_t v___x_1270_; 
v___x_1270_ = lean_unbox(v_defValue_1267_);
return v___x_1270_;
}
else
{
lean_object* v_val_1271_; 
v_val_1271_ = lean_ctor_get(v___x_1269_, 0);
lean_inc(v_val_1271_);
lean_dec_ref_known(v___x_1269_, 1);
if (lean_obj_tag(v_val_1271_) == 1)
{
uint8_t v_v_1272_; 
v_v_1272_ = lean_ctor_get_uint8(v_val_1271_, 0);
lean_dec_ref_known(v_val_1271_, 0);
return v_v_1272_;
}
else
{
uint8_t v___x_1273_; 
lean_dec(v_val_1271_);
v___x_1273_ = lean_unbox(v_defValue_1267_);
return v___x_1273_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0_spec__3___boxed(lean_object* v_opts_1274_, lean_object* v_opt_1275_){
_start:
{
uint8_t v_res_1276_; lean_object* v_r_1277_; 
v_res_1276_ = l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0_spec__3(v_opts_1274_, v_opt_1275_);
lean_dec_ref(v_opt_1275_);
lean_dec_ref(v_opts_1274_);
v_r_1277_ = lean_box(v_res_1276_);
return v_r_1277_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0(uint8_t v_suppressElabErrors_1285_, uint8_t v___y_1286_, lean_object* v_x_1287_){
_start:
{
if (lean_obj_tag(v_x_1287_) == 1)
{
lean_object* v_pre_1288_; 
v_pre_1288_ = lean_ctor_get(v_x_1287_, 0);
switch(lean_obj_tag(v_pre_1288_))
{
case 1:
{
lean_object* v_pre_1289_; 
v_pre_1289_ = lean_ctor_get(v_pre_1288_, 0);
switch(lean_obj_tag(v_pre_1289_))
{
case 0:
{
lean_object* v_str_1290_; lean_object* v_str_1291_; lean_object* v___x_1292_; uint8_t v___x_1293_; 
v_str_1290_ = lean_ctor_get(v_x_1287_, 1);
v_str_1291_ = lean_ctor_get(v_pre_1288_, 1);
v___x_1292_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__0));
v___x_1293_ = lean_string_dec_eq(v_str_1291_, v___x_1292_);
if (v___x_1293_ == 0)
{
lean_object* v___x_1294_; uint8_t v___x_1295_; 
v___x_1294_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__2));
v___x_1295_ = lean_string_dec_eq(v_str_1291_, v___x_1294_);
if (v___x_1295_ == 0)
{
return v___x_1295_;
}
else
{
lean_object* v___x_1296_; uint8_t v___x_1297_; 
v___x_1296_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__1));
v___x_1297_ = lean_string_dec_eq(v_str_1290_, v___x_1296_);
if (v___x_1297_ == 0)
{
return v___x_1297_;
}
else
{
return v_suppressElabErrors_1285_;
}
}
}
else
{
lean_object* v___x_1298_; uint8_t v___x_1299_; 
v___x_1298_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__2));
v___x_1299_ = lean_string_dec_eq(v_str_1290_, v___x_1298_);
if (v___x_1299_ == 0)
{
return v___x_1299_;
}
else
{
return v_suppressElabErrors_1285_;
}
}
}
case 1:
{
lean_object* v_pre_1300_; 
v_pre_1300_ = lean_ctor_get(v_pre_1289_, 0);
if (lean_obj_tag(v_pre_1300_) == 0)
{
lean_object* v_str_1301_; lean_object* v_str_1302_; lean_object* v_str_1303_; lean_object* v___x_1304_; uint8_t v___x_1305_; 
v_str_1301_ = lean_ctor_get(v_x_1287_, 1);
v_str_1302_ = lean_ctor_get(v_pre_1288_, 1);
v_str_1303_ = lean_ctor_get(v_pre_1289_, 1);
v___x_1304_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__3));
v___x_1305_ = lean_string_dec_eq(v_str_1303_, v___x_1304_);
if (v___x_1305_ == 0)
{
return v___x_1305_;
}
else
{
lean_object* v___x_1306_; uint8_t v___x_1307_; 
v___x_1306_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__4));
v___x_1307_ = lean_string_dec_eq(v_str_1302_, v___x_1306_);
if (v___x_1307_ == 0)
{
return v___x_1307_;
}
else
{
lean_object* v___x_1308_; uint8_t v___x_1309_; 
v___x_1308_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__5));
v___x_1309_ = lean_string_dec_eq(v_str_1301_, v___x_1308_);
if (v___x_1309_ == 0)
{
return v___x_1309_;
}
else
{
return v_suppressElabErrors_1285_;
}
}
}
}
else
{
return v___y_1286_;
}
}
default: 
{
return v___y_1286_;
}
}
}
case 0:
{
lean_object* v_str_1310_; lean_object* v___x_1311_; uint8_t v___x_1312_; 
v_str_1310_ = lean_ctor_get(v_x_1287_, 1);
v___x_1311_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__6));
v___x_1312_ = lean_string_dec_eq(v_str_1310_, v___x_1311_);
if (v___x_1312_ == 0)
{
return v___x_1312_;
}
else
{
return v_suppressElabErrors_1285_;
}
}
default: 
{
return v___y_1286_;
}
}
}
else
{
return v___y_1286_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___boxed(lean_object* v_suppressElabErrors_1313_, lean_object* v___y_1314_, lean_object* v_x_1315_){
_start:
{
uint8_t v_suppressElabErrors_boxed_1316_; uint8_t v___y_5082__boxed_1317_; uint8_t v_res_1318_; lean_object* v_r_1319_; 
v_suppressElabErrors_boxed_1316_ = lean_unbox(v_suppressElabErrors_1313_);
v___y_5082__boxed_1317_ = lean_unbox(v___y_1314_);
v_res_1318_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0(v_suppressElabErrors_boxed_1316_, v___y_5082__boxed_1317_, v_x_1315_);
lean_dec(v_x_1315_);
v_r_1319_ = lean_box(v_res_1318_);
return v_r_1319_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6(lean_object* v_ref_1320_, lean_object* v_msgData_1321_, uint8_t v_severity_1322_, uint8_t v_isSilent_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_){
_start:
{
uint8_t v___y_1328_; lean_object* v___y_1329_; lean_object* v___y_1330_; lean_object* v___y_1331_; lean_object* v___y_1332_; lean_object* v___y_1333_; uint8_t v___y_1334_; lean_object* v_toCold_1335_; lean_object* v___y_1336_; lean_object* v___y_1365_; lean_object* v___y_1366_; uint8_t v___y_1367_; uint8_t v___y_1368_; lean_object* v___y_1369_; uint8_t v___y_1370_; lean_object* v___y_1371_; lean_object* v___y_1372_; uint8_t v___y_1392_; lean_object* v___y_1393_; lean_object* v___y_1394_; uint8_t v___y_1395_; lean_object* v___y_1396_; uint8_t v___y_1397_; lean_object* v___y_1398_; uint8_t v___y_1402_; uint8_t v___y_1403_; uint8_t v___y_1404_; uint8_t v___x_1415_; uint8_t v___y_1417_; uint8_t v___y_1418_; uint8_t v___y_1419_; uint8_t v___y_1421_; uint8_t v___x_1429_; 
v___x_1415_ = 2;
v___x_1429_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1322_, v___x_1415_);
if (v___x_1429_ == 0)
{
v___y_1421_ = v___x_1429_;
goto v___jp_1420_;
}
else
{
uint8_t v___x_1430_; 
lean_inc_ref(v_msgData_1321_);
v___x_1430_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_1321_);
v___y_1421_ = v___x_1430_;
goto v___jp_1420_;
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
lean_ctor_set(v___x_1341_, 1, v___y_1331_);
lean_ctor_set(v___x_1341_, 2, v___y_1329_);
lean_ctor_set(v___x_1341_, 3, v___y_1333_);
lean_ctor_set(v___x_1341_, 4, v___x_1340_);
lean_ctor_set_uint8(v___x_1341_, sizeof(void*)*5, v___y_1334_);
lean_ctor_set_uint8(v___x_1341_, sizeof(void*)*5 + 1, v___y_1328_);
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
v_fileName_1373_ = lean_ctor_get(v___y_1371_, 0);
v_fileMap_1374_ = lean_ctor_get(v___y_1371_, 1);
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
v___x_1381_ = l_Lean_FileMap_toPosition(v_fileMap_1374_, v___y_1369_);
lean_dec(v___y_1369_);
v___x_1382_ = l_Lean_FileMap_toPosition(v_fileMap_1374_, v___y_1372_);
lean_dec(v___y_1372_);
v___x_1383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1383_, 0, v___x_1382_);
v___x_1384_ = ((lean_object*)(l_Lean_instInhabitedAttributeImplCore_default___closed__3));
if (v___y_1368_ == 0)
{
lean_del_object(v___x_1379_);
lean_dec_ref(v___y_1365_);
v___y_1328_ = v___y_1367_;
v___y_1329_ = v___x_1383_;
v___y_1330_ = v_a_1377_;
v___y_1331_ = v___x_1381_;
v___y_1332_ = v_fileName_1373_;
v___y_1333_ = v___x_1384_;
v___y_1334_ = v___y_1370_;
v_toCold_1335_ = v___y_1366_;
v___y_1336_ = v___y_1325_;
goto v___jp_1327_;
}
else
{
uint8_t v___x_1385_; 
lean_inc(v_a_1377_);
v___x_1385_ = l_Lean_MessageData_hasTag(v___y_1365_, v_a_1377_);
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
v___y_1328_ = v___y_1367_;
v___y_1329_ = v___x_1383_;
v___y_1330_ = v_a_1377_;
v___y_1331_ = v___x_1381_;
v___y_1332_ = v_fileName_1373_;
v___y_1333_ = v___x_1384_;
v___y_1334_ = v___y_1370_;
v_toCold_1335_ = v___y_1366_;
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
v___y_1365_ = v___y_1393_;
v___y_1366_ = v___y_1394_;
v___y_1367_ = v___y_1395_;
v___y_1368_ = v___y_1392_;
v___y_1369_ = v___y_1398_;
v___y_1370_ = v___y_1397_;
v___y_1371_ = v___y_1394_;
v___y_1372_ = v___y_1398_;
goto v___jp_1364_;
}
else
{
lean_object* v_val_1400_; 
v_val_1400_ = lean_ctor_get(v___x_1399_, 0);
lean_inc(v_val_1400_);
lean_dec_ref_known(v___x_1399_, 1);
v___y_1365_ = v___y_1393_;
v___y_1366_ = v___y_1394_;
v___y_1367_ = v___y_1395_;
v___y_1368_ = v___y_1392_;
v___y_1369_ = v___y_1398_;
v___y_1370_ = v___y_1397_;
v___y_1371_ = v___y_1394_;
v___y_1372_ = v_val_1400_;
goto v___jp_1364_;
}
}
v___jp_1401_:
{
lean_object* v_toCold_1405_; lean_object* v_ref_1406_; uint8_t v_suppressElabErrors_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___f_1410_; lean_object* v_ref_1411_; lean_object* v___x_1412_; 
v_toCold_1405_ = lean_ctor_get(v___y_1324_, 0);
v_ref_1406_ = lean_ctor_get(v___y_1324_, 2);
v_suppressElabErrors_1407_ = lean_ctor_get_uint8(v___y_1324_, sizeof(void*)*3 + 2);
v___x_1408_ = lean_box(v_suppressElabErrors_1407_);
v___x_1409_ = lean_box(v___y_1402_);
v___f_1410_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1410_, 0, v___x_1408_);
lean_closure_set(v___f_1410_, 1, v___x_1409_);
v_ref_1411_ = l_Lean_replaceRef(v_ref_1320_, v_ref_1406_);
v___x_1412_ = l_Lean_Syntax_getPos_x3f(v_ref_1411_, v___y_1403_);
if (lean_obj_tag(v___x_1412_) == 0)
{
lean_object* v___x_1413_; 
v___x_1413_ = lean_unsigned_to_nat(0u);
v___y_1392_ = v_suppressElabErrors_1407_;
v___y_1393_ = v___f_1410_;
v___y_1394_ = v_toCold_1405_;
v___y_1395_ = v___y_1404_;
v___y_1396_ = v_ref_1411_;
v___y_1397_ = v___y_1403_;
v___y_1398_ = v___x_1413_;
goto v___jp_1391_;
}
else
{
lean_object* v_val_1414_; 
v_val_1414_ = lean_ctor_get(v___x_1412_, 0);
lean_inc(v_val_1414_);
lean_dec_ref_known(v___x_1412_, 1);
v___y_1392_ = v_suppressElabErrors_1407_;
v___y_1393_ = v___f_1410_;
v___y_1394_ = v_toCold_1405_;
v___y_1395_ = v___y_1404_;
v___y_1396_ = v_ref_1411_;
v___y_1397_ = v___y_1403_;
v___y_1398_ = v_val_1414_;
goto v___jp_1391_;
}
}
v___jp_1416_:
{
if (v___y_1419_ == 0)
{
v___y_1402_ = v___y_1417_;
v___y_1403_ = v___y_1418_;
v___y_1404_ = v_severity_1322_;
goto v___jp_1401_;
}
else
{
v___y_1402_ = v___y_1417_;
v___y_1403_ = v___y_1418_;
v___y_1404_ = v___x_1415_;
goto v___jp_1401_;
}
}
v___jp_1420_:
{
if (v___y_1421_ == 0)
{
uint8_t v___x_1422_; uint8_t v___x_1423_; 
v___x_1422_ = 1;
v___x_1423_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1322_, v___x_1422_);
if (v___x_1423_ == 0)
{
v___y_1417_ = v___y_1421_;
v___y_1418_ = v___y_1421_;
v___y_1419_ = v___x_1423_;
goto v___jp_1416_;
}
else
{
lean_object* v___x_1424_; lean_object* v___x_1425_; uint8_t v___x_1426_; 
v___x_1424_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1324_);
v___x_1425_ = l_Lean_warningAsError;
v___x_1426_ = l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0_spec__3(v___x_1424_, v___x_1425_);
lean_dec_ref(v___x_1424_);
v___y_1417_ = v___y_1421_;
v___y_1418_ = v___y_1421_;
v___y_1419_ = v___x_1426_;
goto v___jp_1416_;
}
}
else
{
lean_object* v___x_1427_; lean_object* v___x_1428_; 
lean_dec_ref(v_msgData_1321_);
v___x_1427_ = lean_box(0);
v___x_1428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1428_, 0, v___x_1427_);
return v___x_1428_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___boxed(lean_object* v_ref_1431_, lean_object* v_msgData_1432_, lean_object* v_severity_1433_, lean_object* v_isSilent_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_){
_start:
{
uint8_t v_severity_boxed_1438_; uint8_t v_isSilent_boxed_1439_; lean_object* v_res_1440_; 
v_severity_boxed_1438_ = lean_unbox(v_severity_1433_);
v_isSilent_boxed_1439_ = lean_unbox(v_isSilent_1434_);
v_res_1440_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6(v_ref_1431_, v_msgData_1432_, v_severity_boxed_1438_, v_isSilent_boxed_1439_, v___y_1435_, v___y_1436_);
lean_dec(v___y_1436_);
lean_dec_ref(v___y_1435_);
lean_dec(v_ref_1431_);
return v_res_1440_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5(lean_object* v_msgData_1441_, uint8_t v_severity_1442_, uint8_t v_isSilent_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_){
_start:
{
lean_object* v_ref_1447_; lean_object* v___x_1448_; 
v_ref_1447_ = lean_ctor_get(v___y_1444_, 2);
v___x_1448_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6(v_ref_1447_, v_msgData_1441_, v_severity_1442_, v_isSilent_1443_, v___y_1444_, v___y_1445_);
return v___x_1448_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5___boxed(lean_object* v_msgData_1449_, lean_object* v_severity_1450_, lean_object* v_isSilent_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_){
_start:
{
uint8_t v_severity_boxed_1455_; uint8_t v_isSilent_boxed_1456_; lean_object* v_res_1457_; 
v_severity_boxed_1455_ = lean_unbox(v_severity_1450_);
v_isSilent_boxed_1456_ = lean_unbox(v_isSilent_1451_);
v_res_1457_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5(v_msgData_1449_, v_severity_boxed_1455_, v_isSilent_boxed_1456_, v___y_1452_, v___y_1453_);
lean_dec(v___y_1453_);
lean_dec_ref(v___y_1452_);
return v_res_1457_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1(lean_object* v_msgData_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_){
_start:
{
uint8_t v___x_1462_; uint8_t v___x_1463_; lean_object* v___x_1464_; 
v___x_1462_ = 1;
v___x_1463_ = 0;
v___x_1464_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5(v_msgData_1458_, v___x_1462_, v___x_1463_, v___y_1459_, v___y_1460_);
return v___x_1464_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1___boxed(lean_object* v_msgData_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_){
_start:
{
lean_object* v_res_1469_; 
v_res_1469_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1(v_msgData_1465_, v___y_1466_, v___y_1467_);
lean_dec(v___y_1467_);
lean_dec_ref(v___y_1466_);
return v_res_1469_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0___redArg(lean_object* v_opt_1470_, lean_object* v___y_1471_){
_start:
{
lean_object* v___x_1473_; uint8_t v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; 
v___x_1473_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1471_);
v___x_1474_ = l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0_spec__3(v___x_1473_, v_opt_1470_);
lean_dec_ref(v___x_1473_);
v___x_1475_ = lean_box(v___x_1474_);
v___x_1476_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1476_, 0, v___x_1475_);
return v___x_1476_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0___redArg___boxed(lean_object* v_opt_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_){
_start:
{
lean_object* v_res_1480_; 
v_res_1480_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0___redArg(v_opt_1477_, v___y_1478_);
lean_dec_ref(v___y_1478_);
lean_dec_ref(v_opt_1477_);
return v_res_1480_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1482_; lean_object* v___x_1483_; 
v___x_1482_ = ((lean_object*)(l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__0));
v___x_1483_ = l_Lean_stringToMessageData(v___x_1482_);
return v___x_1483_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__3(void){
_start:
{
lean_object* v___x_1485_; lean_object* v___x_1486_; 
v___x_1485_ = ((lean_object*)(l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__2));
v___x_1486_ = l_Lean_stringToMessageData(v___x_1485_);
return v___x_1486_;
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0(lean_object* v_id_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_){
_start:
{
lean_object* v___x_1491_; lean_object* v_env_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v_a_1495_; lean_object* v___x_1497_; uint8_t v_isShared_1498_; uint8_t v_isSharedCheck_1514_; 
v___x_1491_ = lean_st_ref_get(v___y_1489_);
v_env_1492_ = lean_ctor_get(v___x_1491_, 0);
lean_inc_ref(v_env_1492_);
lean_dec(v___x_1491_);
v___x_1493_ = l_Lean_ResolveName_backward_privateInPublic_warn;
v___x_1494_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0___redArg(v___x_1493_, v___y_1488_);
v_a_1495_ = lean_ctor_get(v___x_1494_, 0);
v_isSharedCheck_1514_ = !lean_is_exclusive(v___x_1494_);
if (v_isSharedCheck_1514_ == 0)
{
v___x_1497_ = v___x_1494_;
v_isShared_1498_ = v_isSharedCheck_1514_;
goto v_resetjp_1496_;
}
else
{
lean_inc(v_a_1495_);
lean_dec(v___x_1494_);
v___x_1497_ = lean_box(0);
v_isShared_1498_ = v_isSharedCheck_1514_;
goto v_resetjp_1496_;
}
v_resetjp_1496_:
{
uint8_t v_isExporting_1504_; 
v_isExporting_1504_ = lean_ctor_get_uint8(v_env_1492_, sizeof(void*)*13);
lean_dec_ref(v_env_1492_);
if (v_isExporting_1504_ == 0)
{
lean_dec(v_a_1495_);
lean_dec(v_id_1487_);
goto v___jp_1499_;
}
else
{
uint8_t v___x_1505_; 
v___x_1505_ = l_Lean_isPrivateName(v_id_1487_);
if (v___x_1505_ == 0)
{
lean_dec(v_a_1495_);
lean_dec(v_id_1487_);
goto v___jp_1499_;
}
else
{
uint8_t v___x_1506_; 
v___x_1506_ = lean_unbox(v_a_1495_);
lean_dec(v_a_1495_);
if (v___x_1506_ == 0)
{
lean_dec(v_id_1487_);
goto v___jp_1499_;
}
else
{
lean_object* v___x_1507_; uint8_t v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; 
lean_del_object(v___x_1497_);
v___x_1507_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__1, &l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__1_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__1);
v___x_1508_ = 0;
v___x_1509_ = l_Lean_MessageData_ofConstName(v_id_1487_, v___x_1508_);
v___x_1510_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1510_, 0, v___x_1507_);
lean_ctor_set(v___x_1510_, 1, v___x_1509_);
v___x_1511_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__3, &l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__3_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__3);
v___x_1512_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1512_, 0, v___x_1510_);
lean_ctor_set(v___x_1512_, 1, v___x_1511_);
v___x_1513_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1(v___x_1512_, v___y_1488_, v___y_1489_);
return v___x_1513_;
}
}
}
v___jp_1499_:
{
lean_object* v___x_1500_; lean_object* v___x_1502_; 
v___x_1500_ = lean_box(0);
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
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___boxed(lean_object* v_id_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_){
_start:
{
lean_object* v_res_1519_; 
v_res_1519_ = l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0(v_id_1515_, v___y_1516_, v___y_1517_);
lean_dec(v___y_1517_);
lean_dec_ref(v___y_1516_);
return v_res_1519_;
}
}
static lean_object* _init_l_Lean_ensureAttrDeclIsPublic___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1521_; lean_object* v___x_1522_; 
v___x_1521_ = ((lean_object*)(l_Lean_ensureAttrDeclIsPublic___lam__0___closed__0));
v___x_1522_ = l_Lean_stringToMessageData(v___x_1521_);
return v___x_1522_;
}
}
LEAN_EXPORT lean_object* l_Lean_ensureAttrDeclIsPublic___lam__0(lean_object* v_declName_1523_, uint8_t v_isModule_1524_, lean_object* v_attrName_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_){
_start:
{
lean_object* v___x_1529_; 
lean_inc(v_declName_1523_);
v___x_1529_ = l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0(v_declName_1523_, v___y_1526_, v___y_1527_);
if (lean_obj_tag(v___x_1529_) == 0)
{
lean_object* v___x_1530_; lean_object* v_a_1531_; lean_object* v___x_1533_; uint8_t v_isShared_1534_; uint8_t v_isSharedCheck_1551_; 
lean_dec_ref_known(v___x_1529_, 1);
lean_inc(v_declName_1523_);
v___x_1530_ = l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1___redArg(v_declName_1523_, v_isModule_1524_, v___y_1527_);
v_a_1531_ = lean_ctor_get(v___x_1530_, 0);
v_isSharedCheck_1551_ = !lean_is_exclusive(v___x_1530_);
if (v_isSharedCheck_1551_ == 0)
{
v___x_1533_ = v___x_1530_;
v_isShared_1534_ = v_isSharedCheck_1551_;
goto v_resetjp_1532_;
}
else
{
lean_inc(v_a_1531_);
lean_dec(v___x_1530_);
v___x_1533_ = lean_box(0);
v_isShared_1534_ = v_isSharedCheck_1551_;
goto v_resetjp_1532_;
}
v_resetjp_1532_:
{
uint8_t v___x_1535_; 
v___x_1535_ = lean_unbox(v_a_1531_);
if (v___x_1535_ == 0)
{
lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; uint8_t v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; 
lean_del_object(v___x_1533_);
v___x_1536_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1);
v___x_1537_ = l_Lean_MessageData_ofName(v_attrName_1525_);
v___x_1538_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1538_, 0, v___x_1536_);
lean_ctor_set(v___x_1538_, 1, v___x_1537_);
v___x_1539_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1, &l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1);
v___x_1540_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1540_, 0, v___x_1538_);
lean_ctor_set(v___x_1540_, 1, v___x_1539_);
v___x_1541_ = lean_unbox(v_a_1531_);
lean_dec(v_a_1531_);
v___x_1542_ = l_Lean_MessageData_ofConstName(v_declName_1523_, v___x_1541_);
v___x_1543_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1543_, 0, v___x_1540_);
lean_ctor_set(v___x_1543_, 1, v___x_1542_);
v___x_1544_ = lean_obj_once(&l_Lean_ensureAttrDeclIsPublic___lam__0___closed__1, &l_Lean_ensureAttrDeclIsPublic___lam__0___closed__1_once, _init_l_Lean_ensureAttrDeclIsPublic___lam__0___closed__1);
v___x_1545_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1545_, 0, v___x_1543_);
lean_ctor_set(v___x_1545_, 1, v___x_1544_);
v___x_1546_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_1545_, v___y_1526_, v___y_1527_);
return v___x_1546_;
}
else
{
lean_object* v___x_1547_; lean_object* v___x_1549_; 
lean_dec(v_a_1531_);
lean_dec(v_attrName_1525_);
lean_dec(v_declName_1523_);
v___x_1547_ = lean_box(0);
if (v_isShared_1534_ == 0)
{
lean_ctor_set(v___x_1533_, 0, v___x_1547_);
v___x_1549_ = v___x_1533_;
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
else
{
lean_dec(v_attrName_1525_);
lean_dec(v_declName_1523_);
return v___x_1529_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ensureAttrDeclIsPublic___lam__0___boxed(lean_object* v_declName_1552_, lean_object* v_isModule_1553_, lean_object* v_attrName_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_){
_start:
{
uint8_t v_isModule_boxed_1558_; lean_object* v_res_1559_; 
v_isModule_boxed_1558_ = lean_unbox(v_isModule_1553_);
v_res_1559_ = l_Lean_ensureAttrDeclIsPublic___lam__0(v_declName_1552_, v_isModule_boxed_1558_, v_attrName_1554_, v___y_1555_, v___y_1556_);
lean_dec(v___y_1556_);
lean_dec_ref(v___y_1555_);
return v_res_1559_;
}
}
LEAN_EXPORT lean_object* l_Lean_ensureAttrDeclIsPublic(lean_object* v_attrName_1560_, lean_object* v_declName_1561_, uint8_t v_attrKind_1562_, lean_object* v_a_1563_, lean_object* v_a_1564_){
_start:
{
lean_object* v___x_1566_; lean_object* v_env_1570_; lean_object* v___x_1571_; uint8_t v_isModule_1572_; 
v___x_1566_ = lean_st_ref_get(v_a_1564_);
v_env_1570_ = lean_ctor_get(v___x_1566_, 0);
lean_inc_ref(v_env_1570_);
lean_dec(v___x_1566_);
v___x_1571_ = l_Lean_Environment_header(v_env_1570_);
lean_dec_ref(v_env_1570_);
v_isModule_1572_ = lean_ctor_get_uint8(v___x_1571_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_1571_);
if (v_isModule_1572_ == 0)
{
lean_dec(v_declName_1561_);
lean_dec(v_attrName_1560_);
goto v___jp_1567_;
}
else
{
uint8_t v___x_1573_; uint8_t v___x_1574_; 
v___x_1573_ = 1;
v___x_1574_ = l_Lean_instBEqAttributeKind_beq(v_attrKind_1562_, v___x_1573_);
if (v___x_1574_ == 0)
{
lean_object* v___x_1575_; lean_object* v___f_1576_; lean_object* v___x_1577_; 
v___x_1575_ = lean_box(v_isModule_1572_);
v___f_1576_ = lean_alloc_closure((void*)(l_Lean_ensureAttrDeclIsPublic___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1576_, 0, v_declName_1561_);
lean_closure_set(v___f_1576_, 1, v___x_1575_);
lean_closure_set(v___f_1576_, 2, v_attrName_1560_);
v___x_1577_ = l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg(v___f_1576_, v_isModule_1572_, v_a_1563_, v_a_1564_);
return v___x_1577_;
}
else
{
lean_dec(v_declName_1561_);
lean_dec(v_attrName_1560_);
goto v___jp_1567_;
}
}
v___jp_1567_:
{
lean_object* v___x_1568_; lean_object* v___x_1569_; 
v___x_1568_ = lean_box(0);
v___x_1569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1569_, 0, v___x_1568_);
return v___x_1569_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ensureAttrDeclIsPublic___boxed(lean_object* v_attrName_1578_, lean_object* v_declName_1579_, lean_object* v_attrKind_1580_, lean_object* v_a_1581_, lean_object* v_a_1582_, lean_object* v_a_1583_){
_start:
{
uint8_t v_attrKind_boxed_1584_; lean_object* v_res_1585_; 
v_attrKind_boxed_1584_ = lean_unbox(v_attrKind_1580_);
v_res_1585_ = l_Lean_ensureAttrDeclIsPublic(v_attrName_1578_, v_declName_1579_, v_attrKind_boxed_1584_, v_a_1581_, v_a_1582_);
lean_dec(v_a_1582_);
lean_dec_ref(v_a_1581_);
return v_res_1585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0(lean_object* v_opt_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_){
_start:
{
lean_object* v___x_1590_; 
v___x_1590_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0___redArg(v_opt_1586_, v___y_1587_);
return v___x_1590_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0___boxed(lean_object* v_opt_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_){
_start:
{
lean_object* v_res_1595_; 
v_res_1595_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0(v_opt_1591_, v___y_1592_, v___y_1593_);
lean_dec(v___y_1593_);
lean_dec_ref(v___y_1592_);
lean_dec_ref(v_opt_1591_);
return v_res_1595_;
}
}
static lean_object* _init_l_Lean_ensureAttrDeclIsMeta___closed__1(void){
_start:
{
lean_object* v___x_1597_; lean_object* v___x_1598_; 
v___x_1597_ = ((lean_object*)(l_Lean_ensureAttrDeclIsMeta___closed__0));
v___x_1598_ = l_Lean_stringToMessageData(v___x_1597_);
return v___x_1598_;
}
}
LEAN_EXPORT lean_object* l_Lean_ensureAttrDeclIsMeta(lean_object* v_attrName_1599_, lean_object* v_declName_1600_, uint8_t v_attrKind_1601_, lean_object* v_a_1602_, lean_object* v_a_1603_){
_start:
{
lean_object* v___x_1605_; lean_object* v_env_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; uint8_t v_isModule_1609_; 
v___x_1605_ = lean_st_ref_get(v_a_1603_);
v_env_1606_ = lean_ctor_get(v___x_1605_, 0);
lean_inc_ref(v_env_1606_);
lean_dec(v___x_1605_);
v___x_1607_ = lean_st_ref_get(v_a_1603_);
v___x_1608_ = l_Lean_Environment_header(v_env_1606_);
lean_dec_ref(v_env_1606_);
v_isModule_1609_ = lean_ctor_get_uint8(v___x_1608_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_1608_);
if (v_isModule_1609_ == 0)
{
lean_object* v___x_1610_; 
lean_dec(v___x_1607_);
v___x_1610_ = l_Lean_ensureAttrDeclIsPublic(v_attrName_1599_, v_declName_1600_, v_attrKind_1601_, v_a_1602_, v_a_1603_);
return v___x_1610_;
}
else
{
lean_object* v_env_1611_; uint8_t v___x_1612_; 
v_env_1611_ = lean_ctor_get(v___x_1607_, 0);
lean_inc_ref(v_env_1611_);
lean_dec(v___x_1607_);
lean_inc(v_declName_1600_);
v___x_1612_ = l_Lean_isMarkedMeta(v_env_1611_, v_declName_1600_);
if (v___x_1612_ == 0)
{
lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; 
v___x_1613_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1);
v___x_1614_ = l_Lean_MessageData_ofName(v_attrName_1599_);
v___x_1615_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1615_, 0, v___x_1613_);
lean_ctor_set(v___x_1615_, 1, v___x_1614_);
v___x_1616_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1, &l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1);
v___x_1617_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1617_, 0, v___x_1615_);
lean_ctor_set(v___x_1617_, 1, v___x_1616_);
v___x_1618_ = l_Lean_MessageData_ofConstName(v_declName_1600_, v___x_1612_);
v___x_1619_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1619_, 0, v___x_1617_);
lean_ctor_set(v___x_1619_, 1, v___x_1618_);
v___x_1620_ = lean_obj_once(&l_Lean_ensureAttrDeclIsMeta___closed__1, &l_Lean_ensureAttrDeclIsMeta___closed__1_once, _init_l_Lean_ensureAttrDeclIsMeta___closed__1);
v___x_1621_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1621_, 0, v___x_1619_);
lean_ctor_set(v___x_1621_, 1, v___x_1620_);
v___x_1622_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_1621_, v_a_1602_, v_a_1603_);
return v___x_1622_;
}
else
{
lean_object* v___x_1623_; 
v___x_1623_ = l_Lean_ensureAttrDeclIsPublic(v_attrName_1599_, v_declName_1600_, v_attrKind_1601_, v_a_1602_, v_a_1603_);
return v___x_1623_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ensureAttrDeclIsMeta___boxed(lean_object* v_attrName_1624_, lean_object* v_declName_1625_, lean_object* v_attrKind_1626_, lean_object* v_a_1627_, lean_object* v_a_1628_, lean_object* v_a_1629_){
_start:
{
uint8_t v_attrKind_boxed_1630_; lean_object* v_res_1631_; 
v_attrKind_boxed_1630_ = lean_unbox(v_attrKind_1626_);
v_res_1631_ = l_Lean_ensureAttrDeclIsMeta(v_attrName_1624_, v_declName_1625_, v_attrKind_boxed_1630_, v_a_1627_, v_a_1628_);
lean_dec(v_a_1628_);
lean_dec_ref(v_a_1627_);
return v_res_1631_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__0(lean_object* v_x_1635_, lean_object* v___y_1636_){
_start:
{
lean_object* v___x_1638_; lean_object* v___x_1639_; 
v___x_1638_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___lam__0___closed__1));
v___x_1639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1639_, 0, v___x_1638_);
return v___x_1639_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__0___boxed(lean_object* v_x_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_){
_start:
{
lean_object* v_res_1643_; 
v_res_1643_ = l_Lean_instInhabitedTagAttribute_default___lam__0(v_x_1640_, v___y_1641_);
lean_dec_ref(v___y_1641_);
lean_dec_ref(v_x_1640_);
return v_res_1643_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__1(lean_object* v_s_1644_, lean_object* v_x_1645_){
_start:
{
lean_inc(v_s_1644_);
return v_s_1644_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__1___boxed(lean_object* v_s_1646_, lean_object* v_x_1647_){
_start:
{
lean_object* v_res_1648_; 
v_res_1648_ = l_Lean_instInhabitedTagAttribute_default___lam__1(v_s_1646_, v_x_1647_);
lean_dec(v_x_1647_);
lean_dec(v_s_1646_);
return v_res_1648_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__2(lean_object* v_x_1653_, lean_object* v_x_1654_){
_start:
{
lean_object* v___x_1655_; 
v___x_1655_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___lam__2___closed__1));
return v___x_1655_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__2___boxed(lean_object* v_x_1656_, lean_object* v_x_1657_){
_start:
{
lean_object* v_res_1658_; 
v_res_1658_ = l_Lean_instInhabitedTagAttribute_default___lam__2(v_x_1656_, v_x_1657_);
lean_dec(v_x_1657_);
lean_dec_ref(v_x_1656_);
return v_res_1658_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__3(lean_object* v_x_1659_){
_start:
{
lean_object* v___x_1660_; 
v___x_1660_ = lean_box(0);
return v___x_1660_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__3___boxed(lean_object* v_x_1661_){
_start:
{
lean_object* v_res_1662_; 
v_res_1662_ = l_Lean_instInhabitedTagAttribute_default___lam__3(v_x_1661_);
lean_dec(v_x_1661_);
return v_res_1662_;
}
}
static lean_object* _init_l_Lean_instInhabitedTagAttribute_default___closed__4(void){
_start:
{
lean_object* v___x_1667_; 
v___x_1667_ = l_Lean_instInhabitedEnvExtension_default___redArg();
return v___x_1667_;
}
}
static lean_object* _init_l_Lean_instInhabitedTagAttribute_default___closed__5(void){
_start:
{
lean_object* v___f_1668_; lean_object* v___f_1669_; lean_object* v___f_1670_; lean_object* v___f_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; 
v___f_1668_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___closed__3));
v___f_1669_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___closed__2));
v___f_1670_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___closed__1));
v___f_1671_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___closed__0));
v___x_1672_ = lean_box(0);
v___x_1673_ = lean_obj_once(&l_Lean_instInhabitedTagAttribute_default___closed__4, &l_Lean_instInhabitedTagAttribute_default___closed__4_once, _init_l_Lean_instInhabitedTagAttribute_default___closed__4);
v___x_1674_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1674_, 0, v___x_1673_);
lean_ctor_set(v___x_1674_, 1, v___x_1672_);
lean_ctor_set(v___x_1674_, 2, v___f_1671_);
lean_ctor_set(v___x_1674_, 3, v___f_1670_);
lean_ctor_set(v___x_1674_, 4, v___f_1669_);
lean_ctor_set(v___x_1674_, 5, v___f_1668_);
return v___x_1674_;
}
}
static lean_object* _init_l_Lean_instInhabitedTagAttribute_default___closed__6(void){
_start:
{
lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; 
v___x_1675_ = lean_obj_once(&l_Lean_instInhabitedTagAttribute_default___closed__5, &l_Lean_instInhabitedTagAttribute_default___closed__5_once, _init_l_Lean_instInhabitedTagAttribute_default___closed__5);
v___x_1676_ = ((lean_object*)(l_Lean_instInhabitedAttributeImpl_default));
v___x_1677_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1677_, 0, v___x_1676_);
lean_ctor_set(v___x_1677_, 1, v___x_1675_);
return v___x_1677_;
}
}
static lean_object* _init_l_Lean_instInhabitedTagAttribute_default(void){
_start:
{
lean_object* v___x_1678_; 
v___x_1678_ = lean_obj_once(&l_Lean_instInhabitedTagAttribute_default___closed__6, &l_Lean_instInhabitedTagAttribute_default___closed__6_once, _init_l_Lean_instInhabitedTagAttribute_default___closed__6);
return v___x_1678_;
}
}
static lean_object* _init_l_Lean_instInhabitedTagAttribute(void){
_start:
{
lean_object* v___x_1679_; 
v___x_1679_ = l_Lean_instInhabitedTagAttribute_default;
return v___x_1679_;
}
}
static lean_object* _init_l_Lean_registerTagAttribute___auto__1(void){
_start:
{
lean_object* v___x_1680_; 
v___x_1680_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__28, &l_Lean_AttributeImplCore_ref___autoParam___closed__28_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__28);
return v___x_1680_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__0(lean_object* v_x_1681_){
_start:
{
lean_object* v___x_1682_; 
v___x_1682_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___lam__2___closed__0));
return v___x_1682_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__0___boxed(lean_object* v_x_1683_){
_start:
{
lean_object* v_res_1684_; 
v_res_1684_ = l_Lean_registerTagAttribute___lam__0(v_x_1683_);
lean_dec(v_x_1683_);
return v_res_1684_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerTagAttribute_spec__0(lean_object* v_newState_1685_, lean_object* v_x_1686_, lean_object* v_x_1687_){
_start:
{
if (lean_obj_tag(v_x_1687_) == 0)
{
return v_x_1686_;
}
else
{
lean_object* v_head_1688_; lean_object* v_tail_1689_; uint8_t v___x_1690_; 
v_head_1688_ = lean_ctor_get(v_x_1687_, 0);
lean_inc(v_head_1688_);
v_tail_1689_ = lean_ctor_get(v_x_1687_, 1);
lean_inc(v_tail_1689_);
lean_dec_ref_known(v_x_1687_, 2);
v___x_1690_ = l_Lean_NameSet_contains(v_newState_1685_, v_head_1688_);
if (v___x_1690_ == 0)
{
lean_dec(v_head_1688_);
v_x_1687_ = v_tail_1689_;
goto _start;
}
else
{
lean_object* v___x_1692_; 
v___x_1692_ = l_Lean_NameSet_insert(v_x_1686_, v_head_1688_);
v_x_1686_ = v___x_1692_;
v_x_1687_ = v_tail_1689_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerTagAttribute_spec__0___boxed(lean_object* v_newState_1694_, lean_object* v_x_1695_, lean_object* v_x_1696_){
_start:
{
lean_object* v_res_1697_; 
v_res_1697_ = l_List_foldl___at___00Lean_registerTagAttribute_spec__0(v_newState_1694_, v_x_1695_, v_x_1696_);
lean_dec(v_newState_1694_);
return v_res_1697_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__1(lean_object* v_x_1698_, lean_object* v_newState_1699_, lean_object* v_newConsts_1700_, lean_object* v_s_1701_){
_start:
{
lean_object* v___x_1702_; 
v___x_1702_ = l_List_foldl___at___00Lean_registerTagAttribute_spec__0(v_newState_1699_, v_s_1701_, v_newConsts_1700_);
return v___x_1702_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__1___boxed(lean_object* v_x_1703_, lean_object* v_newState_1704_, lean_object* v_newConsts_1705_, lean_object* v_s_1706_){
_start:
{
lean_object* v_res_1707_; 
v_res_1707_ = l_Lean_registerTagAttribute___lam__1(v_x_1703_, v_newState_1704_, v_newConsts_1705_, v_s_1706_);
lean_dec(v_newState_1704_);
lean_dec(v_x_1703_);
return v_res_1707_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__2(lean_object* v_s_1720_){
_start:
{
lean_object* v___x_1721_; lean_object* v___y_1723_; 
v___x_1721_ = ((lean_object*)(l_Lean_registerTagAttribute___lam__2___closed__5));
if (lean_obj_tag(v_s_1720_) == 0)
{
lean_object* v_size_1727_; 
v_size_1727_ = lean_ctor_get(v_s_1720_, 0);
lean_inc(v_size_1727_);
lean_dec_ref_known(v_s_1720_, 5);
v___y_1723_ = v_size_1727_;
goto v___jp_1722_;
}
else
{
lean_object* v___x_1728_; 
v___x_1728_ = lean_unsigned_to_nat(0u);
v___y_1723_ = v___x_1728_;
goto v___jp_1722_;
}
v___jp_1722_:
{
lean_object* v___x_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; 
v___x_1724_ = l_Nat_reprFast(v___y_1723_);
v___x_1725_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1725_, 0, v___x_1724_);
v___x_1726_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1726_, 0, v___x_1721_);
lean_ctor_set(v___x_1726_, 1, v___x_1725_);
return v___x_1726_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4___redArg(lean_object* v_hi_1729_, lean_object* v_pivot_1730_, lean_object* v_as_1731_, lean_object* v_i_1732_, lean_object* v_k_1733_){
_start:
{
uint8_t v___x_1734_; 
v___x_1734_ = lean_nat_dec_lt(v_k_1733_, v_hi_1729_);
if (v___x_1734_ == 0)
{
lean_object* v___x_1735_; lean_object* v___x_1736_; 
lean_dec(v_k_1733_);
v___x_1735_ = lean_array_fswap(v_as_1731_, v_i_1732_, v_hi_1729_);
v___x_1736_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1736_, 0, v_i_1732_);
lean_ctor_set(v___x_1736_, 1, v___x_1735_);
return v___x_1736_;
}
else
{
lean_object* v___x_1737_; uint8_t v___x_1738_; 
v___x_1737_ = lean_array_fget_borrowed(v_as_1731_, v_k_1733_);
v___x_1738_ = l_Lean_Name_quickLt(v___x_1737_, v_pivot_1730_);
if (v___x_1738_ == 0)
{
lean_object* v___x_1739_; lean_object* v___x_1740_; 
v___x_1739_ = lean_unsigned_to_nat(1u);
v___x_1740_ = lean_nat_add(v_k_1733_, v___x_1739_);
lean_dec(v_k_1733_);
v_k_1733_ = v___x_1740_;
goto _start;
}
else
{
lean_object* v___x_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; 
v___x_1742_ = lean_array_fswap(v_as_1731_, v_i_1732_, v_k_1733_);
v___x_1743_ = lean_unsigned_to_nat(1u);
v___x_1744_ = lean_nat_add(v_i_1732_, v___x_1743_);
lean_dec(v_i_1732_);
v___x_1745_ = lean_nat_add(v_k_1733_, v___x_1743_);
lean_dec(v_k_1733_);
v_as_1731_ = v___x_1742_;
v_i_1732_ = v___x_1744_;
v_k_1733_ = v___x_1745_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4___redArg___boxed(lean_object* v_hi_1747_, lean_object* v_pivot_1748_, lean_object* v_as_1749_, lean_object* v_i_1750_, lean_object* v_k_1751_){
_start:
{
lean_object* v_res_1752_; 
v_res_1752_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4___redArg(v_hi_1747_, v_pivot_1748_, v_as_1749_, v_i_1750_, v_k_1751_);
lean_dec(v_pivot_1748_);
lean_dec(v_hi_1747_);
return v_res_1752_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___redArg(lean_object* v_n_1753_, lean_object* v_as_1754_, lean_object* v_lo_1755_, lean_object* v_hi_1756_){
_start:
{
lean_object* v___y_1758_; uint8_t v___x_1768_; 
v___x_1768_ = lean_nat_dec_lt(v_lo_1755_, v_hi_1756_);
if (v___x_1768_ == 0)
{
lean_dec(v_lo_1755_);
return v_as_1754_;
}
else
{
lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v_mid_1771_; lean_object* v___y_1773_; lean_object* v___y_1779_; lean_object* v___x_1784_; lean_object* v___x_1785_; uint8_t v___x_1786_; 
v___x_1769_ = lean_nat_add(v_lo_1755_, v_hi_1756_);
v___x_1770_ = lean_unsigned_to_nat(1u);
v_mid_1771_ = lean_nat_shiftr(v___x_1769_, v___x_1770_);
lean_dec(v___x_1769_);
v___x_1784_ = lean_array_fget_borrowed(v_as_1754_, v_mid_1771_);
v___x_1785_ = lean_array_fget_borrowed(v_as_1754_, v_lo_1755_);
v___x_1786_ = l_Lean_Name_quickLt(v___x_1784_, v___x_1785_);
if (v___x_1786_ == 0)
{
v___y_1779_ = v_as_1754_;
goto v___jp_1778_;
}
else
{
lean_object* v___x_1787_; 
v___x_1787_ = lean_array_fswap(v_as_1754_, v_lo_1755_, v_mid_1771_);
v___y_1779_ = v___x_1787_;
goto v___jp_1778_;
}
v___jp_1772_:
{
lean_object* v___x_1774_; lean_object* v___x_1775_; uint8_t v___x_1776_; 
v___x_1774_ = lean_array_fget_borrowed(v___y_1773_, v_mid_1771_);
v___x_1775_ = lean_array_fget_borrowed(v___y_1773_, v_hi_1756_);
v___x_1776_ = l_Lean_Name_quickLt(v___x_1774_, v___x_1775_);
if (v___x_1776_ == 0)
{
lean_dec(v_mid_1771_);
v___y_1758_ = v___y_1773_;
goto v___jp_1757_;
}
else
{
lean_object* v___x_1777_; 
v___x_1777_ = lean_array_fswap(v___y_1773_, v_mid_1771_, v_hi_1756_);
lean_dec(v_mid_1771_);
v___y_1758_ = v___x_1777_;
goto v___jp_1757_;
}
}
v___jp_1778_:
{
lean_object* v___x_1780_; lean_object* v___x_1781_; uint8_t v___x_1782_; 
v___x_1780_ = lean_array_fget_borrowed(v___y_1779_, v_hi_1756_);
v___x_1781_ = lean_array_fget_borrowed(v___y_1779_, v_lo_1755_);
v___x_1782_ = l_Lean_Name_quickLt(v___x_1780_, v___x_1781_);
if (v___x_1782_ == 0)
{
v___y_1773_ = v___y_1779_;
goto v___jp_1772_;
}
else
{
lean_object* v___x_1783_; 
v___x_1783_ = lean_array_fswap(v___y_1779_, v_lo_1755_, v_hi_1756_);
v___y_1773_ = v___x_1783_;
goto v___jp_1772_;
}
}
}
v___jp_1757_:
{
lean_object* v_pivot_1759_; lean_object* v___x_1760_; lean_object* v_fst_1761_; lean_object* v_snd_1762_; uint8_t v___x_1763_; 
v_pivot_1759_ = lean_array_fget(v___y_1758_, v_hi_1756_);
lean_inc_n(v_lo_1755_, 2);
v___x_1760_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4___redArg(v_hi_1756_, v_pivot_1759_, v___y_1758_, v_lo_1755_, v_lo_1755_);
lean_dec(v_pivot_1759_);
v_fst_1761_ = lean_ctor_get(v___x_1760_, 0);
lean_inc(v_fst_1761_);
v_snd_1762_ = lean_ctor_get(v___x_1760_, 1);
lean_inc(v_snd_1762_);
lean_dec_ref(v___x_1760_);
v___x_1763_ = lean_nat_dec_le(v_hi_1756_, v_fst_1761_);
if (v___x_1763_ == 0)
{
lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; 
v___x_1764_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___redArg(v_n_1753_, v_snd_1762_, v_lo_1755_, v_fst_1761_);
v___x_1765_ = lean_unsigned_to_nat(1u);
v___x_1766_ = lean_nat_add(v_fst_1761_, v___x_1765_);
lean_dec(v_fst_1761_);
v_as_1754_ = v___x_1764_;
v_lo_1755_ = v___x_1766_;
goto _start;
}
else
{
lean_dec(v_fst_1761_);
lean_dec(v_lo_1755_);
return v_snd_1762_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___redArg___boxed(lean_object* v_n_1788_, lean_object* v_as_1789_, lean_object* v_lo_1790_, lean_object* v_hi_1791_){
_start:
{
lean_object* v_res_1792_; 
v_res_1792_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___redArg(v_n_1788_, v_as_1789_, v_lo_1790_, v_hi_1791_);
lean_dec(v_hi_1791_);
lean_dec(v_n_1788_);
return v_res_1792_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerTagAttribute_spec__2(lean_object* v_env_1793_, lean_object* v_as_1794_, size_t v_i_1795_, size_t v_stop_1796_, lean_object* v_b_1797_){
_start:
{
lean_object* v___y_1799_; uint8_t v___x_1803_; 
v___x_1803_ = lean_usize_dec_eq(v_i_1795_, v_stop_1796_);
if (v___x_1803_ == 0)
{
lean_object* v___x_1804_; uint8_t v___x_1805_; lean_object* v___x_1806_; uint8_t v___x_1807_; 
v___x_1804_ = lean_array_uget_borrowed(v_as_1794_, v_i_1795_);
v___x_1805_ = 1;
lean_inc_ref(v_env_1793_);
v___x_1806_ = l_Lean_Environment_setExporting(v_env_1793_, v___x_1805_);
lean_inc(v___x_1804_);
v___x_1807_ = l_Lean_Environment_contains(v___x_1806_, v___x_1804_, v___x_1803_);
if (v___x_1807_ == 0)
{
v___y_1799_ = v_b_1797_;
goto v___jp_1798_;
}
else
{
lean_object* v___x_1808_; 
lean_inc(v___x_1804_);
v___x_1808_ = lean_array_push(v_b_1797_, v___x_1804_);
v___y_1799_ = v___x_1808_;
goto v___jp_1798_;
}
}
else
{
lean_dec_ref(v_env_1793_);
return v_b_1797_;
}
v___jp_1798_:
{
size_t v___x_1800_; size_t v___x_1801_; 
v___x_1800_ = ((size_t)1ULL);
v___x_1801_ = lean_usize_add(v_i_1795_, v___x_1800_);
v_i_1795_ = v___x_1801_;
v_b_1797_ = v___y_1799_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerTagAttribute_spec__2___boxed(lean_object* v_env_1809_, lean_object* v_as_1810_, lean_object* v_i_1811_, lean_object* v_stop_1812_, lean_object* v_b_1813_){
_start:
{
size_t v_i_boxed_1814_; size_t v_stop_boxed_1815_; lean_object* v_res_1816_; 
v_i_boxed_1814_ = lean_unbox_usize(v_i_1811_);
lean_dec(v_i_1811_);
v_stop_boxed_1815_ = lean_unbox_usize(v_stop_1812_);
lean_dec(v_stop_1812_);
v_res_1816_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerTagAttribute_spec__2(v_env_1809_, v_as_1810_, v_i_boxed_1814_, v_stop_boxed_1815_, v_b_1813_);
lean_dec_ref(v_as_1810_);
return v_res_1816_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerTagAttribute_spec__1_spec__1(lean_object* v_init_1817_, lean_object* v_x_1818_){
_start:
{
if (lean_obj_tag(v_x_1818_) == 0)
{
lean_object* v_k_1819_; lean_object* v_l_1820_; lean_object* v_r_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; 
v_k_1819_ = lean_ctor_get(v_x_1818_, 1);
lean_inc(v_k_1819_);
v_l_1820_ = lean_ctor_get(v_x_1818_, 3);
lean_inc(v_l_1820_);
v_r_1821_ = lean_ctor_get(v_x_1818_, 4);
lean_inc(v_r_1821_);
lean_dec_ref_known(v_x_1818_, 5);
v___x_1822_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerTagAttribute_spec__1_spec__1(v_init_1817_, v_l_1820_);
v___x_1823_ = lean_array_push(v___x_1822_, v_k_1819_);
v_init_1817_ = v___x_1823_;
v_x_1818_ = v_r_1821_;
goto _start;
}
else
{
return v_init_1817_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__3(lean_object* v_env_1825_, lean_object* v_es_1826_){
_start:
{
lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___y_1830_; lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___y_1847_; lean_object* v___y_1848_; uint8_t v___x_1850_; 
v___x_1827_ = lean_unsigned_to_nat(0u);
v___x_1828_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___lam__2___closed__0));
v___x_1844_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerTagAttribute_spec__1_spec__1(v___x_1828_, v_es_1826_);
v___x_1845_ = lean_array_get_size(v___x_1844_);
v___x_1850_ = lean_nat_dec_eq(v___x_1845_, v___x_1827_);
if (v___x_1850_ == 0)
{
lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___y_1854_; uint8_t v___x_1856_; 
v___x_1851_ = lean_unsigned_to_nat(1u);
v___x_1852_ = lean_nat_sub(v___x_1845_, v___x_1851_);
v___x_1856_ = lean_nat_dec_le(v___x_1827_, v___x_1852_);
if (v___x_1856_ == 0)
{
lean_inc(v___x_1852_);
v___y_1854_ = v___x_1852_;
goto v___jp_1853_;
}
else
{
v___y_1854_ = v___x_1827_;
goto v___jp_1853_;
}
v___jp_1853_:
{
uint8_t v___x_1855_; 
v___x_1855_ = lean_nat_dec_le(v___y_1854_, v___x_1852_);
if (v___x_1855_ == 0)
{
lean_dec(v___x_1852_);
lean_inc(v___y_1854_);
v___y_1847_ = v___y_1854_;
v___y_1848_ = v___y_1854_;
goto v___jp_1846_;
}
else
{
v___y_1847_ = v___y_1854_;
v___y_1848_ = v___x_1852_;
goto v___jp_1846_;
}
}
}
else
{
v___y_1830_ = v___x_1844_;
goto v___jp_1829_;
}
v___jp_1829_:
{
lean_object* v___x_1831_; uint8_t v___x_1832_; 
v___x_1831_ = lean_array_get_size(v___y_1830_);
v___x_1832_ = lean_nat_dec_lt(v___x_1827_, v___x_1831_);
if (v___x_1832_ == 0)
{
lean_object* v___x_1833_; 
lean_dec_ref(v_env_1825_);
v___x_1833_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1833_, 0, v___x_1828_);
lean_ctor_set(v___x_1833_, 1, v___x_1828_);
lean_ctor_set(v___x_1833_, 2, v___y_1830_);
return v___x_1833_;
}
else
{
uint8_t v___x_1834_; 
v___x_1834_ = lean_nat_dec_le(v___x_1831_, v___x_1831_);
if (v___x_1834_ == 0)
{
if (v___x_1832_ == 0)
{
lean_object* v___x_1835_; 
lean_dec_ref(v_env_1825_);
v___x_1835_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1835_, 0, v___x_1828_);
lean_ctor_set(v___x_1835_, 1, v___x_1828_);
lean_ctor_set(v___x_1835_, 2, v___y_1830_);
return v___x_1835_;
}
else
{
size_t v___x_1836_; size_t v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; 
v___x_1836_ = ((size_t)0ULL);
v___x_1837_ = lean_usize_of_nat(v___x_1831_);
v___x_1838_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerTagAttribute_spec__2(v_env_1825_, v___y_1830_, v___x_1836_, v___x_1837_, v___x_1828_);
lean_inc_ref(v___x_1838_);
v___x_1839_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1839_, 0, v___x_1838_);
lean_ctor_set(v___x_1839_, 1, v___x_1838_);
lean_ctor_set(v___x_1839_, 2, v___y_1830_);
return v___x_1839_;
}
}
else
{
size_t v___x_1840_; size_t v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; 
v___x_1840_ = ((size_t)0ULL);
v___x_1841_ = lean_usize_of_nat(v___x_1831_);
v___x_1842_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerTagAttribute_spec__2(v_env_1825_, v___y_1830_, v___x_1840_, v___x_1841_, v___x_1828_);
lean_inc_ref(v___x_1842_);
v___x_1843_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1843_, 0, v___x_1842_);
lean_ctor_set(v___x_1843_, 1, v___x_1842_);
lean_ctor_set(v___x_1843_, 2, v___y_1830_);
return v___x_1843_;
}
}
}
v___jp_1846_:
{
lean_object* v___x_1849_; 
v___x_1849_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___redArg(v___x_1845_, v___x_1844_, v___y_1847_, v___y_1848_);
lean_dec(v___y_1848_);
v___y_1830_ = v___x_1849_;
goto v___jp_1829_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__4(lean_object* v_name_1857_, lean_object* v_decl_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_){
_start:
{
lean_object* v___x_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; 
v___x_1862_ = lean_obj_once(&l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1, &l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1_once, _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1);
v___x_1863_ = l_Lean_MessageData_ofName(v_name_1857_);
v___x_1864_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1864_, 0, v___x_1862_);
lean_ctor_set(v___x_1864_, 1, v___x_1863_);
v___x_1865_ = lean_obj_once(&l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3, &l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3_once, _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3);
v___x_1866_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1866_, 0, v___x_1864_);
lean_ctor_set(v___x_1866_, 1, v___x_1865_);
v___x_1867_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_1866_, v___y_1859_, v___y_1860_);
return v___x_1867_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__4___boxed(lean_object* v_name_1868_, lean_object* v_decl_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_){
_start:
{
lean_object* v_res_1873_; 
v_res_1873_ = l_Lean_registerTagAttribute___lam__4(v_name_1868_, v_decl_1869_, v___y_1870_, v___y_1871_);
lean_dec(v___y_1871_);
lean_dec_ref(v___y_1870_);
lean_dec(v_decl_1869_);
return v_res_1873_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__5(lean_object* v___x_1874_, lean_object* v_x_1875_, lean_object* v_x_1876_){
_start:
{
lean_object* v___x_1878_; 
v___x_1878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1878_, 0, v___x_1874_);
return v___x_1878_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__5___boxed(lean_object* v___x_1879_, lean_object* v_x_1880_, lean_object* v_x_1881_, lean_object* v___y_1882_){
_start:
{
lean_object* v_res_1883_; 
v_res_1883_ = l_Lean_registerTagAttribute___lam__5(v___x_1879_, v_x_1880_, v_x_1881_);
lean_dec_ref(v_x_1881_);
lean_dec_ref(v_x_1880_);
return v_res_1883_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__6(lean_object* v___x_1884_){
_start:
{
lean_object* v___x_1886_; 
v___x_1886_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1886_, 0, v___x_1884_);
return v___x_1886_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__6___boxed(lean_object* v___x_1887_, lean_object* v___y_1888_){
_start:
{
lean_object* v_res_1889_; 
v_res_1889_ = l_Lean_registerTagAttribute___lam__6(v___x_1887_);
return v_res_1889_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__7(lean_object* v_a_1890_, lean_object* v_decl_1891_, lean_object* v_s_1892_){
_start:
{
lean_object* v_addEntryFn_1893_; lean_object* v_importedEntries_1894_; lean_object* v_state_1895_; lean_object* v___x_1897_; uint8_t v_isShared_1898_; uint8_t v_isSharedCheck_1903_; 
v_addEntryFn_1893_ = lean_ctor_get(v_a_1890_, 3);
lean_inc(v_addEntryFn_1893_);
lean_dec_ref(v_a_1890_);
v_importedEntries_1894_ = lean_ctor_get(v_s_1892_, 0);
v_state_1895_ = lean_ctor_get(v_s_1892_, 1);
v_isSharedCheck_1903_ = !lean_is_exclusive(v_s_1892_);
if (v_isSharedCheck_1903_ == 0)
{
v___x_1897_ = v_s_1892_;
v_isShared_1898_ = v_isSharedCheck_1903_;
goto v_resetjp_1896_;
}
else
{
lean_inc(v_state_1895_);
lean_inc(v_importedEntries_1894_);
lean_dec(v_s_1892_);
v___x_1897_ = lean_box(0);
v_isShared_1898_ = v_isSharedCheck_1903_;
goto v_resetjp_1896_;
}
v_resetjp_1896_:
{
lean_object* v_state_1899_; lean_object* v___x_1901_; 
v_state_1899_ = lean_apply_2(v_addEntryFn_1893_, v_state_1895_, v_decl_1891_);
if (v_isShared_1898_ == 0)
{
lean_ctor_set(v___x_1897_, 1, v_state_1899_);
v___x_1901_ = v___x_1897_;
goto v_reusejp_1900_;
}
else
{
lean_object* v_reuseFailAlloc_1902_; 
v_reuseFailAlloc_1902_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1902_, 0, v_importedEntries_1894_);
lean_ctor_set(v_reuseFailAlloc_1902_, 1, v_state_1899_);
v___x_1901_ = v_reuseFailAlloc_1902_;
goto v_reusejp_1900_;
}
v_reusejp_1900_:
{
return v___x_1901_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg(lean_object* v_attrName_1904_, lean_object* v_declName_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_){
_start:
{
lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; uint8_t v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; 
v___x_1909_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1);
v___x_1910_ = l_Lean_MessageData_ofName(v_attrName_1904_);
v___x_1911_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1911_, 0, v___x_1909_);
lean_ctor_set(v___x_1911_, 1, v___x_1910_);
v___x_1912_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__3, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__3_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__3);
v___x_1913_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1913_, 0, v___x_1911_);
lean_ctor_set(v___x_1913_, 1, v___x_1912_);
v___x_1914_ = 0;
v___x_1915_ = l_Lean_MessageData_ofConstName(v_declName_1905_, v___x_1914_);
v___x_1916_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1916_, 0, v___x_1913_);
lean_ctor_set(v___x_1916_, 1, v___x_1915_);
v___x_1917_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__5, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__5_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__5);
v___x_1918_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1918_, 0, v___x_1916_);
lean_ctor_set(v___x_1918_, 1, v___x_1917_);
v___x_1919_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_1918_, v___y_1906_, v___y_1907_);
return v___x_1919_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg___boxed(lean_object* v_attrName_1920_, lean_object* v_declName_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_){
_start:
{
lean_object* v_res_1925_; 
v_res_1925_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg(v_attrName_1920_, v_declName_1921_, v___y_1922_, v___y_1923_);
lean_dec(v___y_1923_);
lean_dec_ref(v___y_1922_);
return v_res_1925_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___redArg(lean_object* v_attrName_1926_, lean_object* v_declName_1927_, lean_object* v_asyncPrefix_x3f_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_){
_start:
{
lean_object* v___y_1933_; 
if (lean_obj_tag(v_asyncPrefix_x3f_1928_) == 0)
{
lean_object* v___x_1946_; 
v___x_1946_ = l_Lean_MessageData_nil;
v___y_1933_ = v___x_1946_;
goto v___jp_1932_;
}
else
{
lean_object* v_val_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; 
v_val_1947_ = lean_ctor_get(v_asyncPrefix_x3f_1928_, 0);
lean_inc(v_val_1947_);
lean_dec_ref_known(v_asyncPrefix_x3f_1928_, 1);
v___x_1948_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___redArg___closed__3, &l_Lean_throwAttrNotInAsyncCtx___redArg___closed__3_once, _init_l_Lean_throwAttrNotInAsyncCtx___redArg___closed__3);
v___x_1949_ = l_Lean_MessageData_ofName(v_val_1947_);
v___x_1950_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1950_, 0, v___x_1948_);
lean_ctor_set(v___x_1950_, 1, v___x_1949_);
v___x_1951_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__5, &l_Lean_throwAttrMustBeGlobal___redArg___closed__5_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__5);
v___x_1952_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1952_, 0, v___x_1950_);
lean_ctor_set(v___x_1952_, 1, v___x_1951_);
v___y_1933_ = v___x_1952_;
goto v___jp_1932_;
}
v___jp_1932_:
{
lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; uint8_t v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; 
v___x_1934_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1);
v___x_1935_ = l_Lean_MessageData_ofName(v_attrName_1926_);
v___x_1936_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1936_, 0, v___x_1934_);
lean_ctor_set(v___x_1936_, 1, v___x_1935_);
v___x_1937_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__3, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__3_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__3);
v___x_1938_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1938_, 0, v___x_1936_);
lean_ctor_set(v___x_1938_, 1, v___x_1937_);
v___x_1939_ = 0;
v___x_1940_ = l_Lean_MessageData_ofConstName(v_declName_1927_, v___x_1939_);
v___x_1941_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1941_, 0, v___x_1938_);
lean_ctor_set(v___x_1941_, 1, v___x_1940_);
v___x_1942_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___redArg___closed__1, &l_Lean_throwAttrNotInAsyncCtx___redArg___closed__1_once, _init_l_Lean_throwAttrNotInAsyncCtx___redArg___closed__1);
v___x_1943_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1943_, 0, v___x_1941_);
lean_ctor_set(v___x_1943_, 1, v___x_1942_);
v___x_1944_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1944_, 0, v___x_1943_);
lean_ctor_set(v___x_1944_, 1, v___y_1933_);
v___x_1945_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_1944_, v___y_1929_, v___y_1930_);
return v___x_1945_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___redArg___boxed(lean_object* v_attrName_1953_, lean_object* v_declName_1954_, lean_object* v_asyncPrefix_x3f_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_){
_start:
{
lean_object* v_res_1959_; 
v_res_1959_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___redArg(v_attrName_1953_, v_declName_1954_, v_asyncPrefix_x3f_1955_, v___y_1956_, v___y_1957_);
lean_dec(v___y_1957_);
lean_dec_ref(v___y_1956_);
return v_res_1959_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg(lean_object* v_name_1960_, uint8_t v_kind_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_){
_start:
{
lean_object* v___x_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; lean_object* v___y_1971_; 
v___x_1965_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__1, &l_Lean_throwAttrMustBeGlobal___redArg___closed__1_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__1);
v___x_1966_ = l_Lean_MessageData_ofName(v_name_1960_);
v___x_1967_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1967_, 0, v___x_1965_);
lean_ctor_set(v___x_1967_, 1, v___x_1966_);
v___x_1968_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__3, &l_Lean_throwAttrMustBeGlobal___redArg___closed__3_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__3);
v___x_1969_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1969_, 0, v___x_1967_);
lean_ctor_set(v___x_1969_, 1, v___x_1968_);
switch(v_kind_1961_)
{
case 0:
{
lean_object* v___x_1978_; 
v___x_1978_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__0));
v___y_1971_ = v___x_1978_;
goto v___jp_1970_;
}
case 1:
{
lean_object* v___x_1979_; 
v___x_1979_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__1));
v___y_1971_ = v___x_1979_;
goto v___jp_1970_;
}
default: 
{
lean_object* v___x_1980_; 
v___x_1980_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__2));
v___y_1971_ = v___x_1980_;
goto v___jp_1970_;
}
}
v___jp_1970_:
{
lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; 
lean_inc_ref(v___y_1971_);
v___x_1972_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1972_, 0, v___y_1971_);
v___x_1973_ = l_Lean_MessageData_ofFormat(v___x_1972_);
v___x_1974_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1974_, 0, v___x_1969_);
lean_ctor_set(v___x_1974_, 1, v___x_1973_);
v___x_1975_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__5, &l_Lean_throwAttrMustBeGlobal___redArg___closed__5_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__5);
v___x_1976_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1976_, 0, v___x_1974_);
lean_ctor_set(v___x_1976_, 1, v___x_1975_);
v___x_1977_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_1976_, v___y_1962_, v___y_1963_);
return v___x_1977_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg___boxed(lean_object* v_name_1981_, lean_object* v_kind_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_){
_start:
{
uint8_t v_kind_boxed_1986_; lean_object* v_res_1987_; 
v_kind_boxed_1986_ = lean_unbox(v_kind_1982_);
v_res_1987_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg(v_name_1981_, v_kind_boxed_1986_, v___y_1983_, v___y_1984_);
lean_dec(v___y_1984_);
lean_dec_ref(v___y_1983_);
return v_res_1987_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__8(lean_object* v_a_1988_, lean_object* v_validate_1989_, lean_object* v_name_1990_, lean_object* v_decl_1991_, lean_object* v_stx_1992_, uint8_t v_kind_1993_, lean_object* v___y_1994_, lean_object* v___y_1995_){
_start:
{
lean_object* v_nextMacroScope_1998_; lean_object* v_ngen_1999_; lean_object* v_auxDeclNGen_2000_; lean_object* v_traceState_2001_; lean_object* v_recordedDeps_2002_; lean_object* v_messages_2003_; lean_object* v_infoState_2004_; lean_object* v_snapshotTasks_2005_; lean_object* v___y_2006_; lean_object* v___y_2007_; lean_object* v___y_2008_; lean_object* v___f_2013_; lean_object* v___y_2015_; lean_object* v___y_2016_; lean_object* v___y_2037_; lean_object* v___y_2038_; lean_object* v___y_2039_; lean_object* v___x_2050_; 
lean_inc(v_decl_1991_);
lean_inc_ref(v_a_1988_);
v___f_2013_ = lean_alloc_closure((void*)(l_Lean_registerTagAttribute___lam__7), 3, 2);
lean_closure_set(v___f_2013_, 0, v_a_1988_);
lean_closure_set(v___f_2013_, 1, v_decl_1991_);
v___x_2050_ = l_Lean_Attribute_Builtin_ensureNoArgs(v_stx_1992_, v___y_1994_, v___y_1995_);
if (lean_obj_tag(v___x_2050_) == 0)
{
uint8_t v___x_2051_; uint8_t v___x_2052_; 
lean_dec_ref_known(v___x_2050_, 1);
v___x_2051_ = 0;
v___x_2052_ = l_Lean_instBEqAttributeKind_beq(v_kind_1993_, v___x_2051_);
if (v___x_2052_ == 0)
{
lean_object* v___x_2053_; 
lean_dec_ref(v___f_2013_);
lean_dec(v_decl_1991_);
lean_dec_ref(v_validate_1989_);
lean_dec_ref(v_a_1988_);
v___x_2053_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg(v_name_1990_, v_kind_1993_, v___y_1994_, v___y_1995_);
return v___x_2053_;
}
else
{
goto v___jp_2045_;
}
}
else
{
lean_dec_ref(v___f_2013_);
lean_dec(v_decl_1991_);
lean_dec(v_name_1990_);
lean_dec_ref(v_validate_1989_);
lean_dec_ref(v_a_1988_);
return v___x_2050_;
}
v___jp_1997_:
{
lean_object* v___x_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; 
v___x_2009_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1);
v___x_2010_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_2010_, 0, v___y_2008_);
lean_ctor_set(v___x_2010_, 1, v_nextMacroScope_1998_);
lean_ctor_set(v___x_2010_, 2, v_ngen_1999_);
lean_ctor_set(v___x_2010_, 3, v_auxDeclNGen_2000_);
lean_ctor_set(v___x_2010_, 4, v_traceState_2001_);
lean_ctor_set(v___x_2010_, 5, v___x_2009_);
lean_ctor_set(v___x_2010_, 6, v_recordedDeps_2002_);
lean_ctor_set(v___x_2010_, 7, v_messages_2003_);
lean_ctor_set(v___x_2010_, 8, v_infoState_2004_);
lean_ctor_set(v___x_2010_, 9, v_snapshotTasks_2005_);
v___x_2011_ = lean_st_ref_put(v___y_2007_, v___x_2010_);
v___x_2012_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2012_, 0, v___y_2006_);
return v___x_2012_;
}
v___jp_2014_:
{
lean_object* v___x_2017_; 
lean_inc(v___y_2016_);
lean_inc_ref(v___y_2015_);
lean_inc(v_decl_1991_);
v___x_2017_ = lean_apply_4(v_validate_1989_, v_decl_1991_, v___y_2015_, v___y_2016_, lean_box(0));
if (lean_obj_tag(v___x_2017_) == 0)
{
lean_object* v___x_2018_; lean_object* v_toEnvExtension_2019_; lean_object* v_env_2020_; lean_object* v_nextMacroScope_2021_; lean_object* v_ngen_2022_; lean_object* v_auxDeclNGen_2023_; lean_object* v_traceState_2024_; lean_object* v_recordedDeps_2025_; lean_object* v_messages_2026_; lean_object* v_infoState_2027_; lean_object* v_snapshotTasks_2028_; lean_object* v_asyncMode_2029_; uint8_t v_logWrites_2030_; lean_object* v___x_2031_; uint8_t v___x_2032_; 
lean_dec_ref_known(v___x_2017_, 1);
v___x_2018_ = lean_st_ref_take(v___y_2016_);
v_toEnvExtension_2019_ = lean_ctor_get(v_a_1988_, 0);
lean_inc_ref(v_toEnvExtension_2019_);
lean_dec_ref(v_a_1988_);
v_env_2020_ = lean_ctor_get(v___x_2018_, 0);
lean_inc_ref(v_env_2020_);
v_nextMacroScope_2021_ = lean_ctor_get(v___x_2018_, 1);
lean_inc(v_nextMacroScope_2021_);
v_ngen_2022_ = lean_ctor_get(v___x_2018_, 2);
lean_inc_ref(v_ngen_2022_);
v_auxDeclNGen_2023_ = lean_ctor_get(v___x_2018_, 3);
lean_inc_ref(v_auxDeclNGen_2023_);
v_traceState_2024_ = lean_ctor_get(v___x_2018_, 4);
lean_inc_ref(v_traceState_2024_);
v_recordedDeps_2025_ = lean_ctor_get(v___x_2018_, 6);
lean_inc_ref(v_recordedDeps_2025_);
v_messages_2026_ = lean_ctor_get(v___x_2018_, 7);
lean_inc_ref(v_messages_2026_);
v_infoState_2027_ = lean_ctor_get(v___x_2018_, 8);
lean_inc_ref(v_infoState_2027_);
v_snapshotTasks_2028_ = lean_ctor_get(v___x_2018_, 9);
lean_inc_ref(v_snapshotTasks_2028_);
lean_dec(v___x_2018_);
v_asyncMode_2029_ = lean_ctor_get(v_toEnvExtension_2019_, 2);
lean_inc(v_asyncMode_2029_);
v_logWrites_2030_ = lean_ctor_get_uint8(v_toEnvExtension_2019_, sizeof(void*)*6);
v___x_2031_ = lean_box(0);
v___x_2032_ = 1;
if (v_logWrites_2030_ == 0)
{
lean_object* v___x_2033_; 
v___x_2033_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_2019_, v_env_2020_, v___f_2013_, v_asyncMode_2029_, v_decl_1991_, v___x_2032_);
lean_dec(v_asyncMode_2029_);
v_nextMacroScope_1998_ = v_nextMacroScope_2021_;
v_ngen_1999_ = v_ngen_2022_;
v_auxDeclNGen_2000_ = v_auxDeclNGen_2023_;
v_traceState_2001_ = v_traceState_2024_;
v_recordedDeps_2002_ = v_recordedDeps_2025_;
v_messages_2003_ = v_messages_2026_;
v_infoState_2004_ = v_infoState_2027_;
v_snapshotTasks_2005_ = v_snapshotTasks_2028_;
v___y_2006_ = v___x_2031_;
v___y_2007_ = v___y_2016_;
v___y_2008_ = v___x_2033_;
goto v___jp_1997_;
}
else
{
lean_object* v___x_2034_; lean_object* v___x_2035_; 
lean_inc(v_decl_1991_);
v___x_2034_ = l_Lean_Environment_logDeclChange(v_env_2020_, v_decl_1991_);
v___x_2035_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_2019_, v___x_2034_, v___f_2013_, v_asyncMode_2029_, v_decl_1991_, v___x_2032_);
lean_dec(v_asyncMode_2029_);
v_nextMacroScope_1998_ = v_nextMacroScope_2021_;
v_ngen_1999_ = v_ngen_2022_;
v_auxDeclNGen_2000_ = v_auxDeclNGen_2023_;
v_traceState_2001_ = v_traceState_2024_;
v_recordedDeps_2002_ = v_recordedDeps_2025_;
v_messages_2003_ = v_messages_2026_;
v_infoState_2004_ = v_infoState_2027_;
v_snapshotTasks_2005_ = v_snapshotTasks_2028_;
v___y_2006_ = v___x_2031_;
v___y_2007_ = v___y_2016_;
v___y_2008_ = v___x_2035_;
goto v___jp_1997_;
}
}
else
{
lean_dec_ref(v___f_2013_);
lean_dec(v_decl_1991_);
lean_dec_ref(v_a_1988_);
return v___x_2017_;
}
}
v___jp_2036_:
{
lean_object* v_toEnvExtension_2040_; lean_object* v_asyncMode_2041_; uint8_t v___x_2042_; 
v_toEnvExtension_2040_ = lean_ctor_get(v_a_1988_, 0);
v_asyncMode_2041_ = lean_ctor_get(v_toEnvExtension_2040_, 2);
lean_inc(v_decl_1991_);
lean_inc_ref(v___y_2037_);
v___x_2042_ = l_Lean_EnvExtension_asyncMayModify___redArg(v___y_2037_, v_decl_1991_, v_asyncMode_2041_);
if (v___x_2042_ == 0)
{
lean_object* v___x_2043_; lean_object* v___x_2044_; 
lean_dec_ref(v___f_2013_);
lean_dec_ref(v_validate_1989_);
lean_dec_ref(v_a_1988_);
v___x_2043_ = l_Lean_Environment_asyncPrefix_x3f(v___y_2037_);
v___x_2044_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___redArg(v_name_1990_, v_decl_1991_, v___x_2043_, v___y_2038_, v___y_2039_);
return v___x_2044_;
}
else
{
lean_dec_ref(v___y_2037_);
lean_dec(v_name_1990_);
v___y_2015_ = v___y_2038_;
v___y_2016_ = v___y_2039_;
goto v___jp_2014_;
}
}
v___jp_2045_:
{
lean_object* v___x_2046_; lean_object* v_env_2047_; lean_object* v___x_2048_; 
v___x_2046_ = lean_st_ref_get(v___y_1995_);
v_env_2047_ = lean_ctor_get(v___x_2046_, 0);
lean_inc_ref(v_env_2047_);
lean_dec(v___x_2046_);
v___x_2048_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2047_, v_decl_1991_);
if (lean_obj_tag(v___x_2048_) == 0)
{
v___y_2037_ = v_env_2047_;
v___y_2038_ = v___y_1994_;
v___y_2039_ = v___y_1995_;
goto v___jp_2036_;
}
else
{
lean_object* v___x_2049_; 
lean_dec_ref_known(v___x_2048_, 1);
lean_dec_ref(v_env_2047_);
lean_dec_ref(v___f_2013_);
lean_dec_ref(v_validate_1989_);
lean_dec_ref(v_a_1988_);
v___x_2049_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg(v_name_1990_, v_decl_1991_, v___y_1994_, v___y_1995_);
return v___x_2049_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__8___boxed(lean_object* v_a_2054_, lean_object* v_validate_2055_, lean_object* v_name_2056_, lean_object* v_decl_2057_, lean_object* v_stx_2058_, lean_object* v_kind_2059_, lean_object* v___y_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_){
_start:
{
uint8_t v_kind_boxed_2063_; lean_object* v_res_2064_; 
v_kind_boxed_2063_ = lean_unbox(v_kind_2059_);
v_res_2064_ = l_Lean_registerTagAttribute___lam__8(v_a_2054_, v_validate_2055_, v_name_2056_, v_decl_2057_, v_stx_2058_, v_kind_boxed_2063_, v___y_2060_, v___y_2061_);
lean_dec(v___y_2061_);
lean_dec_ref(v___y_2060_);
return v_res_2064_;
}
}
static lean_object* _init_l_Lean_registerTagAttribute___closed__5(void){
_start:
{
lean_object* v___x_2070_; lean_object* v___f_2071_; 
v___x_2070_ = l_Lean_NameSet_empty;
v___f_2071_ = lean_alloc_closure((void*)(l_Lean_registerTagAttribute___lam__5___boxed), 4, 1);
lean_closure_set(v___f_2071_, 0, v___x_2070_);
return v___f_2071_;
}
}
static lean_object* _init_l_Lean_registerTagAttribute___closed__6(void){
_start:
{
lean_object* v___x_2072_; lean_object* v___f_2073_; 
v___x_2072_ = l_Lean_NameSet_empty;
v___f_2073_ = lean_alloc_closure((void*)(l_Lean_registerTagAttribute___lam__6___boxed), 2, 1);
lean_closure_set(v___f_2073_, 0, v___x_2072_);
return v___f_2073_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute(lean_object* v_name_2076_, lean_object* v_descr_2077_, lean_object* v_validate_2078_, lean_object* v_ref_2079_, uint8_t v_applicationTime_2080_, lean_object* v_asyncMode_2081_, uint8_t v_logWrites_2082_){
_start:
{
lean_object* v___f_2084_; lean_object* v___f_2085_; lean_object* v___f_2086_; lean_object* v___f_2087_; lean_object* v___f_2088_; lean_object* v___f_2089_; lean_object* v___f_2090_; lean_object* v___x_2091_; uint8_t v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; 
v___f_2084_ = ((lean_object*)(l_Lean_registerTagAttribute___closed__0));
v___f_2085_ = ((lean_object*)(l_Lean_registerTagAttribute___closed__2));
v___f_2086_ = ((lean_object*)(l_Lean_registerTagAttribute___closed__3));
v___f_2087_ = ((lean_object*)(l_Lean_registerTagAttribute___closed__4));
lean_inc(v_name_2076_);
v___f_2088_ = lean_alloc_closure((void*)(l_Lean_registerTagAttribute___lam__4___boxed), 5, 1);
lean_closure_set(v___f_2088_, 0, v_name_2076_);
v___f_2089_ = lean_obj_once(&l_Lean_registerTagAttribute___closed__5, &l_Lean_registerTagAttribute___closed__5_once, _init_l_Lean_registerTagAttribute___closed__5);
v___f_2090_ = lean_obj_once(&l_Lean_registerTagAttribute___closed__6, &l_Lean_registerTagAttribute___closed__6_once, _init_l_Lean_registerTagAttribute___closed__6);
v___x_2091_ = ((lean_object*)(l_Lean_registerTagAttribute___closed__7));
v___x_2092_ = 0;
lean_inc(v_ref_2079_);
v___x_2093_ = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(v___x_2093_, 0, v_ref_2079_);
lean_ctor_set(v___x_2093_, 1, v___f_2090_);
lean_ctor_set(v___x_2093_, 2, v___f_2089_);
lean_ctor_set(v___x_2093_, 3, v___f_2087_);
lean_ctor_set(v___x_2093_, 4, v___f_2086_);
lean_ctor_set(v___x_2093_, 5, v___f_2085_);
lean_ctor_set(v___x_2093_, 6, v_asyncMode_2081_);
lean_ctor_set(v___x_2093_, 7, v___x_2091_);
lean_ctor_set_uint8(v___x_2093_, sizeof(void*)*8, v___x_2092_);
lean_ctor_set_uint8(v___x_2093_, sizeof(void*)*8 + 1, v_logWrites_2082_);
v___x_2094_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2094_, 0, v___x_2093_);
lean_ctor_set(v___x_2094_, 1, v___f_2084_);
v___x_2095_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_2094_);
if (lean_obj_tag(v___x_2095_) == 0)
{
lean_object* v_a_2096_; lean_object* v___f_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; 
v_a_2096_ = lean_ctor_get(v___x_2095_, 0);
lean_inc_n(v_a_2096_, 2);
lean_dec_ref_known(v___x_2095_, 1);
lean_inc(v_name_2076_);
v___f_2097_ = lean_alloc_closure((void*)(l_Lean_registerTagAttribute___lam__8___boxed), 9, 3);
lean_closure_set(v___f_2097_, 0, v_a_2096_);
lean_closure_set(v___f_2097_, 1, v_validate_2078_);
lean_closure_set(v___f_2097_, 2, v_name_2076_);
v___x_2098_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2098_, 0, v_ref_2079_);
lean_ctor_set(v___x_2098_, 1, v_name_2076_);
lean_ctor_set(v___x_2098_, 2, v_descr_2077_);
lean_ctor_set_uint8(v___x_2098_, sizeof(void*)*3, v_applicationTime_2080_);
v___x_2099_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2099_, 0, v___x_2098_);
lean_ctor_set(v___x_2099_, 1, v___f_2097_);
lean_ctor_set(v___x_2099_, 2, v___f_2088_);
lean_inc_ref(v___x_2099_);
v___x_2100_ = l_Lean_registerBuiltinAttribute(v___x_2099_);
if (lean_obj_tag(v___x_2100_) == 0)
{
lean_object* v___x_2102_; uint8_t v_isShared_2103_; uint8_t v_isSharedCheck_2108_; 
v_isSharedCheck_2108_ = !lean_is_exclusive(v___x_2100_);
if (v_isSharedCheck_2108_ == 0)
{
lean_object* v_unused_2109_; 
v_unused_2109_ = lean_ctor_get(v___x_2100_, 0);
lean_dec(v_unused_2109_);
v___x_2102_ = v___x_2100_;
v_isShared_2103_ = v_isSharedCheck_2108_;
goto v_resetjp_2101_;
}
else
{
lean_dec(v___x_2100_);
v___x_2102_ = lean_box(0);
v_isShared_2103_ = v_isSharedCheck_2108_;
goto v_resetjp_2101_;
}
v_resetjp_2101_:
{
lean_object* v___x_2104_; lean_object* v___x_2106_; 
v___x_2104_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2104_, 0, v___x_2099_);
lean_ctor_set(v___x_2104_, 1, v_a_2096_);
if (v_isShared_2103_ == 0)
{
lean_ctor_set(v___x_2102_, 0, v___x_2104_);
v___x_2106_ = v___x_2102_;
goto v_reusejp_2105_;
}
else
{
lean_object* v_reuseFailAlloc_2107_; 
v_reuseFailAlloc_2107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2107_, 0, v___x_2104_);
v___x_2106_ = v_reuseFailAlloc_2107_;
goto v_reusejp_2105_;
}
v_reusejp_2105_:
{
return v___x_2106_;
}
}
}
else
{
lean_object* v_a_2110_; lean_object* v___x_2112_; uint8_t v_isShared_2113_; uint8_t v_isSharedCheck_2117_; 
lean_dec_ref_known(v___x_2099_, 3);
lean_dec(v_a_2096_);
v_a_2110_ = lean_ctor_get(v___x_2100_, 0);
v_isSharedCheck_2117_ = !lean_is_exclusive(v___x_2100_);
if (v_isSharedCheck_2117_ == 0)
{
v___x_2112_ = v___x_2100_;
v_isShared_2113_ = v_isSharedCheck_2117_;
goto v_resetjp_2111_;
}
else
{
lean_inc(v_a_2110_);
lean_dec(v___x_2100_);
v___x_2112_ = lean_box(0);
v_isShared_2113_ = v_isSharedCheck_2117_;
goto v_resetjp_2111_;
}
v_resetjp_2111_:
{
lean_object* v___x_2115_; 
if (v_isShared_2113_ == 0)
{
v___x_2115_ = v___x_2112_;
goto v_reusejp_2114_;
}
else
{
lean_object* v_reuseFailAlloc_2116_; 
v_reuseFailAlloc_2116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2116_, 0, v_a_2110_);
v___x_2115_ = v_reuseFailAlloc_2116_;
goto v_reusejp_2114_;
}
v_reusejp_2114_:
{
return v___x_2115_;
}
}
}
}
else
{
lean_object* v_a_2118_; lean_object* v___x_2120_; uint8_t v_isShared_2121_; uint8_t v_isSharedCheck_2125_; 
lean_dec_ref(v___f_2088_);
lean_dec(v_ref_2079_);
lean_dec_ref(v_validate_2078_);
lean_dec_ref(v_descr_2077_);
lean_dec(v_name_2076_);
v_a_2118_ = lean_ctor_get(v___x_2095_, 0);
v_isSharedCheck_2125_ = !lean_is_exclusive(v___x_2095_);
if (v_isSharedCheck_2125_ == 0)
{
v___x_2120_ = v___x_2095_;
v_isShared_2121_ = v_isSharedCheck_2125_;
goto v_resetjp_2119_;
}
else
{
lean_inc(v_a_2118_);
lean_dec(v___x_2095_);
v___x_2120_ = lean_box(0);
v_isShared_2121_ = v_isSharedCheck_2125_;
goto v_resetjp_2119_;
}
v_resetjp_2119_:
{
lean_object* v___x_2123_; 
if (v_isShared_2121_ == 0)
{
v___x_2123_ = v___x_2120_;
goto v_reusejp_2122_;
}
else
{
lean_object* v_reuseFailAlloc_2124_; 
v_reuseFailAlloc_2124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2124_, 0, v_a_2118_);
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
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___boxed(lean_object* v_name_2126_, lean_object* v_descr_2127_, lean_object* v_validate_2128_, lean_object* v_ref_2129_, lean_object* v_applicationTime_2130_, lean_object* v_asyncMode_2131_, lean_object* v_logWrites_2132_, lean_object* v_a_2133_){
_start:
{
uint8_t v_applicationTime_boxed_2134_; uint8_t v_logWrites_boxed_2135_; lean_object* v_res_2136_; 
v_applicationTime_boxed_2134_ = lean_unbox(v_applicationTime_2130_);
v_logWrites_boxed_2135_ = lean_unbox(v_logWrites_2132_);
v_res_2136_ = l_Lean_registerTagAttribute(v_name_2126_, v_descr_2127_, v_validate_2128_, v_ref_2129_, v_applicationTime_boxed_2134_, v_asyncMode_2131_, v_logWrites_boxed_2135_);
return v_res_2136_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerTagAttribute_spec__1(lean_object* v_init_2137_, lean_object* v_t_2138_){
_start:
{
lean_object* v___x_2139_; 
v___x_2139_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerTagAttribute_spec__1_spec__1(v_init_2137_, v_t_2138_);
return v___x_2139_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3(lean_object* v_n_2140_, lean_object* v_as_2141_, lean_object* v_lo_2142_, lean_object* v_hi_2143_, lean_object* v_w_2144_, lean_object* v_hlo_2145_, lean_object* v_hhi_2146_){
_start:
{
lean_object* v___x_2147_; 
v___x_2147_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___redArg(v_n_2140_, v_as_2141_, v_lo_2142_, v_hi_2143_);
return v___x_2147_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___boxed(lean_object* v_n_2148_, lean_object* v_as_2149_, lean_object* v_lo_2150_, lean_object* v_hi_2151_, lean_object* v_w_2152_, lean_object* v_hlo_2153_, lean_object* v_hhi_2154_){
_start:
{
lean_object* v_res_2155_; 
v_res_2155_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3(v_n_2148_, v_as_2149_, v_lo_2150_, v_hi_2151_, v_w_2152_, v_hlo_2153_, v_hhi_2154_);
lean_dec(v_hi_2151_);
lean_dec(v_n_2148_);
return v_res_2155_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4(lean_object* v_00_u03b1_2156_, lean_object* v_attrName_2157_, lean_object* v_declName_2158_, lean_object* v_asyncPrefix_x3f_2159_, lean_object* v___y_2160_, lean_object* v___y_2161_){
_start:
{
lean_object* v___x_2163_; 
v___x_2163_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___redArg(v_attrName_2157_, v_declName_2158_, v_asyncPrefix_x3f_2159_, v___y_2160_, v___y_2161_);
return v___x_2163_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___boxed(lean_object* v_00_u03b1_2164_, lean_object* v_attrName_2165_, lean_object* v_declName_2166_, lean_object* v_asyncPrefix_x3f_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_){
_start:
{
lean_object* v_res_2171_; 
v_res_2171_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4(v_00_u03b1_2164_, v_attrName_2165_, v_declName_2166_, v_asyncPrefix_x3f_2167_, v___y_2168_, v___y_2169_);
lean_dec(v___y_2169_);
lean_dec_ref(v___y_2168_);
return v_res_2171_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5(lean_object* v_00_u03b1_2172_, lean_object* v_attrName_2173_, lean_object* v_declName_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_){
_start:
{
lean_object* v___x_2178_; 
v___x_2178_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg(v_attrName_2173_, v_declName_2174_, v___y_2175_, v___y_2176_);
return v___x_2178_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___boxed(lean_object* v_00_u03b1_2179_, lean_object* v_attrName_2180_, lean_object* v_declName_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_, lean_object* v___y_2184_){
_start:
{
lean_object* v_res_2185_; 
v_res_2185_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5(v_00_u03b1_2179_, v_attrName_2180_, v_declName_2181_, v___y_2182_, v___y_2183_);
lean_dec(v___y_2183_);
lean_dec_ref(v___y_2182_);
return v_res_2185_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6(lean_object* v_00_u03b1_2186_, lean_object* v_name_2187_, uint8_t v_kind_2188_, lean_object* v___y_2189_, lean_object* v___y_2190_){
_start:
{
lean_object* v___x_2192_; 
v___x_2192_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg(v_name_2187_, v_kind_2188_, v___y_2189_, v___y_2190_);
return v___x_2192_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___boxed(lean_object* v_00_u03b1_2193_, lean_object* v_name_2194_, lean_object* v_kind_2195_, lean_object* v___y_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_){
_start:
{
uint8_t v_kind_boxed_2199_; lean_object* v_res_2200_; 
v_kind_boxed_2199_ = lean_unbox(v_kind_2195_);
v_res_2200_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6(v_00_u03b1_2193_, v_name_2194_, v_kind_boxed_2199_, v___y_2196_, v___y_2197_);
lean_dec(v___y_2197_);
lean_dec_ref(v___y_2196_);
return v_res_2200_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4(lean_object* v_n_2201_, lean_object* v_lo_2202_, lean_object* v_hi_2203_, lean_object* v_hhi_2204_, lean_object* v_pivot_2205_, lean_object* v_as_2206_, lean_object* v_i_2207_, lean_object* v_k_2208_, lean_object* v_ilo_2209_, lean_object* v_ik_2210_, lean_object* v_w_2211_){
_start:
{
lean_object* v___x_2212_; 
v___x_2212_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4___redArg(v_hi_2203_, v_pivot_2205_, v_as_2206_, v_i_2207_, v_k_2208_);
return v___x_2212_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4___boxed(lean_object* v_n_2213_, lean_object* v_lo_2214_, lean_object* v_hi_2215_, lean_object* v_hhi_2216_, lean_object* v_pivot_2217_, lean_object* v_as_2218_, lean_object* v_i_2219_, lean_object* v_k_2220_, lean_object* v_ilo_2221_, lean_object* v_ik_2222_, lean_object* v_w_2223_){
_start:
{
lean_object* v_res_2224_; 
v_res_2224_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4(v_n_2213_, v_lo_2214_, v_hi_2215_, v_hhi_2216_, v_pivot_2217_, v_as_2218_, v_i_2219_, v_k_2220_, v_ilo_2221_, v_ik_2222_, v_w_2223_);
lean_dec(v_pivot_2217_);
lean_dec(v_hi_2215_);
lean_dec(v_lo_2214_);
lean_dec(v_n_2213_);
return v_res_2224_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg___lam__0(lean_object* v_addEntryFn_2225_, lean_object* v_decl_2226_, lean_object* v_s_2227_){
_start:
{
lean_object* v_importedEntries_2228_; lean_object* v_state_2229_; lean_object* v___x_2231_; uint8_t v_isShared_2232_; uint8_t v_isSharedCheck_2237_; 
v_importedEntries_2228_ = lean_ctor_get(v_s_2227_, 0);
v_state_2229_ = lean_ctor_get(v_s_2227_, 1);
v_isSharedCheck_2237_ = !lean_is_exclusive(v_s_2227_);
if (v_isSharedCheck_2237_ == 0)
{
v___x_2231_ = v_s_2227_;
v_isShared_2232_ = v_isSharedCheck_2237_;
goto v_resetjp_2230_;
}
else
{
lean_inc(v_state_2229_);
lean_inc(v_importedEntries_2228_);
lean_dec(v_s_2227_);
v___x_2231_ = lean_box(0);
v_isShared_2232_ = v_isSharedCheck_2237_;
goto v_resetjp_2230_;
}
v_resetjp_2230_:
{
lean_object* v_state_2233_; lean_object* v___x_2235_; 
v_state_2233_ = lean_apply_2(v_addEntryFn_2225_, v_state_2229_, v_decl_2226_);
if (v_isShared_2232_ == 0)
{
lean_ctor_set(v___x_2231_, 1, v_state_2233_);
v___x_2235_ = v___x_2231_;
goto v_reusejp_2234_;
}
else
{
lean_object* v_reuseFailAlloc_2236_; 
v_reuseFailAlloc_2236_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2236_, 0, v_importedEntries_2228_);
lean_ctor_set(v_reuseFailAlloc_2236_, 1, v_state_2233_);
v___x_2235_ = v_reuseFailAlloc_2236_;
goto v_reusejp_2234_;
}
v_reusejp_2234_:
{
return v___x_2235_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg___lam__1(lean_object* v_attr_2238_, lean_object* v_decl_2239_, lean_object* v_env_2240_){
_start:
{
lean_object* v_ext_2241_; lean_object* v_toEnvExtension_2242_; lean_object* v_addEntryFn_2243_; lean_object* v_asyncMode_2244_; uint8_t v_logWrites_2245_; lean_object* v___f_2246_; uint8_t v___x_2247_; 
v_ext_2241_ = lean_ctor_get(v_attr_2238_, 1);
lean_inc_ref(v_ext_2241_);
lean_dec_ref(v_attr_2238_);
v_toEnvExtension_2242_ = lean_ctor_get(v_ext_2241_, 0);
lean_inc_ref(v_toEnvExtension_2242_);
v_addEntryFn_2243_ = lean_ctor_get(v_ext_2241_, 3);
lean_inc(v_addEntryFn_2243_);
lean_dec_ref(v_ext_2241_);
v_asyncMode_2244_ = lean_ctor_get(v_toEnvExtension_2242_, 2);
lean_inc(v_asyncMode_2244_);
v_logWrites_2245_ = lean_ctor_get_uint8(v_toEnvExtension_2242_, sizeof(void*)*6);
lean_inc(v_decl_2239_);
v___f_2246_ = lean_alloc_closure((void*)(l_Lean_TagAttribute_setTag___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2246_, 0, v_addEntryFn_2243_);
lean_closure_set(v___f_2246_, 1, v_decl_2239_);
v___x_2247_ = 1;
if (v_logWrites_2245_ == 0)
{
lean_object* v___x_2248_; 
v___x_2248_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_2242_, v_env_2240_, v___f_2246_, v_asyncMode_2244_, v_decl_2239_, v___x_2247_);
lean_dec(v_asyncMode_2244_);
return v___x_2248_;
}
else
{
lean_object* v___x_2249_; lean_object* v___x_2250_; 
lean_inc_ref(v_toEnvExtension_2242_);
v___x_2249_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_2242_, v_env_2240_);
lean_dec_ref(v_env_2240_);
v___x_2250_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_2242_, v___x_2249_, v___f_2246_, v_asyncMode_2244_, v_decl_2239_, v___x_2247_);
lean_dec(v_asyncMode_2244_);
return v___x_2250_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg___lam__2(lean_object* v_modifyEnv_2251_, lean_object* v___f_2252_, lean_object* v_____r_2253_){
_start:
{
lean_object* v___x_2254_; 
v___x_2254_ = lean_apply_1(v_modifyEnv_2251_, v___f_2252_);
return v___x_2254_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg___lam__3(lean_object* v_attr_2255_, lean_object* v_env_2256_, lean_object* v_decl_2257_, lean_object* v_inst_2258_, lean_object* v_inst_2259_, lean_object* v_toBind_2260_, lean_object* v___f_2261_, lean_object* v_modifyEnv_2262_, lean_object* v___f_2263_, lean_object* v_____r_2264_){
_start:
{
lean_object* v_ext_2265_; lean_object* v_toEnvExtension_2266_; lean_object* v_attr_2267_; lean_object* v_asyncMode_2268_; uint8_t v___x_2269_; 
v_ext_2265_ = lean_ctor_get(v_attr_2255_, 1);
v_toEnvExtension_2266_ = lean_ctor_get(v_ext_2265_, 0);
lean_inc_ref(v_toEnvExtension_2266_);
v_attr_2267_ = lean_ctor_get(v_attr_2255_, 0);
lean_inc_ref(v_attr_2267_);
lean_dec_ref(v_attr_2255_);
v_asyncMode_2268_ = lean_ctor_get(v_toEnvExtension_2266_, 2);
lean_inc(v_asyncMode_2268_);
lean_dec_ref(v_toEnvExtension_2266_);
lean_inc(v_decl_2257_);
lean_inc_ref(v_env_2256_);
v___x_2269_ = l_Lean_EnvExtension_asyncMayModify___redArg(v_env_2256_, v_decl_2257_, v_asyncMode_2268_);
lean_dec(v_asyncMode_2268_);
if (v___x_2269_ == 0)
{
lean_object* v_toAttributeImplCore_2270_; lean_object* v_name_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; 
lean_dec_ref(v___f_2263_);
lean_dec(v_modifyEnv_2262_);
v_toAttributeImplCore_2270_ = lean_ctor_get(v_attr_2267_, 0);
lean_inc_ref(v_toAttributeImplCore_2270_);
lean_dec_ref(v_attr_2267_);
v_name_2271_ = lean_ctor_get(v_toAttributeImplCore_2270_, 1);
lean_inc(v_name_2271_);
lean_dec_ref(v_toAttributeImplCore_2270_);
v___x_2272_ = l_Lean_Environment_asyncPrefix_x3f(v_env_2256_);
v___x_2273_ = l_Lean_throwAttrNotInAsyncCtx___redArg(v_inst_2258_, v_inst_2259_, v_name_2271_, v_decl_2257_, v___x_2272_);
v___x_2274_ = lean_apply_4(v_toBind_2260_, lean_box(0), lean_box(0), v___x_2273_, v___f_2261_);
return v___x_2274_;
}
else
{
lean_object* v___x_2275_; 
lean_dec_ref(v_attr_2267_);
lean_dec(v___f_2261_);
lean_dec(v_toBind_2260_);
lean_dec_ref(v_inst_2259_);
lean_dec_ref(v_inst_2258_);
lean_dec(v_decl_2257_);
lean_dec_ref(v_env_2256_);
v___x_2275_ = lean_apply_1(v_modifyEnv_2262_, v___f_2263_);
return v___x_2275_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg___lam__4(lean_object* v___f_2276_, lean_object* v_____r_2277_){
_start:
{
lean_object* v___x_2278_; 
v___x_2278_ = lean_apply_1(v___f_2276_, v_____r_2277_);
return v___x_2278_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg___lam__5(lean_object* v_attr_2279_, lean_object* v_decl_2280_, lean_object* v_inst_2281_, lean_object* v_inst_2282_, lean_object* v_toBind_2283_, lean_object* v___f_2284_, lean_object* v_modifyEnv_2285_, lean_object* v___f_2286_, lean_object* v_env_2287_){
_start:
{
lean_object* v___f_2288_; lean_object* v___x_2289_; 
lean_inc_ref(v___f_2286_);
lean_inc(v_modifyEnv_2285_);
lean_inc(v___f_2284_);
lean_inc(v_toBind_2283_);
lean_inc_ref(v_inst_2282_);
lean_inc_ref(v_inst_2281_);
lean_inc(v_decl_2280_);
lean_inc_ref(v_env_2287_);
lean_inc_ref(v_attr_2279_);
v___f_2288_ = lean_alloc_closure((void*)(l_Lean_TagAttribute_setTag___redArg___lam__3), 10, 9);
lean_closure_set(v___f_2288_, 0, v_attr_2279_);
lean_closure_set(v___f_2288_, 1, v_env_2287_);
lean_closure_set(v___f_2288_, 2, v_decl_2280_);
lean_closure_set(v___f_2288_, 3, v_inst_2281_);
lean_closure_set(v___f_2288_, 4, v_inst_2282_);
lean_closure_set(v___f_2288_, 5, v_toBind_2283_);
lean_closure_set(v___f_2288_, 6, v___f_2284_);
lean_closure_set(v___f_2288_, 7, v_modifyEnv_2285_);
lean_closure_set(v___f_2288_, 8, v___f_2286_);
v___x_2289_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2287_, v_decl_2280_);
if (lean_obj_tag(v___x_2289_) == 0)
{
lean_object* v___x_2290_; lean_object* v___x_2291_; 
lean_dec_ref(v___f_2288_);
v___x_2290_ = lean_box(0);
v___x_2291_ = l_Lean_TagAttribute_setTag___redArg___lam__3(v_attr_2279_, v_env_2287_, v_decl_2280_, v_inst_2281_, v_inst_2282_, v_toBind_2283_, v___f_2284_, v_modifyEnv_2285_, v___f_2286_, v___x_2290_);
return v___x_2291_;
}
else
{
lean_object* v_attr_2292_; lean_object* v_toAttributeImplCore_2293_; lean_object* v_name_2294_; lean_object* v___f_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; 
lean_dec_ref_known(v___x_2289_, 1);
lean_dec_ref(v_env_2287_);
lean_dec_ref(v___f_2286_);
lean_dec(v_modifyEnv_2285_);
lean_dec(v___f_2284_);
v_attr_2292_ = lean_ctor_get(v_attr_2279_, 0);
lean_inc_ref(v_attr_2292_);
lean_dec_ref(v_attr_2279_);
v_toAttributeImplCore_2293_ = lean_ctor_get(v_attr_2292_, 0);
lean_inc_ref(v_toAttributeImplCore_2293_);
lean_dec_ref(v_attr_2292_);
v_name_2294_ = lean_ctor_get(v_toAttributeImplCore_2293_, 1);
lean_inc(v_name_2294_);
lean_dec_ref(v_toAttributeImplCore_2293_);
v___f_2295_ = lean_alloc_closure((void*)(l_Lean_TagAttribute_setTag___redArg___lam__4), 2, 1);
lean_closure_set(v___f_2295_, 0, v___f_2288_);
v___x_2296_ = l_Lean_throwAttrDeclInImportedModule___redArg(v_inst_2281_, v_inst_2282_, v_name_2294_, v_decl_2280_);
v___x_2297_ = lean_apply_4(v_toBind_2283_, lean_box(0), lean_box(0), v___x_2296_, v___f_2295_);
return v___x_2297_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg(lean_object* v_inst_2298_, lean_object* v_inst_2299_, lean_object* v_inst_2300_, lean_object* v_attr_2301_, lean_object* v_decl_2302_){
_start:
{
lean_object* v_toBind_2303_; lean_object* v_getEnv_2304_; lean_object* v_modifyEnv_2305_; lean_object* v___f_2306_; lean_object* v___f_2307_; lean_object* v___f_2308_; lean_object* v___x_2309_; 
v_toBind_2303_ = lean_ctor_get(v_inst_2298_, 1);
lean_inc_n(v_toBind_2303_, 2);
v_getEnv_2304_ = lean_ctor_get(v_inst_2300_, 0);
lean_inc(v_getEnv_2304_);
v_modifyEnv_2305_ = lean_ctor_get(v_inst_2300_, 1);
lean_inc_n(v_modifyEnv_2305_, 2);
lean_dec_ref(v_inst_2300_);
lean_inc(v_decl_2302_);
lean_inc_ref(v_attr_2301_);
v___f_2306_ = lean_alloc_closure((void*)(l_Lean_TagAttribute_setTag___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2306_, 0, v_attr_2301_);
lean_closure_set(v___f_2306_, 1, v_decl_2302_);
lean_inc_ref(v___f_2306_);
v___f_2307_ = lean_alloc_closure((void*)(l_Lean_TagAttribute_setTag___redArg___lam__2), 3, 2);
lean_closure_set(v___f_2307_, 0, v_modifyEnv_2305_);
lean_closure_set(v___f_2307_, 1, v___f_2306_);
v___f_2308_ = lean_alloc_closure((void*)(l_Lean_TagAttribute_setTag___redArg___lam__5), 9, 8);
lean_closure_set(v___f_2308_, 0, v_attr_2301_);
lean_closure_set(v___f_2308_, 1, v_decl_2302_);
lean_closure_set(v___f_2308_, 2, v_inst_2298_);
lean_closure_set(v___f_2308_, 3, v_inst_2299_);
lean_closure_set(v___f_2308_, 4, v_toBind_2303_);
lean_closure_set(v___f_2308_, 5, v___f_2307_);
lean_closure_set(v___f_2308_, 6, v_modifyEnv_2305_);
lean_closure_set(v___f_2308_, 7, v___f_2306_);
v___x_2309_ = lean_apply_4(v_toBind_2303_, lean_box(0), lean_box(0), v_getEnv_2304_, v___f_2308_);
return v___x_2309_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag(lean_object* v_m_2310_, lean_object* v_inst_2311_, lean_object* v_inst_2312_, lean_object* v_inst_2313_, lean_object* v_attr_2314_, lean_object* v_decl_2315_){
_start:
{
lean_object* v___x_2316_; 
v___x_2316_ = l_Lean_TagAttribute_setTag___redArg(v_inst_2311_, v_inst_2312_, v_inst_2313_, v_attr_2314_, v_decl_2315_);
return v___x_2316_;
}
}
LEAN_EXPORT uint8_t l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___redArg(lean_object* v___y_2317_, lean_object* v_as_2318_, lean_object* v_k_2319_, lean_object* v_x_2320_, lean_object* v_x_2321_){
_start:
{
lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v_m_2324_; lean_object* v_a_2325_; uint8_t v___x_2326_; 
v___x_2322_ = lean_nat_add(v_x_2320_, v_x_2321_);
v___x_2323_ = lean_unsigned_to_nat(1u);
v_m_2324_ = lean_nat_shiftr(v___x_2322_, v___x_2323_);
lean_dec(v___x_2322_);
v_a_2325_ = lean_array_fget_borrowed(v_as_2318_, v_m_2324_);
v___x_2326_ = l_Lean_Name_quickLt(v_a_2325_, v_k_2319_);
if (v___x_2326_ == 0)
{
lean_object* v___x_2327_; uint8_t v___x_2328_; 
lean_dec(v_x_2321_);
v___x_2327_ = lean_unsigned_to_nat(0u);
v___x_2328_ = l_Lean_Name_quickLt(v_k_2319_, v_a_2325_);
if (v___x_2328_ == 0)
{
uint8_t v___x_2329_; 
lean_dec(v_m_2324_);
lean_dec(v_x_2320_);
v___x_2329_ = lean_nat_dec_le(v___x_2327_, v___y_2317_);
return v___x_2329_;
}
else
{
uint8_t v___x_2330_; 
v___x_2330_ = lean_nat_dec_eq(v_m_2324_, v___x_2327_);
if (v___x_2330_ == 0)
{
lean_object* v___x_2331_; uint8_t v___x_2332_; 
v___x_2331_ = lean_nat_sub(v_m_2324_, v___x_2323_);
lean_dec(v_m_2324_);
v___x_2332_ = lean_nat_dec_lt(v___x_2331_, v_x_2320_);
if (v___x_2332_ == 0)
{
v_x_2321_ = v___x_2331_;
goto _start;
}
else
{
lean_dec(v___x_2331_);
lean_dec(v_x_2320_);
return v___x_2330_;
}
}
else
{
lean_dec(v_m_2324_);
lean_dec(v_x_2320_);
return v___x_2326_;
}
}
}
else
{
lean_object* v___x_2334_; uint8_t v___x_2335_; 
lean_dec(v_x_2320_);
v___x_2334_ = lean_nat_add(v_m_2324_, v___x_2323_);
lean_dec(v_m_2324_);
v___x_2335_ = lean_nat_dec_le(v___x_2334_, v_x_2321_);
if (v___x_2335_ == 0)
{
lean_dec(v___x_2334_);
lean_dec(v_x_2321_);
return v___x_2335_;
}
else
{
v_x_2320_ = v___x_2334_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___redArg___boxed(lean_object* v___y_2337_, lean_object* v_as_2338_, lean_object* v_k_2339_, lean_object* v_x_2340_, lean_object* v_x_2341_){
_start:
{
uint8_t v_res_2342_; lean_object* v_r_2343_; 
v_res_2342_ = l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___redArg(v___y_2337_, v_as_2338_, v_k_2339_, v_x_2340_, v_x_2341_);
lean_dec(v_k_2339_);
lean_dec_ref(v_as_2338_);
lean_dec(v___y_2337_);
v_r_2343_ = lean_box(v_res_2342_);
return v_r_2343_;
}
}
LEAN_EXPORT uint8_t l_Lean_TagAttribute_hasTag(lean_object* v_attr_2344_, lean_object* v_env_2345_, lean_object* v_decl_2346_){
_start:
{
lean_object* v___x_2347_; lean_object* v___x_2348_; 
v___x_2347_ = lean_box(1);
v___x_2348_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2345_, v_decl_2346_);
if (lean_obj_tag(v___x_2348_) == 0)
{
lean_object* v_ext_2349_; lean_object* v_toEnvExtension_2350_; lean_object* v_asyncMode_2351_; uint8_t v___x_2352_; lean_object* v___x_2353_; uint8_t v___x_2354_; 
v_ext_2349_ = lean_ctor_get(v_attr_2344_, 1);
v_toEnvExtension_2350_ = lean_ctor_get(v_ext_2349_, 0);
v_asyncMode_2351_ = lean_ctor_get(v_toEnvExtension_2350_, 2);
v___x_2352_ = 0;
lean_inc(v_decl_2346_);
v___x_2353_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2347_, v_ext_2349_, v_env_2345_, v_asyncMode_2351_, v_decl_2346_, v___x_2352_);
v___x_2354_ = l_Lean_NameSet_contains(v___x_2353_, v_decl_2346_);
lean_dec(v_decl_2346_);
lean_dec(v___x_2353_);
return v___x_2354_;
}
else
{
lean_object* v_val_2355_; lean_object* v_ext_2356_; uint8_t v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; uint8_t v___x_2361_; 
v_val_2355_ = lean_ctor_get(v___x_2348_, 0);
lean_inc(v_val_2355_);
lean_dec_ref_known(v___x_2348_, 1);
v_ext_2356_ = lean_ctor_get(v_attr_2344_, 1);
v___x_2357_ = 0;
v___x_2358_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_2347_, v_ext_2356_, v_env_2345_, v_val_2355_, v___x_2357_);
lean_dec(v_val_2355_);
lean_dec_ref(v_env_2345_);
v___x_2359_ = lean_unsigned_to_nat(0u);
v___x_2360_ = lean_array_get_size(v___x_2358_);
v___x_2361_ = lean_nat_dec_lt(v___x_2359_, v___x_2360_);
if (v___x_2361_ == 0)
{
lean_dec_ref(v___x_2358_);
lean_dec(v_decl_2346_);
return v___x_2361_;
}
else
{
lean_object* v___x_2362_; lean_object* v___x_2363_; uint8_t v___x_2364_; 
v___x_2362_ = lean_unsigned_to_nat(1u);
v___x_2363_ = lean_nat_sub(v___x_2360_, v___x_2362_);
v___x_2364_ = lean_nat_dec_le(v___x_2359_, v___x_2363_);
if (v___x_2364_ == 0)
{
lean_dec(v___x_2363_);
lean_dec_ref(v___x_2358_);
lean_dec(v_decl_2346_);
return v___x_2364_;
}
else
{
uint8_t v___x_2365_; 
lean_inc(v___x_2363_);
v___x_2365_ = l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___redArg(v___x_2363_, v___x_2358_, v_decl_2346_, v___x_2359_, v___x_2363_);
lean_dec(v_decl_2346_);
lean_dec_ref(v___x_2358_);
lean_dec(v___x_2363_);
return v___x_2365_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_hasTag___boxed(lean_object* v_attr_2366_, lean_object* v_env_2367_, lean_object* v_decl_2368_){
_start:
{
uint8_t v_res_2369_; lean_object* v_r_2370_; 
v_res_2369_ = l_Lean_TagAttribute_hasTag(v_attr_2366_, v_env_2367_, v_decl_2368_);
lean_dec_ref(v_attr_2366_);
v_r_2370_ = lean_box(v_res_2369_);
return v_r_2370_;
}
}
LEAN_EXPORT uint8_t l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0(lean_object* v___y_2371_, lean_object* v_as_2372_, lean_object* v_k_2373_, lean_object* v_x_2374_, lean_object* v_x_2375_, lean_object* v_x_2376_){
_start:
{
uint8_t v___x_2377_; 
v___x_2377_ = l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___redArg(v___y_2371_, v_as_2372_, v_k_2373_, v_x_2374_, v_x_2375_);
return v___x_2377_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___boxed(lean_object* v___y_2378_, lean_object* v_as_2379_, lean_object* v_k_2380_, lean_object* v_x_2381_, lean_object* v_x_2382_, lean_object* v_x_2383_){
_start:
{
uint8_t v_res_2384_; lean_object* v_r_2385_; 
v_res_2384_ = l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0(v___y_2378_, v_as_2379_, v_k_2380_, v_x_2381_, v_x_2382_, v_x_2383_);
lean_dec(v_k_2380_);
lean_dec_ref(v_as_2379_);
lean_dec(v___y_2378_);
v_r_2385_ = lean_box(v_res_2384_);
return v_r_2385_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg___lam__0(lean_object* v_x_2386_, lean_object* v___y_2387_){
_start:
{
lean_object* v___x_2389_; lean_object* v___x_2390_; 
v___x_2389_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___lam__0___closed__1));
v___x_2390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2390_, 0, v___x_2389_);
return v___x_2390_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg___lam__0___boxed(lean_object* v_x_2391_, lean_object* v___y_2392_, lean_object* v___y_2393_){
_start:
{
lean_object* v_res_2394_; 
v_res_2394_ = l_Lean_instInhabitedParametricAttribute_default___redArg___lam__0(v_x_2391_, v___y_2392_);
lean_dec_ref(v___y_2392_);
lean_dec_ref(v_x_2391_);
return v_res_2394_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg___lam__1(lean_object* v_s_2395_, lean_object* v_x_2396_){
_start:
{
lean_inc_ref(v_s_2395_);
return v_s_2395_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg___lam__1___boxed(lean_object* v_s_2397_, lean_object* v_x_2398_){
_start:
{
lean_object* v_res_2399_; 
v_res_2399_ = l_Lean_instInhabitedParametricAttribute_default___redArg___lam__1(v_s_2397_, v_x_2398_);
lean_dec_ref(v_x_2398_);
lean_dec_ref(v_s_2397_);
return v_res_2399_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg___lam__2(lean_object* v_x_2404_, lean_object* v_x_2405_){
_start:
{
lean_object* v___x_2406_; 
v___x_2406_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___redArg___lam__2___closed__1));
return v___x_2406_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg___lam__2___boxed(lean_object* v_x_2407_, lean_object* v_x_2408_){
_start:
{
lean_object* v_res_2409_; 
v_res_2409_ = l_Lean_instInhabitedParametricAttribute_default___redArg___lam__2(v_x_2407_, v_x_2408_);
lean_dec_ref(v_x_2408_);
lean_dec_ref(v_x_2407_);
return v_res_2409_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg___lam__3(lean_object* v_x_2410_){
_start:
{
lean_object* v___x_2411_; 
v___x_2411_ = lean_box(0);
return v___x_2411_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg___lam__3___boxed(lean_object* v_x_2412_){
_start:
{
lean_object* v_res_2413_; 
v_res_2413_ = l_Lean_instInhabitedParametricAttribute_default___redArg___lam__3(v_x_2412_);
lean_dec_ref(v_x_2412_);
return v_res_2413_;
}
}
static lean_object* _init_l_Lean_instInhabitedParametricAttribute_default___redArg___closed__4(void){
_start:
{
lean_object* v___f_2418_; lean_object* v___f_2419_; lean_object* v___f_2420_; lean_object* v___f_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; 
v___f_2418_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___redArg___closed__3));
v___f_2419_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___redArg___closed__2));
v___f_2420_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___redArg___closed__1));
v___f_2421_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___redArg___closed__0));
v___x_2422_ = lean_box(0);
v___x_2423_ = lean_obj_once(&l_Lean_instInhabitedTagAttribute_default___closed__4, &l_Lean_instInhabitedTagAttribute_default___closed__4_once, _init_l_Lean_instInhabitedTagAttribute_default___closed__4);
v___x_2424_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2424_, 0, v___x_2423_);
lean_ctor_set(v___x_2424_, 1, v___x_2422_);
lean_ctor_set(v___x_2424_, 2, v___f_2421_);
lean_ctor_set(v___x_2424_, 3, v___f_2420_);
lean_ctor_set(v___x_2424_, 4, v___f_2419_);
lean_ctor_set(v___x_2424_, 5, v___f_2418_);
return v___x_2424_;
}
}
static lean_object* _init_l_Lean_instInhabitedParametricAttribute_default___redArg___closed__5(void){
_start:
{
uint8_t v___x_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; 
v___x_2425_ = 0;
v___x_2426_ = lean_obj_once(&l_Lean_instInhabitedParametricAttribute_default___redArg___closed__4, &l_Lean_instInhabitedParametricAttribute_default___redArg___closed__4_once, _init_l_Lean_instInhabitedParametricAttribute_default___redArg___closed__4);
v___x_2427_ = ((lean_object*)(l_Lean_instInhabitedAttributeImpl_default));
v___x_2428_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2428_, 0, v___x_2427_);
lean_ctor_set(v___x_2428_, 1, v___x_2426_);
lean_ctor_set_uint8(v___x_2428_, sizeof(void*)*2, v___x_2425_);
return v___x_2428_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg(){
_start:
{
lean_object* v___x_2430_; 
v___x_2430_ = lean_obj_once(&l_Lean_instInhabitedParametricAttribute_default___redArg___closed__5, &l_Lean_instInhabitedParametricAttribute_default___redArg___closed__5_once, _init_l_Lean_instInhabitedParametricAttribute_default___redArg___closed__5);
return v___x_2430_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg___boxed(lean_object* v___dummy_2431_){
_start:
{
lean_object* v_res_2432_; 
v_res_2432_ = l_Lean_instInhabitedParametricAttribute_default___redArg();
return v_res_2432_;
}
}
static lean_object* _init_l_Lean_instInhabitedParametricAttribute_default___closed__0(void){
_start:
{
lean_object* v___x_2433_; 
v___x_2433_ = l_Lean_instInhabitedParametricAttribute_default___redArg();
return v___x_2433_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default(lean_object* v_00_u03b1_2434_){
_start:
{
lean_object* v___x_2435_; 
v___x_2435_ = lean_obj_once(&l_Lean_instInhabitedParametricAttribute_default___closed__0, &l_Lean_instInhabitedParametricAttribute_default___closed__0_once, _init_l_Lean_instInhabitedParametricAttribute_default___closed__0);
return v___x_2435_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute___redArg(){
_start:
{
lean_object* v___x_2437_; 
v___x_2437_ = lean_obj_once(&l_Lean_instInhabitedParametricAttribute_default___closed__0, &l_Lean_instInhabitedParametricAttribute_default___closed__0_once, _init_l_Lean_instInhabitedParametricAttribute_default___closed__0);
return v___x_2437_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute___redArg___boxed(lean_object* v___dummy_2438_){
_start:
{
lean_object* v_res_2439_; 
v_res_2439_ = l_Lean_instInhabitedParametricAttribute___redArg();
return v_res_2439_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute(lean_object* v_a_2440_){
_start:
{
lean_object* v___x_2441_; 
v___x_2441_ = lean_obj_once(&l_Lean_instInhabitedParametricAttribute_default___closed__0, &l_Lean_instInhabitedParametricAttribute_default___closed__0_once, _init_l_Lean_instInhabitedParametricAttribute_default___closed__0);
return v___x_2441_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__0(lean_object* v_x_2442_, lean_object* v_p_2443_){
_start:
{
lean_object* v_fst_2444_; lean_object* v_snd_2445_; lean_object* v___x_2447_; uint8_t v_isShared_2448_; uint8_t v_isSharedCheck_2462_; 
v_fst_2444_ = lean_ctor_get(v_x_2442_, 0);
v_snd_2445_ = lean_ctor_get(v_x_2442_, 1);
v_isSharedCheck_2462_ = !lean_is_exclusive(v_x_2442_);
if (v_isSharedCheck_2462_ == 0)
{
v___x_2447_ = v_x_2442_;
v_isShared_2448_ = v_isSharedCheck_2462_;
goto v_resetjp_2446_;
}
else
{
lean_inc(v_snd_2445_);
lean_inc(v_fst_2444_);
lean_dec(v_x_2442_);
v___x_2447_ = lean_box(0);
v_isShared_2448_ = v_isSharedCheck_2462_;
goto v_resetjp_2446_;
}
v_resetjp_2446_:
{
lean_object* v_fst_2449_; lean_object* v_snd_2450_; lean_object* v___x_2452_; uint8_t v_isShared_2453_; uint8_t v_isSharedCheck_2461_; 
v_fst_2449_ = lean_ctor_get(v_p_2443_, 0);
v_snd_2450_ = lean_ctor_get(v_p_2443_, 1);
v_isSharedCheck_2461_ = !lean_is_exclusive(v_p_2443_);
if (v_isSharedCheck_2461_ == 0)
{
v___x_2452_ = v_p_2443_;
v_isShared_2453_ = v_isSharedCheck_2461_;
goto v_resetjp_2451_;
}
else
{
lean_inc(v_snd_2450_);
lean_inc(v_fst_2449_);
lean_dec(v_p_2443_);
v___x_2452_ = lean_box(0);
v_isShared_2453_ = v_isSharedCheck_2461_;
goto v_resetjp_2451_;
}
v_resetjp_2451_:
{
lean_object* v___x_2455_; 
lean_inc(v_fst_2449_);
if (v_isShared_2448_ == 0)
{
lean_ctor_set_tag(v___x_2447_, 1);
lean_ctor_set(v___x_2447_, 1, v_fst_2444_);
lean_ctor_set(v___x_2447_, 0, v_fst_2449_);
v___x_2455_ = v___x_2447_;
goto v_reusejp_2454_;
}
else
{
lean_object* v_reuseFailAlloc_2460_; 
v_reuseFailAlloc_2460_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2460_, 0, v_fst_2449_);
lean_ctor_set(v_reuseFailAlloc_2460_, 1, v_fst_2444_);
v___x_2455_ = v_reuseFailAlloc_2460_;
goto v_reusejp_2454_;
}
v_reusejp_2454_:
{
lean_object* v___x_2456_; lean_object* v___x_2458_; 
v___x_2456_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_2449_, v_snd_2450_, v_snd_2445_);
if (v_isShared_2453_ == 0)
{
lean_ctor_set(v___x_2452_, 1, v___x_2456_);
lean_ctor_set(v___x_2452_, 0, v___x_2455_);
v___x_2458_ = v___x_2452_;
goto v_reusejp_2457_;
}
else
{
lean_object* v_reuseFailAlloc_2459_; 
v_reuseFailAlloc_2459_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2459_, 0, v___x_2455_);
lean_ctor_set(v_reuseFailAlloc_2459_, 1, v___x_2456_);
v___x_2458_ = v_reuseFailAlloc_2459_;
goto v_reusejp_2457_;
}
v_reusejp_2457_:
{
return v___x_2458_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg(lean_object* v_init_2463_, lean_object* v_x_2464_){
_start:
{
if (lean_obj_tag(v_x_2464_) == 0)
{
lean_object* v_k_2465_; lean_object* v_v_2466_; lean_object* v_l_2467_; lean_object* v_r_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; 
v_k_2465_ = lean_ctor_get(v_x_2464_, 1);
v_v_2466_ = lean_ctor_get(v_x_2464_, 2);
v_l_2467_ = lean_ctor_get(v_x_2464_, 3);
v_r_2468_ = lean_ctor_get(v_x_2464_, 4);
v___x_2469_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg(v_init_2463_, v_l_2467_);
lean_inc(v_v_2466_);
lean_inc(v_k_2465_);
v___x_2470_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2470_, 0, v_k_2465_);
lean_ctor_set(v___x_2470_, 1, v_v_2466_);
v___x_2471_ = lean_array_push(v___x_2469_, v___x_2470_);
v_init_2463_ = v___x_2471_;
v_x_2464_ = v_r_2468_;
goto _start;
}
else
{
return v_init_2463_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg___boxed(lean_object* v_init_2473_, lean_object* v_x_2474_){
_start:
{
lean_object* v_res_2475_; 
v_res_2475_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg(v_init_2473_, v_x_2474_);
lean_dec(v_x_2474_);
return v_res_2475_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5___redArg(lean_object* v_snd_2476_, lean_object* v_as_2477_, size_t v_i_2478_, size_t v_stop_2479_, lean_object* v_b_2480_){
_start:
{
lean_object* v___y_2482_; uint8_t v___x_2486_; 
v___x_2486_ = lean_usize_dec_eq(v_i_2478_, v_stop_2479_);
if (v___x_2486_ == 0)
{
lean_object* v___x_2487_; lean_object* v___x_2488_; 
v___x_2487_ = lean_array_uget_borrowed(v_as_2477_, v_i_2478_);
v___x_2488_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_snd_2476_, v___x_2487_);
if (lean_obj_tag(v___x_2488_) == 0)
{
v___y_2482_ = v_b_2480_;
goto v___jp_2481_;
}
else
{
lean_object* v_val_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; 
v_val_2489_ = lean_ctor_get(v___x_2488_, 0);
lean_inc(v_val_2489_);
lean_dec_ref_known(v___x_2488_, 1);
lean_inc(v___x_2487_);
v___x_2490_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2490_, 0, v___x_2487_);
lean_ctor_set(v___x_2490_, 1, v_val_2489_);
v___x_2491_ = lean_array_push(v_b_2480_, v___x_2490_);
v___y_2482_ = v___x_2491_;
goto v___jp_2481_;
}
}
else
{
return v_b_2480_;
}
v___jp_2481_:
{
size_t v___x_2483_; size_t v___x_2484_; 
v___x_2483_ = ((size_t)1ULL);
v___x_2484_ = lean_usize_add(v_i_2478_, v___x_2483_);
v_i_2478_ = v___x_2484_;
v_b_2480_ = v___y_2482_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5___redArg___boxed(lean_object* v_snd_2492_, lean_object* v_as_2493_, lean_object* v_i_2494_, lean_object* v_stop_2495_, lean_object* v_b_2496_){
_start:
{
size_t v_i_boxed_2497_; size_t v_stop_boxed_2498_; lean_object* v_res_2499_; 
v_i_boxed_2497_ = lean_unbox_usize(v_i_2494_);
lean_dec(v_i_2494_);
v_stop_boxed_2498_ = lean_unbox_usize(v_stop_2495_);
lean_dec(v_stop_2495_);
v_res_2499_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5___redArg(v_snd_2492_, v_as_2493_, v_i_boxed_2497_, v_stop_boxed_2498_, v_b_2496_);
lean_dec_ref(v_as_2493_);
lean_dec(v_snd_2492_);
return v_res_2499_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3___redArg(lean_object* v_snd_2500_, lean_object* v_as_2501_, lean_object* v_start_2502_, lean_object* v_stop_2503_){
_start:
{
lean_object* v___x_2504_; uint8_t v___x_2505_; 
v___x_2504_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___redArg___lam__2___closed__0));
v___x_2505_ = lean_nat_dec_lt(v_start_2502_, v_stop_2503_);
if (v___x_2505_ == 0)
{
return v___x_2504_;
}
else
{
lean_object* v___x_2506_; uint8_t v___x_2507_; 
v___x_2506_ = lean_array_get_size(v_as_2501_);
v___x_2507_ = lean_nat_dec_le(v_stop_2503_, v___x_2506_);
if (v___x_2507_ == 0)
{
uint8_t v___x_2508_; 
v___x_2508_ = lean_nat_dec_lt(v_start_2502_, v___x_2506_);
if (v___x_2508_ == 0)
{
return v___x_2504_;
}
else
{
size_t v___x_2509_; size_t v___x_2510_; lean_object* v___x_2511_; 
v___x_2509_ = lean_usize_of_nat(v_start_2502_);
v___x_2510_ = lean_usize_of_nat(v___x_2506_);
v___x_2511_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5___redArg(v_snd_2500_, v_as_2501_, v___x_2509_, v___x_2510_, v___x_2504_);
return v___x_2511_;
}
}
else
{
size_t v___x_2512_; size_t v___x_2513_; lean_object* v___x_2514_; 
v___x_2512_ = lean_usize_of_nat(v_start_2502_);
v___x_2513_ = lean_usize_of_nat(v_stop_2503_);
v___x_2514_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5___redArg(v_snd_2500_, v_as_2501_, v___x_2512_, v___x_2513_, v___x_2504_);
return v___x_2514_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3___redArg___boxed(lean_object* v_snd_2515_, lean_object* v_as_2516_, lean_object* v_start_2517_, lean_object* v_stop_2518_){
_start:
{
lean_object* v_res_2519_; 
v_res_2519_ = l_Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3___redArg(v_snd_2515_, v_as_2516_, v_start_2517_, v_stop_2518_);
lean_dec(v_stop_2518_);
lean_dec(v_start_2517_);
lean_dec_ref(v_as_2516_);
lean_dec(v_snd_2515_);
return v_res_2519_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2_spec__3___redArg(lean_object* v_hi_2520_, lean_object* v_pivot_2521_, lean_object* v_as_2522_, lean_object* v_i_2523_, lean_object* v_k_2524_){
_start:
{
uint8_t v___x_2525_; 
v___x_2525_ = lean_nat_dec_lt(v_k_2524_, v_hi_2520_);
if (v___x_2525_ == 0)
{
lean_object* v___x_2526_; lean_object* v___x_2527_; 
lean_dec(v_k_2524_);
v___x_2526_ = lean_array_fswap(v_as_2522_, v_i_2523_, v_hi_2520_);
v___x_2527_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2527_, 0, v_i_2523_);
lean_ctor_set(v___x_2527_, 1, v___x_2526_);
return v___x_2527_;
}
else
{
lean_object* v___x_2528_; lean_object* v_fst_2529_; lean_object* v_fst_2530_; uint8_t v___x_2531_; 
v___x_2528_ = lean_array_fget_borrowed(v_as_2522_, v_k_2524_);
v_fst_2529_ = lean_ctor_get(v___x_2528_, 0);
v_fst_2530_ = lean_ctor_get(v_pivot_2521_, 0);
v___x_2531_ = l_Lean_Name_quickLt(v_fst_2529_, v_fst_2530_);
if (v___x_2531_ == 0)
{
lean_object* v___x_2532_; lean_object* v___x_2533_; 
v___x_2532_ = lean_unsigned_to_nat(1u);
v___x_2533_ = lean_nat_add(v_k_2524_, v___x_2532_);
lean_dec(v_k_2524_);
v_k_2524_ = v___x_2533_;
goto _start;
}
else
{
lean_object* v___x_2535_; lean_object* v___x_2536_; lean_object* v___x_2537_; lean_object* v___x_2538_; 
v___x_2535_ = lean_array_fswap(v_as_2522_, v_i_2523_, v_k_2524_);
v___x_2536_ = lean_unsigned_to_nat(1u);
v___x_2537_ = lean_nat_add(v_i_2523_, v___x_2536_);
lean_dec(v_i_2523_);
v___x_2538_ = lean_nat_add(v_k_2524_, v___x_2536_);
lean_dec(v_k_2524_);
v_as_2522_ = v___x_2535_;
v_i_2523_ = v___x_2537_;
v_k_2524_ = v___x_2538_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2_spec__3___redArg___boxed(lean_object* v_hi_2540_, lean_object* v_pivot_2541_, lean_object* v_as_2542_, lean_object* v_i_2543_, lean_object* v_k_2544_){
_start:
{
lean_object* v_res_2545_; 
v_res_2545_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2_spec__3___redArg(v_hi_2540_, v_pivot_2541_, v_as_2542_, v_i_2543_, v_k_2544_);
lean_dec_ref(v_pivot_2541_);
lean_dec(v_hi_2540_);
return v_res_2545_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg___lam__0(lean_object* v_a_2546_, lean_object* v_b_2547_){
_start:
{
lean_object* v_fst_2548_; lean_object* v_fst_2549_; uint8_t v___x_2550_; 
v_fst_2548_ = lean_ctor_get(v_a_2546_, 0);
v_fst_2549_ = lean_ctor_get(v_b_2547_, 0);
v___x_2550_ = l_Lean_Name_quickLt(v_fst_2548_, v_fst_2549_);
return v___x_2550_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg___lam__0___boxed(lean_object* v_a_2551_, lean_object* v_b_2552_){
_start:
{
uint8_t v_res_2553_; lean_object* v_r_2554_; 
v_res_2553_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg___lam__0(v_a_2551_, v_b_2552_);
lean_dec_ref(v_b_2552_);
lean_dec_ref(v_a_2551_);
v_r_2554_ = lean_box(v_res_2553_);
return v_r_2554_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg(lean_object* v_n_2555_, lean_object* v_as_2556_, lean_object* v_lo_2557_, lean_object* v_hi_2558_){
_start:
{
lean_object* v___y_2560_; uint8_t v___x_2570_; 
v___x_2570_ = lean_nat_dec_lt(v_lo_2557_, v_hi_2558_);
if (v___x_2570_ == 0)
{
lean_dec(v_lo_2557_);
return v_as_2556_;
}
else
{
lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v_mid_2573_; lean_object* v___y_2575_; lean_object* v___y_2581_; lean_object* v___x_2586_; lean_object* v___x_2587_; uint8_t v___x_2588_; 
v___x_2571_ = lean_nat_add(v_lo_2557_, v_hi_2558_);
v___x_2572_ = lean_unsigned_to_nat(1u);
v_mid_2573_ = lean_nat_shiftr(v___x_2571_, v___x_2572_);
lean_dec(v___x_2571_);
v___x_2586_ = lean_array_fget_borrowed(v_as_2556_, v_mid_2573_);
v___x_2587_ = lean_array_fget_borrowed(v_as_2556_, v_lo_2557_);
v___x_2588_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg___lam__0(v___x_2586_, v___x_2587_);
if (v___x_2588_ == 0)
{
v___y_2581_ = v_as_2556_;
goto v___jp_2580_;
}
else
{
lean_object* v___x_2589_; 
v___x_2589_ = lean_array_fswap(v_as_2556_, v_lo_2557_, v_mid_2573_);
v___y_2581_ = v___x_2589_;
goto v___jp_2580_;
}
v___jp_2574_:
{
lean_object* v___x_2576_; lean_object* v___x_2577_; uint8_t v___x_2578_; 
v___x_2576_ = lean_array_fget_borrowed(v___y_2575_, v_mid_2573_);
v___x_2577_ = lean_array_fget_borrowed(v___y_2575_, v_hi_2558_);
v___x_2578_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg___lam__0(v___x_2576_, v___x_2577_);
if (v___x_2578_ == 0)
{
lean_dec(v_mid_2573_);
v___y_2560_ = v___y_2575_;
goto v___jp_2559_;
}
else
{
lean_object* v___x_2579_; 
v___x_2579_ = lean_array_fswap(v___y_2575_, v_mid_2573_, v_hi_2558_);
lean_dec(v_mid_2573_);
v___y_2560_ = v___x_2579_;
goto v___jp_2559_;
}
}
v___jp_2580_:
{
lean_object* v___x_2582_; lean_object* v___x_2583_; uint8_t v___x_2584_; 
v___x_2582_ = lean_array_fget_borrowed(v___y_2581_, v_hi_2558_);
v___x_2583_ = lean_array_fget_borrowed(v___y_2581_, v_lo_2557_);
v___x_2584_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg___lam__0(v___x_2582_, v___x_2583_);
if (v___x_2584_ == 0)
{
v___y_2575_ = v___y_2581_;
goto v___jp_2574_;
}
else
{
lean_object* v___x_2585_; 
v___x_2585_ = lean_array_fswap(v___y_2581_, v_lo_2557_, v_hi_2558_);
v___y_2575_ = v___x_2585_;
goto v___jp_2574_;
}
}
}
v___jp_2559_:
{
lean_object* v_pivot_2561_; lean_object* v___x_2562_; lean_object* v_fst_2563_; lean_object* v_snd_2564_; uint8_t v___x_2565_; 
v_pivot_2561_ = lean_array_fget(v___y_2560_, v_hi_2558_);
lean_inc_n(v_lo_2557_, 2);
v___x_2562_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2_spec__3___redArg(v_hi_2558_, v_pivot_2561_, v___y_2560_, v_lo_2557_, v_lo_2557_);
lean_dec(v_pivot_2561_);
v_fst_2563_ = lean_ctor_get(v___x_2562_, 0);
lean_inc(v_fst_2563_);
v_snd_2564_ = lean_ctor_get(v___x_2562_, 1);
lean_inc(v_snd_2564_);
lean_dec_ref(v___x_2562_);
v___x_2565_ = lean_nat_dec_le(v_hi_2558_, v_fst_2563_);
if (v___x_2565_ == 0)
{
lean_object* v___x_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; 
v___x_2566_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg(v_n_2555_, v_snd_2564_, v_lo_2557_, v_fst_2563_);
v___x_2567_ = lean_unsigned_to_nat(1u);
v___x_2568_ = lean_nat_add(v_fst_2563_, v___x_2567_);
lean_dec(v_fst_2563_);
v_as_2556_ = v___x_2566_;
v_lo_2557_ = v___x_2568_;
goto _start;
}
else
{
lean_dec(v_fst_2563_);
lean_dec(v_lo_2557_);
return v_snd_2564_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg___boxed(lean_object* v_n_2590_, lean_object* v_as_2591_, lean_object* v_lo_2592_, lean_object* v_hi_2593_){
_start:
{
lean_object* v_res_2594_; 
v_res_2594_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg(v_n_2590_, v_as_2591_, v_lo_2592_, v_hi_2593_);
lean_dec(v_hi_2593_);
lean_dec(v_n_2590_);
return v_res_2594_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0___redArg(lean_object* v_filterExport_2595_, lean_object* v_env_2596_, lean_object* v_as_2597_, size_t v_i_2598_, size_t v_stop_2599_, lean_object* v_b_2600_){
_start:
{
lean_object* v___y_2602_; uint8_t v___x_2606_; 
v___x_2606_ = lean_usize_dec_eq(v_i_2598_, v_stop_2599_);
if (v___x_2606_ == 0)
{
lean_object* v___x_2607_; lean_object* v_fst_2608_; lean_object* v_snd_2609_; lean_object* v___x_2610_; uint8_t v___x_2611_; 
v___x_2607_ = lean_array_uget_borrowed(v_as_2597_, v_i_2598_);
v_fst_2608_ = lean_ctor_get(v___x_2607_, 0);
v_snd_2609_ = lean_ctor_get(v___x_2607_, 1);
lean_inc_ref(v_filterExport_2595_);
lean_inc(v_snd_2609_);
lean_inc(v_fst_2608_);
lean_inc_ref(v_env_2596_);
v___x_2610_ = lean_apply_3(v_filterExport_2595_, v_env_2596_, v_fst_2608_, v_snd_2609_);
v___x_2611_ = lean_unbox(v___x_2610_);
if (v___x_2611_ == 0)
{
v___y_2602_ = v_b_2600_;
goto v___jp_2601_;
}
else
{
lean_object* v___x_2612_; 
lean_inc(v___x_2607_);
v___x_2612_ = lean_array_push(v_b_2600_, v___x_2607_);
v___y_2602_ = v___x_2612_;
goto v___jp_2601_;
}
}
else
{
lean_dec_ref(v_env_2596_);
lean_dec_ref(v_filterExport_2595_);
return v_b_2600_;
}
v___jp_2601_:
{
size_t v___x_2603_; size_t v___x_2604_; 
v___x_2603_ = ((size_t)1ULL);
v___x_2604_ = lean_usize_add(v_i_2598_, v___x_2603_);
v_i_2598_ = v___x_2604_;
v_b_2600_ = v___y_2602_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0___redArg___boxed(lean_object* v_filterExport_2613_, lean_object* v_env_2614_, lean_object* v_as_2615_, lean_object* v_i_2616_, lean_object* v_stop_2617_, lean_object* v_b_2618_){
_start:
{
size_t v_i_boxed_2619_; size_t v_stop_boxed_2620_; lean_object* v_res_2621_; 
v_i_boxed_2619_ = lean_unbox_usize(v_i_2616_);
lean_dec(v_i_2616_);
v_stop_boxed_2620_ = lean_unbox_usize(v_stop_2617_);
lean_dec(v_stop_2617_);
v_res_2621_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0___redArg(v_filterExport_2613_, v_env_2614_, v_as_2615_, v_i_boxed_2619_, v_stop_boxed_2620_, v_b_2618_);
lean_dec_ref(v_as_2615_);
return v_res_2621_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__1(lean_object* v_filterExport_2622_, uint8_t v_preserveOrder_2623_, lean_object* v_env_2624_, lean_object* v_x_2625_){
_start:
{
lean_object* v___y_2627_; 
if (v_preserveOrder_2623_ == 0)
{
lean_object* v_snd_2643_; lean_object* v___x_2644_; lean_object* v___x_2645_; lean_object* v_r_2646_; lean_object* v___x_2647_; lean_object* v___y_2649_; lean_object* v___y_2650_; uint8_t v___x_2652_; 
v_snd_2643_ = lean_ctor_get(v_x_2625_, 1);
lean_inc(v_snd_2643_);
lean_dec_ref(v_x_2625_);
v___x_2644_ = lean_unsigned_to_nat(0u);
v___x_2645_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___redArg___lam__2___closed__0));
v_r_2646_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg(v___x_2645_, v_snd_2643_);
lean_dec(v_snd_2643_);
v___x_2647_ = lean_array_get_size(v_r_2646_);
v___x_2652_ = lean_nat_dec_eq(v___x_2647_, v___x_2644_);
if (v___x_2652_ == 0)
{
lean_object* v___x_2653_; lean_object* v___x_2654_; lean_object* v___y_2656_; uint8_t v___x_2658_; 
v___x_2653_ = lean_unsigned_to_nat(1u);
v___x_2654_ = lean_nat_sub(v___x_2647_, v___x_2653_);
v___x_2658_ = lean_nat_dec_le(v___x_2644_, v___x_2654_);
if (v___x_2658_ == 0)
{
lean_inc(v___x_2654_);
v___y_2656_ = v___x_2654_;
goto v___jp_2655_;
}
else
{
v___y_2656_ = v___x_2644_;
goto v___jp_2655_;
}
v___jp_2655_:
{
uint8_t v___x_2657_; 
v___x_2657_ = lean_nat_dec_le(v___y_2656_, v___x_2654_);
if (v___x_2657_ == 0)
{
lean_dec(v___x_2654_);
lean_inc(v___y_2656_);
v___y_2649_ = v___y_2656_;
v___y_2650_ = v___y_2656_;
goto v___jp_2648_;
}
else
{
v___y_2649_ = v___y_2656_;
v___y_2650_ = v___x_2654_;
goto v___jp_2648_;
}
}
}
else
{
v___y_2627_ = v_r_2646_;
goto v___jp_2626_;
}
v___jp_2648_:
{
lean_object* v___x_2651_; 
v___x_2651_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg(v___x_2647_, v_r_2646_, v___y_2649_, v___y_2650_);
lean_dec(v___y_2650_);
v___y_2627_ = v___x_2651_;
goto v___jp_2626_;
}
}
else
{
lean_object* v_fst_2659_; lean_object* v_snd_2660_; lean_object* v___x_2661_; lean_object* v___x_2662_; lean_object* v___x_2663_; lean_object* v___x_2664_; lean_object* v___x_2665_; 
v_fst_2659_ = lean_ctor_get(v_x_2625_, 0);
lean_inc(v_fst_2659_);
v_snd_2660_ = lean_ctor_get(v_x_2625_, 1);
lean_inc(v_snd_2660_);
lean_dec_ref(v_x_2625_);
v___x_2661_ = lean_array_mk(v_fst_2659_);
v___x_2662_ = l_Array_reverse___redArg(v___x_2661_);
v___x_2663_ = lean_unsigned_to_nat(0u);
v___x_2664_ = lean_array_get_size(v___x_2662_);
v___x_2665_ = l_Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3___redArg(v_snd_2660_, v___x_2662_, v___x_2663_, v___x_2664_);
lean_dec_ref(v___x_2662_);
lean_dec(v_snd_2660_);
v___y_2627_ = v___x_2665_;
goto v___jp_2626_;
}
v___jp_2626_:
{
lean_object* v___x_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; uint8_t v___x_2631_; 
v___x_2628_ = lean_unsigned_to_nat(0u);
v___x_2629_ = lean_array_get_size(v___y_2627_);
v___x_2630_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___redArg___lam__2___closed__0));
v___x_2631_ = lean_nat_dec_lt(v___x_2628_, v___x_2629_);
if (v___x_2631_ == 0)
{
lean_object* v___x_2632_; 
lean_dec_ref(v_env_2624_);
lean_dec_ref(v_filterExport_2622_);
v___x_2632_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2632_, 0, v___x_2630_);
lean_ctor_set(v___x_2632_, 1, v___x_2630_);
lean_ctor_set(v___x_2632_, 2, v___y_2627_);
return v___x_2632_;
}
else
{
uint8_t v___x_2633_; 
v___x_2633_ = lean_nat_dec_le(v___x_2629_, v___x_2629_);
if (v___x_2633_ == 0)
{
if (v___x_2631_ == 0)
{
lean_object* v___x_2634_; 
lean_dec_ref(v_env_2624_);
lean_dec_ref(v_filterExport_2622_);
v___x_2634_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2634_, 0, v___x_2630_);
lean_ctor_set(v___x_2634_, 1, v___x_2630_);
lean_ctor_set(v___x_2634_, 2, v___y_2627_);
return v___x_2634_;
}
else
{
size_t v___x_2635_; size_t v___x_2636_; lean_object* v___x_2637_; lean_object* v___x_2638_; 
v___x_2635_ = ((size_t)0ULL);
v___x_2636_ = lean_usize_of_nat(v___x_2629_);
v___x_2637_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0___redArg(v_filterExport_2622_, v_env_2624_, v___y_2627_, v___x_2635_, v___x_2636_, v___x_2630_);
lean_inc_ref(v___x_2637_);
v___x_2638_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2638_, 0, v___x_2637_);
lean_ctor_set(v___x_2638_, 1, v___x_2637_);
lean_ctor_set(v___x_2638_, 2, v___y_2627_);
return v___x_2638_;
}
}
else
{
size_t v___x_2639_; size_t v___x_2640_; lean_object* v___x_2641_; lean_object* v___x_2642_; 
v___x_2639_ = ((size_t)0ULL);
v___x_2640_ = lean_usize_of_nat(v___x_2629_);
v___x_2641_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0___redArg(v_filterExport_2622_, v_env_2624_, v___y_2627_, v___x_2639_, v___x_2640_, v___x_2630_);
lean_inc_ref(v___x_2641_);
v___x_2642_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2642_, 0, v___x_2641_);
lean_ctor_set(v___x_2642_, 1, v___x_2641_);
lean_ctor_set(v___x_2642_, 2, v___y_2627_);
return v___x_2642_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__1___boxed(lean_object* v_filterExport_2666_, lean_object* v_preserveOrder_2667_, lean_object* v_env_2668_, lean_object* v_x_2669_){
_start:
{
uint8_t v_preserveOrder_boxed_2670_; lean_object* v_res_2671_; 
v_preserveOrder_boxed_2670_ = lean_unbox(v_preserveOrder_2667_);
v_res_2671_ = l_Lean_registerParametricAttributeExt___redArg___lam__1(v_filterExport_2666_, v_preserveOrder_boxed_2670_, v_env_2668_, v_x_2669_);
return v_res_2671_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__2(lean_object* v_x_2681_){
_start:
{
lean_object* v_snd_2682_; lean_object* v___x_2684_; uint8_t v_isShared_2685_; uint8_t v_isSharedCheck_2696_; 
v_snd_2682_ = lean_ctor_get(v_x_2681_, 1);
v_isSharedCheck_2696_ = !lean_is_exclusive(v_x_2681_);
if (v_isSharedCheck_2696_ == 0)
{
lean_object* v_unused_2697_; 
v_unused_2697_ = lean_ctor_get(v_x_2681_, 0);
lean_dec(v_unused_2697_);
v___x_2684_ = v_x_2681_;
v_isShared_2685_ = v_isSharedCheck_2696_;
goto v_resetjp_2683_;
}
else
{
lean_inc(v_snd_2682_);
lean_dec(v_x_2681_);
v___x_2684_ = lean_box(0);
v_isShared_2685_ = v_isSharedCheck_2696_;
goto v_resetjp_2683_;
}
v_resetjp_2683_:
{
lean_object* v___x_2686_; lean_object* v___y_2688_; 
v___x_2686_ = ((lean_object*)(l_Lean_registerParametricAttributeExt___redArg___lam__2___closed__3));
if (lean_obj_tag(v_snd_2682_) == 0)
{
lean_object* v_size_2694_; 
v_size_2694_ = lean_ctor_get(v_snd_2682_, 0);
lean_inc(v_size_2694_);
lean_dec_ref_known(v_snd_2682_, 5);
v___y_2688_ = v_size_2694_;
goto v___jp_2687_;
}
else
{
lean_object* v___x_2695_; 
v___x_2695_ = lean_unsigned_to_nat(0u);
v___y_2688_ = v___x_2695_;
goto v___jp_2687_;
}
v___jp_2687_:
{
lean_object* v___x_2689_; lean_object* v___x_2690_; lean_object* v___x_2692_; 
v___x_2689_ = l_Nat_reprFast(v___y_2688_);
v___x_2690_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2690_, 0, v___x_2689_);
if (v_isShared_2685_ == 0)
{
lean_ctor_set_tag(v___x_2684_, 5);
lean_ctor_set(v___x_2684_, 1, v___x_2690_);
lean_ctor_set(v___x_2684_, 0, v___x_2686_);
v___x_2692_ = v___x_2684_;
goto v_reusejp_2691_;
}
else
{
lean_object* v_reuseFailAlloc_2693_; 
v_reuseFailAlloc_2693_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2693_, 0, v___x_2686_);
lean_ctor_set(v_reuseFailAlloc_2693_, 1, v___x_2690_);
v___x_2692_ = v_reuseFailAlloc_2693_;
goto v_reusejp_2691_;
}
v_reusejp_2691_:
{
return v___x_2692_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__3(lean_object* v_x_2698_){
_start:
{
lean_object* v___x_2699_; 
v___x_2699_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___redArg___lam__2___closed__0));
return v___x_2699_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__3___boxed(lean_object* v_x_2700_){
_start:
{
lean_object* v_res_2701_; 
v_res_2701_ = l_Lean_registerParametricAttributeExt___redArg___lam__3(v_x_2700_);
lean_dec_ref(v_x_2700_);
return v_res_2701_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__4(lean_object* v___x_2702_){
_start:
{
lean_object* v___x_2704_; 
v___x_2704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2704_, 0, v___x_2702_);
return v___x_2704_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__4___boxed(lean_object* v___x_2705_, lean_object* v___y_2706_){
_start:
{
lean_object* v_res_2707_; 
v_res_2707_ = l_Lean_registerParametricAttributeExt___redArg___lam__4(v___x_2705_);
return v_res_2707_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__5(lean_object* v___x_2708_, lean_object* v_x_2709_, lean_object* v___y_2710_){
_start:
{
lean_object* v___x_2712_; 
v___x_2712_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2712_, 0, v___x_2708_);
return v___x_2712_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__5___boxed(lean_object* v___x_2713_, lean_object* v_x_2714_, lean_object* v___y_2715_, lean_object* v___y_2716_){
_start:
{
lean_object* v_res_2717_; 
v_res_2717_ = l_Lean_registerParametricAttributeExt___redArg___lam__5(v___x_2713_, v_x_2714_, v___y_2715_);
lean_dec_ref(v___y_2715_);
lean_dec_ref(v_x_2714_);
return v_res_2717_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg(lean_object* v_ref_2728_, uint8_t v_preserveOrder_2729_, lean_object* v_filterExport_2730_, uint8_t v_logWrites_2731_){
_start:
{
lean_object* v___f_2733_; lean_object* v___x_2734_; lean_object* v___f_2735_; lean_object* v___f_2736_; lean_object* v___f_2737_; lean_object* v___f_2738_; lean_object* v___f_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; uint8_t v___x_2742_; lean_object* v___x_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; 
v___f_2733_ = ((lean_object*)(l_Lean_registerParametricAttributeExt___redArg___closed__0));
v___x_2734_ = lean_box(v_preserveOrder_2729_);
v___f_2735_ = lean_alloc_closure((void*)(l_Lean_registerParametricAttributeExt___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_2735_, 0, v_filterExport_2730_);
lean_closure_set(v___f_2735_, 1, v___x_2734_);
v___f_2736_ = ((lean_object*)(l_Lean_registerParametricAttributeExt___redArg___closed__1));
v___f_2737_ = ((lean_object*)(l_Lean_registerParametricAttributeExt___redArg___closed__2));
v___f_2738_ = ((lean_object*)(l_Lean_registerParametricAttributeExt___redArg___closed__4));
v___f_2739_ = ((lean_object*)(l_Lean_registerParametricAttributeExt___redArg___closed__5));
v___x_2740_ = lean_box(2);
v___x_2741_ = lean_box(0);
v___x_2742_ = 0;
v___x_2743_ = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(v___x_2743_, 0, v_ref_2728_);
lean_ctor_set(v___x_2743_, 1, v___f_2738_);
lean_ctor_set(v___x_2743_, 2, v___f_2739_);
lean_ctor_set(v___x_2743_, 3, v___f_2733_);
lean_ctor_set(v___x_2743_, 4, v___f_2735_);
lean_ctor_set(v___x_2743_, 5, v___f_2736_);
lean_ctor_set(v___x_2743_, 6, v___x_2740_);
lean_ctor_set(v___x_2743_, 7, v___x_2741_);
lean_ctor_set_uint8(v___x_2743_, sizeof(void*)*8, v___x_2742_);
lean_ctor_set_uint8(v___x_2743_, sizeof(void*)*8 + 1, v_logWrites_2731_);
v___x_2744_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2744_, 0, v___x_2743_);
lean_ctor_set(v___x_2744_, 1, v___f_2737_);
v___x_2745_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_2744_);
return v___x_2745_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___boxed(lean_object* v_ref_2746_, lean_object* v_preserveOrder_2747_, lean_object* v_filterExport_2748_, lean_object* v_logWrites_2749_, lean_object* v_a_2750_){
_start:
{
uint8_t v_preserveOrder_boxed_2751_; uint8_t v_logWrites_boxed_2752_; lean_object* v_res_2753_; 
v_preserveOrder_boxed_2751_ = lean_unbox(v_preserveOrder_2747_);
v_logWrites_boxed_2752_ = lean_unbox(v_logWrites_2749_);
v_res_2753_ = l_Lean_registerParametricAttributeExt___redArg(v_ref_2746_, v_preserveOrder_boxed_2751_, v_filterExport_2748_, v_logWrites_boxed_2752_);
return v_res_2753_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt(lean_object* v_00_u03b1_2754_, lean_object* v_ref_2755_, uint8_t v_preserveOrder_2756_, lean_object* v_filterExport_2757_, uint8_t v_logWrites_2758_){
_start:
{
lean_object* v___x_2760_; 
v___x_2760_ = l_Lean_registerParametricAttributeExt___redArg(v_ref_2755_, v_preserveOrder_2756_, v_filterExport_2757_, v_logWrites_2758_);
return v___x_2760_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___boxed(lean_object* v_00_u03b1_2761_, lean_object* v_ref_2762_, lean_object* v_preserveOrder_2763_, lean_object* v_filterExport_2764_, lean_object* v_logWrites_2765_, lean_object* v_a_2766_){
_start:
{
uint8_t v_preserveOrder_boxed_2767_; uint8_t v_logWrites_boxed_2768_; lean_object* v_res_2769_; 
v_preserveOrder_boxed_2767_ = lean_unbox(v_preserveOrder_2763_);
v_logWrites_boxed_2768_ = lean_unbox(v_logWrites_2765_);
v_res_2769_ = l_Lean_registerParametricAttributeExt(v_00_u03b1_2761_, v_ref_2762_, v_preserveOrder_boxed_2767_, v_filterExport_2764_, v_logWrites_boxed_2768_);
return v_res_2769_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0(lean_object* v_00_u03b1_2770_, lean_object* v_filterExport_2771_, lean_object* v_env_2772_, lean_object* v_as_2773_, size_t v_i_2774_, size_t v_stop_2775_, lean_object* v_b_2776_){
_start:
{
lean_object* v___x_2777_; 
v___x_2777_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0___redArg(v_filterExport_2771_, v_env_2772_, v_as_2773_, v_i_2774_, v_stop_2775_, v_b_2776_);
return v___x_2777_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0___boxed(lean_object* v_00_u03b1_2778_, lean_object* v_filterExport_2779_, lean_object* v_env_2780_, lean_object* v_as_2781_, lean_object* v_i_2782_, lean_object* v_stop_2783_, lean_object* v_b_2784_){
_start:
{
size_t v_i_boxed_2785_; size_t v_stop_boxed_2786_; lean_object* v_res_2787_; 
v_i_boxed_2785_ = lean_unbox_usize(v_i_2782_);
lean_dec(v_i_2782_);
v_stop_boxed_2786_ = lean_unbox_usize(v_stop_2783_);
lean_dec(v_stop_2783_);
v_res_2787_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0(v_00_u03b1_2778_, v_filterExport_2779_, v_env_2780_, v_as_2781_, v_i_boxed_2785_, v_stop_boxed_2786_, v_b_2784_);
lean_dec_ref(v_as_2781_);
return v_res_2787_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1___redArg(lean_object* v_init_2788_, lean_object* v_t_2789_){
_start:
{
lean_object* v___x_2790_; 
v___x_2790_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg(v_init_2788_, v_t_2789_);
return v___x_2790_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1___redArg___boxed(lean_object* v_init_2791_, lean_object* v_t_2792_){
_start:
{
lean_object* v_res_2793_; 
v_res_2793_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1___redArg(v_init_2791_, v_t_2792_);
lean_dec(v_t_2792_);
return v_res_2793_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1(lean_object* v_00_u03b1_2794_, lean_object* v_init_2795_, lean_object* v_t_2796_){
_start:
{
lean_object* v___x_2797_; 
v___x_2797_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg(v_init_2795_, v_t_2796_);
return v___x_2797_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1___boxed(lean_object* v_00_u03b1_2798_, lean_object* v_init_2799_, lean_object* v_t_2800_){
_start:
{
lean_object* v_res_2801_; 
v_res_2801_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1(v_00_u03b1_2798_, v_init_2799_, v_t_2800_);
lean_dec(v_t_2800_);
return v_res_2801_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2(lean_object* v_00_u03b1_2802_, lean_object* v_n_2803_, lean_object* v_as_2804_, lean_object* v_lo_2805_, lean_object* v_hi_2806_, lean_object* v_w_2807_, lean_object* v_hlo_2808_, lean_object* v_hhi_2809_){
_start:
{
lean_object* v___x_2810_; 
v___x_2810_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg(v_n_2803_, v_as_2804_, v_lo_2805_, v_hi_2806_);
return v___x_2810_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___boxed(lean_object* v_00_u03b1_2811_, lean_object* v_n_2812_, lean_object* v_as_2813_, lean_object* v_lo_2814_, lean_object* v_hi_2815_, lean_object* v_w_2816_, lean_object* v_hlo_2817_, lean_object* v_hhi_2818_){
_start:
{
lean_object* v_res_2819_; 
v_res_2819_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2(v_00_u03b1_2811_, v_n_2812_, v_as_2813_, v_lo_2814_, v_hi_2815_, v_w_2816_, v_hlo_2817_, v_hhi_2818_);
lean_dec(v_hi_2815_);
lean_dec(v_n_2812_);
return v_res_2819_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3(lean_object* v_00_u03b1_2820_, lean_object* v_snd_2821_, lean_object* v_as_2822_, lean_object* v_start_2823_, lean_object* v_stop_2824_){
_start:
{
lean_object* v___x_2825_; 
v___x_2825_ = l_Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3___redArg(v_snd_2821_, v_as_2822_, v_start_2823_, v_stop_2824_);
return v___x_2825_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3___boxed(lean_object* v_00_u03b1_2826_, lean_object* v_snd_2827_, lean_object* v_as_2828_, lean_object* v_start_2829_, lean_object* v_stop_2830_){
_start:
{
lean_object* v_res_2831_; 
v_res_2831_ = l_Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3(v_00_u03b1_2826_, v_snd_2827_, v_as_2828_, v_start_2829_, v_stop_2830_);
lean_dec(v_stop_2830_);
lean_dec(v_start_2829_);
lean_dec_ref(v_as_2828_);
lean_dec(v_snd_2827_);
return v_res_2831_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1(lean_object* v_00_u03b1_2832_, lean_object* v_init_2833_, lean_object* v_x_2834_){
_start:
{
lean_object* v___x_2835_; 
v___x_2835_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg(v_init_2833_, v_x_2834_);
return v___x_2835_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___boxed(lean_object* v_00_u03b1_2836_, lean_object* v_init_2837_, lean_object* v_x_2838_){
_start:
{
lean_object* v_res_2839_; 
v_res_2839_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1(v_00_u03b1_2836_, v_init_2837_, v_x_2838_);
lean_dec(v_x_2838_);
return v_res_2839_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2_spec__3(lean_object* v_00_u03b1_2840_, lean_object* v_n_2841_, lean_object* v_lo_2842_, lean_object* v_hi_2843_, lean_object* v_hhi_2844_, lean_object* v_pivot_2845_, lean_object* v_as_2846_, lean_object* v_i_2847_, lean_object* v_k_2848_, lean_object* v_ilo_2849_, lean_object* v_ik_2850_, lean_object* v_w_2851_){
_start:
{
lean_object* v___x_2852_; 
v___x_2852_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2_spec__3___redArg(v_hi_2843_, v_pivot_2845_, v_as_2846_, v_i_2847_, v_k_2848_);
return v___x_2852_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2_spec__3___boxed(lean_object* v_00_u03b1_2853_, lean_object* v_n_2854_, lean_object* v_lo_2855_, lean_object* v_hi_2856_, lean_object* v_hhi_2857_, lean_object* v_pivot_2858_, lean_object* v_as_2859_, lean_object* v_i_2860_, lean_object* v_k_2861_, lean_object* v_ilo_2862_, lean_object* v_ik_2863_, lean_object* v_w_2864_){
_start:
{
lean_object* v_res_2865_; 
v_res_2865_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2_spec__3(v_00_u03b1_2853_, v_n_2854_, v_lo_2855_, v_hi_2856_, v_hhi_2857_, v_pivot_2858_, v_as_2859_, v_i_2860_, v_k_2861_, v_ilo_2862_, v_ik_2863_, v_w_2864_);
lean_dec_ref(v_pivot_2858_);
lean_dec(v_hi_2856_);
lean_dec(v_lo_2855_);
lean_dec(v_n_2854_);
return v_res_2865_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5(lean_object* v_00_u03b1_2866_, lean_object* v_snd_2867_, lean_object* v_as_2868_, size_t v_i_2869_, size_t v_stop_2870_, lean_object* v_b_2871_){
_start:
{
lean_object* v___x_2872_; 
v___x_2872_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5___redArg(v_snd_2867_, v_as_2868_, v_i_2869_, v_stop_2870_, v_b_2871_);
return v___x_2872_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5___boxed(lean_object* v_00_u03b1_2873_, lean_object* v_snd_2874_, lean_object* v_as_2875_, lean_object* v_i_2876_, lean_object* v_stop_2877_, lean_object* v_b_2878_){
_start:
{
size_t v_i_boxed_2879_; size_t v_stop_boxed_2880_; lean_object* v_res_2881_; 
v_i_boxed_2879_ = lean_unbox_usize(v_i_2876_);
lean_dec(v_i_2876_);
v_stop_boxed_2880_ = lean_unbox_usize(v_stop_2877_);
lean_dec(v_stop_2877_);
v_res_2881_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5(v_00_u03b1_2873_, v_snd_2874_, v_as_2875_, v_i_boxed_2879_, v_stop_boxed_2880_, v_b_2878_);
lean_dec_ref(v_as_2875_);
lean_dec(v_snd_2874_);
return v_res_2881_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_registerParametricAttributeForExt_spec__0___redArg(lean_object* v_env_2882_, lean_object* v___y_2883_){
_start:
{
lean_object* v___x_2885_; lean_object* v_nextMacroScope_2886_; lean_object* v_ngen_2887_; lean_object* v_auxDeclNGen_2888_; lean_object* v_traceState_2889_; lean_object* v_recordedDeps_2890_; lean_object* v_messages_2891_; lean_object* v_infoState_2892_; lean_object* v_snapshotTasks_2893_; lean_object* v___x_2895_; uint8_t v_isShared_2896_; uint8_t v_isSharedCheck_2904_; 
v___x_2885_ = lean_st_ref_take(v___y_2883_);
v_nextMacroScope_2886_ = lean_ctor_get(v___x_2885_, 1);
v_ngen_2887_ = lean_ctor_get(v___x_2885_, 2);
v_auxDeclNGen_2888_ = lean_ctor_get(v___x_2885_, 3);
v_traceState_2889_ = lean_ctor_get(v___x_2885_, 4);
v_recordedDeps_2890_ = lean_ctor_get(v___x_2885_, 6);
v_messages_2891_ = lean_ctor_get(v___x_2885_, 7);
v_infoState_2892_ = lean_ctor_get(v___x_2885_, 8);
v_snapshotTasks_2893_ = lean_ctor_get(v___x_2885_, 9);
v_isSharedCheck_2904_ = !lean_is_exclusive(v___x_2885_);
if (v_isSharedCheck_2904_ == 0)
{
lean_object* v_unused_2905_; lean_object* v_unused_2906_; 
v_unused_2905_ = lean_ctor_get(v___x_2885_, 5);
lean_dec(v_unused_2905_);
v_unused_2906_ = lean_ctor_get(v___x_2885_, 0);
lean_dec(v_unused_2906_);
v___x_2895_ = v___x_2885_;
v_isShared_2896_ = v_isSharedCheck_2904_;
goto v_resetjp_2894_;
}
else
{
lean_inc(v_snapshotTasks_2893_);
lean_inc(v_infoState_2892_);
lean_inc(v_messages_2891_);
lean_inc(v_recordedDeps_2890_);
lean_inc(v_traceState_2889_);
lean_inc(v_auxDeclNGen_2888_);
lean_inc(v_ngen_2887_);
lean_inc(v_nextMacroScope_2886_);
lean_dec(v___x_2885_);
v___x_2895_ = lean_box(0);
v_isShared_2896_ = v_isSharedCheck_2904_;
goto v_resetjp_2894_;
}
v_resetjp_2894_:
{
lean_object* v___x_2897_; lean_object* v___x_2898_; lean_object* v___x_2900_; 
v___x_2897_ = lean_box(0);
v___x_2898_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1);
if (v_isShared_2896_ == 0)
{
lean_ctor_set(v___x_2895_, 5, v___x_2898_);
lean_ctor_set(v___x_2895_, 0, v_env_2882_);
v___x_2900_ = v___x_2895_;
goto v_reusejp_2899_;
}
else
{
lean_object* v_reuseFailAlloc_2903_; 
v_reuseFailAlloc_2903_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2903_, 0, v_env_2882_);
lean_ctor_set(v_reuseFailAlloc_2903_, 1, v_nextMacroScope_2886_);
lean_ctor_set(v_reuseFailAlloc_2903_, 2, v_ngen_2887_);
lean_ctor_set(v_reuseFailAlloc_2903_, 3, v_auxDeclNGen_2888_);
lean_ctor_set(v_reuseFailAlloc_2903_, 4, v_traceState_2889_);
lean_ctor_set(v_reuseFailAlloc_2903_, 5, v___x_2898_);
lean_ctor_set(v_reuseFailAlloc_2903_, 6, v_recordedDeps_2890_);
lean_ctor_set(v_reuseFailAlloc_2903_, 7, v_messages_2891_);
lean_ctor_set(v_reuseFailAlloc_2903_, 8, v_infoState_2892_);
lean_ctor_set(v_reuseFailAlloc_2903_, 9, v_snapshotTasks_2893_);
v___x_2900_ = v_reuseFailAlloc_2903_;
goto v_reusejp_2899_;
}
v_reusejp_2899_:
{
lean_object* v___x_2901_; lean_object* v___x_2902_; 
v___x_2901_ = lean_st_ref_put(v___y_2883_, v___x_2900_);
v___x_2902_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2902_, 0, v___x_2897_);
return v___x_2902_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_registerParametricAttributeForExt_spec__0___redArg___boxed(lean_object* v_env_2907_, lean_object* v___y_2908_, lean_object* v___y_2909_){
_start:
{
lean_object* v_res_2910_; 
v_res_2910_ = l_Lean_setEnv___at___00Lean_registerParametricAttributeForExt_spec__0___redArg(v_env_2907_, v___y_2908_);
lean_dec(v___y_2908_);
return v_res_2910_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_registerParametricAttributeForExt_spec__0(lean_object* v_env_2911_, lean_object* v___y_2912_, lean_object* v___y_2913_){
_start:
{
lean_object* v___x_2915_; 
v___x_2915_ = l_Lean_setEnv___at___00Lean_registerParametricAttributeForExt_spec__0___redArg(v_env_2911_, v___y_2913_);
return v___x_2915_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_registerParametricAttributeForExt_spec__0___boxed(lean_object* v_env_2916_, lean_object* v___y_2917_, lean_object* v___y_2918_, lean_object* v___y_2919_){
_start:
{
lean_object* v_res_2920_; 
v_res_2920_ = l_Lean_setEnv___at___00Lean_registerParametricAttributeForExt_spec__0(v_env_2916_, v___y_2917_, v___y_2918_);
lean_dec(v___y_2918_);
lean_dec_ref(v___y_2917_);
return v_res_2920_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___redArg___lam__0(lean_object* v_addEntryFn_2921_, lean_object* v___x_2922_, lean_object* v_s_2923_){
_start:
{
lean_object* v_importedEntries_2924_; lean_object* v_state_2925_; lean_object* v___x_2927_; uint8_t v_isShared_2928_; uint8_t v_isSharedCheck_2933_; 
v_importedEntries_2924_ = lean_ctor_get(v_s_2923_, 0);
v_state_2925_ = lean_ctor_get(v_s_2923_, 1);
v_isSharedCheck_2933_ = !lean_is_exclusive(v_s_2923_);
if (v_isSharedCheck_2933_ == 0)
{
v___x_2927_ = v_s_2923_;
v_isShared_2928_ = v_isSharedCheck_2933_;
goto v_resetjp_2926_;
}
else
{
lean_inc(v_state_2925_);
lean_inc(v_importedEntries_2924_);
lean_dec(v_s_2923_);
v___x_2927_ = lean_box(0);
v_isShared_2928_ = v_isSharedCheck_2933_;
goto v_resetjp_2926_;
}
v_resetjp_2926_:
{
lean_object* v_state_2929_; lean_object* v___x_2931_; 
v_state_2929_ = lean_apply_2(v_addEntryFn_2921_, v_state_2925_, v___x_2922_);
if (v_isShared_2928_ == 0)
{
lean_ctor_set(v___x_2927_, 1, v_state_2929_);
v___x_2931_ = v___x_2927_;
goto v_reusejp_2930_;
}
else
{
lean_object* v_reuseFailAlloc_2932_; 
v_reuseFailAlloc_2932_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2932_, 0, v_importedEntries_2924_);
lean_ctor_set(v_reuseFailAlloc_2932_, 1, v_state_2929_);
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
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___redArg___lam__1(lean_object* v_afterSet_2934_, lean_object* v_getParam_2935_, lean_object* v_ext_2936_, lean_object* v_toAttributeImplCore_2937_, lean_object* v_decl_2938_, lean_object* v_stx_2939_, uint8_t v_kind_2940_, lean_object* v___y_2941_, lean_object* v___y_2942_){
_start:
{
lean_object* v___y_2945_; lean_object* v___y_2946_; lean_object* v___y_2947_; uint8_t v___y_2948_; lean_object* v___y_2951_; lean_object* v___y_2952_; lean_object* v___y_2953_; lean_object* v___y_2954_; lean_object* v_nextMacroScope_2955_; lean_object* v_ngen_2956_; lean_object* v_auxDeclNGen_2957_; lean_object* v_traceState_2958_; lean_object* v_recordedDeps_2959_; lean_object* v_messages_2960_; lean_object* v_infoState_2961_; lean_object* v_snapshotTasks_2962_; lean_object* v___y_2963_; lean_object* v___y_2972_; lean_object* v___y_2973_; lean_object* v___y_2974_; uint8_t v___x_3011_; uint8_t v___x_3012_; 
v___x_3011_ = 0;
v___x_3012_ = l_Lean_instBEqAttributeKind_beq(v_kind_2940_, v___x_3011_);
if (v___x_3012_ == 0)
{
lean_object* v_name_3013_; lean_object* v___x_3014_; 
lean_dec(v_stx_2939_);
lean_dec(v_decl_2938_);
lean_dec_ref(v_ext_2936_);
lean_dec_ref(v_getParam_2935_);
lean_dec_ref(v_afterSet_2934_);
v_name_3013_ = lean_ctor_get(v_toAttributeImplCore_2937_, 1);
lean_inc(v_name_3013_);
lean_dec_ref(v_toAttributeImplCore_2937_);
v___x_3014_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg(v_name_3013_, v_kind_2940_, v___y_2941_, v___y_2942_);
return v___x_3014_;
}
else
{
goto v___jp_3005_;
}
v___jp_2944_:
{
if (v___y_2948_ == 0)
{
lean_object* v___x_2949_; 
lean_dec_ref(v___y_2947_);
v___x_2949_ = l_Lean_setEnv___at___00Lean_registerParametricAttributeForExt_spec__0___redArg(v___y_2946_, v___y_2945_);
return v___x_2949_;
}
else
{
lean_dec_ref(v___y_2946_);
return v___y_2947_;
}
}
v___jp_2950_:
{
lean_object* v___x_2964_; lean_object* v___x_2965_; lean_object* v___x_2966_; lean_object* v___x_2967_; 
v___x_2964_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1);
v___x_2965_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_2965_, 0, v___y_2963_);
lean_ctor_set(v___x_2965_, 1, v_nextMacroScope_2955_);
lean_ctor_set(v___x_2965_, 2, v_ngen_2956_);
lean_ctor_set(v___x_2965_, 3, v_auxDeclNGen_2957_);
lean_ctor_set(v___x_2965_, 4, v_traceState_2958_);
lean_ctor_set(v___x_2965_, 5, v___x_2964_);
lean_ctor_set(v___x_2965_, 6, v_recordedDeps_2959_);
lean_ctor_set(v___x_2965_, 7, v_messages_2960_);
lean_ctor_set(v___x_2965_, 8, v_infoState_2961_);
lean_ctor_set(v___x_2965_, 9, v_snapshotTasks_2962_);
v___x_2966_ = lean_st_ref_put(v___y_2952_, v___x_2965_);
lean_inc(v___y_2952_);
lean_inc_ref(v___y_2954_);
v___x_2967_ = lean_apply_5(v_afterSet_2934_, v_decl_2938_, v___y_2951_, v___y_2954_, v___y_2952_, lean_box(0));
if (lean_obj_tag(v___x_2967_) == 0)
{
lean_dec_ref(v___y_2953_);
return v___x_2967_;
}
else
{
lean_object* v_a_2968_; uint8_t v___x_2969_; 
v_a_2968_ = lean_ctor_get(v___x_2967_, 0);
lean_inc(v_a_2968_);
v___x_2969_ = l_Lean_Exception_isInterrupt(v_a_2968_);
if (v___x_2969_ == 0)
{
uint8_t v___x_2970_; 
v___x_2970_ = l_Lean_Exception_isRuntime(v_a_2968_);
v___y_2945_ = v___y_2952_;
v___y_2946_ = v___y_2953_;
v___y_2947_ = v___x_2967_;
v___y_2948_ = v___x_2970_;
goto v___jp_2944_;
}
else
{
lean_dec(v_a_2968_);
v___y_2945_ = v___y_2952_;
v___y_2946_ = v___y_2953_;
v___y_2947_ = v___x_2967_;
v___y_2948_ = v___x_2969_;
goto v___jp_2944_;
}
}
}
v___jp_2971_:
{
lean_object* v___x_2975_; 
lean_inc(v___y_2974_);
lean_inc_ref(v___y_2973_);
lean_inc(v_decl_2938_);
v___x_2975_ = lean_apply_5(v_getParam_2935_, v_decl_2938_, v_stx_2939_, v___y_2973_, v___y_2974_, lean_box(0));
if (lean_obj_tag(v___x_2975_) == 0)
{
lean_object* v_a_2976_; lean_object* v___x_2977_; lean_object* v_toEnvExtension_2978_; lean_object* v_env_2979_; lean_object* v_nextMacroScope_2980_; lean_object* v_ngen_2981_; lean_object* v_auxDeclNGen_2982_; lean_object* v_traceState_2983_; lean_object* v_recordedDeps_2984_; lean_object* v_messages_2985_; lean_object* v_infoState_2986_; lean_object* v_snapshotTasks_2987_; lean_object* v_addEntryFn_2988_; lean_object* v_asyncMode_2989_; uint8_t v_logWrites_2990_; lean_object* v___x_2991_; lean_object* v___f_2992_; uint8_t v___x_2993_; 
v_a_2976_ = lean_ctor_get(v___x_2975_, 0);
lean_inc_n(v_a_2976_, 2);
lean_dec_ref_known(v___x_2975_, 1);
v___x_2977_ = lean_st_ref_take(v___y_2974_);
v_toEnvExtension_2978_ = lean_ctor_get(v_ext_2936_, 0);
lean_inc_ref(v_toEnvExtension_2978_);
v_env_2979_ = lean_ctor_get(v___x_2977_, 0);
lean_inc_ref(v_env_2979_);
v_nextMacroScope_2980_ = lean_ctor_get(v___x_2977_, 1);
lean_inc(v_nextMacroScope_2980_);
v_ngen_2981_ = lean_ctor_get(v___x_2977_, 2);
lean_inc_ref(v_ngen_2981_);
v_auxDeclNGen_2982_ = lean_ctor_get(v___x_2977_, 3);
lean_inc_ref(v_auxDeclNGen_2982_);
v_traceState_2983_ = lean_ctor_get(v___x_2977_, 4);
lean_inc_ref(v_traceState_2983_);
v_recordedDeps_2984_ = lean_ctor_get(v___x_2977_, 6);
lean_inc_ref(v_recordedDeps_2984_);
v_messages_2985_ = lean_ctor_get(v___x_2977_, 7);
lean_inc_ref(v_messages_2985_);
v_infoState_2986_ = lean_ctor_get(v___x_2977_, 8);
lean_inc_ref(v_infoState_2986_);
v_snapshotTasks_2987_ = lean_ctor_get(v___x_2977_, 9);
lean_inc_ref(v_snapshotTasks_2987_);
lean_dec(v___x_2977_);
v_addEntryFn_2988_ = lean_ctor_get(v_ext_2936_, 3);
lean_inc(v_addEntryFn_2988_);
lean_dec_ref(v_ext_2936_);
v_asyncMode_2989_ = lean_ctor_get(v_toEnvExtension_2978_, 2);
lean_inc(v_asyncMode_2989_);
v_logWrites_2990_ = lean_ctor_get_uint8(v_toEnvExtension_2978_, sizeof(void*)*6);
lean_inc(v_decl_2938_);
v___x_2991_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2991_, 0, v_decl_2938_);
lean_ctor_set(v___x_2991_, 1, v_a_2976_);
v___f_2992_ = lean_alloc_closure((void*)(l_Lean_registerParametricAttributeForExt___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2992_, 0, v_addEntryFn_2988_);
lean_closure_set(v___f_2992_, 1, v___x_2991_);
v___x_2993_ = 1;
if (v_logWrites_2990_ == 0)
{
lean_object* v___x_2994_; 
lean_inc(v_decl_2938_);
v___x_2994_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_2978_, v_env_2979_, v___f_2992_, v_asyncMode_2989_, v_decl_2938_, v___x_2993_);
lean_dec(v_asyncMode_2989_);
v___y_2951_ = v_a_2976_;
v___y_2952_ = v___y_2974_;
v___y_2953_ = v___y_2972_;
v___y_2954_ = v___y_2973_;
v_nextMacroScope_2955_ = v_nextMacroScope_2980_;
v_ngen_2956_ = v_ngen_2981_;
v_auxDeclNGen_2957_ = v_auxDeclNGen_2982_;
v_traceState_2958_ = v_traceState_2983_;
v_recordedDeps_2959_ = v_recordedDeps_2984_;
v_messages_2960_ = v_messages_2985_;
v_infoState_2961_ = v_infoState_2986_;
v_snapshotTasks_2962_ = v_snapshotTasks_2987_;
v___y_2963_ = v___x_2994_;
goto v___jp_2950_;
}
else
{
lean_object* v___x_2995_; lean_object* v___x_2996_; 
lean_inc_n(v_decl_2938_, 2);
v___x_2995_ = l_Lean_Environment_logDeclChange(v_env_2979_, v_decl_2938_);
v___x_2996_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_2978_, v___x_2995_, v___f_2992_, v_asyncMode_2989_, v_decl_2938_, v___x_2993_);
lean_dec(v_asyncMode_2989_);
v___y_2951_ = v_a_2976_;
v___y_2952_ = v___y_2974_;
v___y_2953_ = v___y_2972_;
v___y_2954_ = v___y_2973_;
v_nextMacroScope_2955_ = v_nextMacroScope_2980_;
v_ngen_2956_ = v_ngen_2981_;
v_auxDeclNGen_2957_ = v_auxDeclNGen_2982_;
v_traceState_2958_ = v_traceState_2983_;
v_recordedDeps_2959_ = v_recordedDeps_2984_;
v_messages_2960_ = v_messages_2985_;
v_infoState_2961_ = v_infoState_2986_;
v_snapshotTasks_2962_ = v_snapshotTasks_2987_;
v___y_2963_ = v___x_2996_;
goto v___jp_2950_;
}
}
else
{
lean_object* v_a_2997_; lean_object* v___x_2999_; uint8_t v_isShared_3000_; uint8_t v_isSharedCheck_3004_; 
lean_dec_ref(v___y_2972_);
lean_dec(v_decl_2938_);
lean_dec_ref(v_ext_2936_);
lean_dec_ref(v_afterSet_2934_);
v_a_2997_ = lean_ctor_get(v___x_2975_, 0);
v_isSharedCheck_3004_ = !lean_is_exclusive(v___x_2975_);
if (v_isSharedCheck_3004_ == 0)
{
v___x_2999_ = v___x_2975_;
v_isShared_3000_ = v_isSharedCheck_3004_;
goto v_resetjp_2998_;
}
else
{
lean_inc(v_a_2997_);
lean_dec(v___x_2975_);
v___x_2999_ = lean_box(0);
v_isShared_3000_ = v_isSharedCheck_3004_;
goto v_resetjp_2998_;
}
v_resetjp_2998_:
{
lean_object* v___x_3002_; 
if (v_isShared_3000_ == 0)
{
v___x_3002_ = v___x_2999_;
goto v_reusejp_3001_;
}
else
{
lean_object* v_reuseFailAlloc_3003_; 
v_reuseFailAlloc_3003_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3003_, 0, v_a_2997_);
v___x_3002_ = v_reuseFailAlloc_3003_;
goto v_reusejp_3001_;
}
v_reusejp_3001_:
{
return v___x_3002_;
}
}
}
}
v___jp_3005_:
{
lean_object* v___x_3006_; lean_object* v_env_3007_; lean_object* v___x_3008_; 
v___x_3006_ = lean_st_ref_get(v___y_2942_);
v_env_3007_ = lean_ctor_get(v___x_3006_, 0);
lean_inc_ref(v_env_3007_);
lean_dec(v___x_3006_);
v___x_3008_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3007_, v_decl_2938_);
if (lean_obj_tag(v___x_3008_) == 0)
{
lean_dec_ref(v_toAttributeImplCore_2937_);
v___y_2972_ = v_env_3007_;
v___y_2973_ = v___y_2941_;
v___y_2974_ = v___y_2942_;
goto v___jp_2971_;
}
else
{
lean_object* v_name_3009_; lean_object* v___x_3010_; 
lean_dec_ref_known(v___x_3008_, 1);
lean_dec_ref(v_env_3007_);
lean_dec(v_stx_2939_);
lean_dec_ref(v_ext_2936_);
lean_dec_ref(v_getParam_2935_);
lean_dec_ref(v_afterSet_2934_);
v_name_3009_ = lean_ctor_get(v_toAttributeImplCore_2937_, 1);
lean_inc(v_name_3009_);
lean_dec_ref(v_toAttributeImplCore_2937_);
v___x_3010_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg(v_name_3009_, v_decl_2938_, v___y_2941_, v___y_2942_);
return v___x_3010_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___redArg___lam__1___boxed(lean_object* v_afterSet_3015_, lean_object* v_getParam_3016_, lean_object* v_ext_3017_, lean_object* v_toAttributeImplCore_3018_, lean_object* v_decl_3019_, lean_object* v_stx_3020_, lean_object* v_kind_3021_, lean_object* v___y_3022_, lean_object* v___y_3023_, lean_object* v___y_3024_){
_start:
{
uint8_t v_kind_boxed_3025_; lean_object* v_res_3026_; 
v_kind_boxed_3025_ = lean_unbox(v_kind_3021_);
v_res_3026_ = l_Lean_registerParametricAttributeForExt___redArg___lam__1(v_afterSet_3015_, v_getParam_3016_, v_ext_3017_, v_toAttributeImplCore_3018_, v_decl_3019_, v_stx_3020_, v_kind_boxed_3025_, v___y_3022_, v___y_3023_);
lean_dec(v___y_3023_);
lean_dec_ref(v___y_3022_);
return v_res_3026_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___redArg___lam__2(lean_object* v_toAttributeImplCore_3027_, lean_object* v_decl_3028_, lean_object* v___y_3029_, lean_object* v___y_3030_){
_start:
{
lean_object* v_name_3032_; lean_object* v___x_3033_; lean_object* v___x_3034_; lean_object* v___x_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; 
v_name_3032_ = lean_ctor_get(v_toAttributeImplCore_3027_, 1);
lean_inc(v_name_3032_);
lean_dec_ref(v_toAttributeImplCore_3027_);
v___x_3033_ = lean_obj_once(&l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1, &l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1_once, _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1);
v___x_3034_ = l_Lean_MessageData_ofName(v_name_3032_);
v___x_3035_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3035_, 0, v___x_3033_);
lean_ctor_set(v___x_3035_, 1, v___x_3034_);
v___x_3036_ = lean_obj_once(&l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3, &l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3_once, _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3);
v___x_3037_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3037_, 0, v___x_3035_);
lean_ctor_set(v___x_3037_, 1, v___x_3036_);
v___x_3038_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_3037_, v___y_3029_, v___y_3030_);
return v___x_3038_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___redArg___lam__2___boxed(lean_object* v_toAttributeImplCore_3039_, lean_object* v_decl_3040_, lean_object* v___y_3041_, lean_object* v___y_3042_, lean_object* v___y_3043_){
_start:
{
lean_object* v_res_3044_; 
v_res_3044_ = l_Lean_registerParametricAttributeForExt___redArg___lam__2(v_toAttributeImplCore_3039_, v_decl_3040_, v___y_3041_, v___y_3042_);
lean_dec(v___y_3042_);
lean_dec_ref(v___y_3041_);
lean_dec(v_decl_3040_);
return v_res_3044_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___redArg(lean_object* v_impl_3045_, lean_object* v_ext_3046_){
_start:
{
lean_object* v_toAttributeImplCore_3048_; lean_object* v_getParam_3049_; lean_object* v_afterSet_3050_; uint8_t v_preserveOrder_3051_; lean_object* v___f_3052_; lean_object* v___f_3053_; lean_object* v_attrImpl_3054_; lean_object* v___x_3055_; 
v_toAttributeImplCore_3048_ = lean_ctor_get(v_impl_3045_, 0);
lean_inc_ref_n(v_toAttributeImplCore_3048_, 3);
v_getParam_3049_ = lean_ctor_get(v_impl_3045_, 1);
lean_inc_ref(v_getParam_3049_);
v_afterSet_3050_ = lean_ctor_get(v_impl_3045_, 2);
lean_inc_ref(v_afterSet_3050_);
v_preserveOrder_3051_ = lean_ctor_get_uint8(v_impl_3045_, sizeof(void*)*4);
lean_dec_ref(v_impl_3045_);
lean_inc_ref(v_ext_3046_);
v___f_3052_ = lean_alloc_closure((void*)(l_Lean_registerParametricAttributeForExt___redArg___lam__1___boxed), 10, 4);
lean_closure_set(v___f_3052_, 0, v_afterSet_3050_);
lean_closure_set(v___f_3052_, 1, v_getParam_3049_);
lean_closure_set(v___f_3052_, 2, v_ext_3046_);
lean_closure_set(v___f_3052_, 3, v_toAttributeImplCore_3048_);
v___f_3053_ = lean_alloc_closure((void*)(l_Lean_registerParametricAttributeForExt___redArg___lam__2___boxed), 5, 1);
lean_closure_set(v___f_3053_, 0, v_toAttributeImplCore_3048_);
v_attrImpl_3054_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_attrImpl_3054_, 0, v_toAttributeImplCore_3048_);
lean_ctor_set(v_attrImpl_3054_, 1, v___f_3052_);
lean_ctor_set(v_attrImpl_3054_, 2, v___f_3053_);
lean_inc_ref(v_attrImpl_3054_);
v___x_3055_ = l_Lean_registerBuiltinAttribute(v_attrImpl_3054_);
if (lean_obj_tag(v___x_3055_) == 0)
{
lean_object* v___x_3057_; uint8_t v_isShared_3058_; uint8_t v_isSharedCheck_3063_; 
v_isSharedCheck_3063_ = !lean_is_exclusive(v___x_3055_);
if (v_isSharedCheck_3063_ == 0)
{
lean_object* v_unused_3064_; 
v_unused_3064_ = lean_ctor_get(v___x_3055_, 0);
lean_dec(v_unused_3064_);
v___x_3057_ = v___x_3055_;
v_isShared_3058_ = v_isSharedCheck_3063_;
goto v_resetjp_3056_;
}
else
{
lean_dec(v___x_3055_);
v___x_3057_ = lean_box(0);
v_isShared_3058_ = v_isSharedCheck_3063_;
goto v_resetjp_3056_;
}
v_resetjp_3056_:
{
lean_object* v___x_3059_; lean_object* v___x_3061_; 
v___x_3059_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3059_, 0, v_attrImpl_3054_);
lean_ctor_set(v___x_3059_, 1, v_ext_3046_);
lean_ctor_set_uint8(v___x_3059_, sizeof(void*)*2, v_preserveOrder_3051_);
if (v_isShared_3058_ == 0)
{
lean_ctor_set(v___x_3057_, 0, v___x_3059_);
v___x_3061_ = v___x_3057_;
goto v_reusejp_3060_;
}
else
{
lean_object* v_reuseFailAlloc_3062_; 
v_reuseFailAlloc_3062_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3062_, 0, v___x_3059_);
v___x_3061_ = v_reuseFailAlloc_3062_;
goto v_reusejp_3060_;
}
v_reusejp_3060_:
{
return v___x_3061_;
}
}
}
else
{
lean_object* v_a_3065_; lean_object* v___x_3067_; uint8_t v_isShared_3068_; uint8_t v_isSharedCheck_3072_; 
lean_dec_ref_known(v_attrImpl_3054_, 3);
lean_dec_ref(v_ext_3046_);
v_a_3065_ = lean_ctor_get(v___x_3055_, 0);
v_isSharedCheck_3072_ = !lean_is_exclusive(v___x_3055_);
if (v_isSharedCheck_3072_ == 0)
{
v___x_3067_ = v___x_3055_;
v_isShared_3068_ = v_isSharedCheck_3072_;
goto v_resetjp_3066_;
}
else
{
lean_inc(v_a_3065_);
lean_dec(v___x_3055_);
v___x_3067_ = lean_box(0);
v_isShared_3068_ = v_isSharedCheck_3072_;
goto v_resetjp_3066_;
}
v_resetjp_3066_:
{
lean_object* v___x_3070_; 
if (v_isShared_3068_ == 0)
{
v___x_3070_ = v___x_3067_;
goto v_reusejp_3069_;
}
else
{
lean_object* v_reuseFailAlloc_3071_; 
v_reuseFailAlloc_3071_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3071_, 0, v_a_3065_);
v___x_3070_ = v_reuseFailAlloc_3071_;
goto v_reusejp_3069_;
}
v_reusejp_3069_:
{
return v___x_3070_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___redArg___boxed(lean_object* v_impl_3073_, lean_object* v_ext_3074_, lean_object* v_a_3075_){
_start:
{
lean_object* v_res_3076_; 
v_res_3076_ = l_Lean_registerParametricAttributeForExt___redArg(v_impl_3073_, v_ext_3074_);
return v_res_3076_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt(lean_object* v_00_u03b1_3077_, lean_object* v_impl_3078_, lean_object* v_ext_3079_){
_start:
{
lean_object* v___x_3081_; 
v___x_3081_ = l_Lean_registerParametricAttributeForExt___redArg(v_impl_3078_, v_ext_3079_);
return v___x_3081_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___boxed(lean_object* v_00_u03b1_3082_, lean_object* v_impl_3083_, lean_object* v_ext_3084_, lean_object* v_a_3085_){
_start:
{
lean_object* v_res_3086_; 
v_res_3086_ = l_Lean_registerParametricAttributeForExt(v_00_u03b1_3082_, v_impl_3083_, v_ext_3084_);
return v_res_3086_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg(lean_object* v_impl_3087_){
_start:
{
lean_object* v_toAttributeImplCore_3089_; uint8_t v_preserveOrder_3090_; lean_object* v_filterExport_3091_; lean_object* v_ref_3092_; uint8_t v___x_3093_; lean_object* v___x_3094_; 
v_toAttributeImplCore_3089_ = lean_ctor_get(v_impl_3087_, 0);
v_preserveOrder_3090_ = lean_ctor_get_uint8(v_impl_3087_, sizeof(void*)*4);
v_filterExport_3091_ = lean_ctor_get(v_impl_3087_, 3);
v_ref_3092_ = lean_ctor_get(v_toAttributeImplCore_3089_, 0);
v___x_3093_ = 0;
lean_inc_ref(v_filterExport_3091_);
lean_inc(v_ref_3092_);
v___x_3094_ = l_Lean_registerParametricAttributeExt___redArg(v_ref_3092_, v_preserveOrder_3090_, v_filterExport_3091_, v___x_3093_);
if (lean_obj_tag(v___x_3094_) == 0)
{
lean_object* v_a_3095_; lean_object* v___x_3096_; 
v_a_3095_ = lean_ctor_get(v___x_3094_, 0);
lean_inc(v_a_3095_);
lean_dec_ref_known(v___x_3094_, 1);
v___x_3096_ = l_Lean_registerParametricAttributeForExt___redArg(v_impl_3087_, v_a_3095_);
return v___x_3096_;
}
else
{
lean_object* v_a_3097_; lean_object* v___x_3099_; uint8_t v_isShared_3100_; uint8_t v_isSharedCheck_3104_; 
lean_dec_ref(v_impl_3087_);
v_a_3097_ = lean_ctor_get(v___x_3094_, 0);
v_isSharedCheck_3104_ = !lean_is_exclusive(v___x_3094_);
if (v_isSharedCheck_3104_ == 0)
{
v___x_3099_ = v___x_3094_;
v_isShared_3100_ = v_isSharedCheck_3104_;
goto v_resetjp_3098_;
}
else
{
lean_inc(v_a_3097_);
lean_dec(v___x_3094_);
v___x_3099_ = lean_box(0);
v_isShared_3100_ = v_isSharedCheck_3104_;
goto v_resetjp_3098_;
}
v_resetjp_3098_:
{
lean_object* v___x_3102_; 
if (v_isShared_3100_ == 0)
{
v___x_3102_ = v___x_3099_;
goto v_reusejp_3101_;
}
else
{
lean_object* v_reuseFailAlloc_3103_; 
v_reuseFailAlloc_3103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3103_, 0, v_a_3097_);
v___x_3102_ = v_reuseFailAlloc_3103_;
goto v_reusejp_3101_;
}
v_reusejp_3101_:
{
return v___x_3102_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___boxed(lean_object* v_impl_3105_, lean_object* v_a_3106_){
_start:
{
lean_object* v_res_3107_; 
v_res_3107_ = l_Lean_registerParametricAttribute___redArg(v_impl_3105_);
return v_res_3107_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute(lean_object* v_00_u03b1_3108_, lean_object* v_impl_3109_){
_start:
{
lean_object* v___x_3111_; 
v___x_3111_ = l_Lean_registerParametricAttribute___redArg(v_impl_3109_);
return v___x_3111_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___boxed(lean_object* v_00_u03b1_3112_, lean_object* v_impl_3113_, lean_object* v_a_3114_){
_start:
{
lean_object* v_res_3115_; 
v_res_3115_ = l_Lean_registerParametricAttribute(v_00_u03b1_3112_, v_impl_3113_);
return v_res_3115_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___lam__1(lean_object* v_decl_3116_, lean_object* v___x_3117_, lean_object* v___x_3118_, lean_object* v_a_3119_, lean_object* v_x_3120_, lean_object* v___y_3121_){
_start:
{
lean_object* v_fst_3122_; uint8_t v___x_3123_; 
v_fst_3122_ = lean_ctor_get(v_a_3119_, 0);
v___x_3123_ = lean_name_eq(v_fst_3122_, v_decl_3116_);
if (v___x_3123_ == 0)
{
lean_object* v___x_3124_; 
lean_dec_ref(v_a_3119_);
v___x_3124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3124_, 0, v___x_3117_);
return v___x_3124_;
}
else
{
lean_object* v___x_3125_; lean_object* v___x_3126_; lean_object* v___x_3127_; lean_object* v___x_3128_; 
lean_dec_ref(v___x_3117_);
v___x_3125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3125_, 0, v_a_3119_);
v___x_3126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3126_, 0, v___x_3125_);
v___x_3127_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3127_, 0, v___x_3126_);
lean_ctor_set(v___x_3127_, 1, v___x_3118_);
v___x_3128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3128_, 0, v___x_3127_);
return v___x_3128_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___lam__1___boxed(lean_object* v_decl_3129_, lean_object* v___x_3130_, lean_object* v___x_3131_, lean_object* v_a_3132_, lean_object* v_x_3133_, lean_object* v___y_3134_){
_start:
{
lean_object* v_res_3135_; 
v_res_3135_ = l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___lam__1(v_decl_3129_, v___x_3130_, v___x_3131_, v_a_3132_, v_x_3133_, v___y_3134_);
lean_dec_ref(v___y_3134_);
lean_dec(v_decl_3129_);
return v_res_3135_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg(lean_object* v_inst_3163_, lean_object* v_ext_3164_, uint8_t v_preserveOrder_3165_, lean_object* v_env_3166_, lean_object* v_decl_3167_){
_start:
{
lean_object* v___y_3169_; lean_object* v___x_3180_; lean_object* v___x_3181_; 
v___x_3180_ = ((lean_object*)(l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__0));
v___x_3181_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3166_, v_decl_3167_);
if (lean_obj_tag(v___x_3181_) == 0)
{
lean_object* v_toEnvExtension_3182_; lean_object* v_asyncMode_3183_; lean_object* v___x_3184_; uint8_t v___x_3185_; lean_object* v___x_3186_; lean_object* v_snd_3187_; lean_object* v___x_3188_; 
lean_dec(v_inst_3163_);
v_toEnvExtension_3182_ = lean_ctor_get(v_ext_3164_, 0);
v_asyncMode_3183_ = lean_ctor_get(v_toEnvExtension_3182_, 2);
v___x_3184_ = lean_box(0);
v___x_3185_ = 0;
v___x_3186_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3180_, v_ext_3164_, v_env_3166_, v_asyncMode_3183_, v___x_3184_, v___x_3185_);
v_snd_3187_ = lean_ctor_get(v___x_3186_, 1);
lean_inc(v_snd_3187_);
lean_dec(v___x_3186_);
v___x_3188_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_snd_3187_, v_decl_3167_);
lean_dec(v_decl_3167_);
lean_dec(v_snd_3187_);
return v___x_3188_;
}
else
{
if (v_preserveOrder_3165_ == 0)
{
lean_object* v_val_3189_; uint8_t v___x_3190_; lean_object* v___x_3191_; lean_object* v___x_3192_; lean_object* v___x_3193_; uint8_t v___x_3194_; 
v_val_3189_ = lean_ctor_get(v___x_3181_, 0);
lean_inc(v_val_3189_);
lean_dec_ref_known(v___x_3181_, 1);
v___x_3190_ = 0;
v___x_3191_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_3180_, v_ext_3164_, v_env_3166_, v_val_3189_, v___x_3190_);
lean_dec(v_val_3189_);
lean_dec_ref(v_env_3166_);
v___x_3192_ = lean_unsigned_to_nat(0u);
v___x_3193_ = lean_array_get_size(v___x_3191_);
v___x_3194_ = lean_nat_dec_lt(v___x_3192_, v___x_3193_);
if (v___x_3194_ == 0)
{
lean_object* v___x_3195_; 
lean_dec_ref(v___x_3191_);
lean_dec(v_decl_3167_);
lean_dec(v_inst_3163_);
v___x_3195_ = lean_box(0);
return v___x_3195_;
}
else
{
lean_object* v___x_3196_; lean_object* v___x_3197_; uint8_t v___x_3198_; 
v___x_3196_ = lean_unsigned_to_nat(1u);
v___x_3197_ = lean_nat_sub(v___x_3193_, v___x_3196_);
v___x_3198_ = lean_nat_dec_le(v___x_3192_, v___x_3197_);
if (v___x_3198_ == 0)
{
lean_object* v___x_3199_; 
lean_dec(v___x_3197_);
lean_dec_ref(v___x_3191_);
lean_dec(v_decl_3167_);
lean_dec(v_inst_3163_);
v___x_3199_ = lean_box(0);
return v___x_3199_;
}
else
{
lean_object* v___f_3200_; lean_object* v___x_3201_; lean_object* v___x_3202_; lean_object* v___x_3203_; 
v___f_3200_ = ((lean_object*)(l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__1));
v___x_3201_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3201_, 0, v_decl_3167_);
lean_ctor_set(v___x_3201_, 1, v_inst_3163_);
v___x_3202_ = ((lean_object*)(l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__2));
v___x_3203_ = l_Array_binSearchAux___redArg(v___f_3200_, v___x_3202_, v___x_3191_, v___x_3201_, v___x_3192_, v___x_3197_);
lean_dec_ref(v___x_3191_);
v___y_3169_ = v___x_3203_;
goto v___jp_3168_;
}
}
}
else
{
lean_object* v_val_3204_; uint8_t v___x_3205_; lean_object* v___x_3206_; lean_object* v___x_3207_; lean_object* v___x_3208_; lean_object* v___x_3209_; lean_object* v___x_3210_; lean_object* v___f_3211_; size_t v_sz_3212_; size_t v___x_3213_; lean_object* v___x_3214_; lean_object* v_fst_3215_; 
lean_dec(v_inst_3163_);
v_val_3204_ = lean_ctor_get(v___x_3181_, 0);
lean_inc(v_val_3204_);
lean_dec_ref_known(v___x_3181_, 1);
v___x_3205_ = 0;
v___x_3206_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_3180_, v_ext_3164_, v_env_3166_, v_val_3204_, v___x_3205_);
lean_dec(v_val_3204_);
lean_dec_ref(v_env_3166_);
v___x_3207_ = ((lean_object*)(l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__12));
v___x_3208_ = lean_box(0);
v___x_3209_ = lean_box(0);
v___x_3210_ = ((lean_object*)(l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__13));
v___f_3211_ = lean_alloc_closure((void*)(l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___lam__1___boxed), 6, 3);
lean_closure_set(v___f_3211_, 0, v_decl_3167_);
lean_closure_set(v___f_3211_, 1, v___x_3210_);
lean_closure_set(v___f_3211_, 2, v___x_3209_);
v_sz_3212_ = lean_array_size(v___x_3206_);
v___x_3213_ = ((size_t)0ULL);
v___x_3214_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_3207_, v___x_3206_, v___f_3211_, v_sz_3212_, v___x_3213_, v___x_3210_);
v_fst_3215_ = lean_ctor_get(v___x_3214_, 0);
lean_inc(v_fst_3215_);
lean_dec(v___x_3214_);
if (lean_obj_tag(v_fst_3215_) == 0)
{
return v___x_3208_;
}
else
{
lean_object* v_val_3216_; 
v_val_3216_ = lean_ctor_get(v_fst_3215_, 0);
lean_inc(v_val_3216_);
lean_dec_ref_known(v_fst_3215_, 1);
v___y_3169_ = v_val_3216_;
goto v___jp_3168_;
}
}
}
v___jp_3168_:
{
if (lean_obj_tag(v___y_3169_) == 0)
{
lean_object* v___x_3170_; 
v___x_3170_ = lean_box(0);
return v___x_3170_;
}
else
{
lean_object* v_val_3171_; lean_object* v___x_3173_; uint8_t v_isShared_3174_; uint8_t v_isSharedCheck_3179_; 
v_val_3171_ = lean_ctor_get(v___y_3169_, 0);
v_isSharedCheck_3179_ = !lean_is_exclusive(v___y_3169_);
if (v_isSharedCheck_3179_ == 0)
{
v___x_3173_ = v___y_3169_;
v_isShared_3174_ = v_isSharedCheck_3179_;
goto v_resetjp_3172_;
}
else
{
lean_inc(v_val_3171_);
lean_dec(v___y_3169_);
v___x_3173_ = lean_box(0);
v_isShared_3174_ = v_isSharedCheck_3179_;
goto v_resetjp_3172_;
}
v_resetjp_3172_:
{
lean_object* v_snd_3175_; lean_object* v___x_3177_; 
v_snd_3175_ = lean_ctor_get(v_val_3171_, 1);
lean_inc(v_snd_3175_);
lean_dec(v_val_3171_);
if (v_isShared_3174_ == 0)
{
lean_ctor_set(v___x_3173_, 0, v_snd_3175_);
v___x_3177_ = v___x_3173_;
goto v_reusejp_3176_;
}
else
{
lean_object* v_reuseFailAlloc_3178_; 
v_reuseFailAlloc_3178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3178_, 0, v_snd_3175_);
v___x_3177_ = v_reuseFailAlloc_3178_;
goto v_reusejp_3176_;
}
v_reusejp_3176_:
{
return v___x_3177_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___boxed(lean_object* v_inst_3217_, lean_object* v_ext_3218_, lean_object* v_preserveOrder_3219_, lean_object* v_env_3220_, lean_object* v_decl_3221_){
_start:
{
uint8_t v_preserveOrder_boxed_3222_; lean_object* v_res_3223_; 
v_preserveOrder_boxed_3222_ = lean_unbox(v_preserveOrder_3219_);
v_res_3223_ = l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg(v_inst_3217_, v_ext_3218_, v_preserveOrder_boxed_3222_, v_env_3220_, v_decl_3221_);
lean_dec_ref(v_ext_3218_);
return v_res_3223_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f(lean_object* v_00_u03b1_3224_, lean_object* v_inst_3225_, lean_object* v_ext_3226_, uint8_t v_preserveOrder_3227_, lean_object* v_env_3228_, lean_object* v_decl_3229_){
_start:
{
lean_object* v___x_3230_; 
v___x_3230_ = l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg(v_inst_3225_, v_ext_3226_, v_preserveOrder_3227_, v_env_3228_, v_decl_3229_);
return v___x_3230_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f___boxed(lean_object* v_00_u03b1_3231_, lean_object* v_inst_3232_, lean_object* v_ext_3233_, lean_object* v_preserveOrder_3234_, lean_object* v_env_3235_, lean_object* v_decl_3236_){
_start:
{
uint8_t v_preserveOrder_boxed_3237_; lean_object* v_res_3238_; 
v_preserveOrder_boxed_3237_ = lean_unbox(v_preserveOrder_3234_);
v_res_3238_ = l_Lean_ParametricAttribute_getParamFromExt_x3f(v_00_u03b1_3231_, v_inst_3232_, v_ext_3233_, v_preserveOrder_boxed_3237_, v_env_3235_, v_decl_3236_);
lean_dec_ref(v_ext_3233_);
return v_res_3238_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParam_x3f___redArg(lean_object* v_inst_3239_, lean_object* v_attr_3240_, lean_object* v_env_3241_, lean_object* v_decl_3242_){
_start:
{
lean_object* v_ext_3243_; uint8_t v_preserveOrder_3244_; lean_object* v___x_3245_; 
v_ext_3243_ = lean_ctor_get(v_attr_3240_, 1);
v_preserveOrder_3244_ = lean_ctor_get_uint8(v_attr_3240_, sizeof(void*)*2);
v___x_3245_ = l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg(v_inst_3239_, v_ext_3243_, v_preserveOrder_3244_, v_env_3241_, v_decl_3242_);
return v___x_3245_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParam_x3f___redArg___boxed(lean_object* v_inst_3246_, lean_object* v_attr_3247_, lean_object* v_env_3248_, lean_object* v_decl_3249_){
_start:
{
lean_object* v_res_3250_; 
v_res_3250_ = l_Lean_ParametricAttribute_getParam_x3f___redArg(v_inst_3246_, v_attr_3247_, v_env_3248_, v_decl_3249_);
lean_dec_ref(v_attr_3247_);
return v_res_3250_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParam_x3f(lean_object* v_00_u03b1_3251_, lean_object* v_inst_3252_, lean_object* v_attr_3253_, lean_object* v_env_3254_, lean_object* v_decl_3255_){
_start:
{
lean_object* v___x_3256_; 
v___x_3256_ = l_Lean_ParametricAttribute_getParam_x3f___redArg(v_inst_3252_, v_attr_3253_, v_env_3254_, v_decl_3255_);
return v___x_3256_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParam_x3f___boxed(lean_object* v_00_u03b1_3257_, lean_object* v_inst_3258_, lean_object* v_attr_3259_, lean_object* v_env_3260_, lean_object* v_decl_3261_){
_start:
{
lean_object* v_res_3262_; 
v_res_3262_ = l_Lean_ParametricAttribute_getParam_x3f(v_00_u03b1_3257_, v_inst_3258_, v_attr_3259_, v_env_3260_, v_decl_3261_);
lean_dec_ref(v_attr_3259_);
return v_res_3262_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_setParamFromExt___redArg(lean_object* v_ext_3267_, lean_object* v_attr_3268_, lean_object* v_env_3269_, lean_object* v_decl_3270_, lean_object* v_param_3271_){
_start:
{
lean_object* v___x_3272_; 
v___x_3272_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3269_, v_decl_3270_);
if (lean_obj_tag(v___x_3272_) == 0)
{
lean_object* v_toEnvExtension_3273_; lean_object* v_addEntryFn_3274_; lean_object* v_asyncMode_3275_; uint8_t v_logWrites_3276_; uint8_t v___x_3277_; lean_object* v___x_3278_; lean_object* v___x_3279_; lean_object* v___x_3280_; lean_object* v_snd_3281_; lean_object* v___x_3283_; uint8_t v_isShared_3284_; uint8_t v_isSharedCheck_3316_; 
v_toEnvExtension_3273_ = lean_ctor_get(v_ext_3267_, 0);
lean_inc_ref(v_toEnvExtension_3273_);
v_addEntryFn_3274_ = lean_ctor_get(v_ext_3267_, 3);
lean_inc(v_addEntryFn_3274_);
v_asyncMode_3275_ = lean_ctor_get(v_toEnvExtension_3273_, 2);
lean_inc(v_asyncMode_3275_);
v_logWrites_3276_ = lean_ctor_get_uint8(v_toEnvExtension_3273_, sizeof(void*)*6);
v___x_3277_ = 0;
v___x_3278_ = ((lean_object*)(l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__0));
v___x_3279_ = lean_box(0);
lean_inc_ref(v_env_3269_);
v___x_3280_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3278_, v_ext_3267_, v_env_3269_, v_asyncMode_3275_, v___x_3279_, v___x_3277_);
lean_dec_ref(v_ext_3267_);
v_snd_3281_ = lean_ctor_get(v___x_3280_, 1);
v_isSharedCheck_3316_ = !lean_is_exclusive(v___x_3280_);
if (v_isSharedCheck_3316_ == 0)
{
lean_object* v_unused_3317_; 
v_unused_3317_ = lean_ctor_get(v___x_3280_, 0);
lean_dec(v_unused_3317_);
v___x_3283_ = v___x_3280_;
v_isShared_3284_ = v_isSharedCheck_3316_;
goto v_resetjp_3282_;
}
else
{
lean_inc(v_snd_3281_);
lean_dec(v___x_3280_);
v___x_3283_ = lean_box(0);
v_isShared_3284_ = v_isSharedCheck_3316_;
goto v_resetjp_3282_;
}
v_resetjp_3282_:
{
lean_object* v___x_3285_; 
v___x_3285_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_snd_3281_, v_decl_3270_);
lean_dec(v_snd_3281_);
if (lean_obj_tag(v___x_3285_) == 0)
{
lean_object* v___x_3287_; 
lean_dec_ref(v_attr_3268_);
if (v_isShared_3284_ == 0)
{
lean_ctor_set(v___x_3283_, 1, v_param_3271_);
lean_ctor_set(v___x_3283_, 0, v_decl_3270_);
v___x_3287_ = v___x_3283_;
goto v_reusejp_3286_;
}
else
{
lean_object* v_reuseFailAlloc_3295_; 
v_reuseFailAlloc_3295_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3295_, 0, v_decl_3270_);
lean_ctor_set(v_reuseFailAlloc_3295_, 1, v_param_3271_);
v___x_3287_ = v_reuseFailAlloc_3295_;
goto v_reusejp_3286_;
}
v_reusejp_3286_:
{
lean_object* v___f_3288_; uint8_t v___x_3289_; 
v___f_3288_ = lean_alloc_closure((void*)(l_Lean_registerParametricAttributeForExt___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3288_, 0, v_addEntryFn_3274_);
lean_closure_set(v___f_3288_, 1, v___x_3287_);
v___x_3289_ = 1;
if (v_logWrites_3276_ == 0)
{
lean_object* v___x_3290_; lean_object* v___x_3291_; 
v___x_3290_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_3273_, v_env_3269_, v___f_3288_, v_asyncMode_3275_, v___x_3279_, v___x_3289_);
lean_dec(v_asyncMode_3275_);
v___x_3291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3291_, 0, v___x_3290_);
return v___x_3291_;
}
else
{
lean_object* v___x_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; 
lean_inc_ref(v_toEnvExtension_3273_);
v___x_3292_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_3273_, v_env_3269_);
lean_dec_ref(v_env_3269_);
v___x_3293_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_3273_, v___x_3292_, v___f_3288_, v_asyncMode_3275_, v___x_3279_, v___x_3289_);
lean_dec(v_asyncMode_3275_);
v___x_3294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3294_, 0, v___x_3293_);
return v___x_3294_;
}
}
}
else
{
lean_object* v___x_3297_; uint8_t v_isShared_3298_; uint8_t v_isSharedCheck_3314_; 
lean_del_object(v___x_3283_);
lean_dec(v_asyncMode_3275_);
lean_dec(v_addEntryFn_3274_);
lean_dec_ref(v_toEnvExtension_3273_);
lean_dec(v_param_3271_);
lean_dec_ref(v_env_3269_);
v_isSharedCheck_3314_ = !lean_is_exclusive(v___x_3285_);
if (v_isSharedCheck_3314_ == 0)
{
lean_object* v_unused_3315_; 
v_unused_3315_ = lean_ctor_get(v___x_3285_, 0);
lean_dec(v_unused_3315_);
v___x_3297_ = v___x_3285_;
v_isShared_3298_ = v_isSharedCheck_3314_;
goto v_resetjp_3296_;
}
else
{
lean_dec(v___x_3285_);
v___x_3297_ = lean_box(0);
v_isShared_3298_ = v_isSharedCheck_3314_;
goto v_resetjp_3296_;
}
v_resetjp_3296_:
{
lean_object* v_toAttributeImplCore_3299_; lean_object* v_name_3300_; uint8_t v___x_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; lean_object* v___x_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_3312_; 
v_toAttributeImplCore_3299_ = lean_ctor_get(v_attr_3268_, 0);
lean_inc_ref(v_toAttributeImplCore_3299_);
lean_dec_ref(v_attr_3268_);
v_name_3300_ = lean_ctor_get(v_toAttributeImplCore_3299_, 1);
lean_inc(v_name_3300_);
lean_dec_ref(v_toAttributeImplCore_3299_);
v___x_3301_ = 1;
v___x_3302_ = ((lean_object*)(l_Lean_ParametricAttribute_setParamFromExt___redArg___closed__0));
v___x_3303_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_3300_, v___x_3301_);
v___x_3304_ = lean_string_append(v___x_3302_, v___x_3303_);
lean_dec_ref(v___x_3303_);
v___x_3305_ = ((lean_object*)(l_Lean_ParametricAttribute_setParamFromExt___redArg___closed__1));
v___x_3306_ = lean_string_append(v___x_3304_, v___x_3305_);
v___x_3307_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_decl_3270_, v___x_3301_);
v___x_3308_ = lean_string_append(v___x_3306_, v___x_3307_);
lean_dec_ref(v___x_3307_);
v___x_3309_ = ((lean_object*)(l_Lean_ParametricAttribute_setParamFromExt___redArg___closed__2));
v___x_3310_ = lean_string_append(v___x_3308_, v___x_3309_);
if (v_isShared_3298_ == 0)
{
lean_ctor_set_tag(v___x_3297_, 0);
lean_ctor_set(v___x_3297_, 0, v___x_3310_);
v___x_3312_ = v___x_3297_;
goto v_reusejp_3311_;
}
else
{
lean_object* v_reuseFailAlloc_3313_; 
v_reuseFailAlloc_3313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3313_, 0, v___x_3310_);
v___x_3312_ = v_reuseFailAlloc_3313_;
goto v_reusejp_3311_;
}
v_reusejp_3311_:
{
return v___x_3312_;
}
}
}
}
}
else
{
lean_object* v___x_3319_; uint8_t v_isShared_3320_; uint8_t v_isSharedCheck_3336_; 
lean_dec(v_param_3271_);
lean_dec_ref(v_env_3269_);
lean_dec_ref(v_ext_3267_);
v_isSharedCheck_3336_ = !lean_is_exclusive(v___x_3272_);
if (v_isSharedCheck_3336_ == 0)
{
lean_object* v_unused_3337_; 
v_unused_3337_ = lean_ctor_get(v___x_3272_, 0);
lean_dec(v_unused_3337_);
v___x_3319_ = v___x_3272_;
v_isShared_3320_ = v_isSharedCheck_3336_;
goto v_resetjp_3318_;
}
else
{
lean_dec(v___x_3272_);
v___x_3319_ = lean_box(0);
v_isShared_3320_ = v_isSharedCheck_3336_;
goto v_resetjp_3318_;
}
v_resetjp_3318_:
{
lean_object* v_toAttributeImplCore_3321_; lean_object* v_name_3322_; uint8_t v___x_3323_; lean_object* v___x_3324_; lean_object* v___x_3325_; lean_object* v___x_3326_; lean_object* v___x_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; lean_object* v___x_3334_; 
v_toAttributeImplCore_3321_ = lean_ctor_get(v_attr_3268_, 0);
lean_inc_ref(v_toAttributeImplCore_3321_);
lean_dec_ref(v_attr_3268_);
v_name_3322_ = lean_ctor_get(v_toAttributeImplCore_3321_, 1);
lean_inc(v_name_3322_);
lean_dec_ref(v_toAttributeImplCore_3321_);
v___x_3323_ = 1;
v___x_3324_ = ((lean_object*)(l_Lean_ParametricAttribute_setParamFromExt___redArg___closed__0));
v___x_3325_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_3322_, v___x_3323_);
v___x_3326_ = lean_string_append(v___x_3324_, v___x_3325_);
lean_dec_ref(v___x_3325_);
v___x_3327_ = ((lean_object*)(l_Lean_ParametricAttribute_setParamFromExt___redArg___closed__1));
v___x_3328_ = lean_string_append(v___x_3326_, v___x_3327_);
v___x_3329_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_decl_3270_, v___x_3323_);
v___x_3330_ = lean_string_append(v___x_3328_, v___x_3329_);
lean_dec_ref(v___x_3329_);
v___x_3331_ = ((lean_object*)(l_Lean_ParametricAttribute_setParamFromExt___redArg___closed__3));
v___x_3332_ = lean_string_append(v___x_3330_, v___x_3331_);
if (v_isShared_3320_ == 0)
{
lean_ctor_set_tag(v___x_3319_, 0);
lean_ctor_set(v___x_3319_, 0, v___x_3332_);
v___x_3334_ = v___x_3319_;
goto v_reusejp_3333_;
}
else
{
lean_object* v_reuseFailAlloc_3335_; 
v_reuseFailAlloc_3335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3335_, 0, v___x_3332_);
v___x_3334_ = v_reuseFailAlloc_3335_;
goto v_reusejp_3333_;
}
v_reusejp_3333_:
{
return v___x_3334_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_setParamFromExt(lean_object* v_00_u03b1_3338_, lean_object* v_ext_3339_, lean_object* v_attr_3340_, lean_object* v_env_3341_, lean_object* v_decl_3342_, lean_object* v_param_3343_){
_start:
{
lean_object* v___x_3344_; 
v___x_3344_ = l_Lean_ParametricAttribute_setParamFromExt___redArg(v_ext_3339_, v_attr_3340_, v_env_3341_, v_decl_3342_, v_param_3343_);
return v___x_3344_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_setParam___redArg(lean_object* v_attr_3345_, lean_object* v_env_3346_, lean_object* v_decl_3347_, lean_object* v_param_3348_){
_start:
{
lean_object* v_attr_3349_; lean_object* v_ext_3350_; lean_object* v___x_3351_; 
v_attr_3349_ = lean_ctor_get(v_attr_3345_, 0);
lean_inc_ref(v_attr_3349_);
v_ext_3350_ = lean_ctor_get(v_attr_3345_, 1);
lean_inc_ref(v_ext_3350_);
lean_dec_ref(v_attr_3345_);
v___x_3351_ = l_Lean_ParametricAttribute_setParamFromExt___redArg(v_ext_3350_, v_attr_3349_, v_env_3346_, v_decl_3347_, v_param_3348_);
return v___x_3351_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_setParam(lean_object* v_00_u03b1_3352_, lean_object* v_attr_3353_, lean_object* v_env_3354_, lean_object* v_decl_3355_, lean_object* v_param_3356_){
_start:
{
lean_object* v___x_3357_; 
v___x_3357_ = l_Lean_ParametricAttribute_setParam___redArg(v_attr_3353_, v_env_3354_, v_decl_3355_, v_param_3356_);
return v___x_3357_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___redArg___lam__0(lean_object* v_x_3358_, lean_object* v___y_3359_){
_start:
{
lean_object* v___x_3361_; lean_object* v___x_3362_; 
v___x_3361_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___lam__0___closed__1));
v___x_3362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3362_, 0, v___x_3361_);
return v___x_3362_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___redArg___lam__0___boxed(lean_object* v_x_3363_, lean_object* v___y_3364_, lean_object* v___y_3365_){
_start:
{
lean_object* v_res_3366_; 
v_res_3366_ = l_Lean_instInhabitedEnumAttributes_default___redArg___lam__0(v_x_3363_, v___y_3364_);
lean_dec_ref(v___y_3364_);
lean_dec_ref(v_x_3363_);
return v_res_3366_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___redArg___lam__1(lean_object* v_s_3367_, lean_object* v_x_3368_){
_start:
{
lean_inc(v_s_3367_);
return v_s_3367_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___redArg___lam__1___boxed(lean_object* v_s_3369_, lean_object* v_x_3370_){
_start:
{
lean_object* v_res_3371_; 
v_res_3371_ = l_Lean_instInhabitedEnumAttributes_default___redArg___lam__1(v_s_3369_, v_x_3370_);
lean_dec_ref(v_x_3370_);
lean_dec(v_s_3369_);
return v_res_3371_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___redArg___lam__2(lean_object* v_x_3372_, lean_object* v_x_3373_){
_start:
{
lean_object* v___x_3374_; 
v___x_3374_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___redArg___lam__2___closed__1));
return v___x_3374_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___redArg___lam__2___boxed(lean_object* v_x_3375_, lean_object* v_x_3376_){
_start:
{
lean_object* v_res_3377_; 
v_res_3377_ = l_Lean_instInhabitedEnumAttributes_default___redArg___lam__2(v_x_3375_, v_x_3376_);
lean_dec(v_x_3376_);
lean_dec_ref(v_x_3375_);
return v_res_3377_;
}
}
static lean_object* _init_l_Lean_instInhabitedEnumAttributes_default___redArg___closed__3(void){
_start:
{
lean_object* v___f_3381_; lean_object* v___f_3382_; lean_object* v___f_3383_; lean_object* v___f_3384_; lean_object* v___x_3385_; lean_object* v___x_3386_; lean_object* v___x_3387_; 
v___f_3381_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___closed__3));
v___f_3382_ = ((lean_object*)(l_Lean_instInhabitedEnumAttributes_default___redArg___closed__2));
v___f_3383_ = ((lean_object*)(l_Lean_instInhabitedEnumAttributes_default___redArg___closed__1));
v___f_3384_ = ((lean_object*)(l_Lean_instInhabitedEnumAttributes_default___redArg___closed__0));
v___x_3385_ = lean_box(0);
v___x_3386_ = lean_obj_once(&l_Lean_instInhabitedTagAttribute_default___closed__4, &l_Lean_instInhabitedTagAttribute_default___closed__4_once, _init_l_Lean_instInhabitedTagAttribute_default___closed__4);
v___x_3387_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3387_, 0, v___x_3386_);
lean_ctor_set(v___x_3387_, 1, v___x_3385_);
lean_ctor_set(v___x_3387_, 2, v___f_3384_);
lean_ctor_set(v___x_3387_, 3, v___f_3383_);
lean_ctor_set(v___x_3387_, 4, v___f_3382_);
lean_ctor_set(v___x_3387_, 5, v___f_3381_);
return v___x_3387_;
}
}
static lean_object* _init_l_Lean_instInhabitedEnumAttributes_default___redArg___closed__4(void){
_start:
{
lean_object* v___x_3388_; lean_object* v___x_3389_; lean_object* v___x_3390_; 
v___x_3388_ = lean_obj_once(&l_Lean_instInhabitedEnumAttributes_default___redArg___closed__3, &l_Lean_instInhabitedEnumAttributes_default___redArg___closed__3_once, _init_l_Lean_instInhabitedEnumAttributes_default___redArg___closed__3);
v___x_3389_ = lean_box(0);
v___x_3390_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3390_, 0, v___x_3389_);
lean_ctor_set(v___x_3390_, 1, v___x_3388_);
return v___x_3390_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___redArg(){
_start:
{
lean_object* v___x_3392_; 
v___x_3392_ = lean_obj_once(&l_Lean_instInhabitedEnumAttributes_default___redArg___closed__4, &l_Lean_instInhabitedEnumAttributes_default___redArg___closed__4_once, _init_l_Lean_instInhabitedEnumAttributes_default___redArg___closed__4);
return v___x_3392_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___redArg___boxed(lean_object* v___dummy_3393_){
_start:
{
lean_object* v_res_3394_; 
v_res_3394_ = l_Lean_instInhabitedEnumAttributes_default___redArg();
return v_res_3394_;
}
}
static lean_object* _init_l_Lean_instInhabitedEnumAttributes_default___closed__0(void){
_start:
{
lean_object* v___x_3395_; 
v___x_3395_ = l_Lean_instInhabitedEnumAttributes_default___redArg();
return v___x_3395_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default(lean_object* v_00_u03b1_3396_){
_start:
{
lean_object* v___x_3397_; 
v___x_3397_ = lean_obj_once(&l_Lean_instInhabitedEnumAttributes_default___closed__0, &l_Lean_instInhabitedEnumAttributes_default___closed__0_once, _init_l_Lean_instInhabitedEnumAttributes_default___closed__0);
return v___x_3397_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes___redArg(){
_start:
{
lean_object* v___x_3399_; 
v___x_3399_ = lean_obj_once(&l_Lean_instInhabitedEnumAttributes_default___closed__0, &l_Lean_instInhabitedEnumAttributes_default___closed__0_once, _init_l_Lean_instInhabitedEnumAttributes_default___closed__0);
return v___x_3399_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes___redArg___boxed(lean_object* v___dummy_3400_){
_start:
{
lean_object* v_res_3401_; 
v_res_3401_ = l_Lean_instInhabitedEnumAttributes___redArg();
return v_res_3401_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes(lean_object* v_a_3402_){
_start:
{
lean_object* v___x_3403_; 
v___x_3403_ = lean_obj_once(&l_Lean_instInhabitedEnumAttributes_default___closed__0, &l_Lean_instInhabitedEnumAttributes_default___closed__0_once, _init_l_Lean_instInhabitedEnumAttributes_default___closed__0);
return v___x_3403_;
}
}
static lean_object* _init_l_Lean_registerEnumAttributes___auto__1(void){
_start:
{
lean_object* v___x_3404_; 
v___x_3404_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__28, &l_Lean_AttributeImplCore_ref___autoParam___closed__28_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__28);
return v___x_3404_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__0(lean_object* v_x_3405_){
_start:
{
lean_object* v___x_3406_; 
v___x_3406_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___redArg___lam__2___closed__0));
return v___x_3406_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__0___boxed(lean_object* v_x_3407_){
_start:
{
lean_object* v_res_3408_; 
v_res_3408_ = l_Lean_registerEnumAttributes___redArg___lam__0(v_x_3407_);
lean_dec(v_x_3407_);
return v_res_3408_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___redArg(lean_object* v_newState_3409_, lean_object* v_x_3410_, lean_object* v_x_3411_){
_start:
{
if (lean_obj_tag(v_x_3411_) == 0)
{
return v_x_3410_;
}
else
{
lean_object* v_head_3412_; lean_object* v_tail_3413_; lean_object* v___x_3414_; 
v_head_3412_ = lean_ctor_get(v_x_3411_, 0);
lean_inc(v_head_3412_);
v_tail_3413_ = lean_ctor_get(v_x_3411_, 1);
lean_inc(v_tail_3413_);
lean_dec_ref_known(v_x_3411_, 2);
v___x_3414_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_newState_3409_, v_head_3412_);
if (lean_obj_tag(v___x_3414_) == 1)
{
lean_object* v_val_3415_; lean_object* v___x_3416_; 
v_val_3415_ = lean_ctor_get(v___x_3414_, 0);
lean_inc(v_val_3415_);
lean_dec_ref_known(v___x_3414_, 1);
v___x_3416_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_head_3412_, v_val_3415_, v_x_3410_);
v_x_3410_ = v___x_3416_;
v_x_3411_ = v_tail_3413_;
goto _start;
}
else
{
lean_dec(v___x_3414_);
lean_dec(v_head_3412_);
v_x_3411_ = v_tail_3413_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___redArg___boxed(lean_object* v_newState_3419_, lean_object* v_x_3420_, lean_object* v_x_3421_){
_start:
{
lean_object* v_res_3422_; 
v_res_3422_ = l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___redArg(v_newState_3419_, v_x_3420_, v_x_3421_);
lean_dec(v_newState_3419_);
return v_res_3422_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__1(lean_object* v_x_3423_, lean_object* v_newState_3424_, lean_object* v_consts_3425_, lean_object* v_st_3426_){
_start:
{
lean_object* v___x_3427_; 
v___x_3427_ = l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___redArg(v_newState_3424_, v_st_3426_, v_consts_3425_);
return v___x_3427_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__1___boxed(lean_object* v_x_3428_, lean_object* v_newState_3429_, lean_object* v_consts_3430_, lean_object* v_st_3431_){
_start:
{
lean_object* v_res_3432_; 
v_res_3432_ = l_Lean_registerEnumAttributes___redArg___lam__1(v_x_3428_, v_newState_3429_, v_consts_3430_, v_st_3431_);
lean_dec(v_newState_3429_);
lean_dec(v_x_3428_);
return v_res_3432_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__2(lean_object* v_s_3442_){
_start:
{
lean_object* v___x_3443_; lean_object* v___y_3445_; 
v___x_3443_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___lam__2___closed__3));
if (lean_obj_tag(v_s_3442_) == 0)
{
lean_object* v_size_3449_; 
v_size_3449_ = lean_ctor_get(v_s_3442_, 0);
lean_inc(v_size_3449_);
lean_dec_ref_known(v_s_3442_, 5);
v___y_3445_ = v_size_3449_;
goto v___jp_3444_;
}
else
{
lean_object* v___x_3450_; 
v___x_3450_ = lean_unsigned_to_nat(0u);
v___y_3445_ = v___x_3450_;
goto v___jp_3444_;
}
v___jp_3444_:
{
lean_object* v___x_3446_; lean_object* v___x_3447_; lean_object* v___x_3448_; 
v___x_3446_ = l_Nat_reprFast(v___y_3445_);
v___x_3447_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3447_, 0, v___x_3446_);
v___x_3448_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3448_, 0, v___x_3443_);
lean_ctor_set(v___x_3448_, 1, v___x_3447_);
return v___x_3448_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg(lean_object* v_env_3451_, lean_object* v_as_3452_, size_t v_i_3453_, size_t v_stop_3454_, lean_object* v_b_3455_){
_start:
{
lean_object* v___y_3457_; uint8_t v___x_3461_; 
v___x_3461_ = lean_usize_dec_eq(v_i_3453_, v_stop_3454_);
if (v___x_3461_ == 0)
{
lean_object* v___x_3462_; lean_object* v_fst_3463_; uint8_t v___x_3464_; lean_object* v___x_3465_; uint8_t v___x_3466_; 
v___x_3462_ = lean_array_uget_borrowed(v_as_3452_, v_i_3453_);
v_fst_3463_ = lean_ctor_get(v___x_3462_, 0);
v___x_3464_ = 1;
lean_inc_ref(v_env_3451_);
v___x_3465_ = l_Lean_Environment_setExporting(v_env_3451_, v___x_3464_);
lean_inc(v_fst_3463_);
v___x_3466_ = l_Lean_Environment_contains(v___x_3465_, v_fst_3463_, v___x_3461_);
if (v___x_3466_ == 0)
{
v___y_3457_ = v_b_3455_;
goto v___jp_3456_;
}
else
{
lean_object* v___x_3467_; 
lean_inc(v___x_3462_);
v___x_3467_ = lean_array_push(v_b_3455_, v___x_3462_);
v___y_3457_ = v___x_3467_;
goto v___jp_3456_;
}
}
else
{
lean_dec_ref(v_env_3451_);
return v_b_3455_;
}
v___jp_3456_:
{
size_t v___x_3458_; size_t v___x_3459_; 
v___x_3458_ = ((size_t)1ULL);
v___x_3459_ = lean_usize_add(v_i_3453_, v___x_3458_);
v_i_3453_ = v___x_3459_;
v_b_3455_ = v___y_3457_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg___boxed(lean_object* v_env_3468_, lean_object* v_as_3469_, lean_object* v_i_3470_, lean_object* v_stop_3471_, lean_object* v_b_3472_){
_start:
{
size_t v_i_boxed_3473_; size_t v_stop_boxed_3474_; lean_object* v_res_3475_; 
v_i_boxed_3473_ = lean_unbox_usize(v_i_3470_);
lean_dec(v_i_3470_);
v_stop_boxed_3474_ = lean_unbox_usize(v_stop_3471_);
lean_dec(v_stop_3471_);
v_res_3475_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg(v_env_3468_, v_as_3469_, v_i_boxed_3473_, v_stop_boxed_3474_, v_b_3472_);
lean_dec_ref(v_as_3469_);
return v_res_3475_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__3(lean_object* v_env_3476_, lean_object* v_m_3477_){
_start:
{
lean_object* v___x_3478_; lean_object* v___x_3479_; lean_object* v___y_3481_; lean_object* v___x_3495_; lean_object* v___x_3496_; lean_object* v___y_3498_; lean_object* v___y_3499_; uint8_t v___x_3501_; 
v___x_3478_ = lean_unsigned_to_nat(0u);
v___x_3479_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___redArg___lam__2___closed__0));
v___x_3495_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg(v___x_3479_, v_m_3477_);
v___x_3496_ = lean_array_get_size(v___x_3495_);
v___x_3501_ = lean_nat_dec_eq(v___x_3496_, v___x_3478_);
if (v___x_3501_ == 0)
{
lean_object* v___x_3502_; lean_object* v___x_3503_; lean_object* v___y_3505_; uint8_t v___x_3507_; 
v___x_3502_ = lean_unsigned_to_nat(1u);
v___x_3503_ = lean_nat_sub(v___x_3496_, v___x_3502_);
v___x_3507_ = lean_nat_dec_le(v___x_3478_, v___x_3503_);
if (v___x_3507_ == 0)
{
lean_inc(v___x_3503_);
v___y_3505_ = v___x_3503_;
goto v___jp_3504_;
}
else
{
v___y_3505_ = v___x_3478_;
goto v___jp_3504_;
}
v___jp_3504_:
{
uint8_t v___x_3506_; 
v___x_3506_ = lean_nat_dec_le(v___y_3505_, v___x_3503_);
if (v___x_3506_ == 0)
{
lean_dec(v___x_3503_);
lean_inc(v___y_3505_);
v___y_3498_ = v___y_3505_;
v___y_3499_ = v___y_3505_;
goto v___jp_3497_;
}
else
{
v___y_3498_ = v___y_3505_;
v___y_3499_ = v___x_3503_;
goto v___jp_3497_;
}
}
}
else
{
v___y_3481_ = v___x_3495_;
goto v___jp_3480_;
}
v___jp_3480_:
{
lean_object* v___x_3482_; uint8_t v___x_3483_; 
v___x_3482_ = lean_array_get_size(v___y_3481_);
v___x_3483_ = lean_nat_dec_lt(v___x_3478_, v___x_3482_);
if (v___x_3483_ == 0)
{
lean_object* v___x_3484_; 
lean_dec_ref(v_env_3476_);
v___x_3484_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3484_, 0, v___x_3479_);
lean_ctor_set(v___x_3484_, 1, v___x_3479_);
lean_ctor_set(v___x_3484_, 2, v___y_3481_);
return v___x_3484_;
}
else
{
uint8_t v___x_3485_; 
v___x_3485_ = lean_nat_dec_le(v___x_3482_, v___x_3482_);
if (v___x_3485_ == 0)
{
if (v___x_3483_ == 0)
{
lean_object* v___x_3486_; 
lean_dec_ref(v_env_3476_);
v___x_3486_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3486_, 0, v___x_3479_);
lean_ctor_set(v___x_3486_, 1, v___x_3479_);
lean_ctor_set(v___x_3486_, 2, v___y_3481_);
return v___x_3486_;
}
else
{
size_t v___x_3487_; size_t v___x_3488_; lean_object* v___x_3489_; lean_object* v___x_3490_; 
v___x_3487_ = ((size_t)0ULL);
v___x_3488_ = lean_usize_of_nat(v___x_3482_);
v___x_3489_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg(v_env_3476_, v___y_3481_, v___x_3487_, v___x_3488_, v___x_3479_);
lean_inc_ref(v___x_3489_);
v___x_3490_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3490_, 0, v___x_3489_);
lean_ctor_set(v___x_3490_, 1, v___x_3489_);
lean_ctor_set(v___x_3490_, 2, v___y_3481_);
return v___x_3490_;
}
}
else
{
size_t v___x_3491_; size_t v___x_3492_; lean_object* v___x_3493_; lean_object* v___x_3494_; 
v___x_3491_ = ((size_t)0ULL);
v___x_3492_ = lean_usize_of_nat(v___x_3482_);
v___x_3493_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg(v_env_3476_, v___y_3481_, v___x_3491_, v___x_3492_, v___x_3479_);
lean_inc_ref(v___x_3493_);
v___x_3494_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3494_, 0, v___x_3493_);
lean_ctor_set(v___x_3494_, 1, v___x_3493_);
lean_ctor_set(v___x_3494_, 2, v___y_3481_);
return v___x_3494_;
}
}
}
v___jp_3497_:
{
lean_object* v___x_3500_; 
v___x_3500_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg(v___x_3496_, v___x_3495_, v___y_3498_, v___y_3499_);
lean_dec(v___y_3499_);
v___y_3481_ = v___x_3500_;
goto v___jp_3480_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__3___boxed(lean_object* v_env_3508_, lean_object* v_m_3509_){
_start:
{
lean_object* v_res_3510_; 
v_res_3510_ = l_Lean_registerEnumAttributes___redArg___lam__3(v_env_3508_, v_m_3509_);
lean_dec(v_m_3509_);
return v_res_3510_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__4(lean_object* v_s_3511_, lean_object* v_p_3512_){
_start:
{
lean_object* v_fst_3513_; lean_object* v_snd_3514_; lean_object* v___x_3515_; 
v_fst_3513_ = lean_ctor_get(v_p_3512_, 0);
lean_inc(v_fst_3513_);
v_snd_3514_ = lean_ctor_get(v_p_3512_, 1);
lean_inc(v_snd_3514_);
lean_dec_ref(v_p_3512_);
v___x_3515_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_3513_, v_snd_3514_, v_s_3511_);
return v___x_3515_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__6(lean_object* v___x_3516_, lean_object* v_x_3517_, lean_object* v_x_3518_){
_start:
{
lean_object* v___x_3520_; 
v___x_3520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3520_, 0, v___x_3516_);
return v___x_3520_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__6___boxed(lean_object* v___x_3521_, lean_object* v_x_3522_, lean_object* v_x_3523_, lean_object* v___y_3524_){
_start:
{
lean_object* v_res_3525_; 
v_res_3525_ = l_Lean_registerEnumAttributes___redArg___lam__6(v___x_3521_, v_x_3522_, v_x_3523_);
lean_dec_ref(v_x_3523_);
lean_dec_ref(v_x_3522_);
return v_res_3525_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_registerEnumAttributes_spec__3(lean_object* v_as_3526_){
_start:
{
if (lean_obj_tag(v_as_3526_) == 0)
{
lean_object* v___x_3528_; lean_object* v___x_3529_; 
v___x_3528_ = lean_box(0);
v___x_3529_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3529_, 0, v___x_3528_);
return v___x_3529_;
}
else
{
lean_object* v_head_3530_; lean_object* v_tail_3531_; lean_object* v___x_3532_; 
v_head_3530_ = lean_ctor_get(v_as_3526_, 0);
lean_inc(v_head_3530_);
v_tail_3531_ = lean_ctor_get(v_as_3526_, 1);
lean_inc(v_tail_3531_);
lean_dec_ref_known(v_as_3526_, 2);
v___x_3532_ = l_Lean_registerBuiltinAttribute(v_head_3530_);
if (lean_obj_tag(v___x_3532_) == 0)
{
lean_dec_ref_known(v___x_3532_, 1);
v_as_3526_ = v_tail_3531_;
goto _start;
}
else
{
lean_dec(v_tail_3531_);
return v___x_3532_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_registerEnumAttributes_spec__3___boxed(lean_object* v_as_3534_, lean_object* v___y_3535_){
_start:
{
lean_object* v_res_3536_; 
v_res_3536_ = l_List_forM___at___00Lean_registerEnumAttributes_spec__3(v_as_3534_);
return v_res_3536_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__1(lean_object* v_addEntryFn_3537_, lean_object* v___x_3538_, lean_object* v_s_3539_){
_start:
{
lean_object* v_importedEntries_3540_; lean_object* v_state_3541_; lean_object* v___x_3543_; uint8_t v_isShared_3544_; uint8_t v_isSharedCheck_3549_; 
v_importedEntries_3540_ = lean_ctor_get(v_s_3539_, 0);
v_state_3541_ = lean_ctor_get(v_s_3539_, 1);
v_isSharedCheck_3549_ = !lean_is_exclusive(v_s_3539_);
if (v_isSharedCheck_3549_ == 0)
{
v___x_3543_ = v_s_3539_;
v_isShared_3544_ = v_isSharedCheck_3549_;
goto v_resetjp_3542_;
}
else
{
lean_inc(v_state_3541_);
lean_inc(v_importedEntries_3540_);
lean_dec(v_s_3539_);
v___x_3543_ = lean_box(0);
v_isShared_3544_ = v_isSharedCheck_3549_;
goto v_resetjp_3542_;
}
v_resetjp_3542_:
{
lean_object* v_state_3545_; lean_object* v___x_3547_; 
v_state_3545_ = lean_apply_2(v_addEntryFn_3537_, v_state_3541_, v___x_3538_);
if (v_isShared_3544_ == 0)
{
lean_ctor_set(v___x_3543_, 1, v_state_3545_);
v___x_3547_ = v___x_3543_;
goto v_reusejp_3546_;
}
else
{
lean_object* v_reuseFailAlloc_3548_; 
v_reuseFailAlloc_3548_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3548_, 0, v_importedEntries_3540_);
lean_ctor_set(v_reuseFailAlloc_3548_, 1, v_state_3545_);
v___x_3547_ = v_reuseFailAlloc_3548_;
goto v_reusejp_3546_;
}
v_reusejp_3546_:
{
return v___x_3547_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__2(lean_object* v_validate_3550_, lean_object* v_snd_3551_, lean_object* v_a_3552_, lean_object* v_fst_3553_, lean_object* v_decl_3554_, lean_object* v_stx_3555_, uint8_t v_kind_3556_, lean_object* v___y_3557_, lean_object* v___y_3558_){
_start:
{
lean_object* v___y_3561_; lean_object* v___y_3562_; lean_object* v_nextMacroScope_3563_; lean_object* v_ngen_3564_; lean_object* v_auxDeclNGen_3565_; lean_object* v_traceState_3566_; lean_object* v_recordedDeps_3567_; lean_object* v_messages_3568_; lean_object* v_infoState_3569_; lean_object* v_snapshotTasks_3570_; lean_object* v___y_3571_; lean_object* v___y_3577_; lean_object* v___y_3578_; lean_object* v___x_3606_; 
v___x_3606_ = l_Lean_Attribute_Builtin_ensureNoArgs(v_stx_3555_, v___y_3557_, v___y_3558_);
if (lean_obj_tag(v___x_3606_) == 0)
{
uint8_t v___x_3607_; uint8_t v___x_3608_; 
lean_dec_ref_known(v___x_3606_, 1);
v___x_3607_ = 0;
v___x_3608_ = l_Lean_instBEqAttributeKind_beq(v_kind_3556_, v___x_3607_);
if (v___x_3608_ == 0)
{
lean_object* v___x_3609_; 
lean_dec(v_decl_3554_);
lean_dec_ref(v_a_3552_);
lean_dec(v_snd_3551_);
lean_dec_ref(v_validate_3550_);
v___x_3609_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg(v_fst_3553_, v_kind_3556_, v___y_3557_, v___y_3558_);
return v___x_3609_;
}
else
{
goto v___jp_3601_;
}
}
else
{
lean_dec(v_decl_3554_);
lean_dec(v_fst_3553_);
lean_dec_ref(v_a_3552_);
lean_dec(v_snd_3551_);
lean_dec_ref(v_validate_3550_);
return v___x_3606_;
}
v___jp_3560_:
{
lean_object* v___x_3572_; lean_object* v___x_3573_; lean_object* v___x_3574_; lean_object* v___x_3575_; 
v___x_3572_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1);
v___x_3573_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_3573_, 0, v___y_3571_);
lean_ctor_set(v___x_3573_, 1, v_nextMacroScope_3563_);
lean_ctor_set(v___x_3573_, 2, v_ngen_3564_);
lean_ctor_set(v___x_3573_, 3, v_auxDeclNGen_3565_);
lean_ctor_set(v___x_3573_, 4, v_traceState_3566_);
lean_ctor_set(v___x_3573_, 5, v___x_3572_);
lean_ctor_set(v___x_3573_, 6, v_recordedDeps_3567_);
lean_ctor_set(v___x_3573_, 7, v_messages_3568_);
lean_ctor_set(v___x_3573_, 8, v_infoState_3569_);
lean_ctor_set(v___x_3573_, 9, v_snapshotTasks_3570_);
v___x_3574_ = lean_st_ref_put(v___y_3561_, v___x_3573_);
v___x_3575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3575_, 0, v___y_3562_);
return v___x_3575_;
}
v___jp_3576_:
{
lean_object* v___x_3579_; 
lean_inc(v___y_3578_);
lean_inc_ref(v___y_3577_);
lean_inc(v_snd_3551_);
lean_inc(v_decl_3554_);
v___x_3579_ = lean_apply_5(v_validate_3550_, v_decl_3554_, v_snd_3551_, v___y_3577_, v___y_3578_, lean_box(0));
if (lean_obj_tag(v___x_3579_) == 0)
{
lean_object* v___x_3580_; lean_object* v_toEnvExtension_3581_; lean_object* v_env_3582_; lean_object* v_nextMacroScope_3583_; lean_object* v_ngen_3584_; lean_object* v_auxDeclNGen_3585_; lean_object* v_traceState_3586_; lean_object* v_recordedDeps_3587_; lean_object* v_messages_3588_; lean_object* v_infoState_3589_; lean_object* v_snapshotTasks_3590_; lean_object* v_addEntryFn_3591_; lean_object* v_asyncMode_3592_; uint8_t v_logWrites_3593_; lean_object* v___x_3594_; lean_object* v___x_3595_; lean_object* v___f_3596_; uint8_t v___x_3597_; 
lean_dec_ref_known(v___x_3579_, 1);
v___x_3580_ = lean_st_ref_take(v___y_3578_);
v_toEnvExtension_3581_ = lean_ctor_get(v_a_3552_, 0);
lean_inc_ref(v_toEnvExtension_3581_);
v_env_3582_ = lean_ctor_get(v___x_3580_, 0);
lean_inc_ref(v_env_3582_);
v_nextMacroScope_3583_ = lean_ctor_get(v___x_3580_, 1);
lean_inc(v_nextMacroScope_3583_);
v_ngen_3584_ = lean_ctor_get(v___x_3580_, 2);
lean_inc_ref(v_ngen_3584_);
v_auxDeclNGen_3585_ = lean_ctor_get(v___x_3580_, 3);
lean_inc_ref(v_auxDeclNGen_3585_);
v_traceState_3586_ = lean_ctor_get(v___x_3580_, 4);
lean_inc_ref(v_traceState_3586_);
v_recordedDeps_3587_ = lean_ctor_get(v___x_3580_, 6);
lean_inc_ref(v_recordedDeps_3587_);
v_messages_3588_ = lean_ctor_get(v___x_3580_, 7);
lean_inc_ref(v_messages_3588_);
v_infoState_3589_ = lean_ctor_get(v___x_3580_, 8);
lean_inc_ref(v_infoState_3589_);
v_snapshotTasks_3590_ = lean_ctor_get(v___x_3580_, 9);
lean_inc_ref(v_snapshotTasks_3590_);
lean_dec(v___x_3580_);
v_addEntryFn_3591_ = lean_ctor_get(v_a_3552_, 3);
lean_inc(v_addEntryFn_3591_);
lean_dec_ref(v_a_3552_);
v_asyncMode_3592_ = lean_ctor_get(v_toEnvExtension_3581_, 2);
lean_inc(v_asyncMode_3592_);
v_logWrites_3593_ = lean_ctor_get_uint8(v_toEnvExtension_3581_, sizeof(void*)*6);
v___x_3594_ = lean_box(0);
lean_inc(v_decl_3554_);
v___x_3595_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3595_, 0, v_decl_3554_);
lean_ctor_set(v___x_3595_, 1, v_snd_3551_);
v___f_3596_ = lean_alloc_closure((void*)(l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__1), 3, 2);
lean_closure_set(v___f_3596_, 0, v_addEntryFn_3591_);
lean_closure_set(v___f_3596_, 1, v___x_3595_);
v___x_3597_ = 1;
if (v_logWrites_3593_ == 0)
{
lean_object* v___x_3598_; 
v___x_3598_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_3581_, v_env_3582_, v___f_3596_, v_asyncMode_3592_, v_decl_3554_, v___x_3597_);
lean_dec(v_asyncMode_3592_);
v___y_3561_ = v___y_3578_;
v___y_3562_ = v___x_3594_;
v_nextMacroScope_3563_ = v_nextMacroScope_3583_;
v_ngen_3564_ = v_ngen_3584_;
v_auxDeclNGen_3565_ = v_auxDeclNGen_3585_;
v_traceState_3566_ = v_traceState_3586_;
v_recordedDeps_3567_ = v_recordedDeps_3587_;
v_messages_3568_ = v_messages_3588_;
v_infoState_3569_ = v_infoState_3589_;
v_snapshotTasks_3570_ = v_snapshotTasks_3590_;
v___y_3571_ = v___x_3598_;
goto v___jp_3560_;
}
else
{
lean_object* v___x_3599_; lean_object* v___x_3600_; 
lean_inc_ref(v_toEnvExtension_3581_);
v___x_3599_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_3581_, v_env_3582_);
lean_dec_ref(v_env_3582_);
v___x_3600_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_3581_, v___x_3599_, v___f_3596_, v_asyncMode_3592_, v_decl_3554_, v___x_3597_);
lean_dec(v_asyncMode_3592_);
v___y_3561_ = v___y_3578_;
v___y_3562_ = v___x_3594_;
v_nextMacroScope_3563_ = v_nextMacroScope_3583_;
v_ngen_3564_ = v_ngen_3584_;
v_auxDeclNGen_3565_ = v_auxDeclNGen_3585_;
v_traceState_3566_ = v_traceState_3586_;
v_recordedDeps_3567_ = v_recordedDeps_3587_;
v_messages_3568_ = v_messages_3588_;
v_infoState_3569_ = v_infoState_3589_;
v_snapshotTasks_3570_ = v_snapshotTasks_3590_;
v___y_3571_ = v___x_3600_;
goto v___jp_3560_;
}
}
else
{
lean_dec(v_decl_3554_);
lean_dec_ref(v_a_3552_);
lean_dec(v_snd_3551_);
return v___x_3579_;
}
}
v___jp_3601_:
{
lean_object* v___x_3602_; lean_object* v_env_3603_; lean_object* v___x_3604_; 
v___x_3602_ = lean_st_ref_get(v___y_3558_);
v_env_3603_ = lean_ctor_get(v___x_3602_, 0);
lean_inc_ref(v_env_3603_);
lean_dec(v___x_3602_);
v___x_3604_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3603_, v_decl_3554_);
lean_dec_ref(v_env_3603_);
if (lean_obj_tag(v___x_3604_) == 0)
{
lean_dec(v_fst_3553_);
v___y_3577_ = v___y_3557_;
v___y_3578_ = v___y_3558_;
goto v___jp_3576_;
}
else
{
lean_object* v___x_3605_; 
lean_dec_ref_known(v___x_3604_, 1);
lean_dec_ref(v_a_3552_);
lean_dec(v_snd_3551_);
lean_dec_ref(v_validate_3550_);
v___x_3605_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg(v_fst_3553_, v_decl_3554_, v___y_3557_, v___y_3558_);
return v___x_3605_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__2___boxed(lean_object* v_validate_3610_, lean_object* v_snd_3611_, lean_object* v_a_3612_, lean_object* v_fst_3613_, lean_object* v_decl_3614_, lean_object* v_stx_3615_, lean_object* v_kind_3616_, lean_object* v___y_3617_, lean_object* v___y_3618_, lean_object* v___y_3619_){
_start:
{
uint8_t v_kind_boxed_3620_; lean_object* v_res_3621_; 
v_kind_boxed_3620_ = lean_unbox(v_kind_3616_);
v_res_3621_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__2(v_validate_3610_, v_snd_3611_, v_a_3612_, v_fst_3613_, v_decl_3614_, v_stx_3615_, v_kind_boxed_3620_, v___y_3617_, v___y_3618_);
lean_dec(v___y_3618_);
lean_dec_ref(v___y_3617_);
return v_res_3621_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__0(lean_object* v_fst_3622_, lean_object* v_decl_3623_, lean_object* v___y_3624_, lean_object* v___y_3625_){
_start:
{
lean_object* v___x_3627_; lean_object* v___x_3628_; lean_object* v___x_3629_; lean_object* v___x_3630_; lean_object* v___x_3631_; lean_object* v___x_3632_; 
v___x_3627_ = lean_obj_once(&l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1, &l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1_once, _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1);
v___x_3628_ = l_Lean_MessageData_ofName(v_fst_3622_);
v___x_3629_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3629_, 0, v___x_3627_);
lean_ctor_set(v___x_3629_, 1, v___x_3628_);
v___x_3630_ = lean_obj_once(&l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3, &l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3_once, _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3);
v___x_3631_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3631_, 0, v___x_3629_);
lean_ctor_set(v___x_3631_, 1, v___x_3630_);
v___x_3632_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_3631_, v___y_3624_, v___y_3625_);
return v___x_3632_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__0___boxed(lean_object* v_fst_3633_, lean_object* v_decl_3634_, lean_object* v___y_3635_, lean_object* v___y_3636_, lean_object* v___y_3637_){
_start:
{
lean_object* v_res_3638_; 
v_res_3638_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__0(v_fst_3633_, v_decl_3634_, v___y_3635_, v___y_3636_);
lean_dec(v___y_3636_);
lean_dec_ref(v___y_3635_);
lean_dec(v_decl_3634_);
return v_res_3638_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg(lean_object* v_validate_3639_, lean_object* v_a_3640_, lean_object* v_ref_3641_, uint8_t v_applicationTime_3642_, lean_object* v_a_3643_, lean_object* v_a_3644_){
_start:
{
if (lean_obj_tag(v_a_3643_) == 0)
{
lean_object* v___x_3645_; 
lean_dec(v_ref_3641_);
lean_dec_ref(v_a_3640_);
lean_dec_ref(v_validate_3639_);
v___x_3645_ = l_List_reverse___redArg(v_a_3644_);
return v___x_3645_;
}
else
{
lean_object* v_head_3646_; lean_object* v_snd_3647_; lean_object* v_tail_3648_; lean_object* v___x_3650_; uint8_t v_isShared_3651_; uint8_t v_isSharedCheck_3663_; 
v_head_3646_ = lean_ctor_get(v_a_3643_, 0);
lean_inc(v_head_3646_);
v_snd_3647_ = lean_ctor_get(v_head_3646_, 1);
lean_inc(v_snd_3647_);
v_tail_3648_ = lean_ctor_get(v_a_3643_, 1);
v_isSharedCheck_3663_ = !lean_is_exclusive(v_a_3643_);
if (v_isSharedCheck_3663_ == 0)
{
lean_object* v_unused_3664_; 
v_unused_3664_ = lean_ctor_get(v_a_3643_, 0);
lean_dec(v_unused_3664_);
v___x_3650_ = v_a_3643_;
v_isShared_3651_ = v_isSharedCheck_3663_;
goto v_resetjp_3649_;
}
else
{
lean_inc(v_tail_3648_);
lean_dec(v_a_3643_);
v___x_3650_ = lean_box(0);
v_isShared_3651_ = v_isSharedCheck_3663_;
goto v_resetjp_3649_;
}
v_resetjp_3649_:
{
lean_object* v_fst_3652_; lean_object* v_fst_3653_; lean_object* v_snd_3654_; lean_object* v___f_3655_; lean_object* v___f_3656_; lean_object* v___x_3657_; lean_object* v___x_3658_; lean_object* v___x_3660_; 
v_fst_3652_ = lean_ctor_get(v_head_3646_, 0);
lean_inc_n(v_fst_3652_, 3);
lean_dec(v_head_3646_);
v_fst_3653_ = lean_ctor_get(v_snd_3647_, 0);
lean_inc(v_fst_3653_);
v_snd_3654_ = lean_ctor_get(v_snd_3647_, 1);
lean_inc(v_snd_3654_);
lean_dec(v_snd_3647_);
v___f_3655_ = lean_alloc_closure((void*)(l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__0___boxed), 5, 1);
lean_closure_set(v___f_3655_, 0, v_fst_3652_);
lean_inc_ref(v_a_3640_);
lean_inc_ref(v_validate_3639_);
v___f_3656_ = lean_alloc_closure((void*)(l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__2___boxed), 10, 4);
lean_closure_set(v___f_3656_, 0, v_validate_3639_);
lean_closure_set(v___f_3656_, 1, v_snd_3654_);
lean_closure_set(v___f_3656_, 2, v_a_3640_);
lean_closure_set(v___f_3656_, 3, v_fst_3652_);
lean_inc(v_ref_3641_);
v___x_3657_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_3657_, 0, v_ref_3641_);
lean_ctor_set(v___x_3657_, 1, v_fst_3652_);
lean_ctor_set(v___x_3657_, 2, v_fst_3653_);
lean_ctor_set_uint8(v___x_3657_, sizeof(void*)*3, v_applicationTime_3642_);
v___x_3658_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3658_, 0, v___x_3657_);
lean_ctor_set(v___x_3658_, 1, v___f_3656_);
lean_ctor_set(v___x_3658_, 2, v___f_3655_);
if (v_isShared_3651_ == 0)
{
lean_ctor_set(v___x_3650_, 1, v_a_3644_);
lean_ctor_set(v___x_3650_, 0, v___x_3658_);
v___x_3660_ = v___x_3650_;
goto v_reusejp_3659_;
}
else
{
lean_object* v_reuseFailAlloc_3662_; 
v_reuseFailAlloc_3662_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3662_, 0, v___x_3658_);
lean_ctor_set(v_reuseFailAlloc_3662_, 1, v_a_3644_);
v___x_3660_ = v_reuseFailAlloc_3662_;
goto v_reusejp_3659_;
}
v_reusejp_3659_:
{
v_a_3643_ = v_tail_3648_;
v_a_3644_ = v___x_3660_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___boxed(lean_object* v_validate_3665_, lean_object* v_a_3666_, lean_object* v_ref_3667_, lean_object* v_applicationTime_3668_, lean_object* v_a_3669_, lean_object* v_a_3670_){
_start:
{
uint8_t v_applicationTime_boxed_3671_; lean_object* v_res_3672_; 
v_applicationTime_boxed_3671_ = lean_unbox(v_applicationTime_3668_);
v_res_3672_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg(v_validate_3665_, v_a_3666_, v_ref_3667_, v_applicationTime_boxed_3671_, v_a_3669_, v_a_3670_);
return v_res_3672_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg(lean_object* v_attrDescrs_3686_, lean_object* v_validate_3687_, uint8_t v_applicationTime_3688_, lean_object* v_ref_3689_){
_start:
{
lean_object* v___f_3691_; lean_object* v___f_3692_; lean_object* v___f_3693_; lean_object* v___f_3694_; lean_object* v___f_3695_; lean_object* v___f_3696_; lean_object* v___x_3697_; lean_object* v___x_3698_; uint8_t v___x_3699_; lean_object* v___x_3700_; lean_object* v___x_3701_; lean_object* v___x_3702_; 
v___f_3691_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__0));
v___f_3692_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__2));
v___f_3693_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__3));
v___f_3694_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__4));
v___f_3695_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__5));
v___f_3696_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__6));
v___x_3697_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__7));
v___x_3698_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__8));
v___x_3699_ = 0;
lean_inc(v_ref_3689_);
v___x_3700_ = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(v___x_3700_, 0, v_ref_3689_);
lean_ctor_set(v___x_3700_, 1, v___f_3695_);
lean_ctor_set(v___x_3700_, 2, v___f_3696_);
lean_ctor_set(v___x_3700_, 3, v___f_3694_);
lean_ctor_set(v___x_3700_, 4, v___f_3693_);
lean_ctor_set(v___x_3700_, 5, v___f_3692_);
lean_ctor_set(v___x_3700_, 6, v___x_3697_);
lean_ctor_set(v___x_3700_, 7, v___x_3698_);
lean_ctor_set_uint8(v___x_3700_, sizeof(void*)*8, v___x_3699_);
lean_ctor_set_uint8(v___x_3700_, sizeof(void*)*8 + 1, v___x_3699_);
v___x_3701_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3701_, 0, v___x_3700_);
lean_ctor_set(v___x_3701_, 1, v___f_3691_);
v___x_3702_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_3701_);
if (lean_obj_tag(v___x_3702_) == 0)
{
lean_object* v_a_3703_; lean_object* v___x_3704_; lean_object* v___x_3705_; lean_object* v___x_3706_; 
v_a_3703_ = lean_ctor_get(v___x_3702_, 0);
lean_inc_n(v_a_3703_, 2);
lean_dec_ref_known(v___x_3702_, 1);
v___x_3704_ = lean_box(0);
v___x_3705_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg(v_validate_3687_, v_a_3703_, v_ref_3689_, v_applicationTime_3688_, v_attrDescrs_3686_, v___x_3704_);
lean_inc(v___x_3705_);
v___x_3706_ = l_List_forM___at___00Lean_registerEnumAttributes_spec__3(v___x_3705_);
if (lean_obj_tag(v___x_3706_) == 0)
{
lean_object* v___x_3708_; uint8_t v_isShared_3709_; uint8_t v_isSharedCheck_3714_; 
v_isSharedCheck_3714_ = !lean_is_exclusive(v___x_3706_);
if (v_isSharedCheck_3714_ == 0)
{
lean_object* v_unused_3715_; 
v_unused_3715_ = lean_ctor_get(v___x_3706_, 0);
lean_dec(v_unused_3715_);
v___x_3708_ = v___x_3706_;
v_isShared_3709_ = v_isSharedCheck_3714_;
goto v_resetjp_3707_;
}
else
{
lean_dec(v___x_3706_);
v___x_3708_ = lean_box(0);
v_isShared_3709_ = v_isSharedCheck_3714_;
goto v_resetjp_3707_;
}
v_resetjp_3707_:
{
lean_object* v___x_3710_; lean_object* v___x_3712_; 
v___x_3710_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3710_, 0, v___x_3705_);
lean_ctor_set(v___x_3710_, 1, v_a_3703_);
if (v_isShared_3709_ == 0)
{
lean_ctor_set(v___x_3708_, 0, v___x_3710_);
v___x_3712_ = v___x_3708_;
goto v_reusejp_3711_;
}
else
{
lean_object* v_reuseFailAlloc_3713_; 
v_reuseFailAlloc_3713_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3713_, 0, v___x_3710_);
v___x_3712_ = v_reuseFailAlloc_3713_;
goto v_reusejp_3711_;
}
v_reusejp_3711_:
{
return v___x_3712_;
}
}
}
else
{
lean_object* v_a_3716_; lean_object* v___x_3718_; uint8_t v_isShared_3719_; uint8_t v_isSharedCheck_3723_; 
lean_dec(v___x_3705_);
lean_dec(v_a_3703_);
v_a_3716_ = lean_ctor_get(v___x_3706_, 0);
v_isSharedCheck_3723_ = !lean_is_exclusive(v___x_3706_);
if (v_isSharedCheck_3723_ == 0)
{
v___x_3718_ = v___x_3706_;
v_isShared_3719_ = v_isSharedCheck_3723_;
goto v_resetjp_3717_;
}
else
{
lean_inc(v_a_3716_);
lean_dec(v___x_3706_);
v___x_3718_ = lean_box(0);
v_isShared_3719_ = v_isSharedCheck_3723_;
goto v_resetjp_3717_;
}
v_resetjp_3717_:
{
lean_object* v___x_3721_; 
if (v_isShared_3719_ == 0)
{
v___x_3721_ = v___x_3718_;
goto v_reusejp_3720_;
}
else
{
lean_object* v_reuseFailAlloc_3722_; 
v_reuseFailAlloc_3722_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3722_, 0, v_a_3716_);
v___x_3721_ = v_reuseFailAlloc_3722_;
goto v_reusejp_3720_;
}
v_reusejp_3720_:
{
return v___x_3721_;
}
}
}
}
else
{
lean_object* v_a_3724_; lean_object* v___x_3726_; uint8_t v_isShared_3727_; uint8_t v_isSharedCheck_3731_; 
lean_dec(v_ref_3689_);
lean_dec_ref(v_validate_3687_);
lean_dec(v_attrDescrs_3686_);
v_a_3724_ = lean_ctor_get(v___x_3702_, 0);
v_isSharedCheck_3731_ = !lean_is_exclusive(v___x_3702_);
if (v_isSharedCheck_3731_ == 0)
{
v___x_3726_ = v___x_3702_;
v_isShared_3727_ = v_isSharedCheck_3731_;
goto v_resetjp_3725_;
}
else
{
lean_inc(v_a_3724_);
lean_dec(v___x_3702_);
v___x_3726_ = lean_box(0);
v_isShared_3727_ = v_isSharedCheck_3731_;
goto v_resetjp_3725_;
}
v_resetjp_3725_:
{
lean_object* v___x_3729_; 
if (v_isShared_3727_ == 0)
{
v___x_3729_ = v___x_3726_;
goto v_reusejp_3728_;
}
else
{
lean_object* v_reuseFailAlloc_3730_; 
v_reuseFailAlloc_3730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3730_, 0, v_a_3724_);
v___x_3729_ = v_reuseFailAlloc_3730_;
goto v_reusejp_3728_;
}
v_reusejp_3728_:
{
return v___x_3729_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___boxed(lean_object* v_attrDescrs_3732_, lean_object* v_validate_3733_, lean_object* v_applicationTime_3734_, lean_object* v_ref_3735_, lean_object* v_a_3736_){
_start:
{
uint8_t v_applicationTime_boxed_3737_; lean_object* v_res_3738_; 
v_applicationTime_boxed_3737_ = lean_unbox(v_applicationTime_3734_);
v_res_3738_ = l_Lean_registerEnumAttributes___redArg(v_attrDescrs_3732_, v_validate_3733_, v_applicationTime_boxed_3737_, v_ref_3735_);
return v_res_3738_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes(lean_object* v_00_u03b1_3739_, lean_object* v_attrDescrs_3740_, lean_object* v_validate_3741_, uint8_t v_applicationTime_3742_, lean_object* v_ref_3743_){
_start:
{
lean_object* v___x_3745_; 
v___x_3745_ = l_Lean_registerEnumAttributes___redArg(v_attrDescrs_3740_, v_validate_3741_, v_applicationTime_3742_, v_ref_3743_);
return v___x_3745_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___boxed(lean_object* v_00_u03b1_3746_, lean_object* v_attrDescrs_3747_, lean_object* v_validate_3748_, lean_object* v_applicationTime_3749_, lean_object* v_ref_3750_, lean_object* v_a_3751_){
_start:
{
uint8_t v_applicationTime_boxed_3752_; lean_object* v_res_3753_; 
v_applicationTime_boxed_3752_ = lean_unbox(v_applicationTime_3749_);
v_res_3753_ = l_Lean_registerEnumAttributes(v_00_u03b1_3746_, v_attrDescrs_3747_, v_validate_3748_, v_applicationTime_boxed_3752_, v_ref_3750_);
return v_res_3753_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0(lean_object* v_00_u03b1_3754_, lean_object* v_env_3755_, lean_object* v_as_3756_, size_t v_i_3757_, size_t v_stop_3758_, lean_object* v_b_3759_){
_start:
{
lean_object* v___x_3760_; 
v___x_3760_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg(v_env_3755_, v_as_3756_, v_i_3757_, v_stop_3758_, v_b_3759_);
return v___x_3760_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___boxed(lean_object* v_00_u03b1_3761_, lean_object* v_env_3762_, lean_object* v_as_3763_, lean_object* v_i_3764_, lean_object* v_stop_3765_, lean_object* v_b_3766_){
_start:
{
size_t v_i_boxed_3767_; size_t v_stop_boxed_3768_; lean_object* v_res_3769_; 
v_i_boxed_3767_ = lean_unbox_usize(v_i_3764_);
lean_dec(v_i_3764_);
v_stop_boxed_3768_ = lean_unbox_usize(v_stop_3765_);
lean_dec(v_stop_3765_);
v_res_3769_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0(v_00_u03b1_3761_, v_env_3762_, v_as_3763_, v_i_boxed_3767_, v_stop_boxed_3768_, v_b_3766_);
lean_dec_ref(v_as_3763_);
return v_res_3769_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerEnumAttributes_spec__1(lean_object* v_00_u03b1_3770_, lean_object* v_newState_3771_, lean_object* v_x_3772_, lean_object* v_x_3773_){
_start:
{
lean_object* v___x_3774_; 
v___x_3774_ = l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___redArg(v_newState_3771_, v_x_3772_, v_x_3773_);
return v___x_3774_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___boxed(lean_object* v_00_u03b1_3775_, lean_object* v_newState_3776_, lean_object* v_x_3777_, lean_object* v_x_3778_){
_start:
{
lean_object* v_res_3779_; 
v_res_3779_ = l_List_foldl___at___00Lean_registerEnumAttributes_spec__1(v_00_u03b1_3775_, v_newState_3776_, v_x_3777_, v_x_3778_);
lean_dec(v_newState_3776_);
return v_res_3779_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2(lean_object* v_00_u03b1_3780_, lean_object* v_validate_3781_, lean_object* v_a_3782_, lean_object* v_ref_3783_, uint8_t v_applicationTime_3784_, lean_object* v_a_3785_, lean_object* v_a_3786_){
_start:
{
lean_object* v___x_3787_; 
v___x_3787_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg(v_validate_3781_, v_a_3782_, v_ref_3783_, v_applicationTime_3784_, v_a_3785_, v_a_3786_);
return v___x_3787_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___boxed(lean_object* v_00_u03b1_3788_, lean_object* v_validate_3789_, lean_object* v_a_3790_, lean_object* v_ref_3791_, lean_object* v_applicationTime_3792_, lean_object* v_a_3793_, lean_object* v_a_3794_){
_start:
{
uint8_t v_applicationTime_boxed_3795_; lean_object* v_res_3796_; 
v_applicationTime_boxed_3795_ = lean_unbox(v_applicationTime_3792_);
v_res_3796_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2(v_00_u03b1_3788_, v_validate_3789_, v_a_3790_, v_ref_3791_, v_applicationTime_boxed_3795_, v_a_3793_, v_a_3794_);
return v_res_3796_;
}
}
LEAN_EXPORT lean_object* l_Lean_EnumAttributes_getValue___redArg(lean_object* v_inst_3797_, lean_object* v_attr_3798_, lean_object* v_env_3799_, lean_object* v_decl_3800_){
_start:
{
lean_object* v___x_3801_; lean_object* v___x_3802_; 
v___x_3801_ = lean_box(1);
v___x_3802_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3799_, v_decl_3800_);
if (lean_obj_tag(v___x_3802_) == 0)
{
lean_object* v_ext_3803_; lean_object* v_toEnvExtension_3804_; lean_object* v_asyncMode_3805_; uint8_t v___x_3806_; lean_object* v___x_3807_; lean_object* v___x_3808_; 
lean_dec(v_inst_3797_);
v_ext_3803_ = lean_ctor_get(v_attr_3798_, 1);
lean_inc_ref(v_ext_3803_);
lean_dec_ref(v_attr_3798_);
v_toEnvExtension_3804_ = lean_ctor_get(v_ext_3803_, 0);
v_asyncMode_3805_ = lean_ctor_get(v_toEnvExtension_3804_, 2);
lean_inc(v_asyncMode_3805_);
v___x_3806_ = 0;
lean_inc(v_decl_3800_);
v___x_3807_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3801_, v_ext_3803_, v_env_3799_, v_asyncMode_3805_, v_decl_3800_, v___x_3806_);
lean_dec(v_asyncMode_3805_);
lean_dec_ref(v_ext_3803_);
v___x_3808_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_3807_, v_decl_3800_);
lean_dec(v_decl_3800_);
lean_dec(v___x_3807_);
return v___x_3808_;
}
else
{
lean_object* v_val_3809_; lean_object* v_ext_3810_; lean_object* v___x_3812_; uint8_t v_isShared_3813_; uint8_t v_isSharedCheck_3840_; 
v_val_3809_ = lean_ctor_get(v___x_3802_, 0);
lean_inc(v_val_3809_);
lean_dec_ref_known(v___x_3802_, 1);
v_ext_3810_ = lean_ctor_get(v_attr_3798_, 1);
v_isSharedCheck_3840_ = !lean_is_exclusive(v_attr_3798_);
if (v_isSharedCheck_3840_ == 0)
{
lean_object* v_unused_3841_; 
v_unused_3841_ = lean_ctor_get(v_attr_3798_, 0);
lean_dec(v_unused_3841_);
v___x_3812_ = v_attr_3798_;
v_isShared_3813_ = v_isSharedCheck_3840_;
goto v_resetjp_3811_;
}
else
{
lean_inc(v_ext_3810_);
lean_dec(v_attr_3798_);
v___x_3812_ = lean_box(0);
v_isShared_3813_ = v_isSharedCheck_3840_;
goto v_resetjp_3811_;
}
v_resetjp_3811_:
{
uint8_t v___x_3814_; lean_object* v___x_3815_; lean_object* v___x_3816_; lean_object* v___x_3817_; uint8_t v___x_3818_; 
v___x_3814_ = 0;
v___x_3815_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_3801_, v_ext_3810_, v_env_3799_, v_val_3809_, v___x_3814_);
lean_dec(v_val_3809_);
lean_dec_ref(v_env_3799_);
lean_dec_ref(v_ext_3810_);
v___x_3816_ = lean_unsigned_to_nat(0u);
v___x_3817_ = lean_array_get_size(v___x_3815_);
v___x_3818_ = lean_nat_dec_lt(v___x_3816_, v___x_3817_);
if (v___x_3818_ == 0)
{
lean_object* v___x_3819_; 
lean_dec_ref(v___x_3815_);
lean_del_object(v___x_3812_);
lean_dec(v_decl_3800_);
lean_dec(v_inst_3797_);
v___x_3819_ = lean_box(0);
return v___x_3819_;
}
else
{
lean_object* v___x_3820_; lean_object* v___x_3821_; uint8_t v___x_3822_; 
v___x_3820_ = lean_unsigned_to_nat(1u);
v___x_3821_ = lean_nat_sub(v___x_3817_, v___x_3820_);
v___x_3822_ = lean_nat_dec_le(v___x_3816_, v___x_3821_);
if (v___x_3822_ == 0)
{
lean_object* v___x_3823_; 
lean_dec(v___x_3821_);
lean_dec_ref(v___x_3815_);
lean_del_object(v___x_3812_);
lean_dec(v_decl_3800_);
lean_dec(v_inst_3797_);
v___x_3823_ = lean_box(0);
return v___x_3823_;
}
else
{
lean_object* v___f_3824_; lean_object* v___x_3826_; 
v___f_3824_ = ((lean_object*)(l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__1));
if (v_isShared_3813_ == 0)
{
lean_ctor_set(v___x_3812_, 1, v_inst_3797_);
lean_ctor_set(v___x_3812_, 0, v_decl_3800_);
v___x_3826_ = v___x_3812_;
goto v_reusejp_3825_;
}
else
{
lean_object* v_reuseFailAlloc_3839_; 
v_reuseFailAlloc_3839_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3839_, 0, v_decl_3800_);
lean_ctor_set(v_reuseFailAlloc_3839_, 1, v_inst_3797_);
v___x_3826_ = v_reuseFailAlloc_3839_;
goto v_reusejp_3825_;
}
v_reusejp_3825_:
{
lean_object* v___x_3827_; lean_object* v___x_3828_; 
v___x_3827_ = ((lean_object*)(l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__2));
v___x_3828_ = l_Array_binSearchAux___redArg(v___f_3824_, v___x_3827_, v___x_3815_, v___x_3826_, v___x_3816_, v___x_3821_);
lean_dec_ref(v___x_3815_);
if (lean_obj_tag(v___x_3828_) == 0)
{
lean_object* v___x_3829_; 
v___x_3829_ = lean_box(0);
return v___x_3829_;
}
else
{
lean_object* v_val_3830_; lean_object* v___x_3832_; uint8_t v_isShared_3833_; uint8_t v_isSharedCheck_3838_; 
v_val_3830_ = lean_ctor_get(v___x_3828_, 0);
v_isSharedCheck_3838_ = !lean_is_exclusive(v___x_3828_);
if (v_isSharedCheck_3838_ == 0)
{
v___x_3832_ = v___x_3828_;
v_isShared_3833_ = v_isSharedCheck_3838_;
goto v_resetjp_3831_;
}
else
{
lean_inc(v_val_3830_);
lean_dec(v___x_3828_);
v___x_3832_ = lean_box(0);
v_isShared_3833_ = v_isSharedCheck_3838_;
goto v_resetjp_3831_;
}
v_resetjp_3831_:
{
lean_object* v_snd_3834_; lean_object* v___x_3836_; 
v_snd_3834_ = lean_ctor_get(v_val_3830_, 1);
lean_inc(v_snd_3834_);
lean_dec(v_val_3830_);
if (v_isShared_3833_ == 0)
{
lean_ctor_set(v___x_3832_, 0, v_snd_3834_);
v___x_3836_ = v___x_3832_;
goto v_reusejp_3835_;
}
else
{
lean_object* v_reuseFailAlloc_3837_; 
v_reuseFailAlloc_3837_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3837_, 0, v_snd_3834_);
v___x_3836_ = v_reuseFailAlloc_3837_;
goto v_reusejp_3835_;
}
v_reusejp_3835_:
{
return v___x_3836_;
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
LEAN_EXPORT lean_object* l_Lean_EnumAttributes_getValue(lean_object* v_00_u03b1_3842_, lean_object* v_inst_3843_, lean_object* v_attr_3844_, lean_object* v_env_3845_, lean_object* v_decl_3846_){
_start:
{
lean_object* v___x_3847_; 
v___x_3847_ = l_Lean_EnumAttributes_getValue___redArg(v_inst_3843_, v_attr_3844_, v_env_3845_, v_decl_3846_);
return v___x_3847_;
}
}
LEAN_EXPORT lean_object* l_Lean_EnumAttributes_setValue___redArg(lean_object* v_attrs_3856_, lean_object* v_env_3857_, lean_object* v_decl_3858_, lean_object* v_val_3859_){
_start:
{
lean_object* v_ext_3860_; lean_object* v___x_3862_; uint8_t v_isShared_3863_; uint8_t v_isSharedCheck_3930_; 
v_ext_3860_ = lean_ctor_get(v_attrs_3856_, 1);
v_isSharedCheck_3930_ = !lean_is_exclusive(v_attrs_3856_);
if (v_isSharedCheck_3930_ == 0)
{
lean_object* v_unused_3931_; 
v_unused_3931_ = lean_ctor_get(v_attrs_3856_, 0);
lean_dec(v_unused_3931_);
v___x_3862_ = v_attrs_3856_;
v_isShared_3863_ = v_isSharedCheck_3930_;
goto v_resetjp_3861_;
}
else
{
lean_inc(v_ext_3860_);
lean_dec(v_attrs_3856_);
v___x_3862_ = lean_box(0);
v_isShared_3863_ = v_isSharedCheck_3930_;
goto v_resetjp_3861_;
}
v_resetjp_3861_:
{
lean_object* v_toEnvExtension_3864_; lean_object* v_name_3865_; lean_object* v_addEntryFn_3866_; lean_object* v___x_3867_; uint8_t v___x_3868_; lean_object* v___x_3869_; lean_object* v___x_3870_; lean_object* v___x_3871_; lean_object* v___x_3872_; lean_object* v___x_3873_; lean_object* v___x_3874_; lean_object* v___x_3875_; lean_object* v_pfx_3876_; lean_object* v___x_3877_; 
v_toEnvExtension_3864_ = lean_ctor_get(v_ext_3860_, 0);
lean_inc_ref(v_toEnvExtension_3864_);
v_name_3865_ = lean_ctor_get(v_ext_3860_, 1);
v_addEntryFn_3866_ = lean_ctor_get(v_ext_3860_, 3);
lean_inc(v_addEntryFn_3866_);
v___x_3867_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__0));
v___x_3868_ = 1;
lean_inc(v_name_3865_);
v___x_3869_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_3865_, v___x_3868_);
v___x_3870_ = lean_string_append(v___x_3867_, v___x_3869_);
lean_dec_ref(v___x_3869_);
v___x_3871_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__1));
v___x_3872_ = lean_string_append(v___x_3870_, v___x_3871_);
lean_inc(v_decl_3858_);
v___x_3873_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_decl_3858_, v___x_3868_);
v___x_3874_ = lean_string_append(v___x_3872_, v___x_3873_);
lean_dec_ref(v___x_3873_);
v___x_3875_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__4));
v_pfx_3876_ = lean_string_append(v___x_3874_, v___x_3875_);
v___x_3877_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3857_, v_decl_3858_);
if (lean_obj_tag(v___x_3877_) == 0)
{
lean_object* v_asyncMode_3878_; uint8_t v_logWrites_3879_; uint8_t v___x_3880_; 
v_asyncMode_3878_ = lean_ctor_get(v_toEnvExtension_3864_, 2);
lean_inc(v_asyncMode_3878_);
v_logWrites_3879_ = lean_ctor_get_uint8(v_toEnvExtension_3864_, sizeof(void*)*6);
lean_inc(v_decl_3858_);
lean_inc_ref(v_env_3857_);
v___x_3880_ = l_Lean_EnvExtension_asyncMayModify___redArg(v_env_3857_, v_decl_3858_, v_asyncMode_3878_);
if (v___x_3880_ == 0)
{
lean_object* v___x_3881_; lean_object* v___x_3882_; lean_object* v___y_3884_; lean_object* v___x_3888_; 
lean_dec(v_asyncMode_3878_);
lean_dec(v_addEntryFn_3866_);
lean_dec_ref(v_toEnvExtension_3864_);
lean_del_object(v___x_3862_);
lean_dec_ref(v_ext_3860_);
lean_dec(v_val_3859_);
lean_dec(v_decl_3858_);
v___x_3881_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__2));
v___x_3882_ = lean_string_append(v_pfx_3876_, v___x_3881_);
v___x_3888_ = l_Lean_Environment_asyncPrefix_x3f(v_env_3857_);
if (lean_obj_tag(v___x_3888_) == 0)
{
lean_object* v___x_3889_; 
v___x_3889_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__3));
v___y_3884_ = v___x_3889_;
goto v___jp_3883_;
}
else
{
lean_object* v_val_3890_; lean_object* v___x_3891_; lean_object* v___x_3892_; lean_object* v___x_3893_; lean_object* v___x_3894_; lean_object* v___x_3895_; lean_object* v___x_3896_; 
v_val_3890_ = lean_ctor_get(v___x_3888_, 0);
lean_inc(v_val_3890_);
lean_dec_ref_known(v___x_3888_, 1);
v___x_3891_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__4));
v___x_3892_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_val_3890_, v___x_3868_);
v___x_3893_ = l_addParenHeuristic(v___x_3892_);
v___x_3894_ = lean_string_append(v___x_3891_, v___x_3893_);
lean_dec_ref(v___x_3893_);
v___x_3895_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__5));
v___x_3896_ = lean_string_append(v___x_3894_, v___x_3895_);
v___y_3884_ = v___x_3896_;
goto v___jp_3883_;
}
v___jp_3883_:
{
lean_object* v___x_3885_; lean_object* v___x_3886_; lean_object* v___x_3887_; 
v___x_3885_ = lean_string_append(v___x_3882_, v___y_3884_);
lean_dec_ref(v___y_3884_);
v___x_3886_ = lean_string_append(v___x_3885_, v___x_3875_);
v___x_3887_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3887_, 0, v___x_3886_);
return v___x_3887_;
}
}
else
{
lean_object* v___x_3897_; uint8_t v___x_3898_; lean_object* v___x_3899_; lean_object* v___x_3900_; 
v___x_3897_ = lean_box(1);
v___x_3898_ = 0;
lean_inc(v_decl_3858_);
lean_inc_ref(v_env_3857_);
v___x_3899_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3897_, v_ext_3860_, v_env_3857_, v_asyncMode_3878_, v_decl_3858_, v___x_3898_);
lean_dec_ref(v_ext_3860_);
v___x_3900_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_3899_, v_decl_3858_);
lean_dec(v___x_3899_);
if (lean_obj_tag(v___x_3900_) == 0)
{
lean_object* v___x_3902_; 
lean_dec_ref(v_pfx_3876_);
lean_inc(v_decl_3858_);
if (v_isShared_3863_ == 0)
{
lean_ctor_set(v___x_3862_, 1, v_val_3859_);
lean_ctor_set(v___x_3862_, 0, v_decl_3858_);
v___x_3902_ = v___x_3862_;
goto v_reusejp_3901_;
}
else
{
lean_object* v_reuseFailAlloc_3909_; 
v_reuseFailAlloc_3909_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3909_, 0, v_decl_3858_);
lean_ctor_set(v_reuseFailAlloc_3909_, 1, v_val_3859_);
v___x_3902_ = v_reuseFailAlloc_3909_;
goto v_reusejp_3901_;
}
v_reusejp_3901_:
{
lean_object* v___f_3903_; 
v___f_3903_ = lean_alloc_closure((void*)(l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__1), 3, 2);
lean_closure_set(v___f_3903_, 0, v_addEntryFn_3866_);
lean_closure_set(v___f_3903_, 1, v___x_3902_);
if (v_logWrites_3879_ == 0)
{
lean_object* v___x_3904_; lean_object* v___x_3905_; 
v___x_3904_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_3864_, v_env_3857_, v___f_3903_, v_asyncMode_3878_, v_decl_3858_, v___x_3880_);
lean_dec(v_asyncMode_3878_);
v___x_3905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3905_, 0, v___x_3904_);
return v___x_3905_;
}
else
{
lean_object* v___x_3906_; lean_object* v___x_3907_; lean_object* v___x_3908_; 
lean_inc_ref(v_toEnvExtension_3864_);
v___x_3906_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_3864_, v_env_3857_);
lean_dec_ref(v_env_3857_);
v___x_3907_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_3864_, v___x_3906_, v___f_3903_, v_asyncMode_3878_, v_decl_3858_, v___x_3880_);
lean_dec(v_asyncMode_3878_);
v___x_3908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3908_, 0, v___x_3907_);
return v___x_3908_;
}
}
}
else
{
lean_object* v___x_3911_; uint8_t v_isShared_3912_; uint8_t v_isSharedCheck_3918_; 
lean_dec(v_asyncMode_3878_);
lean_dec(v_addEntryFn_3866_);
lean_dec_ref(v_toEnvExtension_3864_);
lean_del_object(v___x_3862_);
lean_dec(v_val_3859_);
lean_dec(v_decl_3858_);
lean_dec_ref(v_env_3857_);
v_isSharedCheck_3918_ = !lean_is_exclusive(v___x_3900_);
if (v_isSharedCheck_3918_ == 0)
{
lean_object* v_unused_3919_; 
v_unused_3919_ = lean_ctor_get(v___x_3900_, 0);
lean_dec(v_unused_3919_);
v___x_3911_ = v___x_3900_;
v_isShared_3912_ = v_isSharedCheck_3918_;
goto v_resetjp_3910_;
}
else
{
lean_dec(v___x_3900_);
v___x_3911_ = lean_box(0);
v_isShared_3912_ = v_isSharedCheck_3918_;
goto v_resetjp_3910_;
}
v_resetjp_3910_:
{
lean_object* v___x_3913_; lean_object* v___x_3914_; lean_object* v___x_3916_; 
v___x_3913_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__6));
v___x_3914_ = lean_string_append(v_pfx_3876_, v___x_3913_);
if (v_isShared_3912_ == 0)
{
lean_ctor_set_tag(v___x_3911_, 0);
lean_ctor_set(v___x_3911_, 0, v___x_3914_);
v___x_3916_ = v___x_3911_;
goto v_reusejp_3915_;
}
else
{
lean_object* v_reuseFailAlloc_3917_; 
v_reuseFailAlloc_3917_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3917_, 0, v___x_3914_);
v___x_3916_ = v_reuseFailAlloc_3917_;
goto v_reusejp_3915_;
}
v_reusejp_3915_:
{
return v___x_3916_;
}
}
}
}
}
else
{
lean_object* v___x_3921_; uint8_t v_isShared_3922_; uint8_t v_isSharedCheck_3928_; 
lean_dec(v_addEntryFn_3866_);
lean_dec_ref(v_toEnvExtension_3864_);
lean_del_object(v___x_3862_);
lean_dec_ref(v_ext_3860_);
lean_dec(v_val_3859_);
lean_dec(v_decl_3858_);
lean_dec_ref(v_env_3857_);
v_isSharedCheck_3928_ = !lean_is_exclusive(v___x_3877_);
if (v_isSharedCheck_3928_ == 0)
{
lean_object* v_unused_3929_; 
v_unused_3929_ = lean_ctor_get(v___x_3877_, 0);
lean_dec(v_unused_3929_);
v___x_3921_ = v___x_3877_;
v_isShared_3922_ = v_isSharedCheck_3928_;
goto v_resetjp_3920_;
}
else
{
lean_dec(v___x_3877_);
v___x_3921_ = lean_box(0);
v_isShared_3922_ = v_isSharedCheck_3928_;
goto v_resetjp_3920_;
}
v_resetjp_3920_:
{
lean_object* v___x_3923_; lean_object* v___x_3924_; lean_object* v___x_3926_; 
v___x_3923_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__7));
v___x_3924_ = lean_string_append(v_pfx_3876_, v___x_3923_);
if (v_isShared_3922_ == 0)
{
lean_ctor_set_tag(v___x_3921_, 0);
lean_ctor_set(v___x_3921_, 0, v___x_3924_);
v___x_3926_ = v___x_3921_;
goto v_reusejp_3925_;
}
else
{
lean_object* v_reuseFailAlloc_3927_; 
v_reuseFailAlloc_3927_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3927_, 0, v___x_3924_);
v___x_3926_ = v_reuseFailAlloc_3927_;
goto v_reusejp_3925_;
}
v_reusejp_3925_:
{
return v___x_3926_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_EnumAttributes_setValue(lean_object* v_00_u03b1_3932_, lean_object* v_attrs_3933_, lean_object* v_env_3934_, lean_object* v_decl_3935_, lean_object* v_val_3936_){
_start:
{
lean_object* v___x_3937_; 
v___x_3937_ = l_Lean_EnumAttributes_setValue___redArg(v_attrs_3933_, v_env_3934_, v_decl_3935_, v_val_3936_);
return v___x_3937_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_2990505691____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3939_; lean_object* v___x_3940_; lean_object* v___x_3941_; 
v___x_3939_ = lean_obj_once(&l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_, &l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2__once, _init_l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_);
v___x_3940_ = lean_st_mk_ref(v___x_3939_);
v___x_3941_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3941_, 0, v___x_3940_);
return v___x_3941_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_2990505691____hygCtx___hyg_2____boxed(lean_object* v_a_3942_){
_start:
{
lean_object* v_res_3943_; 
v_res_3943_ = l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_2990505691____hygCtx___hyg_2_();
return v_res_3943_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerAttributeImplBuilder(lean_object* v_builderId_3946_, lean_object* v_builder_3947_){
_start:
{
lean_object* v___x_3949_; lean_object* v___x_3950_; uint8_t v___x_3951_; 
v___x_3949_ = l_Lean_attributeImplBuilderTableRef;
v___x_3950_ = lean_st_ref_get(v___x_3949_);
v___x_3951_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(v___x_3950_, v_builderId_3946_);
lean_dec(v___x_3950_);
if (v___x_3951_ == 0)
{
lean_object* v___x_3952_; lean_object* v___x_3953_; lean_object* v___x_3954_; lean_object* v___x_3955_; 
v___x_3952_ = lean_st_ref_take(v___x_3949_);
v___x_3953_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1___redArg(v___x_3952_, v_builderId_3946_, v_builder_3947_);
v___x_3954_ = lean_st_ref_put(v___x_3949_, v___x_3953_);
v___x_3955_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3955_, 0, v___x_3954_);
return v___x_3955_;
}
else
{
lean_object* v___x_3956_; lean_object* v___x_3957_; lean_object* v___x_3958_; lean_object* v___x_3959_; lean_object* v___x_3960_; lean_object* v___x_3961_; lean_object* v___x_3962_; 
lean_dec_ref(v_builder_3947_);
v___x_3956_ = ((lean_object*)(l_Lean_registerAttributeImplBuilder___closed__0));
v___x_3957_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_builderId_3946_, v___x_3951_);
v___x_3958_ = lean_string_append(v___x_3956_, v___x_3957_);
lean_dec_ref(v___x_3957_);
v___x_3959_ = ((lean_object*)(l_Lean_registerAttributeImplBuilder___closed__1));
v___x_3960_ = lean_string_append(v___x_3958_, v___x_3959_);
v___x_3961_ = lean_mk_io_user_error(v___x_3960_);
v___x_3962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3962_, 0, v___x_3961_);
return v___x_3962_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerAttributeImplBuilder___boxed(lean_object* v_builderId_3963_, lean_object* v_builder_3964_, lean_object* v_a_3965_){
_start:
{
lean_object* v_res_3966_; 
v_res_3966_ = l_Lean_registerAttributeImplBuilder(v_builderId_3963_, v_builder_3964_);
return v_res_3966_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___redArg(lean_object* v_e_3967_){
_start:
{
if (lean_obj_tag(v_e_3967_) == 0)
{
lean_object* v_a_3969_; lean_object* v___x_3971_; uint8_t v_isShared_3972_; uint8_t v_isSharedCheck_3977_; 
v_a_3969_ = lean_ctor_get(v_e_3967_, 0);
v_isSharedCheck_3977_ = !lean_is_exclusive(v_e_3967_);
if (v_isSharedCheck_3977_ == 0)
{
v___x_3971_ = v_e_3967_;
v_isShared_3972_ = v_isSharedCheck_3977_;
goto v_resetjp_3970_;
}
else
{
lean_inc(v_a_3969_);
lean_dec(v_e_3967_);
v___x_3971_ = lean_box(0);
v_isShared_3972_ = v_isSharedCheck_3977_;
goto v_resetjp_3970_;
}
v_resetjp_3970_:
{
lean_object* v___x_3973_; lean_object* v___x_3975_; 
v___x_3973_ = lean_mk_io_user_error(v_a_3969_);
if (v_isShared_3972_ == 0)
{
lean_ctor_set_tag(v___x_3971_, 1);
lean_ctor_set(v___x_3971_, 0, v___x_3973_);
v___x_3975_ = v___x_3971_;
goto v_reusejp_3974_;
}
else
{
lean_object* v_reuseFailAlloc_3976_; 
v_reuseFailAlloc_3976_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3976_, 0, v___x_3973_);
v___x_3975_ = v_reuseFailAlloc_3976_;
goto v_reusejp_3974_;
}
v_reusejp_3974_:
{
return v___x_3975_;
}
}
}
else
{
lean_object* v_a_3978_; lean_object* v___x_3980_; uint8_t v_isShared_3981_; uint8_t v_isSharedCheck_3985_; 
v_a_3978_ = lean_ctor_get(v_e_3967_, 0);
v_isSharedCheck_3985_ = !lean_is_exclusive(v_e_3967_);
if (v_isSharedCheck_3985_ == 0)
{
v___x_3980_ = v_e_3967_;
v_isShared_3981_ = v_isSharedCheck_3985_;
goto v_resetjp_3979_;
}
else
{
lean_inc(v_a_3978_);
lean_dec(v_e_3967_);
v___x_3980_ = lean_box(0);
v_isShared_3981_ = v_isSharedCheck_3985_;
goto v_resetjp_3979_;
}
v_resetjp_3979_:
{
lean_object* v___x_3983_; 
if (v_isShared_3981_ == 0)
{
lean_ctor_set_tag(v___x_3980_, 0);
v___x_3983_ = v___x_3980_;
goto v_reusejp_3982_;
}
else
{
lean_object* v_reuseFailAlloc_3984_; 
v_reuseFailAlloc_3984_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3984_, 0, v_a_3978_);
v___x_3983_ = v_reuseFailAlloc_3984_;
goto v_reusejp_3982_;
}
v_reusejp_3982_:
{
return v___x_3983_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___redArg___boxed(lean_object* v_e_3986_, lean_object* v_a_3987_){
_start:
{
lean_object* v_res_3988_; 
v_res_3988_ = l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___redArg(v_e_3986_);
return v_res_3988_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1(lean_object* v_00_u03b1_3989_, lean_object* v_e_3990_){
_start:
{
lean_object* v___x_3992_; 
v___x_3992_ = l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___redArg(v_e_3990_);
return v___x_3992_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___boxed(lean_object* v_00_u03b1_3993_, lean_object* v_e_3994_, lean_object* v_a_3995_){
_start:
{
lean_object* v_res_3996_; 
v_res_3996_ = l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1(v_00_u03b1_3993_, v_e_3994_);
return v_res_3996_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___redArg(lean_object* v_a_3997_, lean_object* v_x_3998_){
_start:
{
if (lean_obj_tag(v_x_3998_) == 0)
{
lean_object* v___x_3999_; 
v___x_3999_ = lean_box(0);
return v___x_3999_;
}
else
{
lean_object* v_key_4000_; lean_object* v_value_4001_; lean_object* v_tail_4002_; uint8_t v___x_4003_; 
v_key_4000_ = lean_ctor_get(v_x_3998_, 0);
v_value_4001_ = lean_ctor_get(v_x_3998_, 1);
v_tail_4002_ = lean_ctor_get(v_x_3998_, 2);
v___x_4003_ = lean_name_eq(v_key_4000_, v_a_3997_);
if (v___x_4003_ == 0)
{
v_x_3998_ = v_tail_4002_;
goto _start;
}
else
{
lean_object* v___x_4005_; 
lean_inc(v_value_4001_);
v___x_4005_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4005_, 0, v_value_4001_);
return v___x_4005_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___redArg___boxed(lean_object* v_a_4006_, lean_object* v_x_4007_){
_start:
{
lean_object* v_res_4008_; 
v_res_4008_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___redArg(v_a_4006_, v_x_4007_);
lean_dec(v_x_4007_);
lean_dec(v_a_4006_);
return v_res_4008_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(lean_object* v_m_4009_, lean_object* v_a_4010_){
_start:
{
lean_object* v_buckets_4011_; lean_object* v___x_4012_; uint64_t v___y_4014_; 
v_buckets_4011_ = lean_ctor_get(v_m_4009_, 1);
v___x_4012_ = lean_array_get_size(v_buckets_4011_);
if (lean_obj_tag(v_a_4010_) == 0)
{
uint64_t v___x_4028_; 
v___x_4028_ = 1723ULL;
v___y_4014_ = v___x_4028_;
goto v___jp_4013_;
}
else
{
uint64_t v_hash_4029_; 
v_hash_4029_ = lean_ctor_get_uint64(v_a_4010_, sizeof(void*)*2);
v___y_4014_ = v_hash_4029_;
goto v___jp_4013_;
}
v___jp_4013_:
{
uint64_t v___x_4015_; uint64_t v___x_4016_; uint64_t v_fold_4017_; uint64_t v___x_4018_; uint64_t v___x_4019_; uint64_t v___x_4020_; size_t v___x_4021_; size_t v___x_4022_; size_t v___x_4023_; size_t v___x_4024_; size_t v___x_4025_; lean_object* v___x_4026_; lean_object* v___x_4027_; 
v___x_4015_ = 32ULL;
v___x_4016_ = lean_uint64_shift_right(v___y_4014_, v___x_4015_);
v_fold_4017_ = lean_uint64_xor(v___y_4014_, v___x_4016_);
v___x_4018_ = 16ULL;
v___x_4019_ = lean_uint64_shift_right(v_fold_4017_, v___x_4018_);
v___x_4020_ = lean_uint64_xor(v_fold_4017_, v___x_4019_);
v___x_4021_ = lean_uint64_to_usize(v___x_4020_);
v___x_4022_ = lean_usize_of_nat(v___x_4012_);
v___x_4023_ = ((size_t)1ULL);
v___x_4024_ = lean_usize_sub(v___x_4022_, v___x_4023_);
v___x_4025_ = lean_usize_land(v___x_4021_, v___x_4024_);
v___x_4026_ = lean_array_uget_borrowed(v_buckets_4011_, v___x_4025_);
v___x_4027_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___redArg(v_a_4010_, v___x_4026_);
return v___x_4027_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg___boxed(lean_object* v_m_4030_, lean_object* v_a_4031_){
_start:
{
lean_object* v_res_4032_; 
v_res_4032_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(v_m_4030_, v_a_4031_);
lean_dec(v_a_4031_);
lean_dec_ref(v_m_4030_);
return v_res_4032_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAttributeImplOfEntry(lean_object* v_e_4034_){
_start:
{
lean_object* v___x_4036_; lean_object* v___x_4037_; lean_object* v_builderId_4038_; lean_object* v_ref_4039_; lean_object* v_args_4040_; lean_object* v___x_4041_; 
v___x_4036_ = l_Lean_attributeImplBuilderTableRef;
v___x_4037_ = lean_st_ref_get(v___x_4036_);
v_builderId_4038_ = lean_ctor_get(v_e_4034_, 0);
lean_inc(v_builderId_4038_);
v_ref_4039_ = lean_ctor_get(v_e_4034_, 1);
lean_inc(v_ref_4039_);
v_args_4040_ = lean_ctor_get(v_e_4034_, 2);
lean_inc(v_args_4040_);
lean_dec_ref(v_e_4034_);
v___x_4041_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(v___x_4037_, v_builderId_4038_);
lean_dec(v___x_4037_);
if (lean_obj_tag(v___x_4041_) == 0)
{
lean_object* v___x_4042_; uint8_t v___x_4043_; lean_object* v___x_4044_; lean_object* v___x_4045_; lean_object* v___x_4046_; lean_object* v___x_4047_; lean_object* v___x_4048_; lean_object* v___x_4049_; 
lean_dec(v_args_4040_);
lean_dec(v_ref_4039_);
v___x_4042_ = ((lean_object*)(l_Lean_mkAttributeImplOfEntry___closed__0));
v___x_4043_ = 1;
v___x_4044_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_builderId_4038_, v___x_4043_);
v___x_4045_ = lean_string_append(v___x_4042_, v___x_4044_);
lean_dec_ref(v___x_4044_);
v___x_4046_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__4));
v___x_4047_ = lean_string_append(v___x_4045_, v___x_4046_);
v___x_4048_ = lean_mk_io_user_error(v___x_4047_);
v___x_4049_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4049_, 0, v___x_4048_);
return v___x_4049_;
}
else
{
lean_object* v_val_4050_; lean_object* v___x_4051_; lean_object* v___x_4052_; 
lean_dec(v_builderId_4038_);
v_val_4050_ = lean_ctor_get(v___x_4041_, 0);
lean_inc(v_val_4050_);
lean_dec_ref_known(v___x_4041_, 1);
v___x_4051_ = lean_apply_2(v_val_4050_, v_ref_4039_, v_args_4040_);
v___x_4052_ = l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___redArg(v___x_4051_);
return v___x_4052_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkAttributeImplOfEntry___boxed(lean_object* v_e_4053_, lean_object* v_a_4054_){
_start:
{
lean_object* v_res_4055_; 
v_res_4055_ = l_Lean_mkAttributeImplOfEntry(v_e_4053_);
return v_res_4055_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0(lean_object* v_00_u03b2_4056_, lean_object* v_m_4057_, lean_object* v_a_4058_){
_start:
{
lean_object* v___x_4059_; 
v___x_4059_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(v_m_4057_, v_a_4058_);
return v___x_4059_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___boxed(lean_object* v_00_u03b2_4060_, lean_object* v_m_4061_, lean_object* v_a_4062_){
_start:
{
lean_object* v_res_4063_; 
v_res_4063_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0(v_00_u03b2_4060_, v_m_4061_, v_a_4062_);
lean_dec(v_a_4062_);
lean_dec_ref(v_m_4061_);
return v_res_4063_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0(lean_object* v_00_u03b2_4064_, lean_object* v_a_4065_, lean_object* v_x_4066_){
_start:
{
lean_object* v___x_4067_; 
v___x_4067_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___redArg(v_a_4065_, v_x_4066_);
return v___x_4067_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___boxed(lean_object* v_00_u03b2_4068_, lean_object* v_a_4069_, lean_object* v_x_4070_){
_start:
{
lean_object* v_res_4071_; 
v_res_4071_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0(v_00_u03b2_4068_, v_a_4069_, v_x_4070_);
lean_dec(v_x_4070_);
lean_dec(v_a_4069_);
return v_res_4071_;
}
}
static lean_object* _init_l_Lean_instInhabitedAttributeExtensionState_default___closed__0(void){
_start:
{
lean_object* v___x_4072_; lean_object* v___x_4073_; lean_object* v___x_4074_; 
v___x_4072_ = lean_obj_once(&l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_, &l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2__once, _init_l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_);
v___x_4073_ = lean_box(0);
v___x_4074_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4074_, 0, v___x_4073_);
lean_ctor_set(v___x_4074_, 1, v___x_4072_);
return v___x_4074_;
}
}
static lean_object* _init_l_Lean_instInhabitedAttributeExtensionState_default(void){
_start:
{
lean_object* v___x_4075_; 
v___x_4075_ = lean_obj_once(&l_Lean_instInhabitedAttributeExtensionState_default___closed__0, &l_Lean_instInhabitedAttributeExtensionState_default___closed__0_once, _init_l_Lean_instInhabitedAttributeExtensionState_default___closed__0);
return v___x_4075_;
}
}
static lean_object* _init_l_Lean_instInhabitedAttributeExtensionState(void){
_start:
{
lean_object* v___x_4076_; 
v___x_4076_ = l_Lean_instInhabitedAttributeExtensionState_default;
return v___x_4076_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_AttributeExtension_mkInitial(){
_start:
{
lean_object* v___x_4078_; lean_object* v___x_4079_; lean_object* v___x_4080_; lean_object* v___x_4081_; lean_object* v___x_4082_; 
v___x_4078_ = l_Lean_attributeMapRef;
v___x_4079_ = lean_st_ref_get(v___x_4078_);
v___x_4080_ = lean_box(0);
v___x_4081_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4081_, 0, v___x_4080_);
lean_ctor_set(v___x_4081_, 1, v___x_4079_);
v___x_4082_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4082_, 0, v___x_4081_);
return v___x_4082_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_AttributeExtension_mkInitial___boxed(lean_object* v_a_4083_){
_start:
{
lean_object* v_res_4084_; 
v_res_4084_ = l___private_Lean_Attributes_0__Lean_AttributeExtension_mkInitial();
return v_res_4084_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAttributeImplOfConstantUnsafe(lean_object* v_env_4090_, lean_object* v_opts_4091_, lean_object* v_declName_4092_){
_start:
{
uint8_t v___x_4095_; lean_object* v___x_4096_; 
v___x_4095_ = 0;
lean_inc(v_declName_4092_);
lean_inc_ref(v_env_4090_);
v___x_4096_ = l_Lean_Environment_find_x3f(v_env_4090_, v_declName_4092_, v___x_4095_);
if (lean_obj_tag(v___x_4096_) == 0)
{
lean_object* v___x_4097_; uint8_t v___x_4098_; lean_object* v___x_4099_; lean_object* v___x_4100_; lean_object* v___x_4101_; lean_object* v___x_4102_; lean_object* v___x_4103_; 
lean_dec_ref(v_env_4090_);
v___x_4097_ = ((lean_object*)(l_Lean_mkAttributeImplOfConstantUnsafe___closed__2));
v___x_4098_ = 1;
v___x_4099_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_declName_4092_, v___x_4098_);
v___x_4100_ = lean_string_append(v___x_4097_, v___x_4099_);
lean_dec_ref(v___x_4099_);
v___x_4101_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__4));
v___x_4102_ = lean_string_append(v___x_4100_, v___x_4101_);
v___x_4103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4103_, 0, v___x_4102_);
return v___x_4103_;
}
else
{
lean_object* v_val_4104_; lean_object* v___x_4105_; 
v_val_4104_ = lean_ctor_get(v___x_4096_, 0);
lean_inc(v_val_4104_);
lean_dec_ref_known(v___x_4096_, 1);
v___x_4105_ = l_Lean_ConstantInfo_type(v_val_4104_);
lean_dec(v_val_4104_);
if (lean_obj_tag(v___x_4105_) == 4)
{
lean_object* v_declName_4106_; 
v_declName_4106_ = lean_ctor_get(v___x_4105_, 0);
lean_inc(v_declName_4106_);
lean_dec_ref_known(v___x_4105_, 2);
if (lean_obj_tag(v_declName_4106_) == 1)
{
lean_object* v_pre_4107_; 
v_pre_4107_ = lean_ctor_get(v_declName_4106_, 0);
lean_inc(v_pre_4107_);
if (lean_obj_tag(v_pre_4107_) == 1)
{
lean_object* v_pre_4108_; 
v_pre_4108_ = lean_ctor_get(v_pre_4107_, 0);
if (lean_obj_tag(v_pre_4108_) == 0)
{
lean_object* v_str_4109_; lean_object* v_str_4110_; lean_object* v___x_4111_; uint8_t v___x_4112_; 
v_str_4109_ = lean_ctor_get(v_declName_4106_, 1);
lean_inc_ref(v_str_4109_);
lean_dec_ref_known(v_declName_4106_, 2);
v_str_4110_ = lean_ctor_get(v_pre_4107_, 1);
lean_inc_ref(v_str_4110_);
lean_dec_ref_known(v_pre_4107_, 2);
v___x_4111_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__0));
v___x_4112_ = lean_string_dec_eq(v_str_4110_, v___x_4111_);
lean_dec_ref(v_str_4110_);
if (v___x_4112_ == 0)
{
lean_dec_ref(v_str_4109_);
lean_dec(v_declName_4092_);
lean_dec_ref(v_env_4090_);
goto v___jp_4093_;
}
else
{
lean_object* v___x_4113_; uint8_t v___x_4114_; 
v___x_4113_ = ((lean_object*)(l_Lean_mkAttributeImplOfConstantUnsafe___closed__3));
v___x_4114_ = lean_string_dec_eq(v_str_4109_, v___x_4113_);
lean_dec_ref(v_str_4109_);
if (v___x_4114_ == 0)
{
lean_dec(v_declName_4092_);
lean_dec_ref(v_env_4090_);
goto v___jp_4093_;
}
else
{
lean_object* v___x_4115_; 
v___x_4115_ = l_Lean_Environment_evalConst___redArg(v_env_4090_, v_opts_4091_, v_declName_4092_, v___x_4114_);
lean_dec(v_declName_4092_);
lean_dec_ref(v_env_4090_);
return v___x_4115_;
}
}
}
else
{
lean_dec_ref_known(v_pre_4107_, 2);
lean_dec_ref_known(v_declName_4106_, 2);
lean_dec(v_declName_4092_);
lean_dec_ref(v_env_4090_);
goto v___jp_4093_;
}
}
else
{
lean_dec_ref_known(v_declName_4106_, 2);
lean_dec(v_pre_4107_);
lean_dec(v_declName_4092_);
lean_dec_ref(v_env_4090_);
goto v___jp_4093_;
}
}
else
{
lean_dec(v_declName_4106_);
lean_dec(v_declName_4092_);
lean_dec_ref(v_env_4090_);
goto v___jp_4093_;
}
}
else
{
lean_dec_ref(v___x_4105_);
lean_dec(v_declName_4092_);
lean_dec_ref(v_env_4090_);
goto v___jp_4093_;
}
}
v___jp_4093_:
{
lean_object* v___x_4094_; 
v___x_4094_ = ((lean_object*)(l_Lean_mkAttributeImplOfConstantUnsafe___closed__1));
return v___x_4094_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkAttributeImplOfConstantUnsafe___boxed(lean_object* v_env_4116_, lean_object* v_opts_4117_, lean_object* v_declName_4118_){
_start:
{
lean_object* v_res_4119_; 
v_res_4119_ = l_Lean_mkAttributeImplOfConstantUnsafe(v_env_4116_, v_opts_4117_, v_declName_4118_);
lean_dec_ref(v_opts_4117_);
return v_res_4119_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg(lean_object* v_as_4120_, size_t v_i_4121_, size_t v_stop_4122_, lean_object* v_b_4123_){
_start:
{
uint8_t v___x_4125_; 
v___x_4125_ = lean_usize_dec_eq(v_i_4121_, v_stop_4122_);
if (v___x_4125_ == 0)
{
lean_object* v___x_4126_; lean_object* v___x_4127_; 
v___x_4126_ = lean_array_uget_borrowed(v_as_4120_, v_i_4121_);
lean_inc(v___x_4126_);
v___x_4127_ = l_Lean_mkAttributeImplOfEntry(v___x_4126_);
if (lean_obj_tag(v___x_4127_) == 0)
{
lean_object* v_a_4128_; lean_object* v_toAttributeImplCore_4129_; lean_object* v_name_4130_; lean_object* v___x_4131_; size_t v___x_4132_; size_t v___x_4133_; 
v_a_4128_ = lean_ctor_get(v___x_4127_, 0);
lean_inc(v_a_4128_);
lean_dec_ref_known(v___x_4127_, 1);
v_toAttributeImplCore_4129_ = lean_ctor_get(v_a_4128_, 0);
v_name_4130_ = lean_ctor_get(v_toAttributeImplCore_4129_, 1);
lean_inc(v_name_4130_);
v___x_4131_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1___redArg(v_b_4123_, v_name_4130_, v_a_4128_);
v___x_4132_ = ((size_t)1ULL);
v___x_4133_ = lean_usize_add(v_i_4121_, v___x_4132_);
v_i_4121_ = v___x_4133_;
v_b_4123_ = v___x_4131_;
goto _start;
}
else
{
lean_object* v_a_4135_; lean_object* v___x_4137_; uint8_t v_isShared_4138_; uint8_t v_isSharedCheck_4142_; 
lean_dec_ref(v_b_4123_);
v_a_4135_ = lean_ctor_get(v___x_4127_, 0);
v_isSharedCheck_4142_ = !lean_is_exclusive(v___x_4127_);
if (v_isSharedCheck_4142_ == 0)
{
v___x_4137_ = v___x_4127_;
v_isShared_4138_ = v_isSharedCheck_4142_;
goto v_resetjp_4136_;
}
else
{
lean_inc(v_a_4135_);
lean_dec(v___x_4127_);
v___x_4137_ = lean_box(0);
v_isShared_4138_ = v_isSharedCheck_4142_;
goto v_resetjp_4136_;
}
v_resetjp_4136_:
{
lean_object* v___x_4140_; 
if (v_isShared_4138_ == 0)
{
v___x_4140_ = v___x_4137_;
goto v_reusejp_4139_;
}
else
{
lean_object* v_reuseFailAlloc_4141_; 
v_reuseFailAlloc_4141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4141_, 0, v_a_4135_);
v___x_4140_ = v_reuseFailAlloc_4141_;
goto v_reusejp_4139_;
}
v_reusejp_4139_:
{
return v___x_4140_;
}
}
}
}
else
{
lean_object* v___x_4143_; 
v___x_4143_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4143_, 0, v_b_4123_);
return v___x_4143_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg___boxed(lean_object* v_as_4144_, lean_object* v_i_4145_, lean_object* v_stop_4146_, lean_object* v_b_4147_, lean_object* v___y_4148_){
_start:
{
size_t v_i_boxed_4149_; size_t v_stop_boxed_4150_; lean_object* v_res_4151_; 
v_i_boxed_4149_ = lean_unbox_usize(v_i_4145_);
lean_dec(v_i_4145_);
v_stop_boxed_4150_ = lean_unbox_usize(v_stop_4146_);
lean_dec(v_stop_4146_);
v_res_4151_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg(v_as_4144_, v_i_boxed_4149_, v_stop_boxed_4150_, v_b_4147_);
lean_dec_ref(v_as_4144_);
return v_res_4151_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__1(lean_object* v_as_4152_, size_t v_i_4153_, size_t v_stop_4154_, lean_object* v_b_4155_, lean_object* v___y_4156_){
_start:
{
lean_object* v_a_4159_; lean_object* v___y_4164_; uint8_t v___x_4166_; 
v___x_4166_ = lean_usize_dec_eq(v_i_4153_, v_stop_4154_);
if (v___x_4166_ == 0)
{
lean_object* v___x_4167_; lean_object* v___x_4168_; lean_object* v___x_4169_; uint8_t v___x_4170_; 
v___x_4167_ = lean_array_uget_borrowed(v_as_4152_, v_i_4153_);
v___x_4168_ = lean_unsigned_to_nat(0u);
v___x_4169_ = lean_array_get_size(v___x_4167_);
v___x_4170_ = lean_nat_dec_lt(v___x_4168_, v___x_4169_);
if (v___x_4170_ == 0)
{
v_a_4159_ = v_b_4155_;
goto v___jp_4158_;
}
else
{
uint8_t v___x_4171_; 
v___x_4171_ = lean_nat_dec_le(v___x_4169_, v___x_4169_);
if (v___x_4171_ == 0)
{
if (v___x_4170_ == 0)
{
v_a_4159_ = v_b_4155_;
goto v___jp_4158_;
}
else
{
size_t v___x_4172_; size_t v___x_4173_; lean_object* v___x_4174_; 
v___x_4172_ = ((size_t)0ULL);
v___x_4173_ = lean_usize_of_nat(v___x_4169_);
v___x_4174_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg(v___x_4167_, v___x_4172_, v___x_4173_, v_b_4155_);
v___y_4164_ = v___x_4174_;
goto v___jp_4163_;
}
}
else
{
size_t v___x_4175_; size_t v___x_4176_; lean_object* v___x_4177_; 
v___x_4175_ = ((size_t)0ULL);
v___x_4176_ = lean_usize_of_nat(v___x_4169_);
v___x_4177_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg(v___x_4167_, v___x_4175_, v___x_4176_, v_b_4155_);
v___y_4164_ = v___x_4177_;
goto v___jp_4163_;
}
}
}
else
{
lean_object* v___x_4178_; 
v___x_4178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4178_, 0, v_b_4155_);
return v___x_4178_;
}
v___jp_4158_:
{
size_t v___x_4160_; size_t v___x_4161_; 
v___x_4160_ = ((size_t)1ULL);
v___x_4161_ = lean_usize_add(v_i_4153_, v___x_4160_);
v_i_4153_ = v___x_4161_;
v_b_4155_ = v_a_4159_;
goto _start;
}
v___jp_4163_:
{
if (lean_obj_tag(v___y_4164_) == 0)
{
lean_object* v_a_4165_; 
v_a_4165_ = lean_ctor_get(v___y_4164_, 0);
lean_inc(v_a_4165_);
lean_dec_ref_known(v___y_4164_, 1);
v_a_4159_ = v_a_4165_;
goto v___jp_4158_;
}
else
{
return v___y_4164_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__1___boxed(lean_object* v_as_4179_, lean_object* v_i_4180_, lean_object* v_stop_4181_, lean_object* v_b_4182_, lean_object* v___y_4183_, lean_object* v___y_4184_){
_start:
{
size_t v_i_boxed_4185_; size_t v_stop_boxed_4186_; lean_object* v_res_4187_; 
v_i_boxed_4185_ = lean_unbox_usize(v_i_4180_);
lean_dec(v_i_4180_);
v_stop_boxed_4186_ = lean_unbox_usize(v_stop_4181_);
lean_dec(v_stop_4181_);
v_res_4187_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__1(v_as_4179_, v_i_boxed_4185_, v_stop_boxed_4186_, v_b_4182_, v___y_4183_);
lean_dec_ref(v___y_4183_);
lean_dec_ref(v_as_4179_);
return v_res_4187_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_AttributeExtension_addImported(lean_object* v_es_4188_, lean_object* v_a_4189_){
_start:
{
lean_object* v_a_4192_; lean_object* v___y_4197_; lean_object* v___x_4207_; lean_object* v___x_4208_; lean_object* v___x_4209_; lean_object* v___x_4210_; uint8_t v___x_4211_; 
v___x_4207_ = l_Lean_attributeMapRef;
v___x_4208_ = lean_st_ref_get(v___x_4207_);
v___x_4209_ = lean_unsigned_to_nat(0u);
v___x_4210_ = lean_array_get_size(v_es_4188_);
v___x_4211_ = lean_nat_dec_lt(v___x_4209_, v___x_4210_);
if (v___x_4211_ == 0)
{
v_a_4192_ = v___x_4208_;
goto v___jp_4191_;
}
else
{
uint8_t v___x_4212_; 
v___x_4212_ = lean_nat_dec_le(v___x_4210_, v___x_4210_);
if (v___x_4212_ == 0)
{
if (v___x_4211_ == 0)
{
v_a_4192_ = v___x_4208_;
goto v___jp_4191_;
}
else
{
size_t v___x_4213_; size_t v___x_4214_; lean_object* v___x_4215_; 
v___x_4213_ = ((size_t)0ULL);
v___x_4214_ = lean_usize_of_nat(v___x_4210_);
v___x_4215_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__1(v_es_4188_, v___x_4213_, v___x_4214_, v___x_4208_, v_a_4189_);
v___y_4197_ = v___x_4215_;
goto v___jp_4196_;
}
}
else
{
size_t v___x_4216_; size_t v___x_4217_; lean_object* v___x_4218_; 
v___x_4216_ = ((size_t)0ULL);
v___x_4217_ = lean_usize_of_nat(v___x_4210_);
v___x_4218_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__1(v_es_4188_, v___x_4216_, v___x_4217_, v___x_4208_, v_a_4189_);
v___y_4197_ = v___x_4218_;
goto v___jp_4196_;
}
}
v___jp_4191_:
{
lean_object* v___x_4193_; lean_object* v___x_4194_; lean_object* v___x_4195_; 
v___x_4193_ = lean_box(0);
v___x_4194_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4194_, 0, v___x_4193_);
lean_ctor_set(v___x_4194_, 1, v_a_4192_);
v___x_4195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4195_, 0, v___x_4194_);
return v___x_4195_;
}
v___jp_4196_:
{
if (lean_obj_tag(v___y_4197_) == 0)
{
lean_object* v_a_4198_; 
v_a_4198_ = lean_ctor_get(v___y_4197_, 0);
lean_inc(v_a_4198_);
lean_dec_ref_known(v___y_4197_, 1);
v_a_4192_ = v_a_4198_;
goto v___jp_4191_;
}
else
{
lean_object* v_a_4199_; lean_object* v___x_4201_; uint8_t v_isShared_4202_; uint8_t v_isSharedCheck_4206_; 
v_a_4199_ = lean_ctor_get(v___y_4197_, 0);
v_isSharedCheck_4206_ = !lean_is_exclusive(v___y_4197_);
if (v_isSharedCheck_4206_ == 0)
{
v___x_4201_ = v___y_4197_;
v_isShared_4202_ = v_isSharedCheck_4206_;
goto v_resetjp_4200_;
}
else
{
lean_inc(v_a_4199_);
lean_dec(v___y_4197_);
v___x_4201_ = lean_box(0);
v_isShared_4202_ = v_isSharedCheck_4206_;
goto v_resetjp_4200_;
}
v_resetjp_4200_:
{
lean_object* v___x_4204_; 
if (v_isShared_4202_ == 0)
{
v___x_4204_ = v___x_4201_;
goto v_reusejp_4203_;
}
else
{
lean_object* v_reuseFailAlloc_4205_; 
v_reuseFailAlloc_4205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4205_, 0, v_a_4199_);
v___x_4204_ = v_reuseFailAlloc_4205_;
goto v_reusejp_4203_;
}
v_reusejp_4203_:
{
return v___x_4204_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_AttributeExtension_addImported___boxed(lean_object* v_es_4219_, lean_object* v_a_4220_, lean_object* v_a_4221_){
_start:
{
lean_object* v_res_4222_; 
v_res_4222_ = l___private_Lean_Attributes_0__Lean_AttributeExtension_addImported(v_es_4219_, v_a_4220_);
lean_dec_ref(v_a_4220_);
lean_dec_ref(v_es_4219_);
return v_res_4222_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0(lean_object* v_as_4223_, size_t v_i_4224_, size_t v_stop_4225_, lean_object* v_b_4226_, lean_object* v___y_4227_){
_start:
{
lean_object* v___x_4229_; 
v___x_4229_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg(v_as_4223_, v_i_4224_, v_stop_4225_, v_b_4226_);
return v___x_4229_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___boxed(lean_object* v_as_4230_, lean_object* v_i_4231_, lean_object* v_stop_4232_, lean_object* v_b_4233_, lean_object* v___y_4234_, lean_object* v___y_4235_){
_start:
{
size_t v_i_boxed_4236_; size_t v_stop_boxed_4237_; lean_object* v_res_4238_; 
v_i_boxed_4236_ = lean_unbox_usize(v_i_4231_);
lean_dec(v_i_4231_);
v_stop_boxed_4237_ = lean_unbox_usize(v_stop_4232_);
lean_dec(v_stop_4232_);
v_res_4238_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0(v_as_4230_, v_i_boxed_4236_, v_stop_boxed_4237_, v_b_4233_, v___y_4234_);
lean_dec_ref(v___y_4234_);
lean_dec_ref(v_as_4230_);
return v_res_4238_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_addAttrEntry(lean_object* v_s_4239_, lean_object* v_e_4240_){
_start:
{
lean_object* v_snd_4241_; lean_object* v_toAttributeImplCore_4242_; lean_object* v_fst_4243_; lean_object* v___x_4245_; uint8_t v_isShared_4246_; uint8_t v_isSharedCheck_4261_; 
v_snd_4241_ = lean_ctor_get(v_e_4240_, 1);
lean_inc(v_snd_4241_);
v_toAttributeImplCore_4242_ = lean_ctor_get(v_snd_4241_, 0);
v_fst_4243_ = lean_ctor_get(v_e_4240_, 0);
v_isSharedCheck_4261_ = !lean_is_exclusive(v_e_4240_);
if (v_isSharedCheck_4261_ == 0)
{
lean_object* v_unused_4262_; 
v_unused_4262_ = lean_ctor_get(v_e_4240_, 1);
lean_dec(v_unused_4262_);
v___x_4245_ = v_e_4240_;
v_isShared_4246_ = v_isSharedCheck_4261_;
goto v_resetjp_4244_;
}
else
{
lean_inc(v_fst_4243_);
lean_dec(v_e_4240_);
v___x_4245_ = lean_box(0);
v_isShared_4246_ = v_isSharedCheck_4261_;
goto v_resetjp_4244_;
}
v_resetjp_4244_:
{
lean_object* v_newEntries_4247_; lean_object* v_map_4248_; lean_object* v___x_4250_; uint8_t v_isShared_4251_; uint8_t v_isSharedCheck_4260_; 
v_newEntries_4247_ = lean_ctor_get(v_s_4239_, 0);
v_map_4248_ = lean_ctor_get(v_s_4239_, 1);
v_isSharedCheck_4260_ = !lean_is_exclusive(v_s_4239_);
if (v_isSharedCheck_4260_ == 0)
{
v___x_4250_ = v_s_4239_;
v_isShared_4251_ = v_isSharedCheck_4260_;
goto v_resetjp_4249_;
}
else
{
lean_inc(v_map_4248_);
lean_inc(v_newEntries_4247_);
lean_dec(v_s_4239_);
v___x_4250_ = lean_box(0);
v_isShared_4251_ = v_isSharedCheck_4260_;
goto v_resetjp_4249_;
}
v_resetjp_4249_:
{
lean_object* v_name_4252_; lean_object* v___x_4254_; 
v_name_4252_ = lean_ctor_get(v_toAttributeImplCore_4242_, 1);
lean_inc(v_name_4252_);
if (v_isShared_4246_ == 0)
{
lean_ctor_set_tag(v___x_4245_, 1);
lean_ctor_set(v___x_4245_, 1, v_newEntries_4247_);
v___x_4254_ = v___x_4245_;
goto v_reusejp_4253_;
}
else
{
lean_object* v_reuseFailAlloc_4259_; 
v_reuseFailAlloc_4259_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4259_, 0, v_fst_4243_);
lean_ctor_set(v_reuseFailAlloc_4259_, 1, v_newEntries_4247_);
v___x_4254_ = v_reuseFailAlloc_4259_;
goto v_reusejp_4253_;
}
v_reusejp_4253_:
{
lean_object* v___x_4255_; lean_object* v___x_4257_; 
v___x_4255_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1___redArg(v_map_4248_, v_name_4252_, v_snd_4241_);
if (v_isShared_4251_ == 0)
{
lean_ctor_set(v___x_4250_, 1, v___x_4255_);
lean_ctor_set(v___x_4250_, 0, v___x_4254_);
v___x_4257_ = v___x_4250_;
goto v_reusejp_4256_;
}
else
{
lean_object* v_reuseFailAlloc_4258_; 
v_reuseFailAlloc_4258_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4258_, 0, v___x_4254_);
lean_ctor_set(v_reuseFailAlloc_4258_, 1, v___x_4255_);
v___x_4257_ = v_reuseFailAlloc_4258_;
goto v_reusejp_4256_;
}
v_reusejp_4256_:
{
return v___x_4257_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn___lam__0_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(lean_object* v_x_4263_, lean_object* v_s_4264_){
_start:
{
lean_object* v_newEntries_4265_; lean_object* v___x_4266_; lean_object* v___x_4267_; lean_object* v___x_4268_; 
v_newEntries_4265_ = lean_ctor_get(v_s_4264_, 0);
lean_inc(v_newEntries_4265_);
lean_dec_ref(v_s_4264_);
v___x_4266_ = l_List_reverse___redArg(v_newEntries_4265_);
v___x_4267_ = lean_array_mk(v___x_4266_);
lean_inc_ref_n(v___x_4267_, 2);
v___x_4268_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4268_, 0, v___x_4267_);
lean_ctor_set(v___x_4268_, 1, v___x_4267_);
lean_ctor_set(v___x_4268_, 2, v___x_4267_);
return v___x_4268_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn___lam__0_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2____boxed(lean_object* v_x_4269_, lean_object* v_s_4270_){
_start:
{
lean_object* v_res_4271_; 
v_res_4271_ = l___private_Lean_Attributes_0__Lean_initFn___lam__0_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(v_x_4269_, v_s_4270_);
lean_dec_ref(v_x_4269_);
return v_res_4271_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn___lam__1_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(lean_object* v_s_4272_){
_start:
{
lean_object* v_newEntries_4273_; lean_object* v___x_4275_; uint8_t v_isShared_4276_; uint8_t v_isSharedCheck_4284_; 
v_newEntries_4273_ = lean_ctor_get(v_s_4272_, 0);
v_isSharedCheck_4284_ = !lean_is_exclusive(v_s_4272_);
if (v_isSharedCheck_4284_ == 0)
{
lean_object* v_unused_4285_; 
v_unused_4285_ = lean_ctor_get(v_s_4272_, 1);
lean_dec(v_unused_4285_);
v___x_4275_ = v_s_4272_;
v_isShared_4276_ = v_isSharedCheck_4284_;
goto v_resetjp_4274_;
}
else
{
lean_inc(v_newEntries_4273_);
lean_dec(v_s_4272_);
v___x_4275_ = lean_box(0);
v_isShared_4276_ = v_isSharedCheck_4284_;
goto v_resetjp_4274_;
}
v_resetjp_4274_:
{
lean_object* v___x_4277_; lean_object* v___x_4278_; lean_object* v___x_4279_; lean_object* v___x_4280_; lean_object* v___x_4282_; 
v___x_4277_ = ((lean_object*)(l_Lean_registerTagAttribute___lam__2___closed__4));
v___x_4278_ = l_List_lengthTR___redArg(v_newEntries_4273_);
lean_dec(v_newEntries_4273_);
v___x_4279_ = l_Nat_reprFast(v___x_4278_);
v___x_4280_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4280_, 0, v___x_4279_);
if (v_isShared_4276_ == 0)
{
lean_ctor_set_tag(v___x_4275_, 5);
lean_ctor_set(v___x_4275_, 1, v___x_4280_);
lean_ctor_set(v___x_4275_, 0, v___x_4277_);
v___x_4282_ = v___x_4275_;
goto v_reusejp_4281_;
}
else
{
lean_object* v_reuseFailAlloc_4283_; 
v_reuseFailAlloc_4283_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4283_, 0, v___x_4277_);
lean_ctor_set(v_reuseFailAlloc_4283_, 1, v___x_4280_);
v___x_4282_ = v_reuseFailAlloc_4283_;
goto v_reusejp_4281_;
}
v_reusejp_4281_:
{
return v___x_4282_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn___lam__2_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(lean_object* v_s_4286_){
_start:
{
lean_object* v_newEntries_4287_; lean_object* v___x_4288_; lean_object* v___x_4289_; 
v_newEntries_4287_ = lean_ctor_get(v_s_4286_, 0);
lean_inc(v_newEntries_4287_);
lean_dec_ref(v_s_4286_);
v___x_4288_ = l_List_reverse___redArg(v_newEntries_4287_);
v___x_4289_ = lean_array_mk(v___x_4288_);
return v___x_4289_;
}
}
static lean_object* _init_l___private_Lean_Attributes_0__Lean_initFn___closed__7_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(void){
_start:
{
uint8_t v___x_4299_; lean_object* v___x_4300_; lean_object* v___x_4301_; lean_object* v___f_4302_; lean_object* v___f_4303_; lean_object* v___x_4304_; lean_object* v___x_4305_; lean_object* v___x_4306_; lean_object* v___x_4307_; lean_object* v___x_4308_; 
v___x_4299_ = 0;
v___x_4300_ = lean_box(0);
v___x_4301_ = lean_box(2);
v___f_4302_ = ((lean_object*)(l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___f_4303_ = ((lean_object*)(l___private_Lean_Attributes_0__Lean_initFn___closed__0_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___x_4304_ = ((lean_object*)(l___private_Lean_Attributes_0__Lean_initFn___closed__6_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___x_4305_ = ((lean_object*)(l___private_Lean_Attributes_0__Lean_initFn___closed__5_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___x_4306_ = lean_alloc_closure((void*)(l___private_Lean_Attributes_0__Lean_AttributeExtension_mkInitial___boxed), 1, 0);
v___x_4307_ = ((lean_object*)(l___private_Lean_Attributes_0__Lean_initFn___closed__4_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___x_4308_ = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(v___x_4308_, 0, v___x_4307_);
lean_ctor_set(v___x_4308_, 1, v___x_4306_);
lean_ctor_set(v___x_4308_, 2, v___x_4305_);
lean_ctor_set(v___x_4308_, 3, v___x_4304_);
lean_ctor_set(v___x_4308_, 4, v___f_4303_);
lean_ctor_set(v___x_4308_, 5, v___f_4302_);
lean_ctor_set(v___x_4308_, 6, v___x_4301_);
lean_ctor_set(v___x_4308_, 7, v___x_4300_);
lean_ctor_set_uint8(v___x_4308_, sizeof(void*)*8, v___x_4299_);
lean_ctor_set_uint8(v___x_4308_, sizeof(void*)*8 + 1, v___x_4299_);
return v___x_4308_;
}
}
static lean_object* _init_l___private_Lean_Attributes_0__Lean_initFn___closed__8_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_4309_; lean_object* v___x_4310_; lean_object* v___x_4311_; 
v___f_4309_ = ((lean_object*)(l___private_Lean_Attributes_0__Lean_initFn___closed__2_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___x_4310_ = lean_obj_once(&l___private_Lean_Attributes_0__Lean_initFn___closed__7_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_, &l___private_Lean_Attributes_0__Lean_initFn___closed__7_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2__once, _init_l___private_Lean_Attributes_0__Lean_initFn___closed__7_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_);
v___x_4311_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4311_, 0, v___x_4310_);
lean_ctor_set(v___x_4311_, 1, v___f_4309_);
return v___x_4311_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4313_; lean_object* v___x_4314_; 
v___x_4313_ = lean_obj_once(&l___private_Lean_Attributes_0__Lean_initFn___closed__8_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_, &l___private_Lean_Attributes_0__Lean_initFn___closed__8_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2__once, _init_l___private_Lean_Attributes_0__Lean_initFn___closed__8_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_);
v___x_4314_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_4313_);
return v___x_4314_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2____boxed(lean_object* v_a_4315_){
_start:
{
lean_object* v_res_4316_; 
v_res_4316_ = l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_();
return v_res_4316_;
}
}
LEAN_EXPORT lean_object* l_Lean_isBuiltinAttribute(lean_object* v_n_4317_){
_start:
{
lean_object* v___x_4319_; lean_object* v___x_4320_; uint8_t v___x_4321_; lean_object* v___x_4322_; lean_object* v___x_4323_; 
v___x_4319_ = l_Lean_attributeMapRef;
v___x_4320_ = lean_st_ref_get(v___x_4319_);
v___x_4321_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(v___x_4320_, v_n_4317_);
lean_dec(v___x_4320_);
v___x_4322_ = lean_box(v___x_4321_);
v___x_4323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4323_, 0, v___x_4322_);
return v___x_4323_;
}
}
LEAN_EXPORT lean_object* l_Lean_isBuiltinAttribute___boxed(lean_object* v_n_4324_, lean_object* v_a_4325_){
_start:
{
lean_object* v_res_4326_; 
v_res_4326_ = l_Lean_isBuiltinAttribute(v_n_4324_);
lean_dec(v_n_4324_);
return v_res_4326_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_getBuiltinAttributeNames_spec__0(lean_object* v_x_4327_, lean_object* v_x_4328_){
_start:
{
if (lean_obj_tag(v_x_4328_) == 0)
{
return v_x_4327_;
}
else
{
lean_object* v_key_4329_; lean_object* v_tail_4330_; lean_object* v___x_4331_; 
v_key_4329_ = lean_ctor_get(v_x_4328_, 0);
v_tail_4330_ = lean_ctor_get(v_x_4328_, 2);
lean_inc(v_key_4329_);
v___x_4331_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4331_, 0, v_key_4329_);
lean_ctor_set(v___x_4331_, 1, v_x_4327_);
v_x_4327_ = v___x_4331_;
v_x_4328_ = v_tail_4330_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_getBuiltinAttributeNames_spec__0___boxed(lean_object* v_x_4333_, lean_object* v_x_4334_){
_start:
{
lean_object* v_res_4335_; 
v_res_4335_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_getBuiltinAttributeNames_spec__0(v_x_4333_, v_x_4334_);
lean_dec(v_x_4334_);
return v_res_4335_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1(lean_object* v_as_4336_, size_t v_i_4337_, size_t v_stop_4338_, lean_object* v_b_4339_){
_start:
{
uint8_t v___x_4340_; 
v___x_4340_ = lean_usize_dec_eq(v_i_4337_, v_stop_4338_);
if (v___x_4340_ == 0)
{
lean_object* v___x_4341_; lean_object* v___x_4342_; size_t v___x_4343_; size_t v___x_4344_; 
v___x_4341_ = lean_array_uget_borrowed(v_as_4336_, v_i_4337_);
v___x_4342_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_getBuiltinAttributeNames_spec__0(v_b_4339_, v___x_4341_);
v___x_4343_ = ((size_t)1ULL);
v___x_4344_ = lean_usize_add(v_i_4337_, v___x_4343_);
v_i_4337_ = v___x_4344_;
v_b_4339_ = v___x_4342_;
goto _start;
}
else
{
return v_b_4339_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1___boxed(lean_object* v_as_4346_, lean_object* v_i_4347_, lean_object* v_stop_4348_, lean_object* v_b_4349_){
_start:
{
size_t v_i_boxed_4350_; size_t v_stop_boxed_4351_; lean_object* v_res_4352_; 
v_i_boxed_4350_ = lean_unbox_usize(v_i_4347_);
lean_dec(v_i_4347_);
v_stop_boxed_4351_ = lean_unbox_usize(v_stop_4348_);
lean_dec(v_stop_4348_);
v_res_4352_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1(v_as_4346_, v_i_boxed_4350_, v_stop_boxed_4351_, v_b_4349_);
lean_dec_ref(v_as_4346_);
return v_res_4352_;
}
}
LEAN_EXPORT lean_object* l_Lean_getBuiltinAttributeNames(){
_start:
{
lean_object* v___x_4354_; lean_object* v___x_4355_; lean_object* v_buckets_4356_; lean_object* v___x_4357_; lean_object* v___x_4358_; lean_object* v___x_4359_; uint8_t v___x_4360_; 
v___x_4354_ = l_Lean_attributeMapRef;
v___x_4355_ = lean_st_ref_get(v___x_4354_);
v_buckets_4356_ = lean_ctor_get(v___x_4355_, 1);
lean_inc_ref(v_buckets_4356_);
lean_dec(v___x_4355_);
v___x_4357_ = lean_box(0);
v___x_4358_ = lean_unsigned_to_nat(0u);
v___x_4359_ = lean_array_get_size(v_buckets_4356_);
v___x_4360_ = lean_nat_dec_lt(v___x_4358_, v___x_4359_);
if (v___x_4360_ == 0)
{
lean_object* v___x_4361_; 
lean_dec_ref(v_buckets_4356_);
v___x_4361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4361_, 0, v___x_4357_);
return v___x_4361_;
}
else
{
size_t v___x_4362_; size_t v___x_4363_; lean_object* v___x_4364_; lean_object* v___x_4365_; 
v___x_4362_ = ((size_t)0ULL);
v___x_4363_ = lean_usize_of_nat(v___x_4359_);
v___x_4364_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1(v_buckets_4356_, v___x_4362_, v___x_4363_, v___x_4357_);
lean_dec_ref(v_buckets_4356_);
v___x_4365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4365_, 0, v___x_4364_);
return v___x_4365_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getBuiltinAttributeNames___boxed(lean_object* v_a_4366_){
_start:
{
lean_object* v_res_4367_; 
v_res_4367_ = l_Lean_getBuiltinAttributeNames();
return v_res_4367_;
}
}
LEAN_EXPORT lean_object* l_Lean_getBuiltinAttributeImpl(lean_object* v_attrName_4369_){
_start:
{
lean_object* v___x_4371_; lean_object* v___x_4372_; lean_object* v___x_4373_; 
v___x_4371_ = l_Lean_attributeMapRef;
v___x_4372_ = lean_st_ref_get(v___x_4371_);
v___x_4373_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(v___x_4372_, v_attrName_4369_);
lean_dec(v___x_4372_);
if (lean_obj_tag(v___x_4373_) == 0)
{
lean_object* v___x_4374_; uint8_t v___x_4375_; lean_object* v___x_4376_; lean_object* v___x_4377_; lean_object* v___x_4378_; lean_object* v___x_4379_; lean_object* v___x_4380_; lean_object* v___x_4381_; 
v___x_4374_ = ((lean_object*)(l_Lean_getBuiltinAttributeImpl___closed__0));
v___x_4375_ = 1;
v___x_4376_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_attrName_4369_, v___x_4375_);
v___x_4377_ = lean_string_append(v___x_4374_, v___x_4376_);
lean_dec_ref(v___x_4376_);
v___x_4378_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__4));
v___x_4379_ = lean_string_append(v___x_4377_, v___x_4378_);
v___x_4380_ = lean_mk_io_user_error(v___x_4379_);
v___x_4381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4381_, 0, v___x_4380_);
return v___x_4381_;
}
else
{
lean_object* v_val_4382_; lean_object* v___x_4384_; uint8_t v_isShared_4385_; uint8_t v_isSharedCheck_4389_; 
lean_dec(v_attrName_4369_);
v_val_4382_ = lean_ctor_get(v___x_4373_, 0);
v_isSharedCheck_4389_ = !lean_is_exclusive(v___x_4373_);
if (v_isSharedCheck_4389_ == 0)
{
v___x_4384_ = v___x_4373_;
v_isShared_4385_ = v_isSharedCheck_4389_;
goto v_resetjp_4383_;
}
else
{
lean_inc(v_val_4382_);
lean_dec(v___x_4373_);
v___x_4384_ = lean_box(0);
v_isShared_4385_ = v_isSharedCheck_4389_;
goto v_resetjp_4383_;
}
v_resetjp_4383_:
{
lean_object* v___x_4387_; 
if (v_isShared_4385_ == 0)
{
lean_ctor_set_tag(v___x_4384_, 0);
v___x_4387_ = v___x_4384_;
goto v_reusejp_4386_;
}
else
{
lean_object* v_reuseFailAlloc_4388_; 
v_reuseFailAlloc_4388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4388_, 0, v_val_4382_);
v___x_4387_ = v_reuseFailAlloc_4388_;
goto v_reusejp_4386_;
}
v_reusejp_4386_:
{
return v___x_4387_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getBuiltinAttributeImpl___boxed(lean_object* v_attrName_4390_, lean_object* v_a_4391_){
_start:
{
lean_object* v_res_4392_; 
v_res_4392_ = l_Lean_getBuiltinAttributeImpl(v_attrName_4390_);
return v_res_4392_;
}
}
LEAN_EXPORT uint8_t l_Lean_isAttribute(lean_object* v_env_4393_, lean_object* v_attrName_4394_){
_start:
{
lean_object* v___x_4395_; lean_object* v_toEnvExtension_4396_; lean_object* v_asyncMode_4397_; lean_object* v___x_4398_; lean_object* v___x_4399_; uint8_t v___x_4400_; lean_object* v___x_4401_; lean_object* v_map_4402_; uint8_t v___x_4403_; 
v___x_4395_ = l_Lean_attributeExtension;
v_toEnvExtension_4396_ = lean_ctor_get(v___x_4395_, 0);
v_asyncMode_4397_ = lean_ctor_get(v_toEnvExtension_4396_, 2);
v___x_4398_ = l_Lean_instInhabitedAttributeExtensionState_default;
v___x_4399_ = lean_box(0);
v___x_4400_ = 0;
v___x_4401_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_4398_, v___x_4395_, v_env_4393_, v_asyncMode_4397_, v___x_4399_, v___x_4400_);
v_map_4402_ = lean_ctor_get(v___x_4401_, 1);
lean_inc_ref(v_map_4402_);
lean_dec(v___x_4401_);
v___x_4403_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(v_map_4402_, v_attrName_4394_);
lean_dec_ref(v_map_4402_);
return v___x_4403_;
}
}
LEAN_EXPORT lean_object* l_Lean_isAttribute___boxed(lean_object* v_env_4404_, lean_object* v_attrName_4405_){
_start:
{
uint8_t v_res_4406_; lean_object* v_r_4407_; 
v_res_4406_ = l_Lean_isAttribute(v_env_4404_, v_attrName_4405_);
lean_dec(v_attrName_4405_);
v_r_4407_ = lean_box(v_res_4406_);
return v_r_4407_;
}
}
LEAN_EXPORT lean_object* l_Lean_getAttributeNames(lean_object* v_env_4408_){
_start:
{
lean_object* v___x_4409_; lean_object* v_toEnvExtension_4410_; lean_object* v_asyncMode_4411_; lean_object* v___x_4412_; lean_object* v___x_4413_; uint8_t v___x_4414_; lean_object* v___x_4415_; lean_object* v_map_4416_; lean_object* v_buckets_4417_; lean_object* v___x_4418_; lean_object* v___x_4419_; lean_object* v___x_4420_; uint8_t v___x_4421_; 
v___x_4409_ = l_Lean_attributeExtension;
v_toEnvExtension_4410_ = lean_ctor_get(v___x_4409_, 0);
v_asyncMode_4411_ = lean_ctor_get(v_toEnvExtension_4410_, 2);
v___x_4412_ = l_Lean_instInhabitedAttributeExtensionState_default;
v___x_4413_ = lean_box(0);
v___x_4414_ = 0;
v___x_4415_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_4412_, v___x_4409_, v_env_4408_, v_asyncMode_4411_, v___x_4413_, v___x_4414_);
v_map_4416_ = lean_ctor_get(v___x_4415_, 1);
lean_inc_ref(v_map_4416_);
lean_dec(v___x_4415_);
v_buckets_4417_ = lean_ctor_get(v_map_4416_, 1);
lean_inc_ref(v_buckets_4417_);
lean_dec_ref(v_map_4416_);
v___x_4418_ = lean_box(0);
v___x_4419_ = lean_unsigned_to_nat(0u);
v___x_4420_ = lean_array_get_size(v_buckets_4417_);
v___x_4421_ = lean_nat_dec_lt(v___x_4419_, v___x_4420_);
if (v___x_4421_ == 0)
{
lean_dec_ref(v_buckets_4417_);
return v___x_4418_;
}
else
{
size_t v___x_4422_; size_t v___x_4423_; lean_object* v___x_4424_; 
v___x_4422_ = ((size_t)0ULL);
v___x_4423_ = lean_usize_of_nat(v___x_4420_);
v___x_4424_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1(v_buckets_4417_, v___x_4422_, v___x_4423_, v___x_4418_);
lean_dec_ref(v_buckets_4417_);
return v___x_4424_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getAttributeImpl(lean_object* v_env_4425_, lean_object* v_attrName_4426_){
_start:
{
lean_object* v___x_4427_; lean_object* v_toEnvExtension_4428_; lean_object* v_asyncMode_4429_; lean_object* v___x_4430_; lean_object* v___x_4431_; uint8_t v___x_4432_; lean_object* v___x_4433_; lean_object* v_map_4434_; lean_object* v___x_4435_; 
v___x_4427_ = l_Lean_attributeExtension;
v_toEnvExtension_4428_ = lean_ctor_get(v___x_4427_, 0);
v_asyncMode_4429_ = lean_ctor_get(v_toEnvExtension_4428_, 2);
v___x_4430_ = l_Lean_instInhabitedAttributeExtensionState_default;
v___x_4431_ = lean_box(0);
v___x_4432_ = 0;
v___x_4433_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_4430_, v___x_4427_, v_env_4425_, v_asyncMode_4429_, v___x_4431_, v___x_4432_);
v_map_4434_ = lean_ctor_get(v___x_4433_, 1);
lean_inc_ref(v_map_4434_);
lean_dec(v___x_4433_);
v___x_4435_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(v_map_4434_, v_attrName_4426_);
lean_dec_ref(v_map_4434_);
if (lean_obj_tag(v___x_4435_) == 0)
{
lean_object* v___x_4436_; uint8_t v___x_4437_; lean_object* v___x_4438_; lean_object* v___x_4439_; lean_object* v___x_4440_; lean_object* v___x_4441_; lean_object* v___x_4442_; 
v___x_4436_ = ((lean_object*)(l_Lean_getBuiltinAttributeImpl___closed__0));
v___x_4437_ = 1;
v___x_4438_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_attrName_4426_, v___x_4437_);
v___x_4439_ = lean_string_append(v___x_4436_, v___x_4438_);
lean_dec_ref(v___x_4438_);
v___x_4440_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__4));
v___x_4441_ = lean_string_append(v___x_4439_, v___x_4440_);
v___x_4442_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4442_, 0, v___x_4441_);
return v___x_4442_;
}
else
{
lean_object* v_val_4443_; lean_object* v___x_4445_; uint8_t v_isShared_4446_; uint8_t v_isSharedCheck_4450_; 
lean_dec(v_attrName_4426_);
v_val_4443_ = lean_ctor_get(v___x_4435_, 0);
v_isSharedCheck_4450_ = !lean_is_exclusive(v___x_4435_);
if (v_isSharedCheck_4450_ == 0)
{
v___x_4445_ = v___x_4435_;
v_isShared_4446_ = v_isSharedCheck_4450_;
goto v_resetjp_4444_;
}
else
{
lean_inc(v_val_4443_);
lean_dec(v___x_4435_);
v___x_4445_ = lean_box(0);
v_isShared_4446_ = v_isSharedCheck_4450_;
goto v_resetjp_4444_;
}
v_resetjp_4444_:
{
lean_object* v___x_4448_; 
if (v_isShared_4446_ == 0)
{
v___x_4448_ = v___x_4445_;
goto v_reusejp_4447_;
}
else
{
lean_object* v_reuseFailAlloc_4449_; 
v_reuseFailAlloc_4449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4449_, 0, v_val_4443_);
v___x_4448_ = v_reuseFailAlloc_4449_;
goto v_reusejp_4447_;
}
v_reusejp_4447_:
{
return v___x_4448_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerAttributeOfBuilder___lam__0(lean_object* v___x_4451_, lean_object* v___x_4452_, lean_object* v_s_4453_){
_start:
{
lean_object* v_addEntryFn_4454_; lean_object* v_importedEntries_4455_; lean_object* v_state_4456_; lean_object* v___x_4458_; uint8_t v_isShared_4459_; uint8_t v_isSharedCheck_4464_; 
v_addEntryFn_4454_ = lean_ctor_get(v___x_4451_, 3);
lean_inc(v_addEntryFn_4454_);
lean_dec_ref(v___x_4451_);
v_importedEntries_4455_ = lean_ctor_get(v_s_4453_, 0);
v_state_4456_ = lean_ctor_get(v_s_4453_, 1);
v_isSharedCheck_4464_ = !lean_is_exclusive(v_s_4453_);
if (v_isSharedCheck_4464_ == 0)
{
v___x_4458_ = v_s_4453_;
v_isShared_4459_ = v_isSharedCheck_4464_;
goto v_resetjp_4457_;
}
else
{
lean_inc(v_state_4456_);
lean_inc(v_importedEntries_4455_);
lean_dec(v_s_4453_);
v___x_4458_ = lean_box(0);
v_isShared_4459_ = v_isSharedCheck_4464_;
goto v_resetjp_4457_;
}
v_resetjp_4457_:
{
lean_object* v_state_4460_; lean_object* v___x_4462_; 
v_state_4460_ = lean_apply_2(v_addEntryFn_4454_, v_state_4456_, v___x_4452_);
if (v_isShared_4459_ == 0)
{
lean_ctor_set(v___x_4458_, 1, v_state_4460_);
v___x_4462_ = v___x_4458_;
goto v_reusejp_4461_;
}
else
{
lean_object* v_reuseFailAlloc_4463_; 
v_reuseFailAlloc_4463_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4463_, 0, v_importedEntries_4455_);
lean_ctor_set(v_reuseFailAlloc_4463_, 1, v_state_4460_);
v___x_4462_ = v_reuseFailAlloc_4463_;
goto v_reusejp_4461_;
}
v_reusejp_4461_:
{
return v___x_4462_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerAttributeOfBuilder(lean_object* v_env_4465_, lean_object* v_builderId_4466_, lean_object* v_ref_4467_, lean_object* v_args_4468_){
_start:
{
lean_object* v_entry_4470_; lean_object* v___x_4471_; 
v_entry_4470_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_entry_4470_, 0, v_builderId_4466_);
lean_ctor_set(v_entry_4470_, 1, v_ref_4467_);
lean_ctor_set(v_entry_4470_, 2, v_args_4468_);
lean_inc_ref(v_entry_4470_);
v___x_4471_ = l_Lean_mkAttributeImplOfEntry(v_entry_4470_);
if (lean_obj_tag(v___x_4471_) == 0)
{
lean_object* v_a_4472_; lean_object* v___x_4474_; uint8_t v_isShared_4475_; uint8_t v_isSharedCheck_4505_; 
v_a_4472_ = lean_ctor_get(v___x_4471_, 0);
v_isSharedCheck_4505_ = !lean_is_exclusive(v___x_4471_);
if (v_isSharedCheck_4505_ == 0)
{
v___x_4474_ = v___x_4471_;
v_isShared_4475_ = v_isSharedCheck_4505_;
goto v_resetjp_4473_;
}
else
{
lean_inc(v_a_4472_);
lean_dec(v___x_4471_);
v___x_4474_ = lean_box(0);
v_isShared_4475_ = v_isSharedCheck_4505_;
goto v_resetjp_4473_;
}
v_resetjp_4473_:
{
lean_object* v_toAttributeImplCore_4476_; lean_object* v_name_4477_; uint8_t v___x_4478_; 
v_toAttributeImplCore_4476_ = lean_ctor_get(v_a_4472_, 0);
v_name_4477_ = lean_ctor_get(v_toAttributeImplCore_4476_, 1);
lean_inc_ref(v_env_4465_);
v___x_4478_ = l_Lean_isAttribute(v_env_4465_, v_name_4477_);
if (v___x_4478_ == 0)
{
lean_object* v___x_4479_; lean_object* v_toEnvExtension_4480_; lean_object* v_asyncMode_4481_; uint8_t v_logWrites_4482_; lean_object* v___x_4483_; lean_object* v___f_4484_; lean_object* v___x_4485_; uint8_t v___x_4486_; 
v___x_4479_ = l_Lean_attributeExtension;
v_toEnvExtension_4480_ = lean_ctor_get(v___x_4479_, 0);
v_asyncMode_4481_ = lean_ctor_get(v_toEnvExtension_4480_, 2);
v_logWrites_4482_ = lean_ctor_get_uint8(v_toEnvExtension_4480_, sizeof(void*)*6);
v___x_4483_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4483_, 0, v_entry_4470_);
lean_ctor_set(v___x_4483_, 1, v_a_4472_);
v___f_4484_ = lean_alloc_closure((void*)(l_Lean_registerAttributeOfBuilder___lam__0), 3, 2);
lean_closure_set(v___f_4484_, 0, v___x_4479_);
lean_closure_set(v___f_4484_, 1, v___x_4483_);
v___x_4485_ = lean_box(0);
v___x_4486_ = 1;
if (v_logWrites_4482_ == 0)
{
lean_object* v___x_4487_; lean_object* v___x_4489_; 
lean_inc_ref(v_toEnvExtension_4480_);
v___x_4487_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_4480_, v_env_4465_, v___f_4484_, v_asyncMode_4481_, v___x_4485_, v___x_4486_);
if (v_isShared_4475_ == 0)
{
lean_ctor_set(v___x_4474_, 0, v___x_4487_);
v___x_4489_ = v___x_4474_;
goto v_reusejp_4488_;
}
else
{
lean_object* v_reuseFailAlloc_4490_; 
v_reuseFailAlloc_4490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4490_, 0, v___x_4487_);
v___x_4489_ = v_reuseFailAlloc_4490_;
goto v_reusejp_4488_;
}
v_reusejp_4488_:
{
return v___x_4489_;
}
}
else
{
lean_object* v___x_4491_; lean_object* v___x_4492_; lean_object* v___x_4494_; 
lean_inc_ref_n(v_toEnvExtension_4480_, 2);
v___x_4491_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_4480_, v_env_4465_);
lean_dec_ref(v_env_4465_);
v___x_4492_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_4480_, v___x_4491_, v___f_4484_, v_asyncMode_4481_, v___x_4485_, v___x_4486_);
if (v_isShared_4475_ == 0)
{
lean_ctor_set(v___x_4474_, 0, v___x_4492_);
v___x_4494_ = v___x_4474_;
goto v_reusejp_4493_;
}
else
{
lean_object* v_reuseFailAlloc_4495_; 
v_reuseFailAlloc_4495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4495_, 0, v___x_4492_);
v___x_4494_ = v_reuseFailAlloc_4495_;
goto v_reusejp_4493_;
}
v_reusejp_4493_:
{
return v___x_4494_;
}
}
}
else
{
lean_object* v___x_4496_; lean_object* v___x_4497_; lean_object* v___x_4498_; lean_object* v___x_4499_; lean_object* v___x_4500_; lean_object* v___x_4501_; lean_object* v___x_4503_; 
lean_inc(v_name_4477_);
lean_dec(v_a_4472_);
lean_dec_ref_known(v_entry_4470_, 3);
lean_dec_ref(v_env_4465_);
v___x_4496_ = ((lean_object*)(l_Lean_registerBuiltinAttribute___closed__2));
v___x_4497_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_4477_, v___x_4478_);
v___x_4498_ = lean_string_append(v___x_4496_, v___x_4497_);
lean_dec_ref(v___x_4497_);
v___x_4499_ = ((lean_object*)(l_Lean_registerBuiltinAttribute___closed__3));
v___x_4500_ = lean_string_append(v___x_4498_, v___x_4499_);
v___x_4501_ = lean_mk_io_user_error(v___x_4500_);
if (v_isShared_4475_ == 0)
{
lean_ctor_set_tag(v___x_4474_, 1);
lean_ctor_set(v___x_4474_, 0, v___x_4501_);
v___x_4503_ = v___x_4474_;
goto v_reusejp_4502_;
}
else
{
lean_object* v_reuseFailAlloc_4504_; 
v_reuseFailAlloc_4504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4504_, 0, v___x_4501_);
v___x_4503_ = v_reuseFailAlloc_4504_;
goto v_reusejp_4502_;
}
v_reusejp_4502_:
{
return v___x_4503_;
}
}
}
}
else
{
lean_object* v_a_4506_; lean_object* v___x_4508_; uint8_t v_isShared_4509_; uint8_t v_isSharedCheck_4513_; 
lean_dec_ref_known(v_entry_4470_, 3);
lean_dec_ref(v_env_4465_);
v_a_4506_ = lean_ctor_get(v___x_4471_, 0);
v_isSharedCheck_4513_ = !lean_is_exclusive(v___x_4471_);
if (v_isSharedCheck_4513_ == 0)
{
v___x_4508_ = v___x_4471_;
v_isShared_4509_ = v_isSharedCheck_4513_;
goto v_resetjp_4507_;
}
else
{
lean_inc(v_a_4506_);
lean_dec(v___x_4471_);
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
LEAN_EXPORT lean_object* l_Lean_registerAttributeOfBuilder___boxed(lean_object* v_env_4514_, lean_object* v_builderId_4515_, lean_object* v_ref_4516_, lean_object* v_args_4517_, lean_object* v_a_4518_){
_start:
{
lean_object* v_res_4519_; 
v_res_4519_ = l_Lean_registerAttributeOfBuilder(v_env_4514_, v_builderId_4515_, v_ref_4516_, v_args_4517_);
return v_res_4519_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg(lean_object* v_x_4520_, lean_object* v___y_4521_, lean_object* v___y_4522_){
_start:
{
if (lean_obj_tag(v_x_4520_) == 0)
{
lean_object* v_a_4524_; lean_object* v___x_4525_; lean_object* v___x_4526_; 
v_a_4524_ = lean_ctor_get(v_x_4520_, 0);
lean_inc(v_a_4524_);
lean_dec_ref_known(v_x_4520_, 1);
v___x_4525_ = l_Lean_stringToMessageData(v_a_4524_);
v___x_4526_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_4525_, v___y_4521_, v___y_4522_);
return v___x_4526_;
}
else
{
lean_object* v_a_4527_; lean_object* v___x_4529_; uint8_t v_isShared_4530_; uint8_t v_isSharedCheck_4534_; 
v_a_4527_ = lean_ctor_get(v_x_4520_, 0);
v_isSharedCheck_4534_ = !lean_is_exclusive(v_x_4520_);
if (v_isSharedCheck_4534_ == 0)
{
v___x_4529_ = v_x_4520_;
v_isShared_4530_ = v_isSharedCheck_4534_;
goto v_resetjp_4528_;
}
else
{
lean_inc(v_a_4527_);
lean_dec(v_x_4520_);
v___x_4529_ = lean_box(0);
v_isShared_4530_ = v_isSharedCheck_4534_;
goto v_resetjp_4528_;
}
v_resetjp_4528_:
{
lean_object* v___x_4532_; 
if (v_isShared_4530_ == 0)
{
lean_ctor_set_tag(v___x_4529_, 0);
v___x_4532_ = v___x_4529_;
goto v_reusejp_4531_;
}
else
{
lean_object* v_reuseFailAlloc_4533_; 
v_reuseFailAlloc_4533_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4533_, 0, v_a_4527_);
v___x_4532_ = v_reuseFailAlloc_4533_;
goto v_reusejp_4531_;
}
v_reusejp_4531_:
{
return v___x_4532_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg___boxed(lean_object* v_x_4535_, lean_object* v___y_4536_, lean_object* v___y_4537_, lean_object* v___y_4538_){
_start:
{
lean_object* v_res_4539_; 
v_res_4539_ = l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg(v_x_4535_, v___y_4536_, v___y_4537_);
lean_dec(v___y_4537_);
lean_dec_ref(v___y_4536_);
return v_res_4539_;
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_add(lean_object* v_declName_4540_, lean_object* v_attrName_4541_, lean_object* v_stx_4542_, uint8_t v_kind_4543_, lean_object* v_a_4544_, lean_object* v_a_4545_){
_start:
{
lean_object* v___x_4547_; lean_object* v_env_4548_; lean_object* v___x_4549_; lean_object* v___x_4550_; 
v___x_4547_ = lean_st_ref_get(v_a_4545_);
v_env_4548_ = lean_ctor_get(v___x_4547_, 0);
lean_inc_ref(v_env_4548_);
lean_dec(v___x_4547_);
v___x_4549_ = l_Lean_getAttributeImpl(v_env_4548_, v_attrName_4541_);
v___x_4550_ = l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg(v___x_4549_, v_a_4544_, v_a_4545_);
if (lean_obj_tag(v___x_4550_) == 0)
{
lean_object* v_a_4551_; lean_object* v_add_4552_; lean_object* v___x_4553_; lean_object* v___x_4554_; 
v_a_4551_ = lean_ctor_get(v___x_4550_, 0);
lean_inc(v_a_4551_);
lean_dec_ref_known(v___x_4550_, 1);
v_add_4552_ = lean_ctor_get(v_a_4551_, 1);
lean_inc_ref(v_add_4552_);
lean_dec(v_a_4551_);
v___x_4553_ = lean_box(v_kind_4543_);
lean_inc(v_a_4545_);
lean_inc_ref(v_a_4544_);
v___x_4554_ = lean_apply_6(v_add_4552_, v_declName_4540_, v_stx_4542_, v___x_4553_, v_a_4544_, v_a_4545_, lean_box(0));
return v___x_4554_;
}
else
{
lean_object* v_a_4555_; lean_object* v___x_4557_; uint8_t v_isShared_4558_; uint8_t v_isSharedCheck_4562_; 
lean_dec(v_stx_4542_);
lean_dec(v_declName_4540_);
v_a_4555_ = lean_ctor_get(v___x_4550_, 0);
v_isSharedCheck_4562_ = !lean_is_exclusive(v___x_4550_);
if (v_isSharedCheck_4562_ == 0)
{
v___x_4557_ = v___x_4550_;
v_isShared_4558_ = v_isSharedCheck_4562_;
goto v_resetjp_4556_;
}
else
{
lean_inc(v_a_4555_);
lean_dec(v___x_4550_);
v___x_4557_ = lean_box(0);
v_isShared_4558_ = v_isSharedCheck_4562_;
goto v_resetjp_4556_;
}
v_resetjp_4556_:
{
lean_object* v___x_4560_; 
if (v_isShared_4558_ == 0)
{
v___x_4560_ = v___x_4557_;
goto v_reusejp_4559_;
}
else
{
lean_object* v_reuseFailAlloc_4561_; 
v_reuseFailAlloc_4561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4561_, 0, v_a_4555_);
v___x_4560_ = v_reuseFailAlloc_4561_;
goto v_reusejp_4559_;
}
v_reusejp_4559_:
{
return v___x_4560_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_add___boxed(lean_object* v_declName_4563_, lean_object* v_attrName_4564_, lean_object* v_stx_4565_, lean_object* v_kind_4566_, lean_object* v_a_4567_, lean_object* v_a_4568_, lean_object* v_a_4569_){
_start:
{
uint8_t v_kind_boxed_4570_; lean_object* v_res_4571_; 
v_kind_boxed_4570_ = lean_unbox(v_kind_4566_);
v_res_4571_ = l_Lean_Attribute_add(v_declName_4563_, v_attrName_4564_, v_stx_4565_, v_kind_boxed_4570_, v_a_4567_, v_a_4568_);
lean_dec(v_a_4568_);
lean_dec_ref(v_a_4567_);
return v_res_4571_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0(lean_object* v_00_u03b1_4572_, lean_object* v_x_4573_, lean_object* v___y_4574_, lean_object* v___y_4575_){
_start:
{
lean_object* v___x_4577_; 
v___x_4577_ = l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg(v_x_4573_, v___y_4574_, v___y_4575_);
return v___x_4577_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___boxed(lean_object* v_00_u03b1_4578_, lean_object* v_x_4579_, lean_object* v___y_4580_, lean_object* v___y_4581_, lean_object* v___y_4582_){
_start:
{
lean_object* v_res_4583_; 
v_res_4583_ = l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0(v_00_u03b1_4578_, v_x_4579_, v___y_4580_, v___y_4581_);
lean_dec(v___y_4581_);
lean_dec_ref(v___y_4580_);
return v_res_4583_;
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_erase(lean_object* v_declName_4584_, lean_object* v_attrName_4585_, lean_object* v_a_4586_, lean_object* v_a_4587_){
_start:
{
lean_object* v___x_4589_; lean_object* v_env_4590_; lean_object* v___x_4591_; lean_object* v___x_4592_; 
v___x_4589_ = lean_st_ref_get(v_a_4587_);
v_env_4590_ = lean_ctor_get(v___x_4589_, 0);
lean_inc_ref(v_env_4590_);
lean_dec(v___x_4589_);
v___x_4591_ = l_Lean_getAttributeImpl(v_env_4590_, v_attrName_4585_);
v___x_4592_ = l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg(v___x_4591_, v_a_4586_, v_a_4587_);
if (lean_obj_tag(v___x_4592_) == 0)
{
lean_object* v_a_4593_; lean_object* v_erase_4594_; lean_object* v___x_4595_; 
v_a_4593_ = lean_ctor_get(v___x_4592_, 0);
lean_inc(v_a_4593_);
lean_dec_ref_known(v___x_4592_, 1);
v_erase_4594_ = lean_ctor_get(v_a_4593_, 2);
lean_inc_ref(v_erase_4594_);
lean_dec(v_a_4593_);
lean_inc(v_a_4587_);
lean_inc_ref(v_a_4586_);
v___x_4595_ = lean_apply_4(v_erase_4594_, v_declName_4584_, v_a_4586_, v_a_4587_, lean_box(0));
return v___x_4595_;
}
else
{
lean_object* v_a_4596_; lean_object* v___x_4598_; uint8_t v_isShared_4599_; uint8_t v_isSharedCheck_4603_; 
lean_dec(v_declName_4584_);
v_a_4596_ = lean_ctor_get(v___x_4592_, 0);
v_isSharedCheck_4603_ = !lean_is_exclusive(v___x_4592_);
if (v_isSharedCheck_4603_ == 0)
{
v___x_4598_ = v___x_4592_;
v_isShared_4599_ = v_isSharedCheck_4603_;
goto v_resetjp_4597_;
}
else
{
lean_inc(v_a_4596_);
lean_dec(v___x_4592_);
v___x_4598_ = lean_box(0);
v_isShared_4599_ = v_isSharedCheck_4603_;
goto v_resetjp_4597_;
}
v_resetjp_4597_:
{
lean_object* v___x_4601_; 
if (v_isShared_4599_ == 0)
{
v___x_4601_ = v___x_4598_;
goto v_reusejp_4600_;
}
else
{
lean_object* v_reuseFailAlloc_4602_; 
v_reuseFailAlloc_4602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4602_, 0, v_a_4596_);
v___x_4601_ = v_reuseFailAlloc_4602_;
goto v_reusejp_4600_;
}
v_reusejp_4600_:
{
return v___x_4601_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_erase___boxed(lean_object* v_declName_4604_, lean_object* v_attrName_4605_, lean_object* v_a_4606_, lean_object* v_a_4607_, lean_object* v_a_4608_){
_start:
{
lean_object* v_res_4609_; 
v_res_4609_ = l_Lean_Attribute_erase(v_declName_4604_, v_attrName_4605_, v_a_4606_, v_a_4607_);
lean_dec(v_a_4607_);
lean_dec_ref(v_a_4606_);
return v_res_4609_;
}
}
LEAN_EXPORT lean_object* l_Lean_updateEnvAttributesImpl___lam__0(lean_object* v___y_4610_, lean_object* v_ps_4611_){
_start:
{
lean_object* v_importedEntries_4612_; lean_object* v___x_4614_; uint8_t v_isShared_4615_; uint8_t v_isSharedCheck_4619_; 
v_importedEntries_4612_ = lean_ctor_get(v_ps_4611_, 0);
v_isSharedCheck_4619_ = !lean_is_exclusive(v_ps_4611_);
if (v_isSharedCheck_4619_ == 0)
{
lean_object* v_unused_4620_; 
v_unused_4620_ = lean_ctor_get(v_ps_4611_, 1);
lean_dec(v_unused_4620_);
v___x_4614_ = v_ps_4611_;
v_isShared_4615_ = v_isSharedCheck_4619_;
goto v_resetjp_4613_;
}
else
{
lean_inc(v_importedEntries_4612_);
lean_dec(v_ps_4611_);
v___x_4614_ = lean_box(0);
v_isShared_4615_ = v_isSharedCheck_4619_;
goto v_resetjp_4613_;
}
v_resetjp_4613_:
{
lean_object* v___x_4617_; 
if (v_isShared_4615_ == 0)
{
lean_ctor_set(v___x_4614_, 1, v___y_4610_);
v___x_4617_ = v___x_4614_;
goto v_reusejp_4616_;
}
else
{
lean_object* v_reuseFailAlloc_4618_; 
v_reuseFailAlloc_4618_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4618_, 0, v_importedEntries_4612_);
lean_ctor_set(v_reuseFailAlloc_4618_, 1, v___y_4610_);
v___x_4617_ = v_reuseFailAlloc_4618_;
goto v_reusejp_4616_;
}
v_reusejp_4616_:
{
return v___x_4617_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_updateEnvAttributesImpl_spec__0(lean_object* v_x_4621_, lean_object* v_x_4622_){
_start:
{
if (lean_obj_tag(v_x_4622_) == 0)
{
return v_x_4621_;
}
else
{
lean_object* v_key_4623_; lean_object* v_value_4624_; lean_object* v_tail_4625_; lean_object* v_newEntries_4626_; lean_object* v_map_4627_; uint8_t v___x_4628_; 
v_key_4623_ = lean_ctor_get(v_x_4622_, 0);
lean_inc(v_key_4623_);
v_value_4624_ = lean_ctor_get(v_x_4622_, 1);
lean_inc(v_value_4624_);
v_tail_4625_ = lean_ctor_get(v_x_4622_, 2);
lean_inc(v_tail_4625_);
lean_dec_ref_known(v_x_4622_, 3);
v_newEntries_4626_ = lean_ctor_get(v_x_4621_, 0);
v_map_4627_ = lean_ctor_get(v_x_4621_, 1);
v___x_4628_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(v_map_4627_, v_key_4623_);
if (v___x_4628_ == 0)
{
lean_object* v___x_4630_; uint8_t v_isShared_4631_; uint8_t v_isSharedCheck_4637_; 
lean_inc_ref(v_map_4627_);
lean_inc(v_newEntries_4626_);
v_isSharedCheck_4637_ = !lean_is_exclusive(v_x_4621_);
if (v_isSharedCheck_4637_ == 0)
{
lean_object* v_unused_4638_; lean_object* v_unused_4639_; 
v_unused_4638_ = lean_ctor_get(v_x_4621_, 1);
lean_dec(v_unused_4638_);
v_unused_4639_ = lean_ctor_get(v_x_4621_, 0);
lean_dec(v_unused_4639_);
v___x_4630_ = v_x_4621_;
v_isShared_4631_ = v_isSharedCheck_4637_;
goto v_resetjp_4629_;
}
else
{
lean_dec(v_x_4621_);
v___x_4630_ = lean_box(0);
v_isShared_4631_ = v_isSharedCheck_4637_;
goto v_resetjp_4629_;
}
v_resetjp_4629_:
{
lean_object* v___x_4632_; lean_object* v___x_4634_; 
v___x_4632_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1___redArg(v_map_4627_, v_key_4623_, v_value_4624_);
if (v_isShared_4631_ == 0)
{
lean_ctor_set(v___x_4630_, 1, v___x_4632_);
v___x_4634_ = v___x_4630_;
goto v_reusejp_4633_;
}
else
{
lean_object* v_reuseFailAlloc_4636_; 
v_reuseFailAlloc_4636_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4636_, 0, v_newEntries_4626_);
lean_ctor_set(v_reuseFailAlloc_4636_, 1, v___x_4632_);
v___x_4634_ = v_reuseFailAlloc_4636_;
goto v_reusejp_4633_;
}
v_reusejp_4633_:
{
v_x_4621_ = v___x_4634_;
v_x_4622_ = v_tail_4625_;
goto _start;
}
}
}
else
{
lean_dec(v_value_4624_);
lean_dec(v_key_4623_);
v_x_4622_ = v_tail_4625_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_updateEnvAttributesImpl_spec__1(lean_object* v_as_4641_, size_t v_i_4642_, size_t v_stop_4643_, lean_object* v_b_4644_){
_start:
{
uint8_t v___x_4645_; 
v___x_4645_ = lean_usize_dec_eq(v_i_4642_, v_stop_4643_);
if (v___x_4645_ == 0)
{
lean_object* v___x_4646_; lean_object* v___x_4647_; size_t v___x_4648_; size_t v___x_4649_; 
v___x_4646_ = lean_array_uget_borrowed(v_as_4641_, v_i_4642_);
lean_inc(v___x_4646_);
v___x_4647_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_updateEnvAttributesImpl_spec__0(v_b_4644_, v___x_4646_);
v___x_4648_ = ((size_t)1ULL);
v___x_4649_ = lean_usize_add(v_i_4642_, v___x_4648_);
v_i_4642_ = v___x_4649_;
v_b_4644_ = v___x_4647_;
goto _start;
}
else
{
return v_b_4644_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_updateEnvAttributesImpl_spec__1___boxed(lean_object* v_as_4651_, lean_object* v_i_4652_, lean_object* v_stop_4653_, lean_object* v_b_4654_){
_start:
{
size_t v_i_boxed_4655_; size_t v_stop_boxed_4656_; lean_object* v_res_4657_; 
v_i_boxed_4655_ = lean_unbox_usize(v_i_4652_);
lean_dec(v_i_4652_);
v_stop_boxed_4656_ = lean_unbox_usize(v_stop_4653_);
lean_dec(v_stop_4653_);
v_res_4657_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_updateEnvAttributesImpl_spec__1(v_as_4651_, v_i_boxed_4655_, v_stop_boxed_4656_, v_b_4654_);
lean_dec_ref(v_as_4651_);
return v_res_4657_;
}
}
LEAN_EXPORT lean_object* lean_update_env_attributes(lean_object* v_env_4658_){
_start:
{
lean_object* v___x_4660_; lean_object* v___x_4661_; lean_object* v___x_4662_; lean_object* v___x_4663_; lean_object* v___y_4665_; lean_object* v_toEnvExtension_4677_; lean_object* v_asyncMode_4678_; lean_object* v_buckets_4679_; lean_object* v___x_4680_; uint8_t v___x_4681_; lean_object* v___x_4682_; lean_object* v___x_4683_; lean_object* v___x_4684_; uint8_t v___x_4685_; 
v___x_4660_ = l_Lean_instInhabitedAttributeExtensionState_default;
v___x_4661_ = l_Lean_attributeMapRef;
v___x_4662_ = lean_st_ref_get(v___x_4661_);
v___x_4663_ = l_Lean_attributeExtension;
v_toEnvExtension_4677_ = lean_ctor_get(v___x_4663_, 0);
v_asyncMode_4678_ = lean_ctor_get(v_toEnvExtension_4677_, 2);
v_buckets_4679_ = lean_ctor_get(v___x_4662_, 1);
lean_inc_ref(v_buckets_4679_);
lean_dec(v___x_4662_);
v___x_4680_ = lean_box(0);
v___x_4681_ = 0;
lean_inc_ref(v_env_4658_);
v___x_4682_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_4660_, v___x_4663_, v_env_4658_, v_asyncMode_4678_, v___x_4680_, v___x_4681_);
v___x_4683_ = lean_unsigned_to_nat(0u);
v___x_4684_ = lean_array_get_size(v_buckets_4679_);
v___x_4685_ = lean_nat_dec_lt(v___x_4683_, v___x_4684_);
if (v___x_4685_ == 0)
{
lean_dec_ref(v_buckets_4679_);
v___y_4665_ = v___x_4682_;
goto v___jp_4664_;
}
else
{
size_t v___x_4686_; size_t v___x_4687_; lean_object* v___x_4688_; 
v___x_4686_ = ((size_t)0ULL);
v___x_4687_ = lean_usize_of_nat(v___x_4684_);
v___x_4688_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_updateEnvAttributesImpl_spec__1(v_buckets_4679_, v___x_4686_, v___x_4687_, v___x_4682_);
lean_dec_ref(v_buckets_4679_);
v___y_4665_ = v___x_4688_;
goto v___jp_4664_;
}
v___jp_4664_:
{
lean_object* v_toEnvExtension_4666_; lean_object* v_asyncMode_4667_; uint8_t v_logWrites_4668_; lean_object* v___f_4669_; lean_object* v___x_4670_; uint8_t v___x_4671_; 
v_toEnvExtension_4666_ = lean_ctor_get(v___x_4663_, 0);
v_asyncMode_4667_ = lean_ctor_get(v_toEnvExtension_4666_, 2);
v_logWrites_4668_ = lean_ctor_get_uint8(v_toEnvExtension_4666_, sizeof(void*)*6);
v___f_4669_ = lean_alloc_closure((void*)(l_Lean_updateEnvAttributesImpl___lam__0), 2, 1);
lean_closure_set(v___f_4669_, 0, v___y_4665_);
v___x_4670_ = lean_box(0);
v___x_4671_ = 1;
if (v_logWrites_4668_ == 0)
{
lean_object* v___x_4672_; lean_object* v___x_4673_; 
lean_inc_ref(v_toEnvExtension_4666_);
v___x_4672_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_4666_, v_env_4658_, v___f_4669_, v_asyncMode_4667_, v___x_4670_, v___x_4671_);
v___x_4673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4673_, 0, v___x_4672_);
return v___x_4673_;
}
else
{
lean_object* v___x_4674_; lean_object* v___x_4675_; lean_object* v___x_4676_; 
lean_inc_ref_n(v_toEnvExtension_4666_, 2);
v___x_4674_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_4666_, v_env_4658_);
lean_dec_ref(v_env_4658_);
v___x_4675_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_4666_, v___x_4674_, v___f_4669_, v_asyncMode_4667_, v___x_4670_, v___x_4671_);
v___x_4676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4676_, 0, v___x_4675_);
return v___x_4676_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_updateEnvAttributesImpl___boxed(lean_object* v_env_4689_, lean_object* v_a_4690_){
_start:
{
lean_object* v_res_4691_; 
v_res_4691_ = lean_update_env_attributes(v_env_4689_);
return v_res_4691_;
}
}
LEAN_EXPORT lean_object* lean_get_num_attributes(){
_start:
{
lean_object* v___x_4693_; lean_object* v___x_4694_; lean_object* v_size_4695_; lean_object* v___x_4696_; 
v___x_4693_ = l_Lean_attributeMapRef;
v___x_4694_ = lean_st_ref_get(v___x_4693_);
v_size_4695_ = lean_ctor_get(v___x_4694_, 0);
lean_inc(v_size_4695_);
lean_dec(v___x_4694_);
v___x_4696_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4696_, 0, v_size_4695_);
return v___x_4696_;
}
}
LEAN_EXPORT lean_object* l_Lean_getNumBuiltinAttributesImpl___boxed(lean_object* v_a_4697_){
_start:
{
lean_object* v_res_4698_; 
v_res_4698_ = lean_get_num_attributes();
return v_res_4698_;
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
