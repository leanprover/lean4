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
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
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
lean_object* l_Lean_PersistentEnvExtension_setState___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_quickLt___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t l_Lean_Name_quickLt(lean_object*, lean_object*);
lean_object* l_Array_qpartition___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_initializing();
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
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
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedMessageData_default;
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Environment_evalConst___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instInhabitedEnvExtension_default(lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_ResolveName_backward_privateInPublic_warn;
uint8_t l_Lean_isPrivateName(lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_Lean_Syntax_isNatLit_x3f(lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
uint8_t l_Lean_isMarkedMeta(lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Array_reverse___redArg(lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getModuleEntries___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_id___boxed(lean_object*, lean_object*);
lean_object* l_Array_binSearchAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_addParenHeuristic(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_toCtorIdx___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_AttributeKind_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_AttributeKind_toCtorIdx___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_instInhabitedAttributeImpl_default___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedAttributeImpl_default___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_instInhabitedAttributeImpl_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instInhabitedAttributeImpl_default___lam__0___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instInhabitedAttributeImpl_default___closed__0 = (const lean_object*)&l_Lean_instInhabitedAttributeImpl_default___closed__0_value;
static const lean_closure_object l_Lean_instInhabitedAttributeImpl_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instInhabitedAttributeImpl_default___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instInhabitedAttributeImpl_default___closed__1 = (const lean_object*)&l_Lean_instInhabitedAttributeImpl_default___closed__1_value;
static const lean_string_object l_Lean_instInhabitedAttributeImpl_default___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "instInhabitedAttributeImpl"};
static const lean_object* l_Lean_instInhabitedAttributeImpl_default___closed__2 = (const lean_object*)&l_Lean_instInhabitedAttributeImpl_default___closed__2_value;
static const lean_ctor_object l_Lean_instInhabitedAttributeImpl_default___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_instInhabitedAttributeImpl_default___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_instInhabitedAttributeImpl_default___closed__3_value_aux_0),((lean_object*)&l_Lean_instInhabitedAttributeImpl_default___closed__2_value),LEAN_SCALAR_PTR_LITERAL(233, 235, 140, 28, 184, 103, 220, 39)}};
static const lean_ctor_object l_Lean_instInhabitedAttributeImpl_default___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_instInhabitedAttributeImpl_default___closed__3_value_aux_1),((lean_object*)&l_Lean_instInhabitedAttributeImplCore_default___closed__1_value),LEAN_SCALAR_PTR_LITERAL(87, 190, 48, 39, 69, 15, 195, 198)}};
static const lean_object* l_Lean_instInhabitedAttributeImpl_default___closed__3 = (const lean_object*)&l_Lean_instInhabitedAttributeImpl_default___closed__3_value;
static const lean_ctor_object l_Lean_instInhabitedAttributeImpl_default___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 8, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_instInhabitedAttributeImpl_default___closed__3_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instInhabitedAttributeImplCore_default___closed__3_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_instInhabitedAttributeImpl_default___closed__4 = (const lean_object*)&l_Lean_instInhabitedAttributeImpl_default___closed__4_value;
static const lean_ctor_object l_Lean_instInhabitedAttributeImpl_default___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_instInhabitedAttributeImpl_default___closed__4_value),((lean_object*)&l_Lean_instInhabitedAttributeImpl_default___closed__0_value),((lean_object*)&l_Lean_instInhabitedAttributeImpl_default___closed__1_value)}};
static const lean_object* l_Lean_instInhabitedAttributeImpl_default___closed__5 = (const lean_object*)&l_Lean_instInhabitedAttributeImpl_default___closed__5_value;
LEAN_EXPORT const lean_object* l_Lean_instInhabitedAttributeImpl_default = (const lean_object*)&l_Lean_instInhabitedAttributeImpl_default___closed__5_value;
LEAN_EXPORT const lean_object* l_Lean_instInhabitedAttributeImpl = (const lean_object*)&l_Lean_instInhabitedAttributeImpl_default___closed__5_value;
static lean_once_cell_t l___private_Lean_Attributes_0__Lean_initFn___closed__0_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Attributes_0__Lean_initFn___closed__0_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_attributeMapRef;
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg___closed__0;
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
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0_spec__0_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0_spec__0_spec__1___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0_spec__0_spec__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0_spec__0_spec__1___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0_spec__0_spec__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0_spec__0_spec__1___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0_spec__0_spec__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0_spec__0_spec__1___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0_spec__0_spec__1___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0_spec__0_spec__1___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0_spec__0_spec__1___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0_spec__0_spec__1___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_closure_object l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_quickLt___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerTagAttribute_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerTagAttribute_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerTagAttribute_spec__1_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__5(lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__5___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_registerTagAttribute___lam__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Attribute `["};
static const lean_object* l_Lean_registerTagAttribute___lam__6___closed__0 = (const lean_object*)&l_Lean_registerTagAttribute___lam__6___closed__0_value;
static lean_once_cell_t l_Lean_registerTagAttribute___lam__6___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_registerTagAttribute___lam__6___closed__1;
static const lean_string_object l_Lean_registerTagAttribute___lam__6___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "]` cannot be erased"};
static const lean_object* l_Lean_registerTagAttribute___lam__6___closed__2 = (const lean_object*)&l_Lean_registerTagAttribute___lam__6___closed__2_value;
static lean_once_cell_t l_Lean_registerTagAttribute___lam__6___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_registerTagAttribute___lam__6___closed__3;
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
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_registerParametricAttribute_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_registerParametricAttribute_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_registerParametricAttribute_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_registerParametricAttribute_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3_spec__4___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttribute_spec__0___redArg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttribute_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___lam__1(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_registerParametricAttribute___redArg___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "parametric attribute"};
static const lean_object* l_Lean_registerParametricAttribute___redArg___lam__2___closed__0 = (const lean_object*)&l_Lean_registerParametricAttribute___redArg___lam__2___closed__0_value;
static const lean_ctor_object l_Lean_registerParametricAttribute___redArg___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_registerParametricAttribute___redArg___lam__2___closed__0_value)}};
static const lean_object* l_Lean_registerParametricAttribute___redArg___lam__2___closed__1 = (const lean_object*)&l_Lean_registerParametricAttribute___redArg___lam__2___closed__1_value;
static const lean_ctor_object l_Lean_registerParametricAttribute___redArg___lam__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_registerParametricAttribute___redArg___lam__2___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_registerParametricAttribute___redArg___lam__2___closed__2 = (const lean_object*)&l_Lean_registerParametricAttribute___redArg___lam__2___closed__2_value;
static const lean_ctor_object l_Lean_registerParametricAttribute___redArg___lam__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_registerParametricAttribute___redArg___lam__2___closed__2_value),((lean_object*)&l_Lean_registerTagAttribute___lam__2___closed__4_value)}};
static const lean_object* l_Lean_registerParametricAttribute___redArg___lam__2___closed__3 = (const lean_object*)&l_Lean_registerParametricAttribute___redArg___lam__2___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___lam__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___lam__3(lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___lam__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___lam__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___lam__5(lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___lam__5___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_registerParametricAttribute___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_registerParametricAttribute___redArg___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_registerParametricAttribute___redArg___closed__0 = (const lean_object*)&l_Lean_registerParametricAttribute___redArg___closed__0_value;
static const lean_closure_object l_Lean_registerParametricAttribute___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_registerParametricAttribute___redArg___lam__2, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_registerParametricAttribute___redArg___closed__1 = (const lean_object*)&l_Lean_registerParametricAttribute___redArg___closed__1_value;
static const lean_closure_object l_Lean_registerParametricAttribute___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_registerParametricAttribute___redArg___lam__3___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_registerParametricAttribute___redArg___closed__2 = (const lean_object*)&l_Lean_registerParametricAttribute___redArg___closed__2_value;
static const lean_ctor_object l_Lean_registerParametricAttribute___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_registerParametricAttribute___redArg___closed__3 = (const lean_object*)&l_Lean_registerParametricAttribute___redArg___closed__3_value;
static const lean_closure_object l_Lean_registerParametricAttribute___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_registerParametricAttribute___redArg___lam__4___boxed, .m_arity = 4, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_registerParametricAttribute___redArg___closed__3_value)} };
static const lean_object* l_Lean_registerParametricAttribute___redArg___closed__4 = (const lean_object*)&l_Lean_registerParametricAttribute___redArg___closed__4_value;
static const lean_closure_object l_Lean_registerParametricAttribute___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_registerParametricAttribute___redArg___lam__5___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_registerParametricAttribute___redArg___closed__3_value)} };
static const lean_object* l_Lean_registerParametricAttribute___redArg___closed__5 = (const lean_object*)&l_Lean_registerParametricAttribute___redArg___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttribute_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttribute_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3_spec__4(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParam_x3f___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParam_x3f___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_ParametricAttribute_getParam_x3f___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_ParametricAttribute_getParam_x3f___redArg___closed__0 = (const lean_object*)&l_Lean_ParametricAttribute_getParam_x3f___redArg___closed__0_value;
static const lean_closure_object l_Lean_ParametricAttribute_getParam_x3f___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_id___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_ParametricAttribute_getParam_x3f___redArg___closed__1 = (const lean_object*)&l_Lean_ParametricAttribute_getParam_x3f___redArg___closed__1_value;
static const lean_closure_object l_Lean_ParametricAttribute_getParam_x3f___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_ParametricAttribute_getParam_x3f___redArg___closed__2 = (const lean_object*)&l_Lean_ParametricAttribute_getParam_x3f___redArg___closed__2_value;
static const lean_closure_object l_Lean_ParametricAttribute_getParam_x3f___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_ParametricAttribute_getParam_x3f___redArg___closed__3 = (const lean_object*)&l_Lean_ParametricAttribute_getParam_x3f___redArg___closed__3_value;
static const lean_closure_object l_Lean_ParametricAttribute_getParam_x3f___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_ParametricAttribute_getParam_x3f___redArg___closed__4 = (const lean_object*)&l_Lean_ParametricAttribute_getParam_x3f___redArg___closed__4_value;
static const lean_closure_object l_Lean_ParametricAttribute_getParam_x3f___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_ParametricAttribute_getParam_x3f___redArg___closed__5 = (const lean_object*)&l_Lean_ParametricAttribute_getParam_x3f___redArg___closed__5_value;
static const lean_closure_object l_Lean_ParametricAttribute_getParam_x3f___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_ParametricAttribute_getParam_x3f___redArg___closed__6 = (const lean_object*)&l_Lean_ParametricAttribute_getParam_x3f___redArg___closed__6_value;
static const lean_closure_object l_Lean_ParametricAttribute_getParam_x3f___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_ParametricAttribute_getParam_x3f___redArg___closed__7 = (const lean_object*)&l_Lean_ParametricAttribute_getParam_x3f___redArg___closed__7_value;
static const lean_closure_object l_Lean_ParametricAttribute_getParam_x3f___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_ParametricAttribute_getParam_x3f___redArg___closed__8 = (const lean_object*)&l_Lean_ParametricAttribute_getParam_x3f___redArg___closed__8_value;
static const lean_ctor_object l_Lean_ParametricAttribute_getParam_x3f___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_ParametricAttribute_getParam_x3f___redArg___closed__2_value),((lean_object*)&l_Lean_ParametricAttribute_getParam_x3f___redArg___closed__3_value)}};
static const lean_object* l_Lean_ParametricAttribute_getParam_x3f___redArg___closed__9 = (const lean_object*)&l_Lean_ParametricAttribute_getParam_x3f___redArg___closed__9_value;
static const lean_ctor_object l_Lean_ParametricAttribute_getParam_x3f___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_ParametricAttribute_getParam_x3f___redArg___closed__9_value),((lean_object*)&l_Lean_ParametricAttribute_getParam_x3f___redArg___closed__4_value),((lean_object*)&l_Lean_ParametricAttribute_getParam_x3f___redArg___closed__5_value),((lean_object*)&l_Lean_ParametricAttribute_getParam_x3f___redArg___closed__6_value),((lean_object*)&l_Lean_ParametricAttribute_getParam_x3f___redArg___closed__7_value)}};
static const lean_object* l_Lean_ParametricAttribute_getParam_x3f___redArg___closed__10 = (const lean_object*)&l_Lean_ParametricAttribute_getParam_x3f___redArg___closed__10_value;
static const lean_ctor_object l_Lean_ParametricAttribute_getParam_x3f___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_ParametricAttribute_getParam_x3f___redArg___closed__10_value),((lean_object*)&l_Lean_ParametricAttribute_getParam_x3f___redArg___closed__8_value)}};
static const lean_object* l_Lean_ParametricAttribute_getParam_x3f___redArg___closed__11 = (const lean_object*)&l_Lean_ParametricAttribute_getParam_x3f___redArg___closed__11_value;
static const lean_ctor_object l_Lean_ParametricAttribute_getParam_x3f___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_ParametricAttribute_getParam_x3f___redArg___closed__12 = (const lean_object*)&l_Lean_ParametricAttribute_getParam_x3f___redArg___closed__12_value;
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParam_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParam_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParam_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParam_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_ParametricAttribute_setParam___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "Failed to add parametric attribute `["};
static const lean_object* l_Lean_ParametricAttribute_setParam___redArg___closed__0 = (const lean_object*)&l_Lean_ParametricAttribute_setParam___redArg___closed__0_value;
static const lean_string_object l_Lean_ParametricAttribute_setParam___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "]` to `"};
static const lean_object* l_Lean_ParametricAttribute_setParam___redArg___closed__1 = (const lean_object*)&l_Lean_ParametricAttribute_setParam___redArg___closed__1_value;
static const lean_string_object l_Lean_ParametricAttribute_setParam___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "`: Attribute has already been set"};
static const lean_object* l_Lean_ParametricAttribute_setParam___redArg___closed__2 = (const lean_object*)&l_Lean_ParametricAttribute_setParam___redArg___closed__2_value;
static const lean_string_object l_Lean_ParametricAttribute_setParam___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "`: Declaration is in an imported module"};
static const lean_object* l_Lean_ParametricAttribute_setParam___redArg___closed__3 = (const lean_object*)&l_Lean_ParametricAttribute_setParam___redArg___closed__3_value;
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
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_registerEnumAttributes_spec__3(lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_registerEnumAttributes_spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* lean_is_attribute(lean_object*);
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
LEAN_EXPORT lean_object* lean_attribute_application_time(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getBuiltinAttributeApplicationTime___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_updateEnvAttributesImpl_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_updateEnvAttributesImpl_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_updateEnvAttributesImpl_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_toCtorIdx(uint8_t v_x_8_){
_start:
{
lean_object* v___x_9_; 
v___x_9_ = l_Lean_AttributeApplicationTime_ctorIdx(v_x_8_);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_toCtorIdx___boxed(lean_object* v_x_10_){
_start:
{
uint8_t v_x_4__boxed_11_; lean_object* v_res_12_; 
v_x_4__boxed_11_ = lean_unbox(v_x_10_);
v_res_12_ = l_Lean_AttributeApplicationTime_toCtorIdx(v_x_4__boxed_11_);
return v_res_12_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_ctorElim___redArg(lean_object* v_k_13_){
_start:
{
lean_inc(v_k_13_);
return v_k_13_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_ctorElim___redArg___boxed(lean_object* v_k_14_){
_start:
{
lean_object* v_res_15_; 
v_res_15_ = l_Lean_AttributeApplicationTime_ctorElim___redArg(v_k_14_);
lean_dec(v_k_14_);
return v_res_15_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_ctorElim(lean_object* v_motive_16_, lean_object* v_ctorIdx_17_, uint8_t v_t_18_, lean_object* v_h_19_, lean_object* v_k_20_){
_start:
{
lean_inc(v_k_20_);
return v_k_20_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_ctorElim___boxed(lean_object* v_motive_21_, lean_object* v_ctorIdx_22_, lean_object* v_t_23_, lean_object* v_h_24_, lean_object* v_k_25_){
_start:
{
uint8_t v_t_boxed_26_; lean_object* v_res_27_; 
v_t_boxed_26_ = lean_unbox(v_t_23_);
v_res_27_ = l_Lean_AttributeApplicationTime_ctorElim(v_motive_21_, v_ctorIdx_22_, v_t_boxed_26_, v_h_24_, v_k_25_);
lean_dec(v_k_25_);
lean_dec(v_ctorIdx_22_);
return v_res_27_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_afterTypeChecking_elim___redArg(lean_object* v_afterTypeChecking_28_){
_start:
{
lean_inc(v_afterTypeChecking_28_);
return v_afterTypeChecking_28_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_afterTypeChecking_elim___redArg___boxed(lean_object* v_afterTypeChecking_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l_Lean_AttributeApplicationTime_afterTypeChecking_elim___redArg(v_afterTypeChecking_29_);
lean_dec(v_afterTypeChecking_29_);
return v_res_30_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_afterTypeChecking_elim(lean_object* v_motive_31_, uint8_t v_t_32_, lean_object* v_h_33_, lean_object* v_afterTypeChecking_34_){
_start:
{
lean_inc(v_afterTypeChecking_34_);
return v_afterTypeChecking_34_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_afterTypeChecking_elim___boxed(lean_object* v_motive_35_, lean_object* v_t_36_, lean_object* v_h_37_, lean_object* v_afterTypeChecking_38_){
_start:
{
uint8_t v_t_boxed_39_; lean_object* v_res_40_; 
v_t_boxed_39_ = lean_unbox(v_t_36_);
v_res_40_ = l_Lean_AttributeApplicationTime_afterTypeChecking_elim(v_motive_35_, v_t_boxed_39_, v_h_37_, v_afterTypeChecking_38_);
lean_dec(v_afterTypeChecking_38_);
return v_res_40_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_afterCompilation_elim___redArg(lean_object* v_afterCompilation_41_){
_start:
{
lean_inc(v_afterCompilation_41_);
return v_afterCompilation_41_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_afterCompilation_elim___redArg___boxed(lean_object* v_afterCompilation_42_){
_start:
{
lean_object* v_res_43_; 
v_res_43_ = l_Lean_AttributeApplicationTime_afterCompilation_elim___redArg(v_afterCompilation_42_);
lean_dec(v_afterCompilation_42_);
return v_res_43_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_afterCompilation_elim(lean_object* v_motive_44_, uint8_t v_t_45_, lean_object* v_h_46_, lean_object* v_afterCompilation_47_){
_start:
{
lean_inc(v_afterCompilation_47_);
return v_afterCompilation_47_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_afterCompilation_elim___boxed(lean_object* v_motive_48_, lean_object* v_t_49_, lean_object* v_h_50_, lean_object* v_afterCompilation_51_){
_start:
{
uint8_t v_t_boxed_52_; lean_object* v_res_53_; 
v_t_boxed_52_ = lean_unbox(v_t_49_);
v_res_53_ = l_Lean_AttributeApplicationTime_afterCompilation_elim(v_motive_48_, v_t_boxed_52_, v_h_50_, v_afterCompilation_51_);
lean_dec(v_afterCompilation_51_);
return v_res_53_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_beforeElaboration_elim___redArg(lean_object* v_beforeElaboration_54_){
_start:
{
lean_inc(v_beforeElaboration_54_);
return v_beforeElaboration_54_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_beforeElaboration_elim___redArg___boxed(lean_object* v_beforeElaboration_55_){
_start:
{
lean_object* v_res_56_; 
v_res_56_ = l_Lean_AttributeApplicationTime_beforeElaboration_elim___redArg(v_beforeElaboration_55_);
lean_dec(v_beforeElaboration_55_);
return v_res_56_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_beforeElaboration_elim(lean_object* v_motive_57_, uint8_t v_t_58_, lean_object* v_h_59_, lean_object* v_beforeElaboration_60_){
_start:
{
lean_inc(v_beforeElaboration_60_);
return v_beforeElaboration_60_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_beforeElaboration_elim___boxed(lean_object* v_motive_61_, lean_object* v_t_62_, lean_object* v_h_63_, lean_object* v_beforeElaboration_64_){
_start:
{
uint8_t v_t_boxed_65_; lean_object* v_res_66_; 
v_t_boxed_65_ = lean_unbox(v_t_62_);
v_res_66_ = l_Lean_AttributeApplicationTime_beforeElaboration_elim(v_motive_61_, v_t_boxed_65_, v_h_63_, v_beforeElaboration_64_);
lean_dec(v_beforeElaboration_64_);
return v_res_66_;
}
}
static uint8_t _init_l_Lean_instInhabitedAttributeApplicationTime_default(void){
_start:
{
uint8_t v___x_67_; 
v___x_67_ = 0;
return v___x_67_;
}
}
static uint8_t _init_l_Lean_instInhabitedAttributeApplicationTime(void){
_start:
{
uint8_t v___x_68_; 
v___x_68_ = 0;
return v___x_68_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqAttributeApplicationTime_beq(uint8_t v_x_69_, uint8_t v_y_70_){
_start:
{
lean_object* v___x_71_; lean_object* v___x_72_; uint8_t v___x_73_; 
v___x_71_ = l_Lean_AttributeApplicationTime_ctorIdx(v_x_69_);
v___x_72_ = l_Lean_AttributeApplicationTime_ctorIdx(v_y_70_);
v___x_73_ = lean_nat_dec_eq(v___x_71_, v___x_72_);
lean_dec(v___x_72_);
lean_dec(v___x_71_);
return v___x_73_;
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqAttributeApplicationTime_beq___boxed(lean_object* v_x_74_, lean_object* v_y_75_){
_start:
{
uint8_t v_x_17__boxed_76_; uint8_t v_y_18__boxed_77_; uint8_t v_res_78_; lean_object* v_r_79_; 
v_x_17__boxed_76_ = lean_unbox(v_x_74_);
v_y_18__boxed_77_ = lean_unbox(v_y_75_);
v_res_78_ = l_Lean_instBEqAttributeApplicationTime_beq(v_x_17__boxed_76_, v_y_18__boxed_77_);
v_r_79_ = lean_box(v_res_78_);
return v_r_79_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadLiftImportMAttrM___lam__0(lean_object* v_00_u03b1_82_, lean_object* v_x_83_, lean_object* v___y_84_, lean_object* v___y_85_){
_start:
{
lean_object* v___x_87_; lean_object* v_env_88_; lean_object* v_options_89_; lean_object* v_ref_90_; lean_object* v___x_91_; lean_object* v___x_92_; 
v___x_87_ = lean_st_ref_get(v___y_85_);
v_env_88_ = lean_ctor_get(v___x_87_, 0);
lean_inc_ref(v_env_88_);
lean_dec(v___x_87_);
v_options_89_ = lean_ctor_get(v___y_84_, 2);
v_ref_90_ = lean_ctor_get(v___y_84_, 5);
lean_inc_ref(v_options_89_);
v___x_91_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_91_, 0, v_env_88_);
lean_ctor_set(v___x_91_, 1, v_options_89_);
v___x_92_ = lean_apply_2(v_x_83_, v___x_91_, lean_box(0));
if (lean_obj_tag(v___x_92_) == 0)
{
lean_object* v_a_93_; lean_object* v___x_95_; uint8_t v_isShared_96_; uint8_t v_isSharedCheck_100_; 
v_a_93_ = lean_ctor_get(v___x_92_, 0);
v_isSharedCheck_100_ = !lean_is_exclusive(v___x_92_);
if (v_isSharedCheck_100_ == 0)
{
v___x_95_ = v___x_92_;
v_isShared_96_ = v_isSharedCheck_100_;
goto v_resetjp_94_;
}
else
{
lean_inc(v_a_93_);
lean_dec(v___x_92_);
v___x_95_ = lean_box(0);
v_isShared_96_ = v_isSharedCheck_100_;
goto v_resetjp_94_;
}
v_resetjp_94_:
{
lean_object* v___x_98_; 
if (v_isShared_96_ == 0)
{
v___x_98_ = v___x_95_;
goto v_reusejp_97_;
}
else
{
lean_object* v_reuseFailAlloc_99_; 
v_reuseFailAlloc_99_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_99_, 0, v_a_93_);
v___x_98_ = v_reuseFailAlloc_99_;
goto v_reusejp_97_;
}
v_reusejp_97_:
{
return v___x_98_;
}
}
}
else
{
lean_object* v_a_101_; lean_object* v___x_103_; uint8_t v_isShared_104_; uint8_t v_isSharedCheck_112_; 
v_a_101_ = lean_ctor_get(v___x_92_, 0);
v_isSharedCheck_112_ = !lean_is_exclusive(v___x_92_);
if (v_isSharedCheck_112_ == 0)
{
v___x_103_ = v___x_92_;
v_isShared_104_ = v_isSharedCheck_112_;
goto v_resetjp_102_;
}
else
{
lean_inc(v_a_101_);
lean_dec(v___x_92_);
v___x_103_ = lean_box(0);
v_isShared_104_ = v_isSharedCheck_112_;
goto v_resetjp_102_;
}
v_resetjp_102_:
{
lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_110_; 
v___x_105_ = lean_io_error_to_string(v_a_101_);
v___x_106_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_106_, 0, v___x_105_);
v___x_107_ = l_Lean_MessageData_ofFormat(v___x_106_);
lean_inc(v_ref_90_);
v___x_108_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_108_, 0, v_ref_90_);
lean_ctor_set(v___x_108_, 1, v___x_107_);
if (v_isShared_104_ == 0)
{
lean_ctor_set(v___x_103_, 0, v___x_108_);
v___x_110_ = v___x_103_;
goto v_reusejp_109_;
}
else
{
lean_object* v_reuseFailAlloc_111_; 
v_reuseFailAlloc_111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_111_, 0, v___x_108_);
v___x_110_ = v_reuseFailAlloc_111_;
goto v_reusejp_109_;
}
v_reusejp_109_:
{
return v___x_110_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadLiftImportMAttrM___lam__0___boxed(lean_object* v_00_u03b1_113_, lean_object* v_x_114_, lean_object* v___y_115_, lean_object* v___y_116_, lean_object* v___y_117_){
_start:
{
lean_object* v_res_118_; 
v_res_118_ = l_Lean_instMonadLiftImportMAttrM___lam__0(v_00_u03b1_113_, v_x_114_, v___y_115_, v___y_116_);
lean_dec(v___y_116_);
lean_dec_ref(v___y_115_);
return v_res_118_;
}
}
static lean_object* _init_l_Lean_AttributeImplCore_ref___autoParam___closed__12(void){
_start:
{
lean_object* v___x_147_; lean_object* v___x_148_; 
v___x_147_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__10));
v___x_148_ = l_Lean_mkAtom(v___x_147_);
return v___x_148_;
}
}
static lean_object* _init_l_Lean_AttributeImplCore_ref___autoParam___closed__13(void){
_start:
{
lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; 
v___x_149_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__12, &l_Lean_AttributeImplCore_ref___autoParam___closed__12_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__12);
v___x_150_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__5));
v___x_151_ = lean_array_push(v___x_150_, v___x_149_);
return v___x_151_;
}
}
static lean_object* _init_l_Lean_AttributeImplCore_ref___autoParam___closed__18(void){
_start:
{
lean_object* v___x_160_; lean_object* v___x_161_; 
v___x_160_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__17));
v___x_161_ = l_Lean_mkAtom(v___x_160_);
return v___x_161_;
}
}
static lean_object* _init_l_Lean_AttributeImplCore_ref___autoParam___closed__19(void){
_start:
{
lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; 
v___x_162_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__18, &l_Lean_AttributeImplCore_ref___autoParam___closed__18_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__18);
v___x_163_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__5));
v___x_164_ = lean_array_push(v___x_163_, v___x_162_);
return v___x_164_;
}
}
static lean_object* _init_l_Lean_AttributeImplCore_ref___autoParam___closed__20(void){
_start:
{
lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; 
v___x_165_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__19, &l_Lean_AttributeImplCore_ref___autoParam___closed__19_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__19);
v___x_166_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__16));
v___x_167_ = lean_box(2);
v___x_168_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_168_, 0, v___x_167_);
lean_ctor_set(v___x_168_, 1, v___x_166_);
lean_ctor_set(v___x_168_, 2, v___x_165_);
return v___x_168_;
}
}
static lean_object* _init_l_Lean_AttributeImplCore_ref___autoParam___closed__21(void){
_start:
{
lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; 
v___x_169_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__20, &l_Lean_AttributeImplCore_ref___autoParam___closed__20_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__20);
v___x_170_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__13, &l_Lean_AttributeImplCore_ref___autoParam___closed__13_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__13);
v___x_171_ = lean_array_push(v___x_170_, v___x_169_);
return v___x_171_;
}
}
static lean_object* _init_l_Lean_AttributeImplCore_ref___autoParam___closed__22(void){
_start:
{
lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; 
v___x_172_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__21, &l_Lean_AttributeImplCore_ref___autoParam___closed__21_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__21);
v___x_173_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__11));
v___x_174_ = lean_box(2);
v___x_175_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_175_, 0, v___x_174_);
lean_ctor_set(v___x_175_, 1, v___x_173_);
lean_ctor_set(v___x_175_, 2, v___x_172_);
return v___x_175_;
}
}
static lean_object* _init_l_Lean_AttributeImplCore_ref___autoParam___closed__23(void){
_start:
{
lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; 
v___x_176_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__22, &l_Lean_AttributeImplCore_ref___autoParam___closed__22_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__22);
v___x_177_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__5));
v___x_178_ = lean_array_push(v___x_177_, v___x_176_);
return v___x_178_;
}
}
static lean_object* _init_l_Lean_AttributeImplCore_ref___autoParam___closed__24(void){
_start:
{
lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; 
v___x_179_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__23, &l_Lean_AttributeImplCore_ref___autoParam___closed__23_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__23);
v___x_180_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__9));
v___x_181_ = lean_box(2);
v___x_182_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_182_, 0, v___x_181_);
lean_ctor_set(v___x_182_, 1, v___x_180_);
lean_ctor_set(v___x_182_, 2, v___x_179_);
return v___x_182_;
}
}
static lean_object* _init_l_Lean_AttributeImplCore_ref___autoParam___closed__25(void){
_start:
{
lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; 
v___x_183_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__24, &l_Lean_AttributeImplCore_ref___autoParam___closed__24_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__24);
v___x_184_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__5));
v___x_185_ = lean_array_push(v___x_184_, v___x_183_);
return v___x_185_;
}
}
static lean_object* _init_l_Lean_AttributeImplCore_ref___autoParam___closed__26(void){
_start:
{
lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; 
v___x_186_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__25, &l_Lean_AttributeImplCore_ref___autoParam___closed__25_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__25);
v___x_187_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__7));
v___x_188_ = lean_box(2);
v___x_189_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_189_, 0, v___x_188_);
lean_ctor_set(v___x_189_, 1, v___x_187_);
lean_ctor_set(v___x_189_, 2, v___x_186_);
return v___x_189_;
}
}
static lean_object* _init_l_Lean_AttributeImplCore_ref___autoParam___closed__27(void){
_start:
{
lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; 
v___x_190_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__26, &l_Lean_AttributeImplCore_ref___autoParam___closed__26_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__26);
v___x_191_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__5));
v___x_192_ = lean_array_push(v___x_191_, v___x_190_);
return v___x_192_;
}
}
static lean_object* _init_l_Lean_AttributeImplCore_ref___autoParam___closed__28(void){
_start:
{
lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; 
v___x_193_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__27, &l_Lean_AttributeImplCore_ref___autoParam___closed__27_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__27);
v___x_194_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__4));
v___x_195_ = lean_box(2);
v___x_196_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_196_, 0, v___x_195_);
lean_ctor_set(v___x_196_, 1, v___x_194_);
lean_ctor_set(v___x_196_, 2, v___x_193_);
return v___x_196_;
}
}
static lean_object* _init_l_Lean_AttributeImplCore_ref___autoParam(void){
_start:
{
lean_object* v___x_197_; 
v___x_197_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__28, &l_Lean_AttributeImplCore_ref___autoParam___closed__28_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__28);
return v___x_197_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_ctorIdx(uint8_t v_x_212_){
_start:
{
switch(v_x_212_)
{
case 0:
{
lean_object* v___x_213_; 
v___x_213_ = lean_unsigned_to_nat(0u);
return v___x_213_;
}
case 1:
{
lean_object* v___x_214_; 
v___x_214_ = lean_unsigned_to_nat(1u);
return v___x_214_;
}
default: 
{
lean_object* v___x_215_; 
v___x_215_ = lean_unsigned_to_nat(2u);
return v___x_215_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_ctorIdx___boxed(lean_object* v_x_216_){
_start:
{
uint8_t v_x_boxed_217_; lean_object* v_res_218_; 
v_x_boxed_217_ = lean_unbox(v_x_216_);
v_res_218_ = l_Lean_AttributeKind_ctorIdx(v_x_boxed_217_);
return v_res_218_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_toCtorIdx(uint8_t v_x_219_){
_start:
{
lean_object* v___x_220_; 
v___x_220_ = l_Lean_AttributeKind_ctorIdx(v_x_219_);
return v___x_220_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_toCtorIdx___boxed(lean_object* v_x_221_){
_start:
{
uint8_t v_x_4__boxed_222_; lean_object* v_res_223_; 
v_x_4__boxed_222_ = lean_unbox(v_x_221_);
v_res_223_ = l_Lean_AttributeKind_toCtorIdx(v_x_4__boxed_222_);
return v_res_223_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_ctorElim___redArg(lean_object* v_k_224_){
_start:
{
lean_inc(v_k_224_);
return v_k_224_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_ctorElim___redArg___boxed(lean_object* v_k_225_){
_start:
{
lean_object* v_res_226_; 
v_res_226_ = l_Lean_AttributeKind_ctorElim___redArg(v_k_225_);
lean_dec(v_k_225_);
return v_res_226_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_ctorElim(lean_object* v_motive_227_, lean_object* v_ctorIdx_228_, uint8_t v_t_229_, lean_object* v_h_230_, lean_object* v_k_231_){
_start:
{
lean_inc(v_k_231_);
return v_k_231_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_ctorElim___boxed(lean_object* v_motive_232_, lean_object* v_ctorIdx_233_, lean_object* v_t_234_, lean_object* v_h_235_, lean_object* v_k_236_){
_start:
{
uint8_t v_t_boxed_237_; lean_object* v_res_238_; 
v_t_boxed_237_ = lean_unbox(v_t_234_);
v_res_238_ = l_Lean_AttributeKind_ctorElim(v_motive_232_, v_ctorIdx_233_, v_t_boxed_237_, v_h_235_, v_k_236_);
lean_dec(v_k_236_);
lean_dec(v_ctorIdx_233_);
return v_res_238_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_global_elim___redArg(lean_object* v_global_239_){
_start:
{
lean_inc(v_global_239_);
return v_global_239_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_global_elim___redArg___boxed(lean_object* v_global_240_){
_start:
{
lean_object* v_res_241_; 
v_res_241_ = l_Lean_AttributeKind_global_elim___redArg(v_global_240_);
lean_dec(v_global_240_);
return v_res_241_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_global_elim(lean_object* v_motive_242_, uint8_t v_t_243_, lean_object* v_h_244_, lean_object* v_global_245_){
_start:
{
lean_inc(v_global_245_);
return v_global_245_;
}
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
LEAN_EXPORT lean_object* l_Lean_AttributeKind_local_elim(lean_object* v_motive_255_, uint8_t v_t_256_, lean_object* v_h_257_, lean_object* v_local_258_){
_start:
{
lean_inc(v_local_258_);
return v_local_258_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_local_elim___boxed(lean_object* v_motive_259_, lean_object* v_t_260_, lean_object* v_h_261_, lean_object* v_local_262_){
_start:
{
uint8_t v_t_boxed_263_; lean_object* v_res_264_; 
v_t_boxed_263_ = lean_unbox(v_t_260_);
v_res_264_ = l_Lean_AttributeKind_local_elim(v_motive_259_, v_t_boxed_263_, v_h_261_, v_local_262_);
lean_dec(v_local_262_);
return v_res_264_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_scoped_elim___redArg(lean_object* v_scoped_265_){
_start:
{
lean_inc(v_scoped_265_);
return v_scoped_265_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_scoped_elim___redArg___boxed(lean_object* v_scoped_266_){
_start:
{
lean_object* v_res_267_; 
v_res_267_ = l_Lean_AttributeKind_scoped_elim___redArg(v_scoped_266_);
lean_dec(v_scoped_266_);
return v_res_267_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_scoped_elim(lean_object* v_motive_268_, uint8_t v_t_269_, lean_object* v_h_270_, lean_object* v_scoped_271_){
_start:
{
lean_inc(v_scoped_271_);
return v_scoped_271_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_scoped_elim___boxed(lean_object* v_motive_272_, lean_object* v_t_273_, lean_object* v_h_274_, lean_object* v_scoped_275_){
_start:
{
uint8_t v_t_boxed_276_; lean_object* v_res_277_; 
v_t_boxed_276_ = lean_unbox(v_t_273_);
v_res_277_ = l_Lean_AttributeKind_scoped_elim(v_motive_272_, v_t_boxed_276_, v_h_274_, v_scoped_275_);
lean_dec(v_scoped_275_);
return v_res_277_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqAttributeKind_beq(uint8_t v_x_278_, uint8_t v_y_279_){
_start:
{
lean_object* v___x_280_; lean_object* v___x_281_; uint8_t v___x_282_; 
v___x_280_ = l_Lean_AttributeKind_ctorIdx(v_x_278_);
v___x_281_ = l_Lean_AttributeKind_ctorIdx(v_y_279_);
v___x_282_ = lean_nat_dec_eq(v___x_280_, v___x_281_);
lean_dec(v___x_281_);
lean_dec(v___x_280_);
return v___x_282_;
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqAttributeKind_beq___boxed(lean_object* v_x_283_, lean_object* v_y_284_){
_start:
{
uint8_t v_x_17__boxed_285_; uint8_t v_y_18__boxed_286_; uint8_t v_res_287_; lean_object* v_r_288_; 
v_x_17__boxed_285_ = lean_unbox(v_x_283_);
v_y_18__boxed_286_ = lean_unbox(v_y_284_);
v_res_287_ = l_Lean_instBEqAttributeKind_beq(v_x_17__boxed_285_, v_y_18__boxed_286_);
v_r_288_ = lean_box(v_res_287_);
return v_r_288_;
}
}
static uint8_t _init_l_Lean_instInhabitedAttributeKind_default(void){
_start:
{
uint8_t v___x_291_; 
v___x_291_ = 0;
return v___x_291_;
}
}
static uint8_t _init_l_Lean_instInhabitedAttributeKind(void){
_start:
{
uint8_t v___x_292_; 
v___x_292_ = 0;
return v___x_292_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToStringAttributeKind___lam__0(uint8_t v_x_296_){
_start:
{
switch(v_x_296_)
{
case 0:
{
lean_object* v___x_297_; 
v___x_297_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__0));
return v___x_297_;
}
case 1:
{
lean_object* v___x_298_; 
v___x_298_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__1));
return v___x_298_;
}
default: 
{
lean_object* v___x_299_; 
v___x_299_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__2));
return v___x_299_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToStringAttributeKind___lam__0___boxed(lean_object* v_x_300_){
_start:
{
uint8_t v_x_36__boxed_301_; lean_object* v_res_302_; 
v_x_36__boxed_301_ = lean_unbox(v_x_300_);
v_res_302_ = l_Lean_instToStringAttributeKind___lam__0(v_x_36__boxed_301_);
return v_res_302_;
}
}
static lean_object* _init_l_Lean_instInhabitedAttributeImpl_default___lam__0___closed__0(void){
_start:
{
lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; 
v___x_305_ = l_Lean_instInhabitedMessageData_default;
v___x_306_ = lean_box(0);
v___x_307_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_307_, 0, v___x_306_);
lean_ctor_set(v___x_307_, 1, v___x_305_);
return v___x_307_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedAttributeImpl_default___lam__0(lean_object* v_x_308_, lean_object* v___y_309_, uint8_t v___y_310_, lean_object* v___y_311_, lean_object* v___y_312_){
_start:
{
lean_object* v___x_314_; lean_object* v___x_315_; 
v___x_314_ = lean_obj_once(&l_Lean_instInhabitedAttributeImpl_default___lam__0___closed__0, &l_Lean_instInhabitedAttributeImpl_default___lam__0___closed__0_once, _init_l_Lean_instInhabitedAttributeImpl_default___lam__0___closed__0);
v___x_315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_315_, 0, v___x_314_);
return v___x_315_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedAttributeImpl_default___lam__0___boxed(lean_object* v_x_316_, lean_object* v___y_317_, lean_object* v___y_318_, lean_object* v___y_319_, lean_object* v___y_320_, lean_object* v___y_321_){
_start:
{
uint8_t v___y_123__boxed_322_; lean_object* v_res_323_; 
v___y_123__boxed_322_ = lean_unbox(v___y_318_);
v_res_323_ = l_Lean_instInhabitedAttributeImpl_default___lam__0(v_x_316_, v___y_317_, v___y_123__boxed_322_, v___y_319_, v___y_320_);
lean_dec(v___y_320_);
lean_dec_ref(v___y_319_);
lean_dec(v___y_317_);
lean_dec(v_x_316_);
return v_res_323_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedAttributeImpl_default___lam__1(lean_object* v_x_324_, lean_object* v___y_325_, lean_object* v___y_326_){
_start:
{
lean_object* v___x_328_; lean_object* v___x_329_; 
v___x_328_ = lean_obj_once(&l_Lean_instInhabitedAttributeImpl_default___lam__0___closed__0, &l_Lean_instInhabitedAttributeImpl_default___lam__0___closed__0_once, _init_l_Lean_instInhabitedAttributeImpl_default___lam__0___closed__0);
v___x_329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_329_, 0, v___x_328_);
return v___x_329_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedAttributeImpl_default___lam__1___boxed(lean_object* v_x_330_, lean_object* v___y_331_, lean_object* v___y_332_, lean_object* v___y_333_){
_start:
{
lean_object* v_res_334_; 
v_res_334_ = l_Lean_instInhabitedAttributeImpl_default___lam__1(v_x_330_, v___y_331_, v___y_332_);
lean_dec(v___y_332_);
lean_dec_ref(v___y_331_);
lean_dec(v_x_330_);
return v_res_334_;
}
}
static lean_object* _init_l___private_Lean_Attributes_0__Lean_initFn___closed__0_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; 
v___x_353_ = lean_box(0);
v___x_354_ = lean_unsigned_to_nat(16u);
v___x_355_ = lean_mk_array(v___x_354_, v___x_353_);
return v___x_355_;
}
}
static lean_object* _init_l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; 
v___x_356_ = lean_obj_once(&l___private_Lean_Attributes_0__Lean_initFn___closed__0_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_, &l___private_Lean_Attributes_0__Lean_initFn___closed__0_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2__once, _init_l___private_Lean_Attributes_0__Lean_initFn___closed__0_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_);
v___x_357_ = lean_unsigned_to_nat(0u);
v___x_358_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_358_, 0, v___x_357_);
lean_ctor_set(v___x_358_, 1, v___x_356_);
return v___x_358_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; 
v___x_360_ = lean_obj_once(&l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_, &l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2__once, _init_l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_);
v___x_361_ = lean_st_mk_ref(v___x_360_);
v___x_362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_362_, 0, v___x_361_);
return v___x_362_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2____boxed(lean_object* v_a_363_){
_start:
{
lean_object* v_res_364_; 
v_res_364_ = l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_();
return v_res_364_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0_spec__0___redArg(lean_object* v_a_365_, lean_object* v_x_366_){
_start:
{
if (lean_obj_tag(v_x_366_) == 0)
{
uint8_t v___x_367_; 
v___x_367_ = 0;
return v___x_367_;
}
else
{
lean_object* v_key_368_; lean_object* v_tail_369_; uint8_t v___x_370_; 
v_key_368_ = lean_ctor_get(v_x_366_, 0);
v_tail_369_ = lean_ctor_get(v_x_366_, 2);
v___x_370_ = lean_name_eq(v_key_368_, v_a_365_);
if (v___x_370_ == 0)
{
v_x_366_ = v_tail_369_;
goto _start;
}
else
{
return v___x_370_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0_spec__0___redArg___boxed(lean_object* v_a_372_, lean_object* v_x_373_){
_start:
{
uint8_t v_res_374_; lean_object* v_r_375_; 
v_res_374_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0_spec__0___redArg(v_a_372_, v_x_373_);
lean_dec(v_x_373_);
lean_dec(v_a_372_);
v_r_375_ = lean_box(v_res_374_);
return v_r_375_;
}
}
static uint64_t _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_376_; uint64_t v___x_377_; 
v___x_376_ = lean_unsigned_to_nat(1723u);
v___x_377_ = lean_uint64_of_nat(v___x_376_);
return v___x_377_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(lean_object* v_m_378_, lean_object* v_a_379_){
_start:
{
lean_object* v_buckets_380_; lean_object* v___x_381_; uint64_t v___y_383_; 
v_buckets_380_ = lean_ctor_get(v_m_378_, 1);
v___x_381_ = lean_array_get_size(v_buckets_380_);
if (lean_obj_tag(v_a_379_) == 0)
{
uint64_t v___x_397_; 
v___x_397_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg___closed__0);
v___y_383_ = v___x_397_;
goto v___jp_382_;
}
else
{
uint64_t v_hash_398_; 
v_hash_398_ = lean_ctor_get_uint64(v_a_379_, sizeof(void*)*2);
v___y_383_ = v_hash_398_;
goto v___jp_382_;
}
v___jp_382_:
{
uint64_t v___x_384_; uint64_t v___x_385_; uint64_t v_fold_386_; uint64_t v___x_387_; uint64_t v___x_388_; uint64_t v___x_389_; size_t v___x_390_; size_t v___x_391_; size_t v___x_392_; size_t v___x_393_; size_t v___x_394_; lean_object* v___x_395_; uint8_t v___x_396_; 
v___x_384_ = 32ULL;
v___x_385_ = lean_uint64_shift_right(v___y_383_, v___x_384_);
v_fold_386_ = lean_uint64_xor(v___y_383_, v___x_385_);
v___x_387_ = 16ULL;
v___x_388_ = lean_uint64_shift_right(v_fold_386_, v___x_387_);
v___x_389_ = lean_uint64_xor(v_fold_386_, v___x_388_);
v___x_390_ = lean_uint64_to_usize(v___x_389_);
v___x_391_ = lean_usize_of_nat(v___x_381_);
v___x_392_ = ((size_t)1ULL);
v___x_393_ = lean_usize_sub(v___x_391_, v___x_392_);
v___x_394_ = lean_usize_land(v___x_390_, v___x_393_);
v___x_395_ = lean_array_uget_borrowed(v_buckets_380_, v___x_394_);
v___x_396_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0_spec__0___redArg(v_a_379_, v___x_395_);
return v___x_396_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg___boxed(lean_object* v_m_399_, lean_object* v_a_400_){
_start:
{
uint8_t v_res_401_; lean_object* v_r_402_; 
v_res_401_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(v_m_399_, v_a_400_);
lean_dec(v_a_400_);
lean_dec_ref(v_m_399_);
v_r_402_ = lean_box(v_res_401_);
return v_r_402_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__3___redArg(lean_object* v_a_403_, lean_object* v_b_404_, lean_object* v_x_405_){
_start:
{
if (lean_obj_tag(v_x_405_) == 0)
{
lean_dec(v_b_404_);
lean_dec(v_a_403_);
return v_x_405_;
}
else
{
lean_object* v_key_406_; lean_object* v_value_407_; lean_object* v_tail_408_; lean_object* v___x_410_; uint8_t v_isShared_411_; uint8_t v_isSharedCheck_420_; 
v_key_406_ = lean_ctor_get(v_x_405_, 0);
v_value_407_ = lean_ctor_get(v_x_405_, 1);
v_tail_408_ = lean_ctor_get(v_x_405_, 2);
v_isSharedCheck_420_ = !lean_is_exclusive(v_x_405_);
if (v_isSharedCheck_420_ == 0)
{
v___x_410_ = v_x_405_;
v_isShared_411_ = v_isSharedCheck_420_;
goto v_resetjp_409_;
}
else
{
lean_inc(v_tail_408_);
lean_inc(v_value_407_);
lean_inc(v_key_406_);
lean_dec(v_x_405_);
v___x_410_ = lean_box(0);
v_isShared_411_ = v_isSharedCheck_420_;
goto v_resetjp_409_;
}
v_resetjp_409_:
{
uint8_t v___x_412_; 
v___x_412_ = lean_name_eq(v_key_406_, v_a_403_);
if (v___x_412_ == 0)
{
lean_object* v___x_413_; lean_object* v___x_415_; 
v___x_413_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__3___redArg(v_a_403_, v_b_404_, v_tail_408_);
if (v_isShared_411_ == 0)
{
lean_ctor_set(v___x_410_, 2, v___x_413_);
v___x_415_ = v___x_410_;
goto v_reusejp_414_;
}
else
{
lean_object* v_reuseFailAlloc_416_; 
v_reuseFailAlloc_416_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_416_, 0, v_key_406_);
lean_ctor_set(v_reuseFailAlloc_416_, 1, v_value_407_);
lean_ctor_set(v_reuseFailAlloc_416_, 2, v___x_413_);
v___x_415_ = v_reuseFailAlloc_416_;
goto v_reusejp_414_;
}
v_reusejp_414_:
{
return v___x_415_;
}
}
else
{
lean_object* v___x_418_; 
lean_dec(v_value_407_);
lean_dec(v_key_406_);
if (v_isShared_411_ == 0)
{
lean_ctor_set(v___x_410_, 1, v_b_404_);
lean_ctor_set(v___x_410_, 0, v_a_403_);
v___x_418_ = v___x_410_;
goto v_reusejp_417_;
}
else
{
lean_object* v_reuseFailAlloc_419_; 
v_reuseFailAlloc_419_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_419_, 0, v_a_403_);
lean_ctor_set(v_reuseFailAlloc_419_, 1, v_b_404_);
lean_ctor_set(v_reuseFailAlloc_419_, 2, v_tail_408_);
v___x_418_ = v_reuseFailAlloc_419_;
goto v_reusejp_417_;
}
v_reusejp_417_:
{
return v___x_418_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2_spec__3_spec__4___redArg(lean_object* v_x_421_, lean_object* v_x_422_){
_start:
{
if (lean_obj_tag(v_x_422_) == 0)
{
return v_x_421_;
}
else
{
lean_object* v_key_423_; lean_object* v_value_424_; lean_object* v_tail_425_; lean_object* v___x_427_; uint8_t v_isShared_428_; uint8_t v_isSharedCheck_451_; 
v_key_423_ = lean_ctor_get(v_x_422_, 0);
v_value_424_ = lean_ctor_get(v_x_422_, 1);
v_tail_425_ = lean_ctor_get(v_x_422_, 2);
v_isSharedCheck_451_ = !lean_is_exclusive(v_x_422_);
if (v_isSharedCheck_451_ == 0)
{
v___x_427_ = v_x_422_;
v_isShared_428_ = v_isSharedCheck_451_;
goto v_resetjp_426_;
}
else
{
lean_inc(v_tail_425_);
lean_inc(v_value_424_);
lean_inc(v_key_423_);
lean_dec(v_x_422_);
v___x_427_ = lean_box(0);
v_isShared_428_ = v_isSharedCheck_451_;
goto v_resetjp_426_;
}
v_resetjp_426_:
{
lean_object* v___x_429_; uint64_t v___y_431_; 
v___x_429_ = lean_array_get_size(v_x_421_);
if (lean_obj_tag(v_key_423_) == 0)
{
uint64_t v___x_449_; 
v___x_449_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg___closed__0);
v___y_431_ = v___x_449_;
goto v___jp_430_;
}
else
{
uint64_t v_hash_450_; 
v_hash_450_ = lean_ctor_get_uint64(v_key_423_, sizeof(void*)*2);
v___y_431_ = v_hash_450_;
goto v___jp_430_;
}
v___jp_430_:
{
uint64_t v___x_432_; uint64_t v___x_433_; uint64_t v_fold_434_; uint64_t v___x_435_; uint64_t v___x_436_; uint64_t v___x_437_; size_t v___x_438_; size_t v___x_439_; size_t v___x_440_; size_t v___x_441_; size_t v___x_442_; lean_object* v___x_443_; lean_object* v___x_445_; 
v___x_432_ = 32ULL;
v___x_433_ = lean_uint64_shift_right(v___y_431_, v___x_432_);
v_fold_434_ = lean_uint64_xor(v___y_431_, v___x_433_);
v___x_435_ = 16ULL;
v___x_436_ = lean_uint64_shift_right(v_fold_434_, v___x_435_);
v___x_437_ = lean_uint64_xor(v_fold_434_, v___x_436_);
v___x_438_ = lean_uint64_to_usize(v___x_437_);
v___x_439_ = lean_usize_of_nat(v___x_429_);
v___x_440_ = ((size_t)1ULL);
v___x_441_ = lean_usize_sub(v___x_439_, v___x_440_);
v___x_442_ = lean_usize_land(v___x_438_, v___x_441_);
v___x_443_ = lean_array_uget_borrowed(v_x_421_, v___x_442_);
lean_inc(v___x_443_);
if (v_isShared_428_ == 0)
{
lean_ctor_set(v___x_427_, 2, v___x_443_);
v___x_445_ = v___x_427_;
goto v_reusejp_444_;
}
else
{
lean_object* v_reuseFailAlloc_448_; 
v_reuseFailAlloc_448_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_448_, 0, v_key_423_);
lean_ctor_set(v_reuseFailAlloc_448_, 1, v_value_424_);
lean_ctor_set(v_reuseFailAlloc_448_, 2, v___x_443_);
v___x_445_ = v_reuseFailAlloc_448_;
goto v_reusejp_444_;
}
v_reusejp_444_:
{
lean_object* v___x_446_; 
v___x_446_ = lean_array_uset(v_x_421_, v___x_442_, v___x_445_);
v_x_421_ = v___x_446_;
v_x_422_ = v_tail_425_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2_spec__3___redArg(lean_object* v_i_452_, lean_object* v_source_453_, lean_object* v_target_454_){
_start:
{
lean_object* v___x_455_; uint8_t v___x_456_; 
v___x_455_ = lean_array_get_size(v_source_453_);
v___x_456_ = lean_nat_dec_lt(v_i_452_, v___x_455_);
if (v___x_456_ == 0)
{
lean_dec_ref(v_source_453_);
lean_dec(v_i_452_);
return v_target_454_;
}
else
{
lean_object* v_es_457_; lean_object* v___x_458_; lean_object* v_source_459_; lean_object* v_target_460_; lean_object* v___x_461_; lean_object* v___x_462_; 
v_es_457_ = lean_array_fget(v_source_453_, v_i_452_);
v___x_458_ = lean_box(0);
v_source_459_ = lean_array_fset(v_source_453_, v_i_452_, v___x_458_);
v_target_460_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2_spec__3_spec__4___redArg(v_target_454_, v_es_457_);
v___x_461_ = lean_unsigned_to_nat(1u);
v___x_462_ = lean_nat_add(v_i_452_, v___x_461_);
lean_dec(v_i_452_);
v_i_452_ = v___x_462_;
v_source_453_ = v_source_459_;
v_target_454_ = v_target_460_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2___redArg(lean_object* v_data_464_){
_start:
{
lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v_nbuckets_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; 
v___x_465_ = lean_array_get_size(v_data_464_);
v___x_466_ = lean_unsigned_to_nat(2u);
v_nbuckets_467_ = lean_nat_mul(v___x_465_, v___x_466_);
v___x_468_ = lean_unsigned_to_nat(0u);
v___x_469_ = lean_box(0);
v___x_470_ = lean_mk_array(v_nbuckets_467_, v___x_469_);
v___x_471_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2_spec__3___redArg(v___x_468_, v_data_464_, v___x_470_);
return v___x_471_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1___redArg(lean_object* v_m_472_, lean_object* v_a_473_, lean_object* v_b_474_){
_start:
{
lean_object* v_size_475_; lean_object* v_buckets_476_; lean_object* v___x_478_; uint8_t v_isShared_479_; uint8_t v_isSharedCheck_522_; 
v_size_475_ = lean_ctor_get(v_m_472_, 0);
v_buckets_476_ = lean_ctor_get(v_m_472_, 1);
v_isSharedCheck_522_ = !lean_is_exclusive(v_m_472_);
if (v_isSharedCheck_522_ == 0)
{
v___x_478_ = v_m_472_;
v_isShared_479_ = v_isSharedCheck_522_;
goto v_resetjp_477_;
}
else
{
lean_inc(v_buckets_476_);
lean_inc(v_size_475_);
lean_dec(v_m_472_);
v___x_478_ = lean_box(0);
v_isShared_479_ = v_isSharedCheck_522_;
goto v_resetjp_477_;
}
v_resetjp_477_:
{
lean_object* v___x_480_; uint64_t v___y_482_; 
v___x_480_ = lean_array_get_size(v_buckets_476_);
if (lean_obj_tag(v_a_473_) == 0)
{
uint64_t v___x_520_; 
v___x_520_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg___closed__0);
v___y_482_ = v___x_520_;
goto v___jp_481_;
}
else
{
uint64_t v_hash_521_; 
v_hash_521_ = lean_ctor_get_uint64(v_a_473_, sizeof(void*)*2);
v___y_482_ = v_hash_521_;
goto v___jp_481_;
}
v___jp_481_:
{
uint64_t v___x_483_; uint64_t v___x_484_; uint64_t v_fold_485_; uint64_t v___x_486_; uint64_t v___x_487_; uint64_t v___x_488_; size_t v___x_489_; size_t v___x_490_; size_t v___x_491_; size_t v___x_492_; size_t v___x_493_; lean_object* v_bkt_494_; uint8_t v___x_495_; 
v___x_483_ = 32ULL;
v___x_484_ = lean_uint64_shift_right(v___y_482_, v___x_483_);
v_fold_485_ = lean_uint64_xor(v___y_482_, v___x_484_);
v___x_486_ = 16ULL;
v___x_487_ = lean_uint64_shift_right(v_fold_485_, v___x_486_);
v___x_488_ = lean_uint64_xor(v_fold_485_, v___x_487_);
v___x_489_ = lean_uint64_to_usize(v___x_488_);
v___x_490_ = lean_usize_of_nat(v___x_480_);
v___x_491_ = ((size_t)1ULL);
v___x_492_ = lean_usize_sub(v___x_490_, v___x_491_);
v___x_493_ = lean_usize_land(v___x_489_, v___x_492_);
v_bkt_494_ = lean_array_uget_borrowed(v_buckets_476_, v___x_493_);
v___x_495_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0_spec__0___redArg(v_a_473_, v_bkt_494_);
if (v___x_495_ == 0)
{
lean_object* v___x_496_; lean_object* v_size_x27_497_; lean_object* v___x_498_; lean_object* v_buckets_x27_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; uint8_t v___x_505_; 
v___x_496_ = lean_unsigned_to_nat(1u);
v_size_x27_497_ = lean_nat_add(v_size_475_, v___x_496_);
lean_dec(v_size_475_);
lean_inc(v_bkt_494_);
v___x_498_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_498_, 0, v_a_473_);
lean_ctor_set(v___x_498_, 1, v_b_474_);
lean_ctor_set(v___x_498_, 2, v_bkt_494_);
v_buckets_x27_499_ = lean_array_uset(v_buckets_476_, v___x_493_, v___x_498_);
v___x_500_ = lean_unsigned_to_nat(4u);
v___x_501_ = lean_nat_mul(v_size_x27_497_, v___x_500_);
v___x_502_ = lean_unsigned_to_nat(3u);
v___x_503_ = lean_nat_div(v___x_501_, v___x_502_);
lean_dec(v___x_501_);
v___x_504_ = lean_array_get_size(v_buckets_x27_499_);
v___x_505_ = lean_nat_dec_le(v___x_503_, v___x_504_);
lean_dec(v___x_503_);
if (v___x_505_ == 0)
{
lean_object* v_val_506_; lean_object* v___x_508_; 
v_val_506_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2___redArg(v_buckets_x27_499_);
if (v_isShared_479_ == 0)
{
lean_ctor_set(v___x_478_, 1, v_val_506_);
lean_ctor_set(v___x_478_, 0, v_size_x27_497_);
v___x_508_ = v___x_478_;
goto v_reusejp_507_;
}
else
{
lean_object* v_reuseFailAlloc_509_; 
v_reuseFailAlloc_509_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_509_, 0, v_size_x27_497_);
lean_ctor_set(v_reuseFailAlloc_509_, 1, v_val_506_);
v___x_508_ = v_reuseFailAlloc_509_;
goto v_reusejp_507_;
}
v_reusejp_507_:
{
return v___x_508_;
}
}
else
{
lean_object* v___x_511_; 
if (v_isShared_479_ == 0)
{
lean_ctor_set(v___x_478_, 1, v_buckets_x27_499_);
lean_ctor_set(v___x_478_, 0, v_size_x27_497_);
v___x_511_ = v___x_478_;
goto v_reusejp_510_;
}
else
{
lean_object* v_reuseFailAlloc_512_; 
v_reuseFailAlloc_512_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_512_, 0, v_size_x27_497_);
lean_ctor_set(v_reuseFailAlloc_512_, 1, v_buckets_x27_499_);
v___x_511_ = v_reuseFailAlloc_512_;
goto v_reusejp_510_;
}
v_reusejp_510_:
{
return v___x_511_;
}
}
}
else
{
lean_object* v___x_513_; lean_object* v_buckets_x27_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_518_; 
lean_inc(v_bkt_494_);
v___x_513_ = lean_box(0);
v_buckets_x27_514_ = lean_array_uset(v_buckets_476_, v___x_493_, v___x_513_);
v___x_515_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__3___redArg(v_a_473_, v_b_474_, v_bkt_494_);
v___x_516_ = lean_array_uset(v_buckets_x27_514_, v___x_493_, v___x_515_);
if (v_isShared_479_ == 0)
{
lean_ctor_set(v___x_478_, 1, v___x_516_);
v___x_518_ = v___x_478_;
goto v_reusejp_517_;
}
else
{
lean_object* v_reuseFailAlloc_519_; 
v_reuseFailAlloc_519_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_519_, 0, v_size_475_);
lean_ctor_set(v_reuseFailAlloc_519_, 1, v___x_516_);
v___x_518_ = v_reuseFailAlloc_519_;
goto v_reusejp_517_;
}
v_reusejp_517_:
{
return v___x_518_;
}
}
}
}
}
}
static lean_object* _init_l_Lean_registerBuiltinAttribute___closed__1(void){
_start:
{
lean_object* v___x_524_; lean_object* v___x_525_; 
v___x_524_ = ((lean_object*)(l_Lean_registerBuiltinAttribute___closed__0));
v___x_525_ = lean_mk_io_user_error(v___x_524_);
return v___x_525_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerBuiltinAttribute(lean_object* v_attr_528_){
_start:
{
lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v_toAttributeImplCore_532_; lean_object* v_name_533_; uint8_t v___x_534_; 
v___x_530_ = l_Lean_attributeMapRef;
v___x_531_ = lean_st_ref_get(v___x_530_);
v_toAttributeImplCore_532_ = lean_ctor_get(v_attr_528_, 0);
v_name_533_ = lean_ctor_get(v_toAttributeImplCore_532_, 1);
lean_inc(v_name_533_);
v___x_534_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(v___x_531_, v_name_533_);
lean_dec(v___x_531_);
if (v___x_534_ == 0)
{
lean_object* v___x_535_; 
v___x_535_ = l_Lean_initializing();
if (lean_obj_tag(v___x_535_) == 0)
{
lean_object* v_a_536_; lean_object* v___x_538_; uint8_t v_isShared_539_; uint8_t v_isSharedCheck_551_; 
v_a_536_ = lean_ctor_get(v___x_535_, 0);
v_isSharedCheck_551_ = !lean_is_exclusive(v___x_535_);
if (v_isSharedCheck_551_ == 0)
{
v___x_538_ = v___x_535_;
v_isShared_539_ = v_isSharedCheck_551_;
goto v_resetjp_537_;
}
else
{
lean_inc(v_a_536_);
lean_dec(v___x_535_);
v___x_538_ = lean_box(0);
v_isShared_539_ = v_isSharedCheck_551_;
goto v_resetjp_537_;
}
v_resetjp_537_:
{
uint8_t v___x_540_; 
v___x_540_ = lean_unbox(v_a_536_);
lean_dec(v_a_536_);
if (v___x_540_ == 0)
{
lean_object* v___x_541_; lean_object* v___x_543_; 
lean_dec(v_name_533_);
lean_dec_ref(v_attr_528_);
v___x_541_ = lean_obj_once(&l_Lean_registerBuiltinAttribute___closed__1, &l_Lean_registerBuiltinAttribute___closed__1_once, _init_l_Lean_registerBuiltinAttribute___closed__1);
if (v_isShared_539_ == 0)
{
lean_ctor_set_tag(v___x_538_, 1);
lean_ctor_set(v___x_538_, 0, v___x_541_);
v___x_543_ = v___x_538_;
goto v_reusejp_542_;
}
else
{
lean_object* v_reuseFailAlloc_544_; 
v_reuseFailAlloc_544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_544_, 0, v___x_541_);
v___x_543_ = v_reuseFailAlloc_544_;
goto v_reusejp_542_;
}
v_reusejp_542_:
{
return v___x_543_;
}
}
else
{
lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_549_; 
v___x_545_ = lean_st_ref_take(v___x_530_);
v___x_546_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1___redArg(v___x_545_, v_name_533_, v_attr_528_);
v___x_547_ = lean_st_ref_set(v___x_530_, v___x_546_);
if (v_isShared_539_ == 0)
{
lean_ctor_set(v___x_538_, 0, v___x_547_);
v___x_549_ = v___x_538_;
goto v_reusejp_548_;
}
else
{
lean_object* v_reuseFailAlloc_550_; 
v_reuseFailAlloc_550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_550_, 0, v___x_547_);
v___x_549_ = v_reuseFailAlloc_550_;
goto v_reusejp_548_;
}
v_reusejp_548_:
{
return v___x_549_;
}
}
}
}
else
{
lean_object* v_a_552_; lean_object* v___x_554_; uint8_t v_isShared_555_; uint8_t v_isSharedCheck_559_; 
lean_dec(v_name_533_);
lean_dec_ref(v_attr_528_);
v_a_552_ = lean_ctor_get(v___x_535_, 0);
v_isSharedCheck_559_ = !lean_is_exclusive(v___x_535_);
if (v_isSharedCheck_559_ == 0)
{
v___x_554_ = v___x_535_;
v_isShared_555_ = v_isSharedCheck_559_;
goto v_resetjp_553_;
}
else
{
lean_inc(v_a_552_);
lean_dec(v___x_535_);
v___x_554_ = lean_box(0);
v_isShared_555_ = v_isSharedCheck_559_;
goto v_resetjp_553_;
}
v_resetjp_553_:
{
lean_object* v___x_557_; 
if (v_isShared_555_ == 0)
{
v___x_557_ = v___x_554_;
goto v_reusejp_556_;
}
else
{
lean_object* v_reuseFailAlloc_558_; 
v_reuseFailAlloc_558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_558_, 0, v_a_552_);
v___x_557_ = v_reuseFailAlloc_558_;
goto v_reusejp_556_;
}
v_reusejp_556_:
{
return v___x_557_;
}
}
}
}
else
{
lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; 
lean_dec_ref(v_attr_528_);
v___x_560_ = ((lean_object*)(l_Lean_registerBuiltinAttribute___closed__2));
v___x_561_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_533_, v___x_534_);
v___x_562_ = lean_string_append(v___x_560_, v___x_561_);
lean_dec_ref(v___x_561_);
v___x_563_ = ((lean_object*)(l_Lean_registerBuiltinAttribute___closed__3));
v___x_564_ = lean_string_append(v___x_562_, v___x_563_);
v___x_565_ = lean_mk_io_user_error(v___x_564_);
v___x_566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_566_, 0, v___x_565_);
return v___x_566_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerBuiltinAttribute___boxed(lean_object* v_attr_567_, lean_object* v_a_568_){
_start:
{
lean_object* v_res_569_; 
v_res_569_ = l_Lean_registerBuiltinAttribute(v_attr_567_);
return v_res_569_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0(lean_object* v_00_u03b2_570_, lean_object* v_m_571_, lean_object* v_a_572_){
_start:
{
uint8_t v___x_573_; 
v___x_573_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(v_m_571_, v_a_572_);
return v___x_573_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___boxed(lean_object* v_00_u03b2_574_, lean_object* v_m_575_, lean_object* v_a_576_){
_start:
{
uint8_t v_res_577_; lean_object* v_r_578_; 
v_res_577_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0(v_00_u03b2_574_, v_m_575_, v_a_576_);
lean_dec(v_a_576_);
lean_dec_ref(v_m_575_);
v_r_578_ = lean_box(v_res_577_);
return v_r_578_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1(lean_object* v_00_u03b2_579_, lean_object* v_m_580_, lean_object* v_a_581_, lean_object* v_b_582_){
_start:
{
lean_object* v___x_583_; 
v___x_583_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1___redArg(v_m_580_, v_a_581_, v_b_582_);
return v___x_583_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0_spec__0(lean_object* v_00_u03b2_584_, lean_object* v_a_585_, lean_object* v_x_586_){
_start:
{
uint8_t v___x_587_; 
v___x_587_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0_spec__0___redArg(v_a_585_, v_x_586_);
return v___x_587_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0_spec__0___boxed(lean_object* v_00_u03b2_588_, lean_object* v_a_589_, lean_object* v_x_590_){
_start:
{
uint8_t v_res_591_; lean_object* v_r_592_; 
v_res_591_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0_spec__0(v_00_u03b2_588_, v_a_589_, v_x_590_);
lean_dec(v_x_590_);
lean_dec(v_a_589_);
v_r_592_ = lean_box(v_res_591_);
return v_r_592_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2(lean_object* v_00_u03b2_593_, lean_object* v_data_594_){
_start:
{
lean_object* v___x_595_; 
v___x_595_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2___redArg(v_data_594_);
return v___x_595_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__3(lean_object* v_00_u03b2_596_, lean_object* v_a_597_, lean_object* v_b_598_, lean_object* v_x_599_){
_start:
{
lean_object* v___x_600_; 
v___x_600_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__3___redArg(v_a_597_, v_b_598_, v_x_599_);
return v___x_600_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_601_, lean_object* v_i_602_, lean_object* v_source_603_, lean_object* v_target_604_){
_start:
{
lean_object* v___x_605_; 
v___x_605_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2_spec__3___redArg(v_i_602_, v_source_603_, v_target_604_);
return v___x_605_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_606_, lean_object* v_x_607_, lean_object* v_x_608_){
_start:
{
lean_object* v___x_609_; 
v___x_609_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2_spec__3_spec__4___redArg(v_x_607_, v_x_608_);
return v___x_609_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0_spec__0_spec__1___closed__0(void){
_start:
{
lean_object* v___x_610_; 
v___x_610_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_610_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0_spec__0_spec__1___closed__1(void){
_start:
{
lean_object* v___x_611_; lean_object* v___x_612_; 
v___x_611_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0_spec__0_spec__1___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0_spec__0_spec__1___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0_spec__0_spec__1___closed__0);
v___x_612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_612_, 0, v___x_611_);
return v___x_612_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0_spec__0_spec__1___closed__2(void){
_start:
{
lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; 
v___x_613_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0_spec__0_spec__1___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0_spec__0_spec__1___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0_spec__0_spec__1___closed__1);
v___x_614_ = lean_unsigned_to_nat(0u);
v___x_615_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_615_, 0, v___x_614_);
lean_ctor_set(v___x_615_, 1, v___x_614_);
lean_ctor_set(v___x_615_, 2, v___x_614_);
lean_ctor_set(v___x_615_, 3, v___x_614_);
lean_ctor_set(v___x_615_, 4, v___x_613_);
lean_ctor_set(v___x_615_, 5, v___x_613_);
lean_ctor_set(v___x_615_, 6, v___x_613_);
lean_ctor_set(v___x_615_, 7, v___x_613_);
lean_ctor_set(v___x_615_, 8, v___x_613_);
lean_ctor_set(v___x_615_, 9, v___x_613_);
return v___x_615_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0_spec__0_spec__1___closed__3(void){
_start:
{
lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; 
v___x_616_ = lean_unsigned_to_nat(32u);
v___x_617_ = lean_mk_empty_array_with_capacity(v___x_616_);
v___x_618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_618_, 0, v___x_617_);
return v___x_618_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0_spec__0_spec__1___closed__4(void){
_start:
{
size_t v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; 
v___x_619_ = ((size_t)5ULL);
v___x_620_ = lean_unsigned_to_nat(0u);
v___x_621_ = lean_unsigned_to_nat(32u);
v___x_622_ = lean_mk_empty_array_with_capacity(v___x_621_);
v___x_623_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0_spec__0_spec__1___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0_spec__0_spec__1___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0_spec__0_spec__1___closed__3);
v___x_624_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_624_, 0, v___x_623_);
lean_ctor_set(v___x_624_, 1, v___x_622_);
lean_ctor_set(v___x_624_, 2, v___x_620_);
lean_ctor_set(v___x_624_, 3, v___x_620_);
lean_ctor_set_usize(v___x_624_, 4, v___x_619_);
return v___x_624_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0_spec__0_spec__1___closed__5(void){
_start:
{
lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; 
v___x_625_ = lean_box(1);
v___x_626_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0_spec__0_spec__1___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0_spec__0_spec__1___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0_spec__0_spec__1___closed__4);
v___x_627_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0_spec__0_spec__1___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0_spec__0_spec__1___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0_spec__0_spec__1___closed__1);
v___x_628_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_628_, 0, v___x_627_);
lean_ctor_set(v___x_628_, 1, v___x_626_);
lean_ctor_set(v___x_628_, 2, v___x_625_);
return v___x_628_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0_spec__0_spec__1(lean_object* v_msgData_629_, lean_object* v___y_630_, lean_object* v___y_631_){
_start:
{
lean_object* v___x_633_; lean_object* v_env_634_; lean_object* v_options_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; 
v___x_633_ = lean_st_ref_get(v___y_631_);
v_env_634_ = lean_ctor_get(v___x_633_, 0);
lean_inc_ref(v_env_634_);
lean_dec(v___x_633_);
v_options_635_ = lean_ctor_get(v___y_630_, 2);
v___x_636_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0_spec__0_spec__1___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0_spec__0_spec__1___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0_spec__0_spec__1___closed__2);
v___x_637_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0_spec__0_spec__1___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0_spec__0_spec__1___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0_spec__0_spec__1___closed__5);
lean_inc_ref(v_options_635_);
v___x_638_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_638_, 0, v_env_634_);
lean_ctor_set(v___x_638_, 1, v___x_636_);
lean_ctor_set(v___x_638_, 2, v___x_637_);
lean_ctor_set(v___x_638_, 3, v_options_635_);
v___x_639_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_639_, 0, v___x_638_);
lean_ctor_set(v___x_639_, 1, v_msgData_629_);
v___x_640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_640_, 0, v___x_639_);
return v___x_640_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0_spec__0_spec__1___boxed(lean_object* v_msgData_641_, lean_object* v___y_642_, lean_object* v___y_643_, lean_object* v___y_644_){
_start:
{
lean_object* v_res_645_; 
v_res_645_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0_spec__0_spec__1(v_msgData_641_, v___y_642_, v___y_643_);
lean_dec(v___y_643_);
lean_dec_ref(v___y_642_);
return v_res_645_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0_spec__0___redArg(lean_object* v_msg_646_, lean_object* v___y_647_, lean_object* v___y_648_){
_start:
{
lean_object* v_ref_650_; lean_object* v___x_651_; lean_object* v_a_652_; lean_object* v___x_654_; uint8_t v_isShared_655_; uint8_t v_isSharedCheck_660_; 
v_ref_650_ = lean_ctor_get(v___y_647_, 5);
v___x_651_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0_spec__0_spec__1(v_msg_646_, v___y_647_, v___y_648_);
v_a_652_ = lean_ctor_get(v___x_651_, 0);
v_isSharedCheck_660_ = !lean_is_exclusive(v___x_651_);
if (v_isSharedCheck_660_ == 0)
{
v___x_654_ = v___x_651_;
v_isShared_655_ = v_isSharedCheck_660_;
goto v_resetjp_653_;
}
else
{
lean_inc(v_a_652_);
lean_dec(v___x_651_);
v___x_654_ = lean_box(0);
v_isShared_655_ = v_isSharedCheck_660_;
goto v_resetjp_653_;
}
v_resetjp_653_:
{
lean_object* v___x_656_; lean_object* v___x_658_; 
lean_inc(v_ref_650_);
v___x_656_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_656_, 0, v_ref_650_);
lean_ctor_set(v___x_656_, 1, v_a_652_);
if (v_isShared_655_ == 0)
{
lean_ctor_set_tag(v___x_654_, 1);
lean_ctor_set(v___x_654_, 0, v___x_656_);
v___x_658_ = v___x_654_;
goto v_reusejp_657_;
}
else
{
lean_object* v_reuseFailAlloc_659_; 
v_reuseFailAlloc_659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_659_, 0, v___x_656_);
v___x_658_ = v_reuseFailAlloc_659_;
goto v_reusejp_657_;
}
v_reusejp_657_:
{
return v___x_658_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0_spec__0___redArg___boxed(lean_object* v_msg_661_, lean_object* v___y_662_, lean_object* v___y_663_, lean_object* v___y_664_){
_start:
{
lean_object* v_res_665_; 
v_res_665_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0_spec__0___redArg(v_msg_661_, v___y_662_, v___y_663_);
lean_dec(v___y_663_);
lean_dec_ref(v___y_662_);
return v_res_665_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg(lean_object* v_ref_666_, lean_object* v_msg_667_, lean_object* v___y_668_, lean_object* v___y_669_){
_start:
{
lean_object* v_fileName_671_; lean_object* v_fileMap_672_; lean_object* v_options_673_; lean_object* v_currRecDepth_674_; lean_object* v_maxRecDepth_675_; lean_object* v_ref_676_; lean_object* v_currNamespace_677_; lean_object* v_openDecls_678_; lean_object* v_initHeartbeats_679_; lean_object* v_maxHeartbeats_680_; lean_object* v_quotContext_681_; lean_object* v_currMacroScope_682_; uint8_t v_diag_683_; lean_object* v_cancelTk_x3f_684_; uint8_t v_suppressElabErrors_685_; lean_object* v_inheritedTraceOptions_686_; lean_object* v_ref_687_; lean_object* v___x_688_; lean_object* v___x_689_; 
v_fileName_671_ = lean_ctor_get(v___y_668_, 0);
v_fileMap_672_ = lean_ctor_get(v___y_668_, 1);
v_options_673_ = lean_ctor_get(v___y_668_, 2);
v_currRecDepth_674_ = lean_ctor_get(v___y_668_, 3);
v_maxRecDepth_675_ = lean_ctor_get(v___y_668_, 4);
v_ref_676_ = lean_ctor_get(v___y_668_, 5);
v_currNamespace_677_ = lean_ctor_get(v___y_668_, 6);
v_openDecls_678_ = lean_ctor_get(v___y_668_, 7);
v_initHeartbeats_679_ = lean_ctor_get(v___y_668_, 8);
v_maxHeartbeats_680_ = lean_ctor_get(v___y_668_, 9);
v_quotContext_681_ = lean_ctor_get(v___y_668_, 10);
v_currMacroScope_682_ = lean_ctor_get(v___y_668_, 11);
v_diag_683_ = lean_ctor_get_uint8(v___y_668_, sizeof(void*)*14);
v_cancelTk_x3f_684_ = lean_ctor_get(v___y_668_, 12);
v_suppressElabErrors_685_ = lean_ctor_get_uint8(v___y_668_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_686_ = lean_ctor_get(v___y_668_, 13);
v_ref_687_ = l_Lean_replaceRef(v_ref_666_, v_ref_676_);
lean_inc_ref(v_inheritedTraceOptions_686_);
lean_inc(v_cancelTk_x3f_684_);
lean_inc(v_currMacroScope_682_);
lean_inc(v_quotContext_681_);
lean_inc(v_maxHeartbeats_680_);
lean_inc(v_initHeartbeats_679_);
lean_inc(v_openDecls_678_);
lean_inc(v_currNamespace_677_);
lean_inc(v_maxRecDepth_675_);
lean_inc(v_currRecDepth_674_);
lean_inc_ref(v_options_673_);
lean_inc_ref(v_fileMap_672_);
lean_inc_ref(v_fileName_671_);
v___x_688_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_688_, 0, v_fileName_671_);
lean_ctor_set(v___x_688_, 1, v_fileMap_672_);
lean_ctor_set(v___x_688_, 2, v_options_673_);
lean_ctor_set(v___x_688_, 3, v_currRecDepth_674_);
lean_ctor_set(v___x_688_, 4, v_maxRecDepth_675_);
lean_ctor_set(v___x_688_, 5, v_ref_687_);
lean_ctor_set(v___x_688_, 6, v_currNamespace_677_);
lean_ctor_set(v___x_688_, 7, v_openDecls_678_);
lean_ctor_set(v___x_688_, 8, v_initHeartbeats_679_);
lean_ctor_set(v___x_688_, 9, v_maxHeartbeats_680_);
lean_ctor_set(v___x_688_, 10, v_quotContext_681_);
lean_ctor_set(v___x_688_, 11, v_currMacroScope_682_);
lean_ctor_set(v___x_688_, 12, v_cancelTk_x3f_684_);
lean_ctor_set(v___x_688_, 13, v_inheritedTraceOptions_686_);
lean_ctor_set_uint8(v___x_688_, sizeof(void*)*14, v_diag_683_);
lean_ctor_set_uint8(v___x_688_, sizeof(void*)*14 + 1, v_suppressElabErrors_685_);
v___x_689_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0_spec__0___redArg(v_msg_667_, v___x_688_, v___y_669_);
lean_dec_ref(v___x_688_);
return v___x_689_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg___boxed(lean_object* v_ref_690_, lean_object* v_msg_691_, lean_object* v___y_692_, lean_object* v___y_693_, lean_object* v___y_694_){
_start:
{
lean_object* v_res_695_; 
v_res_695_ = l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg(v_ref_690_, v_msg_691_, v___y_692_, v___y_693_);
lean_dec(v___y_693_);
lean_dec_ref(v___y_692_);
lean_dec(v_ref_690_);
return v_res_695_;
}
}
static lean_object* _init_l_Lean_Attribute_Builtin_ensureNoArgs___closed__4(void){
_start:
{
lean_object* v___x_704_; lean_object* v___x_705_; 
v___x_704_ = ((lean_object*)(l_Lean_Attribute_Builtin_ensureNoArgs___closed__3));
v___x_705_ = l_Lean_stringToMessageData(v___x_704_);
return v___x_705_;
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_ensureNoArgs(lean_object* v_stx_712_, lean_object* v_a_713_, lean_object* v_a_714_){
_start:
{
lean_object* v___x_716_; uint8_t v___y_727_; lean_object* v___x_733_; uint8_t v___x_734_; 
lean_inc(v_stx_712_);
v___x_716_ = l_Lean_Syntax_getKind(v_stx_712_);
v___x_733_ = ((lean_object*)(l_Lean_Attribute_Builtin_ensureNoArgs___closed__6));
v___x_734_ = lean_name_eq(v___x_716_, v___x_733_);
if (v___x_734_ == 0)
{
v___y_727_ = v___x_734_;
goto v___jp_726_;
}
else
{
lean_object* v___x_735_; lean_object* v___x_736_; uint8_t v___x_737_; 
v___x_735_ = lean_unsigned_to_nat(1u);
v___x_736_ = l_Lean_Syntax_getArg(v_stx_712_, v___x_735_);
v___x_737_ = l_Lean_Syntax_isNone(v___x_736_);
lean_dec(v___x_736_);
v___y_727_ = v___x_737_;
goto v___jp_726_;
}
v___jp_717_:
{
lean_object* v___x_718_; uint8_t v___x_719_; 
v___x_718_ = ((lean_object*)(l_Lean_Attribute_Builtin_ensureNoArgs___closed__2));
v___x_719_ = lean_name_eq(v___x_716_, v___x_718_);
lean_dec(v___x_716_);
if (v___x_719_ == 0)
{
if (lean_obj_tag(v_stx_712_) == 0)
{
lean_object* v___x_720_; lean_object* v___x_721_; 
v___x_720_ = lean_box(0);
v___x_721_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_721_, 0, v___x_720_);
return v___x_721_;
}
else
{
lean_object* v___x_722_; lean_object* v___x_723_; 
v___x_722_ = lean_obj_once(&l_Lean_Attribute_Builtin_ensureNoArgs___closed__4, &l_Lean_Attribute_Builtin_ensureNoArgs___closed__4_once, _init_l_Lean_Attribute_Builtin_ensureNoArgs___closed__4);
v___x_723_ = l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg(v_stx_712_, v___x_722_, v_a_713_, v_a_714_);
lean_dec(v_stx_712_);
return v___x_723_;
}
}
else
{
lean_object* v___x_724_; lean_object* v___x_725_; 
lean_dec(v_stx_712_);
v___x_724_ = lean_box(0);
v___x_725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_725_, 0, v___x_724_);
return v___x_725_;
}
}
v___jp_726_:
{
if (v___y_727_ == 0)
{
goto v___jp_717_;
}
else
{
lean_object* v___x_728_; lean_object* v___x_729_; uint8_t v___x_730_; 
v___x_728_ = lean_unsigned_to_nat(2u);
v___x_729_ = l_Lean_Syntax_getArg(v_stx_712_, v___x_728_);
v___x_730_ = l_Lean_Syntax_isNone(v___x_729_);
lean_dec(v___x_729_);
if (v___x_730_ == 0)
{
goto v___jp_717_;
}
else
{
lean_object* v___x_731_; lean_object* v___x_732_; 
lean_dec(v___x_716_);
lean_dec(v_stx_712_);
v___x_731_ = lean_box(0);
v___x_732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_732_, 0, v___x_731_);
return v___x_732_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_ensureNoArgs___boxed(lean_object* v_stx_738_, lean_object* v_a_739_, lean_object* v_a_740_, lean_object* v_a_741_){
_start:
{
lean_object* v_res_742_; 
v_res_742_ = l_Lean_Attribute_Builtin_ensureNoArgs(v_stx_738_, v_a_739_, v_a_740_);
lean_dec(v_a_740_);
lean_dec_ref(v_a_739_);
return v_res_742_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0(lean_object* v_00_u03b1_743_, lean_object* v_ref_744_, lean_object* v_msg_745_, lean_object* v___y_746_, lean_object* v___y_747_){
_start:
{
lean_object* v___x_749_; 
v___x_749_ = l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg(v_ref_744_, v_msg_745_, v___y_746_, v___y_747_);
return v___x_749_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___boxed(lean_object* v_00_u03b1_750_, lean_object* v_ref_751_, lean_object* v_msg_752_, lean_object* v___y_753_, lean_object* v___y_754_, lean_object* v___y_755_){
_start:
{
lean_object* v_res_756_; 
v_res_756_ = l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0(v_00_u03b1_750_, v_ref_751_, v_msg_752_, v___y_753_, v___y_754_);
lean_dec(v___y_754_);
lean_dec_ref(v___y_753_);
lean_dec(v_ref_751_);
return v_res_756_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0_spec__0(lean_object* v_00_u03b1_757_, lean_object* v_msg_758_, lean_object* v___y_759_, lean_object* v___y_760_){
_start:
{
lean_object* v___x_762_; 
v___x_762_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0_spec__0___redArg(v_msg_758_, v___y_759_, v___y_760_);
return v___x_762_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0_spec__0___boxed(lean_object* v_00_u03b1_763_, lean_object* v_msg_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_){
_start:
{
lean_object* v_res_768_; 
v_res_768_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0_spec__0(v_00_u03b1_763_, v_msg_764_, v___y_765_, v___y_766_);
lean_dec(v___y_766_);
lean_dec_ref(v___y_765_);
return v_res_768_;
}
}
static lean_object* _init_l_Lean_Attribute_Builtin_getIdent_x3f___closed__5(void){
_start:
{
lean_object* v___x_782_; lean_object* v___x_783_; 
v___x_782_ = ((lean_object*)(l_Lean_Attribute_Builtin_getIdent_x3f___closed__4));
v___x_783_ = l_Lean_stringToMessageData(v___x_782_);
return v___x_783_;
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getIdent_x3f(lean_object* v_stx_784_, lean_object* v_a_785_, lean_object* v_a_786_){
_start:
{
lean_object* v___x_796_; lean_object* v___x_797_; uint8_t v___x_798_; 
lean_inc(v_stx_784_);
v___x_796_ = l_Lean_Syntax_getKind(v_stx_784_);
v___x_797_ = ((lean_object*)(l_Lean_Attribute_Builtin_ensureNoArgs___closed__6));
v___x_798_ = lean_name_eq(v___x_796_, v___x_797_);
if (v___x_798_ == 0)
{
lean_object* v___x_799_; uint8_t v___x_800_; 
v___x_799_ = ((lean_object*)(l_Lean_Attribute_Builtin_getIdent_x3f___closed__1));
v___x_800_ = lean_name_eq(v___x_796_, v___x_799_);
if (v___x_800_ == 0)
{
lean_object* v___x_801_; uint8_t v___x_802_; 
v___x_801_ = ((lean_object*)(l_Lean_Attribute_Builtin_getIdent_x3f___closed__3));
v___x_802_ = lean_name_eq(v___x_796_, v___x_801_);
lean_dec(v___x_796_);
if (v___x_802_ == 0)
{
lean_object* v___x_803_; lean_object* v___x_804_; 
v___x_803_ = lean_obj_once(&l_Lean_Attribute_Builtin_getIdent_x3f___closed__5, &l_Lean_Attribute_Builtin_getIdent_x3f___closed__5_once, _init_l_Lean_Attribute_Builtin_getIdent_x3f___closed__5);
v___x_804_ = l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg(v_stx_784_, v___x_803_, v_a_785_, v_a_786_);
lean_dec(v_stx_784_);
return v___x_804_;
}
else
{
goto v___jp_788_;
}
}
else
{
lean_dec(v___x_796_);
goto v___jp_788_;
}
}
else
{
lean_object* v___x_805_; lean_object* v___x_806_; uint8_t v___x_807_; 
lean_dec(v___x_796_);
v___x_805_ = lean_unsigned_to_nat(1u);
v___x_806_ = l_Lean_Syntax_getArg(v_stx_784_, v___x_805_);
lean_dec(v_stx_784_);
v___x_807_ = l_Lean_Syntax_isNone(v___x_806_);
if (v___x_807_ == 0)
{
if (v___x_798_ == 0)
{
lean_dec(v___x_806_);
goto v___jp_793_;
}
else
{
lean_object* v___x_808_; lean_object* v___x_809_; uint8_t v___x_810_; 
v___x_808_ = lean_unsigned_to_nat(0u);
v___x_809_ = l_Lean_Syntax_getArg(v___x_806_, v___x_808_);
lean_dec(v___x_806_);
v___x_810_ = l_Lean_Syntax_isIdent(v___x_809_);
if (v___x_810_ == 0)
{
lean_dec(v___x_809_);
goto v___jp_793_;
}
else
{
lean_object* v___x_811_; lean_object* v___x_812_; 
v___x_811_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_811_, 0, v___x_809_);
v___x_812_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_812_, 0, v___x_811_);
return v___x_812_;
}
}
}
else
{
lean_dec(v___x_806_);
goto v___jp_793_;
}
}
v___jp_788_:
{
lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; 
v___x_789_ = lean_unsigned_to_nat(1u);
v___x_790_ = l_Lean_Syntax_getArg(v_stx_784_, v___x_789_);
lean_dec(v_stx_784_);
v___x_791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_791_, 0, v___x_790_);
v___x_792_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_792_, 0, v___x_791_);
return v___x_792_;
}
v___jp_793_:
{
lean_object* v___x_794_; lean_object* v___x_795_; 
v___x_794_ = lean_box(0);
v___x_795_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_795_, 0, v___x_794_);
return v___x_795_;
}
}
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
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getIdent(lean_object* v_stx_821_, lean_object* v_a_822_, lean_object* v_a_823_){
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
lean_dec_ref(v_a_826_);
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
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getIdent___boxed(lean_object* v_stx_848_, lean_object* v_a_849_, lean_object* v_a_850_, lean_object* v_a_851_){
_start:
{
lean_object* v_res_852_; 
v_res_852_ = l_Lean_Attribute_Builtin_getIdent(v_stx_848_, v_a_849_, v_a_850_);
lean_dec(v_a_850_);
lean_dec_ref(v_a_849_);
return v_res_852_;
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getId_x3f(lean_object* v_stx_853_, lean_object* v_a_854_, lean_object* v_a_855_){
_start:
{
lean_object* v___x_857_; 
v___x_857_ = l_Lean_Attribute_Builtin_getIdent_x3f(v_stx_853_, v_a_854_, v_a_855_);
if (lean_obj_tag(v___x_857_) == 0)
{
lean_object* v_a_858_; lean_object* v___x_860_; uint8_t v_isShared_861_; uint8_t v_isSharedCheck_878_; 
v_a_858_ = lean_ctor_get(v___x_857_, 0);
v_isSharedCheck_878_ = !lean_is_exclusive(v___x_857_);
if (v_isSharedCheck_878_ == 0)
{
v___x_860_ = v___x_857_;
v_isShared_861_ = v_isSharedCheck_878_;
goto v_resetjp_859_;
}
else
{
lean_inc(v_a_858_);
lean_dec(v___x_857_);
v___x_860_ = lean_box(0);
v_isShared_861_ = v_isSharedCheck_878_;
goto v_resetjp_859_;
}
v_resetjp_859_:
{
if (lean_obj_tag(v_a_858_) == 0)
{
lean_object* v___x_862_; lean_object* v___x_864_; 
v___x_862_ = lean_box(0);
if (v_isShared_861_ == 0)
{
lean_ctor_set(v___x_860_, 0, v___x_862_);
v___x_864_ = v___x_860_;
goto v_reusejp_863_;
}
else
{
lean_object* v_reuseFailAlloc_865_; 
v_reuseFailAlloc_865_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_865_, 0, v___x_862_);
v___x_864_ = v_reuseFailAlloc_865_;
goto v_reusejp_863_;
}
v_reusejp_863_:
{
return v___x_864_;
}
}
else
{
lean_object* v_val_866_; lean_object* v___x_868_; uint8_t v_isShared_869_; uint8_t v_isSharedCheck_877_; 
v_val_866_ = lean_ctor_get(v_a_858_, 0);
v_isSharedCheck_877_ = !lean_is_exclusive(v_a_858_);
if (v_isSharedCheck_877_ == 0)
{
v___x_868_ = v_a_858_;
v_isShared_869_ = v_isSharedCheck_877_;
goto v_resetjp_867_;
}
else
{
lean_inc(v_val_866_);
lean_dec(v_a_858_);
v___x_868_ = lean_box(0);
v_isShared_869_ = v_isSharedCheck_877_;
goto v_resetjp_867_;
}
v_resetjp_867_:
{
lean_object* v___x_870_; lean_object* v___x_872_; 
v___x_870_ = l_Lean_Syntax_getId(v_val_866_);
lean_dec(v_val_866_);
if (v_isShared_869_ == 0)
{
lean_ctor_set(v___x_868_, 0, v___x_870_);
v___x_872_ = v___x_868_;
goto v_reusejp_871_;
}
else
{
lean_object* v_reuseFailAlloc_876_; 
v_reuseFailAlloc_876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_876_, 0, v___x_870_);
v___x_872_ = v_reuseFailAlloc_876_;
goto v_reusejp_871_;
}
v_reusejp_871_:
{
lean_object* v___x_874_; 
if (v_isShared_861_ == 0)
{
lean_ctor_set(v___x_860_, 0, v___x_872_);
v___x_874_ = v___x_860_;
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
}
}
}
else
{
lean_object* v_a_879_; lean_object* v___x_881_; uint8_t v_isShared_882_; uint8_t v_isSharedCheck_886_; 
v_a_879_ = lean_ctor_get(v___x_857_, 0);
v_isSharedCheck_886_ = !lean_is_exclusive(v___x_857_);
if (v_isSharedCheck_886_ == 0)
{
v___x_881_ = v___x_857_;
v_isShared_882_ = v_isSharedCheck_886_;
goto v_resetjp_880_;
}
else
{
lean_inc(v_a_879_);
lean_dec(v___x_857_);
v___x_881_ = lean_box(0);
v_isShared_882_ = v_isSharedCheck_886_;
goto v_resetjp_880_;
}
v_resetjp_880_:
{
lean_object* v___x_884_; 
if (v_isShared_882_ == 0)
{
v___x_884_ = v___x_881_;
goto v_reusejp_883_;
}
else
{
lean_object* v_reuseFailAlloc_885_; 
v_reuseFailAlloc_885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_885_, 0, v_a_879_);
v___x_884_ = v_reuseFailAlloc_885_;
goto v_reusejp_883_;
}
v_reusejp_883_:
{
return v___x_884_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getId_x3f___boxed(lean_object* v_stx_887_, lean_object* v_a_888_, lean_object* v_a_889_, lean_object* v_a_890_){
_start:
{
lean_object* v_res_891_; 
v_res_891_ = l_Lean_Attribute_Builtin_getId_x3f(v_stx_887_, v_a_888_, v_a_889_);
lean_dec(v_a_889_);
lean_dec_ref(v_a_888_);
return v_res_891_;
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getId(lean_object* v_stx_892_, lean_object* v_a_893_, lean_object* v_a_894_){
_start:
{
lean_object* v___x_896_; 
v___x_896_ = l_Lean_Attribute_Builtin_getIdent(v_stx_892_, v_a_893_, v_a_894_);
if (lean_obj_tag(v___x_896_) == 0)
{
lean_object* v_a_897_; lean_object* v___x_899_; uint8_t v_isShared_900_; uint8_t v_isSharedCheck_905_; 
v_a_897_ = lean_ctor_get(v___x_896_, 0);
v_isSharedCheck_905_ = !lean_is_exclusive(v___x_896_);
if (v_isSharedCheck_905_ == 0)
{
v___x_899_ = v___x_896_;
v_isShared_900_ = v_isSharedCheck_905_;
goto v_resetjp_898_;
}
else
{
lean_inc(v_a_897_);
lean_dec(v___x_896_);
v___x_899_ = lean_box(0);
v_isShared_900_ = v_isSharedCheck_905_;
goto v_resetjp_898_;
}
v_resetjp_898_:
{
lean_object* v___x_901_; lean_object* v___x_903_; 
v___x_901_ = l_Lean_Syntax_getId(v_a_897_);
lean_dec(v_a_897_);
if (v_isShared_900_ == 0)
{
lean_ctor_set(v___x_899_, 0, v___x_901_);
v___x_903_ = v___x_899_;
goto v_reusejp_902_;
}
else
{
lean_object* v_reuseFailAlloc_904_; 
v_reuseFailAlloc_904_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_904_, 0, v___x_901_);
v___x_903_ = v_reuseFailAlloc_904_;
goto v_reusejp_902_;
}
v_reusejp_902_:
{
return v___x_903_;
}
}
}
else
{
lean_object* v_a_906_; lean_object* v___x_908_; uint8_t v_isShared_909_; uint8_t v_isSharedCheck_913_; 
v_a_906_ = lean_ctor_get(v___x_896_, 0);
v_isSharedCheck_913_ = !lean_is_exclusive(v___x_896_);
if (v_isSharedCheck_913_ == 0)
{
v___x_908_ = v___x_896_;
v_isShared_909_ = v_isSharedCheck_913_;
goto v_resetjp_907_;
}
else
{
lean_inc(v_a_906_);
lean_dec(v___x_896_);
v___x_908_ = lean_box(0);
v_isShared_909_ = v_isSharedCheck_913_;
goto v_resetjp_907_;
}
v_resetjp_907_:
{
lean_object* v___x_911_; 
if (v_isShared_909_ == 0)
{
v___x_911_ = v___x_908_;
goto v_reusejp_910_;
}
else
{
lean_object* v_reuseFailAlloc_912_; 
v_reuseFailAlloc_912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_912_, 0, v_a_906_);
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
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getId___boxed(lean_object* v_stx_914_, lean_object* v_a_915_, lean_object* v_a_916_, lean_object* v_a_917_){
_start:
{
lean_object* v_res_918_; 
v_res_918_ = l_Lean_Attribute_Builtin_getId(v_stx_914_, v_a_915_, v_a_916_);
lean_dec(v_a_916_);
lean_dec_ref(v_a_915_);
return v_res_918_;
}
}
static lean_object* _init_l_Lean_getAttrParamOptPrio___closed__1(void){
_start:
{
lean_object* v___x_920_; lean_object* v___x_921_; 
v___x_920_ = ((lean_object*)(l_Lean_getAttrParamOptPrio___closed__0));
v___x_921_ = l_Lean_stringToMessageData(v___x_920_);
return v___x_921_;
}
}
LEAN_EXPORT lean_object* l_Lean_getAttrParamOptPrio(lean_object* v_optPrioStx_922_, lean_object* v_a_923_, lean_object* v_a_924_){
_start:
{
uint8_t v___x_926_; 
v___x_926_ = l_Lean_Syntax_isNone(v_optPrioStx_922_);
if (v___x_926_ == 0)
{
lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; 
v___x_927_ = lean_unsigned_to_nat(0u);
v___x_928_ = l_Lean_Syntax_getArg(v_optPrioStx_922_, v___x_927_);
v___x_929_ = l_Lean_Syntax_isNatLit_x3f(v___x_928_);
lean_dec(v___x_928_);
if (lean_obj_tag(v___x_929_) == 0)
{
lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; 
v___x_930_ = lean_obj_once(&l_Lean_getAttrParamOptPrio___closed__1, &l_Lean_getAttrParamOptPrio___closed__1_once, _init_l_Lean_getAttrParamOptPrio___closed__1);
lean_inc(v_optPrioStx_922_);
v___x_931_ = l_Lean_MessageData_ofSyntax(v_optPrioStx_922_);
v___x_932_ = l_Lean_indentD(v___x_931_);
v___x_933_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_933_, 0, v___x_930_);
lean_ctor_set(v___x_933_, 1, v___x_932_);
v___x_934_ = l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg(v_optPrioStx_922_, v___x_933_, v_a_923_, v_a_924_);
lean_dec(v_optPrioStx_922_);
return v___x_934_;
}
else
{
lean_object* v_val_935_; lean_object* v___x_937_; uint8_t v_isShared_938_; uint8_t v_isSharedCheck_942_; 
lean_dec(v_optPrioStx_922_);
v_val_935_ = lean_ctor_get(v___x_929_, 0);
v_isSharedCheck_942_ = !lean_is_exclusive(v___x_929_);
if (v_isSharedCheck_942_ == 0)
{
v___x_937_ = v___x_929_;
v_isShared_938_ = v_isSharedCheck_942_;
goto v_resetjp_936_;
}
else
{
lean_inc(v_val_935_);
lean_dec(v___x_929_);
v___x_937_ = lean_box(0);
v_isShared_938_ = v_isSharedCheck_942_;
goto v_resetjp_936_;
}
v_resetjp_936_:
{
lean_object* v___x_940_; 
if (v_isShared_938_ == 0)
{
lean_ctor_set_tag(v___x_937_, 0);
v___x_940_ = v___x_937_;
goto v_reusejp_939_;
}
else
{
lean_object* v_reuseFailAlloc_941_; 
v_reuseFailAlloc_941_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_941_, 0, v_val_935_);
v___x_940_ = v_reuseFailAlloc_941_;
goto v_reusejp_939_;
}
v_reusejp_939_:
{
return v___x_940_;
}
}
}
}
else
{
lean_object* v___x_943_; lean_object* v___x_944_; 
lean_dec(v_optPrioStx_922_);
v___x_943_ = lean_unsigned_to_nat(1000u);
v___x_944_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_944_, 0, v___x_943_);
return v___x_944_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getAttrParamOptPrio___boxed(lean_object* v_optPrioStx_945_, lean_object* v_a_946_, lean_object* v_a_947_, lean_object* v_a_948_){
_start:
{
lean_object* v_res_949_; 
v_res_949_ = l_Lean_getAttrParamOptPrio(v_optPrioStx_945_, v_a_946_, v_a_947_);
lean_dec(v_a_947_);
lean_dec_ref(v_a_946_);
return v_res_949_;
}
}
static lean_object* _init_l_Lean_Attribute_Builtin_getPrio___closed__1(void){
_start:
{
lean_object* v___x_951_; lean_object* v___x_952_; 
v___x_951_ = ((lean_object*)(l_Lean_Attribute_Builtin_getPrio___closed__0));
v___x_952_ = l_Lean_stringToMessageData(v___x_951_);
return v___x_952_;
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getPrio(lean_object* v_stx_953_, lean_object* v_a_954_, lean_object* v_a_955_){
_start:
{
lean_object* v___x_957_; lean_object* v___x_958_; uint8_t v___x_959_; 
lean_inc(v_stx_953_);
v___x_957_ = l_Lean_Syntax_getKind(v_stx_953_);
v___x_958_ = ((lean_object*)(l_Lean_Attribute_Builtin_ensureNoArgs___closed__6));
v___x_959_ = lean_name_eq(v___x_957_, v___x_958_);
lean_dec(v___x_957_);
if (v___x_959_ == 0)
{
lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; 
v___x_960_ = lean_obj_once(&l_Lean_Attribute_Builtin_getPrio___closed__1, &l_Lean_Attribute_Builtin_getPrio___closed__1_once, _init_l_Lean_Attribute_Builtin_getPrio___closed__1);
lean_inc(v_stx_953_);
v___x_961_ = l_Lean_MessageData_ofSyntax(v_stx_953_);
v___x_962_ = l_Lean_indentD(v___x_961_);
v___x_963_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_963_, 0, v___x_960_);
lean_ctor_set(v___x_963_, 1, v___x_962_);
v___x_964_ = l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg(v_stx_953_, v___x_963_, v_a_954_, v_a_955_);
lean_dec(v_stx_953_);
return v___x_964_;
}
else
{
lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; 
v___x_965_ = lean_unsigned_to_nat(1u);
v___x_966_ = l_Lean_Syntax_getArg(v_stx_953_, v___x_965_);
lean_dec(v_stx_953_);
v___x_967_ = l_Lean_getAttrParamOptPrio(v___x_966_, v_a_954_, v_a_955_);
return v___x_967_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getPrio___boxed(lean_object* v_stx_968_, lean_object* v_a_969_, lean_object* v_a_970_, lean_object* v_a_971_){
_start:
{
lean_object* v_res_972_; 
v_res_972_ = l_Lean_Attribute_Builtin_getPrio(v_stx_968_, v_a_969_, v_a_970_);
lean_dec(v_a_970_);
lean_dec_ref(v_a_969_);
return v_res_972_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__1(void){
_start:
{
lean_object* v___x_974_; lean_object* v___x_975_; 
v___x_974_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__0));
v___x_975_ = l_Lean_stringToMessageData(v___x_974_);
return v___x_975_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__3(void){
_start:
{
lean_object* v___x_977_; lean_object* v___x_978_; 
v___x_977_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__2));
v___x_978_ = l_Lean_stringToMessageData(v___x_977_);
return v___x_978_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__5(void){
_start:
{
lean_object* v___x_980_; lean_object* v___x_981_; 
v___x_980_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__4));
v___x_981_ = l_Lean_stringToMessageData(v___x_980_);
return v___x_981_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___redArg(lean_object* v_inst_982_, lean_object* v_inst_983_, lean_object* v_name_984_, uint8_t v_kind_985_){
_start:
{
lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___y_992_; 
v___x_986_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__1, &l_Lean_throwAttrMustBeGlobal___redArg___closed__1_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__1);
v___x_987_ = l_Lean_MessageData_ofName(v_name_984_);
v___x_988_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_988_, 0, v___x_986_);
lean_ctor_set(v___x_988_, 1, v___x_987_);
v___x_989_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__3, &l_Lean_throwAttrMustBeGlobal___redArg___closed__3_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__3);
v___x_990_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_990_, 0, v___x_988_);
lean_ctor_set(v___x_990_, 1, v___x_989_);
switch(v_kind_985_)
{
case 0:
{
lean_object* v___x_999_; 
v___x_999_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__0));
v___y_992_ = v___x_999_;
goto v___jp_991_;
}
case 1:
{
lean_object* v___x_1000_; 
v___x_1000_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__1));
v___y_992_ = v___x_1000_;
goto v___jp_991_;
}
default: 
{
lean_object* v___x_1001_; 
v___x_1001_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__2));
v___y_992_ = v___x_1001_;
goto v___jp_991_;
}
}
v___jp_991_:
{
lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; 
lean_inc_ref(v___y_992_);
v___x_993_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_993_, 0, v___y_992_);
v___x_994_ = l_Lean_MessageData_ofFormat(v___x_993_);
v___x_995_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_995_, 0, v___x_990_);
lean_ctor_set(v___x_995_, 1, v___x_994_);
v___x_996_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__5, &l_Lean_throwAttrMustBeGlobal___redArg___closed__5_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__5);
v___x_997_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_997_, 0, v___x_995_);
lean_ctor_set(v___x_997_, 1, v___x_996_);
v___x_998_ = l_Lean_throwError___redArg(v_inst_982_, v_inst_983_, v___x_997_);
return v___x_998_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___redArg___boxed(lean_object* v_inst_1002_, lean_object* v_inst_1003_, lean_object* v_name_1004_, lean_object* v_kind_1005_){
_start:
{
uint8_t v_kind_boxed_1006_; lean_object* v_res_1007_; 
v_kind_boxed_1006_ = lean_unbox(v_kind_1005_);
v_res_1007_ = l_Lean_throwAttrMustBeGlobal___redArg(v_inst_1002_, v_inst_1003_, v_name_1004_, v_kind_boxed_1006_);
return v_res_1007_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal(lean_object* v_m_1008_, lean_object* v_inst_1009_, lean_object* v_inst_1010_, lean_object* v_00_u03b1_1011_, lean_object* v_name_1012_, uint8_t v_kind_1013_){
_start:
{
lean_object* v___x_1014_; 
v___x_1014_ = l_Lean_throwAttrMustBeGlobal___redArg(v_inst_1009_, v_inst_1010_, v_name_1012_, v_kind_1013_);
return v___x_1014_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___boxed(lean_object* v_m_1015_, lean_object* v_inst_1016_, lean_object* v_inst_1017_, lean_object* v_00_u03b1_1018_, lean_object* v_name_1019_, lean_object* v_kind_1020_){
_start:
{
uint8_t v_kind_boxed_1021_; lean_object* v_res_1022_; 
v_kind_boxed_1021_ = lean_unbox(v_kind_1020_);
v_res_1022_ = l_Lean_throwAttrMustBeGlobal(v_m_1015_, v_inst_1016_, v_inst_1017_, v_00_u03b1_1018_, v_name_1019_, v_kind_boxed_1021_);
return v_res_1022_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1(void){
_start:
{
lean_object* v___x_1024_; lean_object* v___x_1025_; 
v___x_1024_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___redArg___closed__0));
v___x_1025_ = l_Lean_stringToMessageData(v___x_1024_);
return v___x_1025_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__3(void){
_start:
{
lean_object* v___x_1027_; lean_object* v___x_1028_; 
v___x_1027_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___redArg___closed__2));
v___x_1028_ = l_Lean_stringToMessageData(v___x_1027_);
return v___x_1028_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__5(void){
_start:
{
lean_object* v___x_1030_; lean_object* v___x_1031_; 
v___x_1030_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___redArg___closed__4));
v___x_1031_ = l_Lean_stringToMessageData(v___x_1030_);
return v___x_1031_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___redArg(lean_object* v_inst_1032_, lean_object* v_inst_1033_, lean_object* v_attrName_1034_, lean_object* v_declName_1035_){
_start:
{
lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; uint8_t v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; 
v___x_1036_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1);
v___x_1037_ = l_Lean_MessageData_ofName(v_attrName_1034_);
v___x_1038_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1038_, 0, v___x_1036_);
lean_ctor_set(v___x_1038_, 1, v___x_1037_);
v___x_1039_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__3, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__3_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__3);
v___x_1040_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1040_, 0, v___x_1038_);
lean_ctor_set(v___x_1040_, 1, v___x_1039_);
v___x_1041_ = 0;
v___x_1042_ = l_Lean_MessageData_ofConstName(v_declName_1035_, v___x_1041_);
v___x_1043_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1043_, 0, v___x_1040_);
lean_ctor_set(v___x_1043_, 1, v___x_1042_);
v___x_1044_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__5, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__5_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__5);
v___x_1045_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1045_, 0, v___x_1043_);
lean_ctor_set(v___x_1045_, 1, v___x_1044_);
v___x_1046_ = l_Lean_throwError___redArg(v_inst_1032_, v_inst_1033_, v___x_1045_);
return v___x_1046_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule(lean_object* v_m_1047_, lean_object* v_inst_1048_, lean_object* v_inst_1049_, lean_object* v_00_u03b1_1050_, lean_object* v_attrName_1051_, lean_object* v_declName_1052_){
_start:
{
lean_object* v___x_1053_; 
v___x_1053_ = l_Lean_throwAttrDeclInImportedModule___redArg(v_inst_1048_, v_inst_1049_, v_attrName_1051_, v_declName_1052_);
return v___x_1053_;
}
}
static lean_object* _init_l_Lean_throwAttrNotInAsyncCtx___redArg___closed__1(void){
_start:
{
lean_object* v___x_1055_; lean_object* v___x_1056_; 
v___x_1055_ = ((lean_object*)(l_Lean_throwAttrNotInAsyncCtx___redArg___closed__0));
v___x_1056_ = l_Lean_stringToMessageData(v___x_1055_);
return v___x_1056_;
}
}
static lean_object* _init_l_Lean_throwAttrNotInAsyncCtx___redArg___closed__3(void){
_start:
{
lean_object* v___x_1058_; lean_object* v___x_1059_; 
v___x_1058_ = ((lean_object*)(l_Lean_throwAttrNotInAsyncCtx___redArg___closed__2));
v___x_1059_ = l_Lean_stringToMessageData(v___x_1058_);
return v___x_1059_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___redArg(lean_object* v_inst_1060_, lean_object* v_inst_1061_, lean_object* v_attrName_1062_, lean_object* v_declName_1063_, lean_object* v_asyncPrefix_x3f_1064_){
_start:
{
lean_object* v___y_1066_; 
if (lean_obj_tag(v_asyncPrefix_x3f_1064_) == 0)
{
lean_object* v___x_1079_; 
v___x_1079_ = l_Lean_MessageData_nil;
v___y_1066_ = v___x_1079_;
goto v___jp_1065_;
}
else
{
lean_object* v_val_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; 
v_val_1080_ = lean_ctor_get(v_asyncPrefix_x3f_1064_, 0);
lean_inc(v_val_1080_);
lean_dec_ref(v_asyncPrefix_x3f_1064_);
v___x_1081_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___redArg___closed__3, &l_Lean_throwAttrNotInAsyncCtx___redArg___closed__3_once, _init_l_Lean_throwAttrNotInAsyncCtx___redArg___closed__3);
v___x_1082_ = l_Lean_MessageData_ofName(v_val_1080_);
v___x_1083_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1083_, 0, v___x_1081_);
lean_ctor_set(v___x_1083_, 1, v___x_1082_);
v___x_1084_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__5, &l_Lean_throwAttrMustBeGlobal___redArg___closed__5_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__5);
v___x_1085_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1085_, 0, v___x_1083_);
lean_ctor_set(v___x_1085_, 1, v___x_1084_);
v___y_1066_ = v___x_1085_;
goto v___jp_1065_;
}
v___jp_1065_:
{
lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; uint8_t v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; 
v___x_1067_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1);
v___x_1068_ = l_Lean_MessageData_ofName(v_attrName_1062_);
v___x_1069_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1069_, 0, v___x_1067_);
lean_ctor_set(v___x_1069_, 1, v___x_1068_);
v___x_1070_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__3, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__3_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__3);
v___x_1071_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1071_, 0, v___x_1069_);
lean_ctor_set(v___x_1071_, 1, v___x_1070_);
v___x_1072_ = 0;
v___x_1073_ = l_Lean_MessageData_ofConstName(v_declName_1063_, v___x_1072_);
v___x_1074_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1074_, 0, v___x_1071_);
lean_ctor_set(v___x_1074_, 1, v___x_1073_);
v___x_1075_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___redArg___closed__1, &l_Lean_throwAttrNotInAsyncCtx___redArg___closed__1_once, _init_l_Lean_throwAttrNotInAsyncCtx___redArg___closed__1);
v___x_1076_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1076_, 0, v___x_1074_);
lean_ctor_set(v___x_1076_, 1, v___x_1075_);
v___x_1077_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1077_, 0, v___x_1076_);
lean_ctor_set(v___x_1077_, 1, v___y_1066_);
v___x_1078_ = l_Lean_throwError___redArg(v_inst_1060_, v_inst_1061_, v___x_1077_);
return v___x_1078_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx(lean_object* v_m_1086_, lean_object* v_inst_1087_, lean_object* v_inst_1088_, lean_object* v_00_u03b1_1089_, lean_object* v_attrName_1090_, lean_object* v_declName_1091_, lean_object* v_asyncPrefix_x3f_1092_){
_start:
{
lean_object* v___x_1093_; 
v___x_1093_ = l_Lean_throwAttrNotInAsyncCtx___redArg(v_inst_1087_, v_inst_1088_, v_attrName_1090_, v_declName_1091_, v_asyncPrefix_x3f_1092_);
return v___x_1093_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1(void){
_start:
{
lean_object* v___x_1095_; lean_object* v___x_1096_; 
v___x_1095_ = ((lean_object*)(l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__0));
v___x_1096_ = l_Lean_stringToMessageData(v___x_1095_);
return v___x_1096_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__3(void){
_start:
{
lean_object* v___x_1098_; lean_object* v___x_1099_; 
v___x_1098_ = ((lean_object*)(l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__2));
v___x_1099_ = l_Lean_stringToMessageData(v___x_1098_);
return v___x_1099_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__5(void){
_start:
{
lean_object* v___x_1101_; lean_object* v___x_1102_; 
v___x_1101_ = ((lean_object*)(l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__4));
v___x_1102_ = l_Lean_stringToMessageData(v___x_1101_);
return v___x_1102_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__7(void){
_start:
{
lean_object* v___x_1104_; lean_object* v___x_1105_; 
v___x_1104_ = ((lean_object*)(l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__6));
v___x_1105_ = l_Lean_stringToMessageData(v___x_1104_);
return v___x_1105_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclNotOfExpectedType___redArg(lean_object* v_inst_1106_, lean_object* v_inst_1107_, lean_object* v_attrName_1108_, lean_object* v_declName_1109_, lean_object* v_givenType_1110_, lean_object* v_expectedType_1111_){
_start:
{
lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; uint8_t v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; 
v___x_1112_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1);
v___x_1113_ = l_Lean_MessageData_ofName(v_attrName_1108_);
lean_inc_ref(v___x_1113_);
v___x_1114_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1114_, 0, v___x_1112_);
lean_ctor_set(v___x_1114_, 1, v___x_1113_);
v___x_1115_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1, &l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1);
v___x_1116_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1116_, 0, v___x_1114_);
lean_ctor_set(v___x_1116_, 1, v___x_1115_);
v___x_1117_ = 0;
v___x_1118_ = l_Lean_MessageData_ofConstName(v_declName_1109_, v___x_1117_);
v___x_1119_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1119_, 0, v___x_1116_);
lean_ctor_set(v___x_1119_, 1, v___x_1118_);
v___x_1120_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__3, &l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__3_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__3);
v___x_1121_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1121_, 0, v___x_1119_);
lean_ctor_set(v___x_1121_, 1, v___x_1120_);
v___x_1122_ = l_Lean_indentExpr(v_givenType_1110_);
v___x_1123_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1123_, 0, v___x_1121_);
lean_ctor_set(v___x_1123_, 1, v___x_1122_);
v___x_1124_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__5, &l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__5_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__5);
v___x_1125_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1125_, 0, v___x_1123_);
lean_ctor_set(v___x_1125_, 1, v___x_1124_);
v___x_1126_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1126_, 0, v___x_1125_);
lean_ctor_set(v___x_1126_, 1, v___x_1113_);
v___x_1127_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__7, &l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__7_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__7);
v___x_1128_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1128_, 0, v___x_1126_);
lean_ctor_set(v___x_1128_, 1, v___x_1127_);
v___x_1129_ = l_Lean_indentExpr(v_expectedType_1111_);
v___x_1130_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1130_, 0, v___x_1128_);
lean_ctor_set(v___x_1130_, 1, v___x_1129_);
v___x_1131_ = l_Lean_throwError___redArg(v_inst_1106_, v_inst_1107_, v___x_1130_);
return v___x_1131_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclNotOfExpectedType(lean_object* v_m_1132_, lean_object* v_inst_1133_, lean_object* v_inst_1134_, lean_object* v_00_u03b1_1135_, lean_object* v_attrName_1136_, lean_object* v_declName_1137_, lean_object* v_givenType_1138_, lean_object* v_expectedType_1139_){
_start:
{
lean_object* v___x_1140_; 
v___x_1140_ = l_Lean_throwAttrDeclNotOfExpectedType___redArg(v_inst_1133_, v_inst_1134_, v_attrName_1136_, v_declName_1137_, v_givenType_1138_, v_expectedType_1139_);
return v___x_1140_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1___redArg(lean_object* v_constName_1141_, uint8_t v_skipRealize_1142_, lean_object* v___y_1143_){
_start:
{
lean_object* v___x_1145_; lean_object* v_env_1146_; uint8_t v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; 
v___x_1145_ = lean_st_ref_get(v___y_1143_);
v_env_1146_ = lean_ctor_get(v___x_1145_, 0);
lean_inc_ref(v_env_1146_);
lean_dec(v___x_1145_);
v___x_1147_ = l_Lean_Environment_contains(v_env_1146_, v_constName_1141_, v_skipRealize_1142_);
v___x_1148_ = lean_box(v___x_1147_);
v___x_1149_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1149_, 0, v___x_1148_);
return v___x_1149_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1___redArg___boxed(lean_object* v_constName_1150_, lean_object* v_skipRealize_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_){
_start:
{
uint8_t v_skipRealize_boxed_1154_; lean_object* v_res_1155_; 
v_skipRealize_boxed_1154_ = lean_unbox(v_skipRealize_1151_);
v_res_1155_ = l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1___redArg(v_constName_1150_, v_skipRealize_boxed_1154_, v___y_1152_);
lean_dec(v___y_1152_);
return v_res_1155_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1(lean_object* v_constName_1156_, uint8_t v_skipRealize_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_){
_start:
{
lean_object* v___x_1161_; 
v___x_1161_ = l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1___redArg(v_constName_1156_, v_skipRealize_1157_, v___y_1159_);
return v___x_1161_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1___boxed(lean_object* v_constName_1162_, lean_object* v_skipRealize_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_){
_start:
{
uint8_t v_skipRealize_boxed_1167_; lean_object* v_res_1168_; 
v_skipRealize_boxed_1167_ = lean_unbox(v_skipRealize_1163_);
v_res_1168_ = l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1(v_constName_1162_, v_skipRealize_boxed_1167_, v___y_1164_, v___y_1165_);
lean_dec(v___y_1165_);
lean_dec_ref(v___y_1164_);
return v_res_1168_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___lam__0(lean_object* v___y_1169_, uint8_t v_isExporting_1170_, lean_object* v___x_1171_, lean_object* v_a_x3f_1172_){
_start:
{
lean_object* v___x_1174_; lean_object* v_env_1175_; lean_object* v_nextMacroScope_1176_; lean_object* v_ngen_1177_; lean_object* v_auxDeclNGen_1178_; lean_object* v_traceState_1179_; lean_object* v_messages_1180_; lean_object* v_infoState_1181_; lean_object* v_snapshotTasks_1182_; lean_object* v___x_1184_; uint8_t v_isShared_1185_; uint8_t v_isSharedCheck_1193_; 
v___x_1174_ = lean_st_ref_take(v___y_1169_);
v_env_1175_ = lean_ctor_get(v___x_1174_, 0);
v_nextMacroScope_1176_ = lean_ctor_get(v___x_1174_, 1);
v_ngen_1177_ = lean_ctor_get(v___x_1174_, 2);
v_auxDeclNGen_1178_ = lean_ctor_get(v___x_1174_, 3);
v_traceState_1179_ = lean_ctor_get(v___x_1174_, 4);
v_messages_1180_ = lean_ctor_get(v___x_1174_, 6);
v_infoState_1181_ = lean_ctor_get(v___x_1174_, 7);
v_snapshotTasks_1182_ = lean_ctor_get(v___x_1174_, 8);
v_isSharedCheck_1193_ = !lean_is_exclusive(v___x_1174_);
if (v_isSharedCheck_1193_ == 0)
{
lean_object* v_unused_1194_; 
v_unused_1194_ = lean_ctor_get(v___x_1174_, 5);
lean_dec(v_unused_1194_);
v___x_1184_ = v___x_1174_;
v_isShared_1185_ = v_isSharedCheck_1193_;
goto v_resetjp_1183_;
}
else
{
lean_inc(v_snapshotTasks_1182_);
lean_inc(v_infoState_1181_);
lean_inc(v_messages_1180_);
lean_inc(v_traceState_1179_);
lean_inc(v_auxDeclNGen_1178_);
lean_inc(v_ngen_1177_);
lean_inc(v_nextMacroScope_1176_);
lean_inc(v_env_1175_);
lean_dec(v___x_1174_);
v___x_1184_ = lean_box(0);
v_isShared_1185_ = v_isSharedCheck_1193_;
goto v_resetjp_1183_;
}
v_resetjp_1183_:
{
lean_object* v___x_1186_; lean_object* v___x_1188_; 
v___x_1186_ = l_Lean_Environment_setExporting(v_env_1175_, v_isExporting_1170_);
if (v_isShared_1185_ == 0)
{
lean_ctor_set(v___x_1184_, 5, v___x_1171_);
lean_ctor_set(v___x_1184_, 0, v___x_1186_);
v___x_1188_ = v___x_1184_;
goto v_reusejp_1187_;
}
else
{
lean_object* v_reuseFailAlloc_1192_; 
v_reuseFailAlloc_1192_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1192_, 0, v___x_1186_);
lean_ctor_set(v_reuseFailAlloc_1192_, 1, v_nextMacroScope_1176_);
lean_ctor_set(v_reuseFailAlloc_1192_, 2, v_ngen_1177_);
lean_ctor_set(v_reuseFailAlloc_1192_, 3, v_auxDeclNGen_1178_);
lean_ctor_set(v_reuseFailAlloc_1192_, 4, v_traceState_1179_);
lean_ctor_set(v_reuseFailAlloc_1192_, 5, v___x_1171_);
lean_ctor_set(v_reuseFailAlloc_1192_, 6, v_messages_1180_);
lean_ctor_set(v_reuseFailAlloc_1192_, 7, v_infoState_1181_);
lean_ctor_set(v_reuseFailAlloc_1192_, 8, v_snapshotTasks_1182_);
v___x_1188_ = v_reuseFailAlloc_1192_;
goto v_reusejp_1187_;
}
v_reusejp_1187_:
{
lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; 
v___x_1189_ = lean_st_ref_set(v___y_1169_, v___x_1188_);
v___x_1190_ = lean_box(0);
v___x_1191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1191_, 0, v___x_1190_);
return v___x_1191_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___lam__0___boxed(lean_object* v___y_1195_, lean_object* v_isExporting_1196_, lean_object* v___x_1197_, lean_object* v_a_x3f_1198_, lean_object* v___y_1199_){
_start:
{
uint8_t v_isExporting_boxed_1200_; lean_object* v_res_1201_; 
v_isExporting_boxed_1200_ = lean_unbox(v_isExporting_1196_);
v_res_1201_ = l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___lam__0(v___y_1195_, v_isExporting_boxed_1200_, v___x_1197_, v_a_x3f_1198_);
lean_dec(v_a_x3f_1198_);
lean_dec(v___y_1195_);
return v_res_1201_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_1202_; 
v___x_1202_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1202_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_1203_; lean_object* v___x_1204_; 
v___x_1203_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__0, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__0);
v___x_1204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1204_, 0, v___x_1203_);
return v___x_1204_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_1205_; lean_object* v___x_1206_; 
v___x_1205_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1);
v___x_1206_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1206_, 0, v___x_1205_);
lean_ctor_set(v___x_1206_, 1, v___x_1205_);
return v___x_1206_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg(lean_object* v_x_1207_, uint8_t v_isExporting_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_){
_start:
{
lean_object* v___x_1212_; lean_object* v_env_1213_; uint8_t v_isExporting_1214_; lean_object* v___x_1215_; lean_object* v_env_1216_; lean_object* v_nextMacroScope_1217_; lean_object* v_ngen_1218_; lean_object* v_auxDeclNGen_1219_; lean_object* v_traceState_1220_; lean_object* v_messages_1221_; lean_object* v_infoState_1222_; lean_object* v_snapshotTasks_1223_; lean_object* v___x_1225_; uint8_t v_isShared_1226_; uint8_t v_isSharedCheck_1262_; 
v___x_1212_ = lean_st_ref_get(v___y_1210_);
v_env_1213_ = lean_ctor_get(v___x_1212_, 0);
lean_inc_ref(v_env_1213_);
lean_dec(v___x_1212_);
v_isExporting_1214_ = lean_ctor_get_uint8(v_env_1213_, sizeof(void*)*8);
lean_dec_ref(v_env_1213_);
v___x_1215_ = lean_st_ref_take(v___y_1210_);
v_env_1216_ = lean_ctor_get(v___x_1215_, 0);
v_nextMacroScope_1217_ = lean_ctor_get(v___x_1215_, 1);
v_ngen_1218_ = lean_ctor_get(v___x_1215_, 2);
v_auxDeclNGen_1219_ = lean_ctor_get(v___x_1215_, 3);
v_traceState_1220_ = lean_ctor_get(v___x_1215_, 4);
v_messages_1221_ = lean_ctor_get(v___x_1215_, 6);
v_infoState_1222_ = lean_ctor_get(v___x_1215_, 7);
v_snapshotTasks_1223_ = lean_ctor_get(v___x_1215_, 8);
v_isSharedCheck_1262_ = !lean_is_exclusive(v___x_1215_);
if (v_isSharedCheck_1262_ == 0)
{
lean_object* v_unused_1263_; 
v_unused_1263_ = lean_ctor_get(v___x_1215_, 5);
lean_dec(v_unused_1263_);
v___x_1225_ = v___x_1215_;
v_isShared_1226_ = v_isSharedCheck_1262_;
goto v_resetjp_1224_;
}
else
{
lean_inc(v_snapshotTasks_1223_);
lean_inc(v_infoState_1222_);
lean_inc(v_messages_1221_);
lean_inc(v_traceState_1220_);
lean_inc(v_auxDeclNGen_1219_);
lean_inc(v_ngen_1218_);
lean_inc(v_nextMacroScope_1217_);
lean_inc(v_env_1216_);
lean_dec(v___x_1215_);
v___x_1225_ = lean_box(0);
v_isShared_1226_ = v_isSharedCheck_1262_;
goto v_resetjp_1224_;
}
v_resetjp_1224_:
{
lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1230_; 
v___x_1227_ = l_Lean_Environment_setExporting(v_env_1216_, v_isExporting_1208_);
v___x_1228_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2);
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
v_reuseFailAlloc_1261_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1261_, 0, v___x_1227_);
lean_ctor_set(v_reuseFailAlloc_1261_, 1, v_nextMacroScope_1217_);
lean_ctor_set(v_reuseFailAlloc_1261_, 2, v_ngen_1218_);
lean_ctor_set(v_reuseFailAlloc_1261_, 3, v_auxDeclNGen_1219_);
lean_ctor_set(v_reuseFailAlloc_1261_, 4, v_traceState_1220_);
lean_ctor_set(v_reuseFailAlloc_1261_, 5, v___x_1228_);
lean_ctor_set(v_reuseFailAlloc_1261_, 6, v_messages_1221_);
lean_ctor_set(v_reuseFailAlloc_1261_, 7, v_infoState_1222_);
lean_ctor_set(v_reuseFailAlloc_1261_, 8, v_snapshotTasks_1223_);
v___x_1230_ = v_reuseFailAlloc_1261_;
goto v_reusejp_1229_;
}
v_reusejp_1229_:
{
lean_object* v___x_1231_; lean_object* v_r_1232_; 
v___x_1231_ = lean_st_ref_set(v___y_1210_, v___x_1230_);
lean_inc(v___y_1210_);
lean_inc_ref(v___y_1209_);
v_r_1232_ = lean_apply_3(v_x_1207_, v___y_1209_, v___y_1210_, lean_box(0));
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
v___x_1239_ = l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___lam__0(v___y_1210_, v_isExporting_1214_, v___x_1228_, v___x_1238_);
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
lean_dec_ref(v_r_1232_);
v___x_1251_ = lean_box(0);
v___x_1252_ = l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___lam__0(v___y_1210_, v_isExporting_1214_, v___x_1228_, v___x_1251_);
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
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___boxed(lean_object* v_x_1264_, lean_object* v_isExporting_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_){
_start:
{
uint8_t v_isExporting_boxed_1269_; lean_object* v_res_1270_; 
v_isExporting_boxed_1269_ = lean_unbox(v_isExporting_1265_);
v_res_1270_ = l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg(v_x_1264_, v_isExporting_boxed_1269_, v___y_1266_, v___y_1267_);
lean_dec(v___y_1267_);
lean_dec_ref(v___y_1266_);
return v_res_1270_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2(lean_object* v_00_u03b1_1271_, lean_object* v_x_1272_, uint8_t v_isExporting_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_){
_start:
{
lean_object* v___x_1277_; 
v___x_1277_ = l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg(v_x_1272_, v_isExporting_1273_, v___y_1274_, v___y_1275_);
return v___x_1277_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___boxed(lean_object* v_00_u03b1_1278_, lean_object* v_x_1279_, lean_object* v_isExporting_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_){
_start:
{
uint8_t v_isExporting_boxed_1284_; lean_object* v_res_1285_; 
v_isExporting_boxed_1284_ = lean_unbox(v_isExporting_1280_);
v_res_1285_ = l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2(v_00_u03b1_1278_, v_x_1279_, v_isExporting_boxed_1284_, v___y_1281_, v___y_1282_);
lean_dec(v___y_1282_);
lean_dec_ref(v___y_1281_);
return v_res_1285_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0_spec__3(lean_object* v_opts_1286_, lean_object* v_opt_1287_){
_start:
{
lean_object* v_name_1288_; lean_object* v_defValue_1289_; lean_object* v_map_1290_; lean_object* v___x_1291_; 
v_name_1288_ = lean_ctor_get(v_opt_1287_, 0);
v_defValue_1289_ = lean_ctor_get(v_opt_1287_, 1);
v_map_1290_ = lean_ctor_get(v_opts_1286_, 0);
v___x_1291_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1290_, v_name_1288_);
if (lean_obj_tag(v___x_1291_) == 0)
{
uint8_t v___x_1292_; 
v___x_1292_ = lean_unbox(v_defValue_1289_);
return v___x_1292_;
}
else
{
lean_object* v_val_1293_; 
v_val_1293_ = lean_ctor_get(v___x_1291_, 0);
lean_inc(v_val_1293_);
lean_dec_ref(v___x_1291_);
if (lean_obj_tag(v_val_1293_) == 1)
{
uint8_t v_v_1294_; 
v_v_1294_ = lean_ctor_get_uint8(v_val_1293_, 0);
lean_dec_ref(v_val_1293_);
return v_v_1294_;
}
else
{
uint8_t v___x_1295_; 
lean_dec(v_val_1293_);
v___x_1295_ = lean_unbox(v_defValue_1289_);
return v___x_1295_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0_spec__3___boxed(lean_object* v_opts_1296_, lean_object* v_opt_1297_){
_start:
{
uint8_t v_res_1298_; lean_object* v_r_1299_; 
v_res_1298_ = l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0_spec__3(v_opts_1296_, v_opt_1297_);
lean_dec_ref(v_opt_1297_);
lean_dec_ref(v_opts_1296_);
v_r_1299_ = lean_box(v_res_1298_);
return v_r_1299_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0(uint8_t v___y_1307_, uint8_t v_suppressElabErrors_1308_, lean_object* v_x_1309_){
_start:
{
if (lean_obj_tag(v_x_1309_) == 1)
{
lean_object* v_pre_1310_; 
v_pre_1310_ = lean_ctor_get(v_x_1309_, 0);
switch(lean_obj_tag(v_pre_1310_))
{
case 1:
{
lean_object* v_pre_1311_; 
v_pre_1311_ = lean_ctor_get(v_pre_1310_, 0);
switch(lean_obj_tag(v_pre_1311_))
{
case 0:
{
lean_object* v_str_1312_; lean_object* v_str_1313_; lean_object* v___x_1314_; uint8_t v___x_1315_; 
v_str_1312_ = lean_ctor_get(v_x_1309_, 1);
v_str_1313_ = lean_ctor_get(v_pre_1310_, 1);
v___x_1314_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__0));
v___x_1315_ = lean_string_dec_eq(v_str_1313_, v___x_1314_);
if (v___x_1315_ == 0)
{
lean_object* v___x_1316_; uint8_t v___x_1317_; 
v___x_1316_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__2));
v___x_1317_ = lean_string_dec_eq(v_str_1313_, v___x_1316_);
if (v___x_1317_ == 0)
{
return v___y_1307_;
}
else
{
lean_object* v___x_1318_; uint8_t v___x_1319_; 
v___x_1318_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__1));
v___x_1319_ = lean_string_dec_eq(v_str_1312_, v___x_1318_);
if (v___x_1319_ == 0)
{
return v___y_1307_;
}
else
{
return v_suppressElabErrors_1308_;
}
}
}
else
{
lean_object* v___x_1320_; uint8_t v___x_1321_; 
v___x_1320_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__2));
v___x_1321_ = lean_string_dec_eq(v_str_1312_, v___x_1320_);
if (v___x_1321_ == 0)
{
return v___y_1307_;
}
else
{
return v_suppressElabErrors_1308_;
}
}
}
case 1:
{
lean_object* v_pre_1322_; 
v_pre_1322_ = lean_ctor_get(v_pre_1311_, 0);
if (lean_obj_tag(v_pre_1322_) == 0)
{
lean_object* v_str_1323_; lean_object* v_str_1324_; lean_object* v_str_1325_; lean_object* v___x_1326_; uint8_t v___x_1327_; 
v_str_1323_ = lean_ctor_get(v_x_1309_, 1);
v_str_1324_ = lean_ctor_get(v_pre_1310_, 1);
v_str_1325_ = lean_ctor_get(v_pre_1311_, 1);
v___x_1326_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__3));
v___x_1327_ = lean_string_dec_eq(v_str_1325_, v___x_1326_);
if (v___x_1327_ == 0)
{
return v___y_1307_;
}
else
{
lean_object* v___x_1328_; uint8_t v___x_1329_; 
v___x_1328_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__4));
v___x_1329_ = lean_string_dec_eq(v_str_1324_, v___x_1328_);
if (v___x_1329_ == 0)
{
return v___y_1307_;
}
else
{
lean_object* v___x_1330_; uint8_t v___x_1331_; 
v___x_1330_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__5));
v___x_1331_ = lean_string_dec_eq(v_str_1323_, v___x_1330_);
if (v___x_1331_ == 0)
{
return v___y_1307_;
}
else
{
return v_suppressElabErrors_1308_;
}
}
}
}
else
{
return v___y_1307_;
}
}
default: 
{
return v___y_1307_;
}
}
}
case 0:
{
lean_object* v_str_1332_; lean_object* v___x_1333_; uint8_t v___x_1334_; 
v_str_1332_ = lean_ctor_get(v_x_1309_, 1);
v___x_1333_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__6));
v___x_1334_ = lean_string_dec_eq(v_str_1332_, v___x_1333_);
if (v___x_1334_ == 0)
{
return v___y_1307_;
}
else
{
return v_suppressElabErrors_1308_;
}
}
default: 
{
return v___y_1307_;
}
}
}
else
{
return v___y_1307_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___boxed(lean_object* v___y_1335_, lean_object* v_suppressElabErrors_1336_, lean_object* v_x_1337_){
_start:
{
uint8_t v___y_4965__boxed_1338_; uint8_t v_suppressElabErrors_boxed_1339_; uint8_t v_res_1340_; lean_object* v_r_1341_; 
v___y_4965__boxed_1338_ = lean_unbox(v___y_1335_);
v_suppressElabErrors_boxed_1339_ = lean_unbox(v_suppressElabErrors_1336_);
v_res_1340_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0(v___y_4965__boxed_1338_, v_suppressElabErrors_boxed_1339_, v_x_1337_);
lean_dec(v_x_1337_);
v_r_1341_ = lean_box(v_res_1340_);
return v_r_1341_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6(lean_object* v_ref_1342_, lean_object* v_msgData_1343_, uint8_t v_severity_1344_, uint8_t v_isSilent_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_){
_start:
{
lean_object* v___y_1350_; uint8_t v___y_1351_; uint8_t v___y_1352_; lean_object* v___y_1353_; lean_object* v___y_1354_; lean_object* v___y_1355_; lean_object* v___y_1356_; lean_object* v___y_1357_; lean_object* v___y_1358_; lean_object* v___y_1386_; uint8_t v___y_1387_; uint8_t v___y_1388_; lean_object* v___y_1389_; lean_object* v___y_1390_; uint8_t v___y_1391_; lean_object* v___y_1392_; lean_object* v___y_1393_; lean_object* v___y_1411_; lean_object* v___y_1412_; uint8_t v___y_1413_; uint8_t v___y_1414_; lean_object* v___y_1415_; uint8_t v___y_1416_; lean_object* v___y_1417_; lean_object* v___y_1418_; lean_object* v___y_1422_; uint8_t v___y_1423_; lean_object* v___y_1424_; lean_object* v___y_1425_; uint8_t v___y_1426_; lean_object* v___y_1427_; uint8_t v___y_1428_; uint8_t v___x_1433_; lean_object* v___y_1435_; lean_object* v___y_1436_; lean_object* v___y_1437_; uint8_t v___y_1438_; lean_object* v___y_1439_; uint8_t v___y_1440_; uint8_t v___y_1441_; uint8_t v___y_1443_; uint8_t v___x_1458_; 
v___x_1433_ = 2;
v___x_1458_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1344_, v___x_1433_);
if (v___x_1458_ == 0)
{
v___y_1443_ = v___x_1458_;
goto v___jp_1442_;
}
else
{
uint8_t v___x_1459_; 
lean_inc_ref(v_msgData_1343_);
v___x_1459_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_1343_);
v___y_1443_ = v___x_1459_;
goto v___jp_1442_;
}
v___jp_1349_:
{
lean_object* v___x_1359_; lean_object* v_currNamespace_1360_; lean_object* v_openDecls_1361_; lean_object* v_env_1362_; lean_object* v_nextMacroScope_1363_; lean_object* v_ngen_1364_; lean_object* v_auxDeclNGen_1365_; lean_object* v_traceState_1366_; lean_object* v_cache_1367_; lean_object* v_messages_1368_; lean_object* v_infoState_1369_; lean_object* v_snapshotTasks_1370_; lean_object* v___x_1372_; uint8_t v_isShared_1373_; uint8_t v_isSharedCheck_1384_; 
v___x_1359_ = lean_st_ref_take(v___y_1358_);
v_currNamespace_1360_ = lean_ctor_get(v___y_1357_, 6);
v_openDecls_1361_ = lean_ctor_get(v___y_1357_, 7);
v_env_1362_ = lean_ctor_get(v___x_1359_, 0);
v_nextMacroScope_1363_ = lean_ctor_get(v___x_1359_, 1);
v_ngen_1364_ = lean_ctor_get(v___x_1359_, 2);
v_auxDeclNGen_1365_ = lean_ctor_get(v___x_1359_, 3);
v_traceState_1366_ = lean_ctor_get(v___x_1359_, 4);
v_cache_1367_ = lean_ctor_get(v___x_1359_, 5);
v_messages_1368_ = lean_ctor_get(v___x_1359_, 6);
v_infoState_1369_ = lean_ctor_get(v___x_1359_, 7);
v_snapshotTasks_1370_ = lean_ctor_get(v___x_1359_, 8);
v_isSharedCheck_1384_ = !lean_is_exclusive(v___x_1359_);
if (v_isSharedCheck_1384_ == 0)
{
v___x_1372_ = v___x_1359_;
v_isShared_1373_ = v_isSharedCheck_1384_;
goto v_resetjp_1371_;
}
else
{
lean_inc(v_snapshotTasks_1370_);
lean_inc(v_infoState_1369_);
lean_inc(v_messages_1368_);
lean_inc(v_cache_1367_);
lean_inc(v_traceState_1366_);
lean_inc(v_auxDeclNGen_1365_);
lean_inc(v_ngen_1364_);
lean_inc(v_nextMacroScope_1363_);
lean_inc(v_env_1362_);
lean_dec(v___x_1359_);
v___x_1372_ = lean_box(0);
v_isShared_1373_ = v_isSharedCheck_1384_;
goto v_resetjp_1371_;
}
v_resetjp_1371_:
{
lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1379_; 
lean_inc(v_openDecls_1361_);
lean_inc(v_currNamespace_1360_);
v___x_1374_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1374_, 0, v_currNamespace_1360_);
lean_ctor_set(v___x_1374_, 1, v_openDecls_1361_);
v___x_1375_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1375_, 0, v___x_1374_);
lean_ctor_set(v___x_1375_, 1, v___y_1350_);
lean_inc_ref(v___y_1356_);
lean_inc_ref(v___y_1355_);
v___x_1376_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1376_, 0, v___y_1355_);
lean_ctor_set(v___x_1376_, 1, v___y_1353_);
lean_ctor_set(v___x_1376_, 2, v___y_1354_);
lean_ctor_set(v___x_1376_, 3, v___y_1356_);
lean_ctor_set(v___x_1376_, 4, v___x_1375_);
lean_ctor_set_uint8(v___x_1376_, sizeof(void*)*5, v___y_1351_);
lean_ctor_set_uint8(v___x_1376_, sizeof(void*)*5 + 1, v___y_1352_);
lean_ctor_set_uint8(v___x_1376_, sizeof(void*)*5 + 2, v_isSilent_1345_);
v___x_1377_ = l_Lean_MessageLog_add(v___x_1376_, v_messages_1368_);
if (v_isShared_1373_ == 0)
{
lean_ctor_set(v___x_1372_, 6, v___x_1377_);
v___x_1379_ = v___x_1372_;
goto v_reusejp_1378_;
}
else
{
lean_object* v_reuseFailAlloc_1383_; 
v_reuseFailAlloc_1383_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1383_, 0, v_env_1362_);
lean_ctor_set(v_reuseFailAlloc_1383_, 1, v_nextMacroScope_1363_);
lean_ctor_set(v_reuseFailAlloc_1383_, 2, v_ngen_1364_);
lean_ctor_set(v_reuseFailAlloc_1383_, 3, v_auxDeclNGen_1365_);
lean_ctor_set(v_reuseFailAlloc_1383_, 4, v_traceState_1366_);
lean_ctor_set(v_reuseFailAlloc_1383_, 5, v_cache_1367_);
lean_ctor_set(v_reuseFailAlloc_1383_, 6, v___x_1377_);
lean_ctor_set(v_reuseFailAlloc_1383_, 7, v_infoState_1369_);
lean_ctor_set(v_reuseFailAlloc_1383_, 8, v_snapshotTasks_1370_);
v___x_1379_ = v_reuseFailAlloc_1383_;
goto v_reusejp_1378_;
}
v_reusejp_1378_:
{
lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; 
v___x_1380_ = lean_st_ref_set(v___y_1358_, v___x_1379_);
v___x_1381_ = lean_box(0);
v___x_1382_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1382_, 0, v___x_1381_);
return v___x_1382_;
}
}
}
v___jp_1385_:
{
lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v_a_1396_; lean_object* v___x_1398_; uint8_t v_isShared_1399_; uint8_t v_isSharedCheck_1409_; 
v___x_1394_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_1343_);
v___x_1395_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0_spec__0_spec__1(v___x_1394_, v___y_1346_, v___y_1347_);
v_a_1396_ = lean_ctor_get(v___x_1395_, 0);
v_isSharedCheck_1409_ = !lean_is_exclusive(v___x_1395_);
if (v_isSharedCheck_1409_ == 0)
{
v___x_1398_ = v___x_1395_;
v_isShared_1399_ = v_isSharedCheck_1409_;
goto v_resetjp_1397_;
}
else
{
lean_inc(v_a_1396_);
lean_dec(v___x_1395_);
v___x_1398_ = lean_box(0);
v_isShared_1399_ = v_isSharedCheck_1409_;
goto v_resetjp_1397_;
}
v_resetjp_1397_:
{
lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; 
lean_inc_ref_n(v___y_1392_, 2);
v___x_1400_ = l_Lean_FileMap_toPosition(v___y_1392_, v___y_1390_);
lean_dec(v___y_1390_);
v___x_1401_ = l_Lean_FileMap_toPosition(v___y_1392_, v___y_1393_);
lean_dec(v___y_1393_);
v___x_1402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1402_, 0, v___x_1401_);
v___x_1403_ = ((lean_object*)(l_Lean_instInhabitedAttributeImplCore_default___closed__3));
if (v___y_1391_ == 0)
{
lean_del_object(v___x_1398_);
lean_dec_ref(v___y_1386_);
v___y_1350_ = v_a_1396_;
v___y_1351_ = v___y_1387_;
v___y_1352_ = v___y_1388_;
v___y_1353_ = v___x_1400_;
v___y_1354_ = v___x_1402_;
v___y_1355_ = v___y_1389_;
v___y_1356_ = v___x_1403_;
v___y_1357_ = v___y_1346_;
v___y_1358_ = v___y_1347_;
goto v___jp_1349_;
}
else
{
uint8_t v___x_1404_; 
lean_inc(v_a_1396_);
v___x_1404_ = l_Lean_MessageData_hasTag(v___y_1386_, v_a_1396_);
if (v___x_1404_ == 0)
{
lean_object* v___x_1405_; lean_object* v___x_1407_; 
lean_dec_ref(v___x_1402_);
lean_dec_ref(v___x_1400_);
lean_dec(v_a_1396_);
v___x_1405_ = lean_box(0);
if (v_isShared_1399_ == 0)
{
lean_ctor_set(v___x_1398_, 0, v___x_1405_);
v___x_1407_ = v___x_1398_;
goto v_reusejp_1406_;
}
else
{
lean_object* v_reuseFailAlloc_1408_; 
v_reuseFailAlloc_1408_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1408_, 0, v___x_1405_);
v___x_1407_ = v_reuseFailAlloc_1408_;
goto v_reusejp_1406_;
}
v_reusejp_1406_:
{
return v___x_1407_;
}
}
else
{
lean_del_object(v___x_1398_);
v___y_1350_ = v_a_1396_;
v___y_1351_ = v___y_1387_;
v___y_1352_ = v___y_1388_;
v___y_1353_ = v___x_1400_;
v___y_1354_ = v___x_1402_;
v___y_1355_ = v___y_1389_;
v___y_1356_ = v___x_1403_;
v___y_1357_ = v___y_1346_;
v___y_1358_ = v___y_1347_;
goto v___jp_1349_;
}
}
}
}
v___jp_1410_:
{
lean_object* v___x_1419_; 
v___x_1419_ = l_Lean_Syntax_getTailPos_x3f(v___y_1412_, v___y_1413_);
lean_dec(v___y_1412_);
if (lean_obj_tag(v___x_1419_) == 0)
{
lean_inc(v___y_1418_);
v___y_1386_ = v___y_1411_;
v___y_1387_ = v___y_1413_;
v___y_1388_ = v___y_1414_;
v___y_1389_ = v___y_1415_;
v___y_1390_ = v___y_1418_;
v___y_1391_ = v___y_1416_;
v___y_1392_ = v___y_1417_;
v___y_1393_ = v___y_1418_;
goto v___jp_1385_;
}
else
{
lean_object* v_val_1420_; 
v_val_1420_ = lean_ctor_get(v___x_1419_, 0);
lean_inc(v_val_1420_);
lean_dec_ref(v___x_1419_);
v___y_1386_ = v___y_1411_;
v___y_1387_ = v___y_1413_;
v___y_1388_ = v___y_1414_;
v___y_1389_ = v___y_1415_;
v___y_1390_ = v___y_1418_;
v___y_1391_ = v___y_1416_;
v___y_1392_ = v___y_1417_;
v___y_1393_ = v_val_1420_;
goto v___jp_1385_;
}
}
v___jp_1421_:
{
lean_object* v_ref_1429_; lean_object* v___x_1430_; 
v_ref_1429_ = l_Lean_replaceRef(v_ref_1342_, v___y_1424_);
v___x_1430_ = l_Lean_Syntax_getPos_x3f(v_ref_1429_, v___y_1423_);
if (lean_obj_tag(v___x_1430_) == 0)
{
lean_object* v___x_1431_; 
v___x_1431_ = lean_unsigned_to_nat(0u);
v___y_1411_ = v___y_1422_;
v___y_1412_ = v_ref_1429_;
v___y_1413_ = v___y_1423_;
v___y_1414_ = v___y_1428_;
v___y_1415_ = v___y_1425_;
v___y_1416_ = v___y_1426_;
v___y_1417_ = v___y_1427_;
v___y_1418_ = v___x_1431_;
goto v___jp_1410_;
}
else
{
lean_object* v_val_1432_; 
v_val_1432_ = lean_ctor_get(v___x_1430_, 0);
lean_inc(v_val_1432_);
lean_dec_ref(v___x_1430_);
v___y_1411_ = v___y_1422_;
v___y_1412_ = v_ref_1429_;
v___y_1413_ = v___y_1423_;
v___y_1414_ = v___y_1428_;
v___y_1415_ = v___y_1425_;
v___y_1416_ = v___y_1426_;
v___y_1417_ = v___y_1427_;
v___y_1418_ = v_val_1432_;
goto v___jp_1410_;
}
}
v___jp_1434_:
{
if (v___y_1441_ == 0)
{
v___y_1422_ = v___y_1435_;
v___y_1423_ = v___y_1440_;
v___y_1424_ = v___y_1436_;
v___y_1425_ = v___y_1437_;
v___y_1426_ = v___y_1438_;
v___y_1427_ = v___y_1439_;
v___y_1428_ = v_severity_1344_;
goto v___jp_1421_;
}
else
{
v___y_1422_ = v___y_1435_;
v___y_1423_ = v___y_1440_;
v___y_1424_ = v___y_1436_;
v___y_1425_ = v___y_1437_;
v___y_1426_ = v___y_1438_;
v___y_1427_ = v___y_1439_;
v___y_1428_ = v___x_1433_;
goto v___jp_1421_;
}
}
v___jp_1442_:
{
if (v___y_1443_ == 0)
{
lean_object* v_fileName_1444_; lean_object* v_fileMap_1445_; lean_object* v_options_1446_; lean_object* v_ref_1447_; uint8_t v_suppressElabErrors_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___f_1451_; uint8_t v___x_1452_; uint8_t v___x_1453_; 
v_fileName_1444_ = lean_ctor_get(v___y_1346_, 0);
v_fileMap_1445_ = lean_ctor_get(v___y_1346_, 1);
v_options_1446_ = lean_ctor_get(v___y_1346_, 2);
v_ref_1447_ = lean_ctor_get(v___y_1346_, 5);
v_suppressElabErrors_1448_ = lean_ctor_get_uint8(v___y_1346_, sizeof(void*)*14 + 1);
v___x_1449_ = lean_box(v___y_1443_);
v___x_1450_ = lean_box(v_suppressElabErrors_1448_);
v___f_1451_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1451_, 0, v___x_1449_);
lean_closure_set(v___f_1451_, 1, v___x_1450_);
v___x_1452_ = 1;
v___x_1453_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1344_, v___x_1452_);
if (v___x_1453_ == 0)
{
v___y_1435_ = v___f_1451_;
v___y_1436_ = v_ref_1447_;
v___y_1437_ = v_fileName_1444_;
v___y_1438_ = v_suppressElabErrors_1448_;
v___y_1439_ = v_fileMap_1445_;
v___y_1440_ = v___y_1443_;
v___y_1441_ = v___x_1453_;
goto v___jp_1434_;
}
else
{
lean_object* v___x_1454_; uint8_t v___x_1455_; 
v___x_1454_ = l_Lean_warningAsError;
v___x_1455_ = l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0_spec__3(v_options_1446_, v___x_1454_);
v___y_1435_ = v___f_1451_;
v___y_1436_ = v_ref_1447_;
v___y_1437_ = v_fileName_1444_;
v___y_1438_ = v_suppressElabErrors_1448_;
v___y_1439_ = v_fileMap_1445_;
v___y_1440_ = v___y_1443_;
v___y_1441_ = v___x_1455_;
goto v___jp_1434_;
}
}
else
{
lean_object* v___x_1456_; lean_object* v___x_1457_; 
lean_dec_ref(v_msgData_1343_);
v___x_1456_ = lean_box(0);
v___x_1457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1457_, 0, v___x_1456_);
return v___x_1457_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___boxed(lean_object* v_ref_1460_, lean_object* v_msgData_1461_, lean_object* v_severity_1462_, lean_object* v_isSilent_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_){
_start:
{
uint8_t v_severity_boxed_1467_; uint8_t v_isSilent_boxed_1468_; lean_object* v_res_1469_; 
v_severity_boxed_1467_ = lean_unbox(v_severity_1462_);
v_isSilent_boxed_1468_ = lean_unbox(v_isSilent_1463_);
v_res_1469_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6(v_ref_1460_, v_msgData_1461_, v_severity_boxed_1467_, v_isSilent_boxed_1468_, v___y_1464_, v___y_1465_);
lean_dec(v___y_1465_);
lean_dec_ref(v___y_1464_);
lean_dec(v_ref_1460_);
return v_res_1469_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5(lean_object* v_msgData_1470_, uint8_t v_severity_1471_, uint8_t v_isSilent_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_){
_start:
{
lean_object* v_ref_1476_; lean_object* v___x_1477_; 
v_ref_1476_ = lean_ctor_get(v___y_1473_, 5);
v___x_1477_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6(v_ref_1476_, v_msgData_1470_, v_severity_1471_, v_isSilent_1472_, v___y_1473_, v___y_1474_);
return v___x_1477_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5___boxed(lean_object* v_msgData_1478_, lean_object* v_severity_1479_, lean_object* v_isSilent_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_){
_start:
{
uint8_t v_severity_boxed_1484_; uint8_t v_isSilent_boxed_1485_; lean_object* v_res_1486_; 
v_severity_boxed_1484_ = lean_unbox(v_severity_1479_);
v_isSilent_boxed_1485_ = lean_unbox(v_isSilent_1480_);
v_res_1486_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5(v_msgData_1478_, v_severity_boxed_1484_, v_isSilent_boxed_1485_, v___y_1481_, v___y_1482_);
lean_dec(v___y_1482_);
lean_dec_ref(v___y_1481_);
return v_res_1486_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1(lean_object* v_msgData_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_){
_start:
{
uint8_t v___x_1491_; uint8_t v___x_1492_; lean_object* v___x_1493_; 
v___x_1491_ = 1;
v___x_1492_ = 0;
v___x_1493_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5(v_msgData_1487_, v___x_1491_, v___x_1492_, v___y_1488_, v___y_1489_);
return v___x_1493_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1___boxed(lean_object* v_msgData_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_){
_start:
{
lean_object* v_res_1498_; 
v_res_1498_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1(v_msgData_1494_, v___y_1495_, v___y_1496_);
lean_dec(v___y_1496_);
lean_dec_ref(v___y_1495_);
return v_res_1498_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0___redArg(lean_object* v_opt_1499_, lean_object* v___y_1500_){
_start:
{
lean_object* v_options_1502_; uint8_t v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; 
v_options_1502_ = lean_ctor_get(v___y_1500_, 2);
v___x_1503_ = l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0_spec__3(v_options_1502_, v_opt_1499_);
v___x_1504_ = lean_box(v___x_1503_);
v___x_1505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1505_, 0, v___x_1504_);
return v___x_1505_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0___redArg___boxed(lean_object* v_opt_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_){
_start:
{
lean_object* v_res_1509_; 
v_res_1509_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0___redArg(v_opt_1506_, v___y_1507_);
lean_dec_ref(v___y_1507_);
lean_dec_ref(v_opt_1506_);
return v_res_1509_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1511_; lean_object* v___x_1512_; 
v___x_1511_ = ((lean_object*)(l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__0));
v___x_1512_ = l_Lean_stringToMessageData(v___x_1511_);
return v___x_1512_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__3(void){
_start:
{
lean_object* v___x_1514_; lean_object* v___x_1515_; 
v___x_1514_ = ((lean_object*)(l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__2));
v___x_1515_ = l_Lean_stringToMessageData(v___x_1514_);
return v___x_1515_;
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0(lean_object* v_id_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_){
_start:
{
lean_object* v___x_1520_; lean_object* v_env_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v_a_1524_; lean_object* v___x_1526_; uint8_t v_isShared_1527_; uint8_t v_isSharedCheck_1543_; 
v___x_1520_ = lean_st_ref_get(v___y_1518_);
v_env_1521_ = lean_ctor_get(v___x_1520_, 0);
lean_inc_ref(v_env_1521_);
lean_dec(v___x_1520_);
v___x_1522_ = l_Lean_ResolveName_backward_privateInPublic_warn;
v___x_1523_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0___redArg(v___x_1522_, v___y_1517_);
v_a_1524_ = lean_ctor_get(v___x_1523_, 0);
v_isSharedCheck_1543_ = !lean_is_exclusive(v___x_1523_);
if (v_isSharedCheck_1543_ == 0)
{
v___x_1526_ = v___x_1523_;
v_isShared_1527_ = v_isSharedCheck_1543_;
goto v_resetjp_1525_;
}
else
{
lean_inc(v_a_1524_);
lean_dec(v___x_1523_);
v___x_1526_ = lean_box(0);
v_isShared_1527_ = v_isSharedCheck_1543_;
goto v_resetjp_1525_;
}
v_resetjp_1525_:
{
uint8_t v_isExporting_1533_; 
v_isExporting_1533_ = lean_ctor_get_uint8(v_env_1521_, sizeof(void*)*8);
lean_dec_ref(v_env_1521_);
if (v_isExporting_1533_ == 0)
{
lean_dec(v_a_1524_);
lean_dec(v_id_1516_);
goto v___jp_1528_;
}
else
{
uint8_t v___x_1534_; 
v___x_1534_ = l_Lean_isPrivateName(v_id_1516_);
if (v___x_1534_ == 0)
{
lean_dec(v_a_1524_);
lean_dec(v_id_1516_);
goto v___jp_1528_;
}
else
{
uint8_t v___x_1535_; 
v___x_1535_ = lean_unbox(v_a_1524_);
lean_dec(v_a_1524_);
if (v___x_1535_ == 0)
{
lean_dec(v_id_1516_);
goto v___jp_1528_;
}
else
{
lean_object* v___x_1536_; uint8_t v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; 
lean_del_object(v___x_1526_);
v___x_1536_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__1, &l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__1_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__1);
v___x_1537_ = 0;
v___x_1538_ = l_Lean_MessageData_ofConstName(v_id_1516_, v___x_1537_);
v___x_1539_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1539_, 0, v___x_1536_);
lean_ctor_set(v___x_1539_, 1, v___x_1538_);
v___x_1540_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__3, &l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__3_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__3);
v___x_1541_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1541_, 0, v___x_1539_);
lean_ctor_set(v___x_1541_, 1, v___x_1540_);
v___x_1542_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1(v___x_1541_, v___y_1517_, v___y_1518_);
return v___x_1542_;
}
}
}
v___jp_1528_:
{
lean_object* v___x_1529_; lean_object* v___x_1531_; 
v___x_1529_ = lean_box(0);
if (v_isShared_1527_ == 0)
{
lean_ctor_set(v___x_1526_, 0, v___x_1529_);
v___x_1531_ = v___x_1526_;
goto v_reusejp_1530_;
}
else
{
lean_object* v_reuseFailAlloc_1532_; 
v_reuseFailAlloc_1532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1532_, 0, v___x_1529_);
v___x_1531_ = v_reuseFailAlloc_1532_;
goto v_reusejp_1530_;
}
v_reusejp_1530_:
{
return v___x_1531_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___boxed(lean_object* v_id_1544_, lean_object* v___y_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_){
_start:
{
lean_object* v_res_1548_; 
v_res_1548_ = l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0(v_id_1544_, v___y_1545_, v___y_1546_);
lean_dec(v___y_1546_);
lean_dec_ref(v___y_1545_);
return v_res_1548_;
}
}
static lean_object* _init_l_Lean_ensureAttrDeclIsPublic___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1550_; lean_object* v___x_1551_; 
v___x_1550_ = ((lean_object*)(l_Lean_ensureAttrDeclIsPublic___lam__0___closed__0));
v___x_1551_ = l_Lean_stringToMessageData(v___x_1550_);
return v___x_1551_;
}
}
LEAN_EXPORT lean_object* l_Lean_ensureAttrDeclIsPublic___lam__0(lean_object* v_declName_1552_, uint8_t v_isModule_1553_, lean_object* v_attrName_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_){
_start:
{
lean_object* v___x_1558_; 
lean_inc(v_declName_1552_);
v___x_1558_ = l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0(v_declName_1552_, v___y_1555_, v___y_1556_);
if (lean_obj_tag(v___x_1558_) == 0)
{
lean_object* v___x_1559_; lean_object* v_a_1560_; lean_object* v___x_1562_; uint8_t v_isShared_1563_; uint8_t v_isSharedCheck_1580_; 
lean_dec_ref(v___x_1558_);
lean_inc(v_declName_1552_);
v___x_1559_ = l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1___redArg(v_declName_1552_, v_isModule_1553_, v___y_1556_);
v_a_1560_ = lean_ctor_get(v___x_1559_, 0);
v_isSharedCheck_1580_ = !lean_is_exclusive(v___x_1559_);
if (v_isSharedCheck_1580_ == 0)
{
v___x_1562_ = v___x_1559_;
v_isShared_1563_ = v_isSharedCheck_1580_;
goto v_resetjp_1561_;
}
else
{
lean_inc(v_a_1560_);
lean_dec(v___x_1559_);
v___x_1562_ = lean_box(0);
v_isShared_1563_ = v_isSharedCheck_1580_;
goto v_resetjp_1561_;
}
v_resetjp_1561_:
{
uint8_t v___x_1564_; 
v___x_1564_ = lean_unbox(v_a_1560_);
if (v___x_1564_ == 0)
{
lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; uint8_t v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; 
lean_del_object(v___x_1562_);
v___x_1565_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1);
v___x_1566_ = l_Lean_MessageData_ofName(v_attrName_1554_);
v___x_1567_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1567_, 0, v___x_1565_);
lean_ctor_set(v___x_1567_, 1, v___x_1566_);
v___x_1568_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1, &l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1);
v___x_1569_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1569_, 0, v___x_1567_);
lean_ctor_set(v___x_1569_, 1, v___x_1568_);
v___x_1570_ = lean_unbox(v_a_1560_);
lean_dec(v_a_1560_);
v___x_1571_ = l_Lean_MessageData_ofConstName(v_declName_1552_, v___x_1570_);
v___x_1572_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1572_, 0, v___x_1569_);
lean_ctor_set(v___x_1572_, 1, v___x_1571_);
v___x_1573_ = lean_obj_once(&l_Lean_ensureAttrDeclIsPublic___lam__0___closed__1, &l_Lean_ensureAttrDeclIsPublic___lam__0___closed__1_once, _init_l_Lean_ensureAttrDeclIsPublic___lam__0___closed__1);
v___x_1574_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1574_, 0, v___x_1572_);
lean_ctor_set(v___x_1574_, 1, v___x_1573_);
v___x_1575_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0_spec__0___redArg(v___x_1574_, v___y_1555_, v___y_1556_);
return v___x_1575_;
}
else
{
lean_object* v___x_1576_; lean_object* v___x_1578_; 
lean_dec(v_a_1560_);
lean_dec(v_attrName_1554_);
lean_dec(v_declName_1552_);
v___x_1576_ = lean_box(0);
if (v_isShared_1563_ == 0)
{
lean_ctor_set(v___x_1562_, 0, v___x_1576_);
v___x_1578_ = v___x_1562_;
goto v_reusejp_1577_;
}
else
{
lean_object* v_reuseFailAlloc_1579_; 
v_reuseFailAlloc_1579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1579_, 0, v___x_1576_);
v___x_1578_ = v_reuseFailAlloc_1579_;
goto v_reusejp_1577_;
}
v_reusejp_1577_:
{
return v___x_1578_;
}
}
}
}
else
{
lean_dec(v_attrName_1554_);
lean_dec(v_declName_1552_);
return v___x_1558_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ensureAttrDeclIsPublic___lam__0___boxed(lean_object* v_declName_1581_, lean_object* v_isModule_1582_, lean_object* v_attrName_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_){
_start:
{
uint8_t v_isModule_boxed_1587_; lean_object* v_res_1588_; 
v_isModule_boxed_1587_ = lean_unbox(v_isModule_1582_);
v_res_1588_ = l_Lean_ensureAttrDeclIsPublic___lam__0(v_declName_1581_, v_isModule_boxed_1587_, v_attrName_1583_, v___y_1584_, v___y_1585_);
lean_dec(v___y_1585_);
lean_dec_ref(v___y_1584_);
return v_res_1588_;
}
}
LEAN_EXPORT lean_object* l_Lean_ensureAttrDeclIsPublic(lean_object* v_attrName_1589_, lean_object* v_declName_1590_, uint8_t v_attrKind_1591_, lean_object* v_a_1592_, lean_object* v_a_1593_){
_start:
{
lean_object* v___x_1595_; lean_object* v_env_1599_; lean_object* v___x_1600_; uint8_t v_isModule_1601_; 
v___x_1595_ = lean_st_ref_get(v_a_1593_);
v_env_1599_ = lean_ctor_get(v___x_1595_, 0);
lean_inc_ref(v_env_1599_);
lean_dec(v___x_1595_);
v___x_1600_ = l_Lean_Environment_header(v_env_1599_);
lean_dec_ref(v_env_1599_);
v_isModule_1601_ = lean_ctor_get_uint8(v___x_1600_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_1600_);
if (v_isModule_1601_ == 0)
{
lean_dec(v_declName_1590_);
lean_dec(v_attrName_1589_);
goto v___jp_1596_;
}
else
{
uint8_t v___x_1602_; uint8_t v___x_1603_; 
v___x_1602_ = 1;
v___x_1603_ = l_Lean_instBEqAttributeKind_beq(v_attrKind_1591_, v___x_1602_);
if (v___x_1603_ == 0)
{
lean_object* v___x_1604_; lean_object* v___f_1605_; lean_object* v___x_1606_; 
v___x_1604_ = lean_box(v_isModule_1601_);
v___f_1605_ = lean_alloc_closure((void*)(l_Lean_ensureAttrDeclIsPublic___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1605_, 0, v_declName_1590_);
lean_closure_set(v___f_1605_, 1, v___x_1604_);
lean_closure_set(v___f_1605_, 2, v_attrName_1589_);
v___x_1606_ = l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg(v___f_1605_, v_isModule_1601_, v_a_1592_, v_a_1593_);
return v___x_1606_;
}
else
{
lean_dec(v_declName_1590_);
lean_dec(v_attrName_1589_);
goto v___jp_1596_;
}
}
v___jp_1596_:
{
lean_object* v___x_1597_; lean_object* v___x_1598_; 
v___x_1597_ = lean_box(0);
v___x_1598_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1598_, 0, v___x_1597_);
return v___x_1598_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ensureAttrDeclIsPublic___boxed(lean_object* v_attrName_1607_, lean_object* v_declName_1608_, lean_object* v_attrKind_1609_, lean_object* v_a_1610_, lean_object* v_a_1611_, lean_object* v_a_1612_){
_start:
{
uint8_t v_attrKind_boxed_1613_; lean_object* v_res_1614_; 
v_attrKind_boxed_1613_ = lean_unbox(v_attrKind_1609_);
v_res_1614_ = l_Lean_ensureAttrDeclIsPublic(v_attrName_1607_, v_declName_1608_, v_attrKind_boxed_1613_, v_a_1610_, v_a_1611_);
lean_dec(v_a_1611_);
lean_dec_ref(v_a_1610_);
return v_res_1614_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0(lean_object* v_opt_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_){
_start:
{
lean_object* v___x_1619_; 
v___x_1619_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0___redArg(v_opt_1615_, v___y_1616_);
return v___x_1619_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0___boxed(lean_object* v_opt_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_){
_start:
{
lean_object* v_res_1624_; 
v_res_1624_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0(v_opt_1620_, v___y_1621_, v___y_1622_);
lean_dec(v___y_1622_);
lean_dec_ref(v___y_1621_);
lean_dec_ref(v_opt_1620_);
return v_res_1624_;
}
}
static lean_object* _init_l_Lean_ensureAttrDeclIsMeta___closed__1(void){
_start:
{
lean_object* v___x_1626_; lean_object* v___x_1627_; 
v___x_1626_ = ((lean_object*)(l_Lean_ensureAttrDeclIsMeta___closed__0));
v___x_1627_ = l_Lean_stringToMessageData(v___x_1626_);
return v___x_1627_;
}
}
LEAN_EXPORT lean_object* l_Lean_ensureAttrDeclIsMeta(lean_object* v_attrName_1628_, lean_object* v_declName_1629_, uint8_t v_attrKind_1630_, lean_object* v_a_1631_, lean_object* v_a_1632_){
_start:
{
lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v_env_1636_; lean_object* v___x_1637_; uint8_t v_isModule_1638_; 
v___x_1634_ = lean_st_ref_get(v_a_1632_);
v___x_1635_ = lean_st_ref_get(v_a_1632_);
v_env_1636_ = lean_ctor_get(v___x_1634_, 0);
lean_inc_ref(v_env_1636_);
lean_dec(v___x_1634_);
v___x_1637_ = l_Lean_Environment_header(v_env_1636_);
lean_dec_ref(v_env_1636_);
v_isModule_1638_ = lean_ctor_get_uint8(v___x_1637_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_1637_);
if (v_isModule_1638_ == 0)
{
lean_object* v___x_1639_; 
lean_dec(v___x_1635_);
v___x_1639_ = l_Lean_ensureAttrDeclIsPublic(v_attrName_1628_, v_declName_1629_, v_attrKind_1630_, v_a_1631_, v_a_1632_);
return v___x_1639_;
}
else
{
lean_object* v_env_1640_; uint8_t v___x_1641_; 
v_env_1640_ = lean_ctor_get(v___x_1635_, 0);
lean_inc_ref(v_env_1640_);
lean_dec(v___x_1635_);
lean_inc(v_declName_1629_);
v___x_1641_ = l_Lean_isMarkedMeta(v_env_1640_, v_declName_1629_);
if (v___x_1641_ == 0)
{
lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; 
v___x_1642_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1);
v___x_1643_ = l_Lean_MessageData_ofName(v_attrName_1628_);
v___x_1644_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1644_, 0, v___x_1642_);
lean_ctor_set(v___x_1644_, 1, v___x_1643_);
v___x_1645_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1, &l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1);
v___x_1646_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1646_, 0, v___x_1644_);
lean_ctor_set(v___x_1646_, 1, v___x_1645_);
v___x_1647_ = l_Lean_MessageData_ofConstName(v_declName_1629_, v___x_1641_);
v___x_1648_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1648_, 0, v___x_1646_);
lean_ctor_set(v___x_1648_, 1, v___x_1647_);
v___x_1649_ = lean_obj_once(&l_Lean_ensureAttrDeclIsMeta___closed__1, &l_Lean_ensureAttrDeclIsMeta___closed__1_once, _init_l_Lean_ensureAttrDeclIsMeta___closed__1);
v___x_1650_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1650_, 0, v___x_1648_);
lean_ctor_set(v___x_1650_, 1, v___x_1649_);
v___x_1651_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0_spec__0___redArg(v___x_1650_, v_a_1631_, v_a_1632_);
return v___x_1651_;
}
else
{
lean_object* v___x_1652_; 
v___x_1652_ = l_Lean_ensureAttrDeclIsPublic(v_attrName_1628_, v_declName_1629_, v_attrKind_1630_, v_a_1631_, v_a_1632_);
return v___x_1652_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ensureAttrDeclIsMeta___boxed(lean_object* v_attrName_1653_, lean_object* v_declName_1654_, lean_object* v_attrKind_1655_, lean_object* v_a_1656_, lean_object* v_a_1657_, lean_object* v_a_1658_){
_start:
{
uint8_t v_attrKind_boxed_1659_; lean_object* v_res_1660_; 
v_attrKind_boxed_1659_ = lean_unbox(v_attrKind_1655_);
v_res_1660_ = l_Lean_ensureAttrDeclIsMeta(v_attrName_1653_, v_declName_1654_, v_attrKind_boxed_1659_, v_a_1656_, v_a_1657_);
lean_dec(v_a_1657_);
lean_dec_ref(v_a_1656_);
return v_res_1660_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__0(lean_object* v_x_1664_, lean_object* v___y_1665_){
_start:
{
lean_object* v___x_1667_; lean_object* v___x_1668_; 
v___x_1667_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___lam__0___closed__1));
v___x_1668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1668_, 0, v___x_1667_);
return v___x_1668_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__0___boxed(lean_object* v_x_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_){
_start:
{
lean_object* v_res_1672_; 
v_res_1672_ = l_Lean_instInhabitedTagAttribute_default___lam__0(v_x_1669_, v___y_1670_);
lean_dec_ref(v___y_1670_);
lean_dec_ref(v_x_1669_);
return v_res_1672_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__1(lean_object* v_s_1673_, lean_object* v_x_1674_){
_start:
{
lean_inc(v_s_1673_);
return v_s_1673_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__1___boxed(lean_object* v_s_1675_, lean_object* v_x_1676_){
_start:
{
lean_object* v_res_1677_; 
v_res_1677_ = l_Lean_instInhabitedTagAttribute_default___lam__1(v_s_1675_, v_x_1676_);
lean_dec(v_x_1676_);
lean_dec(v_s_1675_);
return v_res_1677_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__2(lean_object* v_x_1682_, lean_object* v_x_1683_){
_start:
{
lean_object* v___x_1684_; 
v___x_1684_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___lam__2___closed__1));
return v___x_1684_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__2___boxed(lean_object* v_x_1685_, lean_object* v_x_1686_){
_start:
{
lean_object* v_res_1687_; 
v_res_1687_ = l_Lean_instInhabitedTagAttribute_default___lam__2(v_x_1685_, v_x_1686_);
lean_dec(v_x_1686_);
lean_dec_ref(v_x_1685_);
return v_res_1687_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__3(lean_object* v_x_1688_){
_start:
{
lean_object* v___x_1689_; 
v___x_1689_ = lean_box(0);
return v___x_1689_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__3___boxed(lean_object* v_x_1690_){
_start:
{
lean_object* v_res_1691_; 
v_res_1691_ = l_Lean_instInhabitedTagAttribute_default___lam__3(v_x_1690_);
lean_dec(v_x_1690_);
return v_res_1691_;
}
}
static lean_object* _init_l_Lean_instInhabitedTagAttribute_default___closed__4(void){
_start:
{
lean_object* v___x_1696_; 
v___x_1696_ = l_Lean_instInhabitedEnvExtension_default(lean_box(0));
return v___x_1696_;
}
}
static lean_object* _init_l_Lean_instInhabitedTagAttribute_default___closed__5(void){
_start:
{
lean_object* v___f_1697_; lean_object* v___f_1698_; lean_object* v___f_1699_; lean_object* v___f_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; 
v___f_1697_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___closed__3));
v___f_1698_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___closed__2));
v___f_1699_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___closed__1));
v___f_1700_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___closed__0));
v___x_1701_ = lean_box(0);
v___x_1702_ = lean_obj_once(&l_Lean_instInhabitedTagAttribute_default___closed__4, &l_Lean_instInhabitedTagAttribute_default___closed__4_once, _init_l_Lean_instInhabitedTagAttribute_default___closed__4);
v___x_1703_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1703_, 0, v___x_1702_);
lean_ctor_set(v___x_1703_, 1, v___x_1701_);
lean_ctor_set(v___x_1703_, 2, v___f_1700_);
lean_ctor_set(v___x_1703_, 3, v___f_1699_);
lean_ctor_set(v___x_1703_, 4, v___f_1698_);
lean_ctor_set(v___x_1703_, 5, v___f_1697_);
return v___x_1703_;
}
}
static lean_object* _init_l_Lean_instInhabitedTagAttribute_default___closed__6(void){
_start:
{
lean_object* v___x_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; 
v___x_1704_ = lean_obj_once(&l_Lean_instInhabitedTagAttribute_default___closed__5, &l_Lean_instInhabitedTagAttribute_default___closed__5_once, _init_l_Lean_instInhabitedTagAttribute_default___closed__5);
v___x_1705_ = ((lean_object*)(l_Lean_instInhabitedAttributeImpl_default));
v___x_1706_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1706_, 0, v___x_1705_);
lean_ctor_set(v___x_1706_, 1, v___x_1704_);
return v___x_1706_;
}
}
static lean_object* _init_l_Lean_instInhabitedTagAttribute_default(void){
_start:
{
lean_object* v___x_1707_; 
v___x_1707_ = lean_obj_once(&l_Lean_instInhabitedTagAttribute_default___closed__6, &l_Lean_instInhabitedTagAttribute_default___closed__6_once, _init_l_Lean_instInhabitedTagAttribute_default___closed__6);
return v___x_1707_;
}
}
static lean_object* _init_l_Lean_instInhabitedTagAttribute(void){
_start:
{
lean_object* v___x_1708_; 
v___x_1708_ = l_Lean_instInhabitedTagAttribute_default;
return v___x_1708_;
}
}
static lean_object* _init_l_Lean_registerTagAttribute___auto__1(void){
_start:
{
lean_object* v___x_1709_; 
v___x_1709_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__28, &l_Lean_AttributeImplCore_ref___autoParam___closed__28_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__28);
return v___x_1709_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__0(lean_object* v_x_1710_){
_start:
{
lean_object* v___x_1711_; 
v___x_1711_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___lam__2___closed__0));
return v___x_1711_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__0___boxed(lean_object* v_x_1712_){
_start:
{
lean_object* v_res_1713_; 
v_res_1713_ = l_Lean_registerTagAttribute___lam__0(v_x_1712_);
lean_dec(v_x_1712_);
return v_res_1713_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerTagAttribute_spec__0(lean_object* v_newState_1714_, lean_object* v_x_1715_, lean_object* v_x_1716_){
_start:
{
if (lean_obj_tag(v_x_1716_) == 0)
{
return v_x_1715_;
}
else
{
lean_object* v_head_1717_; lean_object* v_tail_1718_; uint8_t v___x_1719_; 
v_head_1717_ = lean_ctor_get(v_x_1716_, 0);
lean_inc(v_head_1717_);
v_tail_1718_ = lean_ctor_get(v_x_1716_, 1);
lean_inc(v_tail_1718_);
lean_dec_ref(v_x_1716_);
v___x_1719_ = l_Lean_NameSet_contains(v_newState_1714_, v_head_1717_);
if (v___x_1719_ == 0)
{
lean_dec(v_head_1717_);
v_x_1716_ = v_tail_1718_;
goto _start;
}
else
{
lean_object* v___x_1721_; 
v___x_1721_ = l_Lean_NameSet_insert(v_x_1715_, v_head_1717_);
v_x_1715_ = v___x_1721_;
v_x_1716_ = v_tail_1718_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerTagAttribute_spec__0___boxed(lean_object* v_newState_1723_, lean_object* v_x_1724_, lean_object* v_x_1725_){
_start:
{
lean_object* v_res_1726_; 
v_res_1726_ = l_List_foldl___at___00Lean_registerTagAttribute_spec__0(v_newState_1723_, v_x_1724_, v_x_1725_);
lean_dec(v_newState_1723_);
return v_res_1726_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__1(lean_object* v_x_1727_, lean_object* v_newState_1728_, lean_object* v_newConsts_1729_, lean_object* v_s_1730_){
_start:
{
lean_object* v___x_1731_; 
v___x_1731_ = l_List_foldl___at___00Lean_registerTagAttribute_spec__0(v_newState_1728_, v_s_1730_, v_newConsts_1729_);
return v___x_1731_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__1___boxed(lean_object* v_x_1732_, lean_object* v_newState_1733_, lean_object* v_newConsts_1734_, lean_object* v_s_1735_){
_start:
{
lean_object* v_res_1736_; 
v_res_1736_ = l_Lean_registerTagAttribute___lam__1(v_x_1732_, v_newState_1733_, v_newConsts_1734_, v_s_1735_);
lean_dec(v_newState_1733_);
lean_dec(v_x_1732_);
return v_res_1736_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__2(lean_object* v_s_1749_){
_start:
{
lean_object* v___x_1750_; lean_object* v___y_1752_; 
v___x_1750_ = ((lean_object*)(l_Lean_registerTagAttribute___lam__2___closed__5));
if (lean_obj_tag(v_s_1749_) == 0)
{
lean_object* v_size_1756_; 
v_size_1756_ = lean_ctor_get(v_s_1749_, 0);
lean_inc(v_size_1756_);
lean_dec_ref(v_s_1749_);
v___y_1752_ = v_size_1756_;
goto v___jp_1751_;
}
else
{
lean_object* v___x_1757_; 
v___x_1757_ = lean_unsigned_to_nat(0u);
v___y_1752_ = v___x_1757_;
goto v___jp_1751_;
}
v___jp_1751_:
{
lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; 
v___x_1753_ = l_Nat_reprFast(v___y_1752_);
v___x_1754_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1754_, 0, v___x_1753_);
v___x_1755_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1755_, 0, v___x_1750_);
lean_ctor_set(v___x_1755_, 1, v___x_1754_);
return v___x_1755_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___redArg(lean_object* v_as_1759_, lean_object* v_lo_1760_, lean_object* v_hi_1761_){
_start:
{
uint8_t v___x_1762_; 
v___x_1762_ = lean_nat_dec_lt(v_lo_1760_, v_hi_1761_);
if (v___x_1762_ == 0)
{
lean_dec(v_lo_1760_);
return v_as_1759_;
}
else
{
lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v_fst_1765_; lean_object* v_snd_1766_; uint8_t v___x_1767_; 
v___x_1763_ = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___redArg___closed__0));
lean_inc(v_lo_1760_);
v___x_1764_ = l_Array_qpartition___redArg(v_as_1759_, v___x_1763_, v_lo_1760_, v_hi_1761_);
v_fst_1765_ = lean_ctor_get(v___x_1764_, 0);
lean_inc(v_fst_1765_);
v_snd_1766_ = lean_ctor_get(v___x_1764_, 1);
lean_inc(v_snd_1766_);
lean_dec_ref(v___x_1764_);
v___x_1767_ = lean_nat_dec_le(v_hi_1761_, v_fst_1765_);
if (v___x_1767_ == 0)
{
lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; 
v___x_1768_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___redArg(v_snd_1766_, v_lo_1760_, v_fst_1765_);
v___x_1769_ = lean_unsigned_to_nat(1u);
v___x_1770_ = lean_nat_add(v_fst_1765_, v___x_1769_);
lean_dec(v_fst_1765_);
v_as_1759_ = v___x_1768_;
v_lo_1760_ = v___x_1770_;
goto _start;
}
else
{
lean_dec(v_fst_1765_);
lean_dec(v_lo_1760_);
return v_snd_1766_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___redArg___boxed(lean_object* v_as_1772_, lean_object* v_lo_1773_, lean_object* v_hi_1774_){
_start:
{
lean_object* v_res_1775_; 
v_res_1775_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___redArg(v_as_1772_, v_lo_1773_, v_hi_1774_);
lean_dec(v_hi_1774_);
return v_res_1775_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerTagAttribute_spec__2(lean_object* v_env_1776_, lean_object* v_as_1777_, size_t v_i_1778_, size_t v_stop_1779_, lean_object* v_b_1780_){
_start:
{
lean_object* v___y_1782_; uint8_t v___x_1786_; 
v___x_1786_ = lean_usize_dec_eq(v_i_1778_, v_stop_1779_);
if (v___x_1786_ == 0)
{
lean_object* v___x_1787_; uint8_t v___x_1788_; lean_object* v___x_1789_; uint8_t v___x_1790_; 
v___x_1787_ = lean_array_uget_borrowed(v_as_1777_, v_i_1778_);
v___x_1788_ = 1;
lean_inc_ref(v_env_1776_);
v___x_1789_ = l_Lean_Environment_setExporting(v_env_1776_, v___x_1788_);
lean_inc(v___x_1787_);
v___x_1790_ = l_Lean_Environment_contains(v___x_1789_, v___x_1787_, v___x_1786_);
if (v___x_1790_ == 0)
{
v___y_1782_ = v_b_1780_;
goto v___jp_1781_;
}
else
{
lean_object* v___x_1791_; 
lean_inc(v___x_1787_);
v___x_1791_ = lean_array_push(v_b_1780_, v___x_1787_);
v___y_1782_ = v___x_1791_;
goto v___jp_1781_;
}
}
else
{
lean_dec_ref(v_env_1776_);
return v_b_1780_;
}
v___jp_1781_:
{
size_t v___x_1783_; size_t v___x_1784_; 
v___x_1783_ = ((size_t)1ULL);
v___x_1784_ = lean_usize_add(v_i_1778_, v___x_1783_);
v_i_1778_ = v___x_1784_;
v_b_1780_ = v___y_1782_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerTagAttribute_spec__2___boxed(lean_object* v_env_1792_, lean_object* v_as_1793_, lean_object* v_i_1794_, lean_object* v_stop_1795_, lean_object* v_b_1796_){
_start:
{
size_t v_i_boxed_1797_; size_t v_stop_boxed_1798_; lean_object* v_res_1799_; 
v_i_boxed_1797_ = lean_unbox_usize(v_i_1794_);
lean_dec(v_i_1794_);
v_stop_boxed_1798_ = lean_unbox_usize(v_stop_1795_);
lean_dec(v_stop_1795_);
v_res_1799_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerTagAttribute_spec__2(v_env_1792_, v_as_1793_, v_i_boxed_1797_, v_stop_boxed_1798_, v_b_1796_);
lean_dec_ref(v_as_1793_);
return v_res_1799_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerTagAttribute_spec__1_spec__1(lean_object* v_init_1800_, lean_object* v_x_1801_){
_start:
{
if (lean_obj_tag(v_x_1801_) == 0)
{
lean_object* v_k_1802_; lean_object* v_l_1803_; lean_object* v_r_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; 
v_k_1802_ = lean_ctor_get(v_x_1801_, 1);
lean_inc(v_k_1802_);
v_l_1803_ = lean_ctor_get(v_x_1801_, 3);
lean_inc(v_l_1803_);
v_r_1804_ = lean_ctor_get(v_x_1801_, 4);
lean_inc(v_r_1804_);
lean_dec_ref(v_x_1801_);
v___x_1805_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerTagAttribute_spec__1_spec__1(v_init_1800_, v_l_1803_);
v___x_1806_ = lean_array_push(v___x_1805_, v_k_1802_);
v_init_1800_ = v___x_1806_;
v_x_1801_ = v_r_1804_;
goto _start;
}
else
{
return v_init_1800_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__3(lean_object* v_env_1808_, lean_object* v_es_1809_){
_start:
{
lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___y_1813_; lean_object* v___x_1827_; lean_object* v___y_1829_; lean_object* v___y_1830_; lean_object* v___x_1832_; uint8_t v___x_1833_; 
v___x_1810_ = lean_unsigned_to_nat(0u);
v___x_1811_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___lam__2___closed__0));
v___x_1827_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerTagAttribute_spec__1_spec__1(v___x_1811_, v_es_1809_);
v___x_1832_ = lean_array_get_size(v___x_1827_);
v___x_1833_ = lean_nat_dec_eq(v___x_1832_, v___x_1810_);
if (v___x_1833_ == 0)
{
lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___y_1837_; uint8_t v___x_1839_; 
v___x_1834_ = lean_unsigned_to_nat(1u);
v___x_1835_ = lean_nat_sub(v___x_1832_, v___x_1834_);
v___x_1839_ = lean_nat_dec_le(v___x_1810_, v___x_1835_);
if (v___x_1839_ == 0)
{
lean_inc(v___x_1835_);
v___y_1837_ = v___x_1835_;
goto v___jp_1836_;
}
else
{
v___y_1837_ = v___x_1810_;
goto v___jp_1836_;
}
v___jp_1836_:
{
uint8_t v___x_1838_; 
v___x_1838_ = lean_nat_dec_le(v___y_1837_, v___x_1835_);
if (v___x_1838_ == 0)
{
lean_dec(v___x_1835_);
lean_inc(v___y_1837_);
v___y_1829_ = v___y_1837_;
v___y_1830_ = v___y_1837_;
goto v___jp_1828_;
}
else
{
v___y_1829_ = v___y_1837_;
v___y_1830_ = v___x_1835_;
goto v___jp_1828_;
}
}
}
else
{
v___y_1813_ = v___x_1827_;
goto v___jp_1812_;
}
v___jp_1812_:
{
lean_object* v___x_1814_; uint8_t v___x_1815_; 
v___x_1814_ = lean_array_get_size(v___y_1813_);
v___x_1815_ = lean_nat_dec_lt(v___x_1810_, v___x_1814_);
if (v___x_1815_ == 0)
{
lean_object* v___x_1816_; 
lean_dec_ref(v_env_1808_);
v___x_1816_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1816_, 0, v___x_1811_);
lean_ctor_set(v___x_1816_, 1, v___x_1811_);
lean_ctor_set(v___x_1816_, 2, v___y_1813_);
return v___x_1816_;
}
else
{
uint8_t v___x_1817_; 
v___x_1817_ = lean_nat_dec_le(v___x_1814_, v___x_1814_);
if (v___x_1817_ == 0)
{
if (v___x_1815_ == 0)
{
lean_object* v___x_1818_; 
lean_dec_ref(v_env_1808_);
v___x_1818_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1818_, 0, v___x_1811_);
lean_ctor_set(v___x_1818_, 1, v___x_1811_);
lean_ctor_set(v___x_1818_, 2, v___y_1813_);
return v___x_1818_;
}
else
{
size_t v___x_1819_; size_t v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; 
v___x_1819_ = ((size_t)0ULL);
v___x_1820_ = lean_usize_of_nat(v___x_1814_);
v___x_1821_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerTagAttribute_spec__2(v_env_1808_, v___y_1813_, v___x_1819_, v___x_1820_, v___x_1811_);
lean_inc_ref(v___x_1821_);
v___x_1822_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1822_, 0, v___x_1821_);
lean_ctor_set(v___x_1822_, 1, v___x_1821_);
lean_ctor_set(v___x_1822_, 2, v___y_1813_);
return v___x_1822_;
}
}
else
{
size_t v___x_1823_; size_t v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; 
v___x_1823_ = ((size_t)0ULL);
v___x_1824_ = lean_usize_of_nat(v___x_1814_);
v___x_1825_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerTagAttribute_spec__2(v_env_1808_, v___y_1813_, v___x_1823_, v___x_1824_, v___x_1811_);
lean_inc_ref(v___x_1825_);
v___x_1826_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1826_, 0, v___x_1825_);
lean_ctor_set(v___x_1826_, 1, v___x_1825_);
lean_ctor_set(v___x_1826_, 2, v___y_1813_);
return v___x_1826_;
}
}
}
v___jp_1828_:
{
lean_object* v___x_1831_; 
v___x_1831_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___redArg(v___x_1827_, v___y_1829_, v___y_1830_);
lean_dec(v___y_1830_);
v___y_1813_ = v___x_1831_;
goto v___jp_1812_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__4(lean_object* v___x_1840_, lean_object* v_x_1841_, lean_object* v_x_1842_){
_start:
{
lean_object* v___x_1844_; 
v___x_1844_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1844_, 0, v___x_1840_);
return v___x_1844_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__4___boxed(lean_object* v___x_1845_, lean_object* v_x_1846_, lean_object* v_x_1847_, lean_object* v___y_1848_){
_start:
{
lean_object* v_res_1849_; 
v_res_1849_ = l_Lean_registerTagAttribute___lam__4(v___x_1845_, v_x_1846_, v_x_1847_);
lean_dec_ref(v_x_1847_);
lean_dec_ref(v_x_1846_);
return v_res_1849_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__5(lean_object* v___x_1850_){
_start:
{
lean_object* v___x_1852_; 
v___x_1852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1852_, 0, v___x_1850_);
return v___x_1852_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__5___boxed(lean_object* v___x_1853_, lean_object* v___y_1854_){
_start:
{
lean_object* v_res_1855_; 
v_res_1855_ = l_Lean_registerTagAttribute___lam__5(v___x_1853_);
return v_res_1855_;
}
}
static lean_object* _init_l_Lean_registerTagAttribute___lam__6___closed__1(void){
_start:
{
lean_object* v___x_1857_; lean_object* v___x_1858_; 
v___x_1857_ = ((lean_object*)(l_Lean_registerTagAttribute___lam__6___closed__0));
v___x_1858_ = l_Lean_stringToMessageData(v___x_1857_);
return v___x_1858_;
}
}
static lean_object* _init_l_Lean_registerTagAttribute___lam__6___closed__3(void){
_start:
{
lean_object* v___x_1860_; lean_object* v___x_1861_; 
v___x_1860_ = ((lean_object*)(l_Lean_registerTagAttribute___lam__6___closed__2));
v___x_1861_ = l_Lean_stringToMessageData(v___x_1860_);
return v___x_1861_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__6(lean_object* v_name_1862_, lean_object* v_decl_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_){
_start:
{
lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; 
v___x_1867_ = lean_obj_once(&l_Lean_registerTagAttribute___lam__6___closed__1, &l_Lean_registerTagAttribute___lam__6___closed__1_once, _init_l_Lean_registerTagAttribute___lam__6___closed__1);
v___x_1868_ = l_Lean_MessageData_ofName(v_name_1862_);
v___x_1869_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1869_, 0, v___x_1867_);
lean_ctor_set(v___x_1869_, 1, v___x_1868_);
v___x_1870_ = lean_obj_once(&l_Lean_registerTagAttribute___lam__6___closed__3, &l_Lean_registerTagAttribute___lam__6___closed__3_once, _init_l_Lean_registerTagAttribute___lam__6___closed__3);
v___x_1871_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1871_, 0, v___x_1869_);
lean_ctor_set(v___x_1871_, 1, v___x_1870_);
v___x_1872_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0_spec__0___redArg(v___x_1871_, v___y_1864_, v___y_1865_);
return v___x_1872_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__6___boxed(lean_object* v_name_1873_, lean_object* v_decl_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_){
_start:
{
lean_object* v_res_1878_; 
v_res_1878_ = l_Lean_registerTagAttribute___lam__6(v_name_1873_, v_decl_1874_, v___y_1875_, v___y_1876_);
lean_dec(v___y_1876_);
lean_dec_ref(v___y_1875_);
lean_dec(v_decl_1874_);
return v_res_1878_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg(lean_object* v_attrName_1879_, lean_object* v_declName_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_){
_start:
{
lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; uint8_t v___x_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; 
v___x_1884_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1);
v___x_1885_ = l_Lean_MessageData_ofName(v_attrName_1879_);
v___x_1886_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1886_, 0, v___x_1884_);
lean_ctor_set(v___x_1886_, 1, v___x_1885_);
v___x_1887_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__3, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__3_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__3);
v___x_1888_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1888_, 0, v___x_1886_);
lean_ctor_set(v___x_1888_, 1, v___x_1887_);
v___x_1889_ = 0;
v___x_1890_ = l_Lean_MessageData_ofConstName(v_declName_1880_, v___x_1889_);
v___x_1891_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1891_, 0, v___x_1888_);
lean_ctor_set(v___x_1891_, 1, v___x_1890_);
v___x_1892_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__5, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__5_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__5);
v___x_1893_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1893_, 0, v___x_1891_);
lean_ctor_set(v___x_1893_, 1, v___x_1892_);
v___x_1894_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0_spec__0___redArg(v___x_1893_, v___y_1881_, v___y_1882_);
return v___x_1894_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg___boxed(lean_object* v_attrName_1895_, lean_object* v_declName_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_, lean_object* v___y_1899_){
_start:
{
lean_object* v_res_1900_; 
v_res_1900_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg(v_attrName_1895_, v_declName_1896_, v___y_1897_, v___y_1898_);
lean_dec(v___y_1898_);
lean_dec_ref(v___y_1897_);
return v_res_1900_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___redArg(lean_object* v_attrName_1901_, lean_object* v_declName_1902_, lean_object* v_asyncPrefix_x3f_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_){
_start:
{
lean_object* v___y_1908_; 
if (lean_obj_tag(v_asyncPrefix_x3f_1903_) == 0)
{
lean_object* v___x_1921_; 
v___x_1921_ = l_Lean_MessageData_nil;
v___y_1908_ = v___x_1921_;
goto v___jp_1907_;
}
else
{
lean_object* v_val_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; 
v_val_1922_ = lean_ctor_get(v_asyncPrefix_x3f_1903_, 0);
lean_inc(v_val_1922_);
lean_dec_ref(v_asyncPrefix_x3f_1903_);
v___x_1923_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___redArg___closed__3, &l_Lean_throwAttrNotInAsyncCtx___redArg___closed__3_once, _init_l_Lean_throwAttrNotInAsyncCtx___redArg___closed__3);
v___x_1924_ = l_Lean_MessageData_ofName(v_val_1922_);
v___x_1925_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1925_, 0, v___x_1923_);
lean_ctor_set(v___x_1925_, 1, v___x_1924_);
v___x_1926_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__5, &l_Lean_throwAttrMustBeGlobal___redArg___closed__5_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__5);
v___x_1927_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1927_, 0, v___x_1925_);
lean_ctor_set(v___x_1927_, 1, v___x_1926_);
v___y_1908_ = v___x_1927_;
goto v___jp_1907_;
}
v___jp_1907_:
{
lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; uint8_t v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; 
v___x_1909_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1);
v___x_1910_ = l_Lean_MessageData_ofName(v_attrName_1901_);
v___x_1911_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1911_, 0, v___x_1909_);
lean_ctor_set(v___x_1911_, 1, v___x_1910_);
v___x_1912_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__3, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__3_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__3);
v___x_1913_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1913_, 0, v___x_1911_);
lean_ctor_set(v___x_1913_, 1, v___x_1912_);
v___x_1914_ = 0;
v___x_1915_ = l_Lean_MessageData_ofConstName(v_declName_1902_, v___x_1914_);
v___x_1916_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1916_, 0, v___x_1913_);
lean_ctor_set(v___x_1916_, 1, v___x_1915_);
v___x_1917_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___redArg___closed__1, &l_Lean_throwAttrNotInAsyncCtx___redArg___closed__1_once, _init_l_Lean_throwAttrNotInAsyncCtx___redArg___closed__1);
v___x_1918_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1918_, 0, v___x_1916_);
lean_ctor_set(v___x_1918_, 1, v___x_1917_);
v___x_1919_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1919_, 0, v___x_1918_);
lean_ctor_set(v___x_1919_, 1, v___y_1908_);
v___x_1920_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0_spec__0___redArg(v___x_1919_, v___y_1904_, v___y_1905_);
return v___x_1920_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___redArg___boxed(lean_object* v_attrName_1928_, lean_object* v_declName_1929_, lean_object* v_asyncPrefix_x3f_1930_, lean_object* v___y_1931_, lean_object* v___y_1932_, lean_object* v___y_1933_){
_start:
{
lean_object* v_res_1934_; 
v_res_1934_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___redArg(v_attrName_1928_, v_declName_1929_, v_asyncPrefix_x3f_1930_, v___y_1931_, v___y_1932_);
lean_dec(v___y_1932_);
lean_dec_ref(v___y_1931_);
return v_res_1934_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg(lean_object* v_name_1935_, uint8_t v_kind_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_){
_start:
{
lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; lean_object* v___y_1946_; 
v___x_1940_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__1, &l_Lean_throwAttrMustBeGlobal___redArg___closed__1_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__1);
v___x_1941_ = l_Lean_MessageData_ofName(v_name_1935_);
v___x_1942_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1942_, 0, v___x_1940_);
lean_ctor_set(v___x_1942_, 1, v___x_1941_);
v___x_1943_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__3, &l_Lean_throwAttrMustBeGlobal___redArg___closed__3_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__3);
v___x_1944_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1944_, 0, v___x_1942_);
lean_ctor_set(v___x_1944_, 1, v___x_1943_);
switch(v_kind_1936_)
{
case 0:
{
lean_object* v___x_1953_; 
v___x_1953_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__0));
v___y_1946_ = v___x_1953_;
goto v___jp_1945_;
}
case 1:
{
lean_object* v___x_1954_; 
v___x_1954_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__1));
v___y_1946_ = v___x_1954_;
goto v___jp_1945_;
}
default: 
{
lean_object* v___x_1955_; 
v___x_1955_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__2));
v___y_1946_ = v___x_1955_;
goto v___jp_1945_;
}
}
v___jp_1945_:
{
lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; 
lean_inc_ref(v___y_1946_);
v___x_1947_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1947_, 0, v___y_1946_);
v___x_1948_ = l_Lean_MessageData_ofFormat(v___x_1947_);
v___x_1949_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1949_, 0, v___x_1944_);
lean_ctor_set(v___x_1949_, 1, v___x_1948_);
v___x_1950_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__5, &l_Lean_throwAttrMustBeGlobal___redArg___closed__5_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__5);
v___x_1951_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1951_, 0, v___x_1949_);
lean_ctor_set(v___x_1951_, 1, v___x_1950_);
v___x_1952_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0_spec__0___redArg(v___x_1951_, v___y_1937_, v___y_1938_);
return v___x_1952_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg___boxed(lean_object* v_name_1956_, lean_object* v_kind_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_){
_start:
{
uint8_t v_kind_boxed_1961_; lean_object* v_res_1962_; 
v_kind_boxed_1961_ = lean_unbox(v_kind_1957_);
v_res_1962_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg(v_name_1956_, v_kind_boxed_1961_, v___y_1958_, v___y_1959_);
lean_dec(v___y_1959_);
lean_dec_ref(v___y_1958_);
return v_res_1962_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__7(lean_object* v_validate_1963_, lean_object* v_a_1964_, lean_object* v_name_1965_, lean_object* v_decl_1966_, lean_object* v_stx_1967_, uint8_t v_kind_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_){
_start:
{
lean_object* v___y_1973_; lean_object* v___y_1974_; lean_object* v___y_2008_; lean_object* v___y_2009_; lean_object* v___y_2010_; lean_object* v___y_2017_; lean_object* v___y_2018_; lean_object* v___x_2023_; 
v___x_2023_ = l_Lean_Attribute_Builtin_ensureNoArgs(v_stx_1967_, v___y_1969_, v___y_1970_);
if (lean_obj_tag(v___x_2023_) == 0)
{
uint8_t v___x_2024_; uint8_t v___x_2025_; 
lean_dec_ref(v___x_2023_);
v___x_2024_ = 0;
v___x_2025_ = l_Lean_instBEqAttributeKind_beq(v_kind_1968_, v___x_2024_);
if (v___x_2025_ == 0)
{
lean_object* v___x_2026_; 
lean_dec(v_decl_1966_);
lean_dec_ref(v_a_1964_);
lean_dec_ref(v_validate_1963_);
v___x_2026_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg(v_name_1965_, v_kind_1968_, v___y_1969_, v___y_1970_);
return v___x_2026_;
}
else
{
v___y_2017_ = v___y_1969_;
v___y_2018_ = v___y_1970_;
goto v___jp_2016_;
}
}
else
{
lean_dec(v_decl_1966_);
lean_dec(v_name_1965_);
lean_dec_ref(v_a_1964_);
lean_dec_ref(v_validate_1963_);
return v___x_2023_;
}
v___jp_1972_:
{
lean_object* v___x_1975_; 
lean_inc(v___y_1974_);
lean_inc_ref(v___y_1973_);
lean_inc(v_decl_1966_);
v___x_1975_ = lean_apply_4(v_validate_1963_, v_decl_1966_, v___y_1973_, v___y_1974_, lean_box(0));
if (lean_obj_tag(v___x_1975_) == 0)
{
lean_object* v___x_1977_; uint8_t v_isShared_1978_; uint8_t v_isSharedCheck_2005_; 
v_isSharedCheck_2005_ = !lean_is_exclusive(v___x_1975_);
if (v_isSharedCheck_2005_ == 0)
{
lean_object* v_unused_2006_; 
v_unused_2006_ = lean_ctor_get(v___x_1975_, 0);
lean_dec(v_unused_2006_);
v___x_1977_ = v___x_1975_;
v_isShared_1978_ = v_isSharedCheck_2005_;
goto v_resetjp_1976_;
}
else
{
lean_dec(v___x_1975_);
v___x_1977_ = lean_box(0);
v_isShared_1978_ = v_isSharedCheck_2005_;
goto v_resetjp_1976_;
}
v_resetjp_1976_:
{
lean_object* v___x_1979_; lean_object* v_toEnvExtension_1980_; lean_object* v_env_1981_; lean_object* v_nextMacroScope_1982_; lean_object* v_ngen_1983_; lean_object* v_auxDeclNGen_1984_; lean_object* v_traceState_1985_; lean_object* v_messages_1986_; lean_object* v_infoState_1987_; lean_object* v_snapshotTasks_1988_; lean_object* v___x_1990_; uint8_t v_isShared_1991_; uint8_t v_isSharedCheck_2003_; 
v___x_1979_ = lean_st_ref_take(v___y_1974_);
v_toEnvExtension_1980_ = lean_ctor_get(v_a_1964_, 0);
v_env_1981_ = lean_ctor_get(v___x_1979_, 0);
v_nextMacroScope_1982_ = lean_ctor_get(v___x_1979_, 1);
v_ngen_1983_ = lean_ctor_get(v___x_1979_, 2);
v_auxDeclNGen_1984_ = lean_ctor_get(v___x_1979_, 3);
v_traceState_1985_ = lean_ctor_get(v___x_1979_, 4);
v_messages_1986_ = lean_ctor_get(v___x_1979_, 6);
v_infoState_1987_ = lean_ctor_get(v___x_1979_, 7);
v_snapshotTasks_1988_ = lean_ctor_get(v___x_1979_, 8);
v_isSharedCheck_2003_ = !lean_is_exclusive(v___x_1979_);
if (v_isSharedCheck_2003_ == 0)
{
lean_object* v_unused_2004_; 
v_unused_2004_ = lean_ctor_get(v___x_1979_, 5);
lean_dec(v_unused_2004_);
v___x_1990_ = v___x_1979_;
v_isShared_1991_ = v_isSharedCheck_2003_;
goto v_resetjp_1989_;
}
else
{
lean_inc(v_snapshotTasks_1988_);
lean_inc(v_infoState_1987_);
lean_inc(v_messages_1986_);
lean_inc(v_traceState_1985_);
lean_inc(v_auxDeclNGen_1984_);
lean_inc(v_ngen_1983_);
lean_inc(v_nextMacroScope_1982_);
lean_inc(v_env_1981_);
lean_dec(v___x_1979_);
v___x_1990_ = lean_box(0);
v_isShared_1991_ = v_isSharedCheck_2003_;
goto v_resetjp_1989_;
}
v_resetjp_1989_:
{
lean_object* v_asyncMode_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; lean_object* v___x_1996_; 
v_asyncMode_1992_ = lean_ctor_get(v_toEnvExtension_1980_, 2);
lean_inc(v_asyncMode_1992_);
lean_inc(v_decl_1966_);
v___x_1993_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_a_1964_, v_env_1981_, v_decl_1966_, v_asyncMode_1992_, v_decl_1966_);
lean_dec(v_asyncMode_1992_);
v___x_1994_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2);
if (v_isShared_1991_ == 0)
{
lean_ctor_set(v___x_1990_, 5, v___x_1994_);
lean_ctor_set(v___x_1990_, 0, v___x_1993_);
v___x_1996_ = v___x_1990_;
goto v_reusejp_1995_;
}
else
{
lean_object* v_reuseFailAlloc_2002_; 
v_reuseFailAlloc_2002_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2002_, 0, v___x_1993_);
lean_ctor_set(v_reuseFailAlloc_2002_, 1, v_nextMacroScope_1982_);
lean_ctor_set(v_reuseFailAlloc_2002_, 2, v_ngen_1983_);
lean_ctor_set(v_reuseFailAlloc_2002_, 3, v_auxDeclNGen_1984_);
lean_ctor_set(v_reuseFailAlloc_2002_, 4, v_traceState_1985_);
lean_ctor_set(v_reuseFailAlloc_2002_, 5, v___x_1994_);
lean_ctor_set(v_reuseFailAlloc_2002_, 6, v_messages_1986_);
lean_ctor_set(v_reuseFailAlloc_2002_, 7, v_infoState_1987_);
lean_ctor_set(v_reuseFailAlloc_2002_, 8, v_snapshotTasks_1988_);
v___x_1996_ = v_reuseFailAlloc_2002_;
goto v_reusejp_1995_;
}
v_reusejp_1995_:
{
lean_object* v___x_1997_; lean_object* v___x_1998_; lean_object* v___x_2000_; 
v___x_1997_ = lean_st_ref_set(v___y_1974_, v___x_1996_);
v___x_1998_ = lean_box(0);
if (v_isShared_1978_ == 0)
{
lean_ctor_set(v___x_1977_, 0, v___x_1998_);
v___x_2000_ = v___x_1977_;
goto v_reusejp_1999_;
}
else
{
lean_object* v_reuseFailAlloc_2001_; 
v_reuseFailAlloc_2001_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2001_, 0, v___x_1998_);
v___x_2000_ = v_reuseFailAlloc_2001_;
goto v_reusejp_1999_;
}
v_reusejp_1999_:
{
return v___x_2000_;
}
}
}
}
}
else
{
lean_dec(v_decl_1966_);
lean_dec_ref(v_a_1964_);
return v___x_1975_;
}
}
v___jp_2007_:
{
lean_object* v_toEnvExtension_2011_; lean_object* v_asyncMode_2012_; uint8_t v___x_2013_; 
v_toEnvExtension_2011_ = lean_ctor_get(v_a_1964_, 0);
v_asyncMode_2012_ = lean_ctor_get(v_toEnvExtension_2011_, 2);
lean_inc(v_decl_1966_);
lean_inc_ref(v___y_2008_);
v___x_2013_ = l_Lean_EnvExtension_asyncMayModify___redArg(v___y_2008_, v_decl_1966_, v_asyncMode_2012_);
if (v___x_2013_ == 0)
{
lean_object* v___x_2014_; lean_object* v___x_2015_; 
lean_dec_ref(v_a_1964_);
lean_dec_ref(v_validate_1963_);
v___x_2014_ = l_Lean_Environment_asyncPrefix_x3f(v___y_2008_);
v___x_2015_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___redArg(v_name_1965_, v_decl_1966_, v___x_2014_, v___y_2009_, v___y_2010_);
return v___x_2015_;
}
else
{
lean_dec_ref(v___y_2008_);
lean_dec(v_name_1965_);
v___y_1973_ = v___y_2009_;
v___y_1974_ = v___y_2010_;
goto v___jp_1972_;
}
}
v___jp_2016_:
{
lean_object* v___x_2019_; lean_object* v_env_2020_; lean_object* v___x_2021_; 
v___x_2019_ = lean_st_ref_get(v___y_2018_);
v_env_2020_ = lean_ctor_get(v___x_2019_, 0);
lean_inc_ref(v_env_2020_);
lean_dec(v___x_2019_);
v___x_2021_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2020_, v_decl_1966_);
if (lean_obj_tag(v___x_2021_) == 0)
{
v___y_2008_ = v_env_2020_;
v___y_2009_ = v___y_2017_;
v___y_2010_ = v___y_2018_;
goto v___jp_2007_;
}
else
{
lean_object* v___x_2022_; 
lean_dec_ref(v___x_2021_);
lean_dec_ref(v_env_2020_);
lean_dec_ref(v_a_1964_);
lean_dec_ref(v_validate_1963_);
v___x_2022_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg(v_name_1965_, v_decl_1966_, v___y_2017_, v___y_2018_);
return v___x_2022_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__7___boxed(lean_object* v_validate_2027_, lean_object* v_a_2028_, lean_object* v_name_2029_, lean_object* v_decl_2030_, lean_object* v_stx_2031_, lean_object* v_kind_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_){
_start:
{
uint8_t v_kind_boxed_2036_; lean_object* v_res_2037_; 
v_kind_boxed_2036_ = lean_unbox(v_kind_2032_);
v_res_2037_ = l_Lean_registerTagAttribute___lam__7(v_validate_2027_, v_a_2028_, v_name_2029_, v_decl_2030_, v_stx_2031_, v_kind_boxed_2036_, v___y_2033_, v___y_2034_);
lean_dec(v___y_2034_);
lean_dec_ref(v___y_2033_);
return v_res_2037_;
}
}
static lean_object* _init_l_Lean_registerTagAttribute___closed__5(void){
_start:
{
lean_object* v___x_2043_; lean_object* v___f_2044_; 
v___x_2043_ = l_Lean_NameSet_empty;
v___f_2044_ = lean_alloc_closure((void*)(l_Lean_registerTagAttribute___lam__4___boxed), 4, 1);
lean_closure_set(v___f_2044_, 0, v___x_2043_);
return v___f_2044_;
}
}
static lean_object* _init_l_Lean_registerTagAttribute___closed__6(void){
_start:
{
lean_object* v___x_2045_; lean_object* v___f_2046_; 
v___x_2045_ = l_Lean_NameSet_empty;
v___f_2046_ = lean_alloc_closure((void*)(l_Lean_registerTagAttribute___lam__5___boxed), 2, 1);
lean_closure_set(v___f_2046_, 0, v___x_2045_);
return v___f_2046_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute(lean_object* v_name_2049_, lean_object* v_descr_2050_, lean_object* v_validate_2051_, lean_object* v_ref_2052_, uint8_t v_applicationTime_2053_, lean_object* v_asyncMode_2054_){
_start:
{
lean_object* v___f_2056_; lean_object* v___f_2057_; lean_object* v___f_2058_; lean_object* v___f_2059_; lean_object* v___f_2060_; lean_object* v___f_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; 
v___f_2056_ = ((lean_object*)(l_Lean_registerTagAttribute___closed__0));
v___f_2057_ = ((lean_object*)(l_Lean_registerTagAttribute___closed__2));
v___f_2058_ = ((lean_object*)(l_Lean_registerTagAttribute___closed__3));
v___f_2059_ = ((lean_object*)(l_Lean_registerTagAttribute___closed__4));
v___f_2060_ = lean_obj_once(&l_Lean_registerTagAttribute___closed__5, &l_Lean_registerTagAttribute___closed__5_once, _init_l_Lean_registerTagAttribute___closed__5);
v___f_2061_ = lean_obj_once(&l_Lean_registerTagAttribute___closed__6, &l_Lean_registerTagAttribute___closed__6_once, _init_l_Lean_registerTagAttribute___closed__6);
v___x_2062_ = ((lean_object*)(l_Lean_registerTagAttribute___closed__7));
lean_inc(v_ref_2052_);
v___x_2063_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_2063_, 0, v_ref_2052_);
lean_ctor_set(v___x_2063_, 1, v___f_2061_);
lean_ctor_set(v___x_2063_, 2, v___f_2060_);
lean_ctor_set(v___x_2063_, 3, v___f_2059_);
lean_ctor_set(v___x_2063_, 4, v___f_2058_);
lean_ctor_set(v___x_2063_, 5, v___f_2057_);
lean_ctor_set(v___x_2063_, 6, v_asyncMode_2054_);
lean_ctor_set(v___x_2063_, 7, v___x_2062_);
v___x_2064_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2064_, 0, v___x_2063_);
lean_ctor_set(v___x_2064_, 1, v___f_2056_);
v___x_2065_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_2064_);
if (lean_obj_tag(v___x_2065_) == 0)
{
lean_object* v_a_2066_; lean_object* v___f_2067_; lean_object* v___f_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; 
v_a_2066_ = lean_ctor_get(v___x_2065_, 0);
lean_inc_n(v_a_2066_, 2);
lean_dec_ref(v___x_2065_);
lean_inc_n(v_name_2049_, 2);
v___f_2067_ = lean_alloc_closure((void*)(l_Lean_registerTagAttribute___lam__6___boxed), 5, 1);
lean_closure_set(v___f_2067_, 0, v_name_2049_);
v___f_2068_ = lean_alloc_closure((void*)(l_Lean_registerTagAttribute___lam__7___boxed), 9, 3);
lean_closure_set(v___f_2068_, 0, v_validate_2051_);
lean_closure_set(v___f_2068_, 1, v_a_2066_);
lean_closure_set(v___f_2068_, 2, v_name_2049_);
v___x_2069_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2069_, 0, v_ref_2052_);
lean_ctor_set(v___x_2069_, 1, v_name_2049_);
lean_ctor_set(v___x_2069_, 2, v_descr_2050_);
lean_ctor_set_uint8(v___x_2069_, sizeof(void*)*3, v_applicationTime_2053_);
v___x_2070_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2070_, 0, v___x_2069_);
lean_ctor_set(v___x_2070_, 1, v___f_2068_);
lean_ctor_set(v___x_2070_, 2, v___f_2067_);
lean_inc_ref(v___x_2070_);
v___x_2071_ = l_Lean_registerBuiltinAttribute(v___x_2070_);
if (lean_obj_tag(v___x_2071_) == 0)
{
lean_object* v___x_2073_; uint8_t v_isShared_2074_; uint8_t v_isSharedCheck_2079_; 
v_isSharedCheck_2079_ = !lean_is_exclusive(v___x_2071_);
if (v_isSharedCheck_2079_ == 0)
{
lean_object* v_unused_2080_; 
v_unused_2080_ = lean_ctor_get(v___x_2071_, 0);
lean_dec(v_unused_2080_);
v___x_2073_ = v___x_2071_;
v_isShared_2074_ = v_isSharedCheck_2079_;
goto v_resetjp_2072_;
}
else
{
lean_dec(v___x_2071_);
v___x_2073_ = lean_box(0);
v_isShared_2074_ = v_isSharedCheck_2079_;
goto v_resetjp_2072_;
}
v_resetjp_2072_:
{
lean_object* v___x_2075_; lean_object* v___x_2077_; 
v___x_2075_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2075_, 0, v___x_2070_);
lean_ctor_set(v___x_2075_, 1, v_a_2066_);
if (v_isShared_2074_ == 0)
{
lean_ctor_set(v___x_2073_, 0, v___x_2075_);
v___x_2077_ = v___x_2073_;
goto v_reusejp_2076_;
}
else
{
lean_object* v_reuseFailAlloc_2078_; 
v_reuseFailAlloc_2078_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2078_, 0, v___x_2075_);
v___x_2077_ = v_reuseFailAlloc_2078_;
goto v_reusejp_2076_;
}
v_reusejp_2076_:
{
return v___x_2077_;
}
}
}
else
{
lean_object* v_a_2081_; lean_object* v___x_2083_; uint8_t v_isShared_2084_; uint8_t v_isSharedCheck_2088_; 
lean_dec_ref(v___x_2070_);
lean_dec(v_a_2066_);
v_a_2081_ = lean_ctor_get(v___x_2071_, 0);
v_isSharedCheck_2088_ = !lean_is_exclusive(v___x_2071_);
if (v_isSharedCheck_2088_ == 0)
{
v___x_2083_ = v___x_2071_;
v_isShared_2084_ = v_isSharedCheck_2088_;
goto v_resetjp_2082_;
}
else
{
lean_inc(v_a_2081_);
lean_dec(v___x_2071_);
v___x_2083_ = lean_box(0);
v_isShared_2084_ = v_isSharedCheck_2088_;
goto v_resetjp_2082_;
}
v_resetjp_2082_:
{
lean_object* v___x_2086_; 
if (v_isShared_2084_ == 0)
{
v___x_2086_ = v___x_2083_;
goto v_reusejp_2085_;
}
else
{
lean_object* v_reuseFailAlloc_2087_; 
v_reuseFailAlloc_2087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2087_, 0, v_a_2081_);
v___x_2086_ = v_reuseFailAlloc_2087_;
goto v_reusejp_2085_;
}
v_reusejp_2085_:
{
return v___x_2086_;
}
}
}
}
else
{
lean_object* v_a_2089_; lean_object* v___x_2091_; uint8_t v_isShared_2092_; uint8_t v_isSharedCheck_2096_; 
lean_dec(v_ref_2052_);
lean_dec_ref(v_validate_2051_);
lean_dec_ref(v_descr_2050_);
lean_dec(v_name_2049_);
v_a_2089_ = lean_ctor_get(v___x_2065_, 0);
v_isSharedCheck_2096_ = !lean_is_exclusive(v___x_2065_);
if (v_isSharedCheck_2096_ == 0)
{
v___x_2091_ = v___x_2065_;
v_isShared_2092_ = v_isSharedCheck_2096_;
goto v_resetjp_2090_;
}
else
{
lean_inc(v_a_2089_);
lean_dec(v___x_2065_);
v___x_2091_ = lean_box(0);
v_isShared_2092_ = v_isSharedCheck_2096_;
goto v_resetjp_2090_;
}
v_resetjp_2090_:
{
lean_object* v___x_2094_; 
if (v_isShared_2092_ == 0)
{
v___x_2094_ = v___x_2091_;
goto v_reusejp_2093_;
}
else
{
lean_object* v_reuseFailAlloc_2095_; 
v_reuseFailAlloc_2095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2095_, 0, v_a_2089_);
v___x_2094_ = v_reuseFailAlloc_2095_;
goto v_reusejp_2093_;
}
v_reusejp_2093_:
{
return v___x_2094_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___boxed(lean_object* v_name_2097_, lean_object* v_descr_2098_, lean_object* v_validate_2099_, lean_object* v_ref_2100_, lean_object* v_applicationTime_2101_, lean_object* v_asyncMode_2102_, lean_object* v_a_2103_){
_start:
{
uint8_t v_applicationTime_boxed_2104_; lean_object* v_res_2105_; 
v_applicationTime_boxed_2104_ = lean_unbox(v_applicationTime_2101_);
v_res_2105_ = l_Lean_registerTagAttribute(v_name_2097_, v_descr_2098_, v_validate_2099_, v_ref_2100_, v_applicationTime_boxed_2104_, v_asyncMode_2102_);
return v_res_2105_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerTagAttribute_spec__1(lean_object* v_init_2106_, lean_object* v_t_2107_){
_start:
{
lean_object* v___x_2108_; 
v___x_2108_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerTagAttribute_spec__1_spec__1(v_init_2106_, v_t_2107_);
return v___x_2108_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3(lean_object* v_n_2109_, lean_object* v_as_2110_, lean_object* v_lo_2111_, lean_object* v_hi_2112_, lean_object* v_w_2113_, lean_object* v_hlo_2114_, lean_object* v_hhi_2115_){
_start:
{
lean_object* v___x_2116_; 
v___x_2116_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___redArg(v_as_2110_, v_lo_2111_, v_hi_2112_);
return v___x_2116_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___boxed(lean_object* v_n_2117_, lean_object* v_as_2118_, lean_object* v_lo_2119_, lean_object* v_hi_2120_, lean_object* v_w_2121_, lean_object* v_hlo_2122_, lean_object* v_hhi_2123_){
_start:
{
lean_object* v_res_2124_; 
v_res_2124_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3(v_n_2117_, v_as_2118_, v_lo_2119_, v_hi_2120_, v_w_2121_, v_hlo_2122_, v_hhi_2123_);
lean_dec(v_hi_2120_);
lean_dec(v_n_2117_);
return v_res_2124_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4(lean_object* v_00_u03b1_2125_, lean_object* v_attrName_2126_, lean_object* v_declName_2127_, lean_object* v_asyncPrefix_x3f_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_){
_start:
{
lean_object* v___x_2132_; 
v___x_2132_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___redArg(v_attrName_2126_, v_declName_2127_, v_asyncPrefix_x3f_2128_, v___y_2129_, v___y_2130_);
return v___x_2132_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___boxed(lean_object* v_00_u03b1_2133_, lean_object* v_attrName_2134_, lean_object* v_declName_2135_, lean_object* v_asyncPrefix_x3f_2136_, lean_object* v___y_2137_, lean_object* v___y_2138_, lean_object* v___y_2139_){
_start:
{
lean_object* v_res_2140_; 
v_res_2140_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4(v_00_u03b1_2133_, v_attrName_2134_, v_declName_2135_, v_asyncPrefix_x3f_2136_, v___y_2137_, v___y_2138_);
lean_dec(v___y_2138_);
lean_dec_ref(v___y_2137_);
return v_res_2140_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5(lean_object* v_00_u03b1_2141_, lean_object* v_attrName_2142_, lean_object* v_declName_2143_, lean_object* v___y_2144_, lean_object* v___y_2145_){
_start:
{
lean_object* v___x_2147_; 
v___x_2147_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg(v_attrName_2142_, v_declName_2143_, v___y_2144_, v___y_2145_);
return v___x_2147_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___boxed(lean_object* v_00_u03b1_2148_, lean_object* v_attrName_2149_, lean_object* v_declName_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_, lean_object* v___y_2153_){
_start:
{
lean_object* v_res_2154_; 
v_res_2154_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5(v_00_u03b1_2148_, v_attrName_2149_, v_declName_2150_, v___y_2151_, v___y_2152_);
lean_dec(v___y_2152_);
lean_dec_ref(v___y_2151_);
return v_res_2154_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6(lean_object* v_00_u03b1_2155_, lean_object* v_name_2156_, uint8_t v_kind_2157_, lean_object* v___y_2158_, lean_object* v___y_2159_){
_start:
{
lean_object* v___x_2161_; 
v___x_2161_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg(v_name_2156_, v_kind_2157_, v___y_2158_, v___y_2159_);
return v___x_2161_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___boxed(lean_object* v_00_u03b1_2162_, lean_object* v_name_2163_, lean_object* v_kind_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_, lean_object* v___y_2167_){
_start:
{
uint8_t v_kind_boxed_2168_; lean_object* v_res_2169_; 
v_kind_boxed_2168_ = lean_unbox(v_kind_2164_);
v_res_2169_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6(v_00_u03b1_2162_, v_name_2163_, v_kind_boxed_2168_, v___y_2165_, v___y_2166_);
lean_dec(v___y_2166_);
lean_dec_ref(v___y_2165_);
return v_res_2169_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg___lam__0(lean_object* v_attr_2170_, lean_object* v_decl_2171_, lean_object* v_env_2172_){
_start:
{
lean_object* v_ext_2173_; lean_object* v_toEnvExtension_2174_; lean_object* v_asyncMode_2175_; lean_object* v___x_2176_; 
v_ext_2173_ = lean_ctor_get(v_attr_2170_, 1);
lean_inc_ref(v_ext_2173_);
lean_dec_ref(v_attr_2170_);
v_toEnvExtension_2174_ = lean_ctor_get(v_ext_2173_, 0);
v_asyncMode_2175_ = lean_ctor_get(v_toEnvExtension_2174_, 2);
lean_inc(v_asyncMode_2175_);
lean_inc(v_decl_2171_);
v___x_2176_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_ext_2173_, v_env_2172_, v_decl_2171_, v_asyncMode_2175_, v_decl_2171_);
lean_dec(v_asyncMode_2175_);
return v___x_2176_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg___lam__1(lean_object* v_modifyEnv_2177_, lean_object* v___f_2178_, lean_object* v_____r_2179_){
_start:
{
lean_object* v___x_2180_; 
v___x_2180_ = lean_apply_1(v_modifyEnv_2177_, v___f_2178_);
return v___x_2180_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg___lam__2(lean_object* v_attr_2181_, lean_object* v_env_2182_, lean_object* v_decl_2183_, lean_object* v_inst_2184_, lean_object* v_inst_2185_, lean_object* v_toBind_2186_, lean_object* v___f_2187_, lean_object* v_modifyEnv_2188_, lean_object* v___f_2189_, lean_object* v_____r_2190_){
_start:
{
lean_object* v_ext_2191_; lean_object* v_toEnvExtension_2192_; lean_object* v_attr_2193_; lean_object* v_asyncMode_2194_; uint8_t v___x_2195_; 
v_ext_2191_ = lean_ctor_get(v_attr_2181_, 1);
v_toEnvExtension_2192_ = lean_ctor_get(v_ext_2191_, 0);
lean_inc_ref(v_toEnvExtension_2192_);
v_attr_2193_ = lean_ctor_get(v_attr_2181_, 0);
lean_inc_ref(v_attr_2193_);
lean_dec_ref(v_attr_2181_);
v_asyncMode_2194_ = lean_ctor_get(v_toEnvExtension_2192_, 2);
lean_inc(v_asyncMode_2194_);
lean_dec_ref(v_toEnvExtension_2192_);
lean_inc(v_decl_2183_);
lean_inc_ref(v_env_2182_);
v___x_2195_ = l_Lean_EnvExtension_asyncMayModify___redArg(v_env_2182_, v_decl_2183_, v_asyncMode_2194_);
lean_dec(v_asyncMode_2194_);
if (v___x_2195_ == 0)
{
lean_object* v_toAttributeImplCore_2196_; lean_object* v_name_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; 
lean_dec_ref(v___f_2189_);
lean_dec(v_modifyEnv_2188_);
v_toAttributeImplCore_2196_ = lean_ctor_get(v_attr_2193_, 0);
lean_inc_ref(v_toAttributeImplCore_2196_);
lean_dec_ref(v_attr_2193_);
v_name_2197_ = lean_ctor_get(v_toAttributeImplCore_2196_, 1);
lean_inc(v_name_2197_);
lean_dec_ref(v_toAttributeImplCore_2196_);
v___x_2198_ = l_Lean_Environment_asyncPrefix_x3f(v_env_2182_);
v___x_2199_ = l_Lean_throwAttrNotInAsyncCtx___redArg(v_inst_2184_, v_inst_2185_, v_name_2197_, v_decl_2183_, v___x_2198_);
v___x_2200_ = lean_apply_4(v_toBind_2186_, lean_box(0), lean_box(0), v___x_2199_, v___f_2187_);
return v___x_2200_;
}
else
{
lean_object* v___x_2201_; 
lean_dec_ref(v_attr_2193_);
lean_dec(v___f_2187_);
lean_dec(v_toBind_2186_);
lean_dec_ref(v_inst_2185_);
lean_dec_ref(v_inst_2184_);
lean_dec(v_decl_2183_);
lean_dec_ref(v_env_2182_);
v___x_2201_ = lean_apply_1(v_modifyEnv_2188_, v___f_2189_);
return v___x_2201_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg___lam__3(lean_object* v___f_2202_, lean_object* v_____r_2203_){
_start:
{
lean_object* v___x_2204_; 
v___x_2204_ = lean_apply_1(v___f_2202_, v_____r_2203_);
return v___x_2204_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg___lam__4(lean_object* v_attr_2205_, lean_object* v_decl_2206_, lean_object* v_inst_2207_, lean_object* v_inst_2208_, lean_object* v_toBind_2209_, lean_object* v___f_2210_, lean_object* v_modifyEnv_2211_, lean_object* v___f_2212_, lean_object* v_env_2213_){
_start:
{
lean_object* v___f_2214_; lean_object* v___x_2215_; 
lean_inc_ref(v___f_2212_);
lean_inc(v_modifyEnv_2211_);
lean_inc(v___f_2210_);
lean_inc(v_toBind_2209_);
lean_inc_ref(v_inst_2208_);
lean_inc_ref(v_inst_2207_);
lean_inc(v_decl_2206_);
lean_inc_ref(v_env_2213_);
lean_inc_ref(v_attr_2205_);
v___f_2214_ = lean_alloc_closure((void*)(l_Lean_TagAttribute_setTag___redArg___lam__2), 10, 9);
lean_closure_set(v___f_2214_, 0, v_attr_2205_);
lean_closure_set(v___f_2214_, 1, v_env_2213_);
lean_closure_set(v___f_2214_, 2, v_decl_2206_);
lean_closure_set(v___f_2214_, 3, v_inst_2207_);
lean_closure_set(v___f_2214_, 4, v_inst_2208_);
lean_closure_set(v___f_2214_, 5, v_toBind_2209_);
lean_closure_set(v___f_2214_, 6, v___f_2210_);
lean_closure_set(v___f_2214_, 7, v_modifyEnv_2211_);
lean_closure_set(v___f_2214_, 8, v___f_2212_);
v___x_2215_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2213_, v_decl_2206_);
if (lean_obj_tag(v___x_2215_) == 0)
{
lean_object* v___x_2216_; lean_object* v___x_2217_; 
lean_dec_ref(v___f_2214_);
v___x_2216_ = lean_box(0);
v___x_2217_ = l_Lean_TagAttribute_setTag___redArg___lam__2(v_attr_2205_, v_env_2213_, v_decl_2206_, v_inst_2207_, v_inst_2208_, v_toBind_2209_, v___f_2210_, v_modifyEnv_2211_, v___f_2212_, v___x_2216_);
return v___x_2217_;
}
else
{
lean_object* v_attr_2218_; lean_object* v_toAttributeImplCore_2219_; lean_object* v_name_2220_; lean_object* v___f_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; 
lean_dec_ref(v___x_2215_);
lean_dec_ref(v_env_2213_);
lean_dec_ref(v___f_2212_);
lean_dec(v_modifyEnv_2211_);
lean_dec(v___f_2210_);
v_attr_2218_ = lean_ctor_get(v_attr_2205_, 0);
lean_inc_ref(v_attr_2218_);
lean_dec_ref(v_attr_2205_);
v_toAttributeImplCore_2219_ = lean_ctor_get(v_attr_2218_, 0);
lean_inc_ref(v_toAttributeImplCore_2219_);
lean_dec_ref(v_attr_2218_);
v_name_2220_ = lean_ctor_get(v_toAttributeImplCore_2219_, 1);
lean_inc(v_name_2220_);
lean_dec_ref(v_toAttributeImplCore_2219_);
v___f_2221_ = lean_alloc_closure((void*)(l_Lean_TagAttribute_setTag___redArg___lam__3), 2, 1);
lean_closure_set(v___f_2221_, 0, v___f_2214_);
v___x_2222_ = l_Lean_throwAttrDeclInImportedModule___redArg(v_inst_2207_, v_inst_2208_, v_name_2220_, v_decl_2206_);
v___x_2223_ = lean_apply_4(v_toBind_2209_, lean_box(0), lean_box(0), v___x_2222_, v___f_2221_);
return v___x_2223_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg(lean_object* v_inst_2224_, lean_object* v_inst_2225_, lean_object* v_inst_2226_, lean_object* v_attr_2227_, lean_object* v_decl_2228_){
_start:
{
lean_object* v_toBind_2229_; lean_object* v_getEnv_2230_; lean_object* v_modifyEnv_2231_; lean_object* v___f_2232_; lean_object* v___f_2233_; lean_object* v___f_2234_; lean_object* v___x_2235_; 
v_toBind_2229_ = lean_ctor_get(v_inst_2224_, 1);
lean_inc_n(v_toBind_2229_, 2);
v_getEnv_2230_ = lean_ctor_get(v_inst_2226_, 0);
lean_inc(v_getEnv_2230_);
v_modifyEnv_2231_ = lean_ctor_get(v_inst_2226_, 1);
lean_inc_n(v_modifyEnv_2231_, 2);
lean_dec_ref(v_inst_2226_);
lean_inc(v_decl_2228_);
lean_inc_ref(v_attr_2227_);
v___f_2232_ = lean_alloc_closure((void*)(l_Lean_TagAttribute_setTag___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2232_, 0, v_attr_2227_);
lean_closure_set(v___f_2232_, 1, v_decl_2228_);
lean_inc_ref(v___f_2232_);
v___f_2233_ = lean_alloc_closure((void*)(l_Lean_TagAttribute_setTag___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2233_, 0, v_modifyEnv_2231_);
lean_closure_set(v___f_2233_, 1, v___f_2232_);
v___f_2234_ = lean_alloc_closure((void*)(l_Lean_TagAttribute_setTag___redArg___lam__4), 9, 8);
lean_closure_set(v___f_2234_, 0, v_attr_2227_);
lean_closure_set(v___f_2234_, 1, v_decl_2228_);
lean_closure_set(v___f_2234_, 2, v_inst_2224_);
lean_closure_set(v___f_2234_, 3, v_inst_2225_);
lean_closure_set(v___f_2234_, 4, v_toBind_2229_);
lean_closure_set(v___f_2234_, 5, v___f_2233_);
lean_closure_set(v___f_2234_, 6, v_modifyEnv_2231_);
lean_closure_set(v___f_2234_, 7, v___f_2232_);
v___x_2235_ = lean_apply_4(v_toBind_2229_, lean_box(0), lean_box(0), v_getEnv_2230_, v___f_2234_);
return v___x_2235_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag(lean_object* v_m_2236_, lean_object* v_inst_2237_, lean_object* v_inst_2238_, lean_object* v_inst_2239_, lean_object* v_attr_2240_, lean_object* v_decl_2241_){
_start:
{
lean_object* v___x_2242_; 
v___x_2242_ = l_Lean_TagAttribute_setTag___redArg(v_inst_2237_, v_inst_2238_, v_inst_2239_, v_attr_2240_, v_decl_2241_);
return v___x_2242_;
}
}
LEAN_EXPORT uint8_t l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___redArg(lean_object* v_as_2243_, lean_object* v_k_2244_, lean_object* v_x_2245_, lean_object* v_x_2246_){
_start:
{
lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v_m_2249_; lean_object* v_a_2250_; uint8_t v___x_2251_; 
v___x_2247_ = lean_nat_add(v_x_2245_, v_x_2246_);
v___x_2248_ = lean_unsigned_to_nat(1u);
v_m_2249_ = lean_nat_shiftr(v___x_2247_, v___x_2248_);
lean_dec(v___x_2247_);
v_a_2250_ = lean_array_fget_borrowed(v_as_2243_, v_m_2249_);
v___x_2251_ = l_Lean_Name_quickLt(v_a_2250_, v_k_2244_);
if (v___x_2251_ == 0)
{
uint8_t v___x_2252_; 
lean_dec(v_x_2246_);
v___x_2252_ = l_Lean_Name_quickLt(v_k_2244_, v_a_2250_);
if (v___x_2252_ == 0)
{
uint8_t v___x_2253_; 
lean_dec(v_m_2249_);
lean_dec(v_x_2245_);
v___x_2253_ = 1;
return v___x_2253_;
}
else
{
lean_object* v___x_2254_; uint8_t v___x_2255_; 
v___x_2254_ = lean_unsigned_to_nat(0u);
v___x_2255_ = lean_nat_dec_eq(v_m_2249_, v___x_2254_);
if (v___x_2255_ == 0)
{
lean_object* v___x_2256_; uint8_t v___x_2257_; 
v___x_2256_ = lean_nat_sub(v_m_2249_, v___x_2248_);
lean_dec(v_m_2249_);
v___x_2257_ = lean_nat_dec_lt(v___x_2256_, v_x_2245_);
if (v___x_2257_ == 0)
{
v_x_2246_ = v___x_2256_;
goto _start;
}
else
{
lean_dec(v___x_2256_);
lean_dec(v_x_2245_);
return v___x_2251_;
}
}
else
{
lean_dec(v_m_2249_);
lean_dec(v_x_2245_);
return v___x_2251_;
}
}
}
else
{
lean_object* v___x_2259_; uint8_t v___x_2260_; 
lean_dec(v_x_2245_);
v___x_2259_ = lean_nat_add(v_m_2249_, v___x_2248_);
lean_dec(v_m_2249_);
v___x_2260_ = lean_nat_dec_le(v___x_2259_, v_x_2246_);
if (v___x_2260_ == 0)
{
lean_dec(v___x_2259_);
lean_dec(v_x_2246_);
return v___x_2260_;
}
else
{
v_x_2245_ = v___x_2259_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___redArg___boxed(lean_object* v_as_2262_, lean_object* v_k_2263_, lean_object* v_x_2264_, lean_object* v_x_2265_){
_start:
{
uint8_t v_res_2266_; lean_object* v_r_2267_; 
v_res_2266_ = l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___redArg(v_as_2262_, v_k_2263_, v_x_2264_, v_x_2265_);
lean_dec(v_k_2263_);
lean_dec_ref(v_as_2262_);
v_r_2267_ = lean_box(v_res_2266_);
return v_r_2267_;
}
}
LEAN_EXPORT uint8_t l_Lean_TagAttribute_hasTag(lean_object* v_attr_2268_, lean_object* v_env_2269_, lean_object* v_decl_2270_){
_start:
{
lean_object* v___x_2271_; lean_object* v___x_2272_; 
v___x_2271_ = lean_box(1);
v___x_2272_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2269_, v_decl_2270_);
if (lean_obj_tag(v___x_2272_) == 0)
{
lean_object* v_ext_2273_; lean_object* v_toEnvExtension_2274_; lean_object* v_asyncMode_2275_; lean_object* v___x_2276_; uint8_t v___x_2277_; 
v_ext_2273_ = lean_ctor_get(v_attr_2268_, 1);
v_toEnvExtension_2274_ = lean_ctor_get(v_ext_2273_, 0);
v_asyncMode_2275_ = lean_ctor_get(v_toEnvExtension_2274_, 2);
lean_inc(v_decl_2270_);
v___x_2276_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2271_, v_ext_2273_, v_env_2269_, v_asyncMode_2275_, v_decl_2270_);
v___x_2277_ = l_Lean_NameSet_contains(v___x_2276_, v_decl_2270_);
lean_dec(v_decl_2270_);
lean_dec(v___x_2276_);
return v___x_2277_;
}
else
{
lean_object* v_val_2278_; lean_object* v_ext_2279_; uint8_t v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; uint8_t v___x_2284_; 
v_val_2278_ = lean_ctor_get(v___x_2272_, 0);
lean_inc(v_val_2278_);
lean_dec_ref(v___x_2272_);
v_ext_2279_ = lean_ctor_get(v_attr_2268_, 1);
v___x_2280_ = 0;
v___x_2281_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_2271_, v_ext_2279_, v_env_2269_, v_val_2278_, v___x_2280_);
lean_dec(v_val_2278_);
lean_dec_ref(v_env_2269_);
v___x_2282_ = lean_unsigned_to_nat(0u);
v___x_2283_ = lean_array_get_size(v___x_2281_);
v___x_2284_ = lean_nat_dec_lt(v___x_2282_, v___x_2283_);
if (v___x_2284_ == 0)
{
lean_dec_ref(v___x_2281_);
lean_dec(v_decl_2270_);
return v___x_2284_;
}
else
{
lean_object* v___x_2285_; lean_object* v___x_2286_; uint8_t v___x_2287_; 
v___x_2285_ = lean_unsigned_to_nat(1u);
v___x_2286_ = lean_nat_sub(v___x_2283_, v___x_2285_);
v___x_2287_ = lean_nat_dec_le(v___x_2282_, v___x_2286_);
if (v___x_2287_ == 0)
{
lean_dec(v___x_2286_);
lean_dec_ref(v___x_2281_);
lean_dec(v_decl_2270_);
return v___x_2287_;
}
else
{
uint8_t v___x_2288_; 
v___x_2288_ = l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___redArg(v___x_2281_, v_decl_2270_, v___x_2282_, v___x_2286_);
lean_dec(v_decl_2270_);
lean_dec_ref(v___x_2281_);
return v___x_2288_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_hasTag___boxed(lean_object* v_attr_2289_, lean_object* v_env_2290_, lean_object* v_decl_2291_){
_start:
{
uint8_t v_res_2292_; lean_object* v_r_2293_; 
v_res_2292_ = l_Lean_TagAttribute_hasTag(v_attr_2289_, v_env_2290_, v_decl_2291_);
lean_dec_ref(v_attr_2289_);
v_r_2293_ = lean_box(v_res_2292_);
return v_r_2293_;
}
}
LEAN_EXPORT uint8_t l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0(lean_object* v_as_2294_, lean_object* v_k_2295_, lean_object* v_x_2296_, lean_object* v_x_2297_, lean_object* v_x_2298_){
_start:
{
uint8_t v___x_2299_; 
v___x_2299_ = l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___redArg(v_as_2294_, v_k_2295_, v_x_2296_, v_x_2297_);
return v___x_2299_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___boxed(lean_object* v_as_2300_, lean_object* v_k_2301_, lean_object* v_x_2302_, lean_object* v_x_2303_, lean_object* v_x_2304_){
_start:
{
uint8_t v_res_2305_; lean_object* v_r_2306_; 
v_res_2305_ = l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0(v_as_2300_, v_k_2301_, v_x_2302_, v_x_2303_, v_x_2304_);
lean_dec(v_k_2301_);
lean_dec_ref(v_as_2300_);
v_r_2306_ = lean_box(v_res_2305_);
return v_r_2306_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__0(lean_object* v_x_2307_, lean_object* v___y_2308_){
_start:
{
lean_object* v___x_2310_; lean_object* v___x_2311_; 
v___x_2310_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___lam__0___closed__1));
v___x_2311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2311_, 0, v___x_2310_);
return v___x_2311_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__0___boxed(lean_object* v_x_2312_, lean_object* v___y_2313_, lean_object* v___y_2314_){
_start:
{
lean_object* v_res_2315_; 
v_res_2315_ = l_Lean_instInhabitedParametricAttribute_default___lam__0(v_x_2312_, v___y_2313_);
lean_dec_ref(v___y_2313_);
lean_dec_ref(v_x_2312_);
return v_res_2315_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__1(lean_object* v_s_2316_, lean_object* v_x_2317_){
_start:
{
lean_inc_ref(v_s_2316_);
return v_s_2316_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__1___boxed(lean_object* v_s_2318_, lean_object* v_x_2319_){
_start:
{
lean_object* v_res_2320_; 
v_res_2320_ = l_Lean_instInhabitedParametricAttribute_default___lam__1(v_s_2318_, v_x_2319_);
lean_dec_ref(v_x_2319_);
lean_dec_ref(v_s_2318_);
return v_res_2320_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__2(lean_object* v_x_2325_, lean_object* v_x_2326_){
_start:
{
lean_object* v___x_2327_; 
v___x_2327_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___lam__2___closed__1));
return v___x_2327_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__2___boxed(lean_object* v_x_2328_, lean_object* v_x_2329_){
_start:
{
lean_object* v_res_2330_; 
v_res_2330_ = l_Lean_instInhabitedParametricAttribute_default___lam__2(v_x_2328_, v_x_2329_);
lean_dec_ref(v_x_2329_);
lean_dec_ref(v_x_2328_);
return v_res_2330_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__3(lean_object* v_x_2331_){
_start:
{
lean_object* v___x_2332_; 
v___x_2332_ = lean_box(0);
return v___x_2332_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__3___boxed(lean_object* v_x_2333_){
_start:
{
lean_object* v_res_2334_; 
v_res_2334_ = l_Lean_instInhabitedParametricAttribute_default___lam__3(v_x_2333_);
lean_dec_ref(v_x_2333_);
return v_res_2334_;
}
}
static lean_object* _init_l_Lean_instInhabitedParametricAttribute_default___closed__4(void){
_start:
{
lean_object* v___x_2339_; 
v___x_2339_ = l_Lean_instInhabitedEnvExtension_default(lean_box(0));
return v___x_2339_;
}
}
static lean_object* _init_l_Lean_instInhabitedParametricAttribute_default___closed__5(void){
_start:
{
lean_object* v___f_2340_; lean_object* v___f_2341_; lean_object* v___f_2342_; lean_object* v___f_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; 
v___f_2340_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___closed__3));
v___f_2341_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___closed__2));
v___f_2342_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___closed__1));
v___f_2343_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___closed__0));
v___x_2344_ = lean_box(0);
v___x_2345_ = lean_obj_once(&l_Lean_instInhabitedParametricAttribute_default___closed__4, &l_Lean_instInhabitedParametricAttribute_default___closed__4_once, _init_l_Lean_instInhabitedParametricAttribute_default___closed__4);
v___x_2346_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2346_, 0, v___x_2345_);
lean_ctor_set(v___x_2346_, 1, v___x_2344_);
lean_ctor_set(v___x_2346_, 2, v___f_2343_);
lean_ctor_set(v___x_2346_, 3, v___f_2342_);
lean_ctor_set(v___x_2346_, 4, v___f_2341_);
lean_ctor_set(v___x_2346_, 5, v___f_2340_);
return v___x_2346_;
}
}
static lean_object* _init_l_Lean_instInhabitedParametricAttribute_default___closed__6(void){
_start:
{
uint8_t v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; 
v___x_2347_ = 0;
v___x_2348_ = lean_obj_once(&l_Lean_instInhabitedParametricAttribute_default___closed__5, &l_Lean_instInhabitedParametricAttribute_default___closed__5_once, _init_l_Lean_instInhabitedParametricAttribute_default___closed__5);
v___x_2349_ = ((lean_object*)(l_Lean_instInhabitedAttributeImpl_default));
v___x_2350_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2350_, 0, v___x_2349_);
lean_ctor_set(v___x_2350_, 1, v___x_2348_);
lean_ctor_set_uint8(v___x_2350_, sizeof(void*)*2, v___x_2347_);
return v___x_2350_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default(lean_object* v_00_u03b1_2351_){
_start:
{
lean_object* v___x_2352_; 
v___x_2352_ = lean_obj_once(&l_Lean_instInhabitedParametricAttribute_default___closed__6, &l_Lean_instInhabitedParametricAttribute_default___closed__6_once, _init_l_Lean_instInhabitedParametricAttribute_default___closed__6);
return v___x_2352_;
}
}
static lean_object* _init_l_Lean_instInhabitedParametricAttribute___closed__0(void){
_start:
{
lean_object* v___x_2353_; 
v___x_2353_ = l_Lean_instInhabitedParametricAttribute_default(lean_box(0));
return v___x_2353_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute(lean_object* v_a_2354_){
_start:
{
lean_object* v___x_2355_; 
v___x_2355_ = lean_obj_once(&l_Lean_instInhabitedParametricAttribute___closed__0, &l_Lean_instInhabitedParametricAttribute___closed__0_once, _init_l_Lean_instInhabitedParametricAttribute___closed__0);
return v___x_2355_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_registerParametricAttribute_spec__4___redArg(lean_object* v_env_2356_, lean_object* v___y_2357_){
_start:
{
lean_object* v___x_2359_; lean_object* v_nextMacroScope_2360_; lean_object* v_ngen_2361_; lean_object* v_auxDeclNGen_2362_; lean_object* v_traceState_2363_; lean_object* v_messages_2364_; lean_object* v_infoState_2365_; lean_object* v_snapshotTasks_2366_; lean_object* v___x_2368_; uint8_t v_isShared_2369_; uint8_t v_isSharedCheck_2377_; 
v___x_2359_ = lean_st_ref_take(v___y_2357_);
v_nextMacroScope_2360_ = lean_ctor_get(v___x_2359_, 1);
v_ngen_2361_ = lean_ctor_get(v___x_2359_, 2);
v_auxDeclNGen_2362_ = lean_ctor_get(v___x_2359_, 3);
v_traceState_2363_ = lean_ctor_get(v___x_2359_, 4);
v_messages_2364_ = lean_ctor_get(v___x_2359_, 6);
v_infoState_2365_ = lean_ctor_get(v___x_2359_, 7);
v_snapshotTasks_2366_ = lean_ctor_get(v___x_2359_, 8);
v_isSharedCheck_2377_ = !lean_is_exclusive(v___x_2359_);
if (v_isSharedCheck_2377_ == 0)
{
lean_object* v_unused_2378_; lean_object* v_unused_2379_; 
v_unused_2378_ = lean_ctor_get(v___x_2359_, 5);
lean_dec(v_unused_2378_);
v_unused_2379_ = lean_ctor_get(v___x_2359_, 0);
lean_dec(v_unused_2379_);
v___x_2368_ = v___x_2359_;
v_isShared_2369_ = v_isSharedCheck_2377_;
goto v_resetjp_2367_;
}
else
{
lean_inc(v_snapshotTasks_2366_);
lean_inc(v_infoState_2365_);
lean_inc(v_messages_2364_);
lean_inc(v_traceState_2363_);
lean_inc(v_auxDeclNGen_2362_);
lean_inc(v_ngen_2361_);
lean_inc(v_nextMacroScope_2360_);
lean_dec(v___x_2359_);
v___x_2368_ = lean_box(0);
v_isShared_2369_ = v_isSharedCheck_2377_;
goto v_resetjp_2367_;
}
v_resetjp_2367_:
{
lean_object* v___x_2370_; lean_object* v___x_2372_; 
v___x_2370_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2);
if (v_isShared_2369_ == 0)
{
lean_ctor_set(v___x_2368_, 5, v___x_2370_);
lean_ctor_set(v___x_2368_, 0, v_env_2356_);
v___x_2372_ = v___x_2368_;
goto v_reusejp_2371_;
}
else
{
lean_object* v_reuseFailAlloc_2376_; 
v_reuseFailAlloc_2376_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2376_, 0, v_env_2356_);
lean_ctor_set(v_reuseFailAlloc_2376_, 1, v_nextMacroScope_2360_);
lean_ctor_set(v_reuseFailAlloc_2376_, 2, v_ngen_2361_);
lean_ctor_set(v_reuseFailAlloc_2376_, 3, v_auxDeclNGen_2362_);
lean_ctor_set(v_reuseFailAlloc_2376_, 4, v_traceState_2363_);
lean_ctor_set(v_reuseFailAlloc_2376_, 5, v___x_2370_);
lean_ctor_set(v_reuseFailAlloc_2376_, 6, v_messages_2364_);
lean_ctor_set(v_reuseFailAlloc_2376_, 7, v_infoState_2365_);
lean_ctor_set(v_reuseFailAlloc_2376_, 8, v_snapshotTasks_2366_);
v___x_2372_ = v_reuseFailAlloc_2376_;
goto v_reusejp_2371_;
}
v_reusejp_2371_:
{
lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; 
v___x_2373_ = lean_st_ref_set(v___y_2357_, v___x_2372_);
v___x_2374_ = lean_box(0);
v___x_2375_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2375_, 0, v___x_2374_);
return v___x_2375_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_registerParametricAttribute_spec__4___redArg___boxed(lean_object* v_env_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_){
_start:
{
lean_object* v_res_2383_; 
v_res_2383_ = l_Lean_setEnv___at___00Lean_registerParametricAttribute_spec__4___redArg(v_env_2380_, v___y_2381_);
lean_dec(v___y_2381_);
return v_res_2383_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_registerParametricAttribute_spec__4(lean_object* v_env_2384_, lean_object* v___y_2385_, lean_object* v___y_2386_){
_start:
{
lean_object* v___x_2388_; 
v___x_2388_ = l_Lean_setEnv___at___00Lean_registerParametricAttribute_spec__4___redArg(v_env_2384_, v___y_2386_);
return v___x_2388_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_registerParametricAttribute_spec__4___boxed(lean_object* v_env_2389_, lean_object* v___y_2390_, lean_object* v___y_2391_, lean_object* v___y_2392_){
_start:
{
lean_object* v_res_2393_; 
v_res_2393_ = l_Lean_setEnv___at___00Lean_registerParametricAttribute_spec__4(v_env_2389_, v___y_2390_, v___y_2391_);
lean_dec(v___y_2391_);
lean_dec_ref(v___y_2390_);
return v_res_2393_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___lam__0(lean_object* v_x_2394_, lean_object* v_p_2395_){
_start:
{
lean_object* v_fst_2396_; lean_object* v_snd_2397_; lean_object* v___x_2399_; uint8_t v_isShared_2400_; uint8_t v_isSharedCheck_2414_; 
v_fst_2396_ = lean_ctor_get(v_x_2394_, 0);
v_snd_2397_ = lean_ctor_get(v_x_2394_, 1);
v_isSharedCheck_2414_ = !lean_is_exclusive(v_x_2394_);
if (v_isSharedCheck_2414_ == 0)
{
v___x_2399_ = v_x_2394_;
v_isShared_2400_ = v_isSharedCheck_2414_;
goto v_resetjp_2398_;
}
else
{
lean_inc(v_snd_2397_);
lean_inc(v_fst_2396_);
lean_dec(v_x_2394_);
v___x_2399_ = lean_box(0);
v_isShared_2400_ = v_isSharedCheck_2414_;
goto v_resetjp_2398_;
}
v_resetjp_2398_:
{
lean_object* v_fst_2401_; lean_object* v_snd_2402_; lean_object* v___x_2404_; uint8_t v_isShared_2405_; uint8_t v_isSharedCheck_2413_; 
v_fst_2401_ = lean_ctor_get(v_p_2395_, 0);
v_snd_2402_ = lean_ctor_get(v_p_2395_, 1);
v_isSharedCheck_2413_ = !lean_is_exclusive(v_p_2395_);
if (v_isSharedCheck_2413_ == 0)
{
v___x_2404_ = v_p_2395_;
v_isShared_2405_ = v_isSharedCheck_2413_;
goto v_resetjp_2403_;
}
else
{
lean_inc(v_snd_2402_);
lean_inc(v_fst_2401_);
lean_dec(v_p_2395_);
v___x_2404_ = lean_box(0);
v_isShared_2405_ = v_isSharedCheck_2413_;
goto v_resetjp_2403_;
}
v_resetjp_2403_:
{
lean_object* v___x_2407_; 
lean_inc(v_fst_2401_);
if (v_isShared_2400_ == 0)
{
lean_ctor_set_tag(v___x_2399_, 1);
lean_ctor_set(v___x_2399_, 1, v_fst_2396_);
lean_ctor_set(v___x_2399_, 0, v_fst_2401_);
v___x_2407_ = v___x_2399_;
goto v_reusejp_2406_;
}
else
{
lean_object* v_reuseFailAlloc_2412_; 
v_reuseFailAlloc_2412_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2412_, 0, v_fst_2401_);
lean_ctor_set(v_reuseFailAlloc_2412_, 1, v_fst_2396_);
v___x_2407_ = v_reuseFailAlloc_2412_;
goto v_reusejp_2406_;
}
v_reusejp_2406_:
{
lean_object* v___x_2408_; lean_object* v___x_2410_; 
v___x_2408_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_2401_, v_snd_2402_, v_snd_2397_);
if (v_isShared_2405_ == 0)
{
lean_ctor_set(v___x_2404_, 1, v___x_2408_);
lean_ctor_set(v___x_2404_, 0, v___x_2407_);
v___x_2410_ = v___x_2404_;
goto v_reusejp_2409_;
}
else
{
lean_object* v_reuseFailAlloc_2411_; 
v_reuseFailAlloc_2411_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2411_, 0, v___x_2407_);
lean_ctor_set(v_reuseFailAlloc_2411_, 1, v___x_2408_);
v___x_2410_ = v_reuseFailAlloc_2411_;
goto v_reusejp_2409_;
}
v_reusejp_2409_:
{
return v___x_2410_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1_spec__1___redArg(lean_object* v_init_2415_, lean_object* v_x_2416_){
_start:
{
if (lean_obj_tag(v_x_2416_) == 0)
{
lean_object* v_k_2417_; lean_object* v_v_2418_; lean_object* v_l_2419_; lean_object* v_r_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; 
v_k_2417_ = lean_ctor_get(v_x_2416_, 1);
v_v_2418_ = lean_ctor_get(v_x_2416_, 2);
v_l_2419_ = lean_ctor_get(v_x_2416_, 3);
v_r_2420_ = lean_ctor_get(v_x_2416_, 4);
v___x_2421_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1_spec__1___redArg(v_init_2415_, v_l_2419_);
lean_inc(v_v_2418_);
lean_inc(v_k_2417_);
v___x_2422_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2422_, 0, v_k_2417_);
lean_ctor_set(v___x_2422_, 1, v_v_2418_);
v___x_2423_ = lean_array_push(v___x_2421_, v___x_2422_);
v_init_2415_ = v___x_2423_;
v_x_2416_ = v_r_2420_;
goto _start;
}
else
{
return v_init_2415_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1_spec__1___redArg___boxed(lean_object* v_init_2425_, lean_object* v_x_2426_){
_start:
{
lean_object* v_res_2427_; 
v_res_2427_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1_spec__1___redArg(v_init_2425_, v_x_2426_);
lean_dec(v_x_2426_);
return v_res_2427_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2___redArg___lam__0(lean_object* v_a_2428_, lean_object* v_b_2429_){
_start:
{
lean_object* v_fst_2430_; lean_object* v_fst_2431_; uint8_t v___x_2432_; 
v_fst_2430_ = lean_ctor_get(v_a_2428_, 0);
v_fst_2431_ = lean_ctor_get(v_b_2429_, 0);
v___x_2432_ = l_Lean_Name_quickLt(v_fst_2430_, v_fst_2431_);
return v___x_2432_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2___redArg___lam__0___boxed(lean_object* v_a_2433_, lean_object* v_b_2434_){
_start:
{
uint8_t v_res_2435_; lean_object* v_r_2436_; 
v_res_2435_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2___redArg___lam__0(v_a_2433_, v_b_2434_);
lean_dec_ref(v_b_2434_);
lean_dec_ref(v_a_2433_);
v_r_2436_ = lean_box(v_res_2435_);
return v_r_2436_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2___redArg(lean_object* v_as_2438_, lean_object* v_lo_2439_, lean_object* v_hi_2440_){
_start:
{
uint8_t v___x_2441_; 
v___x_2441_ = lean_nat_dec_lt(v_lo_2439_, v_hi_2440_);
if (v___x_2441_ == 0)
{
lean_dec(v_lo_2439_);
return v_as_2438_;
}
else
{
lean_object* v___f_2442_; lean_object* v___x_2443_; lean_object* v_fst_2444_; lean_object* v_snd_2445_; uint8_t v___x_2446_; 
v___f_2442_ = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2___redArg___closed__0));
lean_inc(v_lo_2439_);
v___x_2443_ = l_Array_qpartition___redArg(v_as_2438_, v___f_2442_, v_lo_2439_, v_hi_2440_);
v_fst_2444_ = lean_ctor_get(v___x_2443_, 0);
lean_inc(v_fst_2444_);
v_snd_2445_ = lean_ctor_get(v___x_2443_, 1);
lean_inc(v_snd_2445_);
lean_dec_ref(v___x_2443_);
v___x_2446_ = lean_nat_dec_le(v_hi_2440_, v_fst_2444_);
if (v___x_2446_ == 0)
{
lean_object* v___x_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; 
v___x_2447_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2___redArg(v_snd_2445_, v_lo_2439_, v_fst_2444_);
v___x_2448_ = lean_unsigned_to_nat(1u);
v___x_2449_ = lean_nat_add(v_fst_2444_, v___x_2448_);
lean_dec(v_fst_2444_);
v_as_2438_ = v___x_2447_;
v_lo_2439_ = v___x_2449_;
goto _start;
}
else
{
lean_dec(v_fst_2444_);
lean_dec(v_lo_2439_);
return v_snd_2445_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2___redArg___boxed(lean_object* v_as_2451_, lean_object* v_lo_2452_, lean_object* v_hi_2453_){
_start:
{
lean_object* v_res_2454_; 
v_res_2454_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2___redArg(v_as_2451_, v_lo_2452_, v_hi_2453_);
lean_dec(v_hi_2453_);
return v_res_2454_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3_spec__4___redArg(lean_object* v_snd_2455_, lean_object* v_as_2456_, size_t v_i_2457_, size_t v_stop_2458_, lean_object* v_b_2459_){
_start:
{
lean_object* v___y_2461_; uint8_t v___x_2465_; 
v___x_2465_ = lean_usize_dec_eq(v_i_2457_, v_stop_2458_);
if (v___x_2465_ == 0)
{
lean_object* v___x_2466_; lean_object* v___x_2467_; 
v___x_2466_ = lean_array_uget_borrowed(v_as_2456_, v_i_2457_);
v___x_2467_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_snd_2455_, v___x_2466_);
if (lean_obj_tag(v___x_2467_) == 0)
{
v___y_2461_ = v_b_2459_;
goto v___jp_2460_;
}
else
{
lean_object* v_val_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; 
v_val_2468_ = lean_ctor_get(v___x_2467_, 0);
lean_inc(v_val_2468_);
lean_dec_ref(v___x_2467_);
lean_inc(v___x_2466_);
v___x_2469_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2469_, 0, v___x_2466_);
lean_ctor_set(v___x_2469_, 1, v_val_2468_);
v___x_2470_ = lean_array_push(v_b_2459_, v___x_2469_);
v___y_2461_ = v___x_2470_;
goto v___jp_2460_;
}
}
else
{
return v_b_2459_;
}
v___jp_2460_:
{
size_t v___x_2462_; size_t v___x_2463_; 
v___x_2462_ = ((size_t)1ULL);
v___x_2463_ = lean_usize_add(v_i_2457_, v___x_2462_);
v_i_2457_ = v___x_2463_;
v_b_2459_ = v___y_2461_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3_spec__4___redArg___boxed(lean_object* v_snd_2471_, lean_object* v_as_2472_, lean_object* v_i_2473_, lean_object* v_stop_2474_, lean_object* v_b_2475_){
_start:
{
size_t v_i_boxed_2476_; size_t v_stop_boxed_2477_; lean_object* v_res_2478_; 
v_i_boxed_2476_ = lean_unbox_usize(v_i_2473_);
lean_dec(v_i_2473_);
v_stop_boxed_2477_ = lean_unbox_usize(v_stop_2474_);
lean_dec(v_stop_2474_);
v_res_2478_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3_spec__4___redArg(v_snd_2471_, v_as_2472_, v_i_boxed_2476_, v_stop_boxed_2477_, v_b_2475_);
lean_dec_ref(v_as_2472_);
lean_dec(v_snd_2471_);
return v_res_2478_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3___redArg(lean_object* v_snd_2479_, lean_object* v_as_2480_, lean_object* v_start_2481_, lean_object* v_stop_2482_){
_start:
{
lean_object* v___x_2483_; uint8_t v___x_2484_; 
v___x_2483_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___lam__2___closed__0));
v___x_2484_ = lean_nat_dec_lt(v_start_2481_, v_stop_2482_);
if (v___x_2484_ == 0)
{
return v___x_2483_;
}
else
{
lean_object* v___x_2485_; uint8_t v___x_2486_; 
v___x_2485_ = lean_array_get_size(v_as_2480_);
v___x_2486_ = lean_nat_dec_le(v_stop_2482_, v___x_2485_);
if (v___x_2486_ == 0)
{
uint8_t v___x_2487_; 
v___x_2487_ = lean_nat_dec_lt(v_start_2481_, v___x_2485_);
if (v___x_2487_ == 0)
{
return v___x_2483_;
}
else
{
size_t v___x_2488_; size_t v___x_2489_; lean_object* v___x_2490_; 
v___x_2488_ = lean_usize_of_nat(v_start_2481_);
v___x_2489_ = lean_usize_of_nat(v___x_2485_);
v___x_2490_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3_spec__4___redArg(v_snd_2479_, v_as_2480_, v___x_2488_, v___x_2489_, v___x_2483_);
return v___x_2490_;
}
}
else
{
size_t v___x_2491_; size_t v___x_2492_; lean_object* v___x_2493_; 
v___x_2491_ = lean_usize_of_nat(v_start_2481_);
v___x_2492_ = lean_usize_of_nat(v_stop_2482_);
v___x_2493_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3_spec__4___redArg(v_snd_2479_, v_as_2480_, v___x_2491_, v___x_2492_, v___x_2483_);
return v___x_2493_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3___redArg___boxed(lean_object* v_snd_2494_, lean_object* v_as_2495_, lean_object* v_start_2496_, lean_object* v_stop_2497_){
_start:
{
lean_object* v_res_2498_; 
v_res_2498_ = l_Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3___redArg(v_snd_2494_, v_as_2495_, v_start_2496_, v_stop_2497_);
lean_dec(v_stop_2497_);
lean_dec(v_start_2496_);
lean_dec_ref(v_as_2495_);
lean_dec(v_snd_2494_);
return v_res_2498_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttribute_spec__0___redArg(lean_object* v_impl_2499_, lean_object* v_env_2500_, lean_object* v_as_2501_, size_t v_i_2502_, size_t v_stop_2503_, lean_object* v_b_2504_){
_start:
{
lean_object* v___y_2506_; uint8_t v___x_2510_; 
v___x_2510_ = lean_usize_dec_eq(v_i_2502_, v_stop_2503_);
if (v___x_2510_ == 0)
{
lean_object* v___x_2511_; lean_object* v_fst_2512_; lean_object* v_snd_2513_; lean_object* v_filterExport_2514_; lean_object* v___x_2515_; uint8_t v___x_2516_; 
v___x_2511_ = lean_array_uget_borrowed(v_as_2501_, v_i_2502_);
v_fst_2512_ = lean_ctor_get(v___x_2511_, 0);
v_snd_2513_ = lean_ctor_get(v___x_2511_, 1);
v_filterExport_2514_ = lean_ctor_get(v_impl_2499_, 3);
lean_inc_ref(v_filterExport_2514_);
lean_inc(v_snd_2513_);
lean_inc(v_fst_2512_);
lean_inc_ref(v_env_2500_);
v___x_2515_ = lean_apply_3(v_filterExport_2514_, v_env_2500_, v_fst_2512_, v_snd_2513_);
v___x_2516_ = lean_unbox(v___x_2515_);
if (v___x_2516_ == 0)
{
v___y_2506_ = v_b_2504_;
goto v___jp_2505_;
}
else
{
lean_object* v___x_2517_; 
lean_inc(v___x_2511_);
v___x_2517_ = lean_array_push(v_b_2504_, v___x_2511_);
v___y_2506_ = v___x_2517_;
goto v___jp_2505_;
}
}
else
{
lean_dec_ref(v_env_2500_);
lean_dec_ref(v_impl_2499_);
return v_b_2504_;
}
v___jp_2505_:
{
size_t v___x_2507_; size_t v___x_2508_; 
v___x_2507_ = ((size_t)1ULL);
v___x_2508_ = lean_usize_add(v_i_2502_, v___x_2507_);
v_i_2502_ = v___x_2508_;
v_b_2504_ = v___y_2506_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttribute_spec__0___redArg___boxed(lean_object* v_impl_2518_, lean_object* v_env_2519_, lean_object* v_as_2520_, lean_object* v_i_2521_, lean_object* v_stop_2522_, lean_object* v_b_2523_){
_start:
{
size_t v_i_boxed_2524_; size_t v_stop_boxed_2525_; lean_object* v_res_2526_; 
v_i_boxed_2524_ = lean_unbox_usize(v_i_2521_);
lean_dec(v_i_2521_);
v_stop_boxed_2525_ = lean_unbox_usize(v_stop_2522_);
lean_dec(v_stop_2522_);
v_res_2526_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttribute_spec__0___redArg(v_impl_2518_, v_env_2519_, v_as_2520_, v_i_boxed_2524_, v_stop_boxed_2525_, v_b_2523_);
lean_dec_ref(v_as_2520_);
return v_res_2526_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___lam__1(lean_object* v_impl_2527_, uint8_t v_preserveOrder_2528_, lean_object* v_env_2529_, lean_object* v_x_2530_){
_start:
{
lean_object* v___y_2532_; 
if (v_preserveOrder_2528_ == 0)
{
lean_object* v_snd_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v_r_2551_; lean_object* v___y_2553_; lean_object* v___y_2554_; lean_object* v___x_2556_; uint8_t v___x_2557_; 
v_snd_2548_ = lean_ctor_get(v_x_2530_, 1);
lean_inc(v_snd_2548_);
lean_dec_ref(v_x_2530_);
v___x_2549_ = lean_unsigned_to_nat(0u);
v___x_2550_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___lam__2___closed__0));
v_r_2551_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1_spec__1___redArg(v___x_2550_, v_snd_2548_);
lean_dec(v_snd_2548_);
v___x_2556_ = lean_array_get_size(v_r_2551_);
v___x_2557_ = lean_nat_dec_eq(v___x_2556_, v___x_2549_);
if (v___x_2557_ == 0)
{
lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___y_2561_; uint8_t v___x_2563_; 
v___x_2558_ = lean_unsigned_to_nat(1u);
v___x_2559_ = lean_nat_sub(v___x_2556_, v___x_2558_);
v___x_2563_ = lean_nat_dec_le(v___x_2549_, v___x_2559_);
if (v___x_2563_ == 0)
{
lean_inc(v___x_2559_);
v___y_2561_ = v___x_2559_;
goto v___jp_2560_;
}
else
{
v___y_2561_ = v___x_2549_;
goto v___jp_2560_;
}
v___jp_2560_:
{
uint8_t v___x_2562_; 
v___x_2562_ = lean_nat_dec_le(v___y_2561_, v___x_2559_);
if (v___x_2562_ == 0)
{
lean_dec(v___x_2559_);
lean_inc(v___y_2561_);
v___y_2553_ = v___y_2561_;
v___y_2554_ = v___y_2561_;
goto v___jp_2552_;
}
else
{
v___y_2553_ = v___y_2561_;
v___y_2554_ = v___x_2559_;
goto v___jp_2552_;
}
}
}
else
{
v___y_2532_ = v_r_2551_;
goto v___jp_2531_;
}
v___jp_2552_:
{
lean_object* v___x_2555_; 
v___x_2555_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2___redArg(v_r_2551_, v___y_2553_, v___y_2554_);
lean_dec(v___y_2554_);
v___y_2532_ = v___x_2555_;
goto v___jp_2531_;
}
}
else
{
lean_object* v_fst_2564_; lean_object* v_snd_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; 
v_fst_2564_ = lean_ctor_get(v_x_2530_, 0);
lean_inc(v_fst_2564_);
v_snd_2565_ = lean_ctor_get(v_x_2530_, 1);
lean_inc(v_snd_2565_);
lean_dec_ref(v_x_2530_);
v___x_2566_ = lean_array_mk(v_fst_2564_);
v___x_2567_ = l_Array_reverse___redArg(v___x_2566_);
v___x_2568_ = lean_unsigned_to_nat(0u);
v___x_2569_ = lean_array_get_size(v___x_2567_);
v___x_2570_ = l_Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3___redArg(v_snd_2565_, v___x_2567_, v___x_2568_, v___x_2569_);
lean_dec_ref(v___x_2567_);
lean_dec(v_snd_2565_);
v___y_2532_ = v___x_2570_;
goto v___jp_2531_;
}
v___jp_2531_:
{
lean_object* v___x_2533_; lean_object* v___x_2534_; lean_object* v___x_2535_; uint8_t v___x_2536_; 
v___x_2533_ = lean_unsigned_to_nat(0u);
v___x_2534_ = lean_array_get_size(v___y_2532_);
v___x_2535_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___lam__2___closed__0));
v___x_2536_ = lean_nat_dec_lt(v___x_2533_, v___x_2534_);
if (v___x_2536_ == 0)
{
lean_object* v___x_2537_; 
lean_dec_ref(v_env_2529_);
lean_dec_ref(v_impl_2527_);
v___x_2537_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2537_, 0, v___x_2535_);
lean_ctor_set(v___x_2537_, 1, v___x_2535_);
lean_ctor_set(v___x_2537_, 2, v___y_2532_);
return v___x_2537_;
}
else
{
uint8_t v___x_2538_; 
v___x_2538_ = lean_nat_dec_le(v___x_2534_, v___x_2534_);
if (v___x_2538_ == 0)
{
if (v___x_2536_ == 0)
{
lean_object* v___x_2539_; 
lean_dec_ref(v_env_2529_);
lean_dec_ref(v_impl_2527_);
v___x_2539_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2539_, 0, v___x_2535_);
lean_ctor_set(v___x_2539_, 1, v___x_2535_);
lean_ctor_set(v___x_2539_, 2, v___y_2532_);
return v___x_2539_;
}
else
{
size_t v___x_2540_; size_t v___x_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; 
v___x_2540_ = ((size_t)0ULL);
v___x_2541_ = lean_usize_of_nat(v___x_2534_);
v___x_2542_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttribute_spec__0___redArg(v_impl_2527_, v_env_2529_, v___y_2532_, v___x_2540_, v___x_2541_, v___x_2535_);
lean_inc_ref(v___x_2542_);
v___x_2543_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2543_, 0, v___x_2542_);
lean_ctor_set(v___x_2543_, 1, v___x_2542_);
lean_ctor_set(v___x_2543_, 2, v___y_2532_);
return v___x_2543_;
}
}
else
{
size_t v___x_2544_; size_t v___x_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; 
v___x_2544_ = ((size_t)0ULL);
v___x_2545_ = lean_usize_of_nat(v___x_2534_);
v___x_2546_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttribute_spec__0___redArg(v_impl_2527_, v_env_2529_, v___y_2532_, v___x_2544_, v___x_2545_, v___x_2535_);
lean_inc_ref(v___x_2546_);
v___x_2547_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2547_, 0, v___x_2546_);
lean_ctor_set(v___x_2547_, 1, v___x_2546_);
lean_ctor_set(v___x_2547_, 2, v___y_2532_);
return v___x_2547_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___lam__1___boxed(lean_object* v_impl_2571_, lean_object* v_preserveOrder_2572_, lean_object* v_env_2573_, lean_object* v_x_2574_){
_start:
{
uint8_t v_preserveOrder_boxed_2575_; lean_object* v_res_2576_; 
v_preserveOrder_boxed_2575_ = lean_unbox(v_preserveOrder_2572_);
v_res_2576_ = l_Lean_registerParametricAttribute___redArg___lam__1(v_impl_2571_, v_preserveOrder_boxed_2575_, v_env_2573_, v_x_2574_);
return v_res_2576_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___lam__2(lean_object* v_x_2586_){
_start:
{
lean_object* v_snd_2587_; lean_object* v___x_2589_; uint8_t v_isShared_2590_; uint8_t v_isSharedCheck_2601_; 
v_snd_2587_ = lean_ctor_get(v_x_2586_, 1);
v_isSharedCheck_2601_ = !lean_is_exclusive(v_x_2586_);
if (v_isSharedCheck_2601_ == 0)
{
lean_object* v_unused_2602_; 
v_unused_2602_ = lean_ctor_get(v_x_2586_, 0);
lean_dec(v_unused_2602_);
v___x_2589_ = v_x_2586_;
v_isShared_2590_ = v_isSharedCheck_2601_;
goto v_resetjp_2588_;
}
else
{
lean_inc(v_snd_2587_);
lean_dec(v_x_2586_);
v___x_2589_ = lean_box(0);
v_isShared_2590_ = v_isSharedCheck_2601_;
goto v_resetjp_2588_;
}
v_resetjp_2588_:
{
lean_object* v___x_2591_; lean_object* v___y_2593_; 
v___x_2591_ = ((lean_object*)(l_Lean_registerParametricAttribute___redArg___lam__2___closed__3));
if (lean_obj_tag(v_snd_2587_) == 0)
{
lean_object* v_size_2599_; 
v_size_2599_ = lean_ctor_get(v_snd_2587_, 0);
lean_inc(v_size_2599_);
lean_dec_ref(v_snd_2587_);
v___y_2593_ = v_size_2599_;
goto v___jp_2592_;
}
else
{
lean_object* v___x_2600_; 
v___x_2600_ = lean_unsigned_to_nat(0u);
v___y_2593_ = v___x_2600_;
goto v___jp_2592_;
}
v___jp_2592_:
{
lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2597_; 
v___x_2594_ = l_Nat_reprFast(v___y_2593_);
v___x_2595_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2595_, 0, v___x_2594_);
if (v_isShared_2590_ == 0)
{
lean_ctor_set_tag(v___x_2589_, 5);
lean_ctor_set(v___x_2589_, 1, v___x_2595_);
lean_ctor_set(v___x_2589_, 0, v___x_2591_);
v___x_2597_ = v___x_2589_;
goto v_reusejp_2596_;
}
else
{
lean_object* v_reuseFailAlloc_2598_; 
v_reuseFailAlloc_2598_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2598_, 0, v___x_2591_);
lean_ctor_set(v_reuseFailAlloc_2598_, 1, v___x_2595_);
v___x_2597_ = v_reuseFailAlloc_2598_;
goto v_reusejp_2596_;
}
v_reusejp_2596_:
{
return v___x_2597_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___lam__3(lean_object* v_x_2603_){
_start:
{
lean_object* v___x_2604_; 
v___x_2604_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___lam__2___closed__0));
return v___x_2604_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___lam__3___boxed(lean_object* v_x_2605_){
_start:
{
lean_object* v_res_2606_; 
v_res_2606_ = l_Lean_registerParametricAttribute___redArg___lam__3(v_x_2605_);
lean_dec_ref(v_x_2605_);
return v_res_2606_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___lam__4(lean_object* v___x_2607_, lean_object* v_x_2608_, lean_object* v___y_2609_){
_start:
{
lean_object* v___x_2611_; 
v___x_2611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2611_, 0, v___x_2607_);
return v___x_2611_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___lam__4___boxed(lean_object* v___x_2612_, lean_object* v_x_2613_, lean_object* v___y_2614_, lean_object* v___y_2615_){
_start:
{
lean_object* v_res_2616_; 
v_res_2616_ = l_Lean_registerParametricAttribute___redArg___lam__4(v___x_2612_, v_x_2613_, v___y_2614_);
lean_dec_ref(v___y_2614_);
lean_dec_ref(v_x_2613_);
return v_res_2616_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___lam__5(lean_object* v___x_2617_){
_start:
{
lean_object* v___x_2619_; 
v___x_2619_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2619_, 0, v___x_2617_);
return v___x_2619_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___lam__5___boxed(lean_object* v___x_2620_, lean_object* v___y_2621_){
_start:
{
lean_object* v_res_2622_; 
v_res_2622_ = l_Lean_registerParametricAttribute___redArg___lam__5(v___x_2620_);
return v_res_2622_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___lam__7(lean_object* v_getParam_2623_, lean_object* v_a_2624_, lean_object* v_afterSet_2625_, lean_object* v_name_2626_, lean_object* v_decl_2627_, lean_object* v_stx_2628_, uint8_t v_kind_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_){
_start:
{
lean_object* v___y_2634_; lean_object* v___y_2635_; lean_object* v___y_2636_; lean_object* v___y_2637_; uint8_t v___y_2638_; lean_object* v___y_2641_; lean_object* v___y_2642_; lean_object* v___y_2643_; uint8_t v___x_2686_; uint8_t v___x_2687_; 
v___x_2686_ = 0;
v___x_2687_ = l_Lean_instBEqAttributeKind_beq(v_kind_2629_, v___x_2686_);
if (v___x_2687_ == 0)
{
lean_object* v___x_2688_; 
lean_dec(v_stx_2628_);
lean_dec(v_decl_2627_);
lean_dec_ref(v_afterSet_2625_);
lean_dec_ref(v_a_2624_);
lean_dec_ref(v_getParam_2623_);
v___x_2688_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg(v_name_2626_, v_kind_2629_, v___y_2630_, v___y_2631_);
return v___x_2688_;
}
else
{
goto v___jp_2681_;
}
v___jp_2633_:
{
if (v___y_2638_ == 0)
{
lean_object* v___x_2639_; 
lean_dec_ref(v___y_2635_);
v___x_2639_ = l_Lean_setEnv___at___00Lean_registerParametricAttribute_spec__4___redArg(v___y_2634_, v___y_2637_);
return v___x_2639_;
}
else
{
lean_dec_ref(v___y_2634_);
return v___y_2635_;
}
}
v___jp_2640_:
{
lean_object* v___x_2644_; 
lean_inc(v___y_2643_);
lean_inc_ref(v___y_2642_);
lean_inc(v_decl_2627_);
v___x_2644_ = lean_apply_5(v_getParam_2623_, v_decl_2627_, v_stx_2628_, v___y_2642_, v___y_2643_, lean_box(0));
if (lean_obj_tag(v___x_2644_) == 0)
{
lean_object* v_a_2645_; lean_object* v___x_2646_; lean_object* v_toEnvExtension_2647_; lean_object* v_env_2648_; lean_object* v_nextMacroScope_2649_; lean_object* v_ngen_2650_; lean_object* v_auxDeclNGen_2651_; lean_object* v_traceState_2652_; lean_object* v_messages_2653_; lean_object* v_infoState_2654_; lean_object* v_snapshotTasks_2655_; lean_object* v___x_2657_; uint8_t v_isShared_2658_; uint8_t v_isSharedCheck_2671_; 
v_a_2645_ = lean_ctor_get(v___x_2644_, 0);
lean_inc(v_a_2645_);
lean_dec_ref(v___x_2644_);
v___x_2646_ = lean_st_ref_take(v___y_2643_);
v_toEnvExtension_2647_ = lean_ctor_get(v_a_2624_, 0);
v_env_2648_ = lean_ctor_get(v___x_2646_, 0);
v_nextMacroScope_2649_ = lean_ctor_get(v___x_2646_, 1);
v_ngen_2650_ = lean_ctor_get(v___x_2646_, 2);
v_auxDeclNGen_2651_ = lean_ctor_get(v___x_2646_, 3);
v_traceState_2652_ = lean_ctor_get(v___x_2646_, 4);
v_messages_2653_ = lean_ctor_get(v___x_2646_, 6);
v_infoState_2654_ = lean_ctor_get(v___x_2646_, 7);
v_snapshotTasks_2655_ = lean_ctor_get(v___x_2646_, 8);
v_isSharedCheck_2671_ = !lean_is_exclusive(v___x_2646_);
if (v_isSharedCheck_2671_ == 0)
{
lean_object* v_unused_2672_; 
v_unused_2672_ = lean_ctor_get(v___x_2646_, 5);
lean_dec(v_unused_2672_);
v___x_2657_ = v___x_2646_;
v_isShared_2658_ = v_isSharedCheck_2671_;
goto v_resetjp_2656_;
}
else
{
lean_inc(v_snapshotTasks_2655_);
lean_inc(v_infoState_2654_);
lean_inc(v_messages_2653_);
lean_inc(v_traceState_2652_);
lean_inc(v_auxDeclNGen_2651_);
lean_inc(v_ngen_2650_);
lean_inc(v_nextMacroScope_2649_);
lean_inc(v_env_2648_);
lean_dec(v___x_2646_);
v___x_2657_ = lean_box(0);
v_isShared_2658_ = v_isSharedCheck_2671_;
goto v_resetjp_2656_;
}
v_resetjp_2656_:
{
lean_object* v_asyncMode_2659_; lean_object* v___x_2660_; lean_object* v___x_2661_; lean_object* v___x_2662_; lean_object* v___x_2664_; 
v_asyncMode_2659_ = lean_ctor_get(v_toEnvExtension_2647_, 2);
lean_inc(v_asyncMode_2659_);
lean_inc(v_a_2645_);
lean_inc_n(v_decl_2627_, 2);
v___x_2660_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2660_, 0, v_decl_2627_);
lean_ctor_set(v___x_2660_, 1, v_a_2645_);
v___x_2661_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_a_2624_, v_env_2648_, v___x_2660_, v_asyncMode_2659_, v_decl_2627_);
lean_dec(v_asyncMode_2659_);
v___x_2662_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2);
if (v_isShared_2658_ == 0)
{
lean_ctor_set(v___x_2657_, 5, v___x_2662_);
lean_ctor_set(v___x_2657_, 0, v___x_2661_);
v___x_2664_ = v___x_2657_;
goto v_reusejp_2663_;
}
else
{
lean_object* v_reuseFailAlloc_2670_; 
v_reuseFailAlloc_2670_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2670_, 0, v___x_2661_);
lean_ctor_set(v_reuseFailAlloc_2670_, 1, v_nextMacroScope_2649_);
lean_ctor_set(v_reuseFailAlloc_2670_, 2, v_ngen_2650_);
lean_ctor_set(v_reuseFailAlloc_2670_, 3, v_auxDeclNGen_2651_);
lean_ctor_set(v_reuseFailAlloc_2670_, 4, v_traceState_2652_);
lean_ctor_set(v_reuseFailAlloc_2670_, 5, v___x_2662_);
lean_ctor_set(v_reuseFailAlloc_2670_, 6, v_messages_2653_);
lean_ctor_set(v_reuseFailAlloc_2670_, 7, v_infoState_2654_);
lean_ctor_set(v_reuseFailAlloc_2670_, 8, v_snapshotTasks_2655_);
v___x_2664_ = v_reuseFailAlloc_2670_;
goto v_reusejp_2663_;
}
v_reusejp_2663_:
{
lean_object* v___x_2665_; lean_object* v___x_2666_; 
v___x_2665_ = lean_st_ref_set(v___y_2643_, v___x_2664_);
lean_inc(v___y_2643_);
lean_inc_ref(v___y_2642_);
v___x_2666_ = lean_apply_5(v_afterSet_2625_, v_decl_2627_, v_a_2645_, v___y_2642_, v___y_2643_, lean_box(0));
if (lean_obj_tag(v___x_2666_) == 0)
{
lean_dec_ref(v___y_2641_);
return v___x_2666_;
}
else
{
lean_object* v_a_2667_; uint8_t v___x_2668_; 
v_a_2667_ = lean_ctor_get(v___x_2666_, 0);
lean_inc(v_a_2667_);
v___x_2668_ = l_Lean_Exception_isInterrupt(v_a_2667_);
if (v___x_2668_ == 0)
{
uint8_t v___x_2669_; 
v___x_2669_ = l_Lean_Exception_isRuntime(v_a_2667_);
v___y_2634_ = v___y_2641_;
v___y_2635_ = v___x_2666_;
v___y_2636_ = v___y_2642_;
v___y_2637_ = v___y_2643_;
v___y_2638_ = v___x_2669_;
goto v___jp_2633_;
}
else
{
lean_dec(v_a_2667_);
v___y_2634_ = v___y_2641_;
v___y_2635_ = v___x_2666_;
v___y_2636_ = v___y_2642_;
v___y_2637_ = v___y_2643_;
v___y_2638_ = v___x_2668_;
goto v___jp_2633_;
}
}
}
}
}
else
{
lean_object* v_a_2673_; lean_object* v___x_2675_; uint8_t v_isShared_2676_; uint8_t v_isSharedCheck_2680_; 
lean_dec_ref(v___y_2641_);
lean_dec(v_decl_2627_);
lean_dec_ref(v_afterSet_2625_);
lean_dec_ref(v_a_2624_);
v_a_2673_ = lean_ctor_get(v___x_2644_, 0);
v_isSharedCheck_2680_ = !lean_is_exclusive(v___x_2644_);
if (v_isSharedCheck_2680_ == 0)
{
v___x_2675_ = v___x_2644_;
v_isShared_2676_ = v_isSharedCheck_2680_;
goto v_resetjp_2674_;
}
else
{
lean_inc(v_a_2673_);
lean_dec(v___x_2644_);
v___x_2675_ = lean_box(0);
v_isShared_2676_ = v_isSharedCheck_2680_;
goto v_resetjp_2674_;
}
v_resetjp_2674_:
{
lean_object* v___x_2678_; 
if (v_isShared_2676_ == 0)
{
v___x_2678_ = v___x_2675_;
goto v_reusejp_2677_;
}
else
{
lean_object* v_reuseFailAlloc_2679_; 
v_reuseFailAlloc_2679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2679_, 0, v_a_2673_);
v___x_2678_ = v_reuseFailAlloc_2679_;
goto v_reusejp_2677_;
}
v_reusejp_2677_:
{
return v___x_2678_;
}
}
}
}
v___jp_2681_:
{
lean_object* v___x_2682_; lean_object* v_env_2683_; lean_object* v___x_2684_; 
v___x_2682_ = lean_st_ref_get(v___y_2631_);
v_env_2683_ = lean_ctor_get(v___x_2682_, 0);
lean_inc_ref(v_env_2683_);
lean_dec(v___x_2682_);
v___x_2684_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2683_, v_decl_2627_);
if (lean_obj_tag(v___x_2684_) == 0)
{
lean_dec(v_name_2626_);
v___y_2641_ = v_env_2683_;
v___y_2642_ = v___y_2630_;
v___y_2643_ = v___y_2631_;
goto v___jp_2640_;
}
else
{
lean_object* v___x_2685_; 
lean_dec_ref(v___x_2684_);
lean_dec_ref(v_env_2683_);
lean_dec(v_stx_2628_);
lean_dec_ref(v_afterSet_2625_);
lean_dec_ref(v_a_2624_);
lean_dec_ref(v_getParam_2623_);
v___x_2685_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg(v_name_2626_, v_decl_2627_, v___y_2630_, v___y_2631_);
return v___x_2685_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___lam__7___boxed(lean_object* v_getParam_2689_, lean_object* v_a_2690_, lean_object* v_afterSet_2691_, lean_object* v_name_2692_, lean_object* v_decl_2693_, lean_object* v_stx_2694_, lean_object* v_kind_2695_, lean_object* v___y_2696_, lean_object* v___y_2697_, lean_object* v___y_2698_){
_start:
{
uint8_t v_kind_boxed_2699_; lean_object* v_res_2700_; 
v_kind_boxed_2699_ = lean_unbox(v_kind_2695_);
v_res_2700_ = l_Lean_registerParametricAttribute___redArg___lam__7(v_getParam_2689_, v_a_2690_, v_afterSet_2691_, v_name_2692_, v_decl_2693_, v_stx_2694_, v_kind_boxed_2699_, v___y_2696_, v___y_2697_);
lean_dec(v___y_2697_);
lean_dec_ref(v___y_2696_);
return v_res_2700_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg(lean_object* v_impl_2711_){
_start:
{
lean_object* v_toAttributeImplCore_2713_; lean_object* v_getParam_2714_; lean_object* v_afterSet_2715_; uint8_t v_preserveOrder_2716_; lean_object* v_ref_2717_; lean_object* v_name_2718_; lean_object* v___f_2719_; lean_object* v___x_2720_; lean_object* v___f_2721_; lean_object* v___f_2722_; lean_object* v___f_2723_; lean_object* v___f_2724_; lean_object* v___f_2725_; lean_object* v___x_2726_; lean_object* v___x_2727_; lean_object* v___x_2728_; lean_object* v___x_2729_; lean_object* v___x_2730_; 
v_toAttributeImplCore_2713_ = lean_ctor_get(v_impl_2711_, 0);
lean_inc_ref(v_toAttributeImplCore_2713_);
v_getParam_2714_ = lean_ctor_get(v_impl_2711_, 1);
lean_inc_ref(v_getParam_2714_);
v_afterSet_2715_ = lean_ctor_get(v_impl_2711_, 2);
lean_inc_ref(v_afterSet_2715_);
v_preserveOrder_2716_ = lean_ctor_get_uint8(v_impl_2711_, sizeof(void*)*4);
v_ref_2717_ = lean_ctor_get(v_toAttributeImplCore_2713_, 0);
v_name_2718_ = lean_ctor_get(v_toAttributeImplCore_2713_, 1);
v___f_2719_ = ((lean_object*)(l_Lean_registerParametricAttribute___redArg___closed__0));
v___x_2720_ = lean_box(v_preserveOrder_2716_);
v___f_2721_ = lean_alloc_closure((void*)(l_Lean_registerParametricAttribute___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_2721_, 0, v_impl_2711_);
lean_closure_set(v___f_2721_, 1, v___x_2720_);
v___f_2722_ = ((lean_object*)(l_Lean_registerParametricAttribute___redArg___closed__1));
v___f_2723_ = ((lean_object*)(l_Lean_registerParametricAttribute___redArg___closed__2));
v___f_2724_ = ((lean_object*)(l_Lean_registerParametricAttribute___redArg___closed__4));
v___f_2725_ = ((lean_object*)(l_Lean_registerParametricAttribute___redArg___closed__5));
v___x_2726_ = lean_box(2);
v___x_2727_ = lean_box(0);
lean_inc(v_ref_2717_);
v___x_2728_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_2728_, 0, v_ref_2717_);
lean_ctor_set(v___x_2728_, 1, v___f_2725_);
lean_ctor_set(v___x_2728_, 2, v___f_2724_);
lean_ctor_set(v___x_2728_, 3, v___f_2719_);
lean_ctor_set(v___x_2728_, 4, v___f_2721_);
lean_ctor_set(v___x_2728_, 5, v___f_2722_);
lean_ctor_set(v___x_2728_, 6, v___x_2726_);
lean_ctor_set(v___x_2728_, 7, v___x_2727_);
v___x_2729_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2729_, 0, v___x_2728_);
lean_ctor_set(v___x_2729_, 1, v___f_2723_);
v___x_2730_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_2729_);
if (lean_obj_tag(v___x_2730_) == 0)
{
lean_object* v_a_2731_; lean_object* v___f_2732_; lean_object* v___f_2733_; lean_object* v___x_2734_; lean_object* v___x_2735_; 
v_a_2731_ = lean_ctor_get(v___x_2730_, 0);
lean_inc_n(v_a_2731_, 2);
lean_dec_ref(v___x_2730_);
lean_inc_n(v_name_2718_, 2);
v___f_2732_ = lean_alloc_closure((void*)(l_Lean_registerTagAttribute___lam__6___boxed), 5, 1);
lean_closure_set(v___f_2732_, 0, v_name_2718_);
v___f_2733_ = lean_alloc_closure((void*)(l_Lean_registerParametricAttribute___redArg___lam__7___boxed), 10, 4);
lean_closure_set(v___f_2733_, 0, v_getParam_2714_);
lean_closure_set(v___f_2733_, 1, v_a_2731_);
lean_closure_set(v___f_2733_, 2, v_afterSet_2715_);
lean_closure_set(v___f_2733_, 3, v_name_2718_);
v___x_2734_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2734_, 0, v_toAttributeImplCore_2713_);
lean_ctor_set(v___x_2734_, 1, v___f_2733_);
lean_ctor_set(v___x_2734_, 2, v___f_2732_);
lean_inc_ref(v___x_2734_);
v___x_2735_ = l_Lean_registerBuiltinAttribute(v___x_2734_);
if (lean_obj_tag(v___x_2735_) == 0)
{
lean_object* v___x_2737_; uint8_t v_isShared_2738_; uint8_t v_isSharedCheck_2743_; 
v_isSharedCheck_2743_ = !lean_is_exclusive(v___x_2735_);
if (v_isSharedCheck_2743_ == 0)
{
lean_object* v_unused_2744_; 
v_unused_2744_ = lean_ctor_get(v___x_2735_, 0);
lean_dec(v_unused_2744_);
v___x_2737_ = v___x_2735_;
v_isShared_2738_ = v_isSharedCheck_2743_;
goto v_resetjp_2736_;
}
else
{
lean_dec(v___x_2735_);
v___x_2737_ = lean_box(0);
v_isShared_2738_ = v_isSharedCheck_2743_;
goto v_resetjp_2736_;
}
v_resetjp_2736_:
{
lean_object* v___x_2739_; lean_object* v___x_2741_; 
v___x_2739_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2739_, 0, v___x_2734_);
lean_ctor_set(v___x_2739_, 1, v_a_2731_);
lean_ctor_set_uint8(v___x_2739_, sizeof(void*)*2, v_preserveOrder_2716_);
if (v_isShared_2738_ == 0)
{
lean_ctor_set(v___x_2737_, 0, v___x_2739_);
v___x_2741_ = v___x_2737_;
goto v_reusejp_2740_;
}
else
{
lean_object* v_reuseFailAlloc_2742_; 
v_reuseFailAlloc_2742_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2742_, 0, v___x_2739_);
v___x_2741_ = v_reuseFailAlloc_2742_;
goto v_reusejp_2740_;
}
v_reusejp_2740_:
{
return v___x_2741_;
}
}
}
else
{
lean_object* v_a_2745_; lean_object* v___x_2747_; uint8_t v_isShared_2748_; uint8_t v_isSharedCheck_2752_; 
lean_dec_ref(v___x_2734_);
lean_dec(v_a_2731_);
v_a_2745_ = lean_ctor_get(v___x_2735_, 0);
v_isSharedCheck_2752_ = !lean_is_exclusive(v___x_2735_);
if (v_isSharedCheck_2752_ == 0)
{
v___x_2747_ = v___x_2735_;
v_isShared_2748_ = v_isSharedCheck_2752_;
goto v_resetjp_2746_;
}
else
{
lean_inc(v_a_2745_);
lean_dec(v___x_2735_);
v___x_2747_ = lean_box(0);
v_isShared_2748_ = v_isSharedCheck_2752_;
goto v_resetjp_2746_;
}
v_resetjp_2746_:
{
lean_object* v___x_2750_; 
if (v_isShared_2748_ == 0)
{
v___x_2750_ = v___x_2747_;
goto v_reusejp_2749_;
}
else
{
lean_object* v_reuseFailAlloc_2751_; 
v_reuseFailAlloc_2751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2751_, 0, v_a_2745_);
v___x_2750_ = v_reuseFailAlloc_2751_;
goto v_reusejp_2749_;
}
v_reusejp_2749_:
{
return v___x_2750_;
}
}
}
}
else
{
lean_object* v_a_2753_; lean_object* v___x_2755_; uint8_t v_isShared_2756_; uint8_t v_isSharedCheck_2760_; 
lean_dec_ref(v_afterSet_2715_);
lean_dec_ref(v_getParam_2714_);
lean_dec_ref(v_toAttributeImplCore_2713_);
v_a_2753_ = lean_ctor_get(v___x_2730_, 0);
v_isSharedCheck_2760_ = !lean_is_exclusive(v___x_2730_);
if (v_isSharedCheck_2760_ == 0)
{
v___x_2755_ = v___x_2730_;
v_isShared_2756_ = v_isSharedCheck_2760_;
goto v_resetjp_2754_;
}
else
{
lean_inc(v_a_2753_);
lean_dec(v___x_2730_);
v___x_2755_ = lean_box(0);
v_isShared_2756_ = v_isSharedCheck_2760_;
goto v_resetjp_2754_;
}
v_resetjp_2754_:
{
lean_object* v___x_2758_; 
if (v_isShared_2756_ == 0)
{
v___x_2758_ = v___x_2755_;
goto v_reusejp_2757_;
}
else
{
lean_object* v_reuseFailAlloc_2759_; 
v_reuseFailAlloc_2759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2759_, 0, v_a_2753_);
v___x_2758_ = v_reuseFailAlloc_2759_;
goto v_reusejp_2757_;
}
v_reusejp_2757_:
{
return v___x_2758_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___boxed(lean_object* v_impl_2761_, lean_object* v_a_2762_){
_start:
{
lean_object* v_res_2763_; 
v_res_2763_ = l_Lean_registerParametricAttribute___redArg(v_impl_2761_);
return v_res_2763_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute(lean_object* v_00_u03b1_2764_, lean_object* v_impl_2765_){
_start:
{
lean_object* v___x_2767_; 
v___x_2767_ = l_Lean_registerParametricAttribute___redArg(v_impl_2765_);
return v___x_2767_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___boxed(lean_object* v_00_u03b1_2768_, lean_object* v_impl_2769_, lean_object* v_a_2770_){
_start:
{
lean_object* v_res_2771_; 
v_res_2771_ = l_Lean_registerParametricAttribute(v_00_u03b1_2768_, v_impl_2769_);
return v_res_2771_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttribute_spec__0(lean_object* v_00_u03b1_2772_, lean_object* v_impl_2773_, lean_object* v_env_2774_, lean_object* v_as_2775_, size_t v_i_2776_, size_t v_stop_2777_, lean_object* v_b_2778_){
_start:
{
lean_object* v___x_2779_; 
v___x_2779_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttribute_spec__0___redArg(v_impl_2773_, v_env_2774_, v_as_2775_, v_i_2776_, v_stop_2777_, v_b_2778_);
return v___x_2779_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttribute_spec__0___boxed(lean_object* v_00_u03b1_2780_, lean_object* v_impl_2781_, lean_object* v_env_2782_, lean_object* v_as_2783_, lean_object* v_i_2784_, lean_object* v_stop_2785_, lean_object* v_b_2786_){
_start:
{
size_t v_i_boxed_2787_; size_t v_stop_boxed_2788_; lean_object* v_res_2789_; 
v_i_boxed_2787_ = lean_unbox_usize(v_i_2784_);
lean_dec(v_i_2784_);
v_stop_boxed_2788_ = lean_unbox_usize(v_stop_2785_);
lean_dec(v_stop_2785_);
v_res_2789_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttribute_spec__0(v_00_u03b1_2780_, v_impl_2781_, v_env_2782_, v_as_2783_, v_i_boxed_2787_, v_stop_boxed_2788_, v_b_2786_);
lean_dec_ref(v_as_2783_);
return v_res_2789_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1___redArg(lean_object* v_init_2790_, lean_object* v_t_2791_){
_start:
{
lean_object* v___x_2792_; 
v___x_2792_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1_spec__1___redArg(v_init_2790_, v_t_2791_);
return v___x_2792_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1___redArg___boxed(lean_object* v_init_2793_, lean_object* v_t_2794_){
_start:
{
lean_object* v_res_2795_; 
v_res_2795_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1___redArg(v_init_2793_, v_t_2794_);
lean_dec(v_t_2794_);
return v_res_2795_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1(lean_object* v_00_u03b1_2796_, lean_object* v_init_2797_, lean_object* v_t_2798_){
_start:
{
lean_object* v___x_2799_; 
v___x_2799_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1_spec__1___redArg(v_init_2797_, v_t_2798_);
return v___x_2799_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1___boxed(lean_object* v_00_u03b1_2800_, lean_object* v_init_2801_, lean_object* v_t_2802_){
_start:
{
lean_object* v_res_2803_; 
v_res_2803_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1(v_00_u03b1_2800_, v_init_2801_, v_t_2802_);
lean_dec(v_t_2802_);
return v_res_2803_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2(lean_object* v_00_u03b1_2804_, lean_object* v_n_2805_, lean_object* v_as_2806_, lean_object* v_lo_2807_, lean_object* v_hi_2808_, lean_object* v_w_2809_, lean_object* v_hlo_2810_, lean_object* v_hhi_2811_){
_start:
{
lean_object* v___x_2812_; 
v___x_2812_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2___redArg(v_as_2806_, v_lo_2807_, v_hi_2808_);
return v___x_2812_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2___boxed(lean_object* v_00_u03b1_2813_, lean_object* v_n_2814_, lean_object* v_as_2815_, lean_object* v_lo_2816_, lean_object* v_hi_2817_, lean_object* v_w_2818_, lean_object* v_hlo_2819_, lean_object* v_hhi_2820_){
_start:
{
lean_object* v_res_2821_; 
v_res_2821_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2(v_00_u03b1_2813_, v_n_2814_, v_as_2815_, v_lo_2816_, v_hi_2817_, v_w_2818_, v_hlo_2819_, v_hhi_2820_);
lean_dec(v_hi_2817_);
lean_dec(v_n_2814_);
return v_res_2821_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3(lean_object* v_00_u03b1_2822_, lean_object* v_snd_2823_, lean_object* v_as_2824_, lean_object* v_start_2825_, lean_object* v_stop_2826_){
_start:
{
lean_object* v___x_2827_; 
v___x_2827_ = l_Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3___redArg(v_snd_2823_, v_as_2824_, v_start_2825_, v_stop_2826_);
return v___x_2827_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3___boxed(lean_object* v_00_u03b1_2828_, lean_object* v_snd_2829_, lean_object* v_as_2830_, lean_object* v_start_2831_, lean_object* v_stop_2832_){
_start:
{
lean_object* v_res_2833_; 
v_res_2833_ = l_Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3(v_00_u03b1_2828_, v_snd_2829_, v_as_2830_, v_start_2831_, v_stop_2832_);
lean_dec(v_stop_2832_);
lean_dec(v_start_2831_);
lean_dec_ref(v_as_2830_);
lean_dec(v_snd_2829_);
return v_res_2833_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1_spec__1(lean_object* v_00_u03b1_2834_, lean_object* v_init_2835_, lean_object* v_x_2836_){
_start:
{
lean_object* v___x_2837_; 
v___x_2837_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1_spec__1___redArg(v_init_2835_, v_x_2836_);
return v___x_2837_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1_spec__1___boxed(lean_object* v_00_u03b1_2838_, lean_object* v_init_2839_, lean_object* v_x_2840_){
_start:
{
lean_object* v_res_2841_; 
v_res_2841_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1_spec__1(v_00_u03b1_2838_, v_init_2839_, v_x_2840_);
lean_dec(v_x_2840_);
return v_res_2841_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3_spec__4(lean_object* v_00_u03b1_2842_, lean_object* v_snd_2843_, lean_object* v_as_2844_, size_t v_i_2845_, size_t v_stop_2846_, lean_object* v_b_2847_){
_start:
{
lean_object* v___x_2848_; 
v___x_2848_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3_spec__4___redArg(v_snd_2843_, v_as_2844_, v_i_2845_, v_stop_2846_, v_b_2847_);
return v___x_2848_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3_spec__4___boxed(lean_object* v_00_u03b1_2849_, lean_object* v_snd_2850_, lean_object* v_as_2851_, lean_object* v_i_2852_, lean_object* v_stop_2853_, lean_object* v_b_2854_){
_start:
{
size_t v_i_boxed_2855_; size_t v_stop_boxed_2856_; lean_object* v_res_2857_; 
v_i_boxed_2855_ = lean_unbox_usize(v_i_2852_);
lean_dec(v_i_2852_);
v_stop_boxed_2856_ = lean_unbox_usize(v_stop_2853_);
lean_dec(v_stop_2853_);
v_res_2857_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3_spec__4(v_00_u03b1_2849_, v_snd_2850_, v_as_2851_, v_i_boxed_2855_, v_stop_boxed_2856_, v_b_2854_);
lean_dec_ref(v_as_2851_);
lean_dec(v_snd_2850_);
return v_res_2857_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParam_x3f___redArg___lam__1(lean_object* v_decl_2858_, lean_object* v___x_2859_, lean_object* v___x_2860_, lean_object* v_a_2861_, lean_object* v_x_2862_, lean_object* v___y_2863_){
_start:
{
lean_object* v_fst_2864_; uint8_t v___x_2865_; 
v_fst_2864_ = lean_ctor_get(v_a_2861_, 0);
v___x_2865_ = lean_name_eq(v_fst_2864_, v_decl_2858_);
if (v___x_2865_ == 0)
{
lean_object* v___x_2866_; 
lean_dec_ref(v_a_2861_);
v___x_2866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2866_, 0, v___x_2859_);
return v___x_2866_;
}
else
{
lean_object* v___x_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; lean_object* v___x_2870_; 
lean_dec_ref(v___x_2859_);
v___x_2867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2867_, 0, v_a_2861_);
v___x_2868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2868_, 0, v___x_2867_);
v___x_2869_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2869_, 0, v___x_2868_);
lean_ctor_set(v___x_2869_, 1, v___x_2860_);
v___x_2870_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2870_, 0, v___x_2869_);
return v___x_2870_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParam_x3f___redArg___lam__1___boxed(lean_object* v_decl_2871_, lean_object* v___x_2872_, lean_object* v___x_2873_, lean_object* v_a_2874_, lean_object* v_x_2875_, lean_object* v___y_2876_){
_start:
{
lean_object* v_res_2877_; 
v_res_2877_ = l_Lean_ParametricAttribute_getParam_x3f___redArg___lam__1(v_decl_2871_, v___x_2872_, v___x_2873_, v_a_2874_, v_x_2875_, v___y_2876_);
lean_dec_ref(v___y_2876_);
lean_dec(v_decl_2871_);
return v_res_2877_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParam_x3f___redArg(lean_object* v_inst_2904_, lean_object* v_attr_2905_, lean_object* v_env_2906_, lean_object* v_decl_2907_){
_start:
{
lean_object* v___y_2909_; lean_object* v___x_2920_; lean_object* v___x_2921_; 
v___x_2920_ = ((lean_object*)(l_Lean_ParametricAttribute_getParam_x3f___redArg___closed__0));
v___x_2921_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2906_, v_decl_2907_);
if (lean_obj_tag(v___x_2921_) == 0)
{
lean_object* v_ext_2922_; lean_object* v_toEnvExtension_2923_; lean_object* v_asyncMode_2924_; lean_object* v___x_2925_; lean_object* v___x_2926_; lean_object* v_snd_2927_; lean_object* v___x_2928_; 
lean_dec(v_inst_2904_);
v_ext_2922_ = lean_ctor_get(v_attr_2905_, 1);
v_toEnvExtension_2923_ = lean_ctor_get(v_ext_2922_, 0);
v_asyncMode_2924_ = lean_ctor_get(v_toEnvExtension_2923_, 2);
v___x_2925_ = lean_box(0);
v___x_2926_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2920_, v_ext_2922_, v_env_2906_, v_asyncMode_2924_, v___x_2925_);
v_snd_2927_ = lean_ctor_get(v___x_2926_, 1);
lean_inc(v_snd_2927_);
lean_dec(v___x_2926_);
v___x_2928_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_snd_2927_, v_decl_2907_);
lean_dec(v_decl_2907_);
lean_dec(v_snd_2927_);
return v___x_2928_;
}
else
{
uint8_t v_preserveOrder_2929_; 
v_preserveOrder_2929_ = lean_ctor_get_uint8(v_attr_2905_, sizeof(void*)*2);
if (v_preserveOrder_2929_ == 0)
{
lean_object* v_val_2930_; lean_object* v_ext_2931_; uint8_t v___x_2932_; lean_object* v___x_2933_; lean_object* v___x_2934_; lean_object* v___x_2935_; uint8_t v___x_2936_; 
v_val_2930_ = lean_ctor_get(v___x_2921_, 0);
lean_inc(v_val_2930_);
lean_dec_ref(v___x_2921_);
v_ext_2931_ = lean_ctor_get(v_attr_2905_, 1);
v___x_2932_ = 0;
v___x_2933_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_2920_, v_ext_2931_, v_env_2906_, v_val_2930_, v___x_2932_);
lean_dec(v_val_2930_);
lean_dec_ref(v_env_2906_);
v___x_2934_ = lean_unsigned_to_nat(0u);
v___x_2935_ = lean_array_get_size(v___x_2933_);
v___x_2936_ = lean_nat_dec_lt(v___x_2934_, v___x_2935_);
if (v___x_2936_ == 0)
{
lean_object* v___x_2937_; 
lean_dec_ref(v___x_2933_);
lean_dec(v_decl_2907_);
lean_dec(v_inst_2904_);
v___x_2937_ = lean_box(0);
return v___x_2937_;
}
else
{
lean_object* v___x_2938_; lean_object* v___x_2939_; uint8_t v___x_2940_; 
v___x_2938_ = lean_unsigned_to_nat(1u);
v___x_2939_ = lean_nat_sub(v___x_2935_, v___x_2938_);
v___x_2940_ = lean_nat_dec_le(v___x_2934_, v___x_2939_);
if (v___x_2940_ == 0)
{
lean_object* v___x_2941_; 
lean_dec(v___x_2939_);
lean_dec_ref(v___x_2933_);
lean_dec(v_decl_2907_);
lean_dec(v_inst_2904_);
v___x_2941_ = lean_box(0);
return v___x_2941_;
}
else
{
lean_object* v___f_2942_; lean_object* v___x_2943_; lean_object* v___x_2944_; lean_object* v___x_2945_; 
v___f_2942_ = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2___redArg___closed__0));
v___x_2943_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2943_, 0, v_decl_2907_);
lean_ctor_set(v___x_2943_, 1, v_inst_2904_);
v___x_2944_ = ((lean_object*)(l_Lean_ParametricAttribute_getParam_x3f___redArg___closed__1));
v___x_2945_ = l_Array_binSearchAux___redArg(v___f_2942_, v___x_2944_, v___x_2933_, v___x_2943_, v___x_2934_, v___x_2939_);
lean_dec_ref(v___x_2933_);
v___y_2909_ = v___x_2945_;
goto v___jp_2908_;
}
}
}
else
{
lean_object* v_val_2946_; lean_object* v_ext_2947_; uint8_t v___x_2948_; lean_object* v___x_2949_; lean_object* v___x_2950_; lean_object* v___x_2951_; lean_object* v___x_2952_; lean_object* v___x_2953_; lean_object* v___f_2954_; size_t v_sz_2955_; size_t v___x_2956_; lean_object* v___x_2957_; lean_object* v_fst_2958_; 
lean_dec(v_inst_2904_);
v_val_2946_ = lean_ctor_get(v___x_2921_, 0);
lean_inc(v_val_2946_);
lean_dec_ref(v___x_2921_);
v_ext_2947_ = lean_ctor_get(v_attr_2905_, 1);
v___x_2948_ = 0;
v___x_2949_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_2920_, v_ext_2947_, v_env_2906_, v_val_2946_, v___x_2948_);
lean_dec(v_val_2946_);
lean_dec_ref(v_env_2906_);
v___x_2950_ = ((lean_object*)(l_Lean_ParametricAttribute_getParam_x3f___redArg___closed__11));
v___x_2951_ = lean_box(0);
v___x_2952_ = lean_box(0);
v___x_2953_ = ((lean_object*)(l_Lean_ParametricAttribute_getParam_x3f___redArg___closed__12));
v___f_2954_ = lean_alloc_closure((void*)(l_Lean_ParametricAttribute_getParam_x3f___redArg___lam__1___boxed), 6, 3);
lean_closure_set(v___f_2954_, 0, v_decl_2907_);
lean_closure_set(v___f_2954_, 1, v___x_2953_);
lean_closure_set(v___f_2954_, 2, v___x_2952_);
v_sz_2955_ = lean_array_size(v___x_2949_);
v___x_2956_ = ((size_t)0ULL);
v___x_2957_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_2950_, v___x_2949_, v___f_2954_, v_sz_2955_, v___x_2956_, v___x_2953_);
v_fst_2958_ = lean_ctor_get(v___x_2957_, 0);
lean_inc(v_fst_2958_);
lean_dec(v___x_2957_);
if (lean_obj_tag(v_fst_2958_) == 0)
{
return v___x_2951_;
}
else
{
lean_object* v_val_2959_; 
v_val_2959_ = lean_ctor_get(v_fst_2958_, 0);
lean_inc(v_val_2959_);
lean_dec_ref(v_fst_2958_);
v___y_2909_ = v_val_2959_;
goto v___jp_2908_;
}
}
}
v___jp_2908_:
{
if (lean_obj_tag(v___y_2909_) == 0)
{
lean_object* v___x_2910_; 
v___x_2910_ = lean_box(0);
return v___x_2910_;
}
else
{
lean_object* v_val_2911_; lean_object* v___x_2913_; uint8_t v_isShared_2914_; uint8_t v_isSharedCheck_2919_; 
v_val_2911_ = lean_ctor_get(v___y_2909_, 0);
v_isSharedCheck_2919_ = !lean_is_exclusive(v___y_2909_);
if (v_isSharedCheck_2919_ == 0)
{
v___x_2913_ = v___y_2909_;
v_isShared_2914_ = v_isSharedCheck_2919_;
goto v_resetjp_2912_;
}
else
{
lean_inc(v_val_2911_);
lean_dec(v___y_2909_);
v___x_2913_ = lean_box(0);
v_isShared_2914_ = v_isSharedCheck_2919_;
goto v_resetjp_2912_;
}
v_resetjp_2912_:
{
lean_object* v_snd_2915_; lean_object* v___x_2917_; 
v_snd_2915_ = lean_ctor_get(v_val_2911_, 1);
lean_inc(v_snd_2915_);
lean_dec(v_val_2911_);
if (v_isShared_2914_ == 0)
{
lean_ctor_set(v___x_2913_, 0, v_snd_2915_);
v___x_2917_ = v___x_2913_;
goto v_reusejp_2916_;
}
else
{
lean_object* v_reuseFailAlloc_2918_; 
v_reuseFailAlloc_2918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2918_, 0, v_snd_2915_);
v___x_2917_ = v_reuseFailAlloc_2918_;
goto v_reusejp_2916_;
}
v_reusejp_2916_:
{
return v___x_2917_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParam_x3f___redArg___boxed(lean_object* v_inst_2960_, lean_object* v_attr_2961_, lean_object* v_env_2962_, lean_object* v_decl_2963_){
_start:
{
lean_object* v_res_2964_; 
v_res_2964_ = l_Lean_ParametricAttribute_getParam_x3f___redArg(v_inst_2960_, v_attr_2961_, v_env_2962_, v_decl_2963_);
lean_dec_ref(v_attr_2961_);
return v_res_2964_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParam_x3f(lean_object* v_00_u03b1_2965_, lean_object* v_inst_2966_, lean_object* v_attr_2967_, lean_object* v_env_2968_, lean_object* v_decl_2969_){
_start:
{
lean_object* v___x_2970_; 
v___x_2970_ = l_Lean_ParametricAttribute_getParam_x3f___redArg(v_inst_2966_, v_attr_2967_, v_env_2968_, v_decl_2969_);
return v___x_2970_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParam_x3f___boxed(lean_object* v_00_u03b1_2971_, lean_object* v_inst_2972_, lean_object* v_attr_2973_, lean_object* v_env_2974_, lean_object* v_decl_2975_){
_start:
{
lean_object* v_res_2976_; 
v_res_2976_ = l_Lean_ParametricAttribute_getParam_x3f(v_00_u03b1_2971_, v_inst_2972_, v_attr_2973_, v_env_2974_, v_decl_2975_);
lean_dec_ref(v_attr_2973_);
return v_res_2976_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_setParam___redArg(lean_object* v_attr_2981_, lean_object* v_env_2982_, lean_object* v_decl_2983_, lean_object* v_param_2984_){
_start:
{
lean_object* v___x_2985_; 
v___x_2985_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2982_, v_decl_2983_);
if (lean_obj_tag(v___x_2985_) == 0)
{
lean_object* v_ext_2986_; lean_object* v_toEnvExtension_2987_; lean_object* v_attr_2988_; lean_object* v_asyncMode_2989_; lean_object* v___x_2990_; lean_object* v___x_2991_; lean_object* v___x_2992_; lean_object* v_snd_2993_; lean_object* v___x_2995_; uint8_t v_isShared_2996_; uint8_t v_isSharedCheck_3023_; 
v_ext_2986_ = lean_ctor_get(v_attr_2981_, 1);
lean_inc_ref(v_ext_2986_);
v_toEnvExtension_2987_ = lean_ctor_get(v_ext_2986_, 0);
v_attr_2988_ = lean_ctor_get(v_attr_2981_, 0);
lean_inc_ref(v_attr_2988_);
lean_dec_ref(v_attr_2981_);
v_asyncMode_2989_ = lean_ctor_get(v_toEnvExtension_2987_, 2);
lean_inc(v_asyncMode_2989_);
v___x_2990_ = ((lean_object*)(l_Lean_ParametricAttribute_getParam_x3f___redArg___closed__0));
v___x_2991_ = lean_box(0);
lean_inc_ref(v_env_2982_);
v___x_2992_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2990_, v_ext_2986_, v_env_2982_, v_asyncMode_2989_, v___x_2991_);
v_snd_2993_ = lean_ctor_get(v___x_2992_, 1);
v_isSharedCheck_3023_ = !lean_is_exclusive(v___x_2992_);
if (v_isSharedCheck_3023_ == 0)
{
lean_object* v_unused_3024_; 
v_unused_3024_ = lean_ctor_get(v___x_2992_, 0);
lean_dec(v_unused_3024_);
v___x_2995_ = v___x_2992_;
v_isShared_2996_ = v_isSharedCheck_3023_;
goto v_resetjp_2994_;
}
else
{
lean_inc(v_snd_2993_);
lean_dec(v___x_2992_);
v___x_2995_ = lean_box(0);
v_isShared_2996_ = v_isSharedCheck_3023_;
goto v_resetjp_2994_;
}
v_resetjp_2994_:
{
lean_object* v___x_2997_; 
v___x_2997_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_snd_2993_, v_decl_2983_);
lean_dec(v_snd_2993_);
if (lean_obj_tag(v___x_2997_) == 0)
{
lean_object* v___x_2999_; 
lean_dec_ref(v_attr_2988_);
if (v_isShared_2996_ == 0)
{
lean_ctor_set(v___x_2995_, 1, v_param_2984_);
lean_ctor_set(v___x_2995_, 0, v_decl_2983_);
v___x_2999_ = v___x_2995_;
goto v_reusejp_2998_;
}
else
{
lean_object* v_reuseFailAlloc_3002_; 
v_reuseFailAlloc_3002_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3002_, 0, v_decl_2983_);
lean_ctor_set(v_reuseFailAlloc_3002_, 1, v_param_2984_);
v___x_2999_ = v_reuseFailAlloc_3002_;
goto v_reusejp_2998_;
}
v_reusejp_2998_:
{
lean_object* v___x_3000_; lean_object* v___x_3001_; 
v___x_3000_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_ext_2986_, v_env_2982_, v___x_2999_, v_asyncMode_2989_, v___x_2991_);
lean_dec(v_asyncMode_2989_);
v___x_3001_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3001_, 0, v___x_3000_);
return v___x_3001_;
}
}
else
{
lean_object* v___x_3004_; uint8_t v_isShared_3005_; uint8_t v_isSharedCheck_3021_; 
lean_del_object(v___x_2995_);
lean_dec(v_asyncMode_2989_);
lean_dec_ref(v_ext_2986_);
lean_dec(v_param_2984_);
lean_dec_ref(v_env_2982_);
v_isSharedCheck_3021_ = !lean_is_exclusive(v___x_2997_);
if (v_isSharedCheck_3021_ == 0)
{
lean_object* v_unused_3022_; 
v_unused_3022_ = lean_ctor_get(v___x_2997_, 0);
lean_dec(v_unused_3022_);
v___x_3004_ = v___x_2997_;
v_isShared_3005_ = v_isSharedCheck_3021_;
goto v_resetjp_3003_;
}
else
{
lean_dec(v___x_2997_);
v___x_3004_ = lean_box(0);
v_isShared_3005_ = v_isSharedCheck_3021_;
goto v_resetjp_3003_;
}
v_resetjp_3003_:
{
lean_object* v_toAttributeImplCore_3006_; lean_object* v_name_3007_; uint8_t v___x_3008_; lean_object* v___x_3009_; lean_object* v___x_3010_; lean_object* v___x_3011_; lean_object* v___x_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; lean_object* v___x_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; lean_object* v___x_3019_; 
v_toAttributeImplCore_3006_ = lean_ctor_get(v_attr_2988_, 0);
lean_inc_ref(v_toAttributeImplCore_3006_);
lean_dec_ref(v_attr_2988_);
v_name_3007_ = lean_ctor_get(v_toAttributeImplCore_3006_, 1);
lean_inc(v_name_3007_);
lean_dec_ref(v_toAttributeImplCore_3006_);
v___x_3008_ = 1;
v___x_3009_ = ((lean_object*)(l_Lean_ParametricAttribute_setParam___redArg___closed__0));
v___x_3010_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_3007_, v___x_3008_);
v___x_3011_ = lean_string_append(v___x_3009_, v___x_3010_);
lean_dec_ref(v___x_3010_);
v___x_3012_ = ((lean_object*)(l_Lean_ParametricAttribute_setParam___redArg___closed__1));
v___x_3013_ = lean_string_append(v___x_3011_, v___x_3012_);
v___x_3014_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_decl_2983_, v___x_3008_);
v___x_3015_ = lean_string_append(v___x_3013_, v___x_3014_);
lean_dec_ref(v___x_3014_);
v___x_3016_ = ((lean_object*)(l_Lean_ParametricAttribute_setParam___redArg___closed__2));
v___x_3017_ = lean_string_append(v___x_3015_, v___x_3016_);
if (v_isShared_3005_ == 0)
{
lean_ctor_set_tag(v___x_3004_, 0);
lean_ctor_set(v___x_3004_, 0, v___x_3017_);
v___x_3019_ = v___x_3004_;
goto v_reusejp_3018_;
}
else
{
lean_object* v_reuseFailAlloc_3020_; 
v_reuseFailAlloc_3020_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3020_, 0, v___x_3017_);
v___x_3019_ = v_reuseFailAlloc_3020_;
goto v_reusejp_3018_;
}
v_reusejp_3018_:
{
return v___x_3019_;
}
}
}
}
}
else
{
lean_object* v___x_3026_; uint8_t v_isShared_3027_; uint8_t v_isSharedCheck_3044_; 
lean_dec(v_param_2984_);
lean_dec_ref(v_env_2982_);
v_isSharedCheck_3044_ = !lean_is_exclusive(v___x_2985_);
if (v_isSharedCheck_3044_ == 0)
{
lean_object* v_unused_3045_; 
v_unused_3045_ = lean_ctor_get(v___x_2985_, 0);
lean_dec(v_unused_3045_);
v___x_3026_ = v___x_2985_;
v_isShared_3027_ = v_isSharedCheck_3044_;
goto v_resetjp_3025_;
}
else
{
lean_dec(v___x_2985_);
v___x_3026_ = lean_box(0);
v_isShared_3027_ = v_isSharedCheck_3044_;
goto v_resetjp_3025_;
}
v_resetjp_3025_:
{
lean_object* v_attr_3028_; lean_object* v_toAttributeImplCore_3029_; lean_object* v_name_3030_; uint8_t v___x_3031_; lean_object* v___x_3032_; lean_object* v___x_3033_; lean_object* v___x_3034_; lean_object* v___x_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; lean_object* v___x_3040_; lean_object* v___x_3042_; 
v_attr_3028_ = lean_ctor_get(v_attr_2981_, 0);
lean_inc_ref(v_attr_3028_);
lean_dec_ref(v_attr_2981_);
v_toAttributeImplCore_3029_ = lean_ctor_get(v_attr_3028_, 0);
lean_inc_ref(v_toAttributeImplCore_3029_);
lean_dec_ref(v_attr_3028_);
v_name_3030_ = lean_ctor_get(v_toAttributeImplCore_3029_, 1);
lean_inc(v_name_3030_);
lean_dec_ref(v_toAttributeImplCore_3029_);
v___x_3031_ = 1;
v___x_3032_ = ((lean_object*)(l_Lean_ParametricAttribute_setParam___redArg___closed__0));
v___x_3033_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_3030_, v___x_3031_);
v___x_3034_ = lean_string_append(v___x_3032_, v___x_3033_);
lean_dec_ref(v___x_3033_);
v___x_3035_ = ((lean_object*)(l_Lean_ParametricAttribute_setParam___redArg___closed__1));
v___x_3036_ = lean_string_append(v___x_3034_, v___x_3035_);
v___x_3037_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_decl_2983_, v___x_3031_);
v___x_3038_ = lean_string_append(v___x_3036_, v___x_3037_);
lean_dec_ref(v___x_3037_);
v___x_3039_ = ((lean_object*)(l_Lean_ParametricAttribute_setParam___redArg___closed__3));
v___x_3040_ = lean_string_append(v___x_3038_, v___x_3039_);
if (v_isShared_3027_ == 0)
{
lean_ctor_set_tag(v___x_3026_, 0);
lean_ctor_set(v___x_3026_, 0, v___x_3040_);
v___x_3042_ = v___x_3026_;
goto v_reusejp_3041_;
}
else
{
lean_object* v_reuseFailAlloc_3043_; 
v_reuseFailAlloc_3043_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3043_, 0, v___x_3040_);
v___x_3042_ = v_reuseFailAlloc_3043_;
goto v_reusejp_3041_;
}
v_reusejp_3041_:
{
return v___x_3042_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_setParam(lean_object* v_00_u03b1_3046_, lean_object* v_attr_3047_, lean_object* v_env_3048_, lean_object* v_decl_3049_, lean_object* v_param_3050_){
_start:
{
lean_object* v___x_3051_; 
v___x_3051_ = l_Lean_ParametricAttribute_setParam___redArg(v_attr_3047_, v_env_3048_, v_decl_3049_, v_param_3050_);
return v___x_3051_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___lam__0(lean_object* v_x_3052_, lean_object* v___y_3053_){
_start:
{
lean_object* v___x_3055_; lean_object* v___x_3056_; 
v___x_3055_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___lam__0___closed__1));
v___x_3056_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3056_, 0, v___x_3055_);
return v___x_3056_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___lam__0___boxed(lean_object* v_x_3057_, lean_object* v___y_3058_, lean_object* v___y_3059_){
_start:
{
lean_object* v_res_3060_; 
v_res_3060_ = l_Lean_instInhabitedEnumAttributes_default___lam__0(v_x_3057_, v___y_3058_);
lean_dec_ref(v___y_3058_);
lean_dec_ref(v_x_3057_);
return v_res_3060_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___lam__1(lean_object* v_s_3061_, lean_object* v_x_3062_){
_start:
{
lean_inc(v_s_3061_);
return v_s_3061_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___lam__1___boxed(lean_object* v_s_3063_, lean_object* v_x_3064_){
_start:
{
lean_object* v_res_3065_; 
v_res_3065_ = l_Lean_instInhabitedEnumAttributes_default___lam__1(v_s_3063_, v_x_3064_);
lean_dec_ref(v_x_3064_);
lean_dec(v_s_3063_);
return v_res_3065_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___lam__2(lean_object* v_x_3066_, lean_object* v_x_3067_){
_start:
{
lean_object* v___x_3068_; 
v___x_3068_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___lam__2___closed__1));
return v___x_3068_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___lam__2___boxed(lean_object* v_x_3069_, lean_object* v_x_3070_){
_start:
{
lean_object* v_res_3071_; 
v_res_3071_ = l_Lean_instInhabitedEnumAttributes_default___lam__2(v_x_3069_, v_x_3070_);
lean_dec(v_x_3070_);
lean_dec_ref(v_x_3069_);
return v_res_3071_;
}
}
static lean_object* _init_l_Lean_instInhabitedEnumAttributes_default___closed__3(void){
_start:
{
lean_object* v___x_3075_; 
v___x_3075_ = l_Lean_instInhabitedEnvExtension_default(lean_box(0));
return v___x_3075_;
}
}
static lean_object* _init_l_Lean_instInhabitedEnumAttributes_default___closed__4(void){
_start:
{
lean_object* v___f_3076_; lean_object* v___f_3077_; lean_object* v___f_3078_; lean_object* v___f_3079_; lean_object* v___x_3080_; lean_object* v___x_3081_; lean_object* v___x_3082_; 
v___f_3076_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___closed__3));
v___f_3077_ = ((lean_object*)(l_Lean_instInhabitedEnumAttributes_default___closed__2));
v___f_3078_ = ((lean_object*)(l_Lean_instInhabitedEnumAttributes_default___closed__1));
v___f_3079_ = ((lean_object*)(l_Lean_instInhabitedEnumAttributes_default___closed__0));
v___x_3080_ = lean_box(0);
v___x_3081_ = lean_obj_once(&l_Lean_instInhabitedEnumAttributes_default___closed__3, &l_Lean_instInhabitedEnumAttributes_default___closed__3_once, _init_l_Lean_instInhabitedEnumAttributes_default___closed__3);
v___x_3082_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3082_, 0, v___x_3081_);
lean_ctor_set(v___x_3082_, 1, v___x_3080_);
lean_ctor_set(v___x_3082_, 2, v___f_3079_);
lean_ctor_set(v___x_3082_, 3, v___f_3078_);
lean_ctor_set(v___x_3082_, 4, v___f_3077_);
lean_ctor_set(v___x_3082_, 5, v___f_3076_);
return v___x_3082_;
}
}
static lean_object* _init_l_Lean_instInhabitedEnumAttributes_default___closed__5(void){
_start:
{
lean_object* v___x_3083_; lean_object* v___x_3084_; lean_object* v___x_3085_; 
v___x_3083_ = lean_obj_once(&l_Lean_instInhabitedEnumAttributes_default___closed__4, &l_Lean_instInhabitedEnumAttributes_default___closed__4_once, _init_l_Lean_instInhabitedEnumAttributes_default___closed__4);
v___x_3084_ = lean_box(0);
v___x_3085_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3085_, 0, v___x_3084_);
lean_ctor_set(v___x_3085_, 1, v___x_3083_);
return v___x_3085_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default(lean_object* v_00_u03b1_3086_){
_start:
{
lean_object* v___x_3087_; 
v___x_3087_ = lean_obj_once(&l_Lean_instInhabitedEnumAttributes_default___closed__5, &l_Lean_instInhabitedEnumAttributes_default___closed__5_once, _init_l_Lean_instInhabitedEnumAttributes_default___closed__5);
return v___x_3087_;
}
}
static lean_object* _init_l_Lean_instInhabitedEnumAttributes___closed__0(void){
_start:
{
lean_object* v___x_3088_; 
v___x_3088_ = l_Lean_instInhabitedEnumAttributes_default(lean_box(0));
return v___x_3088_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes(lean_object* v_a_3089_){
_start:
{
lean_object* v___x_3090_; 
v___x_3090_ = lean_obj_once(&l_Lean_instInhabitedEnumAttributes___closed__0, &l_Lean_instInhabitedEnumAttributes___closed__0_once, _init_l_Lean_instInhabitedEnumAttributes___closed__0);
return v___x_3090_;
}
}
static lean_object* _init_l_Lean_registerEnumAttributes___auto__1(void){
_start:
{
lean_object* v___x_3091_; 
v___x_3091_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__28, &l_Lean_AttributeImplCore_ref___autoParam___closed__28_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__28);
return v___x_3091_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__0(lean_object* v_x_3092_){
_start:
{
lean_object* v___x_3093_; 
v___x_3093_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___lam__2___closed__0));
return v___x_3093_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__0___boxed(lean_object* v_x_3094_){
_start:
{
lean_object* v_res_3095_; 
v_res_3095_ = l_Lean_registerEnumAttributes___redArg___lam__0(v_x_3094_);
lean_dec(v_x_3094_);
return v_res_3095_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___redArg(lean_object* v_newState_3096_, lean_object* v_x_3097_, lean_object* v_x_3098_){
_start:
{
if (lean_obj_tag(v_x_3098_) == 0)
{
return v_x_3097_;
}
else
{
lean_object* v_head_3099_; lean_object* v_tail_3100_; lean_object* v___x_3101_; 
v_head_3099_ = lean_ctor_get(v_x_3098_, 0);
lean_inc(v_head_3099_);
v_tail_3100_ = lean_ctor_get(v_x_3098_, 1);
lean_inc(v_tail_3100_);
lean_dec_ref(v_x_3098_);
v___x_3101_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_newState_3096_, v_head_3099_);
if (lean_obj_tag(v___x_3101_) == 1)
{
lean_object* v_val_3102_; lean_object* v___x_3103_; 
v_val_3102_ = lean_ctor_get(v___x_3101_, 0);
lean_inc(v_val_3102_);
lean_dec_ref(v___x_3101_);
v___x_3103_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_head_3099_, v_val_3102_, v_x_3097_);
v_x_3097_ = v___x_3103_;
v_x_3098_ = v_tail_3100_;
goto _start;
}
else
{
lean_dec(v___x_3101_);
lean_dec(v_head_3099_);
v_x_3098_ = v_tail_3100_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___redArg___boxed(lean_object* v_newState_3106_, lean_object* v_x_3107_, lean_object* v_x_3108_){
_start:
{
lean_object* v_res_3109_; 
v_res_3109_ = l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___redArg(v_newState_3106_, v_x_3107_, v_x_3108_);
lean_dec(v_newState_3106_);
return v_res_3109_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__1(lean_object* v_x_3110_, lean_object* v_newState_3111_, lean_object* v_consts_3112_, lean_object* v_st_3113_){
_start:
{
lean_object* v___x_3114_; 
v___x_3114_ = l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___redArg(v_newState_3111_, v_st_3113_, v_consts_3112_);
return v___x_3114_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__1___boxed(lean_object* v_x_3115_, lean_object* v_newState_3116_, lean_object* v_consts_3117_, lean_object* v_st_3118_){
_start:
{
lean_object* v_res_3119_; 
v_res_3119_ = l_Lean_registerEnumAttributes___redArg___lam__1(v_x_3115_, v_newState_3116_, v_consts_3117_, v_st_3118_);
lean_dec(v_newState_3116_);
lean_dec(v_x_3115_);
return v_res_3119_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__2(lean_object* v_s_3129_){
_start:
{
lean_object* v___x_3130_; lean_object* v___y_3132_; 
v___x_3130_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___lam__2___closed__3));
if (lean_obj_tag(v_s_3129_) == 0)
{
lean_object* v_size_3136_; 
v_size_3136_ = lean_ctor_get(v_s_3129_, 0);
lean_inc(v_size_3136_);
lean_dec_ref(v_s_3129_);
v___y_3132_ = v_size_3136_;
goto v___jp_3131_;
}
else
{
lean_object* v___x_3137_; 
v___x_3137_ = lean_unsigned_to_nat(0u);
v___y_3132_ = v___x_3137_;
goto v___jp_3131_;
}
v___jp_3131_:
{
lean_object* v___x_3133_; lean_object* v___x_3134_; lean_object* v___x_3135_; 
v___x_3133_ = l_Nat_reprFast(v___y_3132_);
v___x_3134_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3134_, 0, v___x_3133_);
v___x_3135_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3135_, 0, v___x_3130_);
lean_ctor_set(v___x_3135_, 1, v___x_3134_);
return v___x_3135_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg(lean_object* v_env_3138_, lean_object* v_as_3139_, size_t v_i_3140_, size_t v_stop_3141_, lean_object* v_b_3142_){
_start:
{
lean_object* v___y_3144_; uint8_t v___x_3148_; 
v___x_3148_ = lean_usize_dec_eq(v_i_3140_, v_stop_3141_);
if (v___x_3148_ == 0)
{
lean_object* v___x_3149_; lean_object* v_fst_3150_; uint8_t v___x_3151_; lean_object* v___x_3152_; uint8_t v___x_3153_; 
v___x_3149_ = lean_array_uget_borrowed(v_as_3139_, v_i_3140_);
v_fst_3150_ = lean_ctor_get(v___x_3149_, 0);
v___x_3151_ = 1;
lean_inc_ref(v_env_3138_);
v___x_3152_ = l_Lean_Environment_setExporting(v_env_3138_, v___x_3151_);
lean_inc(v_fst_3150_);
v___x_3153_ = l_Lean_Environment_contains(v___x_3152_, v_fst_3150_, v___x_3148_);
if (v___x_3153_ == 0)
{
v___y_3144_ = v_b_3142_;
goto v___jp_3143_;
}
else
{
lean_object* v___x_3154_; 
lean_inc(v___x_3149_);
v___x_3154_ = lean_array_push(v_b_3142_, v___x_3149_);
v___y_3144_ = v___x_3154_;
goto v___jp_3143_;
}
}
else
{
lean_dec_ref(v_env_3138_);
return v_b_3142_;
}
v___jp_3143_:
{
size_t v___x_3145_; size_t v___x_3146_; 
v___x_3145_ = ((size_t)1ULL);
v___x_3146_ = lean_usize_add(v_i_3140_, v___x_3145_);
v_i_3140_ = v___x_3146_;
v_b_3142_ = v___y_3144_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg___boxed(lean_object* v_env_3155_, lean_object* v_as_3156_, lean_object* v_i_3157_, lean_object* v_stop_3158_, lean_object* v_b_3159_){
_start:
{
size_t v_i_boxed_3160_; size_t v_stop_boxed_3161_; lean_object* v_res_3162_; 
v_i_boxed_3160_ = lean_unbox_usize(v_i_3157_);
lean_dec(v_i_3157_);
v_stop_boxed_3161_ = lean_unbox_usize(v_stop_3158_);
lean_dec(v_stop_3158_);
v_res_3162_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg(v_env_3155_, v_as_3156_, v_i_boxed_3160_, v_stop_boxed_3161_, v_b_3159_);
lean_dec_ref(v_as_3156_);
return v_res_3162_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__3(lean_object* v_env_3163_, lean_object* v_m_3164_){
_start:
{
lean_object* v___x_3165_; lean_object* v___x_3166_; lean_object* v___y_3168_; lean_object* v___x_3182_; lean_object* v___y_3184_; lean_object* v___y_3185_; lean_object* v___x_3187_; uint8_t v___x_3188_; 
v___x_3165_ = lean_unsigned_to_nat(0u);
v___x_3166_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___lam__2___closed__0));
v___x_3182_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1_spec__1___redArg(v___x_3166_, v_m_3164_);
v___x_3187_ = lean_array_get_size(v___x_3182_);
v___x_3188_ = lean_nat_dec_eq(v___x_3187_, v___x_3165_);
if (v___x_3188_ == 0)
{
lean_object* v___x_3189_; lean_object* v___x_3190_; lean_object* v___y_3192_; uint8_t v___x_3194_; 
v___x_3189_ = lean_unsigned_to_nat(1u);
v___x_3190_ = lean_nat_sub(v___x_3187_, v___x_3189_);
v___x_3194_ = lean_nat_dec_le(v___x_3165_, v___x_3190_);
if (v___x_3194_ == 0)
{
lean_inc(v___x_3190_);
v___y_3192_ = v___x_3190_;
goto v___jp_3191_;
}
else
{
v___y_3192_ = v___x_3165_;
goto v___jp_3191_;
}
v___jp_3191_:
{
uint8_t v___x_3193_; 
v___x_3193_ = lean_nat_dec_le(v___y_3192_, v___x_3190_);
if (v___x_3193_ == 0)
{
lean_dec(v___x_3190_);
lean_inc(v___y_3192_);
v___y_3184_ = v___y_3192_;
v___y_3185_ = v___y_3192_;
goto v___jp_3183_;
}
else
{
v___y_3184_ = v___y_3192_;
v___y_3185_ = v___x_3190_;
goto v___jp_3183_;
}
}
}
else
{
v___y_3168_ = v___x_3182_;
goto v___jp_3167_;
}
v___jp_3167_:
{
lean_object* v___x_3169_; uint8_t v___x_3170_; 
v___x_3169_ = lean_array_get_size(v___y_3168_);
v___x_3170_ = lean_nat_dec_lt(v___x_3165_, v___x_3169_);
if (v___x_3170_ == 0)
{
lean_object* v___x_3171_; 
lean_dec_ref(v_env_3163_);
v___x_3171_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3171_, 0, v___x_3166_);
lean_ctor_set(v___x_3171_, 1, v___x_3166_);
lean_ctor_set(v___x_3171_, 2, v___y_3168_);
return v___x_3171_;
}
else
{
uint8_t v___x_3172_; 
v___x_3172_ = lean_nat_dec_le(v___x_3169_, v___x_3169_);
if (v___x_3172_ == 0)
{
if (v___x_3170_ == 0)
{
lean_object* v___x_3173_; 
lean_dec_ref(v_env_3163_);
v___x_3173_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3173_, 0, v___x_3166_);
lean_ctor_set(v___x_3173_, 1, v___x_3166_);
lean_ctor_set(v___x_3173_, 2, v___y_3168_);
return v___x_3173_;
}
else
{
size_t v___x_3174_; size_t v___x_3175_; lean_object* v___x_3176_; lean_object* v___x_3177_; 
v___x_3174_ = ((size_t)0ULL);
v___x_3175_ = lean_usize_of_nat(v___x_3169_);
v___x_3176_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg(v_env_3163_, v___y_3168_, v___x_3174_, v___x_3175_, v___x_3166_);
lean_inc_ref(v___x_3176_);
v___x_3177_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3177_, 0, v___x_3176_);
lean_ctor_set(v___x_3177_, 1, v___x_3176_);
lean_ctor_set(v___x_3177_, 2, v___y_3168_);
return v___x_3177_;
}
}
else
{
size_t v___x_3178_; size_t v___x_3179_; lean_object* v___x_3180_; lean_object* v___x_3181_; 
v___x_3178_ = ((size_t)0ULL);
v___x_3179_ = lean_usize_of_nat(v___x_3169_);
v___x_3180_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg(v_env_3163_, v___y_3168_, v___x_3178_, v___x_3179_, v___x_3166_);
lean_inc_ref(v___x_3180_);
v___x_3181_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3181_, 0, v___x_3180_);
lean_ctor_set(v___x_3181_, 1, v___x_3180_);
lean_ctor_set(v___x_3181_, 2, v___y_3168_);
return v___x_3181_;
}
}
}
v___jp_3183_:
{
lean_object* v___x_3186_; 
v___x_3186_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2___redArg(v___x_3182_, v___y_3184_, v___y_3185_);
lean_dec(v___y_3185_);
v___y_3168_ = v___x_3186_;
goto v___jp_3167_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__3___boxed(lean_object* v_env_3195_, lean_object* v_m_3196_){
_start:
{
lean_object* v_res_3197_; 
v_res_3197_ = l_Lean_registerEnumAttributes___redArg___lam__3(v_env_3195_, v_m_3196_);
lean_dec(v_m_3196_);
return v_res_3197_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__4(lean_object* v_s_3198_, lean_object* v_p_3199_){
_start:
{
lean_object* v_fst_3200_; lean_object* v_snd_3201_; lean_object* v___x_3202_; 
v_fst_3200_ = lean_ctor_get(v_p_3199_, 0);
lean_inc(v_fst_3200_);
v_snd_3201_ = lean_ctor_get(v_p_3199_, 1);
lean_inc(v_snd_3201_);
lean_dec_ref(v_p_3199_);
v___x_3202_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_3200_, v_snd_3201_, v_s_3198_);
return v___x_3202_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__6(lean_object* v___x_3203_, lean_object* v_x_3204_, lean_object* v_x_3205_){
_start:
{
lean_object* v___x_3207_; 
v___x_3207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3207_, 0, v___x_3203_);
return v___x_3207_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__6___boxed(lean_object* v___x_3208_, lean_object* v_x_3209_, lean_object* v_x_3210_, lean_object* v___y_3211_){
_start:
{
lean_object* v_res_3212_; 
v_res_3212_ = l_Lean_registerEnumAttributes___redArg___lam__6(v___x_3208_, v_x_3209_, v_x_3210_);
lean_dec_ref(v_x_3210_);
lean_dec_ref(v_x_3209_);
return v_res_3212_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_registerEnumAttributes_spec__3(lean_object* v_as_3213_){
_start:
{
if (lean_obj_tag(v_as_3213_) == 0)
{
lean_object* v___x_3215_; lean_object* v___x_3216_; 
v___x_3215_ = lean_box(0);
v___x_3216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3216_, 0, v___x_3215_);
return v___x_3216_;
}
else
{
lean_object* v_head_3217_; lean_object* v_tail_3218_; lean_object* v___x_3219_; 
v_head_3217_ = lean_ctor_get(v_as_3213_, 0);
lean_inc(v_head_3217_);
v_tail_3218_ = lean_ctor_get(v_as_3213_, 1);
lean_inc(v_tail_3218_);
lean_dec_ref(v_as_3213_);
v___x_3219_ = l_Lean_registerBuiltinAttribute(v_head_3217_);
if (lean_obj_tag(v___x_3219_) == 0)
{
lean_dec_ref(v___x_3219_);
v_as_3213_ = v_tail_3218_;
goto _start;
}
else
{
lean_dec(v_tail_3218_);
return v___x_3219_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_registerEnumAttributes_spec__3___boxed(lean_object* v_as_3221_, lean_object* v___y_3222_){
_start:
{
lean_object* v_res_3223_; 
v_res_3223_ = l_List_forM___at___00Lean_registerEnumAttributes_spec__3(v_as_3221_);
return v_res_3223_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__1(lean_object* v_validate_3224_, lean_object* v_snd_3225_, lean_object* v_a_3226_, lean_object* v_fst_3227_, lean_object* v_decl_3228_, lean_object* v_stx_3229_, uint8_t v_kind_3230_, lean_object* v___y_3231_, lean_object* v___y_3232_){
_start:
{
lean_object* v___y_3235_; lean_object* v___y_3236_; lean_object* v___y_3271_; lean_object* v___y_3272_; lean_object* v___x_3277_; 
v___x_3277_ = l_Lean_Attribute_Builtin_ensureNoArgs(v_stx_3229_, v___y_3231_, v___y_3232_);
if (lean_obj_tag(v___x_3277_) == 0)
{
uint8_t v___x_3278_; uint8_t v___x_3279_; 
lean_dec_ref(v___x_3277_);
v___x_3278_ = 0;
v___x_3279_ = l_Lean_instBEqAttributeKind_beq(v_kind_3230_, v___x_3278_);
if (v___x_3279_ == 0)
{
lean_object* v___x_3280_; 
lean_dec(v_decl_3228_);
lean_dec_ref(v_a_3226_);
lean_dec(v_snd_3225_);
lean_dec_ref(v_validate_3224_);
v___x_3280_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg(v_fst_3227_, v_kind_3230_, v___y_3231_, v___y_3232_);
return v___x_3280_;
}
else
{
v___y_3271_ = v___y_3231_;
v___y_3272_ = v___y_3232_;
goto v___jp_3270_;
}
}
else
{
lean_dec(v_decl_3228_);
lean_dec(v_fst_3227_);
lean_dec_ref(v_a_3226_);
lean_dec(v_snd_3225_);
lean_dec_ref(v_validate_3224_);
return v___x_3277_;
}
v___jp_3234_:
{
lean_object* v___x_3237_; 
lean_inc(v___y_3236_);
lean_inc_ref(v___y_3235_);
lean_inc(v_snd_3225_);
lean_inc(v_decl_3228_);
v___x_3237_ = lean_apply_5(v_validate_3224_, v_decl_3228_, v_snd_3225_, v___y_3235_, v___y_3236_, lean_box(0));
if (lean_obj_tag(v___x_3237_) == 0)
{
lean_object* v___x_3239_; uint8_t v_isShared_3240_; uint8_t v_isSharedCheck_3268_; 
v_isSharedCheck_3268_ = !lean_is_exclusive(v___x_3237_);
if (v_isSharedCheck_3268_ == 0)
{
lean_object* v_unused_3269_; 
v_unused_3269_ = lean_ctor_get(v___x_3237_, 0);
lean_dec(v_unused_3269_);
v___x_3239_ = v___x_3237_;
v_isShared_3240_ = v_isSharedCheck_3268_;
goto v_resetjp_3238_;
}
else
{
lean_dec(v___x_3237_);
v___x_3239_ = lean_box(0);
v_isShared_3240_ = v_isSharedCheck_3268_;
goto v_resetjp_3238_;
}
v_resetjp_3238_:
{
lean_object* v___x_3241_; lean_object* v_toEnvExtension_3242_; lean_object* v_env_3243_; lean_object* v_nextMacroScope_3244_; lean_object* v_ngen_3245_; lean_object* v_auxDeclNGen_3246_; lean_object* v_traceState_3247_; lean_object* v_messages_3248_; lean_object* v_infoState_3249_; lean_object* v_snapshotTasks_3250_; lean_object* v___x_3252_; uint8_t v_isShared_3253_; uint8_t v_isSharedCheck_3266_; 
v___x_3241_ = lean_st_ref_take(v___y_3236_);
v_toEnvExtension_3242_ = lean_ctor_get(v_a_3226_, 0);
v_env_3243_ = lean_ctor_get(v___x_3241_, 0);
v_nextMacroScope_3244_ = lean_ctor_get(v___x_3241_, 1);
v_ngen_3245_ = lean_ctor_get(v___x_3241_, 2);
v_auxDeclNGen_3246_ = lean_ctor_get(v___x_3241_, 3);
v_traceState_3247_ = lean_ctor_get(v___x_3241_, 4);
v_messages_3248_ = lean_ctor_get(v___x_3241_, 6);
v_infoState_3249_ = lean_ctor_get(v___x_3241_, 7);
v_snapshotTasks_3250_ = lean_ctor_get(v___x_3241_, 8);
v_isSharedCheck_3266_ = !lean_is_exclusive(v___x_3241_);
if (v_isSharedCheck_3266_ == 0)
{
lean_object* v_unused_3267_; 
v_unused_3267_ = lean_ctor_get(v___x_3241_, 5);
lean_dec(v_unused_3267_);
v___x_3252_ = v___x_3241_;
v_isShared_3253_ = v_isSharedCheck_3266_;
goto v_resetjp_3251_;
}
else
{
lean_inc(v_snapshotTasks_3250_);
lean_inc(v_infoState_3249_);
lean_inc(v_messages_3248_);
lean_inc(v_traceState_3247_);
lean_inc(v_auxDeclNGen_3246_);
lean_inc(v_ngen_3245_);
lean_inc(v_nextMacroScope_3244_);
lean_inc(v_env_3243_);
lean_dec(v___x_3241_);
v___x_3252_ = lean_box(0);
v_isShared_3253_ = v_isSharedCheck_3266_;
goto v_resetjp_3251_;
}
v_resetjp_3251_:
{
lean_object* v_asyncMode_3254_; lean_object* v___x_3255_; lean_object* v___x_3256_; lean_object* v___x_3257_; lean_object* v___x_3259_; 
v_asyncMode_3254_ = lean_ctor_get(v_toEnvExtension_3242_, 2);
lean_inc(v_asyncMode_3254_);
lean_inc(v_decl_3228_);
v___x_3255_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3255_, 0, v_decl_3228_);
lean_ctor_set(v___x_3255_, 1, v_snd_3225_);
v___x_3256_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_a_3226_, v_env_3243_, v___x_3255_, v_asyncMode_3254_, v_decl_3228_);
lean_dec(v_asyncMode_3254_);
v___x_3257_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2);
if (v_isShared_3253_ == 0)
{
lean_ctor_set(v___x_3252_, 5, v___x_3257_);
lean_ctor_set(v___x_3252_, 0, v___x_3256_);
v___x_3259_ = v___x_3252_;
goto v_reusejp_3258_;
}
else
{
lean_object* v_reuseFailAlloc_3265_; 
v_reuseFailAlloc_3265_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3265_, 0, v___x_3256_);
lean_ctor_set(v_reuseFailAlloc_3265_, 1, v_nextMacroScope_3244_);
lean_ctor_set(v_reuseFailAlloc_3265_, 2, v_ngen_3245_);
lean_ctor_set(v_reuseFailAlloc_3265_, 3, v_auxDeclNGen_3246_);
lean_ctor_set(v_reuseFailAlloc_3265_, 4, v_traceState_3247_);
lean_ctor_set(v_reuseFailAlloc_3265_, 5, v___x_3257_);
lean_ctor_set(v_reuseFailAlloc_3265_, 6, v_messages_3248_);
lean_ctor_set(v_reuseFailAlloc_3265_, 7, v_infoState_3249_);
lean_ctor_set(v_reuseFailAlloc_3265_, 8, v_snapshotTasks_3250_);
v___x_3259_ = v_reuseFailAlloc_3265_;
goto v_reusejp_3258_;
}
v_reusejp_3258_:
{
lean_object* v___x_3260_; lean_object* v___x_3261_; lean_object* v___x_3263_; 
v___x_3260_ = lean_st_ref_set(v___y_3236_, v___x_3259_);
v___x_3261_ = lean_box(0);
if (v_isShared_3240_ == 0)
{
lean_ctor_set(v___x_3239_, 0, v___x_3261_);
v___x_3263_ = v___x_3239_;
goto v_reusejp_3262_;
}
else
{
lean_object* v_reuseFailAlloc_3264_; 
v_reuseFailAlloc_3264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3264_, 0, v___x_3261_);
v___x_3263_ = v_reuseFailAlloc_3264_;
goto v_reusejp_3262_;
}
v_reusejp_3262_:
{
return v___x_3263_;
}
}
}
}
}
else
{
lean_dec(v_decl_3228_);
lean_dec_ref(v_a_3226_);
lean_dec(v_snd_3225_);
return v___x_3237_;
}
}
v___jp_3270_:
{
lean_object* v___x_3273_; lean_object* v_env_3274_; lean_object* v___x_3275_; 
v___x_3273_ = lean_st_ref_get(v___y_3272_);
v_env_3274_ = lean_ctor_get(v___x_3273_, 0);
lean_inc_ref(v_env_3274_);
lean_dec(v___x_3273_);
v___x_3275_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3274_, v_decl_3228_);
lean_dec_ref(v_env_3274_);
if (lean_obj_tag(v___x_3275_) == 0)
{
lean_dec(v_fst_3227_);
v___y_3235_ = v___y_3271_;
v___y_3236_ = v___y_3272_;
goto v___jp_3234_;
}
else
{
lean_object* v___x_3276_; 
lean_dec_ref(v___x_3275_);
lean_dec_ref(v_a_3226_);
lean_dec(v_snd_3225_);
lean_dec_ref(v_validate_3224_);
v___x_3276_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg(v_fst_3227_, v_decl_3228_, v___y_3271_, v___y_3272_);
return v___x_3276_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__1___boxed(lean_object* v_validate_3281_, lean_object* v_snd_3282_, lean_object* v_a_3283_, lean_object* v_fst_3284_, lean_object* v_decl_3285_, lean_object* v_stx_3286_, lean_object* v_kind_3287_, lean_object* v___y_3288_, lean_object* v___y_3289_, lean_object* v___y_3290_){
_start:
{
uint8_t v_kind_boxed_3291_; lean_object* v_res_3292_; 
v_kind_boxed_3291_ = lean_unbox(v_kind_3287_);
v_res_3292_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__1(v_validate_3281_, v_snd_3282_, v_a_3283_, v_fst_3284_, v_decl_3285_, v_stx_3286_, v_kind_boxed_3291_, v___y_3288_, v___y_3289_);
lean_dec(v___y_3289_);
lean_dec_ref(v___y_3288_);
return v_res_3292_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__0(lean_object* v_fst_3293_, lean_object* v_decl_3294_, lean_object* v___y_3295_, lean_object* v___y_3296_){
_start:
{
lean_object* v___x_3298_; lean_object* v___x_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; 
v___x_3298_ = lean_obj_once(&l_Lean_registerTagAttribute___lam__6___closed__1, &l_Lean_registerTagAttribute___lam__6___closed__1_once, _init_l_Lean_registerTagAttribute___lam__6___closed__1);
v___x_3299_ = l_Lean_MessageData_ofName(v_fst_3293_);
v___x_3300_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3300_, 0, v___x_3298_);
lean_ctor_set(v___x_3300_, 1, v___x_3299_);
v___x_3301_ = lean_obj_once(&l_Lean_registerTagAttribute___lam__6___closed__3, &l_Lean_registerTagAttribute___lam__6___closed__3_once, _init_l_Lean_registerTagAttribute___lam__6___closed__3);
v___x_3302_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3302_, 0, v___x_3300_);
lean_ctor_set(v___x_3302_, 1, v___x_3301_);
v___x_3303_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0_spec__0___redArg(v___x_3302_, v___y_3295_, v___y_3296_);
return v___x_3303_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__0___boxed(lean_object* v_fst_3304_, lean_object* v_decl_3305_, lean_object* v___y_3306_, lean_object* v___y_3307_, lean_object* v___y_3308_){
_start:
{
lean_object* v_res_3309_; 
v_res_3309_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__0(v_fst_3304_, v_decl_3305_, v___y_3306_, v___y_3307_);
lean_dec(v___y_3307_);
lean_dec_ref(v___y_3306_);
lean_dec(v_decl_3305_);
return v_res_3309_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg(lean_object* v_validate_3310_, lean_object* v_a_3311_, lean_object* v_ref_3312_, uint8_t v_applicationTime_3313_, lean_object* v_a_3314_, lean_object* v_a_3315_){
_start:
{
if (lean_obj_tag(v_a_3314_) == 0)
{
lean_object* v___x_3316_; 
lean_dec(v_ref_3312_);
lean_dec_ref(v_a_3311_);
lean_dec_ref(v_validate_3310_);
v___x_3316_ = l_List_reverse___redArg(v_a_3315_);
return v___x_3316_;
}
else
{
lean_object* v_head_3317_; lean_object* v_snd_3318_; lean_object* v_tail_3319_; lean_object* v___x_3321_; uint8_t v_isShared_3322_; uint8_t v_isSharedCheck_3334_; 
v_head_3317_ = lean_ctor_get(v_a_3314_, 0);
lean_inc(v_head_3317_);
v_snd_3318_ = lean_ctor_get(v_head_3317_, 1);
lean_inc(v_snd_3318_);
v_tail_3319_ = lean_ctor_get(v_a_3314_, 1);
v_isSharedCheck_3334_ = !lean_is_exclusive(v_a_3314_);
if (v_isSharedCheck_3334_ == 0)
{
lean_object* v_unused_3335_; 
v_unused_3335_ = lean_ctor_get(v_a_3314_, 0);
lean_dec(v_unused_3335_);
v___x_3321_ = v_a_3314_;
v_isShared_3322_ = v_isSharedCheck_3334_;
goto v_resetjp_3320_;
}
else
{
lean_inc(v_tail_3319_);
lean_dec(v_a_3314_);
v___x_3321_ = lean_box(0);
v_isShared_3322_ = v_isSharedCheck_3334_;
goto v_resetjp_3320_;
}
v_resetjp_3320_:
{
lean_object* v_fst_3323_; lean_object* v_fst_3324_; lean_object* v_snd_3325_; lean_object* v___f_3326_; lean_object* v___f_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; lean_object* v___x_3331_; 
v_fst_3323_ = lean_ctor_get(v_head_3317_, 0);
lean_inc_n(v_fst_3323_, 3);
lean_dec(v_head_3317_);
v_fst_3324_ = lean_ctor_get(v_snd_3318_, 0);
lean_inc(v_fst_3324_);
v_snd_3325_ = lean_ctor_get(v_snd_3318_, 1);
lean_inc(v_snd_3325_);
lean_dec(v_snd_3318_);
v___f_3326_ = lean_alloc_closure((void*)(l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__0___boxed), 5, 1);
lean_closure_set(v___f_3326_, 0, v_fst_3323_);
lean_inc_ref(v_a_3311_);
lean_inc_ref(v_validate_3310_);
v___f_3327_ = lean_alloc_closure((void*)(l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__1___boxed), 10, 4);
lean_closure_set(v___f_3327_, 0, v_validate_3310_);
lean_closure_set(v___f_3327_, 1, v_snd_3325_);
lean_closure_set(v___f_3327_, 2, v_a_3311_);
lean_closure_set(v___f_3327_, 3, v_fst_3323_);
lean_inc(v_ref_3312_);
v___x_3328_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_3328_, 0, v_ref_3312_);
lean_ctor_set(v___x_3328_, 1, v_fst_3323_);
lean_ctor_set(v___x_3328_, 2, v_fst_3324_);
lean_ctor_set_uint8(v___x_3328_, sizeof(void*)*3, v_applicationTime_3313_);
v___x_3329_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3329_, 0, v___x_3328_);
lean_ctor_set(v___x_3329_, 1, v___f_3327_);
lean_ctor_set(v___x_3329_, 2, v___f_3326_);
if (v_isShared_3322_ == 0)
{
lean_ctor_set(v___x_3321_, 1, v_a_3315_);
lean_ctor_set(v___x_3321_, 0, v___x_3329_);
v___x_3331_ = v___x_3321_;
goto v_reusejp_3330_;
}
else
{
lean_object* v_reuseFailAlloc_3333_; 
v_reuseFailAlloc_3333_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3333_, 0, v___x_3329_);
lean_ctor_set(v_reuseFailAlloc_3333_, 1, v_a_3315_);
v___x_3331_ = v_reuseFailAlloc_3333_;
goto v_reusejp_3330_;
}
v_reusejp_3330_:
{
v_a_3314_ = v_tail_3319_;
v_a_3315_ = v___x_3331_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___boxed(lean_object* v_validate_3336_, lean_object* v_a_3337_, lean_object* v_ref_3338_, lean_object* v_applicationTime_3339_, lean_object* v_a_3340_, lean_object* v_a_3341_){
_start:
{
uint8_t v_applicationTime_boxed_3342_; lean_object* v_res_3343_; 
v_applicationTime_boxed_3342_ = lean_unbox(v_applicationTime_3339_);
v_res_3343_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg(v_validate_3336_, v_a_3337_, v_ref_3338_, v_applicationTime_boxed_3342_, v_a_3340_, v_a_3341_);
return v_res_3343_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg(lean_object* v_attrDescrs_3357_, lean_object* v_validate_3358_, uint8_t v_applicationTime_3359_, lean_object* v_ref_3360_){
_start:
{
lean_object* v___f_3362_; lean_object* v___f_3363_; lean_object* v___f_3364_; lean_object* v___f_3365_; lean_object* v___f_3366_; lean_object* v___f_3367_; lean_object* v___x_3368_; lean_object* v___x_3369_; lean_object* v___x_3370_; lean_object* v___x_3371_; lean_object* v___x_3372_; 
v___f_3362_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__0));
v___f_3363_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__2));
v___f_3364_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__3));
v___f_3365_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__4));
v___f_3366_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__5));
v___f_3367_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__6));
v___x_3368_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__7));
v___x_3369_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__8));
lean_inc(v_ref_3360_);
v___x_3370_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_3370_, 0, v_ref_3360_);
lean_ctor_set(v___x_3370_, 1, v___f_3366_);
lean_ctor_set(v___x_3370_, 2, v___f_3367_);
lean_ctor_set(v___x_3370_, 3, v___f_3365_);
lean_ctor_set(v___x_3370_, 4, v___f_3364_);
lean_ctor_set(v___x_3370_, 5, v___f_3363_);
lean_ctor_set(v___x_3370_, 6, v___x_3368_);
lean_ctor_set(v___x_3370_, 7, v___x_3369_);
v___x_3371_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3371_, 0, v___x_3370_);
lean_ctor_set(v___x_3371_, 1, v___f_3362_);
v___x_3372_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_3371_);
if (lean_obj_tag(v___x_3372_) == 0)
{
lean_object* v_a_3373_; lean_object* v___x_3374_; lean_object* v___x_3375_; lean_object* v___x_3376_; 
v_a_3373_ = lean_ctor_get(v___x_3372_, 0);
lean_inc_n(v_a_3373_, 2);
lean_dec_ref(v___x_3372_);
v___x_3374_ = lean_box(0);
v___x_3375_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg(v_validate_3358_, v_a_3373_, v_ref_3360_, v_applicationTime_3359_, v_attrDescrs_3357_, v___x_3374_);
lean_inc(v___x_3375_);
v___x_3376_ = l_List_forM___at___00Lean_registerEnumAttributes_spec__3(v___x_3375_);
if (lean_obj_tag(v___x_3376_) == 0)
{
lean_object* v___x_3378_; uint8_t v_isShared_3379_; uint8_t v_isSharedCheck_3384_; 
v_isSharedCheck_3384_ = !lean_is_exclusive(v___x_3376_);
if (v_isSharedCheck_3384_ == 0)
{
lean_object* v_unused_3385_; 
v_unused_3385_ = lean_ctor_get(v___x_3376_, 0);
lean_dec(v_unused_3385_);
v___x_3378_ = v___x_3376_;
v_isShared_3379_ = v_isSharedCheck_3384_;
goto v_resetjp_3377_;
}
else
{
lean_dec(v___x_3376_);
v___x_3378_ = lean_box(0);
v_isShared_3379_ = v_isSharedCheck_3384_;
goto v_resetjp_3377_;
}
v_resetjp_3377_:
{
lean_object* v___x_3380_; lean_object* v___x_3382_; 
v___x_3380_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3380_, 0, v___x_3375_);
lean_ctor_set(v___x_3380_, 1, v_a_3373_);
if (v_isShared_3379_ == 0)
{
lean_ctor_set(v___x_3378_, 0, v___x_3380_);
v___x_3382_ = v___x_3378_;
goto v_reusejp_3381_;
}
else
{
lean_object* v_reuseFailAlloc_3383_; 
v_reuseFailAlloc_3383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3383_, 0, v___x_3380_);
v___x_3382_ = v_reuseFailAlloc_3383_;
goto v_reusejp_3381_;
}
v_reusejp_3381_:
{
return v___x_3382_;
}
}
}
else
{
lean_object* v_a_3386_; lean_object* v___x_3388_; uint8_t v_isShared_3389_; uint8_t v_isSharedCheck_3393_; 
lean_dec(v___x_3375_);
lean_dec(v_a_3373_);
v_a_3386_ = lean_ctor_get(v___x_3376_, 0);
v_isSharedCheck_3393_ = !lean_is_exclusive(v___x_3376_);
if (v_isSharedCheck_3393_ == 0)
{
v___x_3388_ = v___x_3376_;
v_isShared_3389_ = v_isSharedCheck_3393_;
goto v_resetjp_3387_;
}
else
{
lean_inc(v_a_3386_);
lean_dec(v___x_3376_);
v___x_3388_ = lean_box(0);
v_isShared_3389_ = v_isSharedCheck_3393_;
goto v_resetjp_3387_;
}
v_resetjp_3387_:
{
lean_object* v___x_3391_; 
if (v_isShared_3389_ == 0)
{
v___x_3391_ = v___x_3388_;
goto v_reusejp_3390_;
}
else
{
lean_object* v_reuseFailAlloc_3392_; 
v_reuseFailAlloc_3392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3392_, 0, v_a_3386_);
v___x_3391_ = v_reuseFailAlloc_3392_;
goto v_reusejp_3390_;
}
v_reusejp_3390_:
{
return v___x_3391_;
}
}
}
}
else
{
lean_object* v_a_3394_; lean_object* v___x_3396_; uint8_t v_isShared_3397_; uint8_t v_isSharedCheck_3401_; 
lean_dec(v_ref_3360_);
lean_dec_ref(v_validate_3358_);
lean_dec(v_attrDescrs_3357_);
v_a_3394_ = lean_ctor_get(v___x_3372_, 0);
v_isSharedCheck_3401_ = !lean_is_exclusive(v___x_3372_);
if (v_isSharedCheck_3401_ == 0)
{
v___x_3396_ = v___x_3372_;
v_isShared_3397_ = v_isSharedCheck_3401_;
goto v_resetjp_3395_;
}
else
{
lean_inc(v_a_3394_);
lean_dec(v___x_3372_);
v___x_3396_ = lean_box(0);
v_isShared_3397_ = v_isSharedCheck_3401_;
goto v_resetjp_3395_;
}
v_resetjp_3395_:
{
lean_object* v___x_3399_; 
if (v_isShared_3397_ == 0)
{
v___x_3399_ = v___x_3396_;
goto v_reusejp_3398_;
}
else
{
lean_object* v_reuseFailAlloc_3400_; 
v_reuseFailAlloc_3400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3400_, 0, v_a_3394_);
v___x_3399_ = v_reuseFailAlloc_3400_;
goto v_reusejp_3398_;
}
v_reusejp_3398_:
{
return v___x_3399_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___boxed(lean_object* v_attrDescrs_3402_, lean_object* v_validate_3403_, lean_object* v_applicationTime_3404_, lean_object* v_ref_3405_, lean_object* v_a_3406_){
_start:
{
uint8_t v_applicationTime_boxed_3407_; lean_object* v_res_3408_; 
v_applicationTime_boxed_3407_ = lean_unbox(v_applicationTime_3404_);
v_res_3408_ = l_Lean_registerEnumAttributes___redArg(v_attrDescrs_3402_, v_validate_3403_, v_applicationTime_boxed_3407_, v_ref_3405_);
return v_res_3408_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes(lean_object* v_00_u03b1_3409_, lean_object* v_attrDescrs_3410_, lean_object* v_validate_3411_, uint8_t v_applicationTime_3412_, lean_object* v_ref_3413_){
_start:
{
lean_object* v___x_3415_; 
v___x_3415_ = l_Lean_registerEnumAttributes___redArg(v_attrDescrs_3410_, v_validate_3411_, v_applicationTime_3412_, v_ref_3413_);
return v___x_3415_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___boxed(lean_object* v_00_u03b1_3416_, lean_object* v_attrDescrs_3417_, lean_object* v_validate_3418_, lean_object* v_applicationTime_3419_, lean_object* v_ref_3420_, lean_object* v_a_3421_){
_start:
{
uint8_t v_applicationTime_boxed_3422_; lean_object* v_res_3423_; 
v_applicationTime_boxed_3422_ = lean_unbox(v_applicationTime_3419_);
v_res_3423_ = l_Lean_registerEnumAttributes(v_00_u03b1_3416_, v_attrDescrs_3417_, v_validate_3418_, v_applicationTime_boxed_3422_, v_ref_3420_);
return v_res_3423_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0(lean_object* v_00_u03b1_3424_, lean_object* v_env_3425_, lean_object* v_as_3426_, size_t v_i_3427_, size_t v_stop_3428_, lean_object* v_b_3429_){
_start:
{
lean_object* v___x_3430_; 
v___x_3430_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg(v_env_3425_, v_as_3426_, v_i_3427_, v_stop_3428_, v_b_3429_);
return v___x_3430_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___boxed(lean_object* v_00_u03b1_3431_, lean_object* v_env_3432_, lean_object* v_as_3433_, lean_object* v_i_3434_, lean_object* v_stop_3435_, lean_object* v_b_3436_){
_start:
{
size_t v_i_boxed_3437_; size_t v_stop_boxed_3438_; lean_object* v_res_3439_; 
v_i_boxed_3437_ = lean_unbox_usize(v_i_3434_);
lean_dec(v_i_3434_);
v_stop_boxed_3438_ = lean_unbox_usize(v_stop_3435_);
lean_dec(v_stop_3435_);
v_res_3439_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0(v_00_u03b1_3431_, v_env_3432_, v_as_3433_, v_i_boxed_3437_, v_stop_boxed_3438_, v_b_3436_);
lean_dec_ref(v_as_3433_);
return v_res_3439_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerEnumAttributes_spec__1(lean_object* v_00_u03b1_3440_, lean_object* v_newState_3441_, lean_object* v_x_3442_, lean_object* v_x_3443_){
_start:
{
lean_object* v___x_3444_; 
v___x_3444_ = l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___redArg(v_newState_3441_, v_x_3442_, v_x_3443_);
return v___x_3444_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___boxed(lean_object* v_00_u03b1_3445_, lean_object* v_newState_3446_, lean_object* v_x_3447_, lean_object* v_x_3448_){
_start:
{
lean_object* v_res_3449_; 
v_res_3449_ = l_List_foldl___at___00Lean_registerEnumAttributes_spec__1(v_00_u03b1_3445_, v_newState_3446_, v_x_3447_, v_x_3448_);
lean_dec(v_newState_3446_);
return v_res_3449_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2(lean_object* v_00_u03b1_3450_, lean_object* v_validate_3451_, lean_object* v_a_3452_, lean_object* v_ref_3453_, uint8_t v_applicationTime_3454_, lean_object* v_a_3455_, lean_object* v_a_3456_){
_start:
{
lean_object* v___x_3457_; 
v___x_3457_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg(v_validate_3451_, v_a_3452_, v_ref_3453_, v_applicationTime_3454_, v_a_3455_, v_a_3456_);
return v___x_3457_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___boxed(lean_object* v_00_u03b1_3458_, lean_object* v_validate_3459_, lean_object* v_a_3460_, lean_object* v_ref_3461_, lean_object* v_applicationTime_3462_, lean_object* v_a_3463_, lean_object* v_a_3464_){
_start:
{
uint8_t v_applicationTime_boxed_3465_; lean_object* v_res_3466_; 
v_applicationTime_boxed_3465_ = lean_unbox(v_applicationTime_3462_);
v_res_3466_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2(v_00_u03b1_3458_, v_validate_3459_, v_a_3460_, v_ref_3461_, v_applicationTime_boxed_3465_, v_a_3463_, v_a_3464_);
return v_res_3466_;
}
}
LEAN_EXPORT lean_object* l_Lean_EnumAttributes_getValue___redArg(lean_object* v_inst_3467_, lean_object* v_attr_3468_, lean_object* v_env_3469_, lean_object* v_decl_3470_){
_start:
{
lean_object* v___x_3471_; lean_object* v___x_3472_; 
v___x_3471_ = lean_box(1);
v___x_3472_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3469_, v_decl_3470_);
if (lean_obj_tag(v___x_3472_) == 0)
{
lean_object* v_ext_3473_; lean_object* v_toEnvExtension_3474_; lean_object* v_asyncMode_3475_; lean_object* v___x_3476_; lean_object* v___x_3477_; 
lean_dec(v_inst_3467_);
v_ext_3473_ = lean_ctor_get(v_attr_3468_, 1);
lean_inc_ref(v_ext_3473_);
lean_dec_ref(v_attr_3468_);
v_toEnvExtension_3474_ = lean_ctor_get(v_ext_3473_, 0);
v_asyncMode_3475_ = lean_ctor_get(v_toEnvExtension_3474_, 2);
lean_inc(v_asyncMode_3475_);
lean_inc(v_decl_3470_);
v___x_3476_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3471_, v_ext_3473_, v_env_3469_, v_asyncMode_3475_, v_decl_3470_);
lean_dec(v_asyncMode_3475_);
lean_dec_ref(v_ext_3473_);
v___x_3477_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_3476_, v_decl_3470_);
lean_dec(v_decl_3470_);
lean_dec(v___x_3476_);
return v___x_3477_;
}
else
{
lean_object* v_val_3478_; lean_object* v_ext_3479_; lean_object* v___x_3481_; uint8_t v_isShared_3482_; uint8_t v_isSharedCheck_3509_; 
v_val_3478_ = lean_ctor_get(v___x_3472_, 0);
lean_inc(v_val_3478_);
lean_dec_ref(v___x_3472_);
v_ext_3479_ = lean_ctor_get(v_attr_3468_, 1);
v_isSharedCheck_3509_ = !lean_is_exclusive(v_attr_3468_);
if (v_isSharedCheck_3509_ == 0)
{
lean_object* v_unused_3510_; 
v_unused_3510_ = lean_ctor_get(v_attr_3468_, 0);
lean_dec(v_unused_3510_);
v___x_3481_ = v_attr_3468_;
v_isShared_3482_ = v_isSharedCheck_3509_;
goto v_resetjp_3480_;
}
else
{
lean_inc(v_ext_3479_);
lean_dec(v_attr_3468_);
v___x_3481_ = lean_box(0);
v_isShared_3482_ = v_isSharedCheck_3509_;
goto v_resetjp_3480_;
}
v_resetjp_3480_:
{
uint8_t v___x_3483_; lean_object* v___x_3484_; lean_object* v___x_3485_; lean_object* v___x_3486_; uint8_t v___x_3487_; 
v___x_3483_ = 0;
v___x_3484_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_3471_, v_ext_3479_, v_env_3469_, v_val_3478_, v___x_3483_);
lean_dec(v_val_3478_);
lean_dec_ref(v_env_3469_);
lean_dec_ref(v_ext_3479_);
v___x_3485_ = lean_unsigned_to_nat(0u);
v___x_3486_ = lean_array_get_size(v___x_3484_);
v___x_3487_ = lean_nat_dec_lt(v___x_3485_, v___x_3486_);
if (v___x_3487_ == 0)
{
lean_object* v___x_3488_; 
lean_dec_ref(v___x_3484_);
lean_del_object(v___x_3481_);
lean_dec(v_decl_3470_);
lean_dec(v_inst_3467_);
v___x_3488_ = lean_box(0);
return v___x_3488_;
}
else
{
lean_object* v___x_3489_; lean_object* v___x_3490_; uint8_t v___x_3491_; 
v___x_3489_ = lean_unsigned_to_nat(1u);
v___x_3490_ = lean_nat_sub(v___x_3486_, v___x_3489_);
v___x_3491_ = lean_nat_dec_le(v___x_3485_, v___x_3490_);
if (v___x_3491_ == 0)
{
lean_object* v___x_3492_; 
lean_dec(v___x_3490_);
lean_dec_ref(v___x_3484_);
lean_del_object(v___x_3481_);
lean_dec(v_decl_3470_);
lean_dec(v_inst_3467_);
v___x_3492_ = lean_box(0);
return v___x_3492_;
}
else
{
lean_object* v___f_3493_; lean_object* v___x_3495_; 
v___f_3493_ = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2___redArg___closed__0));
if (v_isShared_3482_ == 0)
{
lean_ctor_set(v___x_3481_, 1, v_inst_3467_);
lean_ctor_set(v___x_3481_, 0, v_decl_3470_);
v___x_3495_ = v___x_3481_;
goto v_reusejp_3494_;
}
else
{
lean_object* v_reuseFailAlloc_3508_; 
v_reuseFailAlloc_3508_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3508_, 0, v_decl_3470_);
lean_ctor_set(v_reuseFailAlloc_3508_, 1, v_inst_3467_);
v___x_3495_ = v_reuseFailAlloc_3508_;
goto v_reusejp_3494_;
}
v_reusejp_3494_:
{
lean_object* v___x_3496_; lean_object* v___x_3497_; 
v___x_3496_ = ((lean_object*)(l_Lean_ParametricAttribute_getParam_x3f___redArg___closed__1));
v___x_3497_ = l_Array_binSearchAux___redArg(v___f_3493_, v___x_3496_, v___x_3484_, v___x_3495_, v___x_3485_, v___x_3490_);
lean_dec_ref(v___x_3484_);
if (lean_obj_tag(v___x_3497_) == 0)
{
lean_object* v___x_3498_; 
v___x_3498_ = lean_box(0);
return v___x_3498_;
}
else
{
lean_object* v_val_3499_; lean_object* v___x_3501_; uint8_t v_isShared_3502_; uint8_t v_isSharedCheck_3507_; 
v_val_3499_ = lean_ctor_get(v___x_3497_, 0);
v_isSharedCheck_3507_ = !lean_is_exclusive(v___x_3497_);
if (v_isSharedCheck_3507_ == 0)
{
v___x_3501_ = v___x_3497_;
v_isShared_3502_ = v_isSharedCheck_3507_;
goto v_resetjp_3500_;
}
else
{
lean_inc(v_val_3499_);
lean_dec(v___x_3497_);
v___x_3501_ = lean_box(0);
v_isShared_3502_ = v_isSharedCheck_3507_;
goto v_resetjp_3500_;
}
v_resetjp_3500_:
{
lean_object* v_snd_3503_; lean_object* v___x_3505_; 
v_snd_3503_ = lean_ctor_get(v_val_3499_, 1);
lean_inc(v_snd_3503_);
lean_dec(v_val_3499_);
if (v_isShared_3502_ == 0)
{
lean_ctor_set(v___x_3501_, 0, v_snd_3503_);
v___x_3505_ = v___x_3501_;
goto v_reusejp_3504_;
}
else
{
lean_object* v_reuseFailAlloc_3506_; 
v_reuseFailAlloc_3506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3506_, 0, v_snd_3503_);
v___x_3505_ = v_reuseFailAlloc_3506_;
goto v_reusejp_3504_;
}
v_reusejp_3504_:
{
return v___x_3505_;
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
LEAN_EXPORT lean_object* l_Lean_EnumAttributes_getValue(lean_object* v_00_u03b1_3511_, lean_object* v_inst_3512_, lean_object* v_attr_3513_, lean_object* v_env_3514_, lean_object* v_decl_3515_){
_start:
{
lean_object* v___x_3516_; 
v___x_3516_ = l_Lean_EnumAttributes_getValue___redArg(v_inst_3512_, v_attr_3513_, v_env_3514_, v_decl_3515_);
return v___x_3516_;
}
}
LEAN_EXPORT lean_object* l_Lean_EnumAttributes_setValue___redArg(lean_object* v_attrs_3525_, lean_object* v_env_3526_, lean_object* v_decl_3527_, lean_object* v_val_3528_){
_start:
{
lean_object* v_ext_3529_; lean_object* v___x_3531_; uint8_t v_isShared_3532_; uint8_t v_isSharedCheck_3593_; 
v_ext_3529_ = lean_ctor_get(v_attrs_3525_, 1);
v_isSharedCheck_3593_ = !lean_is_exclusive(v_attrs_3525_);
if (v_isSharedCheck_3593_ == 0)
{
lean_object* v_unused_3594_; 
v_unused_3594_ = lean_ctor_get(v_attrs_3525_, 0);
lean_dec(v_unused_3594_);
v___x_3531_ = v_attrs_3525_;
v_isShared_3532_ = v_isSharedCheck_3593_;
goto v_resetjp_3530_;
}
else
{
lean_inc(v_ext_3529_);
lean_dec(v_attrs_3525_);
v___x_3531_ = lean_box(0);
v_isShared_3532_ = v_isSharedCheck_3593_;
goto v_resetjp_3530_;
}
v_resetjp_3530_:
{
lean_object* v_toEnvExtension_3533_; lean_object* v_name_3534_; lean_object* v___x_3535_; uint8_t v___x_3536_; lean_object* v___x_3537_; lean_object* v___x_3538_; lean_object* v___x_3539_; lean_object* v___x_3540_; lean_object* v___x_3541_; lean_object* v___x_3542_; lean_object* v___x_3543_; lean_object* v_pfx_3544_; lean_object* v___x_3545_; 
v_toEnvExtension_3533_ = lean_ctor_get(v_ext_3529_, 0);
v_name_3534_ = lean_ctor_get(v_ext_3529_, 1);
v___x_3535_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__0));
v___x_3536_ = 1;
lean_inc(v_name_3534_);
v___x_3537_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_3534_, v___x_3536_);
v___x_3538_ = lean_string_append(v___x_3535_, v___x_3537_);
lean_dec_ref(v___x_3537_);
v___x_3539_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__1));
v___x_3540_ = lean_string_append(v___x_3538_, v___x_3539_);
lean_inc(v_decl_3527_);
v___x_3541_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_decl_3527_, v___x_3536_);
v___x_3542_ = lean_string_append(v___x_3540_, v___x_3541_);
lean_dec_ref(v___x_3541_);
v___x_3543_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__4));
v_pfx_3544_ = lean_string_append(v___x_3542_, v___x_3543_);
v___x_3545_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3526_, v_decl_3527_);
if (lean_obj_tag(v___x_3545_) == 0)
{
lean_object* v_asyncMode_3546_; uint8_t v___x_3553_; 
v_asyncMode_3546_ = lean_ctor_get(v_toEnvExtension_3533_, 2);
lean_inc(v_asyncMode_3546_);
lean_inc(v_decl_3527_);
lean_inc_ref(v_env_3526_);
v___x_3553_ = l_Lean_EnvExtension_asyncMayModify___redArg(v_env_3526_, v_decl_3527_, v_asyncMode_3546_);
if (v___x_3553_ == 0)
{
lean_object* v___x_3554_; lean_object* v___x_3555_; lean_object* v___y_3557_; lean_object* v___x_3561_; 
lean_dec(v_asyncMode_3546_);
lean_del_object(v___x_3531_);
lean_dec_ref(v_ext_3529_);
lean_dec(v_val_3528_);
lean_dec(v_decl_3527_);
v___x_3554_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__2));
v___x_3555_ = lean_string_append(v_pfx_3544_, v___x_3554_);
v___x_3561_ = l_Lean_Environment_asyncPrefix_x3f(v_env_3526_);
if (lean_obj_tag(v___x_3561_) == 0)
{
lean_object* v___x_3562_; 
v___x_3562_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__3));
v___y_3557_ = v___x_3562_;
goto v___jp_3556_;
}
else
{
lean_object* v_val_3563_; lean_object* v___x_3564_; lean_object* v___x_3565_; lean_object* v___x_3566_; lean_object* v___x_3567_; lean_object* v___x_3568_; lean_object* v___x_3569_; 
v_val_3563_ = lean_ctor_get(v___x_3561_, 0);
lean_inc(v_val_3563_);
lean_dec_ref(v___x_3561_);
v___x_3564_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__4));
v___x_3565_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_val_3563_, v___x_3536_);
v___x_3566_ = l_addParenHeuristic(v___x_3565_);
v___x_3567_ = lean_string_append(v___x_3564_, v___x_3566_);
lean_dec_ref(v___x_3566_);
v___x_3568_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__5));
v___x_3569_ = lean_string_append(v___x_3567_, v___x_3568_);
v___y_3557_ = v___x_3569_;
goto v___jp_3556_;
}
v___jp_3556_:
{
lean_object* v___x_3558_; lean_object* v___x_3559_; lean_object* v___x_3560_; 
v___x_3558_ = lean_string_append(v___x_3555_, v___y_3557_);
lean_dec_ref(v___y_3557_);
v___x_3559_ = lean_string_append(v___x_3558_, v___x_3543_);
v___x_3560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3560_, 0, v___x_3559_);
return v___x_3560_;
}
}
else
{
lean_object* v___x_3570_; lean_object* v___x_3571_; lean_object* v___x_3572_; 
v___x_3570_ = lean_box(1);
lean_inc(v_decl_3527_);
lean_inc_ref(v_env_3526_);
v___x_3571_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3570_, v_ext_3529_, v_env_3526_, v_asyncMode_3546_, v_decl_3527_);
v___x_3572_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_3571_, v_decl_3527_);
lean_dec(v___x_3571_);
if (lean_obj_tag(v___x_3572_) == 0)
{
lean_dec_ref(v_pfx_3544_);
goto v___jp_3547_;
}
else
{
lean_object* v___x_3574_; uint8_t v_isShared_3575_; uint8_t v_isSharedCheck_3581_; 
v_isSharedCheck_3581_ = !lean_is_exclusive(v___x_3572_);
if (v_isSharedCheck_3581_ == 0)
{
lean_object* v_unused_3582_; 
v_unused_3582_ = lean_ctor_get(v___x_3572_, 0);
lean_dec(v_unused_3582_);
v___x_3574_ = v___x_3572_;
v_isShared_3575_ = v_isSharedCheck_3581_;
goto v_resetjp_3573_;
}
else
{
lean_dec(v___x_3572_);
v___x_3574_ = lean_box(0);
v_isShared_3575_ = v_isSharedCheck_3581_;
goto v_resetjp_3573_;
}
v_resetjp_3573_:
{
if (v___x_3553_ == 0)
{
lean_del_object(v___x_3574_);
lean_dec_ref(v_pfx_3544_);
goto v___jp_3547_;
}
else
{
lean_object* v___x_3576_; lean_object* v___x_3577_; lean_object* v___x_3579_; 
lean_dec(v_asyncMode_3546_);
lean_del_object(v___x_3531_);
lean_dec_ref(v_ext_3529_);
lean_dec(v_val_3528_);
lean_dec(v_decl_3527_);
lean_dec_ref(v_env_3526_);
v___x_3576_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__6));
v___x_3577_ = lean_string_append(v_pfx_3544_, v___x_3576_);
if (v_isShared_3575_ == 0)
{
lean_ctor_set_tag(v___x_3574_, 0);
lean_ctor_set(v___x_3574_, 0, v___x_3577_);
v___x_3579_ = v___x_3574_;
goto v_reusejp_3578_;
}
else
{
lean_object* v_reuseFailAlloc_3580_; 
v_reuseFailAlloc_3580_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3580_, 0, v___x_3577_);
v___x_3579_ = v_reuseFailAlloc_3580_;
goto v_reusejp_3578_;
}
v_reusejp_3578_:
{
return v___x_3579_;
}
}
}
}
}
v___jp_3547_:
{
lean_object* v___x_3549_; 
lean_inc(v_decl_3527_);
if (v_isShared_3532_ == 0)
{
lean_ctor_set(v___x_3531_, 1, v_val_3528_);
lean_ctor_set(v___x_3531_, 0, v_decl_3527_);
v___x_3549_ = v___x_3531_;
goto v_reusejp_3548_;
}
else
{
lean_object* v_reuseFailAlloc_3552_; 
v_reuseFailAlloc_3552_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3552_, 0, v_decl_3527_);
lean_ctor_set(v_reuseFailAlloc_3552_, 1, v_val_3528_);
v___x_3549_ = v_reuseFailAlloc_3552_;
goto v_reusejp_3548_;
}
v_reusejp_3548_:
{
lean_object* v___x_3550_; lean_object* v___x_3551_; 
v___x_3550_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_ext_3529_, v_env_3526_, v___x_3549_, v_asyncMode_3546_, v_decl_3527_);
lean_dec(v_asyncMode_3546_);
v___x_3551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3551_, 0, v___x_3550_);
return v___x_3551_;
}
}
}
else
{
lean_object* v___x_3584_; uint8_t v_isShared_3585_; uint8_t v_isSharedCheck_3591_; 
lean_del_object(v___x_3531_);
lean_dec_ref(v_ext_3529_);
lean_dec(v_val_3528_);
lean_dec(v_decl_3527_);
lean_dec_ref(v_env_3526_);
v_isSharedCheck_3591_ = !lean_is_exclusive(v___x_3545_);
if (v_isSharedCheck_3591_ == 0)
{
lean_object* v_unused_3592_; 
v_unused_3592_ = lean_ctor_get(v___x_3545_, 0);
lean_dec(v_unused_3592_);
v___x_3584_ = v___x_3545_;
v_isShared_3585_ = v_isSharedCheck_3591_;
goto v_resetjp_3583_;
}
else
{
lean_dec(v___x_3545_);
v___x_3584_ = lean_box(0);
v_isShared_3585_ = v_isSharedCheck_3591_;
goto v_resetjp_3583_;
}
v_resetjp_3583_:
{
lean_object* v___x_3586_; lean_object* v___x_3587_; lean_object* v___x_3589_; 
v___x_3586_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__7));
v___x_3587_ = lean_string_append(v_pfx_3544_, v___x_3586_);
if (v_isShared_3585_ == 0)
{
lean_ctor_set_tag(v___x_3584_, 0);
lean_ctor_set(v___x_3584_, 0, v___x_3587_);
v___x_3589_ = v___x_3584_;
goto v_reusejp_3588_;
}
else
{
lean_object* v_reuseFailAlloc_3590_; 
v_reuseFailAlloc_3590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3590_, 0, v___x_3587_);
v___x_3589_ = v_reuseFailAlloc_3590_;
goto v_reusejp_3588_;
}
v_reusejp_3588_:
{
return v___x_3589_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_EnumAttributes_setValue(lean_object* v_00_u03b1_3595_, lean_object* v_attrs_3596_, lean_object* v_env_3597_, lean_object* v_decl_3598_, lean_object* v_val_3599_){
_start:
{
lean_object* v___x_3600_; 
v___x_3600_ = l_Lean_EnumAttributes_setValue___redArg(v_attrs_3596_, v_env_3597_, v_decl_3598_, v_val_3599_);
return v___x_3600_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_2990505691____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3602_; lean_object* v___x_3603_; lean_object* v___x_3604_; 
v___x_3602_ = lean_obj_once(&l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_, &l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2__once, _init_l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_);
v___x_3603_ = lean_st_mk_ref(v___x_3602_);
v___x_3604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3604_, 0, v___x_3603_);
return v___x_3604_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_2990505691____hygCtx___hyg_2____boxed(lean_object* v_a_3605_){
_start:
{
lean_object* v_res_3606_; 
v_res_3606_ = l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_2990505691____hygCtx___hyg_2_();
return v_res_3606_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerAttributeImplBuilder(lean_object* v_builderId_3609_, lean_object* v_builder_3610_){
_start:
{
lean_object* v___x_3612_; lean_object* v___x_3613_; uint8_t v___x_3614_; 
v___x_3612_ = l_Lean_attributeImplBuilderTableRef;
v___x_3613_ = lean_st_ref_get(v___x_3612_);
v___x_3614_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(v___x_3613_, v_builderId_3609_);
lean_dec(v___x_3613_);
if (v___x_3614_ == 0)
{
lean_object* v___x_3615_; lean_object* v___x_3616_; lean_object* v___x_3617_; lean_object* v___x_3618_; 
v___x_3615_ = lean_st_ref_take(v___x_3612_);
v___x_3616_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1___redArg(v___x_3615_, v_builderId_3609_, v_builder_3610_);
v___x_3617_ = lean_st_ref_set(v___x_3612_, v___x_3616_);
v___x_3618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3618_, 0, v___x_3617_);
return v___x_3618_;
}
else
{
lean_object* v___x_3619_; lean_object* v___x_3620_; lean_object* v___x_3621_; lean_object* v___x_3622_; lean_object* v___x_3623_; lean_object* v___x_3624_; lean_object* v___x_3625_; 
lean_dec_ref(v_builder_3610_);
v___x_3619_ = ((lean_object*)(l_Lean_registerAttributeImplBuilder___closed__0));
v___x_3620_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_builderId_3609_, v___x_3614_);
v___x_3621_ = lean_string_append(v___x_3619_, v___x_3620_);
lean_dec_ref(v___x_3620_);
v___x_3622_ = ((lean_object*)(l_Lean_registerAttributeImplBuilder___closed__1));
v___x_3623_ = lean_string_append(v___x_3621_, v___x_3622_);
v___x_3624_ = lean_mk_io_user_error(v___x_3623_);
v___x_3625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3625_, 0, v___x_3624_);
return v___x_3625_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerAttributeImplBuilder___boxed(lean_object* v_builderId_3626_, lean_object* v_builder_3627_, lean_object* v_a_3628_){
_start:
{
lean_object* v_res_3629_; 
v_res_3629_ = l_Lean_registerAttributeImplBuilder(v_builderId_3626_, v_builder_3627_);
return v_res_3629_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___redArg(lean_object* v_e_3630_){
_start:
{
if (lean_obj_tag(v_e_3630_) == 0)
{
lean_object* v_a_3632_; lean_object* v___x_3634_; uint8_t v_isShared_3635_; uint8_t v_isSharedCheck_3640_; 
v_a_3632_ = lean_ctor_get(v_e_3630_, 0);
v_isSharedCheck_3640_ = !lean_is_exclusive(v_e_3630_);
if (v_isSharedCheck_3640_ == 0)
{
v___x_3634_ = v_e_3630_;
v_isShared_3635_ = v_isSharedCheck_3640_;
goto v_resetjp_3633_;
}
else
{
lean_inc(v_a_3632_);
lean_dec(v_e_3630_);
v___x_3634_ = lean_box(0);
v_isShared_3635_ = v_isSharedCheck_3640_;
goto v_resetjp_3633_;
}
v_resetjp_3633_:
{
lean_object* v___x_3636_; lean_object* v___x_3638_; 
v___x_3636_ = lean_mk_io_user_error(v_a_3632_);
if (v_isShared_3635_ == 0)
{
lean_ctor_set_tag(v___x_3634_, 1);
lean_ctor_set(v___x_3634_, 0, v___x_3636_);
v___x_3638_ = v___x_3634_;
goto v_reusejp_3637_;
}
else
{
lean_object* v_reuseFailAlloc_3639_; 
v_reuseFailAlloc_3639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3639_, 0, v___x_3636_);
v___x_3638_ = v_reuseFailAlloc_3639_;
goto v_reusejp_3637_;
}
v_reusejp_3637_:
{
return v___x_3638_;
}
}
}
else
{
lean_object* v_a_3641_; lean_object* v___x_3643_; uint8_t v_isShared_3644_; uint8_t v_isSharedCheck_3648_; 
v_a_3641_ = lean_ctor_get(v_e_3630_, 0);
v_isSharedCheck_3648_ = !lean_is_exclusive(v_e_3630_);
if (v_isSharedCheck_3648_ == 0)
{
v___x_3643_ = v_e_3630_;
v_isShared_3644_ = v_isSharedCheck_3648_;
goto v_resetjp_3642_;
}
else
{
lean_inc(v_a_3641_);
lean_dec(v_e_3630_);
v___x_3643_ = lean_box(0);
v_isShared_3644_ = v_isSharedCheck_3648_;
goto v_resetjp_3642_;
}
v_resetjp_3642_:
{
lean_object* v___x_3646_; 
if (v_isShared_3644_ == 0)
{
lean_ctor_set_tag(v___x_3643_, 0);
v___x_3646_ = v___x_3643_;
goto v_reusejp_3645_;
}
else
{
lean_object* v_reuseFailAlloc_3647_; 
v_reuseFailAlloc_3647_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3647_, 0, v_a_3641_);
v___x_3646_ = v_reuseFailAlloc_3647_;
goto v_reusejp_3645_;
}
v_reusejp_3645_:
{
return v___x_3646_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___redArg___boxed(lean_object* v_e_3649_, lean_object* v_a_3650_){
_start:
{
lean_object* v_res_3651_; 
v_res_3651_ = l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___redArg(v_e_3649_);
return v_res_3651_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1(lean_object* v_00_u03b1_3652_, lean_object* v_e_3653_){
_start:
{
lean_object* v___x_3655_; 
v___x_3655_ = l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___redArg(v_e_3653_);
return v___x_3655_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___boxed(lean_object* v_00_u03b1_3656_, lean_object* v_e_3657_, lean_object* v_a_3658_){
_start:
{
lean_object* v_res_3659_; 
v_res_3659_ = l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1(v_00_u03b1_3656_, v_e_3657_);
return v_res_3659_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___redArg(lean_object* v_a_3660_, lean_object* v_x_3661_){
_start:
{
if (lean_obj_tag(v_x_3661_) == 0)
{
lean_object* v___x_3662_; 
v___x_3662_ = lean_box(0);
return v___x_3662_;
}
else
{
lean_object* v_key_3663_; lean_object* v_value_3664_; lean_object* v_tail_3665_; uint8_t v___x_3666_; 
v_key_3663_ = lean_ctor_get(v_x_3661_, 0);
v_value_3664_ = lean_ctor_get(v_x_3661_, 1);
v_tail_3665_ = lean_ctor_get(v_x_3661_, 2);
v___x_3666_ = lean_name_eq(v_key_3663_, v_a_3660_);
if (v___x_3666_ == 0)
{
v_x_3661_ = v_tail_3665_;
goto _start;
}
else
{
lean_object* v___x_3668_; 
lean_inc(v_value_3664_);
v___x_3668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3668_, 0, v_value_3664_);
return v___x_3668_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___redArg___boxed(lean_object* v_a_3669_, lean_object* v_x_3670_){
_start:
{
lean_object* v_res_3671_; 
v_res_3671_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___redArg(v_a_3669_, v_x_3670_);
lean_dec(v_x_3670_);
lean_dec(v_a_3669_);
return v_res_3671_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(lean_object* v_m_3672_, lean_object* v_a_3673_){
_start:
{
lean_object* v_buckets_3674_; lean_object* v___x_3675_; uint64_t v___y_3677_; 
v_buckets_3674_ = lean_ctor_get(v_m_3672_, 1);
v___x_3675_ = lean_array_get_size(v_buckets_3674_);
if (lean_obj_tag(v_a_3673_) == 0)
{
uint64_t v___x_3691_; 
v___x_3691_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg___closed__0);
v___y_3677_ = v___x_3691_;
goto v___jp_3676_;
}
else
{
uint64_t v_hash_3692_; 
v_hash_3692_ = lean_ctor_get_uint64(v_a_3673_, sizeof(void*)*2);
v___y_3677_ = v_hash_3692_;
goto v___jp_3676_;
}
v___jp_3676_:
{
uint64_t v___x_3678_; uint64_t v___x_3679_; uint64_t v_fold_3680_; uint64_t v___x_3681_; uint64_t v___x_3682_; uint64_t v___x_3683_; size_t v___x_3684_; size_t v___x_3685_; size_t v___x_3686_; size_t v___x_3687_; size_t v___x_3688_; lean_object* v___x_3689_; lean_object* v___x_3690_; 
v___x_3678_ = 32ULL;
v___x_3679_ = lean_uint64_shift_right(v___y_3677_, v___x_3678_);
v_fold_3680_ = lean_uint64_xor(v___y_3677_, v___x_3679_);
v___x_3681_ = 16ULL;
v___x_3682_ = lean_uint64_shift_right(v_fold_3680_, v___x_3681_);
v___x_3683_ = lean_uint64_xor(v_fold_3680_, v___x_3682_);
v___x_3684_ = lean_uint64_to_usize(v___x_3683_);
v___x_3685_ = lean_usize_of_nat(v___x_3675_);
v___x_3686_ = ((size_t)1ULL);
v___x_3687_ = lean_usize_sub(v___x_3685_, v___x_3686_);
v___x_3688_ = lean_usize_land(v___x_3684_, v___x_3687_);
v___x_3689_ = lean_array_uget_borrowed(v_buckets_3674_, v___x_3688_);
v___x_3690_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___redArg(v_a_3673_, v___x_3689_);
return v___x_3690_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg___boxed(lean_object* v_m_3693_, lean_object* v_a_3694_){
_start:
{
lean_object* v_res_3695_; 
v_res_3695_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(v_m_3693_, v_a_3694_);
lean_dec(v_a_3694_);
lean_dec_ref(v_m_3693_);
return v_res_3695_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAttributeImplOfEntry(lean_object* v_e_3697_){
_start:
{
lean_object* v___x_3699_; lean_object* v___x_3700_; lean_object* v_builderId_3701_; lean_object* v_ref_3702_; lean_object* v_args_3703_; lean_object* v___x_3704_; 
v___x_3699_ = l_Lean_attributeImplBuilderTableRef;
v___x_3700_ = lean_st_ref_get(v___x_3699_);
v_builderId_3701_ = lean_ctor_get(v_e_3697_, 0);
lean_inc(v_builderId_3701_);
v_ref_3702_ = lean_ctor_get(v_e_3697_, 1);
lean_inc(v_ref_3702_);
v_args_3703_ = lean_ctor_get(v_e_3697_, 2);
lean_inc(v_args_3703_);
lean_dec_ref(v_e_3697_);
v___x_3704_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(v___x_3700_, v_builderId_3701_);
lean_dec(v___x_3700_);
if (lean_obj_tag(v___x_3704_) == 0)
{
lean_object* v___x_3705_; uint8_t v___x_3706_; lean_object* v___x_3707_; lean_object* v___x_3708_; lean_object* v___x_3709_; lean_object* v___x_3710_; lean_object* v___x_3711_; lean_object* v___x_3712_; 
lean_dec(v_args_3703_);
lean_dec(v_ref_3702_);
v___x_3705_ = ((lean_object*)(l_Lean_mkAttributeImplOfEntry___closed__0));
v___x_3706_ = 1;
v___x_3707_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_builderId_3701_, v___x_3706_);
v___x_3708_ = lean_string_append(v___x_3705_, v___x_3707_);
lean_dec_ref(v___x_3707_);
v___x_3709_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__4));
v___x_3710_ = lean_string_append(v___x_3708_, v___x_3709_);
v___x_3711_ = lean_mk_io_user_error(v___x_3710_);
v___x_3712_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3712_, 0, v___x_3711_);
return v___x_3712_;
}
else
{
lean_object* v_val_3713_; lean_object* v___x_3714_; lean_object* v___x_3715_; 
lean_dec(v_builderId_3701_);
v_val_3713_ = lean_ctor_get(v___x_3704_, 0);
lean_inc(v_val_3713_);
lean_dec_ref(v___x_3704_);
v___x_3714_ = lean_apply_2(v_val_3713_, v_ref_3702_, v_args_3703_);
v___x_3715_ = l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___redArg(v___x_3714_);
return v___x_3715_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkAttributeImplOfEntry___boxed(lean_object* v_e_3716_, lean_object* v_a_3717_){
_start:
{
lean_object* v_res_3718_; 
v_res_3718_ = l_Lean_mkAttributeImplOfEntry(v_e_3716_);
return v_res_3718_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0(lean_object* v_00_u03b2_3719_, lean_object* v_m_3720_, lean_object* v_a_3721_){
_start:
{
lean_object* v___x_3722_; 
v___x_3722_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(v_m_3720_, v_a_3721_);
return v___x_3722_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___boxed(lean_object* v_00_u03b2_3723_, lean_object* v_m_3724_, lean_object* v_a_3725_){
_start:
{
lean_object* v_res_3726_; 
v_res_3726_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0(v_00_u03b2_3723_, v_m_3724_, v_a_3725_);
lean_dec(v_a_3725_);
lean_dec_ref(v_m_3724_);
return v_res_3726_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0(lean_object* v_00_u03b2_3727_, lean_object* v_a_3728_, lean_object* v_x_3729_){
_start:
{
lean_object* v___x_3730_; 
v___x_3730_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___redArg(v_a_3728_, v_x_3729_);
return v___x_3730_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3731_, lean_object* v_a_3732_, lean_object* v_x_3733_){
_start:
{
lean_object* v_res_3734_; 
v_res_3734_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0(v_00_u03b2_3731_, v_a_3732_, v_x_3733_);
lean_dec(v_x_3733_);
lean_dec(v_a_3732_);
return v_res_3734_;
}
}
static lean_object* _init_l_Lean_instInhabitedAttributeExtensionState_default___closed__0(void){
_start:
{
lean_object* v___x_3735_; lean_object* v___x_3736_; lean_object* v___x_3737_; 
v___x_3735_ = lean_obj_once(&l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_, &l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2__once, _init_l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_);
v___x_3736_ = lean_box(0);
v___x_3737_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3737_, 0, v___x_3736_);
lean_ctor_set(v___x_3737_, 1, v___x_3735_);
return v___x_3737_;
}
}
static lean_object* _init_l_Lean_instInhabitedAttributeExtensionState_default(void){
_start:
{
lean_object* v___x_3738_; 
v___x_3738_ = lean_obj_once(&l_Lean_instInhabitedAttributeExtensionState_default___closed__0, &l_Lean_instInhabitedAttributeExtensionState_default___closed__0_once, _init_l_Lean_instInhabitedAttributeExtensionState_default___closed__0);
return v___x_3738_;
}
}
static lean_object* _init_l_Lean_instInhabitedAttributeExtensionState(void){
_start:
{
lean_object* v___x_3739_; 
v___x_3739_ = l_Lean_instInhabitedAttributeExtensionState_default;
return v___x_3739_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_AttributeExtension_mkInitial(){
_start:
{
lean_object* v___x_3741_; lean_object* v___x_3742_; lean_object* v___x_3743_; lean_object* v___x_3744_; lean_object* v___x_3745_; 
v___x_3741_ = l_Lean_attributeMapRef;
v___x_3742_ = lean_st_ref_get(v___x_3741_);
v___x_3743_ = lean_box(0);
v___x_3744_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3744_, 0, v___x_3743_);
lean_ctor_set(v___x_3744_, 1, v___x_3742_);
v___x_3745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3745_, 0, v___x_3744_);
return v___x_3745_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_AttributeExtension_mkInitial___boxed(lean_object* v_a_3746_){
_start:
{
lean_object* v_res_3747_; 
v_res_3747_ = l___private_Lean_Attributes_0__Lean_AttributeExtension_mkInitial();
return v_res_3747_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAttributeImplOfConstantUnsafe(lean_object* v_env_3753_, lean_object* v_opts_3754_, lean_object* v_declName_3755_){
_start:
{
uint8_t v___x_3758_; lean_object* v___x_3759_; 
v___x_3758_ = 0;
lean_inc(v_declName_3755_);
lean_inc_ref(v_env_3753_);
v___x_3759_ = l_Lean_Environment_find_x3f(v_env_3753_, v_declName_3755_, v___x_3758_);
if (lean_obj_tag(v___x_3759_) == 0)
{
lean_object* v___x_3760_; uint8_t v___x_3761_; lean_object* v___x_3762_; lean_object* v___x_3763_; lean_object* v___x_3764_; lean_object* v___x_3765_; lean_object* v___x_3766_; 
lean_dec_ref(v_env_3753_);
v___x_3760_ = ((lean_object*)(l_Lean_mkAttributeImplOfConstantUnsafe___closed__2));
v___x_3761_ = 1;
v___x_3762_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_declName_3755_, v___x_3761_);
v___x_3763_ = lean_string_append(v___x_3760_, v___x_3762_);
lean_dec_ref(v___x_3762_);
v___x_3764_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__4));
v___x_3765_ = lean_string_append(v___x_3763_, v___x_3764_);
v___x_3766_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3766_, 0, v___x_3765_);
return v___x_3766_;
}
else
{
lean_object* v_val_3767_; lean_object* v___x_3768_; 
v_val_3767_ = lean_ctor_get(v___x_3759_, 0);
lean_inc(v_val_3767_);
lean_dec_ref(v___x_3759_);
v___x_3768_ = l_Lean_ConstantInfo_type(v_val_3767_);
lean_dec(v_val_3767_);
if (lean_obj_tag(v___x_3768_) == 4)
{
lean_object* v_declName_3769_; 
v_declName_3769_ = lean_ctor_get(v___x_3768_, 0);
lean_inc(v_declName_3769_);
lean_dec_ref(v___x_3768_);
if (lean_obj_tag(v_declName_3769_) == 1)
{
lean_object* v_pre_3770_; 
v_pre_3770_ = lean_ctor_get(v_declName_3769_, 0);
lean_inc(v_pre_3770_);
if (lean_obj_tag(v_pre_3770_) == 1)
{
lean_object* v_pre_3771_; 
v_pre_3771_ = lean_ctor_get(v_pre_3770_, 0);
if (lean_obj_tag(v_pre_3771_) == 0)
{
lean_object* v_str_3772_; lean_object* v_str_3773_; lean_object* v___x_3774_; uint8_t v___x_3775_; 
v_str_3772_ = lean_ctor_get(v_declName_3769_, 1);
lean_inc_ref(v_str_3772_);
lean_dec_ref(v_declName_3769_);
v_str_3773_ = lean_ctor_get(v_pre_3770_, 1);
lean_inc_ref(v_str_3773_);
lean_dec_ref(v_pre_3770_);
v___x_3774_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__0));
v___x_3775_ = lean_string_dec_eq(v_str_3773_, v___x_3774_);
lean_dec_ref(v_str_3773_);
if (v___x_3775_ == 0)
{
lean_dec_ref(v_str_3772_);
lean_dec(v_declName_3755_);
lean_dec_ref(v_env_3753_);
goto v___jp_3756_;
}
else
{
lean_object* v___x_3776_; uint8_t v___x_3777_; 
v___x_3776_ = ((lean_object*)(l_Lean_mkAttributeImplOfConstantUnsafe___closed__3));
v___x_3777_ = lean_string_dec_eq(v_str_3772_, v___x_3776_);
lean_dec_ref(v_str_3772_);
if (v___x_3777_ == 0)
{
lean_dec(v_declName_3755_);
lean_dec_ref(v_env_3753_);
goto v___jp_3756_;
}
else
{
lean_object* v___x_3778_; 
v___x_3778_ = l_Lean_Environment_evalConst___redArg(v_env_3753_, v_opts_3754_, v_declName_3755_, v___x_3777_);
lean_dec(v_declName_3755_);
lean_dec_ref(v_env_3753_);
return v___x_3778_;
}
}
}
else
{
lean_dec_ref(v_pre_3770_);
lean_dec_ref(v_declName_3769_);
lean_dec(v_declName_3755_);
lean_dec_ref(v_env_3753_);
goto v___jp_3756_;
}
}
else
{
lean_dec(v_pre_3770_);
lean_dec_ref(v_declName_3769_);
lean_dec(v_declName_3755_);
lean_dec_ref(v_env_3753_);
goto v___jp_3756_;
}
}
else
{
lean_dec(v_declName_3769_);
lean_dec(v_declName_3755_);
lean_dec_ref(v_env_3753_);
goto v___jp_3756_;
}
}
else
{
lean_dec_ref(v___x_3768_);
lean_dec(v_declName_3755_);
lean_dec_ref(v_env_3753_);
goto v___jp_3756_;
}
}
v___jp_3756_:
{
lean_object* v___x_3757_; 
v___x_3757_ = ((lean_object*)(l_Lean_mkAttributeImplOfConstantUnsafe___closed__1));
return v___x_3757_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkAttributeImplOfConstantUnsafe___boxed(lean_object* v_env_3779_, lean_object* v_opts_3780_, lean_object* v_declName_3781_){
_start:
{
lean_object* v_res_3782_; 
v_res_3782_ = l_Lean_mkAttributeImplOfConstantUnsafe(v_env_3779_, v_opts_3780_, v_declName_3781_);
lean_dec_ref(v_opts_3780_);
return v_res_3782_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg(lean_object* v_as_3783_, size_t v_i_3784_, size_t v_stop_3785_, lean_object* v_b_3786_){
_start:
{
uint8_t v___x_3788_; 
v___x_3788_ = lean_usize_dec_eq(v_i_3784_, v_stop_3785_);
if (v___x_3788_ == 0)
{
lean_object* v___x_3789_; lean_object* v___x_3790_; 
v___x_3789_ = lean_array_uget_borrowed(v_as_3783_, v_i_3784_);
lean_inc(v___x_3789_);
v___x_3790_ = l_Lean_mkAttributeImplOfEntry(v___x_3789_);
if (lean_obj_tag(v___x_3790_) == 0)
{
lean_object* v_a_3791_; lean_object* v_toAttributeImplCore_3792_; lean_object* v_name_3793_; lean_object* v___x_3794_; size_t v___x_3795_; size_t v___x_3796_; 
v_a_3791_ = lean_ctor_get(v___x_3790_, 0);
lean_inc(v_a_3791_);
lean_dec_ref(v___x_3790_);
v_toAttributeImplCore_3792_ = lean_ctor_get(v_a_3791_, 0);
v_name_3793_ = lean_ctor_get(v_toAttributeImplCore_3792_, 1);
lean_inc(v_name_3793_);
v___x_3794_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1___redArg(v_b_3786_, v_name_3793_, v_a_3791_);
v___x_3795_ = ((size_t)1ULL);
v___x_3796_ = lean_usize_add(v_i_3784_, v___x_3795_);
v_i_3784_ = v___x_3796_;
v_b_3786_ = v___x_3794_;
goto _start;
}
else
{
lean_object* v_a_3798_; lean_object* v___x_3800_; uint8_t v_isShared_3801_; uint8_t v_isSharedCheck_3805_; 
lean_dec_ref(v_b_3786_);
v_a_3798_ = lean_ctor_get(v___x_3790_, 0);
v_isSharedCheck_3805_ = !lean_is_exclusive(v___x_3790_);
if (v_isSharedCheck_3805_ == 0)
{
v___x_3800_ = v___x_3790_;
v_isShared_3801_ = v_isSharedCheck_3805_;
goto v_resetjp_3799_;
}
else
{
lean_inc(v_a_3798_);
lean_dec(v___x_3790_);
v___x_3800_ = lean_box(0);
v_isShared_3801_ = v_isSharedCheck_3805_;
goto v_resetjp_3799_;
}
v_resetjp_3799_:
{
lean_object* v___x_3803_; 
if (v_isShared_3801_ == 0)
{
v___x_3803_ = v___x_3800_;
goto v_reusejp_3802_;
}
else
{
lean_object* v_reuseFailAlloc_3804_; 
v_reuseFailAlloc_3804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3804_, 0, v_a_3798_);
v___x_3803_ = v_reuseFailAlloc_3804_;
goto v_reusejp_3802_;
}
v_reusejp_3802_:
{
return v___x_3803_;
}
}
}
}
else
{
lean_object* v___x_3806_; 
v___x_3806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3806_, 0, v_b_3786_);
return v___x_3806_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg___boxed(lean_object* v_as_3807_, lean_object* v_i_3808_, lean_object* v_stop_3809_, lean_object* v_b_3810_, lean_object* v___y_3811_){
_start:
{
size_t v_i_boxed_3812_; size_t v_stop_boxed_3813_; lean_object* v_res_3814_; 
v_i_boxed_3812_ = lean_unbox_usize(v_i_3808_);
lean_dec(v_i_3808_);
v_stop_boxed_3813_ = lean_unbox_usize(v_stop_3809_);
lean_dec(v_stop_3809_);
v_res_3814_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg(v_as_3807_, v_i_boxed_3812_, v_stop_boxed_3813_, v_b_3810_);
lean_dec_ref(v_as_3807_);
return v_res_3814_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__1(lean_object* v_as_3815_, size_t v_i_3816_, size_t v_stop_3817_, lean_object* v_b_3818_, lean_object* v___y_3819_){
_start:
{
lean_object* v_a_3822_; lean_object* v___y_3827_; uint8_t v___x_3829_; 
v___x_3829_ = lean_usize_dec_eq(v_i_3816_, v_stop_3817_);
if (v___x_3829_ == 0)
{
lean_object* v___x_3830_; lean_object* v___x_3831_; lean_object* v___x_3832_; uint8_t v___x_3833_; 
v___x_3830_ = lean_array_uget_borrowed(v_as_3815_, v_i_3816_);
v___x_3831_ = lean_unsigned_to_nat(0u);
v___x_3832_ = lean_array_get_size(v___x_3830_);
v___x_3833_ = lean_nat_dec_lt(v___x_3831_, v___x_3832_);
if (v___x_3833_ == 0)
{
v_a_3822_ = v_b_3818_;
goto v___jp_3821_;
}
else
{
uint8_t v___x_3834_; 
v___x_3834_ = lean_nat_dec_le(v___x_3832_, v___x_3832_);
if (v___x_3834_ == 0)
{
if (v___x_3833_ == 0)
{
v_a_3822_ = v_b_3818_;
goto v___jp_3821_;
}
else
{
size_t v___x_3835_; size_t v___x_3836_; lean_object* v___x_3837_; 
v___x_3835_ = ((size_t)0ULL);
v___x_3836_ = lean_usize_of_nat(v___x_3832_);
v___x_3837_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg(v___x_3830_, v___x_3835_, v___x_3836_, v_b_3818_);
v___y_3827_ = v___x_3837_;
goto v___jp_3826_;
}
}
else
{
size_t v___x_3838_; size_t v___x_3839_; lean_object* v___x_3840_; 
v___x_3838_ = ((size_t)0ULL);
v___x_3839_ = lean_usize_of_nat(v___x_3832_);
v___x_3840_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg(v___x_3830_, v___x_3838_, v___x_3839_, v_b_3818_);
v___y_3827_ = v___x_3840_;
goto v___jp_3826_;
}
}
}
else
{
lean_object* v___x_3841_; 
v___x_3841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3841_, 0, v_b_3818_);
return v___x_3841_;
}
v___jp_3821_:
{
size_t v___x_3823_; size_t v___x_3824_; 
v___x_3823_ = ((size_t)1ULL);
v___x_3824_ = lean_usize_add(v_i_3816_, v___x_3823_);
v_i_3816_ = v___x_3824_;
v_b_3818_ = v_a_3822_;
goto _start;
}
v___jp_3826_:
{
if (lean_obj_tag(v___y_3827_) == 0)
{
lean_object* v_a_3828_; 
v_a_3828_ = lean_ctor_get(v___y_3827_, 0);
lean_inc(v_a_3828_);
lean_dec_ref(v___y_3827_);
v_a_3822_ = v_a_3828_;
goto v___jp_3821_;
}
else
{
return v___y_3827_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__1___boxed(lean_object* v_as_3842_, lean_object* v_i_3843_, lean_object* v_stop_3844_, lean_object* v_b_3845_, lean_object* v___y_3846_, lean_object* v___y_3847_){
_start:
{
size_t v_i_boxed_3848_; size_t v_stop_boxed_3849_; lean_object* v_res_3850_; 
v_i_boxed_3848_ = lean_unbox_usize(v_i_3843_);
lean_dec(v_i_3843_);
v_stop_boxed_3849_ = lean_unbox_usize(v_stop_3844_);
lean_dec(v_stop_3844_);
v_res_3850_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__1(v_as_3842_, v_i_boxed_3848_, v_stop_boxed_3849_, v_b_3845_, v___y_3846_);
lean_dec_ref(v___y_3846_);
lean_dec_ref(v_as_3842_);
return v_res_3850_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_AttributeExtension_addImported(lean_object* v_es_3851_, lean_object* v_a_3852_){
_start:
{
lean_object* v_a_3855_; lean_object* v___y_3860_; lean_object* v___x_3870_; lean_object* v___x_3871_; lean_object* v___x_3872_; lean_object* v___x_3873_; uint8_t v___x_3874_; 
v___x_3870_ = l_Lean_attributeMapRef;
v___x_3871_ = lean_st_ref_get(v___x_3870_);
v___x_3872_ = lean_unsigned_to_nat(0u);
v___x_3873_ = lean_array_get_size(v_es_3851_);
v___x_3874_ = lean_nat_dec_lt(v___x_3872_, v___x_3873_);
if (v___x_3874_ == 0)
{
v_a_3855_ = v___x_3871_;
goto v___jp_3854_;
}
else
{
uint8_t v___x_3875_; 
v___x_3875_ = lean_nat_dec_le(v___x_3873_, v___x_3873_);
if (v___x_3875_ == 0)
{
if (v___x_3874_ == 0)
{
v_a_3855_ = v___x_3871_;
goto v___jp_3854_;
}
else
{
size_t v___x_3876_; size_t v___x_3877_; lean_object* v___x_3878_; 
v___x_3876_ = ((size_t)0ULL);
v___x_3877_ = lean_usize_of_nat(v___x_3873_);
v___x_3878_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__1(v_es_3851_, v___x_3876_, v___x_3877_, v___x_3871_, v_a_3852_);
v___y_3860_ = v___x_3878_;
goto v___jp_3859_;
}
}
else
{
size_t v___x_3879_; size_t v___x_3880_; lean_object* v___x_3881_; 
v___x_3879_ = ((size_t)0ULL);
v___x_3880_ = lean_usize_of_nat(v___x_3873_);
v___x_3881_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__1(v_es_3851_, v___x_3879_, v___x_3880_, v___x_3871_, v_a_3852_);
v___y_3860_ = v___x_3881_;
goto v___jp_3859_;
}
}
v___jp_3854_:
{
lean_object* v___x_3856_; lean_object* v___x_3857_; lean_object* v___x_3858_; 
v___x_3856_ = lean_box(0);
v___x_3857_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3857_, 0, v___x_3856_);
lean_ctor_set(v___x_3857_, 1, v_a_3855_);
v___x_3858_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3858_, 0, v___x_3857_);
return v___x_3858_;
}
v___jp_3859_:
{
if (lean_obj_tag(v___y_3860_) == 0)
{
lean_object* v_a_3861_; 
v_a_3861_ = lean_ctor_get(v___y_3860_, 0);
lean_inc(v_a_3861_);
lean_dec_ref(v___y_3860_);
v_a_3855_ = v_a_3861_;
goto v___jp_3854_;
}
else
{
lean_object* v_a_3862_; lean_object* v___x_3864_; uint8_t v_isShared_3865_; uint8_t v_isSharedCheck_3869_; 
v_a_3862_ = lean_ctor_get(v___y_3860_, 0);
v_isSharedCheck_3869_ = !lean_is_exclusive(v___y_3860_);
if (v_isSharedCheck_3869_ == 0)
{
v___x_3864_ = v___y_3860_;
v_isShared_3865_ = v_isSharedCheck_3869_;
goto v_resetjp_3863_;
}
else
{
lean_inc(v_a_3862_);
lean_dec(v___y_3860_);
v___x_3864_ = lean_box(0);
v_isShared_3865_ = v_isSharedCheck_3869_;
goto v_resetjp_3863_;
}
v_resetjp_3863_:
{
lean_object* v___x_3867_; 
if (v_isShared_3865_ == 0)
{
v___x_3867_ = v___x_3864_;
goto v_reusejp_3866_;
}
else
{
lean_object* v_reuseFailAlloc_3868_; 
v_reuseFailAlloc_3868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3868_, 0, v_a_3862_);
v___x_3867_ = v_reuseFailAlloc_3868_;
goto v_reusejp_3866_;
}
v_reusejp_3866_:
{
return v___x_3867_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_AttributeExtension_addImported___boxed(lean_object* v_es_3882_, lean_object* v_a_3883_, lean_object* v_a_3884_){
_start:
{
lean_object* v_res_3885_; 
v_res_3885_ = l___private_Lean_Attributes_0__Lean_AttributeExtension_addImported(v_es_3882_, v_a_3883_);
lean_dec_ref(v_a_3883_);
lean_dec_ref(v_es_3882_);
return v_res_3885_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0(lean_object* v_as_3886_, size_t v_i_3887_, size_t v_stop_3888_, lean_object* v_b_3889_, lean_object* v___y_3890_){
_start:
{
lean_object* v___x_3892_; 
v___x_3892_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg(v_as_3886_, v_i_3887_, v_stop_3888_, v_b_3889_);
return v___x_3892_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___boxed(lean_object* v_as_3893_, lean_object* v_i_3894_, lean_object* v_stop_3895_, lean_object* v_b_3896_, lean_object* v___y_3897_, lean_object* v___y_3898_){
_start:
{
size_t v_i_boxed_3899_; size_t v_stop_boxed_3900_; lean_object* v_res_3901_; 
v_i_boxed_3899_ = lean_unbox_usize(v_i_3894_);
lean_dec(v_i_3894_);
v_stop_boxed_3900_ = lean_unbox_usize(v_stop_3895_);
lean_dec(v_stop_3895_);
v_res_3901_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0(v_as_3893_, v_i_boxed_3899_, v_stop_boxed_3900_, v_b_3896_, v___y_3897_);
lean_dec_ref(v___y_3897_);
lean_dec_ref(v_as_3893_);
return v_res_3901_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_addAttrEntry(lean_object* v_s_3902_, lean_object* v_e_3903_){
_start:
{
lean_object* v_snd_3904_; lean_object* v_toAttributeImplCore_3905_; lean_object* v_fst_3906_; lean_object* v___x_3908_; uint8_t v_isShared_3909_; uint8_t v_isSharedCheck_3924_; 
v_snd_3904_ = lean_ctor_get(v_e_3903_, 1);
lean_inc(v_snd_3904_);
v_toAttributeImplCore_3905_ = lean_ctor_get(v_snd_3904_, 0);
v_fst_3906_ = lean_ctor_get(v_e_3903_, 0);
v_isSharedCheck_3924_ = !lean_is_exclusive(v_e_3903_);
if (v_isSharedCheck_3924_ == 0)
{
lean_object* v_unused_3925_; 
v_unused_3925_ = lean_ctor_get(v_e_3903_, 1);
lean_dec(v_unused_3925_);
v___x_3908_ = v_e_3903_;
v_isShared_3909_ = v_isSharedCheck_3924_;
goto v_resetjp_3907_;
}
else
{
lean_inc(v_fst_3906_);
lean_dec(v_e_3903_);
v___x_3908_ = lean_box(0);
v_isShared_3909_ = v_isSharedCheck_3924_;
goto v_resetjp_3907_;
}
v_resetjp_3907_:
{
lean_object* v_newEntries_3910_; lean_object* v_map_3911_; lean_object* v___x_3913_; uint8_t v_isShared_3914_; uint8_t v_isSharedCheck_3923_; 
v_newEntries_3910_ = lean_ctor_get(v_s_3902_, 0);
v_map_3911_ = lean_ctor_get(v_s_3902_, 1);
v_isSharedCheck_3923_ = !lean_is_exclusive(v_s_3902_);
if (v_isSharedCheck_3923_ == 0)
{
v___x_3913_ = v_s_3902_;
v_isShared_3914_ = v_isSharedCheck_3923_;
goto v_resetjp_3912_;
}
else
{
lean_inc(v_map_3911_);
lean_inc(v_newEntries_3910_);
lean_dec(v_s_3902_);
v___x_3913_ = lean_box(0);
v_isShared_3914_ = v_isSharedCheck_3923_;
goto v_resetjp_3912_;
}
v_resetjp_3912_:
{
lean_object* v_name_3915_; lean_object* v___x_3917_; 
v_name_3915_ = lean_ctor_get(v_toAttributeImplCore_3905_, 1);
lean_inc(v_name_3915_);
if (v_isShared_3909_ == 0)
{
lean_ctor_set_tag(v___x_3908_, 1);
lean_ctor_set(v___x_3908_, 1, v_newEntries_3910_);
v___x_3917_ = v___x_3908_;
goto v_reusejp_3916_;
}
else
{
lean_object* v_reuseFailAlloc_3922_; 
v_reuseFailAlloc_3922_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3922_, 0, v_fst_3906_);
lean_ctor_set(v_reuseFailAlloc_3922_, 1, v_newEntries_3910_);
v___x_3917_ = v_reuseFailAlloc_3922_;
goto v_reusejp_3916_;
}
v_reusejp_3916_:
{
lean_object* v___x_3918_; lean_object* v___x_3920_; 
v___x_3918_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1___redArg(v_map_3911_, v_name_3915_, v_snd_3904_);
if (v_isShared_3914_ == 0)
{
lean_ctor_set(v___x_3913_, 1, v___x_3918_);
lean_ctor_set(v___x_3913_, 0, v___x_3917_);
v___x_3920_ = v___x_3913_;
goto v_reusejp_3919_;
}
else
{
lean_object* v_reuseFailAlloc_3921_; 
v_reuseFailAlloc_3921_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3921_, 0, v___x_3917_);
lean_ctor_set(v_reuseFailAlloc_3921_, 1, v___x_3918_);
v___x_3920_ = v_reuseFailAlloc_3921_;
goto v_reusejp_3919_;
}
v_reusejp_3919_:
{
return v___x_3920_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn___lam__0_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(lean_object* v_x_3926_, lean_object* v_s_3927_){
_start:
{
lean_object* v_newEntries_3928_; lean_object* v___x_3929_; lean_object* v___x_3930_; lean_object* v___x_3931_; 
v_newEntries_3928_ = lean_ctor_get(v_s_3927_, 0);
lean_inc(v_newEntries_3928_);
lean_dec_ref(v_s_3927_);
v___x_3929_ = l_List_reverse___redArg(v_newEntries_3928_);
v___x_3930_ = lean_array_mk(v___x_3929_);
lean_inc_ref_n(v___x_3930_, 2);
v___x_3931_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3931_, 0, v___x_3930_);
lean_ctor_set(v___x_3931_, 1, v___x_3930_);
lean_ctor_set(v___x_3931_, 2, v___x_3930_);
return v___x_3931_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn___lam__0_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2____boxed(lean_object* v_x_3932_, lean_object* v_s_3933_){
_start:
{
lean_object* v_res_3934_; 
v_res_3934_ = l___private_Lean_Attributes_0__Lean_initFn___lam__0_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(v_x_3932_, v_s_3933_);
lean_dec_ref(v_x_3932_);
return v_res_3934_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn___lam__1_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(lean_object* v_s_3935_){
_start:
{
lean_object* v_newEntries_3936_; lean_object* v___x_3938_; uint8_t v_isShared_3939_; uint8_t v_isSharedCheck_3947_; 
v_newEntries_3936_ = lean_ctor_get(v_s_3935_, 0);
v_isSharedCheck_3947_ = !lean_is_exclusive(v_s_3935_);
if (v_isSharedCheck_3947_ == 0)
{
lean_object* v_unused_3948_; 
v_unused_3948_ = lean_ctor_get(v_s_3935_, 1);
lean_dec(v_unused_3948_);
v___x_3938_ = v_s_3935_;
v_isShared_3939_ = v_isSharedCheck_3947_;
goto v_resetjp_3937_;
}
else
{
lean_inc(v_newEntries_3936_);
lean_dec(v_s_3935_);
v___x_3938_ = lean_box(0);
v_isShared_3939_ = v_isSharedCheck_3947_;
goto v_resetjp_3937_;
}
v_resetjp_3937_:
{
lean_object* v___x_3940_; lean_object* v___x_3941_; lean_object* v___x_3942_; lean_object* v___x_3943_; lean_object* v___x_3945_; 
v___x_3940_ = ((lean_object*)(l_Lean_registerTagAttribute___lam__2___closed__4));
v___x_3941_ = l_List_lengthTR___redArg(v_newEntries_3936_);
lean_dec(v_newEntries_3936_);
v___x_3942_ = l_Nat_reprFast(v___x_3941_);
v___x_3943_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3943_, 0, v___x_3942_);
if (v_isShared_3939_ == 0)
{
lean_ctor_set_tag(v___x_3938_, 5);
lean_ctor_set(v___x_3938_, 1, v___x_3943_);
lean_ctor_set(v___x_3938_, 0, v___x_3940_);
v___x_3945_ = v___x_3938_;
goto v_reusejp_3944_;
}
else
{
lean_object* v_reuseFailAlloc_3946_; 
v_reuseFailAlloc_3946_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3946_, 0, v___x_3940_);
lean_ctor_set(v_reuseFailAlloc_3946_, 1, v___x_3943_);
v___x_3945_ = v_reuseFailAlloc_3946_;
goto v_reusejp_3944_;
}
v_reusejp_3944_:
{
return v___x_3945_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn___lam__2_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(lean_object* v_s_3949_){
_start:
{
lean_object* v_newEntries_3950_; lean_object* v___x_3951_; lean_object* v___x_3952_; 
v_newEntries_3950_ = lean_ctor_get(v_s_3949_, 0);
lean_inc(v_newEntries_3950_);
lean_dec_ref(v_s_3949_);
v___x_3951_ = l_List_reverse___redArg(v_newEntries_3950_);
v___x_3952_ = lean_array_mk(v___x_3951_);
return v___x_3952_;
}
}
static lean_object* _init_l___private_Lean_Attributes_0__Lean_initFn___closed__7_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3962_; lean_object* v___x_3963_; lean_object* v___f_3964_; lean_object* v___f_3965_; lean_object* v___x_3966_; lean_object* v___x_3967_; lean_object* v___x_3968_; lean_object* v___x_3969_; lean_object* v___x_3970_; 
v___x_3962_ = lean_box(0);
v___x_3963_ = lean_box(2);
v___f_3964_ = ((lean_object*)(l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___f_3965_ = ((lean_object*)(l___private_Lean_Attributes_0__Lean_initFn___closed__0_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___x_3966_ = ((lean_object*)(l___private_Lean_Attributes_0__Lean_initFn___closed__6_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___x_3967_ = ((lean_object*)(l___private_Lean_Attributes_0__Lean_initFn___closed__5_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___x_3968_ = lean_alloc_closure((void*)(l___private_Lean_Attributes_0__Lean_AttributeExtension_mkInitial___boxed), 1, 0);
v___x_3969_ = ((lean_object*)(l___private_Lean_Attributes_0__Lean_initFn___closed__4_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___x_3970_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_3970_, 0, v___x_3969_);
lean_ctor_set(v___x_3970_, 1, v___x_3968_);
lean_ctor_set(v___x_3970_, 2, v___x_3967_);
lean_ctor_set(v___x_3970_, 3, v___x_3966_);
lean_ctor_set(v___x_3970_, 4, v___f_3965_);
lean_ctor_set(v___x_3970_, 5, v___f_3964_);
lean_ctor_set(v___x_3970_, 6, v___x_3963_);
lean_ctor_set(v___x_3970_, 7, v___x_3962_);
return v___x_3970_;
}
}
static lean_object* _init_l___private_Lean_Attributes_0__Lean_initFn___closed__8_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_3971_; lean_object* v___x_3972_; lean_object* v___x_3973_; 
v___f_3971_ = ((lean_object*)(l___private_Lean_Attributes_0__Lean_initFn___closed__2_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___x_3972_ = lean_obj_once(&l___private_Lean_Attributes_0__Lean_initFn___closed__7_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_, &l___private_Lean_Attributes_0__Lean_initFn___closed__7_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2__once, _init_l___private_Lean_Attributes_0__Lean_initFn___closed__7_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_);
v___x_3973_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3973_, 0, v___x_3972_);
lean_ctor_set(v___x_3973_, 1, v___f_3971_);
return v___x_3973_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3975_; lean_object* v___x_3976_; 
v___x_3975_ = lean_obj_once(&l___private_Lean_Attributes_0__Lean_initFn___closed__8_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_, &l___private_Lean_Attributes_0__Lean_initFn___closed__8_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2__once, _init_l___private_Lean_Attributes_0__Lean_initFn___closed__8_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_);
v___x_3976_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_3975_);
return v___x_3976_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2____boxed(lean_object* v_a_3977_){
_start:
{
lean_object* v_res_3978_; 
v_res_3978_ = l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_();
return v_res_3978_;
}
}
LEAN_EXPORT lean_object* lean_is_attribute(lean_object* v_n_3979_){
_start:
{
lean_object* v___x_3981_; lean_object* v___x_3982_; uint8_t v___x_3983_; lean_object* v___x_3984_; lean_object* v___x_3985_; 
v___x_3981_ = l_Lean_attributeMapRef;
v___x_3982_ = lean_st_ref_get(v___x_3981_);
v___x_3983_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(v___x_3982_, v_n_3979_);
lean_dec(v_n_3979_);
lean_dec(v___x_3982_);
v___x_3984_ = lean_box(v___x_3983_);
v___x_3985_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3985_, 0, v___x_3984_);
return v___x_3985_;
}
}
LEAN_EXPORT lean_object* l_Lean_isBuiltinAttribute___boxed(lean_object* v_n_3986_, lean_object* v_a_3987_){
_start:
{
lean_object* v_res_3988_; 
v_res_3988_ = lean_is_attribute(v_n_3986_);
return v_res_3988_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_getBuiltinAttributeNames_spec__0(lean_object* v_x_3989_, lean_object* v_x_3990_){
_start:
{
if (lean_obj_tag(v_x_3990_) == 0)
{
return v_x_3989_;
}
else
{
lean_object* v_key_3991_; lean_object* v_tail_3992_; lean_object* v___x_3993_; 
v_key_3991_ = lean_ctor_get(v_x_3990_, 0);
v_tail_3992_ = lean_ctor_get(v_x_3990_, 2);
lean_inc(v_key_3991_);
v___x_3993_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3993_, 0, v_key_3991_);
lean_ctor_set(v___x_3993_, 1, v_x_3989_);
v_x_3989_ = v___x_3993_;
v_x_3990_ = v_tail_3992_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_getBuiltinAttributeNames_spec__0___boxed(lean_object* v_x_3995_, lean_object* v_x_3996_){
_start:
{
lean_object* v_res_3997_; 
v_res_3997_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_getBuiltinAttributeNames_spec__0(v_x_3995_, v_x_3996_);
lean_dec(v_x_3996_);
return v_res_3997_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1(lean_object* v_as_3998_, size_t v_i_3999_, size_t v_stop_4000_, lean_object* v_b_4001_){
_start:
{
uint8_t v___x_4002_; 
v___x_4002_ = lean_usize_dec_eq(v_i_3999_, v_stop_4000_);
if (v___x_4002_ == 0)
{
lean_object* v___x_4003_; lean_object* v___x_4004_; size_t v___x_4005_; size_t v___x_4006_; 
v___x_4003_ = lean_array_uget_borrowed(v_as_3998_, v_i_3999_);
v___x_4004_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_getBuiltinAttributeNames_spec__0(v_b_4001_, v___x_4003_);
v___x_4005_ = ((size_t)1ULL);
v___x_4006_ = lean_usize_add(v_i_3999_, v___x_4005_);
v_i_3999_ = v___x_4006_;
v_b_4001_ = v___x_4004_;
goto _start;
}
else
{
return v_b_4001_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1___boxed(lean_object* v_as_4008_, lean_object* v_i_4009_, lean_object* v_stop_4010_, lean_object* v_b_4011_){
_start:
{
size_t v_i_boxed_4012_; size_t v_stop_boxed_4013_; lean_object* v_res_4014_; 
v_i_boxed_4012_ = lean_unbox_usize(v_i_4009_);
lean_dec(v_i_4009_);
v_stop_boxed_4013_ = lean_unbox_usize(v_stop_4010_);
lean_dec(v_stop_4010_);
v_res_4014_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1(v_as_4008_, v_i_boxed_4012_, v_stop_boxed_4013_, v_b_4011_);
lean_dec_ref(v_as_4008_);
return v_res_4014_;
}
}
LEAN_EXPORT lean_object* l_Lean_getBuiltinAttributeNames(){
_start:
{
lean_object* v___x_4016_; lean_object* v___x_4017_; lean_object* v_buckets_4018_; lean_object* v___x_4019_; lean_object* v___x_4020_; lean_object* v___x_4021_; uint8_t v___x_4022_; 
v___x_4016_ = l_Lean_attributeMapRef;
v___x_4017_ = lean_st_ref_get(v___x_4016_);
v_buckets_4018_ = lean_ctor_get(v___x_4017_, 1);
lean_inc_ref(v_buckets_4018_);
lean_dec(v___x_4017_);
v___x_4019_ = lean_box(0);
v___x_4020_ = lean_unsigned_to_nat(0u);
v___x_4021_ = lean_array_get_size(v_buckets_4018_);
v___x_4022_ = lean_nat_dec_lt(v___x_4020_, v___x_4021_);
if (v___x_4022_ == 0)
{
lean_object* v___x_4023_; 
lean_dec_ref(v_buckets_4018_);
v___x_4023_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4023_, 0, v___x_4019_);
return v___x_4023_;
}
else
{
uint8_t v___x_4024_; 
v___x_4024_ = lean_nat_dec_le(v___x_4021_, v___x_4021_);
if (v___x_4024_ == 0)
{
if (v___x_4022_ == 0)
{
lean_object* v___x_4025_; 
lean_dec_ref(v_buckets_4018_);
v___x_4025_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4025_, 0, v___x_4019_);
return v___x_4025_;
}
else
{
size_t v___x_4026_; size_t v___x_4027_; lean_object* v___x_4028_; lean_object* v___x_4029_; 
v___x_4026_ = ((size_t)0ULL);
v___x_4027_ = lean_usize_of_nat(v___x_4021_);
v___x_4028_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1(v_buckets_4018_, v___x_4026_, v___x_4027_, v___x_4019_);
lean_dec_ref(v_buckets_4018_);
v___x_4029_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4029_, 0, v___x_4028_);
return v___x_4029_;
}
}
else
{
size_t v___x_4030_; size_t v___x_4031_; lean_object* v___x_4032_; lean_object* v___x_4033_; 
v___x_4030_ = ((size_t)0ULL);
v___x_4031_ = lean_usize_of_nat(v___x_4021_);
v___x_4032_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1(v_buckets_4018_, v___x_4030_, v___x_4031_, v___x_4019_);
lean_dec_ref(v_buckets_4018_);
v___x_4033_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4033_, 0, v___x_4032_);
return v___x_4033_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getBuiltinAttributeNames___boxed(lean_object* v_a_4034_){
_start:
{
lean_object* v_res_4035_; 
v_res_4035_ = l_Lean_getBuiltinAttributeNames();
return v_res_4035_;
}
}
LEAN_EXPORT lean_object* l_Lean_getBuiltinAttributeImpl(lean_object* v_attrName_4037_){
_start:
{
lean_object* v___x_4039_; lean_object* v___x_4040_; lean_object* v___x_4041_; 
v___x_4039_ = l_Lean_attributeMapRef;
v___x_4040_ = lean_st_ref_get(v___x_4039_);
v___x_4041_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(v___x_4040_, v_attrName_4037_);
lean_dec(v___x_4040_);
if (lean_obj_tag(v___x_4041_) == 0)
{
lean_object* v___x_4042_; uint8_t v___x_4043_; lean_object* v___x_4044_; lean_object* v___x_4045_; lean_object* v___x_4046_; lean_object* v___x_4047_; lean_object* v___x_4048_; lean_object* v___x_4049_; 
v___x_4042_ = ((lean_object*)(l_Lean_getBuiltinAttributeImpl___closed__0));
v___x_4043_ = 1;
v___x_4044_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_attrName_4037_, v___x_4043_);
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
lean_object* v_val_4050_; lean_object* v___x_4052_; uint8_t v_isShared_4053_; uint8_t v_isSharedCheck_4057_; 
lean_dec(v_attrName_4037_);
v_val_4050_ = lean_ctor_get(v___x_4041_, 0);
v_isSharedCheck_4057_ = !lean_is_exclusive(v___x_4041_);
if (v_isSharedCheck_4057_ == 0)
{
v___x_4052_ = v___x_4041_;
v_isShared_4053_ = v_isSharedCheck_4057_;
goto v_resetjp_4051_;
}
else
{
lean_inc(v_val_4050_);
lean_dec(v___x_4041_);
v___x_4052_ = lean_box(0);
v_isShared_4053_ = v_isSharedCheck_4057_;
goto v_resetjp_4051_;
}
v_resetjp_4051_:
{
lean_object* v___x_4055_; 
if (v_isShared_4053_ == 0)
{
lean_ctor_set_tag(v___x_4052_, 0);
v___x_4055_ = v___x_4052_;
goto v_reusejp_4054_;
}
else
{
lean_object* v_reuseFailAlloc_4056_; 
v_reuseFailAlloc_4056_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4056_, 0, v_val_4050_);
v___x_4055_ = v_reuseFailAlloc_4056_;
goto v_reusejp_4054_;
}
v_reusejp_4054_:
{
return v___x_4055_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getBuiltinAttributeImpl___boxed(lean_object* v_attrName_4058_, lean_object* v_a_4059_){
_start:
{
lean_object* v_res_4060_; 
v_res_4060_ = l_Lean_getBuiltinAttributeImpl(v_attrName_4058_);
return v_res_4060_;
}
}
LEAN_EXPORT lean_object* lean_attribute_application_time(lean_object* v_n_4061_){
_start:
{
lean_object* v___x_4063_; 
v___x_4063_ = l_Lean_getBuiltinAttributeImpl(v_n_4061_);
if (lean_obj_tag(v___x_4063_) == 0)
{
lean_object* v_a_4064_; lean_object* v___x_4066_; uint8_t v_isShared_4067_; uint8_t v_isSharedCheck_4074_; 
v_a_4064_ = lean_ctor_get(v___x_4063_, 0);
v_isSharedCheck_4074_ = !lean_is_exclusive(v___x_4063_);
if (v_isSharedCheck_4074_ == 0)
{
v___x_4066_ = v___x_4063_;
v_isShared_4067_ = v_isSharedCheck_4074_;
goto v_resetjp_4065_;
}
else
{
lean_inc(v_a_4064_);
lean_dec(v___x_4063_);
v___x_4066_ = lean_box(0);
v_isShared_4067_ = v_isSharedCheck_4074_;
goto v_resetjp_4065_;
}
v_resetjp_4065_:
{
lean_object* v_toAttributeImplCore_4068_; uint8_t v_applicationTime_4069_; lean_object* v___x_4070_; lean_object* v___x_4072_; 
v_toAttributeImplCore_4068_ = lean_ctor_get(v_a_4064_, 0);
lean_inc_ref(v_toAttributeImplCore_4068_);
lean_dec(v_a_4064_);
v_applicationTime_4069_ = lean_ctor_get_uint8(v_toAttributeImplCore_4068_, sizeof(void*)*3);
lean_dec_ref(v_toAttributeImplCore_4068_);
v___x_4070_ = lean_box(v_applicationTime_4069_);
if (v_isShared_4067_ == 0)
{
lean_ctor_set(v___x_4066_, 0, v___x_4070_);
v___x_4072_ = v___x_4066_;
goto v_reusejp_4071_;
}
else
{
lean_object* v_reuseFailAlloc_4073_; 
v_reuseFailAlloc_4073_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4073_, 0, v___x_4070_);
v___x_4072_ = v_reuseFailAlloc_4073_;
goto v_reusejp_4071_;
}
v_reusejp_4071_:
{
return v___x_4072_;
}
}
}
else
{
lean_object* v_a_4075_; lean_object* v___x_4077_; uint8_t v_isShared_4078_; uint8_t v_isSharedCheck_4082_; 
v_a_4075_ = lean_ctor_get(v___x_4063_, 0);
v_isSharedCheck_4082_ = !lean_is_exclusive(v___x_4063_);
if (v_isSharedCheck_4082_ == 0)
{
v___x_4077_ = v___x_4063_;
v_isShared_4078_ = v_isSharedCheck_4082_;
goto v_resetjp_4076_;
}
else
{
lean_inc(v_a_4075_);
lean_dec(v___x_4063_);
v___x_4077_ = lean_box(0);
v_isShared_4078_ = v_isSharedCheck_4082_;
goto v_resetjp_4076_;
}
v_resetjp_4076_:
{
lean_object* v___x_4080_; 
if (v_isShared_4078_ == 0)
{
v___x_4080_ = v___x_4077_;
goto v_reusejp_4079_;
}
else
{
lean_object* v_reuseFailAlloc_4081_; 
v_reuseFailAlloc_4081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4081_, 0, v_a_4075_);
v___x_4080_ = v_reuseFailAlloc_4081_;
goto v_reusejp_4079_;
}
v_reusejp_4079_:
{
return v___x_4080_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getBuiltinAttributeApplicationTime___boxed(lean_object* v_n_4083_, lean_object* v_a_4084_){
_start:
{
lean_object* v_res_4085_; 
v_res_4085_ = lean_attribute_application_time(v_n_4083_);
return v_res_4085_;
}
}
LEAN_EXPORT uint8_t l_Lean_isAttribute(lean_object* v_env_4086_, lean_object* v_attrName_4087_){
_start:
{
lean_object* v___x_4088_; lean_object* v_toEnvExtension_4089_; lean_object* v_asyncMode_4090_; lean_object* v___x_4091_; lean_object* v___x_4092_; lean_object* v___x_4093_; lean_object* v_map_4094_; uint8_t v___x_4095_; 
v___x_4088_ = l_Lean_attributeExtension;
v_toEnvExtension_4089_ = lean_ctor_get(v___x_4088_, 0);
v_asyncMode_4090_ = lean_ctor_get(v_toEnvExtension_4089_, 2);
v___x_4091_ = l_Lean_instInhabitedAttributeExtensionState_default;
v___x_4092_ = lean_box(0);
v___x_4093_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_4091_, v___x_4088_, v_env_4086_, v_asyncMode_4090_, v___x_4092_);
v_map_4094_ = lean_ctor_get(v___x_4093_, 1);
lean_inc_ref(v_map_4094_);
lean_dec(v___x_4093_);
v___x_4095_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(v_map_4094_, v_attrName_4087_);
lean_dec_ref(v_map_4094_);
return v___x_4095_;
}
}
LEAN_EXPORT lean_object* l_Lean_isAttribute___boxed(lean_object* v_env_4096_, lean_object* v_attrName_4097_){
_start:
{
uint8_t v_res_4098_; lean_object* v_r_4099_; 
v_res_4098_ = l_Lean_isAttribute(v_env_4096_, v_attrName_4097_);
lean_dec(v_attrName_4097_);
v_r_4099_ = lean_box(v_res_4098_);
return v_r_4099_;
}
}
LEAN_EXPORT lean_object* l_Lean_getAttributeNames(lean_object* v_env_4100_){
_start:
{
lean_object* v___x_4101_; lean_object* v_toEnvExtension_4102_; lean_object* v_asyncMode_4103_; lean_object* v___x_4104_; lean_object* v___x_4105_; lean_object* v___x_4106_; lean_object* v_map_4107_; lean_object* v_buckets_4108_; lean_object* v___x_4109_; lean_object* v___x_4110_; lean_object* v___x_4111_; uint8_t v___x_4112_; 
v___x_4101_ = l_Lean_attributeExtension;
v_toEnvExtension_4102_ = lean_ctor_get(v___x_4101_, 0);
v_asyncMode_4103_ = lean_ctor_get(v_toEnvExtension_4102_, 2);
v___x_4104_ = l_Lean_instInhabitedAttributeExtensionState_default;
v___x_4105_ = lean_box(0);
v___x_4106_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_4104_, v___x_4101_, v_env_4100_, v_asyncMode_4103_, v___x_4105_);
v_map_4107_ = lean_ctor_get(v___x_4106_, 1);
lean_inc_ref(v_map_4107_);
lean_dec(v___x_4106_);
v_buckets_4108_ = lean_ctor_get(v_map_4107_, 1);
lean_inc_ref(v_buckets_4108_);
lean_dec_ref(v_map_4107_);
v___x_4109_ = lean_box(0);
v___x_4110_ = lean_unsigned_to_nat(0u);
v___x_4111_ = lean_array_get_size(v_buckets_4108_);
v___x_4112_ = lean_nat_dec_lt(v___x_4110_, v___x_4111_);
if (v___x_4112_ == 0)
{
lean_dec_ref(v_buckets_4108_);
return v___x_4109_;
}
else
{
uint8_t v___x_4113_; 
v___x_4113_ = lean_nat_dec_le(v___x_4111_, v___x_4111_);
if (v___x_4113_ == 0)
{
if (v___x_4112_ == 0)
{
lean_dec_ref(v_buckets_4108_);
return v___x_4109_;
}
else
{
size_t v___x_4114_; size_t v___x_4115_; lean_object* v___x_4116_; 
v___x_4114_ = ((size_t)0ULL);
v___x_4115_ = lean_usize_of_nat(v___x_4111_);
v___x_4116_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1(v_buckets_4108_, v___x_4114_, v___x_4115_, v___x_4109_);
lean_dec_ref(v_buckets_4108_);
return v___x_4116_;
}
}
else
{
size_t v___x_4117_; size_t v___x_4118_; lean_object* v___x_4119_; 
v___x_4117_ = ((size_t)0ULL);
v___x_4118_ = lean_usize_of_nat(v___x_4111_);
v___x_4119_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1(v_buckets_4108_, v___x_4117_, v___x_4118_, v___x_4109_);
lean_dec_ref(v_buckets_4108_);
return v___x_4119_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getAttributeImpl(lean_object* v_env_4120_, lean_object* v_attrName_4121_){
_start:
{
lean_object* v___x_4122_; lean_object* v_toEnvExtension_4123_; lean_object* v_asyncMode_4124_; lean_object* v___x_4125_; lean_object* v___x_4126_; lean_object* v___x_4127_; lean_object* v_map_4128_; lean_object* v___x_4129_; 
v___x_4122_ = l_Lean_attributeExtension;
v_toEnvExtension_4123_ = lean_ctor_get(v___x_4122_, 0);
v_asyncMode_4124_ = lean_ctor_get(v_toEnvExtension_4123_, 2);
v___x_4125_ = l_Lean_instInhabitedAttributeExtensionState_default;
v___x_4126_ = lean_box(0);
v___x_4127_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_4125_, v___x_4122_, v_env_4120_, v_asyncMode_4124_, v___x_4126_);
v_map_4128_ = lean_ctor_get(v___x_4127_, 1);
lean_inc_ref(v_map_4128_);
lean_dec(v___x_4127_);
v___x_4129_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(v_map_4128_, v_attrName_4121_);
lean_dec_ref(v_map_4128_);
if (lean_obj_tag(v___x_4129_) == 0)
{
lean_object* v___x_4130_; uint8_t v___x_4131_; lean_object* v___x_4132_; lean_object* v___x_4133_; lean_object* v___x_4134_; lean_object* v___x_4135_; lean_object* v___x_4136_; 
v___x_4130_ = ((lean_object*)(l_Lean_getBuiltinAttributeImpl___closed__0));
v___x_4131_ = 1;
v___x_4132_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_attrName_4121_, v___x_4131_);
v___x_4133_ = lean_string_append(v___x_4130_, v___x_4132_);
lean_dec_ref(v___x_4132_);
v___x_4134_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__4));
v___x_4135_ = lean_string_append(v___x_4133_, v___x_4134_);
v___x_4136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4136_, 0, v___x_4135_);
return v___x_4136_;
}
else
{
lean_object* v_val_4137_; lean_object* v___x_4139_; uint8_t v_isShared_4140_; uint8_t v_isSharedCheck_4144_; 
lean_dec(v_attrName_4121_);
v_val_4137_ = lean_ctor_get(v___x_4129_, 0);
v_isSharedCheck_4144_ = !lean_is_exclusive(v___x_4129_);
if (v_isSharedCheck_4144_ == 0)
{
v___x_4139_ = v___x_4129_;
v_isShared_4140_ = v_isSharedCheck_4144_;
goto v_resetjp_4138_;
}
else
{
lean_inc(v_val_4137_);
lean_dec(v___x_4129_);
v___x_4139_ = lean_box(0);
v_isShared_4140_ = v_isSharedCheck_4144_;
goto v_resetjp_4138_;
}
v_resetjp_4138_:
{
lean_object* v___x_4142_; 
if (v_isShared_4140_ == 0)
{
v___x_4142_ = v___x_4139_;
goto v_reusejp_4141_;
}
else
{
lean_object* v_reuseFailAlloc_4143_; 
v_reuseFailAlloc_4143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4143_, 0, v_val_4137_);
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
LEAN_EXPORT lean_object* l_Lean_registerAttributeOfBuilder(lean_object* v_env_4145_, lean_object* v_builderId_4146_, lean_object* v_ref_4147_, lean_object* v_args_4148_){
_start:
{
lean_object* v_entry_4150_; lean_object* v___x_4151_; 
v_entry_4150_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_entry_4150_, 0, v_builderId_4146_);
lean_ctor_set(v_entry_4150_, 1, v_ref_4147_);
lean_ctor_set(v_entry_4150_, 2, v_args_4148_);
lean_inc_ref(v_entry_4150_);
v___x_4151_ = l_Lean_mkAttributeImplOfEntry(v_entry_4150_);
if (lean_obj_tag(v___x_4151_) == 0)
{
lean_object* v_a_4152_; lean_object* v___x_4154_; uint8_t v_isShared_4155_; uint8_t v_isSharedCheck_4177_; 
v_a_4152_ = lean_ctor_get(v___x_4151_, 0);
v_isSharedCheck_4177_ = !lean_is_exclusive(v___x_4151_);
if (v_isSharedCheck_4177_ == 0)
{
v___x_4154_ = v___x_4151_;
v_isShared_4155_ = v_isSharedCheck_4177_;
goto v_resetjp_4153_;
}
else
{
lean_inc(v_a_4152_);
lean_dec(v___x_4151_);
v___x_4154_ = lean_box(0);
v_isShared_4155_ = v_isSharedCheck_4177_;
goto v_resetjp_4153_;
}
v_resetjp_4153_:
{
lean_object* v_toAttributeImplCore_4156_; lean_object* v_name_4157_; uint8_t v___x_4158_; 
v_toAttributeImplCore_4156_ = lean_ctor_get(v_a_4152_, 0);
v_name_4157_ = lean_ctor_get(v_toAttributeImplCore_4156_, 1);
lean_inc_ref(v_env_4145_);
v___x_4158_ = l_Lean_isAttribute(v_env_4145_, v_name_4157_);
if (v___x_4158_ == 0)
{
lean_object* v___x_4159_; lean_object* v_toEnvExtension_4160_; lean_object* v_asyncMode_4161_; lean_object* v___x_4162_; lean_object* v___x_4163_; lean_object* v___x_4164_; lean_object* v___x_4166_; 
v___x_4159_ = l_Lean_attributeExtension;
v_toEnvExtension_4160_ = lean_ctor_get(v___x_4159_, 0);
v_asyncMode_4161_ = lean_ctor_get(v_toEnvExtension_4160_, 2);
v___x_4162_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4162_, 0, v_entry_4150_);
lean_ctor_set(v___x_4162_, 1, v_a_4152_);
v___x_4163_ = lean_box(0);
v___x_4164_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_4159_, v_env_4145_, v___x_4162_, v_asyncMode_4161_, v___x_4163_);
if (v_isShared_4155_ == 0)
{
lean_ctor_set(v___x_4154_, 0, v___x_4164_);
v___x_4166_ = v___x_4154_;
goto v_reusejp_4165_;
}
else
{
lean_object* v_reuseFailAlloc_4167_; 
v_reuseFailAlloc_4167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4167_, 0, v___x_4164_);
v___x_4166_ = v_reuseFailAlloc_4167_;
goto v_reusejp_4165_;
}
v_reusejp_4165_:
{
return v___x_4166_;
}
}
else
{
lean_object* v___x_4168_; lean_object* v___x_4169_; lean_object* v___x_4170_; lean_object* v___x_4171_; lean_object* v___x_4172_; lean_object* v___x_4173_; lean_object* v___x_4175_; 
lean_inc(v_name_4157_);
lean_dec(v_a_4152_);
lean_dec_ref(v_entry_4150_);
lean_dec_ref(v_env_4145_);
v___x_4168_ = ((lean_object*)(l_Lean_registerBuiltinAttribute___closed__2));
v___x_4169_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_4157_, v___x_4158_);
v___x_4170_ = lean_string_append(v___x_4168_, v___x_4169_);
lean_dec_ref(v___x_4169_);
v___x_4171_ = ((lean_object*)(l_Lean_registerBuiltinAttribute___closed__3));
v___x_4172_ = lean_string_append(v___x_4170_, v___x_4171_);
v___x_4173_ = lean_mk_io_user_error(v___x_4172_);
if (v_isShared_4155_ == 0)
{
lean_ctor_set_tag(v___x_4154_, 1);
lean_ctor_set(v___x_4154_, 0, v___x_4173_);
v___x_4175_ = v___x_4154_;
goto v_reusejp_4174_;
}
else
{
lean_object* v_reuseFailAlloc_4176_; 
v_reuseFailAlloc_4176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4176_, 0, v___x_4173_);
v___x_4175_ = v_reuseFailAlloc_4176_;
goto v_reusejp_4174_;
}
v_reusejp_4174_:
{
return v___x_4175_;
}
}
}
}
else
{
lean_object* v_a_4178_; lean_object* v___x_4180_; uint8_t v_isShared_4181_; uint8_t v_isSharedCheck_4185_; 
lean_dec_ref(v_entry_4150_);
lean_dec_ref(v_env_4145_);
v_a_4178_ = lean_ctor_get(v___x_4151_, 0);
v_isSharedCheck_4185_ = !lean_is_exclusive(v___x_4151_);
if (v_isSharedCheck_4185_ == 0)
{
v___x_4180_ = v___x_4151_;
v_isShared_4181_ = v_isSharedCheck_4185_;
goto v_resetjp_4179_;
}
else
{
lean_inc(v_a_4178_);
lean_dec(v___x_4151_);
v___x_4180_ = lean_box(0);
v_isShared_4181_ = v_isSharedCheck_4185_;
goto v_resetjp_4179_;
}
v_resetjp_4179_:
{
lean_object* v___x_4183_; 
if (v_isShared_4181_ == 0)
{
v___x_4183_ = v___x_4180_;
goto v_reusejp_4182_;
}
else
{
lean_object* v_reuseFailAlloc_4184_; 
v_reuseFailAlloc_4184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4184_, 0, v_a_4178_);
v___x_4183_ = v_reuseFailAlloc_4184_;
goto v_reusejp_4182_;
}
v_reusejp_4182_:
{
return v___x_4183_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerAttributeOfBuilder___boxed(lean_object* v_env_4186_, lean_object* v_builderId_4187_, lean_object* v_ref_4188_, lean_object* v_args_4189_, lean_object* v_a_4190_){
_start:
{
lean_object* v_res_4191_; 
v_res_4191_ = l_Lean_registerAttributeOfBuilder(v_env_4186_, v_builderId_4187_, v_ref_4188_, v_args_4189_);
return v_res_4191_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg(lean_object* v_x_4192_, lean_object* v___y_4193_, lean_object* v___y_4194_){
_start:
{
if (lean_obj_tag(v_x_4192_) == 0)
{
lean_object* v_a_4196_; lean_object* v___x_4197_; lean_object* v___x_4198_; 
v_a_4196_ = lean_ctor_get(v_x_4192_, 0);
lean_inc(v_a_4196_);
lean_dec_ref(v_x_4192_);
v___x_4197_ = l_Lean_stringToMessageData(v_a_4196_);
v___x_4198_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0_spec__0___redArg(v___x_4197_, v___y_4193_, v___y_4194_);
return v___x_4198_;
}
else
{
lean_object* v_a_4199_; lean_object* v___x_4201_; uint8_t v_isShared_4202_; uint8_t v_isSharedCheck_4206_; 
v_a_4199_ = lean_ctor_get(v_x_4192_, 0);
v_isSharedCheck_4206_ = !lean_is_exclusive(v_x_4192_);
if (v_isSharedCheck_4206_ == 0)
{
v___x_4201_ = v_x_4192_;
v_isShared_4202_ = v_isSharedCheck_4206_;
goto v_resetjp_4200_;
}
else
{
lean_inc(v_a_4199_);
lean_dec(v_x_4192_);
v___x_4201_ = lean_box(0);
v_isShared_4202_ = v_isSharedCheck_4206_;
goto v_resetjp_4200_;
}
v_resetjp_4200_:
{
lean_object* v___x_4204_; 
if (v_isShared_4202_ == 0)
{
lean_ctor_set_tag(v___x_4201_, 0);
v___x_4204_ = v___x_4201_;
goto v_reusejp_4203_;
}
else
{
lean_object* v_reuseFailAlloc_4205_; 
v_reuseFailAlloc_4205_ = lean_alloc_ctor(0, 1, 0);
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
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg___boxed(lean_object* v_x_4207_, lean_object* v___y_4208_, lean_object* v___y_4209_, lean_object* v___y_4210_){
_start:
{
lean_object* v_res_4211_; 
v_res_4211_ = l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg(v_x_4207_, v___y_4208_, v___y_4209_);
lean_dec(v___y_4209_);
lean_dec_ref(v___y_4208_);
return v_res_4211_;
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_add(lean_object* v_declName_4212_, lean_object* v_attrName_4213_, lean_object* v_stx_4214_, uint8_t v_kind_4215_, lean_object* v_a_4216_, lean_object* v_a_4217_){
_start:
{
lean_object* v___x_4219_; lean_object* v_env_4220_; lean_object* v___x_4221_; lean_object* v___x_4222_; 
v___x_4219_ = lean_st_ref_get(v_a_4217_);
v_env_4220_ = lean_ctor_get(v___x_4219_, 0);
lean_inc_ref(v_env_4220_);
lean_dec(v___x_4219_);
v___x_4221_ = l_Lean_getAttributeImpl(v_env_4220_, v_attrName_4213_);
v___x_4222_ = l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg(v___x_4221_, v_a_4216_, v_a_4217_);
if (lean_obj_tag(v___x_4222_) == 0)
{
lean_object* v_a_4223_; lean_object* v_add_4224_; lean_object* v___x_4225_; lean_object* v___x_4226_; 
v_a_4223_ = lean_ctor_get(v___x_4222_, 0);
lean_inc(v_a_4223_);
lean_dec_ref(v___x_4222_);
v_add_4224_ = lean_ctor_get(v_a_4223_, 1);
lean_inc_ref(v_add_4224_);
lean_dec(v_a_4223_);
v___x_4225_ = lean_box(v_kind_4215_);
lean_inc(v_a_4217_);
lean_inc_ref(v_a_4216_);
v___x_4226_ = lean_apply_6(v_add_4224_, v_declName_4212_, v_stx_4214_, v___x_4225_, v_a_4216_, v_a_4217_, lean_box(0));
return v___x_4226_;
}
else
{
lean_object* v_a_4227_; lean_object* v___x_4229_; uint8_t v_isShared_4230_; uint8_t v_isSharedCheck_4234_; 
lean_dec(v_stx_4214_);
lean_dec(v_declName_4212_);
v_a_4227_ = lean_ctor_get(v___x_4222_, 0);
v_isSharedCheck_4234_ = !lean_is_exclusive(v___x_4222_);
if (v_isSharedCheck_4234_ == 0)
{
v___x_4229_ = v___x_4222_;
v_isShared_4230_ = v_isSharedCheck_4234_;
goto v_resetjp_4228_;
}
else
{
lean_inc(v_a_4227_);
lean_dec(v___x_4222_);
v___x_4229_ = lean_box(0);
v_isShared_4230_ = v_isSharedCheck_4234_;
goto v_resetjp_4228_;
}
v_resetjp_4228_:
{
lean_object* v___x_4232_; 
if (v_isShared_4230_ == 0)
{
v___x_4232_ = v___x_4229_;
goto v_reusejp_4231_;
}
else
{
lean_object* v_reuseFailAlloc_4233_; 
v_reuseFailAlloc_4233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4233_, 0, v_a_4227_);
v___x_4232_ = v_reuseFailAlloc_4233_;
goto v_reusejp_4231_;
}
v_reusejp_4231_:
{
return v___x_4232_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_add___boxed(lean_object* v_declName_4235_, lean_object* v_attrName_4236_, lean_object* v_stx_4237_, lean_object* v_kind_4238_, lean_object* v_a_4239_, lean_object* v_a_4240_, lean_object* v_a_4241_){
_start:
{
uint8_t v_kind_boxed_4242_; lean_object* v_res_4243_; 
v_kind_boxed_4242_ = lean_unbox(v_kind_4238_);
v_res_4243_ = l_Lean_Attribute_add(v_declName_4235_, v_attrName_4236_, v_stx_4237_, v_kind_boxed_4242_, v_a_4239_, v_a_4240_);
lean_dec(v_a_4240_);
lean_dec_ref(v_a_4239_);
return v_res_4243_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0(lean_object* v_00_u03b1_4244_, lean_object* v_x_4245_, lean_object* v___y_4246_, lean_object* v___y_4247_){
_start:
{
lean_object* v___x_4249_; 
v___x_4249_ = l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg(v_x_4245_, v___y_4246_, v___y_4247_);
return v___x_4249_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___boxed(lean_object* v_00_u03b1_4250_, lean_object* v_x_4251_, lean_object* v___y_4252_, lean_object* v___y_4253_, lean_object* v___y_4254_){
_start:
{
lean_object* v_res_4255_; 
v_res_4255_ = l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0(v_00_u03b1_4250_, v_x_4251_, v___y_4252_, v___y_4253_);
lean_dec(v___y_4253_);
lean_dec_ref(v___y_4252_);
return v_res_4255_;
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_erase(lean_object* v_declName_4256_, lean_object* v_attrName_4257_, lean_object* v_a_4258_, lean_object* v_a_4259_){
_start:
{
lean_object* v___x_4261_; lean_object* v_env_4262_; lean_object* v___x_4263_; lean_object* v___x_4264_; 
v___x_4261_ = lean_st_ref_get(v_a_4259_);
v_env_4262_ = lean_ctor_get(v___x_4261_, 0);
lean_inc_ref(v_env_4262_);
lean_dec(v___x_4261_);
v___x_4263_ = l_Lean_getAttributeImpl(v_env_4262_, v_attrName_4257_);
v___x_4264_ = l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg(v___x_4263_, v_a_4258_, v_a_4259_);
if (lean_obj_tag(v___x_4264_) == 0)
{
lean_object* v_a_4265_; lean_object* v_erase_4266_; lean_object* v___x_4267_; 
v_a_4265_ = lean_ctor_get(v___x_4264_, 0);
lean_inc(v_a_4265_);
lean_dec_ref(v___x_4264_);
v_erase_4266_ = lean_ctor_get(v_a_4265_, 2);
lean_inc_ref(v_erase_4266_);
lean_dec(v_a_4265_);
lean_inc(v_a_4259_);
lean_inc_ref(v_a_4258_);
v___x_4267_ = lean_apply_4(v_erase_4266_, v_declName_4256_, v_a_4258_, v_a_4259_, lean_box(0));
return v___x_4267_;
}
else
{
lean_object* v_a_4268_; lean_object* v___x_4270_; uint8_t v_isShared_4271_; uint8_t v_isSharedCheck_4275_; 
lean_dec(v_declName_4256_);
v_a_4268_ = lean_ctor_get(v___x_4264_, 0);
v_isSharedCheck_4275_ = !lean_is_exclusive(v___x_4264_);
if (v_isSharedCheck_4275_ == 0)
{
v___x_4270_ = v___x_4264_;
v_isShared_4271_ = v_isSharedCheck_4275_;
goto v_resetjp_4269_;
}
else
{
lean_inc(v_a_4268_);
lean_dec(v___x_4264_);
v___x_4270_ = lean_box(0);
v_isShared_4271_ = v_isSharedCheck_4275_;
goto v_resetjp_4269_;
}
v_resetjp_4269_:
{
lean_object* v___x_4273_; 
if (v_isShared_4271_ == 0)
{
v___x_4273_ = v___x_4270_;
goto v_reusejp_4272_;
}
else
{
lean_object* v_reuseFailAlloc_4274_; 
v_reuseFailAlloc_4274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4274_, 0, v_a_4268_);
v___x_4273_ = v_reuseFailAlloc_4274_;
goto v_reusejp_4272_;
}
v_reusejp_4272_:
{
return v___x_4273_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_erase___boxed(lean_object* v_declName_4276_, lean_object* v_attrName_4277_, lean_object* v_a_4278_, lean_object* v_a_4279_, lean_object* v_a_4280_){
_start:
{
lean_object* v_res_4281_; 
v_res_4281_ = l_Lean_Attribute_erase(v_declName_4276_, v_attrName_4277_, v_a_4278_, v_a_4279_);
lean_dec(v_a_4279_);
lean_dec_ref(v_a_4278_);
return v_res_4281_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_updateEnvAttributesImpl_spec__0(lean_object* v_x_4282_, lean_object* v_x_4283_){
_start:
{
if (lean_obj_tag(v_x_4283_) == 0)
{
return v_x_4282_;
}
else
{
lean_object* v_key_4284_; lean_object* v_value_4285_; lean_object* v_tail_4286_; lean_object* v_newEntries_4287_; lean_object* v_map_4288_; uint8_t v___x_4289_; 
v_key_4284_ = lean_ctor_get(v_x_4283_, 0);
lean_inc(v_key_4284_);
v_value_4285_ = lean_ctor_get(v_x_4283_, 1);
lean_inc(v_value_4285_);
v_tail_4286_ = lean_ctor_get(v_x_4283_, 2);
lean_inc(v_tail_4286_);
lean_dec_ref(v_x_4283_);
v_newEntries_4287_ = lean_ctor_get(v_x_4282_, 0);
v_map_4288_ = lean_ctor_get(v_x_4282_, 1);
v___x_4289_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(v_map_4288_, v_key_4284_);
if (v___x_4289_ == 0)
{
lean_object* v___x_4291_; uint8_t v_isShared_4292_; uint8_t v_isSharedCheck_4298_; 
lean_inc_ref(v_map_4288_);
lean_inc(v_newEntries_4287_);
v_isSharedCheck_4298_ = !lean_is_exclusive(v_x_4282_);
if (v_isSharedCheck_4298_ == 0)
{
lean_object* v_unused_4299_; lean_object* v_unused_4300_; 
v_unused_4299_ = lean_ctor_get(v_x_4282_, 1);
lean_dec(v_unused_4299_);
v_unused_4300_ = lean_ctor_get(v_x_4282_, 0);
lean_dec(v_unused_4300_);
v___x_4291_ = v_x_4282_;
v_isShared_4292_ = v_isSharedCheck_4298_;
goto v_resetjp_4290_;
}
else
{
lean_dec(v_x_4282_);
v___x_4291_ = lean_box(0);
v_isShared_4292_ = v_isSharedCheck_4298_;
goto v_resetjp_4290_;
}
v_resetjp_4290_:
{
lean_object* v___x_4293_; lean_object* v___x_4295_; 
v___x_4293_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1___redArg(v_map_4288_, v_key_4284_, v_value_4285_);
if (v_isShared_4292_ == 0)
{
lean_ctor_set(v___x_4291_, 1, v___x_4293_);
v___x_4295_ = v___x_4291_;
goto v_reusejp_4294_;
}
else
{
lean_object* v_reuseFailAlloc_4297_; 
v_reuseFailAlloc_4297_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4297_, 0, v_newEntries_4287_);
lean_ctor_set(v_reuseFailAlloc_4297_, 1, v___x_4293_);
v___x_4295_ = v_reuseFailAlloc_4297_;
goto v_reusejp_4294_;
}
v_reusejp_4294_:
{
v_x_4282_ = v___x_4295_;
v_x_4283_ = v_tail_4286_;
goto _start;
}
}
}
else
{
lean_dec(v_value_4285_);
lean_dec(v_key_4284_);
v_x_4283_ = v_tail_4286_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_updateEnvAttributesImpl_spec__1(lean_object* v_as_4302_, size_t v_i_4303_, size_t v_stop_4304_, lean_object* v_b_4305_){
_start:
{
uint8_t v___x_4306_; 
v___x_4306_ = lean_usize_dec_eq(v_i_4303_, v_stop_4304_);
if (v___x_4306_ == 0)
{
lean_object* v___x_4307_; lean_object* v___x_4308_; size_t v___x_4309_; size_t v___x_4310_; 
v___x_4307_ = lean_array_uget_borrowed(v_as_4302_, v_i_4303_);
lean_inc(v___x_4307_);
v___x_4308_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_updateEnvAttributesImpl_spec__0(v_b_4305_, v___x_4307_);
v___x_4309_ = ((size_t)1ULL);
v___x_4310_ = lean_usize_add(v_i_4303_, v___x_4309_);
v_i_4303_ = v___x_4310_;
v_b_4305_ = v___x_4308_;
goto _start;
}
else
{
return v_b_4305_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_updateEnvAttributesImpl_spec__1___boxed(lean_object* v_as_4312_, lean_object* v_i_4313_, lean_object* v_stop_4314_, lean_object* v_b_4315_){
_start:
{
size_t v_i_boxed_4316_; size_t v_stop_boxed_4317_; lean_object* v_res_4318_; 
v_i_boxed_4316_ = lean_unbox_usize(v_i_4313_);
lean_dec(v_i_4313_);
v_stop_boxed_4317_ = lean_unbox_usize(v_stop_4314_);
lean_dec(v_stop_4314_);
v_res_4318_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_updateEnvAttributesImpl_spec__1(v_as_4312_, v_i_boxed_4316_, v_stop_boxed_4317_, v_b_4315_);
lean_dec_ref(v_as_4312_);
return v_res_4318_;
}
}
LEAN_EXPORT lean_object* lean_update_env_attributes(lean_object* v_env_4319_){
_start:
{
lean_object* v___x_4321_; lean_object* v___x_4322_; lean_object* v___x_4323_; lean_object* v___y_4325_; lean_object* v_toEnvExtension_4328_; lean_object* v_asyncMode_4329_; lean_object* v_buckets_4330_; lean_object* v___x_4331_; lean_object* v___x_4332_; lean_object* v___x_4333_; lean_object* v___x_4334_; lean_object* v___x_4335_; uint8_t v___x_4336_; 
v___x_4321_ = l_Lean_attributeMapRef;
v___x_4322_ = lean_st_ref_get(v___x_4321_);
v___x_4323_ = l_Lean_attributeExtension;
v_toEnvExtension_4328_ = lean_ctor_get(v___x_4323_, 0);
v_asyncMode_4329_ = lean_ctor_get(v_toEnvExtension_4328_, 2);
v_buckets_4330_ = lean_ctor_get(v___x_4322_, 1);
lean_inc_ref(v_buckets_4330_);
lean_dec(v___x_4322_);
v___x_4331_ = l_Lean_instInhabitedAttributeExtensionState_default;
v___x_4332_ = lean_box(0);
lean_inc_ref(v_env_4319_);
v___x_4333_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_4331_, v___x_4323_, v_env_4319_, v_asyncMode_4329_, v___x_4332_);
v___x_4334_ = lean_unsigned_to_nat(0u);
v___x_4335_ = lean_array_get_size(v_buckets_4330_);
v___x_4336_ = lean_nat_dec_lt(v___x_4334_, v___x_4335_);
if (v___x_4336_ == 0)
{
lean_dec_ref(v_buckets_4330_);
v___y_4325_ = v___x_4333_;
goto v___jp_4324_;
}
else
{
uint8_t v___x_4337_; 
v___x_4337_ = lean_nat_dec_le(v___x_4335_, v___x_4335_);
if (v___x_4337_ == 0)
{
if (v___x_4336_ == 0)
{
lean_dec_ref(v_buckets_4330_);
v___y_4325_ = v___x_4333_;
goto v___jp_4324_;
}
else
{
size_t v___x_4338_; size_t v___x_4339_; lean_object* v___x_4340_; 
v___x_4338_ = ((size_t)0ULL);
v___x_4339_ = lean_usize_of_nat(v___x_4335_);
v___x_4340_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_updateEnvAttributesImpl_spec__1(v_buckets_4330_, v___x_4338_, v___x_4339_, v___x_4333_);
lean_dec_ref(v_buckets_4330_);
v___y_4325_ = v___x_4340_;
goto v___jp_4324_;
}
}
else
{
size_t v___x_4341_; size_t v___x_4342_; lean_object* v___x_4343_; 
v___x_4341_ = ((size_t)0ULL);
v___x_4342_ = lean_usize_of_nat(v___x_4335_);
v___x_4343_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_updateEnvAttributesImpl_spec__1(v_buckets_4330_, v___x_4341_, v___x_4342_, v___x_4333_);
lean_dec_ref(v_buckets_4330_);
v___y_4325_ = v___x_4343_;
goto v___jp_4324_;
}
}
v___jp_4324_:
{
lean_object* v___x_4326_; lean_object* v___x_4327_; 
v___x_4326_ = l_Lean_PersistentEnvExtension_setState___redArg(v___x_4323_, v_env_4319_, v___y_4325_);
v___x_4327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4327_, 0, v___x_4326_);
return v___x_4327_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_updateEnvAttributesImpl___boxed(lean_object* v_env_4344_, lean_object* v_a_4345_){
_start:
{
lean_object* v_res_4346_; 
v_res_4346_ = lean_update_env_attributes(v_env_4344_);
return v_res_4346_;
}
}
LEAN_EXPORT lean_object* lean_get_num_attributes(){
_start:
{
lean_object* v___x_4348_; lean_object* v___x_4349_; lean_object* v_size_4350_; lean_object* v___x_4351_; 
v___x_4348_ = l_Lean_attributeMapRef;
v___x_4349_ = lean_st_ref_get(v___x_4348_);
v_size_4350_ = lean_ctor_get(v___x_4349_, 0);
lean_inc(v_size_4350_);
lean_dec(v___x_4349_);
v___x_4351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4351_, 0, v_size_4350_);
return v___x_4351_;
}
}
LEAN_EXPORT lean_object* l_Lean_getNumBuiltinAttributesImpl___boxed(lean_object* v_a_4352_){
_start:
{
lean_object* v_res_4353_; 
v_res_4353_ = lean_get_num_attributes();
return v_res_4353_;
}
}
lean_object* runtime_initialize_Lean_CoreM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_MetaAttr(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Attributes(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
