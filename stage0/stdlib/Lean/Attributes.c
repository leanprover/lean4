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
static const lean_string_object l_Lean_instInhabitedAttributeImplCore_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_instInhabitedAttributeImplCore_default___closed__0 = (const lean_object*)&l_Lean_instInhabitedAttributeImplCore_default___closed__0_value;
static const lean_ctor_object l_Lean_instInhabitedAttributeImplCore_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 8, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instInhabitedAttributeImplCore_default___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_instInhabitedAttributeImplCore_default___closed__1 = (const lean_object*)&l_Lean_instInhabitedAttributeImplCore_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_instInhabitedAttributeImplCore_default = (const lean_object*)&l_Lean_instInhabitedAttributeImplCore_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_instInhabitedAttributeImplCore = (const lean_object*)&l_Lean_instInhabitedAttributeImplCore_default___closed__1_value;
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
static const lean_ctor_object l_Lean_instInhabitedAttributeImpl_default___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_instInhabitedAttributeImplCore_default___closed__1_value),((lean_object*)&l_Lean_instInhabitedAttributeImpl_default___closed__0_value),((lean_object*)&l_Lean_instInhabitedAttributeImpl_default___closed__1_value)}};
static const lean_object* l_Lean_instInhabitedAttributeImpl_default___closed__2 = (const lean_object*)&l_Lean_instInhabitedAttributeImpl_default___closed__2_value;
LEAN_EXPORT const lean_object* l_Lean_instInhabitedAttributeImpl_default = (const lean_object*)&l_Lean_instInhabitedAttributeImpl_default___closed__2_value;
LEAN_EXPORT const lean_object* l_Lean_instInhabitedAttributeImpl = (const lean_object*)&l_Lean_instInhabitedAttributeImpl_default___closed__2_value;
static lean_once_cell_t l_Lean_initFn___closed__0_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_initFn___closed__0_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_;
static lean_once_cell_t l_Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2____boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_Attributes_2990505691____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_Attributes_2990505691____hygCtx___hyg_2____boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn___lam__1_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn___lam__2_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(lean_object*);
static const lean_closure_object l_Lean_initFn___closed__0_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_initFn___lam__0_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_initFn___closed__0_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__0_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_initFn___closed__1_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_initFn___lam__1_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_initFn___closed__1_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__1_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_initFn___closed__2_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_initFn___lam__2_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_initFn___closed__2_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__2_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_initFn___closed__3_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "attributeExtension"};
static const lean_object* l_Lean_initFn___closed__3_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__3_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_initFn___closed__4_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_AttributeImplCore_ref___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_initFn___closed__4_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_initFn___closed__4_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_initFn___closed__3_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(219, 25, 250, 145, 208, 184, 170, 105)}};
static const lean_object* l_Lean_initFn___closed__4_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__4_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_initFn___closed__5_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Attributes_0__Lean_AttributeExtension_addImported___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_initFn___closed__5_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__5_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_initFn___closed__6_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Attributes_0__Lean_addAttrEntry, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_initFn___closed__6_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__6_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2__value;
static lean_once_cell_t l_Lean_initFn___closed__7_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_initFn___closed__7_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_;
static lean_once_cell_t l_Lean_initFn___closed__8_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_initFn___closed__8_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2____boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_AttributeKind_ctorIdx(uint8_t v_x_205_){
_start:
{
switch(v_x_205_)
{
case 0:
{
lean_object* v___x_206_; 
v___x_206_ = lean_unsigned_to_nat(0u);
return v___x_206_;
}
case 1:
{
lean_object* v___x_207_; 
v___x_207_ = lean_unsigned_to_nat(1u);
return v___x_207_;
}
default: 
{
lean_object* v___x_208_; 
v___x_208_ = lean_unsigned_to_nat(2u);
return v___x_208_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_ctorIdx___boxed(lean_object* v_x_209_){
_start:
{
uint8_t v_x_boxed_210_; lean_object* v_res_211_; 
v_x_boxed_210_ = lean_unbox(v_x_209_);
v_res_211_ = l_Lean_AttributeKind_ctorIdx(v_x_boxed_210_);
return v_res_211_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_toCtorIdx(uint8_t v_x_212_){
_start:
{
lean_object* v___x_213_; 
v___x_213_ = l_Lean_AttributeKind_ctorIdx(v_x_212_);
return v___x_213_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_toCtorIdx___boxed(lean_object* v_x_214_){
_start:
{
uint8_t v_x_4__boxed_215_; lean_object* v_res_216_; 
v_x_4__boxed_215_ = lean_unbox(v_x_214_);
v_res_216_ = l_Lean_AttributeKind_toCtorIdx(v_x_4__boxed_215_);
return v_res_216_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_ctorElim___redArg(lean_object* v_k_217_){
_start:
{
lean_inc(v_k_217_);
return v_k_217_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_ctorElim___redArg___boxed(lean_object* v_k_218_){
_start:
{
lean_object* v_res_219_; 
v_res_219_ = l_Lean_AttributeKind_ctorElim___redArg(v_k_218_);
lean_dec(v_k_218_);
return v_res_219_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_ctorElim(lean_object* v_motive_220_, lean_object* v_ctorIdx_221_, uint8_t v_t_222_, lean_object* v_h_223_, lean_object* v_k_224_){
_start:
{
lean_inc(v_k_224_);
return v_k_224_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_ctorElim___boxed(lean_object* v_motive_225_, lean_object* v_ctorIdx_226_, lean_object* v_t_227_, lean_object* v_h_228_, lean_object* v_k_229_){
_start:
{
uint8_t v_t_boxed_230_; lean_object* v_res_231_; 
v_t_boxed_230_ = lean_unbox(v_t_227_);
v_res_231_ = l_Lean_AttributeKind_ctorElim(v_motive_225_, v_ctorIdx_226_, v_t_boxed_230_, v_h_228_, v_k_229_);
lean_dec(v_k_229_);
lean_dec(v_ctorIdx_226_);
return v_res_231_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_global_elim___redArg(lean_object* v_global_232_){
_start:
{
lean_inc(v_global_232_);
return v_global_232_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_global_elim___redArg___boxed(lean_object* v_global_233_){
_start:
{
lean_object* v_res_234_; 
v_res_234_ = l_Lean_AttributeKind_global_elim___redArg(v_global_233_);
lean_dec(v_global_233_);
return v_res_234_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_global_elim(lean_object* v_motive_235_, uint8_t v_t_236_, lean_object* v_h_237_, lean_object* v_global_238_){
_start:
{
lean_inc(v_global_238_);
return v_global_238_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_global_elim___boxed(lean_object* v_motive_239_, lean_object* v_t_240_, lean_object* v_h_241_, lean_object* v_global_242_){
_start:
{
uint8_t v_t_boxed_243_; lean_object* v_res_244_; 
v_t_boxed_243_ = lean_unbox(v_t_240_);
v_res_244_ = l_Lean_AttributeKind_global_elim(v_motive_239_, v_t_boxed_243_, v_h_241_, v_global_242_);
lean_dec(v_global_242_);
return v_res_244_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_local_elim___redArg(lean_object* v_local_245_){
_start:
{
lean_inc(v_local_245_);
return v_local_245_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_local_elim___redArg___boxed(lean_object* v_local_246_){
_start:
{
lean_object* v_res_247_; 
v_res_247_ = l_Lean_AttributeKind_local_elim___redArg(v_local_246_);
lean_dec(v_local_246_);
return v_res_247_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_local_elim(lean_object* v_motive_248_, uint8_t v_t_249_, lean_object* v_h_250_, lean_object* v_local_251_){
_start:
{
lean_inc(v_local_251_);
return v_local_251_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_local_elim___boxed(lean_object* v_motive_252_, lean_object* v_t_253_, lean_object* v_h_254_, lean_object* v_local_255_){
_start:
{
uint8_t v_t_boxed_256_; lean_object* v_res_257_; 
v_t_boxed_256_ = lean_unbox(v_t_253_);
v_res_257_ = l_Lean_AttributeKind_local_elim(v_motive_252_, v_t_boxed_256_, v_h_254_, v_local_255_);
lean_dec(v_local_255_);
return v_res_257_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_scoped_elim___redArg(lean_object* v_scoped_258_){
_start:
{
lean_inc(v_scoped_258_);
return v_scoped_258_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_scoped_elim___redArg___boxed(lean_object* v_scoped_259_){
_start:
{
lean_object* v_res_260_; 
v_res_260_ = l_Lean_AttributeKind_scoped_elim___redArg(v_scoped_259_);
lean_dec(v_scoped_259_);
return v_res_260_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_scoped_elim(lean_object* v_motive_261_, uint8_t v_t_262_, lean_object* v_h_263_, lean_object* v_scoped_264_){
_start:
{
lean_inc(v_scoped_264_);
return v_scoped_264_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_scoped_elim___boxed(lean_object* v_motive_265_, lean_object* v_t_266_, lean_object* v_h_267_, lean_object* v_scoped_268_){
_start:
{
uint8_t v_t_boxed_269_; lean_object* v_res_270_; 
v_t_boxed_269_ = lean_unbox(v_t_266_);
v_res_270_ = l_Lean_AttributeKind_scoped_elim(v_motive_265_, v_t_boxed_269_, v_h_267_, v_scoped_268_);
lean_dec(v_scoped_268_);
return v_res_270_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqAttributeKind_beq(uint8_t v_x_271_, uint8_t v_y_272_){
_start:
{
lean_object* v___x_273_; lean_object* v___x_274_; uint8_t v___x_275_; 
v___x_273_ = l_Lean_AttributeKind_ctorIdx(v_x_271_);
v___x_274_ = l_Lean_AttributeKind_ctorIdx(v_y_272_);
v___x_275_ = lean_nat_dec_eq(v___x_273_, v___x_274_);
lean_dec(v___x_274_);
lean_dec(v___x_273_);
return v___x_275_;
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqAttributeKind_beq___boxed(lean_object* v_x_276_, lean_object* v_y_277_){
_start:
{
uint8_t v_x_17__boxed_278_; uint8_t v_y_18__boxed_279_; uint8_t v_res_280_; lean_object* v_r_281_; 
v_x_17__boxed_278_ = lean_unbox(v_x_276_);
v_y_18__boxed_279_ = lean_unbox(v_y_277_);
v_res_280_ = l_Lean_instBEqAttributeKind_beq(v_x_17__boxed_278_, v_y_18__boxed_279_);
v_r_281_ = lean_box(v_res_280_);
return v_r_281_;
}
}
static uint8_t _init_l_Lean_instInhabitedAttributeKind_default(void){
_start:
{
uint8_t v___x_284_; 
v___x_284_ = 0;
return v___x_284_;
}
}
static uint8_t _init_l_Lean_instInhabitedAttributeKind(void){
_start:
{
uint8_t v___x_285_; 
v___x_285_ = 0;
return v___x_285_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToStringAttributeKind___lam__0(uint8_t v_x_289_){
_start:
{
switch(v_x_289_)
{
case 0:
{
lean_object* v___x_290_; 
v___x_290_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__0));
return v___x_290_;
}
case 1:
{
lean_object* v___x_291_; 
v___x_291_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__1));
return v___x_291_;
}
default: 
{
lean_object* v___x_292_; 
v___x_292_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__2));
return v___x_292_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToStringAttributeKind___lam__0___boxed(lean_object* v_x_293_){
_start:
{
uint8_t v_x_36__boxed_294_; lean_object* v_res_295_; 
v_x_36__boxed_294_ = lean_unbox(v_x_293_);
v_res_295_ = l_Lean_instToStringAttributeKind___lam__0(v_x_36__boxed_294_);
return v_res_295_;
}
}
static lean_object* _init_l_Lean_instInhabitedAttributeImpl_default___lam__0___closed__0(void){
_start:
{
lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; 
v___x_298_ = l_Lean_instInhabitedMessageData_default;
v___x_299_ = lean_box(0);
v___x_300_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_300_, 0, v___x_299_);
lean_ctor_set(v___x_300_, 1, v___x_298_);
return v___x_300_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedAttributeImpl_default___lam__0(lean_object* v_x_301_, lean_object* v___y_302_, uint8_t v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_){
_start:
{
lean_object* v___x_307_; lean_object* v___x_308_; 
v___x_307_ = lean_obj_once(&l_Lean_instInhabitedAttributeImpl_default___lam__0___closed__0, &l_Lean_instInhabitedAttributeImpl_default___lam__0___closed__0_once, _init_l_Lean_instInhabitedAttributeImpl_default___lam__0___closed__0);
v___x_308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_308_, 0, v___x_307_);
return v___x_308_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedAttributeImpl_default___lam__0___boxed(lean_object* v_x_309_, lean_object* v___y_310_, lean_object* v___y_311_, lean_object* v___y_312_, lean_object* v___y_313_, lean_object* v___y_314_){
_start:
{
uint8_t v___y_112__boxed_315_; lean_object* v_res_316_; 
v___y_112__boxed_315_ = lean_unbox(v___y_311_);
v_res_316_ = l_Lean_instInhabitedAttributeImpl_default___lam__0(v_x_309_, v___y_310_, v___y_112__boxed_315_, v___y_312_, v___y_313_);
lean_dec(v___y_313_);
lean_dec_ref(v___y_312_);
lean_dec(v___y_310_);
lean_dec(v_x_309_);
return v_res_316_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedAttributeImpl_default___lam__1(lean_object* v_x_317_, lean_object* v___y_318_, lean_object* v___y_319_){
_start:
{
lean_object* v___x_321_; lean_object* v___x_322_; 
v___x_321_ = lean_obj_once(&l_Lean_instInhabitedAttributeImpl_default___lam__0___closed__0, &l_Lean_instInhabitedAttributeImpl_default___lam__0___closed__0_once, _init_l_Lean_instInhabitedAttributeImpl_default___lam__0___closed__0);
v___x_322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_322_, 0, v___x_321_);
return v___x_322_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedAttributeImpl_default___lam__1___boxed(lean_object* v_x_323_, lean_object* v___y_324_, lean_object* v___y_325_, lean_object* v___y_326_){
_start:
{
lean_object* v_res_327_; 
v_res_327_ = l_Lean_instInhabitedAttributeImpl_default___lam__1(v_x_323_, v___y_324_, v___y_325_);
lean_dec(v___y_325_);
lean_dec_ref(v___y_324_);
lean_dec(v_x_323_);
return v_res_327_;
}
}
static lean_object* _init_l_Lean_initFn___closed__0_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; 
v___x_336_ = lean_box(0);
v___x_337_ = lean_unsigned_to_nat(16u);
v___x_338_ = lean_mk_array(v___x_337_, v___x_336_);
return v___x_338_;
}
}
static lean_object* _init_l_Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; 
v___x_339_ = lean_obj_once(&l_Lean_initFn___closed__0_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_, &l_Lean_initFn___closed__0_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2__once, _init_l_Lean_initFn___closed__0_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_);
v___x_340_ = lean_unsigned_to_nat(0u);
v___x_341_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_341_, 0, v___x_340_);
lean_ctor_set(v___x_341_, 1, v___x_339_);
return v___x_341_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; 
v___x_343_ = lean_obj_once(&l_Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_, &l_Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2__once, _init_l_Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_);
v___x_344_ = lean_st_mk_ref(v___x_343_);
v___x_345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_345_, 0, v___x_344_);
return v___x_345_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2____boxed(lean_object* v_a_346_){
_start:
{
lean_object* v_res_347_; 
v_res_347_ = l_Lean_initFn_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_();
return v_res_347_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0_spec__0___redArg(lean_object* v_a_348_, lean_object* v_x_349_){
_start:
{
if (lean_obj_tag(v_x_349_) == 0)
{
uint8_t v___x_350_; 
v___x_350_ = 0;
return v___x_350_;
}
else
{
lean_object* v_key_351_; lean_object* v_tail_352_; uint8_t v___x_353_; 
v_key_351_ = lean_ctor_get(v_x_349_, 0);
v_tail_352_ = lean_ctor_get(v_x_349_, 2);
v___x_353_ = lean_name_eq(v_key_351_, v_a_348_);
if (v___x_353_ == 0)
{
v_x_349_ = v_tail_352_;
goto _start;
}
else
{
return v___x_353_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0_spec__0___redArg___boxed(lean_object* v_a_355_, lean_object* v_x_356_){
_start:
{
uint8_t v_res_357_; lean_object* v_r_358_; 
v_res_357_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0_spec__0___redArg(v_a_355_, v_x_356_);
lean_dec(v_x_356_);
lean_dec(v_a_355_);
v_r_358_ = lean_box(v_res_357_);
return v_r_358_;
}
}
static uint64_t _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_359_; uint64_t v___x_360_; 
v___x_359_ = lean_unsigned_to_nat(1723u);
v___x_360_ = lean_uint64_of_nat(v___x_359_);
return v___x_360_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(lean_object* v_m_361_, lean_object* v_a_362_){
_start:
{
lean_object* v_buckets_363_; lean_object* v___x_364_; uint64_t v___y_366_; 
v_buckets_363_ = lean_ctor_get(v_m_361_, 1);
v___x_364_ = lean_array_get_size(v_buckets_363_);
if (lean_obj_tag(v_a_362_) == 0)
{
uint64_t v___x_380_; 
v___x_380_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg___closed__0);
v___y_366_ = v___x_380_;
goto v___jp_365_;
}
else
{
uint64_t v_hash_381_; 
v_hash_381_ = lean_ctor_get_uint64(v_a_362_, sizeof(void*)*2);
v___y_366_ = v_hash_381_;
goto v___jp_365_;
}
v___jp_365_:
{
uint64_t v___x_367_; uint64_t v___x_368_; uint64_t v_fold_369_; uint64_t v___x_370_; uint64_t v___x_371_; uint64_t v___x_372_; size_t v___x_373_; size_t v___x_374_; size_t v___x_375_; size_t v___x_376_; size_t v___x_377_; lean_object* v___x_378_; uint8_t v___x_379_; 
v___x_367_ = 32ULL;
v___x_368_ = lean_uint64_shift_right(v___y_366_, v___x_367_);
v_fold_369_ = lean_uint64_xor(v___y_366_, v___x_368_);
v___x_370_ = 16ULL;
v___x_371_ = lean_uint64_shift_right(v_fold_369_, v___x_370_);
v___x_372_ = lean_uint64_xor(v_fold_369_, v___x_371_);
v___x_373_ = lean_uint64_to_usize(v___x_372_);
v___x_374_ = lean_usize_of_nat(v___x_364_);
v___x_375_ = ((size_t)1ULL);
v___x_376_ = lean_usize_sub(v___x_374_, v___x_375_);
v___x_377_ = lean_usize_land(v___x_373_, v___x_376_);
v___x_378_ = lean_array_uget_borrowed(v_buckets_363_, v___x_377_);
v___x_379_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0_spec__0___redArg(v_a_362_, v___x_378_);
return v___x_379_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg___boxed(lean_object* v_m_382_, lean_object* v_a_383_){
_start:
{
uint8_t v_res_384_; lean_object* v_r_385_; 
v_res_384_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(v_m_382_, v_a_383_);
lean_dec(v_a_383_);
lean_dec_ref(v_m_382_);
v_r_385_ = lean_box(v_res_384_);
return v_r_385_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__3___redArg(lean_object* v_a_386_, lean_object* v_b_387_, lean_object* v_x_388_){
_start:
{
if (lean_obj_tag(v_x_388_) == 0)
{
lean_dec(v_b_387_);
lean_dec(v_a_386_);
return v_x_388_;
}
else
{
lean_object* v_key_389_; lean_object* v_value_390_; lean_object* v_tail_391_; lean_object* v___x_393_; uint8_t v_isShared_394_; uint8_t v_isSharedCheck_403_; 
v_key_389_ = lean_ctor_get(v_x_388_, 0);
v_value_390_ = lean_ctor_get(v_x_388_, 1);
v_tail_391_ = lean_ctor_get(v_x_388_, 2);
v_isSharedCheck_403_ = !lean_is_exclusive(v_x_388_);
if (v_isSharedCheck_403_ == 0)
{
v___x_393_ = v_x_388_;
v_isShared_394_ = v_isSharedCheck_403_;
goto v_resetjp_392_;
}
else
{
lean_inc(v_tail_391_);
lean_inc(v_value_390_);
lean_inc(v_key_389_);
lean_dec(v_x_388_);
v___x_393_ = lean_box(0);
v_isShared_394_ = v_isSharedCheck_403_;
goto v_resetjp_392_;
}
v_resetjp_392_:
{
uint8_t v___x_395_; 
v___x_395_ = lean_name_eq(v_key_389_, v_a_386_);
if (v___x_395_ == 0)
{
lean_object* v___x_396_; lean_object* v___x_398_; 
v___x_396_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__3___redArg(v_a_386_, v_b_387_, v_tail_391_);
if (v_isShared_394_ == 0)
{
lean_ctor_set(v___x_393_, 2, v___x_396_);
v___x_398_ = v___x_393_;
goto v_reusejp_397_;
}
else
{
lean_object* v_reuseFailAlloc_399_; 
v_reuseFailAlloc_399_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_399_, 0, v_key_389_);
lean_ctor_set(v_reuseFailAlloc_399_, 1, v_value_390_);
lean_ctor_set(v_reuseFailAlloc_399_, 2, v___x_396_);
v___x_398_ = v_reuseFailAlloc_399_;
goto v_reusejp_397_;
}
v_reusejp_397_:
{
return v___x_398_;
}
}
else
{
lean_object* v___x_401_; 
lean_dec(v_value_390_);
lean_dec(v_key_389_);
if (v_isShared_394_ == 0)
{
lean_ctor_set(v___x_393_, 1, v_b_387_);
lean_ctor_set(v___x_393_, 0, v_a_386_);
v___x_401_ = v___x_393_;
goto v_reusejp_400_;
}
else
{
lean_object* v_reuseFailAlloc_402_; 
v_reuseFailAlloc_402_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_402_, 0, v_a_386_);
lean_ctor_set(v_reuseFailAlloc_402_, 1, v_b_387_);
lean_ctor_set(v_reuseFailAlloc_402_, 2, v_tail_391_);
v___x_401_ = v_reuseFailAlloc_402_;
goto v_reusejp_400_;
}
v_reusejp_400_:
{
return v___x_401_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2_spec__3_spec__4___redArg(lean_object* v_x_404_, lean_object* v_x_405_){
_start:
{
if (lean_obj_tag(v_x_405_) == 0)
{
return v_x_404_;
}
else
{
lean_object* v_key_406_; lean_object* v_value_407_; lean_object* v_tail_408_; lean_object* v___x_410_; uint8_t v_isShared_411_; uint8_t v_isSharedCheck_434_; 
v_key_406_ = lean_ctor_get(v_x_405_, 0);
v_value_407_ = lean_ctor_get(v_x_405_, 1);
v_tail_408_ = lean_ctor_get(v_x_405_, 2);
v_isSharedCheck_434_ = !lean_is_exclusive(v_x_405_);
if (v_isSharedCheck_434_ == 0)
{
v___x_410_ = v_x_405_;
v_isShared_411_ = v_isSharedCheck_434_;
goto v_resetjp_409_;
}
else
{
lean_inc(v_tail_408_);
lean_inc(v_value_407_);
lean_inc(v_key_406_);
lean_dec(v_x_405_);
v___x_410_ = lean_box(0);
v_isShared_411_ = v_isSharedCheck_434_;
goto v_resetjp_409_;
}
v_resetjp_409_:
{
lean_object* v___x_412_; uint64_t v___y_414_; 
v___x_412_ = lean_array_get_size(v_x_404_);
if (lean_obj_tag(v_key_406_) == 0)
{
uint64_t v___x_432_; 
v___x_432_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg___closed__0);
v___y_414_ = v___x_432_;
goto v___jp_413_;
}
else
{
uint64_t v_hash_433_; 
v_hash_433_ = lean_ctor_get_uint64(v_key_406_, sizeof(void*)*2);
v___y_414_ = v_hash_433_;
goto v___jp_413_;
}
v___jp_413_:
{
uint64_t v___x_415_; uint64_t v___x_416_; uint64_t v_fold_417_; uint64_t v___x_418_; uint64_t v___x_419_; uint64_t v___x_420_; size_t v___x_421_; size_t v___x_422_; size_t v___x_423_; size_t v___x_424_; size_t v___x_425_; lean_object* v___x_426_; lean_object* v___x_428_; 
v___x_415_ = 32ULL;
v___x_416_ = lean_uint64_shift_right(v___y_414_, v___x_415_);
v_fold_417_ = lean_uint64_xor(v___y_414_, v___x_416_);
v___x_418_ = 16ULL;
v___x_419_ = lean_uint64_shift_right(v_fold_417_, v___x_418_);
v___x_420_ = lean_uint64_xor(v_fold_417_, v___x_419_);
v___x_421_ = lean_uint64_to_usize(v___x_420_);
v___x_422_ = lean_usize_of_nat(v___x_412_);
v___x_423_ = ((size_t)1ULL);
v___x_424_ = lean_usize_sub(v___x_422_, v___x_423_);
v___x_425_ = lean_usize_land(v___x_421_, v___x_424_);
v___x_426_ = lean_array_uget_borrowed(v_x_404_, v___x_425_);
lean_inc(v___x_426_);
if (v_isShared_411_ == 0)
{
lean_ctor_set(v___x_410_, 2, v___x_426_);
v___x_428_ = v___x_410_;
goto v_reusejp_427_;
}
else
{
lean_object* v_reuseFailAlloc_431_; 
v_reuseFailAlloc_431_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_431_, 0, v_key_406_);
lean_ctor_set(v_reuseFailAlloc_431_, 1, v_value_407_);
lean_ctor_set(v_reuseFailAlloc_431_, 2, v___x_426_);
v___x_428_ = v_reuseFailAlloc_431_;
goto v_reusejp_427_;
}
v_reusejp_427_:
{
lean_object* v___x_429_; 
v___x_429_ = lean_array_uset(v_x_404_, v___x_425_, v___x_428_);
v_x_404_ = v___x_429_;
v_x_405_ = v_tail_408_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2_spec__3___redArg(lean_object* v_i_435_, lean_object* v_source_436_, lean_object* v_target_437_){
_start:
{
lean_object* v___x_438_; uint8_t v___x_439_; 
v___x_438_ = lean_array_get_size(v_source_436_);
v___x_439_ = lean_nat_dec_lt(v_i_435_, v___x_438_);
if (v___x_439_ == 0)
{
lean_dec_ref(v_source_436_);
lean_dec(v_i_435_);
return v_target_437_;
}
else
{
lean_object* v_es_440_; lean_object* v___x_441_; lean_object* v_source_442_; lean_object* v_target_443_; lean_object* v___x_444_; lean_object* v___x_445_; 
v_es_440_ = lean_array_fget(v_source_436_, v_i_435_);
v___x_441_ = lean_box(0);
v_source_442_ = lean_array_fset(v_source_436_, v_i_435_, v___x_441_);
v_target_443_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2_spec__3_spec__4___redArg(v_target_437_, v_es_440_);
v___x_444_ = lean_unsigned_to_nat(1u);
v___x_445_ = lean_nat_add(v_i_435_, v___x_444_);
lean_dec(v_i_435_);
v_i_435_ = v___x_445_;
v_source_436_ = v_source_442_;
v_target_437_ = v_target_443_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2___redArg(lean_object* v_data_447_){
_start:
{
lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v_nbuckets_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; 
v___x_448_ = lean_array_get_size(v_data_447_);
v___x_449_ = lean_unsigned_to_nat(2u);
v_nbuckets_450_ = lean_nat_mul(v___x_448_, v___x_449_);
v___x_451_ = lean_unsigned_to_nat(0u);
v___x_452_ = lean_box(0);
v___x_453_ = lean_mk_array(v_nbuckets_450_, v___x_452_);
v___x_454_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2_spec__3___redArg(v___x_451_, v_data_447_, v___x_453_);
return v___x_454_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1___redArg(lean_object* v_m_455_, lean_object* v_a_456_, lean_object* v_b_457_){
_start:
{
lean_object* v_size_458_; lean_object* v_buckets_459_; lean_object* v___x_461_; uint8_t v_isShared_462_; uint8_t v_isSharedCheck_505_; 
v_size_458_ = lean_ctor_get(v_m_455_, 0);
v_buckets_459_ = lean_ctor_get(v_m_455_, 1);
v_isSharedCheck_505_ = !lean_is_exclusive(v_m_455_);
if (v_isSharedCheck_505_ == 0)
{
v___x_461_ = v_m_455_;
v_isShared_462_ = v_isSharedCheck_505_;
goto v_resetjp_460_;
}
else
{
lean_inc(v_buckets_459_);
lean_inc(v_size_458_);
lean_dec(v_m_455_);
v___x_461_ = lean_box(0);
v_isShared_462_ = v_isSharedCheck_505_;
goto v_resetjp_460_;
}
v_resetjp_460_:
{
lean_object* v___x_463_; uint64_t v___y_465_; 
v___x_463_ = lean_array_get_size(v_buckets_459_);
if (lean_obj_tag(v_a_456_) == 0)
{
uint64_t v___x_503_; 
v___x_503_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg___closed__0);
v___y_465_ = v___x_503_;
goto v___jp_464_;
}
else
{
uint64_t v_hash_504_; 
v_hash_504_ = lean_ctor_get_uint64(v_a_456_, sizeof(void*)*2);
v___y_465_ = v_hash_504_;
goto v___jp_464_;
}
v___jp_464_:
{
uint64_t v___x_466_; uint64_t v___x_467_; uint64_t v_fold_468_; uint64_t v___x_469_; uint64_t v___x_470_; uint64_t v___x_471_; size_t v___x_472_; size_t v___x_473_; size_t v___x_474_; size_t v___x_475_; size_t v___x_476_; lean_object* v_bkt_477_; uint8_t v___x_478_; 
v___x_466_ = 32ULL;
v___x_467_ = lean_uint64_shift_right(v___y_465_, v___x_466_);
v_fold_468_ = lean_uint64_xor(v___y_465_, v___x_467_);
v___x_469_ = 16ULL;
v___x_470_ = lean_uint64_shift_right(v_fold_468_, v___x_469_);
v___x_471_ = lean_uint64_xor(v_fold_468_, v___x_470_);
v___x_472_ = lean_uint64_to_usize(v___x_471_);
v___x_473_ = lean_usize_of_nat(v___x_463_);
v___x_474_ = ((size_t)1ULL);
v___x_475_ = lean_usize_sub(v___x_473_, v___x_474_);
v___x_476_ = lean_usize_land(v___x_472_, v___x_475_);
v_bkt_477_ = lean_array_uget_borrowed(v_buckets_459_, v___x_476_);
v___x_478_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0_spec__0___redArg(v_a_456_, v_bkt_477_);
if (v___x_478_ == 0)
{
lean_object* v___x_479_; lean_object* v_size_x27_480_; lean_object* v___x_481_; lean_object* v_buckets_x27_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; uint8_t v___x_488_; 
v___x_479_ = lean_unsigned_to_nat(1u);
v_size_x27_480_ = lean_nat_add(v_size_458_, v___x_479_);
lean_dec(v_size_458_);
lean_inc(v_bkt_477_);
v___x_481_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_481_, 0, v_a_456_);
lean_ctor_set(v___x_481_, 1, v_b_457_);
lean_ctor_set(v___x_481_, 2, v_bkt_477_);
v_buckets_x27_482_ = lean_array_uset(v_buckets_459_, v___x_476_, v___x_481_);
v___x_483_ = lean_unsigned_to_nat(4u);
v___x_484_ = lean_nat_mul(v_size_x27_480_, v___x_483_);
v___x_485_ = lean_unsigned_to_nat(3u);
v___x_486_ = lean_nat_div(v___x_484_, v___x_485_);
lean_dec(v___x_484_);
v___x_487_ = lean_array_get_size(v_buckets_x27_482_);
v___x_488_ = lean_nat_dec_le(v___x_486_, v___x_487_);
lean_dec(v___x_486_);
if (v___x_488_ == 0)
{
lean_object* v_val_489_; lean_object* v___x_491_; 
v_val_489_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2___redArg(v_buckets_x27_482_);
if (v_isShared_462_ == 0)
{
lean_ctor_set(v___x_461_, 1, v_val_489_);
lean_ctor_set(v___x_461_, 0, v_size_x27_480_);
v___x_491_ = v___x_461_;
goto v_reusejp_490_;
}
else
{
lean_object* v_reuseFailAlloc_492_; 
v_reuseFailAlloc_492_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_492_, 0, v_size_x27_480_);
lean_ctor_set(v_reuseFailAlloc_492_, 1, v_val_489_);
v___x_491_ = v_reuseFailAlloc_492_;
goto v_reusejp_490_;
}
v_reusejp_490_:
{
return v___x_491_;
}
}
else
{
lean_object* v___x_494_; 
if (v_isShared_462_ == 0)
{
lean_ctor_set(v___x_461_, 1, v_buckets_x27_482_);
lean_ctor_set(v___x_461_, 0, v_size_x27_480_);
v___x_494_ = v___x_461_;
goto v_reusejp_493_;
}
else
{
lean_object* v_reuseFailAlloc_495_; 
v_reuseFailAlloc_495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_495_, 0, v_size_x27_480_);
lean_ctor_set(v_reuseFailAlloc_495_, 1, v_buckets_x27_482_);
v___x_494_ = v_reuseFailAlloc_495_;
goto v_reusejp_493_;
}
v_reusejp_493_:
{
return v___x_494_;
}
}
}
else
{
lean_object* v___x_496_; lean_object* v_buckets_x27_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_501_; 
lean_inc(v_bkt_477_);
v___x_496_ = lean_box(0);
v_buckets_x27_497_ = lean_array_uset(v_buckets_459_, v___x_476_, v___x_496_);
v___x_498_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__3___redArg(v_a_456_, v_b_457_, v_bkt_477_);
v___x_499_ = lean_array_uset(v_buckets_x27_497_, v___x_476_, v___x_498_);
if (v_isShared_462_ == 0)
{
lean_ctor_set(v___x_461_, 1, v___x_499_);
v___x_501_ = v___x_461_;
goto v_reusejp_500_;
}
else
{
lean_object* v_reuseFailAlloc_502_; 
v_reuseFailAlloc_502_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_502_, 0, v_size_458_);
lean_ctor_set(v_reuseFailAlloc_502_, 1, v___x_499_);
v___x_501_ = v_reuseFailAlloc_502_;
goto v_reusejp_500_;
}
v_reusejp_500_:
{
return v___x_501_;
}
}
}
}
}
}
static lean_object* _init_l_Lean_registerBuiltinAttribute___closed__1(void){
_start:
{
lean_object* v___x_507_; lean_object* v___x_508_; 
v___x_507_ = ((lean_object*)(l_Lean_registerBuiltinAttribute___closed__0));
v___x_508_ = lean_mk_io_user_error(v___x_507_);
return v___x_508_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerBuiltinAttribute(lean_object* v_attr_511_){
_start:
{
lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v_toAttributeImplCore_515_; lean_object* v_name_516_; uint8_t v___x_517_; 
v___x_513_ = l_Lean_attributeMapRef;
v___x_514_ = lean_st_ref_get(v___x_513_);
v_toAttributeImplCore_515_ = lean_ctor_get(v_attr_511_, 0);
v_name_516_ = lean_ctor_get(v_toAttributeImplCore_515_, 1);
lean_inc(v_name_516_);
v___x_517_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(v___x_514_, v_name_516_);
lean_dec(v___x_514_);
if (v___x_517_ == 0)
{
lean_object* v___x_518_; 
v___x_518_ = l_Lean_initializing();
if (lean_obj_tag(v___x_518_) == 0)
{
lean_object* v_a_519_; lean_object* v___x_521_; uint8_t v_isShared_522_; uint8_t v_isSharedCheck_534_; 
v_a_519_ = lean_ctor_get(v___x_518_, 0);
v_isSharedCheck_534_ = !lean_is_exclusive(v___x_518_);
if (v_isSharedCheck_534_ == 0)
{
v___x_521_ = v___x_518_;
v_isShared_522_ = v_isSharedCheck_534_;
goto v_resetjp_520_;
}
else
{
lean_inc(v_a_519_);
lean_dec(v___x_518_);
v___x_521_ = lean_box(0);
v_isShared_522_ = v_isSharedCheck_534_;
goto v_resetjp_520_;
}
v_resetjp_520_:
{
uint8_t v___x_523_; 
v___x_523_ = lean_unbox(v_a_519_);
lean_dec(v_a_519_);
if (v___x_523_ == 0)
{
lean_object* v___x_524_; lean_object* v___x_526_; 
lean_dec(v_name_516_);
lean_dec_ref(v_attr_511_);
v___x_524_ = lean_obj_once(&l_Lean_registerBuiltinAttribute___closed__1, &l_Lean_registerBuiltinAttribute___closed__1_once, _init_l_Lean_registerBuiltinAttribute___closed__1);
if (v_isShared_522_ == 0)
{
lean_ctor_set_tag(v___x_521_, 1);
lean_ctor_set(v___x_521_, 0, v___x_524_);
v___x_526_ = v___x_521_;
goto v_reusejp_525_;
}
else
{
lean_object* v_reuseFailAlloc_527_; 
v_reuseFailAlloc_527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_527_, 0, v___x_524_);
v___x_526_ = v_reuseFailAlloc_527_;
goto v_reusejp_525_;
}
v_reusejp_525_:
{
return v___x_526_;
}
}
else
{
lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_532_; 
v___x_528_ = lean_st_ref_take(v___x_513_);
v___x_529_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1___redArg(v___x_528_, v_name_516_, v_attr_511_);
v___x_530_ = lean_st_ref_set(v___x_513_, v___x_529_);
if (v_isShared_522_ == 0)
{
lean_ctor_set(v___x_521_, 0, v___x_530_);
v___x_532_ = v___x_521_;
goto v_reusejp_531_;
}
else
{
lean_object* v_reuseFailAlloc_533_; 
v_reuseFailAlloc_533_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_533_, 0, v___x_530_);
v___x_532_ = v_reuseFailAlloc_533_;
goto v_reusejp_531_;
}
v_reusejp_531_:
{
return v___x_532_;
}
}
}
}
else
{
lean_object* v_a_535_; lean_object* v___x_537_; uint8_t v_isShared_538_; uint8_t v_isSharedCheck_542_; 
lean_dec(v_name_516_);
lean_dec_ref(v_attr_511_);
v_a_535_ = lean_ctor_get(v___x_518_, 0);
v_isSharedCheck_542_ = !lean_is_exclusive(v___x_518_);
if (v_isSharedCheck_542_ == 0)
{
v___x_537_ = v___x_518_;
v_isShared_538_ = v_isSharedCheck_542_;
goto v_resetjp_536_;
}
else
{
lean_inc(v_a_535_);
lean_dec(v___x_518_);
v___x_537_ = lean_box(0);
v_isShared_538_ = v_isSharedCheck_542_;
goto v_resetjp_536_;
}
v_resetjp_536_:
{
lean_object* v___x_540_; 
if (v_isShared_538_ == 0)
{
v___x_540_ = v___x_537_;
goto v_reusejp_539_;
}
else
{
lean_object* v_reuseFailAlloc_541_; 
v_reuseFailAlloc_541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_541_, 0, v_a_535_);
v___x_540_ = v_reuseFailAlloc_541_;
goto v_reusejp_539_;
}
v_reusejp_539_:
{
return v___x_540_;
}
}
}
}
else
{
lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; 
lean_dec_ref(v_attr_511_);
v___x_543_ = ((lean_object*)(l_Lean_registerBuiltinAttribute___closed__2));
v___x_544_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_516_, v___x_517_);
v___x_545_ = lean_string_append(v___x_543_, v___x_544_);
lean_dec_ref(v___x_544_);
v___x_546_ = ((lean_object*)(l_Lean_registerBuiltinAttribute___closed__3));
v___x_547_ = lean_string_append(v___x_545_, v___x_546_);
v___x_548_ = lean_mk_io_user_error(v___x_547_);
v___x_549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_549_, 0, v___x_548_);
return v___x_549_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerBuiltinAttribute___boxed(lean_object* v_attr_550_, lean_object* v_a_551_){
_start:
{
lean_object* v_res_552_; 
v_res_552_ = l_Lean_registerBuiltinAttribute(v_attr_550_);
return v_res_552_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0(lean_object* v_00_u03b2_553_, lean_object* v_m_554_, lean_object* v_a_555_){
_start:
{
uint8_t v___x_556_; 
v___x_556_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(v_m_554_, v_a_555_);
return v___x_556_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___boxed(lean_object* v_00_u03b2_557_, lean_object* v_m_558_, lean_object* v_a_559_){
_start:
{
uint8_t v_res_560_; lean_object* v_r_561_; 
v_res_560_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0(v_00_u03b2_557_, v_m_558_, v_a_559_);
lean_dec(v_a_559_);
lean_dec_ref(v_m_558_);
v_r_561_ = lean_box(v_res_560_);
return v_r_561_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1(lean_object* v_00_u03b2_562_, lean_object* v_m_563_, lean_object* v_a_564_, lean_object* v_b_565_){
_start:
{
lean_object* v___x_566_; 
v___x_566_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1___redArg(v_m_563_, v_a_564_, v_b_565_);
return v___x_566_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0_spec__0(lean_object* v_00_u03b2_567_, lean_object* v_a_568_, lean_object* v_x_569_){
_start:
{
uint8_t v___x_570_; 
v___x_570_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0_spec__0___redArg(v_a_568_, v_x_569_);
return v___x_570_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0_spec__0___boxed(lean_object* v_00_u03b2_571_, lean_object* v_a_572_, lean_object* v_x_573_){
_start:
{
uint8_t v_res_574_; lean_object* v_r_575_; 
v_res_574_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0_spec__0(v_00_u03b2_571_, v_a_572_, v_x_573_);
lean_dec(v_x_573_);
lean_dec(v_a_572_);
v_r_575_ = lean_box(v_res_574_);
return v_r_575_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2(lean_object* v_00_u03b2_576_, lean_object* v_data_577_){
_start:
{
lean_object* v___x_578_; 
v___x_578_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2___redArg(v_data_577_);
return v___x_578_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__3(lean_object* v_00_u03b2_579_, lean_object* v_a_580_, lean_object* v_b_581_, lean_object* v_x_582_){
_start:
{
lean_object* v___x_583_; 
v___x_583_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__3___redArg(v_a_580_, v_b_581_, v_x_582_);
return v___x_583_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_584_, lean_object* v_i_585_, lean_object* v_source_586_, lean_object* v_target_587_){
_start:
{
lean_object* v___x_588_; 
v___x_588_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2_spec__3___redArg(v_i_585_, v_source_586_, v_target_587_);
return v___x_588_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_589_, lean_object* v_x_590_, lean_object* v_x_591_){
_start:
{
lean_object* v___x_592_; 
v___x_592_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2_spec__3_spec__4___redArg(v_x_590_, v_x_591_);
return v___x_592_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0_spec__0_spec__1___closed__0(void){
_start:
{
lean_object* v___x_593_; 
v___x_593_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_593_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0_spec__0_spec__1___closed__1(void){
_start:
{
lean_object* v___x_594_; lean_object* v___x_595_; 
v___x_594_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0_spec__0_spec__1___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0_spec__0_spec__1___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0_spec__0_spec__1___closed__0);
v___x_595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_595_, 0, v___x_594_);
return v___x_595_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0_spec__0_spec__1___closed__2(void){
_start:
{
lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; 
v___x_596_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0_spec__0_spec__1___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0_spec__0_spec__1___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0_spec__0_spec__1___closed__1);
v___x_597_ = lean_unsigned_to_nat(0u);
v___x_598_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_598_, 0, v___x_597_);
lean_ctor_set(v___x_598_, 1, v___x_597_);
lean_ctor_set(v___x_598_, 2, v___x_597_);
lean_ctor_set(v___x_598_, 3, v___x_597_);
lean_ctor_set(v___x_598_, 4, v___x_596_);
lean_ctor_set(v___x_598_, 5, v___x_596_);
lean_ctor_set(v___x_598_, 6, v___x_596_);
lean_ctor_set(v___x_598_, 7, v___x_596_);
lean_ctor_set(v___x_598_, 8, v___x_596_);
lean_ctor_set(v___x_598_, 9, v___x_596_);
return v___x_598_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0_spec__0_spec__1___closed__3(void){
_start:
{
lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; 
v___x_599_ = lean_unsigned_to_nat(32u);
v___x_600_ = lean_mk_empty_array_with_capacity(v___x_599_);
v___x_601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_601_, 0, v___x_600_);
return v___x_601_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0_spec__0_spec__1___closed__4(void){
_start:
{
size_t v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; 
v___x_602_ = ((size_t)5ULL);
v___x_603_ = lean_unsigned_to_nat(0u);
v___x_604_ = lean_unsigned_to_nat(32u);
v___x_605_ = lean_mk_empty_array_with_capacity(v___x_604_);
v___x_606_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0_spec__0_spec__1___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0_spec__0_spec__1___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0_spec__0_spec__1___closed__3);
v___x_607_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_607_, 0, v___x_606_);
lean_ctor_set(v___x_607_, 1, v___x_605_);
lean_ctor_set(v___x_607_, 2, v___x_603_);
lean_ctor_set(v___x_607_, 3, v___x_603_);
lean_ctor_set_usize(v___x_607_, 4, v___x_602_);
return v___x_607_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0_spec__0_spec__1___closed__5(void){
_start:
{
lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; 
v___x_608_ = lean_box(1);
v___x_609_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0_spec__0_spec__1___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0_spec__0_spec__1___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0_spec__0_spec__1___closed__4);
v___x_610_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0_spec__0_spec__1___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0_spec__0_spec__1___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0_spec__0_spec__1___closed__1);
v___x_611_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_611_, 0, v___x_610_);
lean_ctor_set(v___x_611_, 1, v___x_609_);
lean_ctor_set(v___x_611_, 2, v___x_608_);
return v___x_611_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0_spec__0_spec__1(lean_object* v_msgData_612_, lean_object* v___y_613_, lean_object* v___y_614_){
_start:
{
lean_object* v___x_616_; lean_object* v_env_617_; lean_object* v_options_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; 
v___x_616_ = lean_st_ref_get(v___y_614_);
v_env_617_ = lean_ctor_get(v___x_616_, 0);
lean_inc_ref(v_env_617_);
lean_dec(v___x_616_);
v_options_618_ = lean_ctor_get(v___y_613_, 2);
v___x_619_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0_spec__0_spec__1___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0_spec__0_spec__1___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0_spec__0_spec__1___closed__2);
v___x_620_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0_spec__0_spec__1___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0_spec__0_spec__1___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0_spec__0_spec__1___closed__5);
lean_inc_ref(v_options_618_);
v___x_621_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_621_, 0, v_env_617_);
lean_ctor_set(v___x_621_, 1, v___x_619_);
lean_ctor_set(v___x_621_, 2, v___x_620_);
lean_ctor_set(v___x_621_, 3, v_options_618_);
v___x_622_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_622_, 0, v___x_621_);
lean_ctor_set(v___x_622_, 1, v_msgData_612_);
v___x_623_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_623_, 0, v___x_622_);
return v___x_623_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0_spec__0_spec__1___boxed(lean_object* v_msgData_624_, lean_object* v___y_625_, lean_object* v___y_626_, lean_object* v___y_627_){
_start:
{
lean_object* v_res_628_; 
v_res_628_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0_spec__0_spec__1(v_msgData_624_, v___y_625_, v___y_626_);
lean_dec(v___y_626_);
lean_dec_ref(v___y_625_);
return v_res_628_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0_spec__0___redArg(lean_object* v_msg_629_, lean_object* v___y_630_, lean_object* v___y_631_){
_start:
{
lean_object* v_ref_633_; lean_object* v___x_634_; lean_object* v_a_635_; lean_object* v___x_637_; uint8_t v_isShared_638_; uint8_t v_isSharedCheck_643_; 
v_ref_633_ = lean_ctor_get(v___y_630_, 5);
v___x_634_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0_spec__0_spec__1(v_msg_629_, v___y_630_, v___y_631_);
v_a_635_ = lean_ctor_get(v___x_634_, 0);
v_isSharedCheck_643_ = !lean_is_exclusive(v___x_634_);
if (v_isSharedCheck_643_ == 0)
{
v___x_637_ = v___x_634_;
v_isShared_638_ = v_isSharedCheck_643_;
goto v_resetjp_636_;
}
else
{
lean_inc(v_a_635_);
lean_dec(v___x_634_);
v___x_637_ = lean_box(0);
v_isShared_638_ = v_isSharedCheck_643_;
goto v_resetjp_636_;
}
v_resetjp_636_:
{
lean_object* v___x_639_; lean_object* v___x_641_; 
lean_inc(v_ref_633_);
v___x_639_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_639_, 0, v_ref_633_);
lean_ctor_set(v___x_639_, 1, v_a_635_);
if (v_isShared_638_ == 0)
{
lean_ctor_set_tag(v___x_637_, 1);
lean_ctor_set(v___x_637_, 0, v___x_639_);
v___x_641_ = v___x_637_;
goto v_reusejp_640_;
}
else
{
lean_object* v_reuseFailAlloc_642_; 
v_reuseFailAlloc_642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_642_, 0, v___x_639_);
v___x_641_ = v_reuseFailAlloc_642_;
goto v_reusejp_640_;
}
v_reusejp_640_:
{
return v___x_641_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0_spec__0___redArg___boxed(lean_object* v_msg_644_, lean_object* v___y_645_, lean_object* v___y_646_, lean_object* v___y_647_){
_start:
{
lean_object* v_res_648_; 
v_res_648_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0_spec__0___redArg(v_msg_644_, v___y_645_, v___y_646_);
lean_dec(v___y_646_);
lean_dec_ref(v___y_645_);
return v_res_648_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg(lean_object* v_ref_649_, lean_object* v_msg_650_, lean_object* v___y_651_, lean_object* v___y_652_){
_start:
{
lean_object* v_fileName_654_; lean_object* v_fileMap_655_; lean_object* v_options_656_; lean_object* v_currRecDepth_657_; lean_object* v_maxRecDepth_658_; lean_object* v_ref_659_; lean_object* v_currNamespace_660_; lean_object* v_openDecls_661_; lean_object* v_initHeartbeats_662_; lean_object* v_maxHeartbeats_663_; lean_object* v_quotContext_664_; lean_object* v_currMacroScope_665_; uint8_t v_diag_666_; lean_object* v_cancelTk_x3f_667_; uint8_t v_suppressElabErrors_668_; lean_object* v_inheritedTraceOptions_669_; lean_object* v_ref_670_; lean_object* v___x_671_; lean_object* v___x_672_; 
v_fileName_654_ = lean_ctor_get(v___y_651_, 0);
v_fileMap_655_ = lean_ctor_get(v___y_651_, 1);
v_options_656_ = lean_ctor_get(v___y_651_, 2);
v_currRecDepth_657_ = lean_ctor_get(v___y_651_, 3);
v_maxRecDepth_658_ = lean_ctor_get(v___y_651_, 4);
v_ref_659_ = lean_ctor_get(v___y_651_, 5);
v_currNamespace_660_ = lean_ctor_get(v___y_651_, 6);
v_openDecls_661_ = lean_ctor_get(v___y_651_, 7);
v_initHeartbeats_662_ = lean_ctor_get(v___y_651_, 8);
v_maxHeartbeats_663_ = lean_ctor_get(v___y_651_, 9);
v_quotContext_664_ = lean_ctor_get(v___y_651_, 10);
v_currMacroScope_665_ = lean_ctor_get(v___y_651_, 11);
v_diag_666_ = lean_ctor_get_uint8(v___y_651_, sizeof(void*)*14);
v_cancelTk_x3f_667_ = lean_ctor_get(v___y_651_, 12);
v_suppressElabErrors_668_ = lean_ctor_get_uint8(v___y_651_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_669_ = lean_ctor_get(v___y_651_, 13);
v_ref_670_ = l_Lean_replaceRef(v_ref_649_, v_ref_659_);
lean_inc_ref(v_inheritedTraceOptions_669_);
lean_inc(v_cancelTk_x3f_667_);
lean_inc(v_currMacroScope_665_);
lean_inc(v_quotContext_664_);
lean_inc(v_maxHeartbeats_663_);
lean_inc(v_initHeartbeats_662_);
lean_inc(v_openDecls_661_);
lean_inc(v_currNamespace_660_);
lean_inc(v_maxRecDepth_658_);
lean_inc(v_currRecDepth_657_);
lean_inc_ref(v_options_656_);
lean_inc_ref(v_fileMap_655_);
lean_inc_ref(v_fileName_654_);
v___x_671_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_671_, 0, v_fileName_654_);
lean_ctor_set(v___x_671_, 1, v_fileMap_655_);
lean_ctor_set(v___x_671_, 2, v_options_656_);
lean_ctor_set(v___x_671_, 3, v_currRecDepth_657_);
lean_ctor_set(v___x_671_, 4, v_maxRecDepth_658_);
lean_ctor_set(v___x_671_, 5, v_ref_670_);
lean_ctor_set(v___x_671_, 6, v_currNamespace_660_);
lean_ctor_set(v___x_671_, 7, v_openDecls_661_);
lean_ctor_set(v___x_671_, 8, v_initHeartbeats_662_);
lean_ctor_set(v___x_671_, 9, v_maxHeartbeats_663_);
lean_ctor_set(v___x_671_, 10, v_quotContext_664_);
lean_ctor_set(v___x_671_, 11, v_currMacroScope_665_);
lean_ctor_set(v___x_671_, 12, v_cancelTk_x3f_667_);
lean_ctor_set(v___x_671_, 13, v_inheritedTraceOptions_669_);
lean_ctor_set_uint8(v___x_671_, sizeof(void*)*14, v_diag_666_);
lean_ctor_set_uint8(v___x_671_, sizeof(void*)*14 + 1, v_suppressElabErrors_668_);
v___x_672_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0_spec__0___redArg(v_msg_650_, v___x_671_, v___y_652_);
lean_dec_ref(v___x_671_);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0_spec__0(lean_object* v_00_u03b1_740_, lean_object* v_msg_741_, lean_object* v___y_742_, lean_object* v___y_743_){
_start:
{
lean_object* v___x_745_; 
v___x_745_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0_spec__0___redArg(v_msg_741_, v___y_742_, v___y_743_);
return v___x_745_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0_spec__0___boxed(lean_object* v_00_u03b1_746_, lean_object* v_msg_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_){
_start:
{
lean_object* v_res_751_; 
v_res_751_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0_spec__0(v_00_u03b1_746_, v_msg_747_, v___y_748_, v___y_749_);
lean_dec(v___y_749_);
lean_dec_ref(v___y_748_);
return v_res_751_;
}
}
static lean_object* _init_l_Lean_Attribute_Builtin_getIdent_x3f___closed__5(void){
_start:
{
lean_object* v___x_765_; lean_object* v___x_766_; 
v___x_765_ = ((lean_object*)(l_Lean_Attribute_Builtin_getIdent_x3f___closed__4));
v___x_766_ = l_Lean_stringToMessageData(v___x_765_);
return v___x_766_;
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getIdent_x3f(lean_object* v_stx_767_, lean_object* v_a_768_, lean_object* v_a_769_){
_start:
{
lean_object* v___x_779_; lean_object* v___x_780_; uint8_t v___x_781_; 
lean_inc(v_stx_767_);
v___x_779_ = l_Lean_Syntax_getKind(v_stx_767_);
v___x_780_ = ((lean_object*)(l_Lean_Attribute_Builtin_ensureNoArgs___closed__6));
v___x_781_ = lean_name_eq(v___x_779_, v___x_780_);
if (v___x_781_ == 0)
{
lean_object* v___x_782_; uint8_t v___x_783_; 
v___x_782_ = ((lean_object*)(l_Lean_Attribute_Builtin_getIdent_x3f___closed__1));
v___x_783_ = lean_name_eq(v___x_779_, v___x_782_);
if (v___x_783_ == 0)
{
lean_object* v___x_784_; uint8_t v___x_785_; 
v___x_784_ = ((lean_object*)(l_Lean_Attribute_Builtin_getIdent_x3f___closed__3));
v___x_785_ = lean_name_eq(v___x_779_, v___x_784_);
lean_dec(v___x_779_);
if (v___x_785_ == 0)
{
lean_object* v___x_786_; lean_object* v___x_787_; 
v___x_786_ = lean_obj_once(&l_Lean_Attribute_Builtin_getIdent_x3f___closed__5, &l_Lean_Attribute_Builtin_getIdent_x3f___closed__5_once, _init_l_Lean_Attribute_Builtin_getIdent_x3f___closed__5);
v___x_787_ = l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg(v_stx_767_, v___x_786_, v_a_768_, v_a_769_);
lean_dec(v_stx_767_);
return v___x_787_;
}
else
{
goto v___jp_771_;
}
}
else
{
lean_dec(v___x_779_);
goto v___jp_771_;
}
}
else
{
lean_object* v___x_788_; lean_object* v___x_789_; uint8_t v___x_790_; 
lean_dec(v___x_779_);
v___x_788_ = lean_unsigned_to_nat(1u);
v___x_789_ = l_Lean_Syntax_getArg(v_stx_767_, v___x_788_);
lean_dec(v_stx_767_);
v___x_790_ = l_Lean_Syntax_isNone(v___x_789_);
if (v___x_790_ == 0)
{
if (v___x_781_ == 0)
{
lean_dec(v___x_789_);
goto v___jp_776_;
}
else
{
lean_object* v___x_791_; lean_object* v___x_792_; uint8_t v___x_793_; 
v___x_791_ = lean_unsigned_to_nat(0u);
v___x_792_ = l_Lean_Syntax_getArg(v___x_789_, v___x_791_);
lean_dec(v___x_789_);
v___x_793_ = l_Lean_Syntax_isIdent(v___x_792_);
if (v___x_793_ == 0)
{
lean_dec(v___x_792_);
goto v___jp_776_;
}
else
{
lean_object* v___x_794_; lean_object* v___x_795_; 
v___x_794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_794_, 0, v___x_792_);
v___x_795_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_795_, 0, v___x_794_);
return v___x_795_;
}
}
}
else
{
lean_dec(v___x_789_);
goto v___jp_776_;
}
}
v___jp_771_:
{
lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; 
v___x_772_ = lean_unsigned_to_nat(1u);
v___x_773_ = l_Lean_Syntax_getArg(v_stx_767_, v___x_772_);
lean_dec(v_stx_767_);
v___x_774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_774_, 0, v___x_773_);
v___x_775_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_775_, 0, v___x_774_);
return v___x_775_;
}
v___jp_776_:
{
lean_object* v___x_777_; lean_object* v___x_778_; 
v___x_777_ = lean_box(0);
v___x_778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_778_, 0, v___x_777_);
return v___x_778_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getIdent_x3f___boxed(lean_object* v_stx_796_, lean_object* v_a_797_, lean_object* v_a_798_, lean_object* v_a_799_){
_start:
{
lean_object* v_res_800_; 
v_res_800_ = l_Lean_Attribute_Builtin_getIdent_x3f(v_stx_796_, v_a_797_, v_a_798_);
lean_dec(v_a_798_);
lean_dec_ref(v_a_797_);
return v_res_800_;
}
}
static lean_object* _init_l_Lean_Attribute_Builtin_getIdent___closed__1(void){
_start:
{
lean_object* v___x_802_; lean_object* v___x_803_; 
v___x_802_ = ((lean_object*)(l_Lean_Attribute_Builtin_getIdent___closed__0));
v___x_803_ = l_Lean_stringToMessageData(v___x_802_);
return v___x_803_;
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getIdent(lean_object* v_stx_804_, lean_object* v_a_805_, lean_object* v_a_806_){
_start:
{
lean_object* v___x_808_; 
lean_inc(v_stx_804_);
v___x_808_ = l_Lean_Attribute_Builtin_getIdent_x3f(v_stx_804_, v_a_805_, v_a_806_);
if (lean_obj_tag(v___x_808_) == 0)
{
lean_object* v_a_809_; lean_object* v___x_811_; uint8_t v_isShared_812_; uint8_t v_isSharedCheck_822_; 
v_a_809_ = lean_ctor_get(v___x_808_, 0);
v_isSharedCheck_822_ = !lean_is_exclusive(v___x_808_);
if (v_isSharedCheck_822_ == 0)
{
v___x_811_ = v___x_808_;
v_isShared_812_ = v_isSharedCheck_822_;
goto v_resetjp_810_;
}
else
{
lean_inc(v_a_809_);
lean_dec(v___x_808_);
v___x_811_ = lean_box(0);
v_isShared_812_ = v_isSharedCheck_822_;
goto v_resetjp_810_;
}
v_resetjp_810_:
{
if (lean_obj_tag(v_a_809_) == 0)
{
lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; 
lean_del_object(v___x_811_);
v___x_813_ = lean_obj_once(&l_Lean_Attribute_Builtin_getIdent___closed__1, &l_Lean_Attribute_Builtin_getIdent___closed__1_once, _init_l_Lean_Attribute_Builtin_getIdent___closed__1);
lean_inc(v_stx_804_);
v___x_814_ = l_Lean_MessageData_ofSyntax(v_stx_804_);
v___x_815_ = l_Lean_indentD(v___x_814_);
v___x_816_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_816_, 0, v___x_813_);
lean_ctor_set(v___x_816_, 1, v___x_815_);
v___x_817_ = l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg(v_stx_804_, v___x_816_, v_a_805_, v_a_806_);
lean_dec(v_stx_804_);
return v___x_817_;
}
else
{
lean_object* v_val_818_; lean_object* v___x_820_; 
lean_dec(v_stx_804_);
v_val_818_ = lean_ctor_get(v_a_809_, 0);
lean_inc(v_val_818_);
lean_dec_ref(v_a_809_);
if (v_isShared_812_ == 0)
{
lean_ctor_set(v___x_811_, 0, v_val_818_);
v___x_820_ = v___x_811_;
goto v_reusejp_819_;
}
else
{
lean_object* v_reuseFailAlloc_821_; 
v_reuseFailAlloc_821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_821_, 0, v_val_818_);
v___x_820_ = v_reuseFailAlloc_821_;
goto v_reusejp_819_;
}
v_reusejp_819_:
{
return v___x_820_;
}
}
}
}
else
{
lean_object* v_a_823_; lean_object* v___x_825_; uint8_t v_isShared_826_; uint8_t v_isSharedCheck_830_; 
lean_dec(v_stx_804_);
v_a_823_ = lean_ctor_get(v___x_808_, 0);
v_isSharedCheck_830_ = !lean_is_exclusive(v___x_808_);
if (v_isSharedCheck_830_ == 0)
{
v___x_825_ = v___x_808_;
v_isShared_826_ = v_isSharedCheck_830_;
goto v_resetjp_824_;
}
else
{
lean_inc(v_a_823_);
lean_dec(v___x_808_);
v___x_825_ = lean_box(0);
v_isShared_826_ = v_isSharedCheck_830_;
goto v_resetjp_824_;
}
v_resetjp_824_:
{
lean_object* v___x_828_; 
if (v_isShared_826_ == 0)
{
v___x_828_ = v___x_825_;
goto v_reusejp_827_;
}
else
{
lean_object* v_reuseFailAlloc_829_; 
v_reuseFailAlloc_829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_829_, 0, v_a_823_);
v___x_828_ = v_reuseFailAlloc_829_;
goto v_reusejp_827_;
}
v_reusejp_827_:
{
return v___x_828_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getIdent___boxed(lean_object* v_stx_831_, lean_object* v_a_832_, lean_object* v_a_833_, lean_object* v_a_834_){
_start:
{
lean_object* v_res_835_; 
v_res_835_ = l_Lean_Attribute_Builtin_getIdent(v_stx_831_, v_a_832_, v_a_833_);
lean_dec(v_a_833_);
lean_dec_ref(v_a_832_);
return v_res_835_;
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getId_x3f(lean_object* v_stx_836_, lean_object* v_a_837_, lean_object* v_a_838_){
_start:
{
lean_object* v___x_840_; 
v___x_840_ = l_Lean_Attribute_Builtin_getIdent_x3f(v_stx_836_, v_a_837_, v_a_838_);
if (lean_obj_tag(v___x_840_) == 0)
{
lean_object* v_a_841_; lean_object* v___x_843_; uint8_t v_isShared_844_; uint8_t v_isSharedCheck_861_; 
v_a_841_ = lean_ctor_get(v___x_840_, 0);
v_isSharedCheck_861_ = !lean_is_exclusive(v___x_840_);
if (v_isSharedCheck_861_ == 0)
{
v___x_843_ = v___x_840_;
v_isShared_844_ = v_isSharedCheck_861_;
goto v_resetjp_842_;
}
else
{
lean_inc(v_a_841_);
lean_dec(v___x_840_);
v___x_843_ = lean_box(0);
v_isShared_844_ = v_isSharedCheck_861_;
goto v_resetjp_842_;
}
v_resetjp_842_:
{
if (lean_obj_tag(v_a_841_) == 0)
{
lean_object* v___x_845_; lean_object* v___x_847_; 
v___x_845_ = lean_box(0);
if (v_isShared_844_ == 0)
{
lean_ctor_set(v___x_843_, 0, v___x_845_);
v___x_847_ = v___x_843_;
goto v_reusejp_846_;
}
else
{
lean_object* v_reuseFailAlloc_848_; 
v_reuseFailAlloc_848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_848_, 0, v___x_845_);
v___x_847_ = v_reuseFailAlloc_848_;
goto v_reusejp_846_;
}
v_reusejp_846_:
{
return v___x_847_;
}
}
else
{
lean_object* v_val_849_; lean_object* v___x_851_; uint8_t v_isShared_852_; uint8_t v_isSharedCheck_860_; 
v_val_849_ = lean_ctor_get(v_a_841_, 0);
v_isSharedCheck_860_ = !lean_is_exclusive(v_a_841_);
if (v_isSharedCheck_860_ == 0)
{
v___x_851_ = v_a_841_;
v_isShared_852_ = v_isSharedCheck_860_;
goto v_resetjp_850_;
}
else
{
lean_inc(v_val_849_);
lean_dec(v_a_841_);
v___x_851_ = lean_box(0);
v_isShared_852_ = v_isSharedCheck_860_;
goto v_resetjp_850_;
}
v_resetjp_850_:
{
lean_object* v___x_853_; lean_object* v___x_855_; 
v___x_853_ = l_Lean_Syntax_getId(v_val_849_);
lean_dec(v_val_849_);
if (v_isShared_852_ == 0)
{
lean_ctor_set(v___x_851_, 0, v___x_853_);
v___x_855_ = v___x_851_;
goto v_reusejp_854_;
}
else
{
lean_object* v_reuseFailAlloc_859_; 
v_reuseFailAlloc_859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_859_, 0, v___x_853_);
v___x_855_ = v_reuseFailAlloc_859_;
goto v_reusejp_854_;
}
v_reusejp_854_:
{
lean_object* v___x_857_; 
if (v_isShared_844_ == 0)
{
lean_ctor_set(v___x_843_, 0, v___x_855_);
v___x_857_ = v___x_843_;
goto v_reusejp_856_;
}
else
{
lean_object* v_reuseFailAlloc_858_; 
v_reuseFailAlloc_858_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_858_, 0, v___x_855_);
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
}
}
else
{
lean_object* v_a_862_; lean_object* v___x_864_; uint8_t v_isShared_865_; uint8_t v_isSharedCheck_869_; 
v_a_862_ = lean_ctor_get(v___x_840_, 0);
v_isSharedCheck_869_ = !lean_is_exclusive(v___x_840_);
if (v_isSharedCheck_869_ == 0)
{
v___x_864_ = v___x_840_;
v_isShared_865_ = v_isSharedCheck_869_;
goto v_resetjp_863_;
}
else
{
lean_inc(v_a_862_);
lean_dec(v___x_840_);
v___x_864_ = lean_box(0);
v_isShared_865_ = v_isSharedCheck_869_;
goto v_resetjp_863_;
}
v_resetjp_863_:
{
lean_object* v___x_867_; 
if (v_isShared_865_ == 0)
{
v___x_867_ = v___x_864_;
goto v_reusejp_866_;
}
else
{
lean_object* v_reuseFailAlloc_868_; 
v_reuseFailAlloc_868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_868_, 0, v_a_862_);
v___x_867_ = v_reuseFailAlloc_868_;
goto v_reusejp_866_;
}
v_reusejp_866_:
{
return v___x_867_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getId_x3f___boxed(lean_object* v_stx_870_, lean_object* v_a_871_, lean_object* v_a_872_, lean_object* v_a_873_){
_start:
{
lean_object* v_res_874_; 
v_res_874_ = l_Lean_Attribute_Builtin_getId_x3f(v_stx_870_, v_a_871_, v_a_872_);
lean_dec(v_a_872_);
lean_dec_ref(v_a_871_);
return v_res_874_;
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getId(lean_object* v_stx_875_, lean_object* v_a_876_, lean_object* v_a_877_){
_start:
{
lean_object* v___x_879_; 
v___x_879_ = l_Lean_Attribute_Builtin_getIdent(v_stx_875_, v_a_876_, v_a_877_);
if (lean_obj_tag(v___x_879_) == 0)
{
lean_object* v_a_880_; lean_object* v___x_882_; uint8_t v_isShared_883_; uint8_t v_isSharedCheck_888_; 
v_a_880_ = lean_ctor_get(v___x_879_, 0);
v_isSharedCheck_888_ = !lean_is_exclusive(v___x_879_);
if (v_isSharedCheck_888_ == 0)
{
v___x_882_ = v___x_879_;
v_isShared_883_ = v_isSharedCheck_888_;
goto v_resetjp_881_;
}
else
{
lean_inc(v_a_880_);
lean_dec(v___x_879_);
v___x_882_ = lean_box(0);
v_isShared_883_ = v_isSharedCheck_888_;
goto v_resetjp_881_;
}
v_resetjp_881_:
{
lean_object* v___x_884_; lean_object* v___x_886_; 
v___x_884_ = l_Lean_Syntax_getId(v_a_880_);
lean_dec(v_a_880_);
if (v_isShared_883_ == 0)
{
lean_ctor_set(v___x_882_, 0, v___x_884_);
v___x_886_ = v___x_882_;
goto v_reusejp_885_;
}
else
{
lean_object* v_reuseFailAlloc_887_; 
v_reuseFailAlloc_887_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_887_, 0, v___x_884_);
v___x_886_ = v_reuseFailAlloc_887_;
goto v_reusejp_885_;
}
v_reusejp_885_:
{
return v___x_886_;
}
}
}
else
{
lean_object* v_a_889_; lean_object* v___x_891_; uint8_t v_isShared_892_; uint8_t v_isSharedCheck_896_; 
v_a_889_ = lean_ctor_get(v___x_879_, 0);
v_isSharedCheck_896_ = !lean_is_exclusive(v___x_879_);
if (v_isSharedCheck_896_ == 0)
{
v___x_891_ = v___x_879_;
v_isShared_892_ = v_isSharedCheck_896_;
goto v_resetjp_890_;
}
else
{
lean_inc(v_a_889_);
lean_dec(v___x_879_);
v___x_891_ = lean_box(0);
v_isShared_892_ = v_isSharedCheck_896_;
goto v_resetjp_890_;
}
v_resetjp_890_:
{
lean_object* v___x_894_; 
if (v_isShared_892_ == 0)
{
v___x_894_ = v___x_891_;
goto v_reusejp_893_;
}
else
{
lean_object* v_reuseFailAlloc_895_; 
v_reuseFailAlloc_895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_895_, 0, v_a_889_);
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
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getId___boxed(lean_object* v_stx_897_, lean_object* v_a_898_, lean_object* v_a_899_, lean_object* v_a_900_){
_start:
{
lean_object* v_res_901_; 
v_res_901_ = l_Lean_Attribute_Builtin_getId(v_stx_897_, v_a_898_, v_a_899_);
lean_dec(v_a_899_);
lean_dec_ref(v_a_898_);
return v_res_901_;
}
}
static lean_object* _init_l_Lean_getAttrParamOptPrio___closed__1(void){
_start:
{
lean_object* v___x_903_; lean_object* v___x_904_; 
v___x_903_ = ((lean_object*)(l_Lean_getAttrParamOptPrio___closed__0));
v___x_904_ = l_Lean_stringToMessageData(v___x_903_);
return v___x_904_;
}
}
LEAN_EXPORT lean_object* l_Lean_getAttrParamOptPrio(lean_object* v_optPrioStx_905_, lean_object* v_a_906_, lean_object* v_a_907_){
_start:
{
uint8_t v___x_909_; 
v___x_909_ = l_Lean_Syntax_isNone(v_optPrioStx_905_);
if (v___x_909_ == 0)
{
lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; 
v___x_910_ = lean_unsigned_to_nat(0u);
v___x_911_ = l_Lean_Syntax_getArg(v_optPrioStx_905_, v___x_910_);
v___x_912_ = l_Lean_Syntax_isNatLit_x3f(v___x_911_);
lean_dec(v___x_911_);
if (lean_obj_tag(v___x_912_) == 0)
{
lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; 
v___x_913_ = lean_obj_once(&l_Lean_getAttrParamOptPrio___closed__1, &l_Lean_getAttrParamOptPrio___closed__1_once, _init_l_Lean_getAttrParamOptPrio___closed__1);
lean_inc(v_optPrioStx_905_);
v___x_914_ = l_Lean_MessageData_ofSyntax(v_optPrioStx_905_);
v___x_915_ = l_Lean_indentD(v___x_914_);
v___x_916_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_916_, 0, v___x_913_);
lean_ctor_set(v___x_916_, 1, v___x_915_);
v___x_917_ = l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg(v_optPrioStx_905_, v___x_916_, v_a_906_, v_a_907_);
lean_dec(v_optPrioStx_905_);
return v___x_917_;
}
else
{
lean_object* v_val_918_; lean_object* v___x_920_; uint8_t v_isShared_921_; uint8_t v_isSharedCheck_925_; 
lean_dec(v_optPrioStx_905_);
v_val_918_ = lean_ctor_get(v___x_912_, 0);
v_isSharedCheck_925_ = !lean_is_exclusive(v___x_912_);
if (v_isSharedCheck_925_ == 0)
{
v___x_920_ = v___x_912_;
v_isShared_921_ = v_isSharedCheck_925_;
goto v_resetjp_919_;
}
else
{
lean_inc(v_val_918_);
lean_dec(v___x_912_);
v___x_920_ = lean_box(0);
v_isShared_921_ = v_isSharedCheck_925_;
goto v_resetjp_919_;
}
v_resetjp_919_:
{
lean_object* v___x_923_; 
if (v_isShared_921_ == 0)
{
lean_ctor_set_tag(v___x_920_, 0);
v___x_923_ = v___x_920_;
goto v_reusejp_922_;
}
else
{
lean_object* v_reuseFailAlloc_924_; 
v_reuseFailAlloc_924_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_924_, 0, v_val_918_);
v___x_923_ = v_reuseFailAlloc_924_;
goto v_reusejp_922_;
}
v_reusejp_922_:
{
return v___x_923_;
}
}
}
}
else
{
lean_object* v___x_926_; lean_object* v___x_927_; 
lean_dec(v_optPrioStx_905_);
v___x_926_ = lean_unsigned_to_nat(1000u);
v___x_927_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_927_, 0, v___x_926_);
return v___x_927_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getAttrParamOptPrio___boxed(lean_object* v_optPrioStx_928_, lean_object* v_a_929_, lean_object* v_a_930_, lean_object* v_a_931_){
_start:
{
lean_object* v_res_932_; 
v_res_932_ = l_Lean_getAttrParamOptPrio(v_optPrioStx_928_, v_a_929_, v_a_930_);
lean_dec(v_a_930_);
lean_dec_ref(v_a_929_);
return v_res_932_;
}
}
static lean_object* _init_l_Lean_Attribute_Builtin_getPrio___closed__1(void){
_start:
{
lean_object* v___x_934_; lean_object* v___x_935_; 
v___x_934_ = ((lean_object*)(l_Lean_Attribute_Builtin_getPrio___closed__0));
v___x_935_ = l_Lean_stringToMessageData(v___x_934_);
return v___x_935_;
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getPrio(lean_object* v_stx_936_, lean_object* v_a_937_, lean_object* v_a_938_){
_start:
{
lean_object* v___x_940_; lean_object* v___x_941_; uint8_t v___x_942_; 
lean_inc(v_stx_936_);
v___x_940_ = l_Lean_Syntax_getKind(v_stx_936_);
v___x_941_ = ((lean_object*)(l_Lean_Attribute_Builtin_ensureNoArgs___closed__6));
v___x_942_ = lean_name_eq(v___x_940_, v___x_941_);
lean_dec(v___x_940_);
if (v___x_942_ == 0)
{
lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; 
v___x_943_ = lean_obj_once(&l_Lean_Attribute_Builtin_getPrio___closed__1, &l_Lean_Attribute_Builtin_getPrio___closed__1_once, _init_l_Lean_Attribute_Builtin_getPrio___closed__1);
lean_inc(v_stx_936_);
v___x_944_ = l_Lean_MessageData_ofSyntax(v_stx_936_);
v___x_945_ = l_Lean_indentD(v___x_944_);
v___x_946_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_946_, 0, v___x_943_);
lean_ctor_set(v___x_946_, 1, v___x_945_);
v___x_947_ = l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg(v_stx_936_, v___x_946_, v_a_937_, v_a_938_);
lean_dec(v_stx_936_);
return v___x_947_;
}
else
{
lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; 
v___x_948_ = lean_unsigned_to_nat(1u);
v___x_949_ = l_Lean_Syntax_getArg(v_stx_936_, v___x_948_);
lean_dec(v_stx_936_);
v___x_950_ = l_Lean_getAttrParamOptPrio(v___x_949_, v_a_937_, v_a_938_);
return v___x_950_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getPrio___boxed(lean_object* v_stx_951_, lean_object* v_a_952_, lean_object* v_a_953_, lean_object* v_a_954_){
_start:
{
lean_object* v_res_955_; 
v_res_955_ = l_Lean_Attribute_Builtin_getPrio(v_stx_951_, v_a_952_, v_a_953_);
lean_dec(v_a_953_);
lean_dec_ref(v_a_952_);
return v_res_955_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__1(void){
_start:
{
lean_object* v___x_957_; lean_object* v___x_958_; 
v___x_957_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__0));
v___x_958_ = l_Lean_stringToMessageData(v___x_957_);
return v___x_958_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__3(void){
_start:
{
lean_object* v___x_960_; lean_object* v___x_961_; 
v___x_960_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__2));
v___x_961_ = l_Lean_stringToMessageData(v___x_960_);
return v___x_961_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__5(void){
_start:
{
lean_object* v___x_963_; lean_object* v___x_964_; 
v___x_963_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__4));
v___x_964_ = l_Lean_stringToMessageData(v___x_963_);
return v___x_964_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___redArg(lean_object* v_inst_965_, lean_object* v_inst_966_, lean_object* v_name_967_, uint8_t v_kind_968_){
_start:
{
lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___y_975_; 
v___x_969_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__1, &l_Lean_throwAttrMustBeGlobal___redArg___closed__1_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__1);
v___x_970_ = l_Lean_MessageData_ofName(v_name_967_);
v___x_971_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_971_, 0, v___x_969_);
lean_ctor_set(v___x_971_, 1, v___x_970_);
v___x_972_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__3, &l_Lean_throwAttrMustBeGlobal___redArg___closed__3_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__3);
v___x_973_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_973_, 0, v___x_971_);
lean_ctor_set(v___x_973_, 1, v___x_972_);
switch(v_kind_968_)
{
case 0:
{
lean_object* v___x_982_; 
v___x_982_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__0));
v___y_975_ = v___x_982_;
goto v___jp_974_;
}
case 1:
{
lean_object* v___x_983_; 
v___x_983_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__1));
v___y_975_ = v___x_983_;
goto v___jp_974_;
}
default: 
{
lean_object* v___x_984_; 
v___x_984_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__2));
v___y_975_ = v___x_984_;
goto v___jp_974_;
}
}
v___jp_974_:
{
lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; 
lean_inc_ref(v___y_975_);
v___x_976_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_976_, 0, v___y_975_);
v___x_977_ = l_Lean_MessageData_ofFormat(v___x_976_);
v___x_978_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_978_, 0, v___x_973_);
lean_ctor_set(v___x_978_, 1, v___x_977_);
v___x_979_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__5, &l_Lean_throwAttrMustBeGlobal___redArg___closed__5_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__5);
v___x_980_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_980_, 0, v___x_978_);
lean_ctor_set(v___x_980_, 1, v___x_979_);
v___x_981_ = l_Lean_throwError___redArg(v_inst_965_, v_inst_966_, v___x_980_);
return v___x_981_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___redArg___boxed(lean_object* v_inst_985_, lean_object* v_inst_986_, lean_object* v_name_987_, lean_object* v_kind_988_){
_start:
{
uint8_t v_kind_boxed_989_; lean_object* v_res_990_; 
v_kind_boxed_989_ = lean_unbox(v_kind_988_);
v_res_990_ = l_Lean_throwAttrMustBeGlobal___redArg(v_inst_985_, v_inst_986_, v_name_987_, v_kind_boxed_989_);
return v_res_990_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal(lean_object* v_m_991_, lean_object* v_inst_992_, lean_object* v_inst_993_, lean_object* v_00_u03b1_994_, lean_object* v_name_995_, uint8_t v_kind_996_){
_start:
{
lean_object* v___x_997_; 
v___x_997_ = l_Lean_throwAttrMustBeGlobal___redArg(v_inst_992_, v_inst_993_, v_name_995_, v_kind_996_);
return v___x_997_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___boxed(lean_object* v_m_998_, lean_object* v_inst_999_, lean_object* v_inst_1000_, lean_object* v_00_u03b1_1001_, lean_object* v_name_1002_, lean_object* v_kind_1003_){
_start:
{
uint8_t v_kind_boxed_1004_; lean_object* v_res_1005_; 
v_kind_boxed_1004_ = lean_unbox(v_kind_1003_);
v_res_1005_ = l_Lean_throwAttrMustBeGlobal(v_m_998_, v_inst_999_, v_inst_1000_, v_00_u03b1_1001_, v_name_1002_, v_kind_boxed_1004_);
return v_res_1005_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1(void){
_start:
{
lean_object* v___x_1007_; lean_object* v___x_1008_; 
v___x_1007_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___redArg___closed__0));
v___x_1008_ = l_Lean_stringToMessageData(v___x_1007_);
return v___x_1008_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__3(void){
_start:
{
lean_object* v___x_1010_; lean_object* v___x_1011_; 
v___x_1010_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___redArg___closed__2));
v___x_1011_ = l_Lean_stringToMessageData(v___x_1010_);
return v___x_1011_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__5(void){
_start:
{
lean_object* v___x_1013_; lean_object* v___x_1014_; 
v___x_1013_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___redArg___closed__4));
v___x_1014_ = l_Lean_stringToMessageData(v___x_1013_);
return v___x_1014_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___redArg(lean_object* v_inst_1015_, lean_object* v_inst_1016_, lean_object* v_attrName_1017_, lean_object* v_declName_1018_){
_start:
{
lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; uint8_t v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; 
v___x_1019_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1);
v___x_1020_ = l_Lean_MessageData_ofName(v_attrName_1017_);
v___x_1021_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1021_, 0, v___x_1019_);
lean_ctor_set(v___x_1021_, 1, v___x_1020_);
v___x_1022_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__3, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__3_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__3);
v___x_1023_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1023_, 0, v___x_1021_);
lean_ctor_set(v___x_1023_, 1, v___x_1022_);
v___x_1024_ = 0;
v___x_1025_ = l_Lean_MessageData_ofConstName(v_declName_1018_, v___x_1024_);
v___x_1026_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1026_, 0, v___x_1023_);
lean_ctor_set(v___x_1026_, 1, v___x_1025_);
v___x_1027_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__5, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__5_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__5);
v___x_1028_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1028_, 0, v___x_1026_);
lean_ctor_set(v___x_1028_, 1, v___x_1027_);
v___x_1029_ = l_Lean_throwError___redArg(v_inst_1015_, v_inst_1016_, v___x_1028_);
return v___x_1029_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule(lean_object* v_m_1030_, lean_object* v_inst_1031_, lean_object* v_inst_1032_, lean_object* v_00_u03b1_1033_, lean_object* v_attrName_1034_, lean_object* v_declName_1035_){
_start:
{
lean_object* v___x_1036_; 
v___x_1036_ = l_Lean_throwAttrDeclInImportedModule___redArg(v_inst_1031_, v_inst_1032_, v_attrName_1034_, v_declName_1035_);
return v___x_1036_;
}
}
static lean_object* _init_l_Lean_throwAttrNotInAsyncCtx___redArg___closed__1(void){
_start:
{
lean_object* v___x_1038_; lean_object* v___x_1039_; 
v___x_1038_ = ((lean_object*)(l_Lean_throwAttrNotInAsyncCtx___redArg___closed__0));
v___x_1039_ = l_Lean_stringToMessageData(v___x_1038_);
return v___x_1039_;
}
}
static lean_object* _init_l_Lean_throwAttrNotInAsyncCtx___redArg___closed__3(void){
_start:
{
lean_object* v___x_1041_; lean_object* v___x_1042_; 
v___x_1041_ = ((lean_object*)(l_Lean_throwAttrNotInAsyncCtx___redArg___closed__2));
v___x_1042_ = l_Lean_stringToMessageData(v___x_1041_);
return v___x_1042_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___redArg(lean_object* v_inst_1043_, lean_object* v_inst_1044_, lean_object* v_attrName_1045_, lean_object* v_declName_1046_, lean_object* v_asyncPrefix_x3f_1047_){
_start:
{
lean_object* v___y_1049_; 
if (lean_obj_tag(v_asyncPrefix_x3f_1047_) == 0)
{
lean_object* v___x_1062_; 
v___x_1062_ = l_Lean_MessageData_nil;
v___y_1049_ = v___x_1062_;
goto v___jp_1048_;
}
else
{
lean_object* v_val_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; 
v_val_1063_ = lean_ctor_get(v_asyncPrefix_x3f_1047_, 0);
lean_inc(v_val_1063_);
lean_dec_ref(v_asyncPrefix_x3f_1047_);
v___x_1064_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___redArg___closed__3, &l_Lean_throwAttrNotInAsyncCtx___redArg___closed__3_once, _init_l_Lean_throwAttrNotInAsyncCtx___redArg___closed__3);
v___x_1065_ = l_Lean_MessageData_ofName(v_val_1063_);
v___x_1066_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1066_, 0, v___x_1064_);
lean_ctor_set(v___x_1066_, 1, v___x_1065_);
v___x_1067_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__5, &l_Lean_throwAttrMustBeGlobal___redArg___closed__5_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__5);
v___x_1068_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1068_, 0, v___x_1066_);
lean_ctor_set(v___x_1068_, 1, v___x_1067_);
v___y_1049_ = v___x_1068_;
goto v___jp_1048_;
}
v___jp_1048_:
{
lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; uint8_t v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; 
v___x_1050_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1);
v___x_1051_ = l_Lean_MessageData_ofName(v_attrName_1045_);
v___x_1052_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1052_, 0, v___x_1050_);
lean_ctor_set(v___x_1052_, 1, v___x_1051_);
v___x_1053_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__3, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__3_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__3);
v___x_1054_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1054_, 0, v___x_1052_);
lean_ctor_set(v___x_1054_, 1, v___x_1053_);
v___x_1055_ = 0;
v___x_1056_ = l_Lean_MessageData_ofConstName(v_declName_1046_, v___x_1055_);
v___x_1057_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1057_, 0, v___x_1054_);
lean_ctor_set(v___x_1057_, 1, v___x_1056_);
v___x_1058_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___redArg___closed__1, &l_Lean_throwAttrNotInAsyncCtx___redArg___closed__1_once, _init_l_Lean_throwAttrNotInAsyncCtx___redArg___closed__1);
v___x_1059_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1059_, 0, v___x_1057_);
lean_ctor_set(v___x_1059_, 1, v___x_1058_);
v___x_1060_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1060_, 0, v___x_1059_);
lean_ctor_set(v___x_1060_, 1, v___y_1049_);
v___x_1061_ = l_Lean_throwError___redArg(v_inst_1043_, v_inst_1044_, v___x_1060_);
return v___x_1061_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx(lean_object* v_m_1069_, lean_object* v_inst_1070_, lean_object* v_inst_1071_, lean_object* v_00_u03b1_1072_, lean_object* v_attrName_1073_, lean_object* v_declName_1074_, lean_object* v_asyncPrefix_x3f_1075_){
_start:
{
lean_object* v___x_1076_; 
v___x_1076_ = l_Lean_throwAttrNotInAsyncCtx___redArg(v_inst_1070_, v_inst_1071_, v_attrName_1073_, v_declName_1074_, v_asyncPrefix_x3f_1075_);
return v___x_1076_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1(void){
_start:
{
lean_object* v___x_1078_; lean_object* v___x_1079_; 
v___x_1078_ = ((lean_object*)(l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__0));
v___x_1079_ = l_Lean_stringToMessageData(v___x_1078_);
return v___x_1079_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__3(void){
_start:
{
lean_object* v___x_1081_; lean_object* v___x_1082_; 
v___x_1081_ = ((lean_object*)(l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__2));
v___x_1082_ = l_Lean_stringToMessageData(v___x_1081_);
return v___x_1082_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__5(void){
_start:
{
lean_object* v___x_1084_; lean_object* v___x_1085_; 
v___x_1084_ = ((lean_object*)(l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__4));
v___x_1085_ = l_Lean_stringToMessageData(v___x_1084_);
return v___x_1085_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__7(void){
_start:
{
lean_object* v___x_1087_; lean_object* v___x_1088_; 
v___x_1087_ = ((lean_object*)(l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__6));
v___x_1088_ = l_Lean_stringToMessageData(v___x_1087_);
return v___x_1088_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclNotOfExpectedType___redArg(lean_object* v_inst_1089_, lean_object* v_inst_1090_, lean_object* v_attrName_1091_, lean_object* v_declName_1092_, lean_object* v_givenType_1093_, lean_object* v_expectedType_1094_){
_start:
{
lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; uint8_t v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; 
v___x_1095_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1);
v___x_1096_ = l_Lean_MessageData_ofName(v_attrName_1091_);
lean_inc_ref(v___x_1096_);
v___x_1097_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1097_, 0, v___x_1095_);
lean_ctor_set(v___x_1097_, 1, v___x_1096_);
v___x_1098_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1, &l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1);
v___x_1099_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1099_, 0, v___x_1097_);
lean_ctor_set(v___x_1099_, 1, v___x_1098_);
v___x_1100_ = 0;
v___x_1101_ = l_Lean_MessageData_ofConstName(v_declName_1092_, v___x_1100_);
v___x_1102_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1102_, 0, v___x_1099_);
lean_ctor_set(v___x_1102_, 1, v___x_1101_);
v___x_1103_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__3, &l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__3_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__3);
v___x_1104_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1104_, 0, v___x_1102_);
lean_ctor_set(v___x_1104_, 1, v___x_1103_);
v___x_1105_ = l_Lean_indentExpr(v_givenType_1093_);
v___x_1106_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1106_, 0, v___x_1104_);
lean_ctor_set(v___x_1106_, 1, v___x_1105_);
v___x_1107_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__5, &l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__5_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__5);
v___x_1108_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1108_, 0, v___x_1106_);
lean_ctor_set(v___x_1108_, 1, v___x_1107_);
v___x_1109_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1109_, 0, v___x_1108_);
lean_ctor_set(v___x_1109_, 1, v___x_1096_);
v___x_1110_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__7, &l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__7_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__7);
v___x_1111_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1111_, 0, v___x_1109_);
lean_ctor_set(v___x_1111_, 1, v___x_1110_);
v___x_1112_ = l_Lean_indentExpr(v_expectedType_1094_);
v___x_1113_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1113_, 0, v___x_1111_);
lean_ctor_set(v___x_1113_, 1, v___x_1112_);
v___x_1114_ = l_Lean_throwError___redArg(v_inst_1089_, v_inst_1090_, v___x_1113_);
return v___x_1114_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclNotOfExpectedType(lean_object* v_m_1115_, lean_object* v_inst_1116_, lean_object* v_inst_1117_, lean_object* v_00_u03b1_1118_, lean_object* v_attrName_1119_, lean_object* v_declName_1120_, lean_object* v_givenType_1121_, lean_object* v_expectedType_1122_){
_start:
{
lean_object* v___x_1123_; 
v___x_1123_ = l_Lean_throwAttrDeclNotOfExpectedType___redArg(v_inst_1116_, v_inst_1117_, v_attrName_1119_, v_declName_1120_, v_givenType_1121_, v_expectedType_1122_);
return v___x_1123_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1___redArg(lean_object* v_constName_1124_, uint8_t v_skipRealize_1125_, lean_object* v___y_1126_){
_start:
{
lean_object* v___x_1128_; lean_object* v_env_1129_; uint8_t v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; 
v___x_1128_ = lean_st_ref_get(v___y_1126_);
v_env_1129_ = lean_ctor_get(v___x_1128_, 0);
lean_inc_ref(v_env_1129_);
lean_dec(v___x_1128_);
v___x_1130_ = l_Lean_Environment_contains(v_env_1129_, v_constName_1124_, v_skipRealize_1125_);
v___x_1131_ = lean_box(v___x_1130_);
v___x_1132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1132_, 0, v___x_1131_);
return v___x_1132_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1___redArg___boxed(lean_object* v_constName_1133_, lean_object* v_skipRealize_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_){
_start:
{
uint8_t v_skipRealize_boxed_1137_; lean_object* v_res_1138_; 
v_skipRealize_boxed_1137_ = lean_unbox(v_skipRealize_1134_);
v_res_1138_ = l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1___redArg(v_constName_1133_, v_skipRealize_boxed_1137_, v___y_1135_);
lean_dec(v___y_1135_);
return v_res_1138_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1(lean_object* v_constName_1139_, uint8_t v_skipRealize_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_){
_start:
{
lean_object* v___x_1144_; 
v___x_1144_ = l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1___redArg(v_constName_1139_, v_skipRealize_1140_, v___y_1142_);
return v___x_1144_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1___boxed(lean_object* v_constName_1145_, lean_object* v_skipRealize_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_){
_start:
{
uint8_t v_skipRealize_boxed_1150_; lean_object* v_res_1151_; 
v_skipRealize_boxed_1150_ = lean_unbox(v_skipRealize_1146_);
v_res_1151_ = l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1(v_constName_1145_, v_skipRealize_boxed_1150_, v___y_1147_, v___y_1148_);
lean_dec(v___y_1148_);
lean_dec_ref(v___y_1147_);
return v_res_1151_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___lam__0(lean_object* v___y_1152_, uint8_t v_isExporting_1153_, lean_object* v___x_1154_, lean_object* v_a_x3f_1155_){
_start:
{
lean_object* v___x_1157_; lean_object* v_env_1158_; lean_object* v_nextMacroScope_1159_; lean_object* v_ngen_1160_; lean_object* v_auxDeclNGen_1161_; lean_object* v_traceState_1162_; lean_object* v_messages_1163_; lean_object* v_infoState_1164_; lean_object* v_snapshotTasks_1165_; lean_object* v___x_1167_; uint8_t v_isShared_1168_; uint8_t v_isSharedCheck_1176_; 
v___x_1157_ = lean_st_ref_take(v___y_1152_);
v_env_1158_ = lean_ctor_get(v___x_1157_, 0);
v_nextMacroScope_1159_ = lean_ctor_get(v___x_1157_, 1);
v_ngen_1160_ = lean_ctor_get(v___x_1157_, 2);
v_auxDeclNGen_1161_ = lean_ctor_get(v___x_1157_, 3);
v_traceState_1162_ = lean_ctor_get(v___x_1157_, 4);
v_messages_1163_ = lean_ctor_get(v___x_1157_, 6);
v_infoState_1164_ = lean_ctor_get(v___x_1157_, 7);
v_snapshotTasks_1165_ = lean_ctor_get(v___x_1157_, 8);
v_isSharedCheck_1176_ = !lean_is_exclusive(v___x_1157_);
if (v_isSharedCheck_1176_ == 0)
{
lean_object* v_unused_1177_; 
v_unused_1177_ = lean_ctor_get(v___x_1157_, 5);
lean_dec(v_unused_1177_);
v___x_1167_ = v___x_1157_;
v_isShared_1168_ = v_isSharedCheck_1176_;
goto v_resetjp_1166_;
}
else
{
lean_inc(v_snapshotTasks_1165_);
lean_inc(v_infoState_1164_);
lean_inc(v_messages_1163_);
lean_inc(v_traceState_1162_);
lean_inc(v_auxDeclNGen_1161_);
lean_inc(v_ngen_1160_);
lean_inc(v_nextMacroScope_1159_);
lean_inc(v_env_1158_);
lean_dec(v___x_1157_);
v___x_1167_ = lean_box(0);
v_isShared_1168_ = v_isSharedCheck_1176_;
goto v_resetjp_1166_;
}
v_resetjp_1166_:
{
lean_object* v___x_1169_; lean_object* v___x_1171_; 
v___x_1169_ = l_Lean_Environment_setExporting(v_env_1158_, v_isExporting_1153_);
if (v_isShared_1168_ == 0)
{
lean_ctor_set(v___x_1167_, 5, v___x_1154_);
lean_ctor_set(v___x_1167_, 0, v___x_1169_);
v___x_1171_ = v___x_1167_;
goto v_reusejp_1170_;
}
else
{
lean_object* v_reuseFailAlloc_1175_; 
v_reuseFailAlloc_1175_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1175_, 0, v___x_1169_);
lean_ctor_set(v_reuseFailAlloc_1175_, 1, v_nextMacroScope_1159_);
lean_ctor_set(v_reuseFailAlloc_1175_, 2, v_ngen_1160_);
lean_ctor_set(v_reuseFailAlloc_1175_, 3, v_auxDeclNGen_1161_);
lean_ctor_set(v_reuseFailAlloc_1175_, 4, v_traceState_1162_);
lean_ctor_set(v_reuseFailAlloc_1175_, 5, v___x_1154_);
lean_ctor_set(v_reuseFailAlloc_1175_, 6, v_messages_1163_);
lean_ctor_set(v_reuseFailAlloc_1175_, 7, v_infoState_1164_);
lean_ctor_set(v_reuseFailAlloc_1175_, 8, v_snapshotTasks_1165_);
v___x_1171_ = v_reuseFailAlloc_1175_;
goto v_reusejp_1170_;
}
v_reusejp_1170_:
{
lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; 
v___x_1172_ = lean_st_ref_set(v___y_1152_, v___x_1171_);
v___x_1173_ = lean_box(0);
v___x_1174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1174_, 0, v___x_1173_);
return v___x_1174_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___lam__0___boxed(lean_object* v___y_1178_, lean_object* v_isExporting_1179_, lean_object* v___x_1180_, lean_object* v_a_x3f_1181_, lean_object* v___y_1182_){
_start:
{
uint8_t v_isExporting_boxed_1183_; lean_object* v_res_1184_; 
v_isExporting_boxed_1183_ = lean_unbox(v_isExporting_1179_);
v_res_1184_ = l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___lam__0(v___y_1178_, v_isExporting_boxed_1183_, v___x_1180_, v_a_x3f_1181_);
lean_dec(v_a_x3f_1181_);
lean_dec(v___y_1178_);
return v_res_1184_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_1185_; 
v___x_1185_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1185_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_1186_; lean_object* v___x_1187_; 
v___x_1186_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__0, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__0);
v___x_1187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1187_, 0, v___x_1186_);
return v___x_1187_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_1188_; lean_object* v___x_1189_; 
v___x_1188_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1);
v___x_1189_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1189_, 0, v___x_1188_);
lean_ctor_set(v___x_1189_, 1, v___x_1188_);
return v___x_1189_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg(lean_object* v_x_1190_, uint8_t v_isExporting_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_){
_start:
{
lean_object* v___x_1195_; lean_object* v_env_1196_; uint8_t v_isExporting_1197_; lean_object* v___x_1198_; lean_object* v_env_1199_; lean_object* v_nextMacroScope_1200_; lean_object* v_ngen_1201_; lean_object* v_auxDeclNGen_1202_; lean_object* v_traceState_1203_; lean_object* v_messages_1204_; lean_object* v_infoState_1205_; lean_object* v_snapshotTasks_1206_; lean_object* v___x_1208_; uint8_t v_isShared_1209_; uint8_t v_isSharedCheck_1245_; 
v___x_1195_ = lean_st_ref_get(v___y_1193_);
v_env_1196_ = lean_ctor_get(v___x_1195_, 0);
lean_inc_ref(v_env_1196_);
lean_dec(v___x_1195_);
v_isExporting_1197_ = lean_ctor_get_uint8(v_env_1196_, sizeof(void*)*8);
lean_dec_ref(v_env_1196_);
v___x_1198_ = lean_st_ref_take(v___y_1193_);
v_env_1199_ = lean_ctor_get(v___x_1198_, 0);
v_nextMacroScope_1200_ = lean_ctor_get(v___x_1198_, 1);
v_ngen_1201_ = lean_ctor_get(v___x_1198_, 2);
v_auxDeclNGen_1202_ = lean_ctor_get(v___x_1198_, 3);
v_traceState_1203_ = lean_ctor_get(v___x_1198_, 4);
v_messages_1204_ = lean_ctor_get(v___x_1198_, 6);
v_infoState_1205_ = lean_ctor_get(v___x_1198_, 7);
v_snapshotTasks_1206_ = lean_ctor_get(v___x_1198_, 8);
v_isSharedCheck_1245_ = !lean_is_exclusive(v___x_1198_);
if (v_isSharedCheck_1245_ == 0)
{
lean_object* v_unused_1246_; 
v_unused_1246_ = lean_ctor_get(v___x_1198_, 5);
lean_dec(v_unused_1246_);
v___x_1208_ = v___x_1198_;
v_isShared_1209_ = v_isSharedCheck_1245_;
goto v_resetjp_1207_;
}
else
{
lean_inc(v_snapshotTasks_1206_);
lean_inc(v_infoState_1205_);
lean_inc(v_messages_1204_);
lean_inc(v_traceState_1203_);
lean_inc(v_auxDeclNGen_1202_);
lean_inc(v_ngen_1201_);
lean_inc(v_nextMacroScope_1200_);
lean_inc(v_env_1199_);
lean_dec(v___x_1198_);
v___x_1208_ = lean_box(0);
v_isShared_1209_ = v_isSharedCheck_1245_;
goto v_resetjp_1207_;
}
v_resetjp_1207_:
{
lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1213_; 
v___x_1210_ = l_Lean_Environment_setExporting(v_env_1199_, v_isExporting_1191_);
v___x_1211_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2);
if (v_isShared_1209_ == 0)
{
lean_ctor_set(v___x_1208_, 5, v___x_1211_);
lean_ctor_set(v___x_1208_, 0, v___x_1210_);
v___x_1213_ = v___x_1208_;
goto v_reusejp_1212_;
}
else
{
lean_object* v_reuseFailAlloc_1244_; 
v_reuseFailAlloc_1244_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1244_, 0, v___x_1210_);
lean_ctor_set(v_reuseFailAlloc_1244_, 1, v_nextMacroScope_1200_);
lean_ctor_set(v_reuseFailAlloc_1244_, 2, v_ngen_1201_);
lean_ctor_set(v_reuseFailAlloc_1244_, 3, v_auxDeclNGen_1202_);
lean_ctor_set(v_reuseFailAlloc_1244_, 4, v_traceState_1203_);
lean_ctor_set(v_reuseFailAlloc_1244_, 5, v___x_1211_);
lean_ctor_set(v_reuseFailAlloc_1244_, 6, v_messages_1204_);
lean_ctor_set(v_reuseFailAlloc_1244_, 7, v_infoState_1205_);
lean_ctor_set(v_reuseFailAlloc_1244_, 8, v_snapshotTasks_1206_);
v___x_1213_ = v_reuseFailAlloc_1244_;
goto v_reusejp_1212_;
}
v_reusejp_1212_:
{
lean_object* v___x_1214_; lean_object* v_r_1215_; 
v___x_1214_ = lean_st_ref_set(v___y_1193_, v___x_1213_);
lean_inc(v___y_1193_);
lean_inc_ref(v___y_1192_);
v_r_1215_ = lean_apply_3(v_x_1190_, v___y_1192_, v___y_1193_, lean_box(0));
if (lean_obj_tag(v_r_1215_) == 0)
{
lean_object* v_a_1216_; lean_object* v___x_1218_; uint8_t v_isShared_1219_; uint8_t v_isSharedCheck_1232_; 
v_a_1216_ = lean_ctor_get(v_r_1215_, 0);
v_isSharedCheck_1232_ = !lean_is_exclusive(v_r_1215_);
if (v_isSharedCheck_1232_ == 0)
{
v___x_1218_ = v_r_1215_;
v_isShared_1219_ = v_isSharedCheck_1232_;
goto v_resetjp_1217_;
}
else
{
lean_inc(v_a_1216_);
lean_dec(v_r_1215_);
v___x_1218_ = lean_box(0);
v_isShared_1219_ = v_isSharedCheck_1232_;
goto v_resetjp_1217_;
}
v_resetjp_1217_:
{
lean_object* v___x_1221_; 
lean_inc(v_a_1216_);
if (v_isShared_1219_ == 0)
{
lean_ctor_set_tag(v___x_1218_, 1);
v___x_1221_ = v___x_1218_;
goto v_reusejp_1220_;
}
else
{
lean_object* v_reuseFailAlloc_1231_; 
v_reuseFailAlloc_1231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1231_, 0, v_a_1216_);
v___x_1221_ = v_reuseFailAlloc_1231_;
goto v_reusejp_1220_;
}
v_reusejp_1220_:
{
lean_object* v___x_1222_; lean_object* v___x_1224_; uint8_t v_isShared_1225_; uint8_t v_isSharedCheck_1229_; 
v___x_1222_ = l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___lam__0(v___y_1193_, v_isExporting_1197_, v___x_1211_, v___x_1221_);
lean_dec_ref(v___x_1221_);
v_isSharedCheck_1229_ = !lean_is_exclusive(v___x_1222_);
if (v_isSharedCheck_1229_ == 0)
{
lean_object* v_unused_1230_; 
v_unused_1230_ = lean_ctor_get(v___x_1222_, 0);
lean_dec(v_unused_1230_);
v___x_1224_ = v___x_1222_;
v_isShared_1225_ = v_isSharedCheck_1229_;
goto v_resetjp_1223_;
}
else
{
lean_dec(v___x_1222_);
v___x_1224_ = lean_box(0);
v_isShared_1225_ = v_isSharedCheck_1229_;
goto v_resetjp_1223_;
}
v_resetjp_1223_:
{
lean_object* v___x_1227_; 
if (v_isShared_1225_ == 0)
{
lean_ctor_set(v___x_1224_, 0, v_a_1216_);
v___x_1227_ = v___x_1224_;
goto v_reusejp_1226_;
}
else
{
lean_object* v_reuseFailAlloc_1228_; 
v_reuseFailAlloc_1228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1228_, 0, v_a_1216_);
v___x_1227_ = v_reuseFailAlloc_1228_;
goto v_reusejp_1226_;
}
v_reusejp_1226_:
{
return v___x_1227_;
}
}
}
}
}
else
{
lean_object* v_a_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1237_; uint8_t v_isShared_1238_; uint8_t v_isSharedCheck_1242_; 
v_a_1233_ = lean_ctor_get(v_r_1215_, 0);
lean_inc(v_a_1233_);
lean_dec_ref(v_r_1215_);
v___x_1234_ = lean_box(0);
v___x_1235_ = l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___lam__0(v___y_1193_, v_isExporting_1197_, v___x_1211_, v___x_1234_);
v_isSharedCheck_1242_ = !lean_is_exclusive(v___x_1235_);
if (v_isSharedCheck_1242_ == 0)
{
lean_object* v_unused_1243_; 
v_unused_1243_ = lean_ctor_get(v___x_1235_, 0);
lean_dec(v_unused_1243_);
v___x_1237_ = v___x_1235_;
v_isShared_1238_ = v_isSharedCheck_1242_;
goto v_resetjp_1236_;
}
else
{
lean_dec(v___x_1235_);
v___x_1237_ = lean_box(0);
v_isShared_1238_ = v_isSharedCheck_1242_;
goto v_resetjp_1236_;
}
v_resetjp_1236_:
{
lean_object* v___x_1240_; 
if (v_isShared_1238_ == 0)
{
lean_ctor_set_tag(v___x_1237_, 1);
lean_ctor_set(v___x_1237_, 0, v_a_1233_);
v___x_1240_ = v___x_1237_;
goto v_reusejp_1239_;
}
else
{
lean_object* v_reuseFailAlloc_1241_; 
v_reuseFailAlloc_1241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1241_, 0, v_a_1233_);
v___x_1240_ = v_reuseFailAlloc_1241_;
goto v_reusejp_1239_;
}
v_reusejp_1239_:
{
return v___x_1240_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___boxed(lean_object* v_x_1247_, lean_object* v_isExporting_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_){
_start:
{
uint8_t v_isExporting_boxed_1252_; lean_object* v_res_1253_; 
v_isExporting_boxed_1252_ = lean_unbox(v_isExporting_1248_);
v_res_1253_ = l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg(v_x_1247_, v_isExporting_boxed_1252_, v___y_1249_, v___y_1250_);
lean_dec(v___y_1250_);
lean_dec_ref(v___y_1249_);
return v_res_1253_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2(lean_object* v_00_u03b1_1254_, lean_object* v_x_1255_, uint8_t v_isExporting_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_){
_start:
{
lean_object* v___x_1260_; 
v___x_1260_ = l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg(v_x_1255_, v_isExporting_1256_, v___y_1257_, v___y_1258_);
return v___x_1260_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___boxed(lean_object* v_00_u03b1_1261_, lean_object* v_x_1262_, lean_object* v_isExporting_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_){
_start:
{
uint8_t v_isExporting_boxed_1267_; lean_object* v_res_1268_; 
v_isExporting_boxed_1267_ = lean_unbox(v_isExporting_1263_);
v_res_1268_ = l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2(v_00_u03b1_1261_, v_x_1262_, v_isExporting_boxed_1267_, v___y_1264_, v___y_1265_);
lean_dec(v___y_1265_);
lean_dec_ref(v___y_1264_);
return v_res_1268_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0_spec__3(lean_object* v_opts_1269_, lean_object* v_opt_1270_){
_start:
{
lean_object* v_name_1271_; lean_object* v_defValue_1272_; lean_object* v_map_1273_; lean_object* v___x_1274_; 
v_name_1271_ = lean_ctor_get(v_opt_1270_, 0);
v_defValue_1272_ = lean_ctor_get(v_opt_1270_, 1);
v_map_1273_ = lean_ctor_get(v_opts_1269_, 0);
v___x_1274_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1273_, v_name_1271_);
if (lean_obj_tag(v___x_1274_) == 0)
{
uint8_t v___x_1275_; 
v___x_1275_ = lean_unbox(v_defValue_1272_);
return v___x_1275_;
}
else
{
lean_object* v_val_1276_; 
v_val_1276_ = lean_ctor_get(v___x_1274_, 0);
lean_inc(v_val_1276_);
lean_dec_ref(v___x_1274_);
if (lean_obj_tag(v_val_1276_) == 1)
{
uint8_t v_v_1277_; 
v_v_1277_ = lean_ctor_get_uint8(v_val_1276_, 0);
lean_dec_ref(v_val_1276_);
return v_v_1277_;
}
else
{
uint8_t v___x_1278_; 
lean_dec(v_val_1276_);
v___x_1278_ = lean_unbox(v_defValue_1272_);
return v___x_1278_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0_spec__3___boxed(lean_object* v_opts_1279_, lean_object* v_opt_1280_){
_start:
{
uint8_t v_res_1281_; lean_object* v_r_1282_; 
v_res_1281_ = l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0_spec__3(v_opts_1279_, v_opt_1280_);
lean_dec_ref(v_opt_1280_);
lean_dec_ref(v_opts_1279_);
v_r_1282_ = lean_box(v_res_1281_);
return v_r_1282_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0(uint8_t v___y_1290_, uint8_t v_suppressElabErrors_1291_, lean_object* v_x_1292_){
_start:
{
if (lean_obj_tag(v_x_1292_) == 1)
{
lean_object* v_pre_1293_; 
v_pre_1293_ = lean_ctor_get(v_x_1292_, 0);
switch(lean_obj_tag(v_pre_1293_))
{
case 1:
{
lean_object* v_pre_1294_; 
v_pre_1294_ = lean_ctor_get(v_pre_1293_, 0);
switch(lean_obj_tag(v_pre_1294_))
{
case 0:
{
lean_object* v_str_1295_; lean_object* v_str_1296_; lean_object* v___x_1297_; uint8_t v___x_1298_; 
v_str_1295_ = lean_ctor_get(v_x_1292_, 1);
v_str_1296_ = lean_ctor_get(v_pre_1293_, 1);
v___x_1297_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__0));
v___x_1298_ = lean_string_dec_eq(v_str_1296_, v___x_1297_);
if (v___x_1298_ == 0)
{
lean_object* v___x_1299_; uint8_t v___x_1300_; 
v___x_1299_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__2));
v___x_1300_ = lean_string_dec_eq(v_str_1296_, v___x_1299_);
if (v___x_1300_ == 0)
{
return v___y_1290_;
}
else
{
lean_object* v___x_1301_; uint8_t v___x_1302_; 
v___x_1301_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__1));
v___x_1302_ = lean_string_dec_eq(v_str_1295_, v___x_1301_);
if (v___x_1302_ == 0)
{
return v___y_1290_;
}
else
{
return v_suppressElabErrors_1291_;
}
}
}
else
{
lean_object* v___x_1303_; uint8_t v___x_1304_; 
v___x_1303_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__2));
v___x_1304_ = lean_string_dec_eq(v_str_1295_, v___x_1303_);
if (v___x_1304_ == 0)
{
return v___y_1290_;
}
else
{
return v_suppressElabErrors_1291_;
}
}
}
case 1:
{
lean_object* v_pre_1305_; 
v_pre_1305_ = lean_ctor_get(v_pre_1294_, 0);
if (lean_obj_tag(v_pre_1305_) == 0)
{
lean_object* v_str_1306_; lean_object* v_str_1307_; lean_object* v_str_1308_; lean_object* v___x_1309_; uint8_t v___x_1310_; 
v_str_1306_ = lean_ctor_get(v_x_1292_, 1);
v_str_1307_ = lean_ctor_get(v_pre_1293_, 1);
v_str_1308_ = lean_ctor_get(v_pre_1294_, 1);
v___x_1309_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__3));
v___x_1310_ = lean_string_dec_eq(v_str_1308_, v___x_1309_);
if (v___x_1310_ == 0)
{
return v___y_1290_;
}
else
{
lean_object* v___x_1311_; uint8_t v___x_1312_; 
v___x_1311_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__4));
v___x_1312_ = lean_string_dec_eq(v_str_1307_, v___x_1311_);
if (v___x_1312_ == 0)
{
return v___y_1290_;
}
else
{
lean_object* v___x_1313_; uint8_t v___x_1314_; 
v___x_1313_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__5));
v___x_1314_ = lean_string_dec_eq(v_str_1306_, v___x_1313_);
if (v___x_1314_ == 0)
{
return v___y_1290_;
}
else
{
return v_suppressElabErrors_1291_;
}
}
}
}
else
{
return v___y_1290_;
}
}
default: 
{
return v___y_1290_;
}
}
}
case 0:
{
lean_object* v_str_1315_; lean_object* v___x_1316_; uint8_t v___x_1317_; 
v_str_1315_ = lean_ctor_get(v_x_1292_, 1);
v___x_1316_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__6));
v___x_1317_ = lean_string_dec_eq(v_str_1315_, v___x_1316_);
if (v___x_1317_ == 0)
{
return v___y_1290_;
}
else
{
return v_suppressElabErrors_1291_;
}
}
default: 
{
return v___y_1290_;
}
}
}
else
{
return v___y_1290_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___boxed(lean_object* v___y_1318_, lean_object* v_suppressElabErrors_1319_, lean_object* v_x_1320_){
_start:
{
uint8_t v___y_4965__boxed_1321_; uint8_t v_suppressElabErrors_boxed_1322_; uint8_t v_res_1323_; lean_object* v_r_1324_; 
v___y_4965__boxed_1321_ = lean_unbox(v___y_1318_);
v_suppressElabErrors_boxed_1322_ = lean_unbox(v_suppressElabErrors_1319_);
v_res_1323_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0(v___y_4965__boxed_1321_, v_suppressElabErrors_boxed_1322_, v_x_1320_);
lean_dec(v_x_1320_);
v_r_1324_ = lean_box(v_res_1323_);
return v_r_1324_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6(lean_object* v_ref_1325_, lean_object* v_msgData_1326_, uint8_t v_severity_1327_, uint8_t v_isSilent_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_){
_start:
{
uint8_t v___y_1333_; lean_object* v___y_1334_; lean_object* v___y_1335_; lean_object* v___y_1336_; uint8_t v___y_1337_; lean_object* v___y_1338_; lean_object* v___y_1339_; lean_object* v___y_1340_; lean_object* v___y_1341_; lean_object* v___y_1369_; lean_object* v___y_1370_; lean_object* v___y_1371_; lean_object* v___y_1372_; uint8_t v___y_1373_; uint8_t v___y_1374_; uint8_t v___y_1375_; lean_object* v___y_1376_; lean_object* v___y_1394_; lean_object* v___y_1395_; uint8_t v___y_1396_; lean_object* v___y_1397_; uint8_t v___y_1398_; lean_object* v___y_1399_; uint8_t v___y_1400_; lean_object* v___y_1401_; lean_object* v___y_1405_; lean_object* v___y_1406_; lean_object* v___y_1407_; lean_object* v___y_1408_; uint8_t v___y_1409_; uint8_t v___y_1410_; uint8_t v___y_1411_; uint8_t v___x_1416_; lean_object* v___y_1418_; lean_object* v___y_1419_; lean_object* v___y_1420_; lean_object* v___y_1421_; uint8_t v___y_1422_; uint8_t v___y_1423_; uint8_t v___y_1424_; uint8_t v___y_1426_; uint8_t v___x_1441_; 
v___x_1416_ = 2;
v___x_1441_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1327_, v___x_1416_);
if (v___x_1441_ == 0)
{
v___y_1426_ = v___x_1441_;
goto v___jp_1425_;
}
else
{
uint8_t v___x_1442_; 
lean_inc_ref(v_msgData_1326_);
v___x_1442_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_1326_);
v___y_1426_ = v___x_1442_;
goto v___jp_1425_;
}
v___jp_1332_:
{
lean_object* v___x_1342_; lean_object* v_currNamespace_1343_; lean_object* v_openDecls_1344_; lean_object* v_env_1345_; lean_object* v_nextMacroScope_1346_; lean_object* v_ngen_1347_; lean_object* v_auxDeclNGen_1348_; lean_object* v_traceState_1349_; lean_object* v_cache_1350_; lean_object* v_messages_1351_; lean_object* v_infoState_1352_; lean_object* v_snapshotTasks_1353_; lean_object* v___x_1355_; uint8_t v_isShared_1356_; uint8_t v_isSharedCheck_1367_; 
v___x_1342_ = lean_st_ref_take(v___y_1341_);
v_currNamespace_1343_ = lean_ctor_get(v___y_1340_, 6);
v_openDecls_1344_ = lean_ctor_get(v___y_1340_, 7);
v_env_1345_ = lean_ctor_get(v___x_1342_, 0);
v_nextMacroScope_1346_ = lean_ctor_get(v___x_1342_, 1);
v_ngen_1347_ = lean_ctor_get(v___x_1342_, 2);
v_auxDeclNGen_1348_ = lean_ctor_get(v___x_1342_, 3);
v_traceState_1349_ = lean_ctor_get(v___x_1342_, 4);
v_cache_1350_ = lean_ctor_get(v___x_1342_, 5);
v_messages_1351_ = lean_ctor_get(v___x_1342_, 6);
v_infoState_1352_ = lean_ctor_get(v___x_1342_, 7);
v_snapshotTasks_1353_ = lean_ctor_get(v___x_1342_, 8);
v_isSharedCheck_1367_ = !lean_is_exclusive(v___x_1342_);
if (v_isSharedCheck_1367_ == 0)
{
v___x_1355_ = v___x_1342_;
v_isShared_1356_ = v_isSharedCheck_1367_;
goto v_resetjp_1354_;
}
else
{
lean_inc(v_snapshotTasks_1353_);
lean_inc(v_infoState_1352_);
lean_inc(v_messages_1351_);
lean_inc(v_cache_1350_);
lean_inc(v_traceState_1349_);
lean_inc(v_auxDeclNGen_1348_);
lean_inc(v_ngen_1347_);
lean_inc(v_nextMacroScope_1346_);
lean_inc(v_env_1345_);
lean_dec(v___x_1342_);
v___x_1355_ = lean_box(0);
v_isShared_1356_ = v_isSharedCheck_1367_;
goto v_resetjp_1354_;
}
v_resetjp_1354_:
{
lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1362_; 
lean_inc(v_openDecls_1344_);
lean_inc(v_currNamespace_1343_);
v___x_1357_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1357_, 0, v_currNamespace_1343_);
lean_ctor_set(v___x_1357_, 1, v_openDecls_1344_);
v___x_1358_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1358_, 0, v___x_1357_);
lean_ctor_set(v___x_1358_, 1, v___y_1336_);
lean_inc_ref(v___y_1338_);
lean_inc_ref(v___y_1335_);
v___x_1359_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1359_, 0, v___y_1335_);
lean_ctor_set(v___x_1359_, 1, v___y_1339_);
lean_ctor_set(v___x_1359_, 2, v___y_1334_);
lean_ctor_set(v___x_1359_, 3, v___y_1338_);
lean_ctor_set(v___x_1359_, 4, v___x_1358_);
lean_ctor_set_uint8(v___x_1359_, sizeof(void*)*5, v___y_1333_);
lean_ctor_set_uint8(v___x_1359_, sizeof(void*)*5 + 1, v___y_1337_);
lean_ctor_set_uint8(v___x_1359_, sizeof(void*)*5 + 2, v_isSilent_1328_);
v___x_1360_ = l_Lean_MessageLog_add(v___x_1359_, v_messages_1351_);
if (v_isShared_1356_ == 0)
{
lean_ctor_set(v___x_1355_, 6, v___x_1360_);
v___x_1362_ = v___x_1355_;
goto v_reusejp_1361_;
}
else
{
lean_object* v_reuseFailAlloc_1366_; 
v_reuseFailAlloc_1366_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1366_, 0, v_env_1345_);
lean_ctor_set(v_reuseFailAlloc_1366_, 1, v_nextMacroScope_1346_);
lean_ctor_set(v_reuseFailAlloc_1366_, 2, v_ngen_1347_);
lean_ctor_set(v_reuseFailAlloc_1366_, 3, v_auxDeclNGen_1348_);
lean_ctor_set(v_reuseFailAlloc_1366_, 4, v_traceState_1349_);
lean_ctor_set(v_reuseFailAlloc_1366_, 5, v_cache_1350_);
lean_ctor_set(v_reuseFailAlloc_1366_, 6, v___x_1360_);
lean_ctor_set(v_reuseFailAlloc_1366_, 7, v_infoState_1352_);
lean_ctor_set(v_reuseFailAlloc_1366_, 8, v_snapshotTasks_1353_);
v___x_1362_ = v_reuseFailAlloc_1366_;
goto v_reusejp_1361_;
}
v_reusejp_1361_:
{
lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; 
v___x_1363_ = lean_st_ref_set(v___y_1341_, v___x_1362_);
v___x_1364_ = lean_box(0);
v___x_1365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1365_, 0, v___x_1364_);
return v___x_1365_;
}
}
}
v___jp_1368_:
{
lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v_a_1379_; lean_object* v___x_1381_; uint8_t v_isShared_1382_; uint8_t v_isSharedCheck_1392_; 
v___x_1377_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_1326_);
v___x_1378_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0_spec__0_spec__1(v___x_1377_, v___y_1329_, v___y_1330_);
v_a_1379_ = lean_ctor_get(v___x_1378_, 0);
v_isSharedCheck_1392_ = !lean_is_exclusive(v___x_1378_);
if (v_isSharedCheck_1392_ == 0)
{
v___x_1381_ = v___x_1378_;
v_isShared_1382_ = v_isSharedCheck_1392_;
goto v_resetjp_1380_;
}
else
{
lean_inc(v_a_1379_);
lean_dec(v___x_1378_);
v___x_1381_ = lean_box(0);
v_isShared_1382_ = v_isSharedCheck_1392_;
goto v_resetjp_1380_;
}
v_resetjp_1380_:
{
lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; 
lean_inc_ref_n(v___y_1371_, 2);
v___x_1383_ = l_Lean_FileMap_toPosition(v___y_1371_, v___y_1370_);
lean_dec(v___y_1370_);
v___x_1384_ = l_Lean_FileMap_toPosition(v___y_1371_, v___y_1376_);
lean_dec(v___y_1376_);
v___x_1385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1385_, 0, v___x_1384_);
v___x_1386_ = ((lean_object*)(l_Lean_instInhabitedAttributeImplCore_default___closed__0));
if (v___y_1375_ == 0)
{
lean_del_object(v___x_1381_);
lean_dec_ref(v___y_1369_);
v___y_1333_ = v___y_1373_;
v___y_1334_ = v___x_1385_;
v___y_1335_ = v___y_1372_;
v___y_1336_ = v_a_1379_;
v___y_1337_ = v___y_1374_;
v___y_1338_ = v___x_1386_;
v___y_1339_ = v___x_1383_;
v___y_1340_ = v___y_1329_;
v___y_1341_ = v___y_1330_;
goto v___jp_1332_;
}
else
{
uint8_t v___x_1387_; 
lean_inc(v_a_1379_);
v___x_1387_ = l_Lean_MessageData_hasTag(v___y_1369_, v_a_1379_);
if (v___x_1387_ == 0)
{
lean_object* v___x_1388_; lean_object* v___x_1390_; 
lean_dec_ref(v___x_1385_);
lean_dec_ref(v___x_1383_);
lean_dec(v_a_1379_);
v___x_1388_ = lean_box(0);
if (v_isShared_1382_ == 0)
{
lean_ctor_set(v___x_1381_, 0, v___x_1388_);
v___x_1390_ = v___x_1381_;
goto v_reusejp_1389_;
}
else
{
lean_object* v_reuseFailAlloc_1391_; 
v_reuseFailAlloc_1391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1391_, 0, v___x_1388_);
v___x_1390_ = v_reuseFailAlloc_1391_;
goto v_reusejp_1389_;
}
v_reusejp_1389_:
{
return v___x_1390_;
}
}
else
{
lean_del_object(v___x_1381_);
v___y_1333_ = v___y_1373_;
v___y_1334_ = v___x_1385_;
v___y_1335_ = v___y_1372_;
v___y_1336_ = v_a_1379_;
v___y_1337_ = v___y_1374_;
v___y_1338_ = v___x_1386_;
v___y_1339_ = v___x_1383_;
v___y_1340_ = v___y_1329_;
v___y_1341_ = v___y_1330_;
goto v___jp_1332_;
}
}
}
}
v___jp_1393_:
{
lean_object* v___x_1402_; 
v___x_1402_ = l_Lean_Syntax_getTailPos_x3f(v___y_1399_, v___y_1396_);
lean_dec(v___y_1399_);
if (lean_obj_tag(v___x_1402_) == 0)
{
lean_inc(v___y_1401_);
v___y_1369_ = v___y_1394_;
v___y_1370_ = v___y_1401_;
v___y_1371_ = v___y_1395_;
v___y_1372_ = v___y_1397_;
v___y_1373_ = v___y_1396_;
v___y_1374_ = v___y_1398_;
v___y_1375_ = v___y_1400_;
v___y_1376_ = v___y_1401_;
goto v___jp_1368_;
}
else
{
lean_object* v_val_1403_; 
v_val_1403_ = lean_ctor_get(v___x_1402_, 0);
lean_inc(v_val_1403_);
lean_dec_ref(v___x_1402_);
v___y_1369_ = v___y_1394_;
v___y_1370_ = v___y_1401_;
v___y_1371_ = v___y_1395_;
v___y_1372_ = v___y_1397_;
v___y_1373_ = v___y_1396_;
v___y_1374_ = v___y_1398_;
v___y_1375_ = v___y_1400_;
v___y_1376_ = v_val_1403_;
goto v___jp_1368_;
}
}
v___jp_1404_:
{
lean_object* v_ref_1412_; lean_object* v___x_1413_; 
v_ref_1412_ = l_Lean_replaceRef(v_ref_1325_, v___y_1406_);
v___x_1413_ = l_Lean_Syntax_getPos_x3f(v_ref_1412_, v___y_1409_);
if (lean_obj_tag(v___x_1413_) == 0)
{
lean_object* v___x_1414_; 
v___x_1414_ = lean_unsigned_to_nat(0u);
v___y_1394_ = v___y_1405_;
v___y_1395_ = v___y_1407_;
v___y_1396_ = v___y_1409_;
v___y_1397_ = v___y_1408_;
v___y_1398_ = v___y_1411_;
v___y_1399_ = v_ref_1412_;
v___y_1400_ = v___y_1410_;
v___y_1401_ = v___x_1414_;
goto v___jp_1393_;
}
else
{
lean_object* v_val_1415_; 
v_val_1415_ = lean_ctor_get(v___x_1413_, 0);
lean_inc(v_val_1415_);
lean_dec_ref(v___x_1413_);
v___y_1394_ = v___y_1405_;
v___y_1395_ = v___y_1407_;
v___y_1396_ = v___y_1409_;
v___y_1397_ = v___y_1408_;
v___y_1398_ = v___y_1411_;
v___y_1399_ = v_ref_1412_;
v___y_1400_ = v___y_1410_;
v___y_1401_ = v_val_1415_;
goto v___jp_1393_;
}
}
v___jp_1417_:
{
if (v___y_1424_ == 0)
{
v___y_1405_ = v___y_1419_;
v___y_1406_ = v___y_1418_;
v___y_1407_ = v___y_1420_;
v___y_1408_ = v___y_1421_;
v___y_1409_ = v___y_1423_;
v___y_1410_ = v___y_1422_;
v___y_1411_ = v_severity_1327_;
goto v___jp_1404_;
}
else
{
v___y_1405_ = v___y_1419_;
v___y_1406_ = v___y_1418_;
v___y_1407_ = v___y_1420_;
v___y_1408_ = v___y_1421_;
v___y_1409_ = v___y_1423_;
v___y_1410_ = v___y_1422_;
v___y_1411_ = v___x_1416_;
goto v___jp_1404_;
}
}
v___jp_1425_:
{
if (v___y_1426_ == 0)
{
lean_object* v_fileName_1427_; lean_object* v_fileMap_1428_; lean_object* v_options_1429_; lean_object* v_ref_1430_; uint8_t v_suppressElabErrors_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___f_1434_; uint8_t v___x_1435_; uint8_t v___x_1436_; 
v_fileName_1427_ = lean_ctor_get(v___y_1329_, 0);
v_fileMap_1428_ = lean_ctor_get(v___y_1329_, 1);
v_options_1429_ = lean_ctor_get(v___y_1329_, 2);
v_ref_1430_ = lean_ctor_get(v___y_1329_, 5);
v_suppressElabErrors_1431_ = lean_ctor_get_uint8(v___y_1329_, sizeof(void*)*14 + 1);
v___x_1432_ = lean_box(v___y_1426_);
v___x_1433_ = lean_box(v_suppressElabErrors_1431_);
v___f_1434_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1434_, 0, v___x_1432_);
lean_closure_set(v___f_1434_, 1, v___x_1433_);
v___x_1435_ = 1;
v___x_1436_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1327_, v___x_1435_);
if (v___x_1436_ == 0)
{
v___y_1418_ = v_ref_1430_;
v___y_1419_ = v___f_1434_;
v___y_1420_ = v_fileMap_1428_;
v___y_1421_ = v_fileName_1427_;
v___y_1422_ = v_suppressElabErrors_1431_;
v___y_1423_ = v___y_1426_;
v___y_1424_ = v___x_1436_;
goto v___jp_1417_;
}
else
{
lean_object* v___x_1437_; uint8_t v___x_1438_; 
v___x_1437_ = l_Lean_warningAsError;
v___x_1438_ = l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0_spec__3(v_options_1429_, v___x_1437_);
v___y_1418_ = v_ref_1430_;
v___y_1419_ = v___f_1434_;
v___y_1420_ = v_fileMap_1428_;
v___y_1421_ = v_fileName_1427_;
v___y_1422_ = v_suppressElabErrors_1431_;
v___y_1423_ = v___y_1426_;
v___y_1424_ = v___x_1438_;
goto v___jp_1417_;
}
}
else
{
lean_object* v___x_1439_; lean_object* v___x_1440_; 
lean_dec_ref(v_msgData_1326_);
v___x_1439_ = lean_box(0);
v___x_1440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1440_, 0, v___x_1439_);
return v___x_1440_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___boxed(lean_object* v_ref_1443_, lean_object* v_msgData_1444_, lean_object* v_severity_1445_, lean_object* v_isSilent_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_){
_start:
{
uint8_t v_severity_boxed_1450_; uint8_t v_isSilent_boxed_1451_; lean_object* v_res_1452_; 
v_severity_boxed_1450_ = lean_unbox(v_severity_1445_);
v_isSilent_boxed_1451_ = lean_unbox(v_isSilent_1446_);
v_res_1452_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6(v_ref_1443_, v_msgData_1444_, v_severity_boxed_1450_, v_isSilent_boxed_1451_, v___y_1447_, v___y_1448_);
lean_dec(v___y_1448_);
lean_dec_ref(v___y_1447_);
lean_dec(v_ref_1443_);
return v_res_1452_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5(lean_object* v_msgData_1453_, uint8_t v_severity_1454_, uint8_t v_isSilent_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_){
_start:
{
lean_object* v_ref_1459_; lean_object* v___x_1460_; 
v_ref_1459_ = lean_ctor_get(v___y_1456_, 5);
v___x_1460_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6(v_ref_1459_, v_msgData_1453_, v_severity_1454_, v_isSilent_1455_, v___y_1456_, v___y_1457_);
return v___x_1460_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5___boxed(lean_object* v_msgData_1461_, lean_object* v_severity_1462_, lean_object* v_isSilent_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_){
_start:
{
uint8_t v_severity_boxed_1467_; uint8_t v_isSilent_boxed_1468_; lean_object* v_res_1469_; 
v_severity_boxed_1467_ = lean_unbox(v_severity_1462_);
v_isSilent_boxed_1468_ = lean_unbox(v_isSilent_1463_);
v_res_1469_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5(v_msgData_1461_, v_severity_boxed_1467_, v_isSilent_boxed_1468_, v___y_1464_, v___y_1465_);
lean_dec(v___y_1465_);
lean_dec_ref(v___y_1464_);
return v_res_1469_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1(lean_object* v_msgData_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_){
_start:
{
uint8_t v___x_1474_; uint8_t v___x_1475_; lean_object* v___x_1476_; 
v___x_1474_ = 1;
v___x_1475_ = 0;
v___x_1476_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5(v_msgData_1470_, v___x_1474_, v___x_1475_, v___y_1471_, v___y_1472_);
return v___x_1476_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1___boxed(lean_object* v_msgData_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_){
_start:
{
lean_object* v_res_1481_; 
v_res_1481_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1(v_msgData_1477_, v___y_1478_, v___y_1479_);
lean_dec(v___y_1479_);
lean_dec_ref(v___y_1478_);
return v_res_1481_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0___redArg(lean_object* v_opt_1482_, lean_object* v___y_1483_){
_start:
{
lean_object* v_options_1485_; uint8_t v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; 
v_options_1485_ = lean_ctor_get(v___y_1483_, 2);
v___x_1486_ = l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0_spec__3(v_options_1485_, v_opt_1482_);
v___x_1487_ = lean_box(v___x_1486_);
v___x_1488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1488_, 0, v___x_1487_);
return v___x_1488_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0___redArg___boxed(lean_object* v_opt_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_){
_start:
{
lean_object* v_res_1492_; 
v_res_1492_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0___redArg(v_opt_1489_, v___y_1490_);
lean_dec_ref(v___y_1490_);
lean_dec_ref(v_opt_1489_);
return v_res_1492_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1494_; lean_object* v___x_1495_; 
v___x_1494_ = ((lean_object*)(l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__0));
v___x_1495_ = l_Lean_stringToMessageData(v___x_1494_);
return v___x_1495_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__3(void){
_start:
{
lean_object* v___x_1497_; lean_object* v___x_1498_; 
v___x_1497_ = ((lean_object*)(l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__2));
v___x_1498_ = l_Lean_stringToMessageData(v___x_1497_);
return v___x_1498_;
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0(lean_object* v_id_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_){
_start:
{
lean_object* v___x_1503_; lean_object* v_env_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v_a_1507_; lean_object* v___x_1509_; uint8_t v_isShared_1510_; uint8_t v_isSharedCheck_1526_; 
v___x_1503_ = lean_st_ref_get(v___y_1501_);
v_env_1504_ = lean_ctor_get(v___x_1503_, 0);
lean_inc_ref(v_env_1504_);
lean_dec(v___x_1503_);
v___x_1505_ = l_Lean_ResolveName_backward_privateInPublic_warn;
v___x_1506_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0___redArg(v___x_1505_, v___y_1500_);
v_a_1507_ = lean_ctor_get(v___x_1506_, 0);
v_isSharedCheck_1526_ = !lean_is_exclusive(v___x_1506_);
if (v_isSharedCheck_1526_ == 0)
{
v___x_1509_ = v___x_1506_;
v_isShared_1510_ = v_isSharedCheck_1526_;
goto v_resetjp_1508_;
}
else
{
lean_inc(v_a_1507_);
lean_dec(v___x_1506_);
v___x_1509_ = lean_box(0);
v_isShared_1510_ = v_isSharedCheck_1526_;
goto v_resetjp_1508_;
}
v_resetjp_1508_:
{
uint8_t v_isExporting_1516_; 
v_isExporting_1516_ = lean_ctor_get_uint8(v_env_1504_, sizeof(void*)*8);
lean_dec_ref(v_env_1504_);
if (v_isExporting_1516_ == 0)
{
lean_dec(v_a_1507_);
lean_dec(v_id_1499_);
goto v___jp_1511_;
}
else
{
uint8_t v___x_1517_; 
v___x_1517_ = l_Lean_isPrivateName(v_id_1499_);
if (v___x_1517_ == 0)
{
lean_dec(v_a_1507_);
lean_dec(v_id_1499_);
goto v___jp_1511_;
}
else
{
uint8_t v___x_1518_; 
v___x_1518_ = lean_unbox(v_a_1507_);
lean_dec(v_a_1507_);
if (v___x_1518_ == 0)
{
lean_dec(v_id_1499_);
goto v___jp_1511_;
}
else
{
lean_object* v___x_1519_; uint8_t v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; 
lean_del_object(v___x_1509_);
v___x_1519_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__1, &l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__1_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__1);
v___x_1520_ = 0;
v___x_1521_ = l_Lean_MessageData_ofConstName(v_id_1499_, v___x_1520_);
v___x_1522_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1522_, 0, v___x_1519_);
lean_ctor_set(v___x_1522_, 1, v___x_1521_);
v___x_1523_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__3, &l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__3_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__3);
v___x_1524_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1524_, 0, v___x_1522_);
lean_ctor_set(v___x_1524_, 1, v___x_1523_);
v___x_1525_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1(v___x_1524_, v___y_1500_, v___y_1501_);
return v___x_1525_;
}
}
}
v___jp_1511_:
{
lean_object* v___x_1512_; lean_object* v___x_1514_; 
v___x_1512_ = lean_box(0);
if (v_isShared_1510_ == 0)
{
lean_ctor_set(v___x_1509_, 0, v___x_1512_);
v___x_1514_ = v___x_1509_;
goto v_reusejp_1513_;
}
else
{
lean_object* v_reuseFailAlloc_1515_; 
v_reuseFailAlloc_1515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1515_, 0, v___x_1512_);
v___x_1514_ = v_reuseFailAlloc_1515_;
goto v_reusejp_1513_;
}
v_reusejp_1513_:
{
return v___x_1514_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___boxed(lean_object* v_id_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_){
_start:
{
lean_object* v_res_1531_; 
v_res_1531_ = l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0(v_id_1527_, v___y_1528_, v___y_1529_);
lean_dec(v___y_1529_);
lean_dec_ref(v___y_1528_);
return v_res_1531_;
}
}
static lean_object* _init_l_Lean_ensureAttrDeclIsPublic___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1533_; lean_object* v___x_1534_; 
v___x_1533_ = ((lean_object*)(l_Lean_ensureAttrDeclIsPublic___lam__0___closed__0));
v___x_1534_ = l_Lean_stringToMessageData(v___x_1533_);
return v___x_1534_;
}
}
LEAN_EXPORT lean_object* l_Lean_ensureAttrDeclIsPublic___lam__0(lean_object* v_declName_1535_, uint8_t v_isModule_1536_, lean_object* v_attrName_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_){
_start:
{
lean_object* v___x_1541_; 
lean_inc(v_declName_1535_);
v___x_1541_ = l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0(v_declName_1535_, v___y_1538_, v___y_1539_);
if (lean_obj_tag(v___x_1541_) == 0)
{
lean_object* v___x_1542_; lean_object* v_a_1543_; lean_object* v___x_1545_; uint8_t v_isShared_1546_; uint8_t v_isSharedCheck_1563_; 
lean_dec_ref(v___x_1541_);
lean_inc(v_declName_1535_);
v___x_1542_ = l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1___redArg(v_declName_1535_, v_isModule_1536_, v___y_1539_);
v_a_1543_ = lean_ctor_get(v___x_1542_, 0);
v_isSharedCheck_1563_ = !lean_is_exclusive(v___x_1542_);
if (v_isSharedCheck_1563_ == 0)
{
v___x_1545_ = v___x_1542_;
v_isShared_1546_ = v_isSharedCheck_1563_;
goto v_resetjp_1544_;
}
else
{
lean_inc(v_a_1543_);
lean_dec(v___x_1542_);
v___x_1545_ = lean_box(0);
v_isShared_1546_ = v_isSharedCheck_1563_;
goto v_resetjp_1544_;
}
v_resetjp_1544_:
{
uint8_t v___x_1547_; 
v___x_1547_ = lean_unbox(v_a_1543_);
if (v___x_1547_ == 0)
{
lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; uint8_t v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; 
lean_del_object(v___x_1545_);
v___x_1548_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1);
v___x_1549_ = l_Lean_MessageData_ofName(v_attrName_1537_);
v___x_1550_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1550_, 0, v___x_1548_);
lean_ctor_set(v___x_1550_, 1, v___x_1549_);
v___x_1551_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1, &l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1);
v___x_1552_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1552_, 0, v___x_1550_);
lean_ctor_set(v___x_1552_, 1, v___x_1551_);
v___x_1553_ = lean_unbox(v_a_1543_);
lean_dec(v_a_1543_);
v___x_1554_ = l_Lean_MessageData_ofConstName(v_declName_1535_, v___x_1553_);
v___x_1555_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1555_, 0, v___x_1552_);
lean_ctor_set(v___x_1555_, 1, v___x_1554_);
v___x_1556_ = lean_obj_once(&l_Lean_ensureAttrDeclIsPublic___lam__0___closed__1, &l_Lean_ensureAttrDeclIsPublic___lam__0___closed__1_once, _init_l_Lean_ensureAttrDeclIsPublic___lam__0___closed__1);
v___x_1557_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1557_, 0, v___x_1555_);
lean_ctor_set(v___x_1557_, 1, v___x_1556_);
v___x_1558_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0_spec__0___redArg(v___x_1557_, v___y_1538_, v___y_1539_);
return v___x_1558_;
}
else
{
lean_object* v___x_1559_; lean_object* v___x_1561_; 
lean_dec(v_a_1543_);
lean_dec(v_attrName_1537_);
lean_dec(v_declName_1535_);
v___x_1559_ = lean_box(0);
if (v_isShared_1546_ == 0)
{
lean_ctor_set(v___x_1545_, 0, v___x_1559_);
v___x_1561_ = v___x_1545_;
goto v_reusejp_1560_;
}
else
{
lean_object* v_reuseFailAlloc_1562_; 
v_reuseFailAlloc_1562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1562_, 0, v___x_1559_);
v___x_1561_ = v_reuseFailAlloc_1562_;
goto v_reusejp_1560_;
}
v_reusejp_1560_:
{
return v___x_1561_;
}
}
}
}
else
{
lean_dec(v_attrName_1537_);
lean_dec(v_declName_1535_);
return v___x_1541_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ensureAttrDeclIsPublic___lam__0___boxed(lean_object* v_declName_1564_, lean_object* v_isModule_1565_, lean_object* v_attrName_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_){
_start:
{
uint8_t v_isModule_boxed_1570_; lean_object* v_res_1571_; 
v_isModule_boxed_1570_ = lean_unbox(v_isModule_1565_);
v_res_1571_ = l_Lean_ensureAttrDeclIsPublic___lam__0(v_declName_1564_, v_isModule_boxed_1570_, v_attrName_1566_, v___y_1567_, v___y_1568_);
lean_dec(v___y_1568_);
lean_dec_ref(v___y_1567_);
return v_res_1571_;
}
}
LEAN_EXPORT lean_object* l_Lean_ensureAttrDeclIsPublic(lean_object* v_attrName_1572_, lean_object* v_declName_1573_, uint8_t v_attrKind_1574_, lean_object* v_a_1575_, lean_object* v_a_1576_){
_start:
{
lean_object* v___x_1578_; lean_object* v_env_1582_; lean_object* v___x_1583_; uint8_t v_isModule_1584_; 
v___x_1578_ = lean_st_ref_get(v_a_1576_);
v_env_1582_ = lean_ctor_get(v___x_1578_, 0);
lean_inc_ref(v_env_1582_);
lean_dec(v___x_1578_);
v___x_1583_ = l_Lean_Environment_header(v_env_1582_);
lean_dec_ref(v_env_1582_);
v_isModule_1584_ = lean_ctor_get_uint8(v___x_1583_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_1583_);
if (v_isModule_1584_ == 0)
{
lean_dec(v_declName_1573_);
lean_dec(v_attrName_1572_);
goto v___jp_1579_;
}
else
{
uint8_t v___x_1585_; uint8_t v___x_1586_; 
v___x_1585_ = 1;
v___x_1586_ = l_Lean_instBEqAttributeKind_beq(v_attrKind_1574_, v___x_1585_);
if (v___x_1586_ == 0)
{
lean_object* v___x_1587_; lean_object* v___f_1588_; lean_object* v___x_1589_; 
v___x_1587_ = lean_box(v_isModule_1584_);
v___f_1588_ = lean_alloc_closure((void*)(l_Lean_ensureAttrDeclIsPublic___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1588_, 0, v_declName_1573_);
lean_closure_set(v___f_1588_, 1, v___x_1587_);
lean_closure_set(v___f_1588_, 2, v_attrName_1572_);
v___x_1589_ = l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg(v___f_1588_, v_isModule_1584_, v_a_1575_, v_a_1576_);
return v___x_1589_;
}
else
{
lean_dec(v_declName_1573_);
lean_dec(v_attrName_1572_);
goto v___jp_1579_;
}
}
v___jp_1579_:
{
lean_object* v___x_1580_; lean_object* v___x_1581_; 
v___x_1580_ = lean_box(0);
v___x_1581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1581_, 0, v___x_1580_);
return v___x_1581_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ensureAttrDeclIsPublic___boxed(lean_object* v_attrName_1590_, lean_object* v_declName_1591_, lean_object* v_attrKind_1592_, lean_object* v_a_1593_, lean_object* v_a_1594_, lean_object* v_a_1595_){
_start:
{
uint8_t v_attrKind_boxed_1596_; lean_object* v_res_1597_; 
v_attrKind_boxed_1596_ = lean_unbox(v_attrKind_1592_);
v_res_1597_ = l_Lean_ensureAttrDeclIsPublic(v_attrName_1590_, v_declName_1591_, v_attrKind_boxed_1596_, v_a_1593_, v_a_1594_);
lean_dec(v_a_1594_);
lean_dec_ref(v_a_1593_);
return v_res_1597_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0(lean_object* v_opt_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_){
_start:
{
lean_object* v___x_1602_; 
v___x_1602_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0___redArg(v_opt_1598_, v___y_1599_);
return v___x_1602_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0___boxed(lean_object* v_opt_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_){
_start:
{
lean_object* v_res_1607_; 
v_res_1607_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0(v_opt_1603_, v___y_1604_, v___y_1605_);
lean_dec(v___y_1605_);
lean_dec_ref(v___y_1604_);
lean_dec_ref(v_opt_1603_);
return v_res_1607_;
}
}
static lean_object* _init_l_Lean_ensureAttrDeclIsMeta___closed__1(void){
_start:
{
lean_object* v___x_1609_; lean_object* v___x_1610_; 
v___x_1609_ = ((lean_object*)(l_Lean_ensureAttrDeclIsMeta___closed__0));
v___x_1610_ = l_Lean_stringToMessageData(v___x_1609_);
return v___x_1610_;
}
}
LEAN_EXPORT lean_object* l_Lean_ensureAttrDeclIsMeta(lean_object* v_attrName_1611_, lean_object* v_declName_1612_, uint8_t v_attrKind_1613_, lean_object* v_a_1614_, lean_object* v_a_1615_){
_start:
{
lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v_env_1619_; lean_object* v___x_1620_; uint8_t v_isModule_1621_; 
v___x_1617_ = lean_st_ref_get(v_a_1615_);
v___x_1618_ = lean_st_ref_get(v_a_1615_);
v_env_1619_ = lean_ctor_get(v___x_1617_, 0);
lean_inc_ref(v_env_1619_);
lean_dec(v___x_1617_);
v___x_1620_ = l_Lean_Environment_header(v_env_1619_);
lean_dec_ref(v_env_1619_);
v_isModule_1621_ = lean_ctor_get_uint8(v___x_1620_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_1620_);
if (v_isModule_1621_ == 0)
{
lean_object* v___x_1622_; 
lean_dec(v___x_1618_);
v___x_1622_ = l_Lean_ensureAttrDeclIsPublic(v_attrName_1611_, v_declName_1612_, v_attrKind_1613_, v_a_1614_, v_a_1615_);
return v___x_1622_;
}
else
{
lean_object* v_env_1623_; uint8_t v___x_1624_; 
v_env_1623_ = lean_ctor_get(v___x_1618_, 0);
lean_inc_ref(v_env_1623_);
lean_dec(v___x_1618_);
lean_inc(v_declName_1612_);
v___x_1624_ = l_Lean_isMarkedMeta(v_env_1623_, v_declName_1612_);
if (v___x_1624_ == 0)
{
lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; 
v___x_1625_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1);
v___x_1626_ = l_Lean_MessageData_ofName(v_attrName_1611_);
v___x_1627_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1627_, 0, v___x_1625_);
lean_ctor_set(v___x_1627_, 1, v___x_1626_);
v___x_1628_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1, &l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1);
v___x_1629_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1629_, 0, v___x_1627_);
lean_ctor_set(v___x_1629_, 1, v___x_1628_);
v___x_1630_ = l_Lean_MessageData_ofConstName(v_declName_1612_, v___x_1624_);
v___x_1631_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1631_, 0, v___x_1629_);
lean_ctor_set(v___x_1631_, 1, v___x_1630_);
v___x_1632_ = lean_obj_once(&l_Lean_ensureAttrDeclIsMeta___closed__1, &l_Lean_ensureAttrDeclIsMeta___closed__1_once, _init_l_Lean_ensureAttrDeclIsMeta___closed__1);
v___x_1633_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1633_, 0, v___x_1631_);
lean_ctor_set(v___x_1633_, 1, v___x_1632_);
v___x_1634_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0_spec__0___redArg(v___x_1633_, v_a_1614_, v_a_1615_);
return v___x_1634_;
}
else
{
lean_object* v___x_1635_; 
v___x_1635_ = l_Lean_ensureAttrDeclIsPublic(v_attrName_1611_, v_declName_1612_, v_attrKind_1613_, v_a_1614_, v_a_1615_);
return v___x_1635_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ensureAttrDeclIsMeta___boxed(lean_object* v_attrName_1636_, lean_object* v_declName_1637_, lean_object* v_attrKind_1638_, lean_object* v_a_1639_, lean_object* v_a_1640_, lean_object* v_a_1641_){
_start:
{
uint8_t v_attrKind_boxed_1642_; lean_object* v_res_1643_; 
v_attrKind_boxed_1642_ = lean_unbox(v_attrKind_1638_);
v_res_1643_ = l_Lean_ensureAttrDeclIsMeta(v_attrName_1636_, v_declName_1637_, v_attrKind_boxed_1642_, v_a_1639_, v_a_1640_);
lean_dec(v_a_1640_);
lean_dec_ref(v_a_1639_);
return v_res_1643_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__0(lean_object* v_x_1647_, lean_object* v___y_1648_){
_start:
{
lean_object* v___x_1650_; lean_object* v___x_1651_; 
v___x_1650_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___lam__0___closed__1));
v___x_1651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1651_, 0, v___x_1650_);
return v___x_1651_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__0___boxed(lean_object* v_x_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_){
_start:
{
lean_object* v_res_1655_; 
v_res_1655_ = l_Lean_instInhabitedTagAttribute_default___lam__0(v_x_1652_, v___y_1653_);
lean_dec_ref(v___y_1653_);
lean_dec_ref(v_x_1652_);
return v_res_1655_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__1(lean_object* v_s_1656_, lean_object* v_x_1657_){
_start:
{
lean_inc(v_s_1656_);
return v_s_1656_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__1___boxed(lean_object* v_s_1658_, lean_object* v_x_1659_){
_start:
{
lean_object* v_res_1660_; 
v_res_1660_ = l_Lean_instInhabitedTagAttribute_default___lam__1(v_s_1658_, v_x_1659_);
lean_dec(v_x_1659_);
lean_dec(v_s_1658_);
return v_res_1660_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__2(lean_object* v_x_1665_, lean_object* v_x_1666_){
_start:
{
lean_object* v___x_1667_; 
v___x_1667_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___lam__2___closed__1));
return v___x_1667_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__2___boxed(lean_object* v_x_1668_, lean_object* v_x_1669_){
_start:
{
lean_object* v_res_1670_; 
v_res_1670_ = l_Lean_instInhabitedTagAttribute_default___lam__2(v_x_1668_, v_x_1669_);
lean_dec(v_x_1669_);
lean_dec_ref(v_x_1668_);
return v_res_1670_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__3(lean_object* v_x_1671_){
_start:
{
lean_object* v___x_1672_; 
v___x_1672_ = lean_box(0);
return v___x_1672_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__3___boxed(lean_object* v_x_1673_){
_start:
{
lean_object* v_res_1674_; 
v_res_1674_ = l_Lean_instInhabitedTagAttribute_default___lam__3(v_x_1673_);
lean_dec(v_x_1673_);
return v_res_1674_;
}
}
static lean_object* _init_l_Lean_instInhabitedTagAttribute_default___closed__4(void){
_start:
{
lean_object* v___x_1679_; 
v___x_1679_ = l_Lean_instInhabitedEnvExtension_default(lean_box(0));
return v___x_1679_;
}
}
static lean_object* _init_l_Lean_instInhabitedTagAttribute_default___closed__5(void){
_start:
{
lean_object* v___f_1680_; lean_object* v___f_1681_; lean_object* v___f_1682_; lean_object* v___f_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; 
v___f_1680_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___closed__3));
v___f_1681_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___closed__2));
v___f_1682_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___closed__1));
v___f_1683_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___closed__0));
v___x_1684_ = lean_box(0);
v___x_1685_ = lean_obj_once(&l_Lean_instInhabitedTagAttribute_default___closed__4, &l_Lean_instInhabitedTagAttribute_default___closed__4_once, _init_l_Lean_instInhabitedTagAttribute_default___closed__4);
v___x_1686_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1686_, 0, v___x_1685_);
lean_ctor_set(v___x_1686_, 1, v___x_1684_);
lean_ctor_set(v___x_1686_, 2, v___f_1683_);
lean_ctor_set(v___x_1686_, 3, v___f_1682_);
lean_ctor_set(v___x_1686_, 4, v___f_1681_);
lean_ctor_set(v___x_1686_, 5, v___f_1680_);
return v___x_1686_;
}
}
static lean_object* _init_l_Lean_instInhabitedTagAttribute_default___closed__6(void){
_start:
{
lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; 
v___x_1687_ = lean_obj_once(&l_Lean_instInhabitedTagAttribute_default___closed__5, &l_Lean_instInhabitedTagAttribute_default___closed__5_once, _init_l_Lean_instInhabitedTagAttribute_default___closed__5);
v___x_1688_ = ((lean_object*)(l_Lean_instInhabitedAttributeImpl_default));
v___x_1689_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1689_, 0, v___x_1688_);
lean_ctor_set(v___x_1689_, 1, v___x_1687_);
return v___x_1689_;
}
}
static lean_object* _init_l_Lean_instInhabitedTagAttribute_default(void){
_start:
{
lean_object* v___x_1690_; 
v___x_1690_ = lean_obj_once(&l_Lean_instInhabitedTagAttribute_default___closed__6, &l_Lean_instInhabitedTagAttribute_default___closed__6_once, _init_l_Lean_instInhabitedTagAttribute_default___closed__6);
return v___x_1690_;
}
}
static lean_object* _init_l_Lean_instInhabitedTagAttribute(void){
_start:
{
lean_object* v___x_1691_; 
v___x_1691_ = l_Lean_instInhabitedTagAttribute_default;
return v___x_1691_;
}
}
static lean_object* _init_l_Lean_registerTagAttribute___auto__1(void){
_start:
{
lean_object* v___x_1692_; 
v___x_1692_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__28, &l_Lean_AttributeImplCore_ref___autoParam___closed__28_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__28);
return v___x_1692_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__0(lean_object* v_x_1693_){
_start:
{
lean_object* v___x_1694_; 
v___x_1694_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___lam__2___closed__0));
return v___x_1694_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__0___boxed(lean_object* v_x_1695_){
_start:
{
lean_object* v_res_1696_; 
v_res_1696_ = l_Lean_registerTagAttribute___lam__0(v_x_1695_);
lean_dec(v_x_1695_);
return v_res_1696_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerTagAttribute_spec__0(lean_object* v_newState_1697_, lean_object* v_x_1698_, lean_object* v_x_1699_){
_start:
{
if (lean_obj_tag(v_x_1699_) == 0)
{
return v_x_1698_;
}
else
{
lean_object* v_head_1700_; lean_object* v_tail_1701_; uint8_t v___x_1702_; 
v_head_1700_ = lean_ctor_get(v_x_1699_, 0);
lean_inc(v_head_1700_);
v_tail_1701_ = lean_ctor_get(v_x_1699_, 1);
lean_inc(v_tail_1701_);
lean_dec_ref(v_x_1699_);
v___x_1702_ = l_Lean_NameSet_contains(v_newState_1697_, v_head_1700_);
if (v___x_1702_ == 0)
{
lean_dec(v_head_1700_);
v_x_1699_ = v_tail_1701_;
goto _start;
}
else
{
lean_object* v___x_1704_; 
v___x_1704_ = l_Lean_NameSet_insert(v_x_1698_, v_head_1700_);
v_x_1698_ = v___x_1704_;
v_x_1699_ = v_tail_1701_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerTagAttribute_spec__0___boxed(lean_object* v_newState_1706_, lean_object* v_x_1707_, lean_object* v_x_1708_){
_start:
{
lean_object* v_res_1709_; 
v_res_1709_ = l_List_foldl___at___00Lean_registerTagAttribute_spec__0(v_newState_1706_, v_x_1707_, v_x_1708_);
lean_dec(v_newState_1706_);
return v_res_1709_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__1(lean_object* v_x_1710_, lean_object* v_newState_1711_, lean_object* v_newConsts_1712_, lean_object* v_s_1713_){
_start:
{
lean_object* v___x_1714_; 
v___x_1714_ = l_List_foldl___at___00Lean_registerTagAttribute_spec__0(v_newState_1711_, v_s_1713_, v_newConsts_1712_);
return v___x_1714_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__1___boxed(lean_object* v_x_1715_, lean_object* v_newState_1716_, lean_object* v_newConsts_1717_, lean_object* v_s_1718_){
_start:
{
lean_object* v_res_1719_; 
v_res_1719_ = l_Lean_registerTagAttribute___lam__1(v_x_1715_, v_newState_1716_, v_newConsts_1717_, v_s_1718_);
lean_dec(v_newState_1716_);
lean_dec(v_x_1715_);
return v_res_1719_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__2(lean_object* v_s_1732_){
_start:
{
lean_object* v___x_1733_; lean_object* v___y_1735_; 
v___x_1733_ = ((lean_object*)(l_Lean_registerTagAttribute___lam__2___closed__5));
if (lean_obj_tag(v_s_1732_) == 0)
{
lean_object* v_size_1739_; 
v_size_1739_ = lean_ctor_get(v_s_1732_, 0);
lean_inc(v_size_1739_);
lean_dec_ref(v_s_1732_);
v___y_1735_ = v_size_1739_;
goto v___jp_1734_;
}
else
{
lean_object* v___x_1740_; 
v___x_1740_ = lean_unsigned_to_nat(0u);
v___y_1735_ = v___x_1740_;
goto v___jp_1734_;
}
v___jp_1734_:
{
lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; 
v___x_1736_ = l_Nat_reprFast(v___y_1735_);
v___x_1737_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1737_, 0, v___x_1736_);
v___x_1738_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1738_, 0, v___x_1733_);
lean_ctor_set(v___x_1738_, 1, v___x_1737_);
return v___x_1738_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___redArg(lean_object* v_as_1742_, lean_object* v_lo_1743_, lean_object* v_hi_1744_){
_start:
{
uint8_t v___x_1745_; 
v___x_1745_ = lean_nat_dec_lt(v_lo_1743_, v_hi_1744_);
if (v___x_1745_ == 0)
{
lean_dec(v_lo_1743_);
return v_as_1742_;
}
else
{
lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v_fst_1748_; lean_object* v_snd_1749_; uint8_t v___x_1750_; 
v___x_1746_ = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___redArg___closed__0));
lean_inc(v_lo_1743_);
v___x_1747_ = l_Array_qpartition___redArg(v_as_1742_, v___x_1746_, v_lo_1743_, v_hi_1744_);
v_fst_1748_ = lean_ctor_get(v___x_1747_, 0);
lean_inc(v_fst_1748_);
v_snd_1749_ = lean_ctor_get(v___x_1747_, 1);
lean_inc(v_snd_1749_);
lean_dec_ref(v___x_1747_);
v___x_1750_ = lean_nat_dec_le(v_hi_1744_, v_fst_1748_);
if (v___x_1750_ == 0)
{
lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; 
v___x_1751_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___redArg(v_snd_1749_, v_lo_1743_, v_fst_1748_);
v___x_1752_ = lean_unsigned_to_nat(1u);
v___x_1753_ = lean_nat_add(v_fst_1748_, v___x_1752_);
lean_dec(v_fst_1748_);
v_as_1742_ = v___x_1751_;
v_lo_1743_ = v___x_1753_;
goto _start;
}
else
{
lean_dec(v_fst_1748_);
lean_dec(v_lo_1743_);
return v_snd_1749_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___redArg___boxed(lean_object* v_as_1755_, lean_object* v_lo_1756_, lean_object* v_hi_1757_){
_start:
{
lean_object* v_res_1758_; 
v_res_1758_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___redArg(v_as_1755_, v_lo_1756_, v_hi_1757_);
lean_dec(v_hi_1757_);
return v_res_1758_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerTagAttribute_spec__2(lean_object* v_env_1759_, lean_object* v_as_1760_, size_t v_i_1761_, size_t v_stop_1762_, lean_object* v_b_1763_){
_start:
{
lean_object* v___y_1765_; uint8_t v___x_1769_; 
v___x_1769_ = lean_usize_dec_eq(v_i_1761_, v_stop_1762_);
if (v___x_1769_ == 0)
{
lean_object* v___x_1770_; uint8_t v___x_1771_; lean_object* v___x_1772_; uint8_t v___x_1773_; 
v___x_1770_ = lean_array_uget_borrowed(v_as_1760_, v_i_1761_);
v___x_1771_ = 1;
lean_inc_ref(v_env_1759_);
v___x_1772_ = l_Lean_Environment_setExporting(v_env_1759_, v___x_1771_);
lean_inc(v___x_1770_);
v___x_1773_ = l_Lean_Environment_contains(v___x_1772_, v___x_1770_, v___x_1769_);
if (v___x_1773_ == 0)
{
v___y_1765_ = v_b_1763_;
goto v___jp_1764_;
}
else
{
lean_object* v___x_1774_; 
lean_inc(v___x_1770_);
v___x_1774_ = lean_array_push(v_b_1763_, v___x_1770_);
v___y_1765_ = v___x_1774_;
goto v___jp_1764_;
}
}
else
{
lean_dec_ref(v_env_1759_);
return v_b_1763_;
}
v___jp_1764_:
{
size_t v___x_1766_; size_t v___x_1767_; 
v___x_1766_ = ((size_t)1ULL);
v___x_1767_ = lean_usize_add(v_i_1761_, v___x_1766_);
v_i_1761_ = v___x_1767_;
v_b_1763_ = v___y_1765_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerTagAttribute_spec__2___boxed(lean_object* v_env_1775_, lean_object* v_as_1776_, lean_object* v_i_1777_, lean_object* v_stop_1778_, lean_object* v_b_1779_){
_start:
{
size_t v_i_boxed_1780_; size_t v_stop_boxed_1781_; lean_object* v_res_1782_; 
v_i_boxed_1780_ = lean_unbox_usize(v_i_1777_);
lean_dec(v_i_1777_);
v_stop_boxed_1781_ = lean_unbox_usize(v_stop_1778_);
lean_dec(v_stop_1778_);
v_res_1782_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerTagAttribute_spec__2(v_env_1775_, v_as_1776_, v_i_boxed_1780_, v_stop_boxed_1781_, v_b_1779_);
lean_dec_ref(v_as_1776_);
return v_res_1782_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerTagAttribute_spec__1_spec__1(lean_object* v_init_1783_, lean_object* v_x_1784_){
_start:
{
if (lean_obj_tag(v_x_1784_) == 0)
{
lean_object* v_k_1785_; lean_object* v_l_1786_; lean_object* v_r_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; 
v_k_1785_ = lean_ctor_get(v_x_1784_, 1);
lean_inc(v_k_1785_);
v_l_1786_ = lean_ctor_get(v_x_1784_, 3);
lean_inc(v_l_1786_);
v_r_1787_ = lean_ctor_get(v_x_1784_, 4);
lean_inc(v_r_1787_);
lean_dec_ref(v_x_1784_);
v___x_1788_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerTagAttribute_spec__1_spec__1(v_init_1783_, v_l_1786_);
v___x_1789_ = lean_array_push(v___x_1788_, v_k_1785_);
v_init_1783_ = v___x_1789_;
v_x_1784_ = v_r_1787_;
goto _start;
}
else
{
return v_init_1783_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__3(lean_object* v_env_1791_, lean_object* v_es_1792_){
_start:
{
lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___y_1796_; lean_object* v___x_1810_; lean_object* v___y_1812_; lean_object* v___y_1813_; lean_object* v___x_1815_; uint8_t v___x_1816_; 
v___x_1793_ = lean_unsigned_to_nat(0u);
v___x_1794_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___lam__2___closed__0));
v___x_1810_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerTagAttribute_spec__1_spec__1(v___x_1794_, v_es_1792_);
v___x_1815_ = lean_array_get_size(v___x_1810_);
v___x_1816_ = lean_nat_dec_eq(v___x_1815_, v___x_1793_);
if (v___x_1816_ == 0)
{
lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___y_1820_; uint8_t v___x_1822_; 
v___x_1817_ = lean_unsigned_to_nat(1u);
v___x_1818_ = lean_nat_sub(v___x_1815_, v___x_1817_);
v___x_1822_ = lean_nat_dec_le(v___x_1793_, v___x_1818_);
if (v___x_1822_ == 0)
{
lean_inc(v___x_1818_);
v___y_1820_ = v___x_1818_;
goto v___jp_1819_;
}
else
{
v___y_1820_ = v___x_1793_;
goto v___jp_1819_;
}
v___jp_1819_:
{
uint8_t v___x_1821_; 
v___x_1821_ = lean_nat_dec_le(v___y_1820_, v___x_1818_);
if (v___x_1821_ == 0)
{
lean_dec(v___x_1818_);
lean_inc(v___y_1820_);
v___y_1812_ = v___y_1820_;
v___y_1813_ = v___y_1820_;
goto v___jp_1811_;
}
else
{
v___y_1812_ = v___y_1820_;
v___y_1813_ = v___x_1818_;
goto v___jp_1811_;
}
}
}
else
{
v___y_1796_ = v___x_1810_;
goto v___jp_1795_;
}
v___jp_1795_:
{
lean_object* v___x_1797_; uint8_t v___x_1798_; 
v___x_1797_ = lean_array_get_size(v___y_1796_);
v___x_1798_ = lean_nat_dec_lt(v___x_1793_, v___x_1797_);
if (v___x_1798_ == 0)
{
lean_object* v___x_1799_; 
lean_dec_ref(v_env_1791_);
v___x_1799_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1799_, 0, v___x_1794_);
lean_ctor_set(v___x_1799_, 1, v___x_1794_);
lean_ctor_set(v___x_1799_, 2, v___y_1796_);
return v___x_1799_;
}
else
{
uint8_t v___x_1800_; 
v___x_1800_ = lean_nat_dec_le(v___x_1797_, v___x_1797_);
if (v___x_1800_ == 0)
{
if (v___x_1798_ == 0)
{
lean_object* v___x_1801_; 
lean_dec_ref(v_env_1791_);
v___x_1801_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1801_, 0, v___x_1794_);
lean_ctor_set(v___x_1801_, 1, v___x_1794_);
lean_ctor_set(v___x_1801_, 2, v___y_1796_);
return v___x_1801_;
}
else
{
size_t v___x_1802_; size_t v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; 
v___x_1802_ = ((size_t)0ULL);
v___x_1803_ = lean_usize_of_nat(v___x_1797_);
v___x_1804_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerTagAttribute_spec__2(v_env_1791_, v___y_1796_, v___x_1802_, v___x_1803_, v___x_1794_);
lean_inc_ref(v___x_1804_);
v___x_1805_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1805_, 0, v___x_1804_);
lean_ctor_set(v___x_1805_, 1, v___x_1804_);
lean_ctor_set(v___x_1805_, 2, v___y_1796_);
return v___x_1805_;
}
}
else
{
size_t v___x_1806_; size_t v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; 
v___x_1806_ = ((size_t)0ULL);
v___x_1807_ = lean_usize_of_nat(v___x_1797_);
v___x_1808_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerTagAttribute_spec__2(v_env_1791_, v___y_1796_, v___x_1806_, v___x_1807_, v___x_1794_);
lean_inc_ref(v___x_1808_);
v___x_1809_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1809_, 0, v___x_1808_);
lean_ctor_set(v___x_1809_, 1, v___x_1808_);
lean_ctor_set(v___x_1809_, 2, v___y_1796_);
return v___x_1809_;
}
}
}
v___jp_1811_:
{
lean_object* v___x_1814_; 
v___x_1814_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___redArg(v___x_1810_, v___y_1812_, v___y_1813_);
lean_dec(v___y_1813_);
v___y_1796_ = v___x_1814_;
goto v___jp_1795_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__4(lean_object* v___x_1823_, lean_object* v_x_1824_, lean_object* v_x_1825_){
_start:
{
lean_object* v___x_1827_; 
v___x_1827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1827_, 0, v___x_1823_);
return v___x_1827_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__4___boxed(lean_object* v___x_1828_, lean_object* v_x_1829_, lean_object* v_x_1830_, lean_object* v___y_1831_){
_start:
{
lean_object* v_res_1832_; 
v_res_1832_ = l_Lean_registerTagAttribute___lam__4(v___x_1828_, v_x_1829_, v_x_1830_);
lean_dec_ref(v_x_1830_);
lean_dec_ref(v_x_1829_);
return v_res_1832_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__5(lean_object* v___x_1833_){
_start:
{
lean_object* v___x_1835_; 
v___x_1835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1835_, 0, v___x_1833_);
return v___x_1835_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__5___boxed(lean_object* v___x_1836_, lean_object* v___y_1837_){
_start:
{
lean_object* v_res_1838_; 
v_res_1838_ = l_Lean_registerTagAttribute___lam__5(v___x_1836_);
return v_res_1838_;
}
}
static lean_object* _init_l_Lean_registerTagAttribute___lam__6___closed__1(void){
_start:
{
lean_object* v___x_1840_; lean_object* v___x_1841_; 
v___x_1840_ = ((lean_object*)(l_Lean_registerTagAttribute___lam__6___closed__0));
v___x_1841_ = l_Lean_stringToMessageData(v___x_1840_);
return v___x_1841_;
}
}
static lean_object* _init_l_Lean_registerTagAttribute___lam__6___closed__3(void){
_start:
{
lean_object* v___x_1843_; lean_object* v___x_1844_; 
v___x_1843_ = ((lean_object*)(l_Lean_registerTagAttribute___lam__6___closed__2));
v___x_1844_ = l_Lean_stringToMessageData(v___x_1843_);
return v___x_1844_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__6(lean_object* v_name_1845_, lean_object* v_decl_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_){
_start:
{
lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; 
v___x_1850_ = lean_obj_once(&l_Lean_registerTagAttribute___lam__6___closed__1, &l_Lean_registerTagAttribute___lam__6___closed__1_once, _init_l_Lean_registerTagAttribute___lam__6___closed__1);
v___x_1851_ = l_Lean_MessageData_ofName(v_name_1845_);
v___x_1852_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1852_, 0, v___x_1850_);
lean_ctor_set(v___x_1852_, 1, v___x_1851_);
v___x_1853_ = lean_obj_once(&l_Lean_registerTagAttribute___lam__6___closed__3, &l_Lean_registerTagAttribute___lam__6___closed__3_once, _init_l_Lean_registerTagAttribute___lam__6___closed__3);
v___x_1854_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1854_, 0, v___x_1852_);
lean_ctor_set(v___x_1854_, 1, v___x_1853_);
v___x_1855_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0_spec__0___redArg(v___x_1854_, v___y_1847_, v___y_1848_);
return v___x_1855_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__6___boxed(lean_object* v_name_1856_, lean_object* v_decl_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_){
_start:
{
lean_object* v_res_1861_; 
v_res_1861_ = l_Lean_registerTagAttribute___lam__6(v_name_1856_, v_decl_1857_, v___y_1858_, v___y_1859_);
lean_dec(v___y_1859_);
lean_dec_ref(v___y_1858_);
lean_dec(v_decl_1857_);
return v_res_1861_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg(lean_object* v_attrName_1862_, lean_object* v_declName_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_){
_start:
{
lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; uint8_t v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; 
v___x_1867_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1);
v___x_1868_ = l_Lean_MessageData_ofName(v_attrName_1862_);
v___x_1869_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1869_, 0, v___x_1867_);
lean_ctor_set(v___x_1869_, 1, v___x_1868_);
v___x_1870_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__3, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__3_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__3);
v___x_1871_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1871_, 0, v___x_1869_);
lean_ctor_set(v___x_1871_, 1, v___x_1870_);
v___x_1872_ = 0;
v___x_1873_ = l_Lean_MessageData_ofConstName(v_declName_1863_, v___x_1872_);
v___x_1874_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1874_, 0, v___x_1871_);
lean_ctor_set(v___x_1874_, 1, v___x_1873_);
v___x_1875_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__5, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__5_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__5);
v___x_1876_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1876_, 0, v___x_1874_);
lean_ctor_set(v___x_1876_, 1, v___x_1875_);
v___x_1877_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0_spec__0___redArg(v___x_1876_, v___y_1864_, v___y_1865_);
return v___x_1877_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg___boxed(lean_object* v_attrName_1878_, lean_object* v_declName_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_){
_start:
{
lean_object* v_res_1883_; 
v_res_1883_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg(v_attrName_1878_, v_declName_1879_, v___y_1880_, v___y_1881_);
lean_dec(v___y_1881_);
lean_dec_ref(v___y_1880_);
return v_res_1883_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___redArg(lean_object* v_attrName_1884_, lean_object* v_declName_1885_, lean_object* v_asyncPrefix_x3f_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_){
_start:
{
lean_object* v___y_1891_; 
if (lean_obj_tag(v_asyncPrefix_x3f_1886_) == 0)
{
lean_object* v___x_1904_; 
v___x_1904_ = l_Lean_MessageData_nil;
v___y_1891_ = v___x_1904_;
goto v___jp_1890_;
}
else
{
lean_object* v_val_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; 
v_val_1905_ = lean_ctor_get(v_asyncPrefix_x3f_1886_, 0);
lean_inc(v_val_1905_);
lean_dec_ref(v_asyncPrefix_x3f_1886_);
v___x_1906_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___redArg___closed__3, &l_Lean_throwAttrNotInAsyncCtx___redArg___closed__3_once, _init_l_Lean_throwAttrNotInAsyncCtx___redArg___closed__3);
v___x_1907_ = l_Lean_MessageData_ofName(v_val_1905_);
v___x_1908_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1908_, 0, v___x_1906_);
lean_ctor_set(v___x_1908_, 1, v___x_1907_);
v___x_1909_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__5, &l_Lean_throwAttrMustBeGlobal___redArg___closed__5_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__5);
v___x_1910_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1910_, 0, v___x_1908_);
lean_ctor_set(v___x_1910_, 1, v___x_1909_);
v___y_1891_ = v___x_1910_;
goto v___jp_1890_;
}
v___jp_1890_:
{
lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; uint8_t v___x_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; 
v___x_1892_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1);
v___x_1893_ = l_Lean_MessageData_ofName(v_attrName_1884_);
v___x_1894_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1894_, 0, v___x_1892_);
lean_ctor_set(v___x_1894_, 1, v___x_1893_);
v___x_1895_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__3, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__3_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__3);
v___x_1896_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1896_, 0, v___x_1894_);
lean_ctor_set(v___x_1896_, 1, v___x_1895_);
v___x_1897_ = 0;
v___x_1898_ = l_Lean_MessageData_ofConstName(v_declName_1885_, v___x_1897_);
v___x_1899_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1899_, 0, v___x_1896_);
lean_ctor_set(v___x_1899_, 1, v___x_1898_);
v___x_1900_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___redArg___closed__1, &l_Lean_throwAttrNotInAsyncCtx___redArg___closed__1_once, _init_l_Lean_throwAttrNotInAsyncCtx___redArg___closed__1);
v___x_1901_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1901_, 0, v___x_1899_);
lean_ctor_set(v___x_1901_, 1, v___x_1900_);
v___x_1902_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1902_, 0, v___x_1901_);
lean_ctor_set(v___x_1902_, 1, v___y_1891_);
v___x_1903_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0_spec__0___redArg(v___x_1902_, v___y_1887_, v___y_1888_);
return v___x_1903_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___redArg___boxed(lean_object* v_attrName_1911_, lean_object* v_declName_1912_, lean_object* v_asyncPrefix_x3f_1913_, lean_object* v___y_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_){
_start:
{
lean_object* v_res_1917_; 
v_res_1917_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___redArg(v_attrName_1911_, v_declName_1912_, v_asyncPrefix_x3f_1913_, v___y_1914_, v___y_1915_);
lean_dec(v___y_1915_);
lean_dec_ref(v___y_1914_);
return v_res_1917_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg(lean_object* v_name_1918_, uint8_t v_kind_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_){
_start:
{
lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___y_1929_; 
v___x_1923_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__1, &l_Lean_throwAttrMustBeGlobal___redArg___closed__1_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__1);
v___x_1924_ = l_Lean_MessageData_ofName(v_name_1918_);
v___x_1925_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1925_, 0, v___x_1923_);
lean_ctor_set(v___x_1925_, 1, v___x_1924_);
v___x_1926_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__3, &l_Lean_throwAttrMustBeGlobal___redArg___closed__3_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__3);
v___x_1927_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1927_, 0, v___x_1925_);
lean_ctor_set(v___x_1927_, 1, v___x_1926_);
switch(v_kind_1919_)
{
case 0:
{
lean_object* v___x_1936_; 
v___x_1936_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__0));
v___y_1929_ = v___x_1936_;
goto v___jp_1928_;
}
case 1:
{
lean_object* v___x_1937_; 
v___x_1937_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__1));
v___y_1929_ = v___x_1937_;
goto v___jp_1928_;
}
default: 
{
lean_object* v___x_1938_; 
v___x_1938_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__2));
v___y_1929_ = v___x_1938_;
goto v___jp_1928_;
}
}
v___jp_1928_:
{
lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; 
lean_inc_ref(v___y_1929_);
v___x_1930_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1930_, 0, v___y_1929_);
v___x_1931_ = l_Lean_MessageData_ofFormat(v___x_1930_);
v___x_1932_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1932_, 0, v___x_1927_);
lean_ctor_set(v___x_1932_, 1, v___x_1931_);
v___x_1933_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__5, &l_Lean_throwAttrMustBeGlobal___redArg___closed__5_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__5);
v___x_1934_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1934_, 0, v___x_1932_);
lean_ctor_set(v___x_1934_, 1, v___x_1933_);
v___x_1935_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0_spec__0___redArg(v___x_1934_, v___y_1920_, v___y_1921_);
return v___x_1935_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg___boxed(lean_object* v_name_1939_, lean_object* v_kind_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_){
_start:
{
uint8_t v_kind_boxed_1944_; lean_object* v_res_1945_; 
v_kind_boxed_1944_ = lean_unbox(v_kind_1940_);
v_res_1945_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg(v_name_1939_, v_kind_boxed_1944_, v___y_1941_, v___y_1942_);
lean_dec(v___y_1942_);
lean_dec_ref(v___y_1941_);
return v_res_1945_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__7(lean_object* v_validate_1946_, lean_object* v_a_1947_, lean_object* v_name_1948_, lean_object* v_decl_1949_, lean_object* v_stx_1950_, uint8_t v_kind_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_){
_start:
{
lean_object* v___y_1956_; lean_object* v___y_1957_; lean_object* v___y_1991_; lean_object* v___y_1992_; lean_object* v___y_1993_; lean_object* v___y_2000_; lean_object* v___y_2001_; lean_object* v___x_2006_; 
v___x_2006_ = l_Lean_Attribute_Builtin_ensureNoArgs(v_stx_1950_, v___y_1952_, v___y_1953_);
if (lean_obj_tag(v___x_2006_) == 0)
{
uint8_t v___x_2007_; uint8_t v___x_2008_; 
lean_dec_ref(v___x_2006_);
v___x_2007_ = 0;
v___x_2008_ = l_Lean_instBEqAttributeKind_beq(v_kind_1951_, v___x_2007_);
if (v___x_2008_ == 0)
{
lean_object* v___x_2009_; 
lean_dec(v_decl_1949_);
lean_dec_ref(v_a_1947_);
lean_dec_ref(v_validate_1946_);
v___x_2009_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg(v_name_1948_, v_kind_1951_, v___y_1952_, v___y_1953_);
return v___x_2009_;
}
else
{
v___y_2000_ = v___y_1952_;
v___y_2001_ = v___y_1953_;
goto v___jp_1999_;
}
}
else
{
lean_dec(v_decl_1949_);
lean_dec(v_name_1948_);
lean_dec_ref(v_a_1947_);
lean_dec_ref(v_validate_1946_);
return v___x_2006_;
}
v___jp_1955_:
{
lean_object* v___x_1958_; 
lean_inc(v___y_1957_);
lean_inc_ref(v___y_1956_);
lean_inc(v_decl_1949_);
v___x_1958_ = lean_apply_4(v_validate_1946_, v_decl_1949_, v___y_1956_, v___y_1957_, lean_box(0));
if (lean_obj_tag(v___x_1958_) == 0)
{
lean_object* v___x_1960_; uint8_t v_isShared_1961_; uint8_t v_isSharedCheck_1988_; 
v_isSharedCheck_1988_ = !lean_is_exclusive(v___x_1958_);
if (v_isSharedCheck_1988_ == 0)
{
lean_object* v_unused_1989_; 
v_unused_1989_ = lean_ctor_get(v___x_1958_, 0);
lean_dec(v_unused_1989_);
v___x_1960_ = v___x_1958_;
v_isShared_1961_ = v_isSharedCheck_1988_;
goto v_resetjp_1959_;
}
else
{
lean_dec(v___x_1958_);
v___x_1960_ = lean_box(0);
v_isShared_1961_ = v_isSharedCheck_1988_;
goto v_resetjp_1959_;
}
v_resetjp_1959_:
{
lean_object* v___x_1962_; lean_object* v_toEnvExtension_1963_; lean_object* v_env_1964_; lean_object* v_nextMacroScope_1965_; lean_object* v_ngen_1966_; lean_object* v_auxDeclNGen_1967_; lean_object* v_traceState_1968_; lean_object* v_messages_1969_; lean_object* v_infoState_1970_; lean_object* v_snapshotTasks_1971_; lean_object* v___x_1973_; uint8_t v_isShared_1974_; uint8_t v_isSharedCheck_1986_; 
v___x_1962_ = lean_st_ref_take(v___y_1957_);
v_toEnvExtension_1963_ = lean_ctor_get(v_a_1947_, 0);
v_env_1964_ = lean_ctor_get(v___x_1962_, 0);
v_nextMacroScope_1965_ = lean_ctor_get(v___x_1962_, 1);
v_ngen_1966_ = lean_ctor_get(v___x_1962_, 2);
v_auxDeclNGen_1967_ = lean_ctor_get(v___x_1962_, 3);
v_traceState_1968_ = lean_ctor_get(v___x_1962_, 4);
v_messages_1969_ = lean_ctor_get(v___x_1962_, 6);
v_infoState_1970_ = lean_ctor_get(v___x_1962_, 7);
v_snapshotTasks_1971_ = lean_ctor_get(v___x_1962_, 8);
v_isSharedCheck_1986_ = !lean_is_exclusive(v___x_1962_);
if (v_isSharedCheck_1986_ == 0)
{
lean_object* v_unused_1987_; 
v_unused_1987_ = lean_ctor_get(v___x_1962_, 5);
lean_dec(v_unused_1987_);
v___x_1973_ = v___x_1962_;
v_isShared_1974_ = v_isSharedCheck_1986_;
goto v_resetjp_1972_;
}
else
{
lean_inc(v_snapshotTasks_1971_);
lean_inc(v_infoState_1970_);
lean_inc(v_messages_1969_);
lean_inc(v_traceState_1968_);
lean_inc(v_auxDeclNGen_1967_);
lean_inc(v_ngen_1966_);
lean_inc(v_nextMacroScope_1965_);
lean_inc(v_env_1964_);
lean_dec(v___x_1962_);
v___x_1973_ = lean_box(0);
v_isShared_1974_ = v_isSharedCheck_1986_;
goto v_resetjp_1972_;
}
v_resetjp_1972_:
{
lean_object* v_asyncMode_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1979_; 
v_asyncMode_1975_ = lean_ctor_get(v_toEnvExtension_1963_, 2);
lean_inc(v_asyncMode_1975_);
lean_inc(v_decl_1949_);
v___x_1976_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_a_1947_, v_env_1964_, v_decl_1949_, v_asyncMode_1975_, v_decl_1949_);
lean_dec(v_asyncMode_1975_);
v___x_1977_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2);
if (v_isShared_1974_ == 0)
{
lean_ctor_set(v___x_1973_, 5, v___x_1977_);
lean_ctor_set(v___x_1973_, 0, v___x_1976_);
v___x_1979_ = v___x_1973_;
goto v_reusejp_1978_;
}
else
{
lean_object* v_reuseFailAlloc_1985_; 
v_reuseFailAlloc_1985_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1985_, 0, v___x_1976_);
lean_ctor_set(v_reuseFailAlloc_1985_, 1, v_nextMacroScope_1965_);
lean_ctor_set(v_reuseFailAlloc_1985_, 2, v_ngen_1966_);
lean_ctor_set(v_reuseFailAlloc_1985_, 3, v_auxDeclNGen_1967_);
lean_ctor_set(v_reuseFailAlloc_1985_, 4, v_traceState_1968_);
lean_ctor_set(v_reuseFailAlloc_1985_, 5, v___x_1977_);
lean_ctor_set(v_reuseFailAlloc_1985_, 6, v_messages_1969_);
lean_ctor_set(v_reuseFailAlloc_1985_, 7, v_infoState_1970_);
lean_ctor_set(v_reuseFailAlloc_1985_, 8, v_snapshotTasks_1971_);
v___x_1979_ = v_reuseFailAlloc_1985_;
goto v_reusejp_1978_;
}
v_reusejp_1978_:
{
lean_object* v___x_1980_; lean_object* v___x_1981_; lean_object* v___x_1983_; 
v___x_1980_ = lean_st_ref_set(v___y_1957_, v___x_1979_);
v___x_1981_ = lean_box(0);
if (v_isShared_1961_ == 0)
{
lean_ctor_set(v___x_1960_, 0, v___x_1981_);
v___x_1983_ = v___x_1960_;
goto v_reusejp_1982_;
}
else
{
lean_object* v_reuseFailAlloc_1984_; 
v_reuseFailAlloc_1984_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1984_, 0, v___x_1981_);
v___x_1983_ = v_reuseFailAlloc_1984_;
goto v_reusejp_1982_;
}
v_reusejp_1982_:
{
return v___x_1983_;
}
}
}
}
}
else
{
lean_dec(v_decl_1949_);
lean_dec_ref(v_a_1947_);
return v___x_1958_;
}
}
v___jp_1990_:
{
lean_object* v_toEnvExtension_1994_; lean_object* v_asyncMode_1995_; uint8_t v___x_1996_; 
v_toEnvExtension_1994_ = lean_ctor_get(v_a_1947_, 0);
v_asyncMode_1995_ = lean_ctor_get(v_toEnvExtension_1994_, 2);
lean_inc(v_decl_1949_);
lean_inc_ref(v___y_1991_);
v___x_1996_ = l_Lean_EnvExtension_asyncMayModify___redArg(v___y_1991_, v_decl_1949_, v_asyncMode_1995_);
if (v___x_1996_ == 0)
{
lean_object* v___x_1997_; lean_object* v___x_1998_; 
lean_dec_ref(v_a_1947_);
lean_dec_ref(v_validate_1946_);
v___x_1997_ = l_Lean_Environment_asyncPrefix_x3f(v___y_1991_);
v___x_1998_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___redArg(v_name_1948_, v_decl_1949_, v___x_1997_, v___y_1992_, v___y_1993_);
return v___x_1998_;
}
else
{
lean_dec_ref(v___y_1991_);
lean_dec(v_name_1948_);
v___y_1956_ = v___y_1992_;
v___y_1957_ = v___y_1993_;
goto v___jp_1955_;
}
}
v___jp_1999_:
{
lean_object* v___x_2002_; lean_object* v_env_2003_; lean_object* v___x_2004_; 
v___x_2002_ = lean_st_ref_get(v___y_2001_);
v_env_2003_ = lean_ctor_get(v___x_2002_, 0);
lean_inc_ref(v_env_2003_);
lean_dec(v___x_2002_);
v___x_2004_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2003_, v_decl_1949_);
if (lean_obj_tag(v___x_2004_) == 0)
{
v___y_1991_ = v_env_2003_;
v___y_1992_ = v___y_2000_;
v___y_1993_ = v___y_2001_;
goto v___jp_1990_;
}
else
{
lean_object* v___x_2005_; 
lean_dec_ref(v___x_2004_);
lean_dec_ref(v_env_2003_);
lean_dec_ref(v_a_1947_);
lean_dec_ref(v_validate_1946_);
v___x_2005_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg(v_name_1948_, v_decl_1949_, v___y_2000_, v___y_2001_);
return v___x_2005_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__7___boxed(lean_object* v_validate_2010_, lean_object* v_a_2011_, lean_object* v_name_2012_, lean_object* v_decl_2013_, lean_object* v_stx_2014_, lean_object* v_kind_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_, lean_object* v___y_2018_){
_start:
{
uint8_t v_kind_boxed_2019_; lean_object* v_res_2020_; 
v_kind_boxed_2019_ = lean_unbox(v_kind_2015_);
v_res_2020_ = l_Lean_registerTagAttribute___lam__7(v_validate_2010_, v_a_2011_, v_name_2012_, v_decl_2013_, v_stx_2014_, v_kind_boxed_2019_, v___y_2016_, v___y_2017_);
lean_dec(v___y_2017_);
lean_dec_ref(v___y_2016_);
return v_res_2020_;
}
}
static lean_object* _init_l_Lean_registerTagAttribute___closed__5(void){
_start:
{
lean_object* v___x_2026_; lean_object* v___f_2027_; 
v___x_2026_ = l_Lean_NameSet_empty;
v___f_2027_ = lean_alloc_closure((void*)(l_Lean_registerTagAttribute___lam__4___boxed), 4, 1);
lean_closure_set(v___f_2027_, 0, v___x_2026_);
return v___f_2027_;
}
}
static lean_object* _init_l_Lean_registerTagAttribute___closed__6(void){
_start:
{
lean_object* v___x_2028_; lean_object* v___f_2029_; 
v___x_2028_ = l_Lean_NameSet_empty;
v___f_2029_ = lean_alloc_closure((void*)(l_Lean_registerTagAttribute___lam__5___boxed), 2, 1);
lean_closure_set(v___f_2029_, 0, v___x_2028_);
return v___f_2029_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute(lean_object* v_name_2032_, lean_object* v_descr_2033_, lean_object* v_validate_2034_, lean_object* v_ref_2035_, uint8_t v_applicationTime_2036_, lean_object* v_asyncMode_2037_){
_start:
{
lean_object* v___f_2039_; lean_object* v___f_2040_; lean_object* v___f_2041_; lean_object* v___f_2042_; lean_object* v___f_2043_; lean_object* v___f_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; 
v___f_2039_ = ((lean_object*)(l_Lean_registerTagAttribute___closed__0));
v___f_2040_ = ((lean_object*)(l_Lean_registerTagAttribute___closed__2));
v___f_2041_ = ((lean_object*)(l_Lean_registerTagAttribute___closed__3));
v___f_2042_ = ((lean_object*)(l_Lean_registerTagAttribute___closed__4));
v___f_2043_ = lean_obj_once(&l_Lean_registerTagAttribute___closed__5, &l_Lean_registerTagAttribute___closed__5_once, _init_l_Lean_registerTagAttribute___closed__5);
v___f_2044_ = lean_obj_once(&l_Lean_registerTagAttribute___closed__6, &l_Lean_registerTagAttribute___closed__6_once, _init_l_Lean_registerTagAttribute___closed__6);
v___x_2045_ = ((lean_object*)(l_Lean_registerTagAttribute___closed__7));
lean_inc(v_ref_2035_);
v___x_2046_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_2046_, 0, v_ref_2035_);
lean_ctor_set(v___x_2046_, 1, v___f_2044_);
lean_ctor_set(v___x_2046_, 2, v___f_2043_);
lean_ctor_set(v___x_2046_, 3, v___f_2042_);
lean_ctor_set(v___x_2046_, 4, v___f_2041_);
lean_ctor_set(v___x_2046_, 5, v___f_2040_);
lean_ctor_set(v___x_2046_, 6, v_asyncMode_2037_);
lean_ctor_set(v___x_2046_, 7, v___x_2045_);
v___x_2047_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2047_, 0, v___x_2046_);
lean_ctor_set(v___x_2047_, 1, v___f_2039_);
v___x_2048_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_2047_);
if (lean_obj_tag(v___x_2048_) == 0)
{
lean_object* v_a_2049_; lean_object* v___f_2050_; lean_object* v___f_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; 
v_a_2049_ = lean_ctor_get(v___x_2048_, 0);
lean_inc_n(v_a_2049_, 2);
lean_dec_ref(v___x_2048_);
lean_inc_n(v_name_2032_, 2);
v___f_2050_ = lean_alloc_closure((void*)(l_Lean_registerTagAttribute___lam__6___boxed), 5, 1);
lean_closure_set(v___f_2050_, 0, v_name_2032_);
v___f_2051_ = lean_alloc_closure((void*)(l_Lean_registerTagAttribute___lam__7___boxed), 9, 3);
lean_closure_set(v___f_2051_, 0, v_validate_2034_);
lean_closure_set(v___f_2051_, 1, v_a_2049_);
lean_closure_set(v___f_2051_, 2, v_name_2032_);
v___x_2052_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2052_, 0, v_ref_2035_);
lean_ctor_set(v___x_2052_, 1, v_name_2032_);
lean_ctor_set(v___x_2052_, 2, v_descr_2033_);
lean_ctor_set_uint8(v___x_2052_, sizeof(void*)*3, v_applicationTime_2036_);
v___x_2053_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2053_, 0, v___x_2052_);
lean_ctor_set(v___x_2053_, 1, v___f_2051_);
lean_ctor_set(v___x_2053_, 2, v___f_2050_);
lean_inc_ref(v___x_2053_);
v___x_2054_ = l_Lean_registerBuiltinAttribute(v___x_2053_);
if (lean_obj_tag(v___x_2054_) == 0)
{
lean_object* v___x_2056_; uint8_t v_isShared_2057_; uint8_t v_isSharedCheck_2062_; 
v_isSharedCheck_2062_ = !lean_is_exclusive(v___x_2054_);
if (v_isSharedCheck_2062_ == 0)
{
lean_object* v_unused_2063_; 
v_unused_2063_ = lean_ctor_get(v___x_2054_, 0);
lean_dec(v_unused_2063_);
v___x_2056_ = v___x_2054_;
v_isShared_2057_ = v_isSharedCheck_2062_;
goto v_resetjp_2055_;
}
else
{
lean_dec(v___x_2054_);
v___x_2056_ = lean_box(0);
v_isShared_2057_ = v_isSharedCheck_2062_;
goto v_resetjp_2055_;
}
v_resetjp_2055_:
{
lean_object* v___x_2058_; lean_object* v___x_2060_; 
v___x_2058_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2058_, 0, v___x_2053_);
lean_ctor_set(v___x_2058_, 1, v_a_2049_);
if (v_isShared_2057_ == 0)
{
lean_ctor_set(v___x_2056_, 0, v___x_2058_);
v___x_2060_ = v___x_2056_;
goto v_reusejp_2059_;
}
else
{
lean_object* v_reuseFailAlloc_2061_; 
v_reuseFailAlloc_2061_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2061_, 0, v___x_2058_);
v___x_2060_ = v_reuseFailAlloc_2061_;
goto v_reusejp_2059_;
}
v_reusejp_2059_:
{
return v___x_2060_;
}
}
}
else
{
lean_object* v_a_2064_; lean_object* v___x_2066_; uint8_t v_isShared_2067_; uint8_t v_isSharedCheck_2071_; 
lean_dec_ref(v___x_2053_);
lean_dec(v_a_2049_);
v_a_2064_ = lean_ctor_get(v___x_2054_, 0);
v_isSharedCheck_2071_ = !lean_is_exclusive(v___x_2054_);
if (v_isSharedCheck_2071_ == 0)
{
v___x_2066_ = v___x_2054_;
v_isShared_2067_ = v_isSharedCheck_2071_;
goto v_resetjp_2065_;
}
else
{
lean_inc(v_a_2064_);
lean_dec(v___x_2054_);
v___x_2066_ = lean_box(0);
v_isShared_2067_ = v_isSharedCheck_2071_;
goto v_resetjp_2065_;
}
v_resetjp_2065_:
{
lean_object* v___x_2069_; 
if (v_isShared_2067_ == 0)
{
v___x_2069_ = v___x_2066_;
goto v_reusejp_2068_;
}
else
{
lean_object* v_reuseFailAlloc_2070_; 
v_reuseFailAlloc_2070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2070_, 0, v_a_2064_);
v___x_2069_ = v_reuseFailAlloc_2070_;
goto v_reusejp_2068_;
}
v_reusejp_2068_:
{
return v___x_2069_;
}
}
}
}
else
{
lean_object* v_a_2072_; lean_object* v___x_2074_; uint8_t v_isShared_2075_; uint8_t v_isSharedCheck_2079_; 
lean_dec(v_ref_2035_);
lean_dec_ref(v_validate_2034_);
lean_dec_ref(v_descr_2033_);
lean_dec(v_name_2032_);
v_a_2072_ = lean_ctor_get(v___x_2048_, 0);
v_isSharedCheck_2079_ = !lean_is_exclusive(v___x_2048_);
if (v_isSharedCheck_2079_ == 0)
{
v___x_2074_ = v___x_2048_;
v_isShared_2075_ = v_isSharedCheck_2079_;
goto v_resetjp_2073_;
}
else
{
lean_inc(v_a_2072_);
lean_dec(v___x_2048_);
v___x_2074_ = lean_box(0);
v_isShared_2075_ = v_isSharedCheck_2079_;
goto v_resetjp_2073_;
}
v_resetjp_2073_:
{
lean_object* v___x_2077_; 
if (v_isShared_2075_ == 0)
{
v___x_2077_ = v___x_2074_;
goto v_reusejp_2076_;
}
else
{
lean_object* v_reuseFailAlloc_2078_; 
v_reuseFailAlloc_2078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2078_, 0, v_a_2072_);
v___x_2077_ = v_reuseFailAlloc_2078_;
goto v_reusejp_2076_;
}
v_reusejp_2076_:
{
return v___x_2077_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___boxed(lean_object* v_name_2080_, lean_object* v_descr_2081_, lean_object* v_validate_2082_, lean_object* v_ref_2083_, lean_object* v_applicationTime_2084_, lean_object* v_asyncMode_2085_, lean_object* v_a_2086_){
_start:
{
uint8_t v_applicationTime_boxed_2087_; lean_object* v_res_2088_; 
v_applicationTime_boxed_2087_ = lean_unbox(v_applicationTime_2084_);
v_res_2088_ = l_Lean_registerTagAttribute(v_name_2080_, v_descr_2081_, v_validate_2082_, v_ref_2083_, v_applicationTime_boxed_2087_, v_asyncMode_2085_);
return v_res_2088_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerTagAttribute_spec__1(lean_object* v_init_2089_, lean_object* v_t_2090_){
_start:
{
lean_object* v___x_2091_; 
v___x_2091_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerTagAttribute_spec__1_spec__1(v_init_2089_, v_t_2090_);
return v___x_2091_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3(lean_object* v_n_2092_, lean_object* v_as_2093_, lean_object* v_lo_2094_, lean_object* v_hi_2095_, lean_object* v_w_2096_, lean_object* v_hlo_2097_, lean_object* v_hhi_2098_){
_start:
{
lean_object* v___x_2099_; 
v___x_2099_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___redArg(v_as_2093_, v_lo_2094_, v_hi_2095_);
return v___x_2099_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___boxed(lean_object* v_n_2100_, lean_object* v_as_2101_, lean_object* v_lo_2102_, lean_object* v_hi_2103_, lean_object* v_w_2104_, lean_object* v_hlo_2105_, lean_object* v_hhi_2106_){
_start:
{
lean_object* v_res_2107_; 
v_res_2107_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3(v_n_2100_, v_as_2101_, v_lo_2102_, v_hi_2103_, v_w_2104_, v_hlo_2105_, v_hhi_2106_);
lean_dec(v_hi_2103_);
lean_dec(v_n_2100_);
return v_res_2107_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4(lean_object* v_00_u03b1_2108_, lean_object* v_attrName_2109_, lean_object* v_declName_2110_, lean_object* v_asyncPrefix_x3f_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_){
_start:
{
lean_object* v___x_2115_; 
v___x_2115_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___redArg(v_attrName_2109_, v_declName_2110_, v_asyncPrefix_x3f_2111_, v___y_2112_, v___y_2113_);
return v___x_2115_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___boxed(lean_object* v_00_u03b1_2116_, lean_object* v_attrName_2117_, lean_object* v_declName_2118_, lean_object* v_asyncPrefix_x3f_2119_, lean_object* v___y_2120_, lean_object* v___y_2121_, lean_object* v___y_2122_){
_start:
{
lean_object* v_res_2123_; 
v_res_2123_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4(v_00_u03b1_2116_, v_attrName_2117_, v_declName_2118_, v_asyncPrefix_x3f_2119_, v___y_2120_, v___y_2121_);
lean_dec(v___y_2121_);
lean_dec_ref(v___y_2120_);
return v_res_2123_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5(lean_object* v_00_u03b1_2124_, lean_object* v_attrName_2125_, lean_object* v_declName_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_){
_start:
{
lean_object* v___x_2130_; 
v___x_2130_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg(v_attrName_2125_, v_declName_2126_, v___y_2127_, v___y_2128_);
return v___x_2130_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___boxed(lean_object* v_00_u03b1_2131_, lean_object* v_attrName_2132_, lean_object* v_declName_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_){
_start:
{
lean_object* v_res_2137_; 
v_res_2137_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5(v_00_u03b1_2131_, v_attrName_2132_, v_declName_2133_, v___y_2134_, v___y_2135_);
lean_dec(v___y_2135_);
lean_dec_ref(v___y_2134_);
return v_res_2137_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6(lean_object* v_00_u03b1_2138_, lean_object* v_name_2139_, uint8_t v_kind_2140_, lean_object* v___y_2141_, lean_object* v___y_2142_){
_start:
{
lean_object* v___x_2144_; 
v___x_2144_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg(v_name_2139_, v_kind_2140_, v___y_2141_, v___y_2142_);
return v___x_2144_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___boxed(lean_object* v_00_u03b1_2145_, lean_object* v_name_2146_, lean_object* v_kind_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_){
_start:
{
uint8_t v_kind_boxed_2151_; lean_object* v_res_2152_; 
v_kind_boxed_2151_ = lean_unbox(v_kind_2147_);
v_res_2152_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6(v_00_u03b1_2145_, v_name_2146_, v_kind_boxed_2151_, v___y_2148_, v___y_2149_);
lean_dec(v___y_2149_);
lean_dec_ref(v___y_2148_);
return v_res_2152_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg___lam__0(lean_object* v_attr_2153_, lean_object* v_decl_2154_, lean_object* v_env_2155_){
_start:
{
lean_object* v_ext_2156_; lean_object* v_toEnvExtension_2157_; lean_object* v_asyncMode_2158_; lean_object* v___x_2159_; 
v_ext_2156_ = lean_ctor_get(v_attr_2153_, 1);
lean_inc_ref(v_ext_2156_);
lean_dec_ref(v_attr_2153_);
v_toEnvExtension_2157_ = lean_ctor_get(v_ext_2156_, 0);
v_asyncMode_2158_ = lean_ctor_get(v_toEnvExtension_2157_, 2);
lean_inc(v_asyncMode_2158_);
lean_inc(v_decl_2154_);
v___x_2159_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_ext_2156_, v_env_2155_, v_decl_2154_, v_asyncMode_2158_, v_decl_2154_);
lean_dec(v_asyncMode_2158_);
return v___x_2159_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg___lam__1(lean_object* v_modifyEnv_2160_, lean_object* v___f_2161_, lean_object* v_____r_2162_){
_start:
{
lean_object* v___x_2163_; 
v___x_2163_ = lean_apply_1(v_modifyEnv_2160_, v___f_2161_);
return v___x_2163_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg___lam__2(lean_object* v_attr_2164_, lean_object* v_env_2165_, lean_object* v_decl_2166_, lean_object* v_inst_2167_, lean_object* v_inst_2168_, lean_object* v_toBind_2169_, lean_object* v___f_2170_, lean_object* v_modifyEnv_2171_, lean_object* v___f_2172_, lean_object* v_____r_2173_){
_start:
{
lean_object* v_ext_2174_; lean_object* v_toEnvExtension_2175_; lean_object* v_attr_2176_; lean_object* v_asyncMode_2177_; uint8_t v___x_2178_; 
v_ext_2174_ = lean_ctor_get(v_attr_2164_, 1);
v_toEnvExtension_2175_ = lean_ctor_get(v_ext_2174_, 0);
lean_inc_ref(v_toEnvExtension_2175_);
v_attr_2176_ = lean_ctor_get(v_attr_2164_, 0);
lean_inc_ref(v_attr_2176_);
lean_dec_ref(v_attr_2164_);
v_asyncMode_2177_ = lean_ctor_get(v_toEnvExtension_2175_, 2);
lean_inc(v_asyncMode_2177_);
lean_dec_ref(v_toEnvExtension_2175_);
lean_inc(v_decl_2166_);
lean_inc_ref(v_env_2165_);
v___x_2178_ = l_Lean_EnvExtension_asyncMayModify___redArg(v_env_2165_, v_decl_2166_, v_asyncMode_2177_);
lean_dec(v_asyncMode_2177_);
if (v___x_2178_ == 0)
{
lean_object* v_toAttributeImplCore_2179_; lean_object* v_name_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; 
lean_dec_ref(v___f_2172_);
lean_dec(v_modifyEnv_2171_);
v_toAttributeImplCore_2179_ = lean_ctor_get(v_attr_2176_, 0);
lean_inc_ref(v_toAttributeImplCore_2179_);
lean_dec_ref(v_attr_2176_);
v_name_2180_ = lean_ctor_get(v_toAttributeImplCore_2179_, 1);
lean_inc(v_name_2180_);
lean_dec_ref(v_toAttributeImplCore_2179_);
v___x_2181_ = l_Lean_Environment_asyncPrefix_x3f(v_env_2165_);
v___x_2182_ = l_Lean_throwAttrNotInAsyncCtx___redArg(v_inst_2167_, v_inst_2168_, v_name_2180_, v_decl_2166_, v___x_2181_);
v___x_2183_ = lean_apply_4(v_toBind_2169_, lean_box(0), lean_box(0), v___x_2182_, v___f_2170_);
return v___x_2183_;
}
else
{
lean_object* v___x_2184_; 
lean_dec_ref(v_attr_2176_);
lean_dec(v___f_2170_);
lean_dec(v_toBind_2169_);
lean_dec_ref(v_inst_2168_);
lean_dec_ref(v_inst_2167_);
lean_dec(v_decl_2166_);
lean_dec_ref(v_env_2165_);
v___x_2184_ = lean_apply_1(v_modifyEnv_2171_, v___f_2172_);
return v___x_2184_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg___lam__3(lean_object* v___f_2185_, lean_object* v_____r_2186_){
_start:
{
lean_object* v___x_2187_; 
v___x_2187_ = lean_apply_1(v___f_2185_, v_____r_2186_);
return v___x_2187_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg___lam__4(lean_object* v_attr_2188_, lean_object* v_decl_2189_, lean_object* v_inst_2190_, lean_object* v_inst_2191_, lean_object* v_toBind_2192_, lean_object* v___f_2193_, lean_object* v_modifyEnv_2194_, lean_object* v___f_2195_, lean_object* v_env_2196_){
_start:
{
lean_object* v___f_2197_; lean_object* v___x_2198_; 
lean_inc_ref(v___f_2195_);
lean_inc(v_modifyEnv_2194_);
lean_inc(v___f_2193_);
lean_inc(v_toBind_2192_);
lean_inc_ref(v_inst_2191_);
lean_inc_ref(v_inst_2190_);
lean_inc(v_decl_2189_);
lean_inc_ref(v_env_2196_);
lean_inc_ref(v_attr_2188_);
v___f_2197_ = lean_alloc_closure((void*)(l_Lean_TagAttribute_setTag___redArg___lam__2), 10, 9);
lean_closure_set(v___f_2197_, 0, v_attr_2188_);
lean_closure_set(v___f_2197_, 1, v_env_2196_);
lean_closure_set(v___f_2197_, 2, v_decl_2189_);
lean_closure_set(v___f_2197_, 3, v_inst_2190_);
lean_closure_set(v___f_2197_, 4, v_inst_2191_);
lean_closure_set(v___f_2197_, 5, v_toBind_2192_);
lean_closure_set(v___f_2197_, 6, v___f_2193_);
lean_closure_set(v___f_2197_, 7, v_modifyEnv_2194_);
lean_closure_set(v___f_2197_, 8, v___f_2195_);
v___x_2198_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2196_, v_decl_2189_);
if (lean_obj_tag(v___x_2198_) == 0)
{
lean_object* v___x_2199_; lean_object* v___x_2200_; 
lean_dec_ref(v___f_2197_);
v___x_2199_ = lean_box(0);
v___x_2200_ = l_Lean_TagAttribute_setTag___redArg___lam__2(v_attr_2188_, v_env_2196_, v_decl_2189_, v_inst_2190_, v_inst_2191_, v_toBind_2192_, v___f_2193_, v_modifyEnv_2194_, v___f_2195_, v___x_2199_);
return v___x_2200_;
}
else
{
lean_object* v_attr_2201_; lean_object* v_toAttributeImplCore_2202_; lean_object* v_name_2203_; lean_object* v___f_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; 
lean_dec_ref(v___x_2198_);
lean_dec_ref(v_env_2196_);
lean_dec_ref(v___f_2195_);
lean_dec(v_modifyEnv_2194_);
lean_dec(v___f_2193_);
v_attr_2201_ = lean_ctor_get(v_attr_2188_, 0);
lean_inc_ref(v_attr_2201_);
lean_dec_ref(v_attr_2188_);
v_toAttributeImplCore_2202_ = lean_ctor_get(v_attr_2201_, 0);
lean_inc_ref(v_toAttributeImplCore_2202_);
lean_dec_ref(v_attr_2201_);
v_name_2203_ = lean_ctor_get(v_toAttributeImplCore_2202_, 1);
lean_inc(v_name_2203_);
lean_dec_ref(v_toAttributeImplCore_2202_);
v___f_2204_ = lean_alloc_closure((void*)(l_Lean_TagAttribute_setTag___redArg___lam__3), 2, 1);
lean_closure_set(v___f_2204_, 0, v___f_2197_);
v___x_2205_ = l_Lean_throwAttrDeclInImportedModule___redArg(v_inst_2190_, v_inst_2191_, v_name_2203_, v_decl_2189_);
v___x_2206_ = lean_apply_4(v_toBind_2192_, lean_box(0), lean_box(0), v___x_2205_, v___f_2204_);
return v___x_2206_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg(lean_object* v_inst_2207_, lean_object* v_inst_2208_, lean_object* v_inst_2209_, lean_object* v_attr_2210_, lean_object* v_decl_2211_){
_start:
{
lean_object* v_toBind_2212_; lean_object* v_getEnv_2213_; lean_object* v_modifyEnv_2214_; lean_object* v___f_2215_; lean_object* v___f_2216_; lean_object* v___f_2217_; lean_object* v___x_2218_; 
v_toBind_2212_ = lean_ctor_get(v_inst_2207_, 1);
lean_inc_n(v_toBind_2212_, 2);
v_getEnv_2213_ = lean_ctor_get(v_inst_2209_, 0);
lean_inc(v_getEnv_2213_);
v_modifyEnv_2214_ = lean_ctor_get(v_inst_2209_, 1);
lean_inc_n(v_modifyEnv_2214_, 2);
lean_dec_ref(v_inst_2209_);
lean_inc(v_decl_2211_);
lean_inc_ref(v_attr_2210_);
v___f_2215_ = lean_alloc_closure((void*)(l_Lean_TagAttribute_setTag___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2215_, 0, v_attr_2210_);
lean_closure_set(v___f_2215_, 1, v_decl_2211_);
lean_inc_ref(v___f_2215_);
v___f_2216_ = lean_alloc_closure((void*)(l_Lean_TagAttribute_setTag___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2216_, 0, v_modifyEnv_2214_);
lean_closure_set(v___f_2216_, 1, v___f_2215_);
v___f_2217_ = lean_alloc_closure((void*)(l_Lean_TagAttribute_setTag___redArg___lam__4), 9, 8);
lean_closure_set(v___f_2217_, 0, v_attr_2210_);
lean_closure_set(v___f_2217_, 1, v_decl_2211_);
lean_closure_set(v___f_2217_, 2, v_inst_2207_);
lean_closure_set(v___f_2217_, 3, v_inst_2208_);
lean_closure_set(v___f_2217_, 4, v_toBind_2212_);
lean_closure_set(v___f_2217_, 5, v___f_2216_);
lean_closure_set(v___f_2217_, 6, v_modifyEnv_2214_);
lean_closure_set(v___f_2217_, 7, v___f_2215_);
v___x_2218_ = lean_apply_4(v_toBind_2212_, lean_box(0), lean_box(0), v_getEnv_2213_, v___f_2217_);
return v___x_2218_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag(lean_object* v_m_2219_, lean_object* v_inst_2220_, lean_object* v_inst_2221_, lean_object* v_inst_2222_, lean_object* v_attr_2223_, lean_object* v_decl_2224_){
_start:
{
lean_object* v___x_2225_; 
v___x_2225_ = l_Lean_TagAttribute_setTag___redArg(v_inst_2220_, v_inst_2221_, v_inst_2222_, v_attr_2223_, v_decl_2224_);
return v___x_2225_;
}
}
LEAN_EXPORT uint8_t l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___redArg(lean_object* v_as_2226_, lean_object* v_k_2227_, lean_object* v_x_2228_, lean_object* v_x_2229_){
_start:
{
lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v_m_2232_; lean_object* v_a_2233_; uint8_t v___x_2234_; 
v___x_2230_ = lean_nat_add(v_x_2228_, v_x_2229_);
v___x_2231_ = lean_unsigned_to_nat(1u);
v_m_2232_ = lean_nat_shiftr(v___x_2230_, v___x_2231_);
lean_dec(v___x_2230_);
v_a_2233_ = lean_array_fget_borrowed(v_as_2226_, v_m_2232_);
v___x_2234_ = l_Lean_Name_quickLt(v_a_2233_, v_k_2227_);
if (v___x_2234_ == 0)
{
uint8_t v___x_2235_; 
lean_dec(v_x_2229_);
v___x_2235_ = l_Lean_Name_quickLt(v_k_2227_, v_a_2233_);
if (v___x_2235_ == 0)
{
uint8_t v___x_2236_; 
lean_dec(v_m_2232_);
lean_dec(v_x_2228_);
v___x_2236_ = 1;
return v___x_2236_;
}
else
{
lean_object* v___x_2237_; uint8_t v___x_2238_; 
v___x_2237_ = lean_unsigned_to_nat(0u);
v___x_2238_ = lean_nat_dec_eq(v_m_2232_, v___x_2237_);
if (v___x_2238_ == 0)
{
lean_object* v___x_2239_; uint8_t v___x_2240_; 
v___x_2239_ = lean_nat_sub(v_m_2232_, v___x_2231_);
lean_dec(v_m_2232_);
v___x_2240_ = lean_nat_dec_lt(v___x_2239_, v_x_2228_);
if (v___x_2240_ == 0)
{
v_x_2229_ = v___x_2239_;
goto _start;
}
else
{
lean_dec(v___x_2239_);
lean_dec(v_x_2228_);
return v___x_2234_;
}
}
else
{
lean_dec(v_m_2232_);
lean_dec(v_x_2228_);
return v___x_2234_;
}
}
}
else
{
lean_object* v___x_2242_; uint8_t v___x_2243_; 
lean_dec(v_x_2228_);
v___x_2242_ = lean_nat_add(v_m_2232_, v___x_2231_);
lean_dec(v_m_2232_);
v___x_2243_ = lean_nat_dec_le(v___x_2242_, v_x_2229_);
if (v___x_2243_ == 0)
{
lean_dec(v___x_2242_);
lean_dec(v_x_2229_);
return v___x_2243_;
}
else
{
v_x_2228_ = v___x_2242_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___redArg___boxed(lean_object* v_as_2245_, lean_object* v_k_2246_, lean_object* v_x_2247_, lean_object* v_x_2248_){
_start:
{
uint8_t v_res_2249_; lean_object* v_r_2250_; 
v_res_2249_ = l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___redArg(v_as_2245_, v_k_2246_, v_x_2247_, v_x_2248_);
lean_dec(v_k_2246_);
lean_dec_ref(v_as_2245_);
v_r_2250_ = lean_box(v_res_2249_);
return v_r_2250_;
}
}
LEAN_EXPORT uint8_t l_Lean_TagAttribute_hasTag(lean_object* v_attr_2251_, lean_object* v_env_2252_, lean_object* v_decl_2253_){
_start:
{
lean_object* v___x_2254_; lean_object* v___x_2255_; 
v___x_2254_ = lean_box(1);
v___x_2255_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2252_, v_decl_2253_);
if (lean_obj_tag(v___x_2255_) == 0)
{
lean_object* v_ext_2256_; lean_object* v_toEnvExtension_2257_; lean_object* v_asyncMode_2258_; lean_object* v___x_2259_; uint8_t v___x_2260_; 
v_ext_2256_ = lean_ctor_get(v_attr_2251_, 1);
v_toEnvExtension_2257_ = lean_ctor_get(v_ext_2256_, 0);
v_asyncMode_2258_ = lean_ctor_get(v_toEnvExtension_2257_, 2);
lean_inc(v_decl_2253_);
v___x_2259_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2254_, v_ext_2256_, v_env_2252_, v_asyncMode_2258_, v_decl_2253_);
v___x_2260_ = l_Lean_NameSet_contains(v___x_2259_, v_decl_2253_);
lean_dec(v_decl_2253_);
lean_dec(v___x_2259_);
return v___x_2260_;
}
else
{
lean_object* v_val_2261_; lean_object* v_ext_2262_; uint8_t v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; uint8_t v___x_2267_; 
v_val_2261_ = lean_ctor_get(v___x_2255_, 0);
lean_inc(v_val_2261_);
lean_dec_ref(v___x_2255_);
v_ext_2262_ = lean_ctor_get(v_attr_2251_, 1);
v___x_2263_ = 0;
v___x_2264_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_2254_, v_ext_2262_, v_env_2252_, v_val_2261_, v___x_2263_);
lean_dec(v_val_2261_);
lean_dec_ref(v_env_2252_);
v___x_2265_ = lean_unsigned_to_nat(0u);
v___x_2266_ = lean_array_get_size(v___x_2264_);
v___x_2267_ = lean_nat_dec_lt(v___x_2265_, v___x_2266_);
if (v___x_2267_ == 0)
{
lean_dec_ref(v___x_2264_);
lean_dec(v_decl_2253_);
return v___x_2267_;
}
else
{
lean_object* v___x_2268_; lean_object* v___x_2269_; uint8_t v___x_2270_; 
v___x_2268_ = lean_unsigned_to_nat(1u);
v___x_2269_ = lean_nat_sub(v___x_2266_, v___x_2268_);
v___x_2270_ = lean_nat_dec_le(v___x_2265_, v___x_2269_);
if (v___x_2270_ == 0)
{
lean_dec(v___x_2269_);
lean_dec_ref(v___x_2264_);
lean_dec(v_decl_2253_);
return v___x_2270_;
}
else
{
uint8_t v___x_2271_; 
v___x_2271_ = l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___redArg(v___x_2264_, v_decl_2253_, v___x_2265_, v___x_2269_);
lean_dec(v_decl_2253_);
lean_dec_ref(v___x_2264_);
return v___x_2271_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_hasTag___boxed(lean_object* v_attr_2272_, lean_object* v_env_2273_, lean_object* v_decl_2274_){
_start:
{
uint8_t v_res_2275_; lean_object* v_r_2276_; 
v_res_2275_ = l_Lean_TagAttribute_hasTag(v_attr_2272_, v_env_2273_, v_decl_2274_);
lean_dec_ref(v_attr_2272_);
v_r_2276_ = lean_box(v_res_2275_);
return v_r_2276_;
}
}
LEAN_EXPORT uint8_t l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0(lean_object* v_as_2277_, lean_object* v_k_2278_, lean_object* v_x_2279_, lean_object* v_x_2280_, lean_object* v_x_2281_){
_start:
{
uint8_t v___x_2282_; 
v___x_2282_ = l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___redArg(v_as_2277_, v_k_2278_, v_x_2279_, v_x_2280_);
return v___x_2282_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___boxed(lean_object* v_as_2283_, lean_object* v_k_2284_, lean_object* v_x_2285_, lean_object* v_x_2286_, lean_object* v_x_2287_){
_start:
{
uint8_t v_res_2288_; lean_object* v_r_2289_; 
v_res_2288_ = l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0(v_as_2283_, v_k_2284_, v_x_2285_, v_x_2286_, v_x_2287_);
lean_dec(v_k_2284_);
lean_dec_ref(v_as_2283_);
v_r_2289_ = lean_box(v_res_2288_);
return v_r_2289_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__0(lean_object* v_x_2290_, lean_object* v___y_2291_){
_start:
{
lean_object* v___x_2293_; lean_object* v___x_2294_; 
v___x_2293_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___lam__0___closed__1));
v___x_2294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2294_, 0, v___x_2293_);
return v___x_2294_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__0___boxed(lean_object* v_x_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_){
_start:
{
lean_object* v_res_2298_; 
v_res_2298_ = l_Lean_instInhabitedParametricAttribute_default___lam__0(v_x_2295_, v___y_2296_);
lean_dec_ref(v___y_2296_);
lean_dec_ref(v_x_2295_);
return v_res_2298_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__1(lean_object* v_s_2299_, lean_object* v_x_2300_){
_start:
{
lean_inc_ref(v_s_2299_);
return v_s_2299_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__1___boxed(lean_object* v_s_2301_, lean_object* v_x_2302_){
_start:
{
lean_object* v_res_2303_; 
v_res_2303_ = l_Lean_instInhabitedParametricAttribute_default___lam__1(v_s_2301_, v_x_2302_);
lean_dec_ref(v_x_2302_);
lean_dec_ref(v_s_2301_);
return v_res_2303_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__2(lean_object* v_x_2308_, lean_object* v_x_2309_){
_start:
{
lean_object* v___x_2310_; 
v___x_2310_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___lam__2___closed__1));
return v___x_2310_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__2___boxed(lean_object* v_x_2311_, lean_object* v_x_2312_){
_start:
{
lean_object* v_res_2313_; 
v_res_2313_ = l_Lean_instInhabitedParametricAttribute_default___lam__2(v_x_2311_, v_x_2312_);
lean_dec_ref(v_x_2312_);
lean_dec_ref(v_x_2311_);
return v_res_2313_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__3(lean_object* v_x_2314_){
_start:
{
lean_object* v___x_2315_; 
v___x_2315_ = lean_box(0);
return v___x_2315_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__3___boxed(lean_object* v_x_2316_){
_start:
{
lean_object* v_res_2317_; 
v_res_2317_ = l_Lean_instInhabitedParametricAttribute_default___lam__3(v_x_2316_);
lean_dec_ref(v_x_2316_);
return v_res_2317_;
}
}
static lean_object* _init_l_Lean_instInhabitedParametricAttribute_default___closed__4(void){
_start:
{
lean_object* v___x_2322_; 
v___x_2322_ = l_Lean_instInhabitedEnvExtension_default(lean_box(0));
return v___x_2322_;
}
}
static lean_object* _init_l_Lean_instInhabitedParametricAttribute_default___closed__5(void){
_start:
{
lean_object* v___f_2323_; lean_object* v___f_2324_; lean_object* v___f_2325_; lean_object* v___f_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; 
v___f_2323_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___closed__3));
v___f_2324_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___closed__2));
v___f_2325_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___closed__1));
v___f_2326_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___closed__0));
v___x_2327_ = lean_box(0);
v___x_2328_ = lean_obj_once(&l_Lean_instInhabitedParametricAttribute_default___closed__4, &l_Lean_instInhabitedParametricAttribute_default___closed__4_once, _init_l_Lean_instInhabitedParametricAttribute_default___closed__4);
v___x_2329_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2329_, 0, v___x_2328_);
lean_ctor_set(v___x_2329_, 1, v___x_2327_);
lean_ctor_set(v___x_2329_, 2, v___f_2326_);
lean_ctor_set(v___x_2329_, 3, v___f_2325_);
lean_ctor_set(v___x_2329_, 4, v___f_2324_);
lean_ctor_set(v___x_2329_, 5, v___f_2323_);
return v___x_2329_;
}
}
static lean_object* _init_l_Lean_instInhabitedParametricAttribute_default___closed__6(void){
_start:
{
uint8_t v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; 
v___x_2330_ = 0;
v___x_2331_ = lean_obj_once(&l_Lean_instInhabitedParametricAttribute_default___closed__5, &l_Lean_instInhabitedParametricAttribute_default___closed__5_once, _init_l_Lean_instInhabitedParametricAttribute_default___closed__5);
v___x_2332_ = ((lean_object*)(l_Lean_instInhabitedAttributeImpl_default));
v___x_2333_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2333_, 0, v___x_2332_);
lean_ctor_set(v___x_2333_, 1, v___x_2331_);
lean_ctor_set_uint8(v___x_2333_, sizeof(void*)*2, v___x_2330_);
return v___x_2333_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default(lean_object* v_a_2334_){
_start:
{
lean_object* v___x_2335_; 
v___x_2335_ = lean_obj_once(&l_Lean_instInhabitedParametricAttribute_default___closed__6, &l_Lean_instInhabitedParametricAttribute_default___closed__6_once, _init_l_Lean_instInhabitedParametricAttribute_default___closed__6);
return v___x_2335_;
}
}
static lean_object* _init_l_Lean_instInhabitedParametricAttribute___closed__0(void){
_start:
{
lean_object* v___x_2336_; 
v___x_2336_ = l_Lean_instInhabitedParametricAttribute_default(lean_box(0));
return v___x_2336_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute(lean_object* v_a_2337_){
_start:
{
lean_object* v___x_2338_; 
v___x_2338_ = lean_obj_once(&l_Lean_instInhabitedParametricAttribute___closed__0, &l_Lean_instInhabitedParametricAttribute___closed__0_once, _init_l_Lean_instInhabitedParametricAttribute___closed__0);
return v___x_2338_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_registerParametricAttribute_spec__4___redArg(lean_object* v_env_2339_, lean_object* v___y_2340_){
_start:
{
lean_object* v___x_2342_; lean_object* v_nextMacroScope_2343_; lean_object* v_ngen_2344_; lean_object* v_auxDeclNGen_2345_; lean_object* v_traceState_2346_; lean_object* v_messages_2347_; lean_object* v_infoState_2348_; lean_object* v_snapshotTasks_2349_; lean_object* v___x_2351_; uint8_t v_isShared_2352_; uint8_t v_isSharedCheck_2360_; 
v___x_2342_ = lean_st_ref_take(v___y_2340_);
v_nextMacroScope_2343_ = lean_ctor_get(v___x_2342_, 1);
v_ngen_2344_ = lean_ctor_get(v___x_2342_, 2);
v_auxDeclNGen_2345_ = lean_ctor_get(v___x_2342_, 3);
v_traceState_2346_ = lean_ctor_get(v___x_2342_, 4);
v_messages_2347_ = lean_ctor_get(v___x_2342_, 6);
v_infoState_2348_ = lean_ctor_get(v___x_2342_, 7);
v_snapshotTasks_2349_ = lean_ctor_get(v___x_2342_, 8);
v_isSharedCheck_2360_ = !lean_is_exclusive(v___x_2342_);
if (v_isSharedCheck_2360_ == 0)
{
lean_object* v_unused_2361_; lean_object* v_unused_2362_; 
v_unused_2361_ = lean_ctor_get(v___x_2342_, 5);
lean_dec(v_unused_2361_);
v_unused_2362_ = lean_ctor_get(v___x_2342_, 0);
lean_dec(v_unused_2362_);
v___x_2351_ = v___x_2342_;
v_isShared_2352_ = v_isSharedCheck_2360_;
goto v_resetjp_2350_;
}
else
{
lean_inc(v_snapshotTasks_2349_);
lean_inc(v_infoState_2348_);
lean_inc(v_messages_2347_);
lean_inc(v_traceState_2346_);
lean_inc(v_auxDeclNGen_2345_);
lean_inc(v_ngen_2344_);
lean_inc(v_nextMacroScope_2343_);
lean_dec(v___x_2342_);
v___x_2351_ = lean_box(0);
v_isShared_2352_ = v_isSharedCheck_2360_;
goto v_resetjp_2350_;
}
v_resetjp_2350_:
{
lean_object* v___x_2353_; lean_object* v___x_2355_; 
v___x_2353_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2);
if (v_isShared_2352_ == 0)
{
lean_ctor_set(v___x_2351_, 5, v___x_2353_);
lean_ctor_set(v___x_2351_, 0, v_env_2339_);
v___x_2355_ = v___x_2351_;
goto v_reusejp_2354_;
}
else
{
lean_object* v_reuseFailAlloc_2359_; 
v_reuseFailAlloc_2359_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2359_, 0, v_env_2339_);
lean_ctor_set(v_reuseFailAlloc_2359_, 1, v_nextMacroScope_2343_);
lean_ctor_set(v_reuseFailAlloc_2359_, 2, v_ngen_2344_);
lean_ctor_set(v_reuseFailAlloc_2359_, 3, v_auxDeclNGen_2345_);
lean_ctor_set(v_reuseFailAlloc_2359_, 4, v_traceState_2346_);
lean_ctor_set(v_reuseFailAlloc_2359_, 5, v___x_2353_);
lean_ctor_set(v_reuseFailAlloc_2359_, 6, v_messages_2347_);
lean_ctor_set(v_reuseFailAlloc_2359_, 7, v_infoState_2348_);
lean_ctor_set(v_reuseFailAlloc_2359_, 8, v_snapshotTasks_2349_);
v___x_2355_ = v_reuseFailAlloc_2359_;
goto v_reusejp_2354_;
}
v_reusejp_2354_:
{
lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; 
v___x_2356_ = lean_st_ref_set(v___y_2340_, v___x_2355_);
v___x_2357_ = lean_box(0);
v___x_2358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2358_, 0, v___x_2357_);
return v___x_2358_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_registerParametricAttribute_spec__4___redArg___boxed(lean_object* v_env_2363_, lean_object* v___y_2364_, lean_object* v___y_2365_){
_start:
{
lean_object* v_res_2366_; 
v_res_2366_ = l_Lean_setEnv___at___00Lean_registerParametricAttribute_spec__4___redArg(v_env_2363_, v___y_2364_);
lean_dec(v___y_2364_);
return v_res_2366_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_registerParametricAttribute_spec__4(lean_object* v_env_2367_, lean_object* v___y_2368_, lean_object* v___y_2369_){
_start:
{
lean_object* v___x_2371_; 
v___x_2371_ = l_Lean_setEnv___at___00Lean_registerParametricAttribute_spec__4___redArg(v_env_2367_, v___y_2369_);
return v___x_2371_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_registerParametricAttribute_spec__4___boxed(lean_object* v_env_2372_, lean_object* v___y_2373_, lean_object* v___y_2374_, lean_object* v___y_2375_){
_start:
{
lean_object* v_res_2376_; 
v_res_2376_ = l_Lean_setEnv___at___00Lean_registerParametricAttribute_spec__4(v_env_2372_, v___y_2373_, v___y_2374_);
lean_dec(v___y_2374_);
lean_dec_ref(v___y_2373_);
return v_res_2376_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___lam__0(lean_object* v_x_2377_, lean_object* v_p_2378_){
_start:
{
lean_object* v_fst_2379_; lean_object* v_snd_2380_; lean_object* v___x_2382_; uint8_t v_isShared_2383_; uint8_t v_isSharedCheck_2397_; 
v_fst_2379_ = lean_ctor_get(v_x_2377_, 0);
v_snd_2380_ = lean_ctor_get(v_x_2377_, 1);
v_isSharedCheck_2397_ = !lean_is_exclusive(v_x_2377_);
if (v_isSharedCheck_2397_ == 0)
{
v___x_2382_ = v_x_2377_;
v_isShared_2383_ = v_isSharedCheck_2397_;
goto v_resetjp_2381_;
}
else
{
lean_inc(v_snd_2380_);
lean_inc(v_fst_2379_);
lean_dec(v_x_2377_);
v___x_2382_ = lean_box(0);
v_isShared_2383_ = v_isSharedCheck_2397_;
goto v_resetjp_2381_;
}
v_resetjp_2381_:
{
lean_object* v_fst_2384_; lean_object* v_snd_2385_; lean_object* v___x_2387_; uint8_t v_isShared_2388_; uint8_t v_isSharedCheck_2396_; 
v_fst_2384_ = lean_ctor_get(v_p_2378_, 0);
v_snd_2385_ = lean_ctor_get(v_p_2378_, 1);
v_isSharedCheck_2396_ = !lean_is_exclusive(v_p_2378_);
if (v_isSharedCheck_2396_ == 0)
{
v___x_2387_ = v_p_2378_;
v_isShared_2388_ = v_isSharedCheck_2396_;
goto v_resetjp_2386_;
}
else
{
lean_inc(v_snd_2385_);
lean_inc(v_fst_2384_);
lean_dec(v_p_2378_);
v___x_2387_ = lean_box(0);
v_isShared_2388_ = v_isSharedCheck_2396_;
goto v_resetjp_2386_;
}
v_resetjp_2386_:
{
lean_object* v___x_2390_; 
lean_inc(v_fst_2384_);
if (v_isShared_2383_ == 0)
{
lean_ctor_set_tag(v___x_2382_, 1);
lean_ctor_set(v___x_2382_, 1, v_fst_2379_);
lean_ctor_set(v___x_2382_, 0, v_fst_2384_);
v___x_2390_ = v___x_2382_;
goto v_reusejp_2389_;
}
else
{
lean_object* v_reuseFailAlloc_2395_; 
v_reuseFailAlloc_2395_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2395_, 0, v_fst_2384_);
lean_ctor_set(v_reuseFailAlloc_2395_, 1, v_fst_2379_);
v___x_2390_ = v_reuseFailAlloc_2395_;
goto v_reusejp_2389_;
}
v_reusejp_2389_:
{
lean_object* v___x_2391_; lean_object* v___x_2393_; 
v___x_2391_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_2384_, v_snd_2385_, v_snd_2380_);
if (v_isShared_2388_ == 0)
{
lean_ctor_set(v___x_2387_, 1, v___x_2391_);
lean_ctor_set(v___x_2387_, 0, v___x_2390_);
v___x_2393_ = v___x_2387_;
goto v_reusejp_2392_;
}
else
{
lean_object* v_reuseFailAlloc_2394_; 
v_reuseFailAlloc_2394_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2394_, 0, v___x_2390_);
lean_ctor_set(v_reuseFailAlloc_2394_, 1, v___x_2391_);
v___x_2393_ = v_reuseFailAlloc_2394_;
goto v_reusejp_2392_;
}
v_reusejp_2392_:
{
return v___x_2393_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1_spec__1___redArg(lean_object* v_init_2398_, lean_object* v_x_2399_){
_start:
{
if (lean_obj_tag(v_x_2399_) == 0)
{
lean_object* v_k_2400_; lean_object* v_v_2401_; lean_object* v_l_2402_; lean_object* v_r_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; 
v_k_2400_ = lean_ctor_get(v_x_2399_, 1);
v_v_2401_ = lean_ctor_get(v_x_2399_, 2);
v_l_2402_ = lean_ctor_get(v_x_2399_, 3);
v_r_2403_ = lean_ctor_get(v_x_2399_, 4);
v___x_2404_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1_spec__1___redArg(v_init_2398_, v_l_2402_);
lean_inc(v_v_2401_);
lean_inc(v_k_2400_);
v___x_2405_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2405_, 0, v_k_2400_);
lean_ctor_set(v___x_2405_, 1, v_v_2401_);
v___x_2406_ = lean_array_push(v___x_2404_, v___x_2405_);
v_init_2398_ = v___x_2406_;
v_x_2399_ = v_r_2403_;
goto _start;
}
else
{
return v_init_2398_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1_spec__1___redArg___boxed(lean_object* v_init_2408_, lean_object* v_x_2409_){
_start:
{
lean_object* v_res_2410_; 
v_res_2410_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1_spec__1___redArg(v_init_2408_, v_x_2409_);
lean_dec(v_x_2409_);
return v_res_2410_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2___redArg___lam__0(lean_object* v_a_2411_, lean_object* v_b_2412_){
_start:
{
lean_object* v_fst_2413_; lean_object* v_fst_2414_; uint8_t v___x_2415_; 
v_fst_2413_ = lean_ctor_get(v_a_2411_, 0);
v_fst_2414_ = lean_ctor_get(v_b_2412_, 0);
v___x_2415_ = l_Lean_Name_quickLt(v_fst_2413_, v_fst_2414_);
return v___x_2415_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2___redArg___lam__0___boxed(lean_object* v_a_2416_, lean_object* v_b_2417_){
_start:
{
uint8_t v_res_2418_; lean_object* v_r_2419_; 
v_res_2418_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2___redArg___lam__0(v_a_2416_, v_b_2417_);
lean_dec_ref(v_b_2417_);
lean_dec_ref(v_a_2416_);
v_r_2419_ = lean_box(v_res_2418_);
return v_r_2419_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2___redArg(lean_object* v_as_2421_, lean_object* v_lo_2422_, lean_object* v_hi_2423_){
_start:
{
uint8_t v___x_2424_; 
v___x_2424_ = lean_nat_dec_lt(v_lo_2422_, v_hi_2423_);
if (v___x_2424_ == 0)
{
lean_dec(v_lo_2422_);
return v_as_2421_;
}
else
{
lean_object* v___f_2425_; lean_object* v___x_2426_; lean_object* v_fst_2427_; lean_object* v_snd_2428_; uint8_t v___x_2429_; 
v___f_2425_ = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2___redArg___closed__0));
lean_inc(v_lo_2422_);
v___x_2426_ = l_Array_qpartition___redArg(v_as_2421_, v___f_2425_, v_lo_2422_, v_hi_2423_);
v_fst_2427_ = lean_ctor_get(v___x_2426_, 0);
lean_inc(v_fst_2427_);
v_snd_2428_ = lean_ctor_get(v___x_2426_, 1);
lean_inc(v_snd_2428_);
lean_dec_ref(v___x_2426_);
v___x_2429_ = lean_nat_dec_le(v_hi_2423_, v_fst_2427_);
if (v___x_2429_ == 0)
{
lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; 
v___x_2430_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2___redArg(v_snd_2428_, v_lo_2422_, v_fst_2427_);
v___x_2431_ = lean_unsigned_to_nat(1u);
v___x_2432_ = lean_nat_add(v_fst_2427_, v___x_2431_);
lean_dec(v_fst_2427_);
v_as_2421_ = v___x_2430_;
v_lo_2422_ = v___x_2432_;
goto _start;
}
else
{
lean_dec(v_fst_2427_);
lean_dec(v_lo_2422_);
return v_snd_2428_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2___redArg___boxed(lean_object* v_as_2434_, lean_object* v_lo_2435_, lean_object* v_hi_2436_){
_start:
{
lean_object* v_res_2437_; 
v_res_2437_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2___redArg(v_as_2434_, v_lo_2435_, v_hi_2436_);
lean_dec(v_hi_2436_);
return v_res_2437_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3_spec__4___redArg(lean_object* v_snd_2438_, lean_object* v_as_2439_, size_t v_i_2440_, size_t v_stop_2441_, lean_object* v_b_2442_){
_start:
{
lean_object* v___y_2444_; uint8_t v___x_2448_; 
v___x_2448_ = lean_usize_dec_eq(v_i_2440_, v_stop_2441_);
if (v___x_2448_ == 0)
{
lean_object* v___x_2449_; lean_object* v___x_2450_; 
v___x_2449_ = lean_array_uget_borrowed(v_as_2439_, v_i_2440_);
v___x_2450_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_snd_2438_, v___x_2449_);
if (lean_obj_tag(v___x_2450_) == 0)
{
v___y_2444_ = v_b_2442_;
goto v___jp_2443_;
}
else
{
lean_object* v_val_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; 
v_val_2451_ = lean_ctor_get(v___x_2450_, 0);
lean_inc(v_val_2451_);
lean_dec_ref(v___x_2450_);
lean_inc(v___x_2449_);
v___x_2452_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2452_, 0, v___x_2449_);
lean_ctor_set(v___x_2452_, 1, v_val_2451_);
v___x_2453_ = lean_array_push(v_b_2442_, v___x_2452_);
v___y_2444_ = v___x_2453_;
goto v___jp_2443_;
}
}
else
{
return v_b_2442_;
}
v___jp_2443_:
{
size_t v___x_2445_; size_t v___x_2446_; 
v___x_2445_ = ((size_t)1ULL);
v___x_2446_ = lean_usize_add(v_i_2440_, v___x_2445_);
v_i_2440_ = v___x_2446_;
v_b_2442_ = v___y_2444_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3_spec__4___redArg___boxed(lean_object* v_snd_2454_, lean_object* v_as_2455_, lean_object* v_i_2456_, lean_object* v_stop_2457_, lean_object* v_b_2458_){
_start:
{
size_t v_i_boxed_2459_; size_t v_stop_boxed_2460_; lean_object* v_res_2461_; 
v_i_boxed_2459_ = lean_unbox_usize(v_i_2456_);
lean_dec(v_i_2456_);
v_stop_boxed_2460_ = lean_unbox_usize(v_stop_2457_);
lean_dec(v_stop_2457_);
v_res_2461_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3_spec__4___redArg(v_snd_2454_, v_as_2455_, v_i_boxed_2459_, v_stop_boxed_2460_, v_b_2458_);
lean_dec_ref(v_as_2455_);
lean_dec(v_snd_2454_);
return v_res_2461_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3___redArg(lean_object* v_snd_2462_, lean_object* v_as_2463_, lean_object* v_start_2464_, lean_object* v_stop_2465_){
_start:
{
lean_object* v___x_2466_; uint8_t v___x_2467_; 
v___x_2466_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___lam__2___closed__0));
v___x_2467_ = lean_nat_dec_lt(v_start_2464_, v_stop_2465_);
if (v___x_2467_ == 0)
{
return v___x_2466_;
}
else
{
lean_object* v___x_2468_; uint8_t v___x_2469_; 
v___x_2468_ = lean_array_get_size(v_as_2463_);
v___x_2469_ = lean_nat_dec_le(v_stop_2465_, v___x_2468_);
if (v___x_2469_ == 0)
{
uint8_t v___x_2470_; 
v___x_2470_ = lean_nat_dec_lt(v_start_2464_, v___x_2468_);
if (v___x_2470_ == 0)
{
return v___x_2466_;
}
else
{
size_t v___x_2471_; size_t v___x_2472_; lean_object* v___x_2473_; 
v___x_2471_ = lean_usize_of_nat(v_start_2464_);
v___x_2472_ = lean_usize_of_nat(v___x_2468_);
v___x_2473_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3_spec__4___redArg(v_snd_2462_, v_as_2463_, v___x_2471_, v___x_2472_, v___x_2466_);
return v___x_2473_;
}
}
else
{
size_t v___x_2474_; size_t v___x_2475_; lean_object* v___x_2476_; 
v___x_2474_ = lean_usize_of_nat(v_start_2464_);
v___x_2475_ = lean_usize_of_nat(v_stop_2465_);
v___x_2476_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3_spec__4___redArg(v_snd_2462_, v_as_2463_, v___x_2474_, v___x_2475_, v___x_2466_);
return v___x_2476_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3___redArg___boxed(lean_object* v_snd_2477_, lean_object* v_as_2478_, lean_object* v_start_2479_, lean_object* v_stop_2480_){
_start:
{
lean_object* v_res_2481_; 
v_res_2481_ = l_Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3___redArg(v_snd_2477_, v_as_2478_, v_start_2479_, v_stop_2480_);
lean_dec(v_stop_2480_);
lean_dec(v_start_2479_);
lean_dec_ref(v_as_2478_);
lean_dec(v_snd_2477_);
return v_res_2481_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttribute_spec__0___redArg(lean_object* v_impl_2482_, lean_object* v_env_2483_, lean_object* v_as_2484_, size_t v_i_2485_, size_t v_stop_2486_, lean_object* v_b_2487_){
_start:
{
lean_object* v___y_2489_; uint8_t v___x_2493_; 
v___x_2493_ = lean_usize_dec_eq(v_i_2485_, v_stop_2486_);
if (v___x_2493_ == 0)
{
lean_object* v___x_2494_; lean_object* v_fst_2495_; lean_object* v_snd_2496_; lean_object* v_filterExport_2497_; lean_object* v___x_2498_; uint8_t v___x_2499_; 
v___x_2494_ = lean_array_uget_borrowed(v_as_2484_, v_i_2485_);
v_fst_2495_ = lean_ctor_get(v___x_2494_, 0);
v_snd_2496_ = lean_ctor_get(v___x_2494_, 1);
v_filterExport_2497_ = lean_ctor_get(v_impl_2482_, 3);
lean_inc_ref(v_filterExport_2497_);
lean_inc(v_snd_2496_);
lean_inc(v_fst_2495_);
lean_inc_ref(v_env_2483_);
v___x_2498_ = lean_apply_3(v_filterExport_2497_, v_env_2483_, v_fst_2495_, v_snd_2496_);
v___x_2499_ = lean_unbox(v___x_2498_);
if (v___x_2499_ == 0)
{
v___y_2489_ = v_b_2487_;
goto v___jp_2488_;
}
else
{
lean_object* v___x_2500_; 
lean_inc(v___x_2494_);
v___x_2500_ = lean_array_push(v_b_2487_, v___x_2494_);
v___y_2489_ = v___x_2500_;
goto v___jp_2488_;
}
}
else
{
lean_dec_ref(v_env_2483_);
lean_dec_ref(v_impl_2482_);
return v_b_2487_;
}
v___jp_2488_:
{
size_t v___x_2490_; size_t v___x_2491_; 
v___x_2490_ = ((size_t)1ULL);
v___x_2491_ = lean_usize_add(v_i_2485_, v___x_2490_);
v_i_2485_ = v___x_2491_;
v_b_2487_ = v___y_2489_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttribute_spec__0___redArg___boxed(lean_object* v_impl_2501_, lean_object* v_env_2502_, lean_object* v_as_2503_, lean_object* v_i_2504_, lean_object* v_stop_2505_, lean_object* v_b_2506_){
_start:
{
size_t v_i_boxed_2507_; size_t v_stop_boxed_2508_; lean_object* v_res_2509_; 
v_i_boxed_2507_ = lean_unbox_usize(v_i_2504_);
lean_dec(v_i_2504_);
v_stop_boxed_2508_ = lean_unbox_usize(v_stop_2505_);
lean_dec(v_stop_2505_);
v_res_2509_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttribute_spec__0___redArg(v_impl_2501_, v_env_2502_, v_as_2503_, v_i_boxed_2507_, v_stop_boxed_2508_, v_b_2506_);
lean_dec_ref(v_as_2503_);
return v_res_2509_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___lam__1(lean_object* v_impl_2510_, uint8_t v_preserveOrder_2511_, lean_object* v_env_2512_, lean_object* v_x_2513_){
_start:
{
lean_object* v___y_2515_; 
if (v_preserveOrder_2511_ == 0)
{
lean_object* v_snd_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; lean_object* v_r_2534_; lean_object* v___y_2536_; lean_object* v___y_2537_; lean_object* v___x_2539_; uint8_t v___x_2540_; 
v_snd_2531_ = lean_ctor_get(v_x_2513_, 1);
lean_inc(v_snd_2531_);
lean_dec_ref(v_x_2513_);
v___x_2532_ = lean_unsigned_to_nat(0u);
v___x_2533_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___lam__2___closed__0));
v_r_2534_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1_spec__1___redArg(v___x_2533_, v_snd_2531_);
lean_dec(v_snd_2531_);
v___x_2539_ = lean_array_get_size(v_r_2534_);
v___x_2540_ = lean_nat_dec_eq(v___x_2539_, v___x_2532_);
if (v___x_2540_ == 0)
{
lean_object* v___x_2541_; lean_object* v___x_2542_; lean_object* v___y_2544_; uint8_t v___x_2546_; 
v___x_2541_ = lean_unsigned_to_nat(1u);
v___x_2542_ = lean_nat_sub(v___x_2539_, v___x_2541_);
v___x_2546_ = lean_nat_dec_le(v___x_2532_, v___x_2542_);
if (v___x_2546_ == 0)
{
lean_inc(v___x_2542_);
v___y_2544_ = v___x_2542_;
goto v___jp_2543_;
}
else
{
v___y_2544_ = v___x_2532_;
goto v___jp_2543_;
}
v___jp_2543_:
{
uint8_t v___x_2545_; 
v___x_2545_ = lean_nat_dec_le(v___y_2544_, v___x_2542_);
if (v___x_2545_ == 0)
{
lean_dec(v___x_2542_);
lean_inc(v___y_2544_);
v___y_2536_ = v___y_2544_;
v___y_2537_ = v___y_2544_;
goto v___jp_2535_;
}
else
{
v___y_2536_ = v___y_2544_;
v___y_2537_ = v___x_2542_;
goto v___jp_2535_;
}
}
}
else
{
v___y_2515_ = v_r_2534_;
goto v___jp_2514_;
}
v___jp_2535_:
{
lean_object* v___x_2538_; 
v___x_2538_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2___redArg(v_r_2534_, v___y_2536_, v___y_2537_);
lean_dec(v___y_2537_);
v___y_2515_ = v___x_2538_;
goto v___jp_2514_;
}
}
else
{
lean_object* v_fst_2547_; lean_object* v_snd_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; 
v_fst_2547_ = lean_ctor_get(v_x_2513_, 0);
lean_inc(v_fst_2547_);
v_snd_2548_ = lean_ctor_get(v_x_2513_, 1);
lean_inc(v_snd_2548_);
lean_dec_ref(v_x_2513_);
v___x_2549_ = lean_array_mk(v_fst_2547_);
v___x_2550_ = l_Array_reverse___redArg(v___x_2549_);
v___x_2551_ = lean_unsigned_to_nat(0u);
v___x_2552_ = lean_array_get_size(v___x_2550_);
v___x_2553_ = l_Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3___redArg(v_snd_2548_, v___x_2550_, v___x_2551_, v___x_2552_);
lean_dec_ref(v___x_2550_);
lean_dec(v_snd_2548_);
v___y_2515_ = v___x_2553_;
goto v___jp_2514_;
}
v___jp_2514_:
{
lean_object* v___x_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; uint8_t v___x_2519_; 
v___x_2516_ = lean_unsigned_to_nat(0u);
v___x_2517_ = lean_array_get_size(v___y_2515_);
v___x_2518_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___lam__2___closed__0));
v___x_2519_ = lean_nat_dec_lt(v___x_2516_, v___x_2517_);
if (v___x_2519_ == 0)
{
lean_object* v___x_2520_; 
lean_dec_ref(v_env_2512_);
lean_dec_ref(v_impl_2510_);
v___x_2520_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2520_, 0, v___x_2518_);
lean_ctor_set(v___x_2520_, 1, v___x_2518_);
lean_ctor_set(v___x_2520_, 2, v___y_2515_);
return v___x_2520_;
}
else
{
uint8_t v___x_2521_; 
v___x_2521_ = lean_nat_dec_le(v___x_2517_, v___x_2517_);
if (v___x_2521_ == 0)
{
if (v___x_2519_ == 0)
{
lean_object* v___x_2522_; 
lean_dec_ref(v_env_2512_);
lean_dec_ref(v_impl_2510_);
v___x_2522_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2522_, 0, v___x_2518_);
lean_ctor_set(v___x_2522_, 1, v___x_2518_);
lean_ctor_set(v___x_2522_, 2, v___y_2515_);
return v___x_2522_;
}
else
{
size_t v___x_2523_; size_t v___x_2524_; lean_object* v___x_2525_; lean_object* v___x_2526_; 
v___x_2523_ = ((size_t)0ULL);
v___x_2524_ = lean_usize_of_nat(v___x_2517_);
v___x_2525_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttribute_spec__0___redArg(v_impl_2510_, v_env_2512_, v___y_2515_, v___x_2523_, v___x_2524_, v___x_2518_);
lean_inc_ref(v___x_2525_);
v___x_2526_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2526_, 0, v___x_2525_);
lean_ctor_set(v___x_2526_, 1, v___x_2525_);
lean_ctor_set(v___x_2526_, 2, v___y_2515_);
return v___x_2526_;
}
}
else
{
size_t v___x_2527_; size_t v___x_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; 
v___x_2527_ = ((size_t)0ULL);
v___x_2528_ = lean_usize_of_nat(v___x_2517_);
v___x_2529_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttribute_spec__0___redArg(v_impl_2510_, v_env_2512_, v___y_2515_, v___x_2527_, v___x_2528_, v___x_2518_);
lean_inc_ref(v___x_2529_);
v___x_2530_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2530_, 0, v___x_2529_);
lean_ctor_set(v___x_2530_, 1, v___x_2529_);
lean_ctor_set(v___x_2530_, 2, v___y_2515_);
return v___x_2530_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___lam__1___boxed(lean_object* v_impl_2554_, lean_object* v_preserveOrder_2555_, lean_object* v_env_2556_, lean_object* v_x_2557_){
_start:
{
uint8_t v_preserveOrder_boxed_2558_; lean_object* v_res_2559_; 
v_preserveOrder_boxed_2558_ = lean_unbox(v_preserveOrder_2555_);
v_res_2559_ = l_Lean_registerParametricAttribute___redArg___lam__1(v_impl_2554_, v_preserveOrder_boxed_2558_, v_env_2556_, v_x_2557_);
return v_res_2559_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___lam__2(lean_object* v_x_2569_){
_start:
{
lean_object* v_snd_2570_; lean_object* v___x_2572_; uint8_t v_isShared_2573_; uint8_t v_isSharedCheck_2584_; 
v_snd_2570_ = lean_ctor_get(v_x_2569_, 1);
v_isSharedCheck_2584_ = !lean_is_exclusive(v_x_2569_);
if (v_isSharedCheck_2584_ == 0)
{
lean_object* v_unused_2585_; 
v_unused_2585_ = lean_ctor_get(v_x_2569_, 0);
lean_dec(v_unused_2585_);
v___x_2572_ = v_x_2569_;
v_isShared_2573_ = v_isSharedCheck_2584_;
goto v_resetjp_2571_;
}
else
{
lean_inc(v_snd_2570_);
lean_dec(v_x_2569_);
v___x_2572_ = lean_box(0);
v_isShared_2573_ = v_isSharedCheck_2584_;
goto v_resetjp_2571_;
}
v_resetjp_2571_:
{
lean_object* v___x_2574_; lean_object* v___y_2576_; 
v___x_2574_ = ((lean_object*)(l_Lean_registerParametricAttribute___redArg___lam__2___closed__3));
if (lean_obj_tag(v_snd_2570_) == 0)
{
lean_object* v_size_2582_; 
v_size_2582_ = lean_ctor_get(v_snd_2570_, 0);
lean_inc(v_size_2582_);
lean_dec_ref(v_snd_2570_);
v___y_2576_ = v_size_2582_;
goto v___jp_2575_;
}
else
{
lean_object* v___x_2583_; 
v___x_2583_ = lean_unsigned_to_nat(0u);
v___y_2576_ = v___x_2583_;
goto v___jp_2575_;
}
v___jp_2575_:
{
lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2580_; 
v___x_2577_ = l_Nat_reprFast(v___y_2576_);
v___x_2578_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2578_, 0, v___x_2577_);
if (v_isShared_2573_ == 0)
{
lean_ctor_set_tag(v___x_2572_, 5);
lean_ctor_set(v___x_2572_, 1, v___x_2578_);
lean_ctor_set(v___x_2572_, 0, v___x_2574_);
v___x_2580_ = v___x_2572_;
goto v_reusejp_2579_;
}
else
{
lean_object* v_reuseFailAlloc_2581_; 
v_reuseFailAlloc_2581_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2581_, 0, v___x_2574_);
lean_ctor_set(v_reuseFailAlloc_2581_, 1, v___x_2578_);
v___x_2580_ = v_reuseFailAlloc_2581_;
goto v_reusejp_2579_;
}
v_reusejp_2579_:
{
return v___x_2580_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___lam__3(lean_object* v_x_2586_){
_start:
{
lean_object* v___x_2587_; 
v___x_2587_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___lam__2___closed__0));
return v___x_2587_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___lam__3___boxed(lean_object* v_x_2588_){
_start:
{
lean_object* v_res_2589_; 
v_res_2589_ = l_Lean_registerParametricAttribute___redArg___lam__3(v_x_2588_);
lean_dec_ref(v_x_2588_);
return v_res_2589_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___lam__4(lean_object* v___x_2590_, lean_object* v_x_2591_, lean_object* v___y_2592_){
_start:
{
lean_object* v___x_2594_; 
v___x_2594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2594_, 0, v___x_2590_);
return v___x_2594_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___lam__4___boxed(lean_object* v___x_2595_, lean_object* v_x_2596_, lean_object* v___y_2597_, lean_object* v___y_2598_){
_start:
{
lean_object* v_res_2599_; 
v_res_2599_ = l_Lean_registerParametricAttribute___redArg___lam__4(v___x_2595_, v_x_2596_, v___y_2597_);
lean_dec_ref(v___y_2597_);
lean_dec_ref(v_x_2596_);
return v_res_2599_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___lam__5(lean_object* v___x_2600_){
_start:
{
lean_object* v___x_2602_; 
v___x_2602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2602_, 0, v___x_2600_);
return v___x_2602_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___lam__5___boxed(lean_object* v___x_2603_, lean_object* v___y_2604_){
_start:
{
lean_object* v_res_2605_; 
v_res_2605_ = l_Lean_registerParametricAttribute___redArg___lam__5(v___x_2603_);
return v_res_2605_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___lam__7(lean_object* v_getParam_2606_, lean_object* v_a_2607_, lean_object* v_afterSet_2608_, lean_object* v_name_2609_, lean_object* v_decl_2610_, lean_object* v_stx_2611_, uint8_t v_kind_2612_, lean_object* v___y_2613_, lean_object* v___y_2614_){
_start:
{
lean_object* v___y_2617_; lean_object* v___y_2618_; lean_object* v___y_2619_; lean_object* v___y_2620_; uint8_t v___y_2621_; lean_object* v___y_2624_; lean_object* v___y_2625_; lean_object* v___y_2626_; uint8_t v___x_2669_; uint8_t v___x_2670_; 
v___x_2669_ = 0;
v___x_2670_ = l_Lean_instBEqAttributeKind_beq(v_kind_2612_, v___x_2669_);
if (v___x_2670_ == 0)
{
lean_object* v___x_2671_; 
lean_dec(v_stx_2611_);
lean_dec(v_decl_2610_);
lean_dec_ref(v_afterSet_2608_);
lean_dec_ref(v_a_2607_);
lean_dec_ref(v_getParam_2606_);
v___x_2671_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg(v_name_2609_, v_kind_2612_, v___y_2613_, v___y_2614_);
return v___x_2671_;
}
else
{
goto v___jp_2664_;
}
v___jp_2616_:
{
if (v___y_2621_ == 0)
{
lean_object* v___x_2622_; 
lean_dec_ref(v___y_2619_);
v___x_2622_ = l_Lean_setEnv___at___00Lean_registerParametricAttribute_spec__4___redArg(v___y_2617_, v___y_2620_);
return v___x_2622_;
}
else
{
lean_dec_ref(v___y_2617_);
return v___y_2619_;
}
}
v___jp_2623_:
{
lean_object* v___x_2627_; 
lean_inc(v___y_2626_);
lean_inc_ref(v___y_2625_);
lean_inc(v_decl_2610_);
v___x_2627_ = lean_apply_5(v_getParam_2606_, v_decl_2610_, v_stx_2611_, v___y_2625_, v___y_2626_, lean_box(0));
if (lean_obj_tag(v___x_2627_) == 0)
{
lean_object* v_a_2628_; lean_object* v___x_2629_; lean_object* v_toEnvExtension_2630_; lean_object* v_env_2631_; lean_object* v_nextMacroScope_2632_; lean_object* v_ngen_2633_; lean_object* v_auxDeclNGen_2634_; lean_object* v_traceState_2635_; lean_object* v_messages_2636_; lean_object* v_infoState_2637_; lean_object* v_snapshotTasks_2638_; lean_object* v___x_2640_; uint8_t v_isShared_2641_; uint8_t v_isSharedCheck_2654_; 
v_a_2628_ = lean_ctor_get(v___x_2627_, 0);
lean_inc(v_a_2628_);
lean_dec_ref(v___x_2627_);
v___x_2629_ = lean_st_ref_take(v___y_2626_);
v_toEnvExtension_2630_ = lean_ctor_get(v_a_2607_, 0);
v_env_2631_ = lean_ctor_get(v___x_2629_, 0);
v_nextMacroScope_2632_ = lean_ctor_get(v___x_2629_, 1);
v_ngen_2633_ = lean_ctor_get(v___x_2629_, 2);
v_auxDeclNGen_2634_ = lean_ctor_get(v___x_2629_, 3);
v_traceState_2635_ = lean_ctor_get(v___x_2629_, 4);
v_messages_2636_ = lean_ctor_get(v___x_2629_, 6);
v_infoState_2637_ = lean_ctor_get(v___x_2629_, 7);
v_snapshotTasks_2638_ = lean_ctor_get(v___x_2629_, 8);
v_isSharedCheck_2654_ = !lean_is_exclusive(v___x_2629_);
if (v_isSharedCheck_2654_ == 0)
{
lean_object* v_unused_2655_; 
v_unused_2655_ = lean_ctor_get(v___x_2629_, 5);
lean_dec(v_unused_2655_);
v___x_2640_ = v___x_2629_;
v_isShared_2641_ = v_isSharedCheck_2654_;
goto v_resetjp_2639_;
}
else
{
lean_inc(v_snapshotTasks_2638_);
lean_inc(v_infoState_2637_);
lean_inc(v_messages_2636_);
lean_inc(v_traceState_2635_);
lean_inc(v_auxDeclNGen_2634_);
lean_inc(v_ngen_2633_);
lean_inc(v_nextMacroScope_2632_);
lean_inc(v_env_2631_);
lean_dec(v___x_2629_);
v___x_2640_ = lean_box(0);
v_isShared_2641_ = v_isSharedCheck_2654_;
goto v_resetjp_2639_;
}
v_resetjp_2639_:
{
lean_object* v_asyncMode_2642_; lean_object* v___x_2643_; lean_object* v___x_2644_; lean_object* v___x_2645_; lean_object* v___x_2647_; 
v_asyncMode_2642_ = lean_ctor_get(v_toEnvExtension_2630_, 2);
lean_inc(v_asyncMode_2642_);
lean_inc(v_a_2628_);
lean_inc_n(v_decl_2610_, 2);
v___x_2643_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2643_, 0, v_decl_2610_);
lean_ctor_set(v___x_2643_, 1, v_a_2628_);
v___x_2644_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_a_2607_, v_env_2631_, v___x_2643_, v_asyncMode_2642_, v_decl_2610_);
lean_dec(v_asyncMode_2642_);
v___x_2645_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2);
if (v_isShared_2641_ == 0)
{
lean_ctor_set(v___x_2640_, 5, v___x_2645_);
lean_ctor_set(v___x_2640_, 0, v___x_2644_);
v___x_2647_ = v___x_2640_;
goto v_reusejp_2646_;
}
else
{
lean_object* v_reuseFailAlloc_2653_; 
v_reuseFailAlloc_2653_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2653_, 0, v___x_2644_);
lean_ctor_set(v_reuseFailAlloc_2653_, 1, v_nextMacroScope_2632_);
lean_ctor_set(v_reuseFailAlloc_2653_, 2, v_ngen_2633_);
lean_ctor_set(v_reuseFailAlloc_2653_, 3, v_auxDeclNGen_2634_);
lean_ctor_set(v_reuseFailAlloc_2653_, 4, v_traceState_2635_);
lean_ctor_set(v_reuseFailAlloc_2653_, 5, v___x_2645_);
lean_ctor_set(v_reuseFailAlloc_2653_, 6, v_messages_2636_);
lean_ctor_set(v_reuseFailAlloc_2653_, 7, v_infoState_2637_);
lean_ctor_set(v_reuseFailAlloc_2653_, 8, v_snapshotTasks_2638_);
v___x_2647_ = v_reuseFailAlloc_2653_;
goto v_reusejp_2646_;
}
v_reusejp_2646_:
{
lean_object* v___x_2648_; lean_object* v___x_2649_; 
v___x_2648_ = lean_st_ref_set(v___y_2626_, v___x_2647_);
lean_inc(v___y_2626_);
lean_inc_ref(v___y_2625_);
v___x_2649_ = lean_apply_5(v_afterSet_2608_, v_decl_2610_, v_a_2628_, v___y_2625_, v___y_2626_, lean_box(0));
if (lean_obj_tag(v___x_2649_) == 0)
{
lean_dec_ref(v___y_2624_);
return v___x_2649_;
}
else
{
lean_object* v_a_2650_; uint8_t v___x_2651_; 
v_a_2650_ = lean_ctor_get(v___x_2649_, 0);
lean_inc(v_a_2650_);
v___x_2651_ = l_Lean_Exception_isInterrupt(v_a_2650_);
if (v___x_2651_ == 0)
{
uint8_t v___x_2652_; 
v___x_2652_ = l_Lean_Exception_isRuntime(v_a_2650_);
v___y_2617_ = v___y_2624_;
v___y_2618_ = v___y_2625_;
v___y_2619_ = v___x_2649_;
v___y_2620_ = v___y_2626_;
v___y_2621_ = v___x_2652_;
goto v___jp_2616_;
}
else
{
lean_dec(v_a_2650_);
v___y_2617_ = v___y_2624_;
v___y_2618_ = v___y_2625_;
v___y_2619_ = v___x_2649_;
v___y_2620_ = v___y_2626_;
v___y_2621_ = v___x_2651_;
goto v___jp_2616_;
}
}
}
}
}
else
{
lean_object* v_a_2656_; lean_object* v___x_2658_; uint8_t v_isShared_2659_; uint8_t v_isSharedCheck_2663_; 
lean_dec_ref(v___y_2624_);
lean_dec(v_decl_2610_);
lean_dec_ref(v_afterSet_2608_);
lean_dec_ref(v_a_2607_);
v_a_2656_ = lean_ctor_get(v___x_2627_, 0);
v_isSharedCheck_2663_ = !lean_is_exclusive(v___x_2627_);
if (v_isSharedCheck_2663_ == 0)
{
v___x_2658_ = v___x_2627_;
v_isShared_2659_ = v_isSharedCheck_2663_;
goto v_resetjp_2657_;
}
else
{
lean_inc(v_a_2656_);
lean_dec(v___x_2627_);
v___x_2658_ = lean_box(0);
v_isShared_2659_ = v_isSharedCheck_2663_;
goto v_resetjp_2657_;
}
v_resetjp_2657_:
{
lean_object* v___x_2661_; 
if (v_isShared_2659_ == 0)
{
v___x_2661_ = v___x_2658_;
goto v_reusejp_2660_;
}
else
{
lean_object* v_reuseFailAlloc_2662_; 
v_reuseFailAlloc_2662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2662_, 0, v_a_2656_);
v___x_2661_ = v_reuseFailAlloc_2662_;
goto v_reusejp_2660_;
}
v_reusejp_2660_:
{
return v___x_2661_;
}
}
}
}
v___jp_2664_:
{
lean_object* v___x_2665_; lean_object* v_env_2666_; lean_object* v___x_2667_; 
v___x_2665_ = lean_st_ref_get(v___y_2614_);
v_env_2666_ = lean_ctor_get(v___x_2665_, 0);
lean_inc_ref(v_env_2666_);
lean_dec(v___x_2665_);
v___x_2667_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2666_, v_decl_2610_);
if (lean_obj_tag(v___x_2667_) == 0)
{
lean_dec(v_name_2609_);
v___y_2624_ = v_env_2666_;
v___y_2625_ = v___y_2613_;
v___y_2626_ = v___y_2614_;
goto v___jp_2623_;
}
else
{
lean_object* v___x_2668_; 
lean_dec_ref(v___x_2667_);
lean_dec_ref(v_env_2666_);
lean_dec(v_stx_2611_);
lean_dec_ref(v_afterSet_2608_);
lean_dec_ref(v_a_2607_);
lean_dec_ref(v_getParam_2606_);
v___x_2668_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg(v_name_2609_, v_decl_2610_, v___y_2613_, v___y_2614_);
return v___x_2668_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___lam__7___boxed(lean_object* v_getParam_2672_, lean_object* v_a_2673_, lean_object* v_afterSet_2674_, lean_object* v_name_2675_, lean_object* v_decl_2676_, lean_object* v_stx_2677_, lean_object* v_kind_2678_, lean_object* v___y_2679_, lean_object* v___y_2680_, lean_object* v___y_2681_){
_start:
{
uint8_t v_kind_boxed_2682_; lean_object* v_res_2683_; 
v_kind_boxed_2682_ = lean_unbox(v_kind_2678_);
v_res_2683_ = l_Lean_registerParametricAttribute___redArg___lam__7(v_getParam_2672_, v_a_2673_, v_afterSet_2674_, v_name_2675_, v_decl_2676_, v_stx_2677_, v_kind_boxed_2682_, v___y_2679_, v___y_2680_);
lean_dec(v___y_2680_);
lean_dec_ref(v___y_2679_);
return v_res_2683_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg(lean_object* v_impl_2694_){
_start:
{
lean_object* v_toAttributeImplCore_2696_; lean_object* v_getParam_2697_; lean_object* v_afterSet_2698_; uint8_t v_preserveOrder_2699_; lean_object* v_ref_2700_; lean_object* v_name_2701_; lean_object* v___f_2702_; lean_object* v___x_2703_; lean_object* v___f_2704_; lean_object* v___f_2705_; lean_object* v___f_2706_; lean_object* v___f_2707_; lean_object* v___f_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; lean_object* v___x_2711_; lean_object* v___x_2712_; lean_object* v___x_2713_; 
v_toAttributeImplCore_2696_ = lean_ctor_get(v_impl_2694_, 0);
lean_inc_ref(v_toAttributeImplCore_2696_);
v_getParam_2697_ = lean_ctor_get(v_impl_2694_, 1);
lean_inc_ref(v_getParam_2697_);
v_afterSet_2698_ = lean_ctor_get(v_impl_2694_, 2);
lean_inc_ref(v_afterSet_2698_);
v_preserveOrder_2699_ = lean_ctor_get_uint8(v_impl_2694_, sizeof(void*)*4);
v_ref_2700_ = lean_ctor_get(v_toAttributeImplCore_2696_, 0);
v_name_2701_ = lean_ctor_get(v_toAttributeImplCore_2696_, 1);
v___f_2702_ = ((lean_object*)(l_Lean_registerParametricAttribute___redArg___closed__0));
v___x_2703_ = lean_box(v_preserveOrder_2699_);
v___f_2704_ = lean_alloc_closure((void*)(l_Lean_registerParametricAttribute___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_2704_, 0, v_impl_2694_);
lean_closure_set(v___f_2704_, 1, v___x_2703_);
v___f_2705_ = ((lean_object*)(l_Lean_registerParametricAttribute___redArg___closed__1));
v___f_2706_ = ((lean_object*)(l_Lean_registerParametricAttribute___redArg___closed__2));
v___f_2707_ = ((lean_object*)(l_Lean_registerParametricAttribute___redArg___closed__4));
v___f_2708_ = ((lean_object*)(l_Lean_registerParametricAttribute___redArg___closed__5));
v___x_2709_ = lean_box(2);
v___x_2710_ = lean_box(0);
lean_inc(v_ref_2700_);
v___x_2711_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_2711_, 0, v_ref_2700_);
lean_ctor_set(v___x_2711_, 1, v___f_2708_);
lean_ctor_set(v___x_2711_, 2, v___f_2707_);
lean_ctor_set(v___x_2711_, 3, v___f_2702_);
lean_ctor_set(v___x_2711_, 4, v___f_2704_);
lean_ctor_set(v___x_2711_, 5, v___f_2705_);
lean_ctor_set(v___x_2711_, 6, v___x_2709_);
lean_ctor_set(v___x_2711_, 7, v___x_2710_);
v___x_2712_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2712_, 0, v___x_2711_);
lean_ctor_set(v___x_2712_, 1, v___f_2706_);
v___x_2713_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_2712_);
if (lean_obj_tag(v___x_2713_) == 0)
{
lean_object* v_a_2714_; lean_object* v___f_2715_; lean_object* v___f_2716_; lean_object* v___x_2717_; lean_object* v___x_2718_; 
v_a_2714_ = lean_ctor_get(v___x_2713_, 0);
lean_inc_n(v_a_2714_, 2);
lean_dec_ref(v___x_2713_);
lean_inc_n(v_name_2701_, 2);
v___f_2715_ = lean_alloc_closure((void*)(l_Lean_registerTagAttribute___lam__6___boxed), 5, 1);
lean_closure_set(v___f_2715_, 0, v_name_2701_);
v___f_2716_ = lean_alloc_closure((void*)(l_Lean_registerParametricAttribute___redArg___lam__7___boxed), 10, 4);
lean_closure_set(v___f_2716_, 0, v_getParam_2697_);
lean_closure_set(v___f_2716_, 1, v_a_2714_);
lean_closure_set(v___f_2716_, 2, v_afterSet_2698_);
lean_closure_set(v___f_2716_, 3, v_name_2701_);
v___x_2717_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2717_, 0, v_toAttributeImplCore_2696_);
lean_ctor_set(v___x_2717_, 1, v___f_2716_);
lean_ctor_set(v___x_2717_, 2, v___f_2715_);
lean_inc_ref(v___x_2717_);
v___x_2718_ = l_Lean_registerBuiltinAttribute(v___x_2717_);
if (lean_obj_tag(v___x_2718_) == 0)
{
lean_object* v___x_2720_; uint8_t v_isShared_2721_; uint8_t v_isSharedCheck_2726_; 
v_isSharedCheck_2726_ = !lean_is_exclusive(v___x_2718_);
if (v_isSharedCheck_2726_ == 0)
{
lean_object* v_unused_2727_; 
v_unused_2727_ = lean_ctor_get(v___x_2718_, 0);
lean_dec(v_unused_2727_);
v___x_2720_ = v___x_2718_;
v_isShared_2721_ = v_isSharedCheck_2726_;
goto v_resetjp_2719_;
}
else
{
lean_dec(v___x_2718_);
v___x_2720_ = lean_box(0);
v_isShared_2721_ = v_isSharedCheck_2726_;
goto v_resetjp_2719_;
}
v_resetjp_2719_:
{
lean_object* v___x_2722_; lean_object* v___x_2724_; 
v___x_2722_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2722_, 0, v___x_2717_);
lean_ctor_set(v___x_2722_, 1, v_a_2714_);
lean_ctor_set_uint8(v___x_2722_, sizeof(void*)*2, v_preserveOrder_2699_);
if (v_isShared_2721_ == 0)
{
lean_ctor_set(v___x_2720_, 0, v___x_2722_);
v___x_2724_ = v___x_2720_;
goto v_reusejp_2723_;
}
else
{
lean_object* v_reuseFailAlloc_2725_; 
v_reuseFailAlloc_2725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2725_, 0, v___x_2722_);
v___x_2724_ = v_reuseFailAlloc_2725_;
goto v_reusejp_2723_;
}
v_reusejp_2723_:
{
return v___x_2724_;
}
}
}
else
{
lean_object* v_a_2728_; lean_object* v___x_2730_; uint8_t v_isShared_2731_; uint8_t v_isSharedCheck_2735_; 
lean_dec_ref(v___x_2717_);
lean_dec(v_a_2714_);
v_a_2728_ = lean_ctor_get(v___x_2718_, 0);
v_isSharedCheck_2735_ = !lean_is_exclusive(v___x_2718_);
if (v_isSharedCheck_2735_ == 0)
{
v___x_2730_ = v___x_2718_;
v_isShared_2731_ = v_isSharedCheck_2735_;
goto v_resetjp_2729_;
}
else
{
lean_inc(v_a_2728_);
lean_dec(v___x_2718_);
v___x_2730_ = lean_box(0);
v_isShared_2731_ = v_isSharedCheck_2735_;
goto v_resetjp_2729_;
}
v_resetjp_2729_:
{
lean_object* v___x_2733_; 
if (v_isShared_2731_ == 0)
{
v___x_2733_ = v___x_2730_;
goto v_reusejp_2732_;
}
else
{
lean_object* v_reuseFailAlloc_2734_; 
v_reuseFailAlloc_2734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2734_, 0, v_a_2728_);
v___x_2733_ = v_reuseFailAlloc_2734_;
goto v_reusejp_2732_;
}
v_reusejp_2732_:
{
return v___x_2733_;
}
}
}
}
else
{
lean_object* v_a_2736_; lean_object* v___x_2738_; uint8_t v_isShared_2739_; uint8_t v_isSharedCheck_2743_; 
lean_dec_ref(v_afterSet_2698_);
lean_dec_ref(v_getParam_2697_);
lean_dec_ref(v_toAttributeImplCore_2696_);
v_a_2736_ = lean_ctor_get(v___x_2713_, 0);
v_isSharedCheck_2743_ = !lean_is_exclusive(v___x_2713_);
if (v_isSharedCheck_2743_ == 0)
{
v___x_2738_ = v___x_2713_;
v_isShared_2739_ = v_isSharedCheck_2743_;
goto v_resetjp_2737_;
}
else
{
lean_inc(v_a_2736_);
lean_dec(v___x_2713_);
v___x_2738_ = lean_box(0);
v_isShared_2739_ = v_isSharedCheck_2743_;
goto v_resetjp_2737_;
}
v_resetjp_2737_:
{
lean_object* v___x_2741_; 
if (v_isShared_2739_ == 0)
{
v___x_2741_ = v___x_2738_;
goto v_reusejp_2740_;
}
else
{
lean_object* v_reuseFailAlloc_2742_; 
v_reuseFailAlloc_2742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2742_, 0, v_a_2736_);
v___x_2741_ = v_reuseFailAlloc_2742_;
goto v_reusejp_2740_;
}
v_reusejp_2740_:
{
return v___x_2741_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___boxed(lean_object* v_impl_2744_, lean_object* v_a_2745_){
_start:
{
lean_object* v_res_2746_; 
v_res_2746_ = l_Lean_registerParametricAttribute___redArg(v_impl_2744_);
return v_res_2746_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute(lean_object* v_00_u03b1_2747_, lean_object* v_impl_2748_){
_start:
{
lean_object* v___x_2750_; 
v___x_2750_ = l_Lean_registerParametricAttribute___redArg(v_impl_2748_);
return v___x_2750_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___boxed(lean_object* v_00_u03b1_2751_, lean_object* v_impl_2752_, lean_object* v_a_2753_){
_start:
{
lean_object* v_res_2754_; 
v_res_2754_ = l_Lean_registerParametricAttribute(v_00_u03b1_2751_, v_impl_2752_);
return v_res_2754_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttribute_spec__0(lean_object* v_00_u03b1_2755_, lean_object* v_impl_2756_, lean_object* v_env_2757_, lean_object* v_as_2758_, size_t v_i_2759_, size_t v_stop_2760_, lean_object* v_b_2761_){
_start:
{
lean_object* v___x_2762_; 
v___x_2762_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttribute_spec__0___redArg(v_impl_2756_, v_env_2757_, v_as_2758_, v_i_2759_, v_stop_2760_, v_b_2761_);
return v___x_2762_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttribute_spec__0___boxed(lean_object* v_00_u03b1_2763_, lean_object* v_impl_2764_, lean_object* v_env_2765_, lean_object* v_as_2766_, lean_object* v_i_2767_, lean_object* v_stop_2768_, lean_object* v_b_2769_){
_start:
{
size_t v_i_boxed_2770_; size_t v_stop_boxed_2771_; lean_object* v_res_2772_; 
v_i_boxed_2770_ = lean_unbox_usize(v_i_2767_);
lean_dec(v_i_2767_);
v_stop_boxed_2771_ = lean_unbox_usize(v_stop_2768_);
lean_dec(v_stop_2768_);
v_res_2772_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttribute_spec__0(v_00_u03b1_2763_, v_impl_2764_, v_env_2765_, v_as_2766_, v_i_boxed_2770_, v_stop_boxed_2771_, v_b_2769_);
lean_dec_ref(v_as_2766_);
return v_res_2772_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1___redArg(lean_object* v_init_2773_, lean_object* v_t_2774_){
_start:
{
lean_object* v___x_2775_; 
v___x_2775_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1_spec__1___redArg(v_init_2773_, v_t_2774_);
return v___x_2775_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1___redArg___boxed(lean_object* v_init_2776_, lean_object* v_t_2777_){
_start:
{
lean_object* v_res_2778_; 
v_res_2778_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1___redArg(v_init_2776_, v_t_2777_);
lean_dec(v_t_2777_);
return v_res_2778_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1(lean_object* v_00_u03b1_2779_, lean_object* v_init_2780_, lean_object* v_t_2781_){
_start:
{
lean_object* v___x_2782_; 
v___x_2782_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1_spec__1___redArg(v_init_2780_, v_t_2781_);
return v___x_2782_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1___boxed(lean_object* v_00_u03b1_2783_, lean_object* v_init_2784_, lean_object* v_t_2785_){
_start:
{
lean_object* v_res_2786_; 
v_res_2786_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1(v_00_u03b1_2783_, v_init_2784_, v_t_2785_);
lean_dec(v_t_2785_);
return v_res_2786_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2(lean_object* v_00_u03b1_2787_, lean_object* v_n_2788_, lean_object* v_as_2789_, lean_object* v_lo_2790_, lean_object* v_hi_2791_, lean_object* v_w_2792_, lean_object* v_hlo_2793_, lean_object* v_hhi_2794_){
_start:
{
lean_object* v___x_2795_; 
v___x_2795_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2___redArg(v_as_2789_, v_lo_2790_, v_hi_2791_);
return v___x_2795_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2___boxed(lean_object* v_00_u03b1_2796_, lean_object* v_n_2797_, lean_object* v_as_2798_, lean_object* v_lo_2799_, lean_object* v_hi_2800_, lean_object* v_w_2801_, lean_object* v_hlo_2802_, lean_object* v_hhi_2803_){
_start:
{
lean_object* v_res_2804_; 
v_res_2804_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2(v_00_u03b1_2796_, v_n_2797_, v_as_2798_, v_lo_2799_, v_hi_2800_, v_w_2801_, v_hlo_2802_, v_hhi_2803_);
lean_dec(v_hi_2800_);
lean_dec(v_n_2797_);
return v_res_2804_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3(lean_object* v_00_u03b1_2805_, lean_object* v_snd_2806_, lean_object* v_as_2807_, lean_object* v_start_2808_, lean_object* v_stop_2809_){
_start:
{
lean_object* v___x_2810_; 
v___x_2810_ = l_Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3___redArg(v_snd_2806_, v_as_2807_, v_start_2808_, v_stop_2809_);
return v___x_2810_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3___boxed(lean_object* v_00_u03b1_2811_, lean_object* v_snd_2812_, lean_object* v_as_2813_, lean_object* v_start_2814_, lean_object* v_stop_2815_){
_start:
{
lean_object* v_res_2816_; 
v_res_2816_ = l_Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3(v_00_u03b1_2811_, v_snd_2812_, v_as_2813_, v_start_2814_, v_stop_2815_);
lean_dec(v_stop_2815_);
lean_dec(v_start_2814_);
lean_dec_ref(v_as_2813_);
lean_dec(v_snd_2812_);
return v_res_2816_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1_spec__1(lean_object* v_00_u03b1_2817_, lean_object* v_init_2818_, lean_object* v_x_2819_){
_start:
{
lean_object* v___x_2820_; 
v___x_2820_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1_spec__1___redArg(v_init_2818_, v_x_2819_);
return v___x_2820_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1_spec__1___boxed(lean_object* v_00_u03b1_2821_, lean_object* v_init_2822_, lean_object* v_x_2823_){
_start:
{
lean_object* v_res_2824_; 
v_res_2824_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1_spec__1(v_00_u03b1_2821_, v_init_2822_, v_x_2823_);
lean_dec(v_x_2823_);
return v_res_2824_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3_spec__4(lean_object* v_00_u03b1_2825_, lean_object* v_snd_2826_, lean_object* v_as_2827_, size_t v_i_2828_, size_t v_stop_2829_, lean_object* v_b_2830_){
_start:
{
lean_object* v___x_2831_; 
v___x_2831_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3_spec__4___redArg(v_snd_2826_, v_as_2827_, v_i_2828_, v_stop_2829_, v_b_2830_);
return v___x_2831_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3_spec__4___boxed(lean_object* v_00_u03b1_2832_, lean_object* v_snd_2833_, lean_object* v_as_2834_, lean_object* v_i_2835_, lean_object* v_stop_2836_, lean_object* v_b_2837_){
_start:
{
size_t v_i_boxed_2838_; size_t v_stop_boxed_2839_; lean_object* v_res_2840_; 
v_i_boxed_2838_ = lean_unbox_usize(v_i_2835_);
lean_dec(v_i_2835_);
v_stop_boxed_2839_ = lean_unbox_usize(v_stop_2836_);
lean_dec(v_stop_2836_);
v_res_2840_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3_spec__4(v_00_u03b1_2832_, v_snd_2833_, v_as_2834_, v_i_boxed_2838_, v_stop_boxed_2839_, v_b_2837_);
lean_dec_ref(v_as_2834_);
lean_dec(v_snd_2833_);
return v_res_2840_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParam_x3f___redArg___lam__1(lean_object* v_decl_2841_, lean_object* v___x_2842_, lean_object* v___x_2843_, lean_object* v_a_2844_, lean_object* v_x_2845_, lean_object* v___y_2846_){
_start:
{
lean_object* v_fst_2847_; uint8_t v___x_2848_; 
v_fst_2847_ = lean_ctor_get(v_a_2844_, 0);
v___x_2848_ = lean_name_eq(v_fst_2847_, v_decl_2841_);
if (v___x_2848_ == 0)
{
lean_object* v___x_2849_; 
lean_dec_ref(v_a_2844_);
v___x_2849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2849_, 0, v___x_2842_);
return v___x_2849_;
}
else
{
lean_object* v___x_2850_; lean_object* v___x_2851_; lean_object* v___x_2852_; lean_object* v___x_2853_; 
lean_dec_ref(v___x_2842_);
v___x_2850_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2850_, 0, v_a_2844_);
v___x_2851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2851_, 0, v___x_2850_);
v___x_2852_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2852_, 0, v___x_2851_);
lean_ctor_set(v___x_2852_, 1, v___x_2843_);
v___x_2853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2853_, 0, v___x_2852_);
return v___x_2853_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParam_x3f___redArg___lam__1___boxed(lean_object* v_decl_2854_, lean_object* v___x_2855_, lean_object* v___x_2856_, lean_object* v_a_2857_, lean_object* v_x_2858_, lean_object* v___y_2859_){
_start:
{
lean_object* v_res_2860_; 
v_res_2860_ = l_Lean_ParametricAttribute_getParam_x3f___redArg___lam__1(v_decl_2854_, v___x_2855_, v___x_2856_, v_a_2857_, v_x_2858_, v___y_2859_);
lean_dec_ref(v___y_2859_);
lean_dec(v_decl_2854_);
return v_res_2860_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParam_x3f___redArg(lean_object* v_inst_2887_, lean_object* v_attr_2888_, lean_object* v_env_2889_, lean_object* v_decl_2890_){
_start:
{
lean_object* v___y_2892_; lean_object* v___x_2903_; lean_object* v___x_2904_; 
v___x_2903_ = ((lean_object*)(l_Lean_ParametricAttribute_getParam_x3f___redArg___closed__0));
v___x_2904_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2889_, v_decl_2890_);
if (lean_obj_tag(v___x_2904_) == 0)
{
lean_object* v_ext_2905_; lean_object* v_toEnvExtension_2906_; lean_object* v_asyncMode_2907_; lean_object* v___x_2908_; lean_object* v___x_2909_; lean_object* v_snd_2910_; lean_object* v___x_2911_; 
lean_dec(v_inst_2887_);
v_ext_2905_ = lean_ctor_get(v_attr_2888_, 1);
v_toEnvExtension_2906_ = lean_ctor_get(v_ext_2905_, 0);
v_asyncMode_2907_ = lean_ctor_get(v_toEnvExtension_2906_, 2);
v___x_2908_ = lean_box(0);
v___x_2909_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2903_, v_ext_2905_, v_env_2889_, v_asyncMode_2907_, v___x_2908_);
v_snd_2910_ = lean_ctor_get(v___x_2909_, 1);
lean_inc(v_snd_2910_);
lean_dec(v___x_2909_);
v___x_2911_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_snd_2910_, v_decl_2890_);
lean_dec(v_decl_2890_);
lean_dec(v_snd_2910_);
return v___x_2911_;
}
else
{
uint8_t v_preserveOrder_2912_; 
v_preserveOrder_2912_ = lean_ctor_get_uint8(v_attr_2888_, sizeof(void*)*2);
if (v_preserveOrder_2912_ == 0)
{
lean_object* v_val_2913_; lean_object* v_ext_2914_; uint8_t v___x_2915_; lean_object* v___x_2916_; lean_object* v___x_2917_; lean_object* v___x_2918_; uint8_t v___x_2919_; 
v_val_2913_ = lean_ctor_get(v___x_2904_, 0);
lean_inc(v_val_2913_);
lean_dec_ref(v___x_2904_);
v_ext_2914_ = lean_ctor_get(v_attr_2888_, 1);
v___x_2915_ = 0;
v___x_2916_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_2903_, v_ext_2914_, v_env_2889_, v_val_2913_, v___x_2915_);
lean_dec(v_val_2913_);
lean_dec_ref(v_env_2889_);
v___x_2917_ = lean_unsigned_to_nat(0u);
v___x_2918_ = lean_array_get_size(v___x_2916_);
v___x_2919_ = lean_nat_dec_lt(v___x_2917_, v___x_2918_);
if (v___x_2919_ == 0)
{
lean_object* v___x_2920_; 
lean_dec_ref(v___x_2916_);
lean_dec(v_decl_2890_);
lean_dec(v_inst_2887_);
v___x_2920_ = lean_box(0);
return v___x_2920_;
}
else
{
lean_object* v___x_2921_; lean_object* v___x_2922_; uint8_t v___x_2923_; 
v___x_2921_ = lean_unsigned_to_nat(1u);
v___x_2922_ = lean_nat_sub(v___x_2918_, v___x_2921_);
v___x_2923_ = lean_nat_dec_le(v___x_2917_, v___x_2922_);
if (v___x_2923_ == 0)
{
lean_object* v___x_2924_; 
lean_dec(v___x_2922_);
lean_dec_ref(v___x_2916_);
lean_dec(v_decl_2890_);
lean_dec(v_inst_2887_);
v___x_2924_ = lean_box(0);
return v___x_2924_;
}
else
{
lean_object* v___f_2925_; lean_object* v___x_2926_; lean_object* v___x_2927_; lean_object* v___x_2928_; 
v___f_2925_ = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2___redArg___closed__0));
v___x_2926_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2926_, 0, v_decl_2890_);
lean_ctor_set(v___x_2926_, 1, v_inst_2887_);
v___x_2927_ = ((lean_object*)(l_Lean_ParametricAttribute_getParam_x3f___redArg___closed__1));
v___x_2928_ = l_Array_binSearchAux___redArg(v___f_2925_, v___x_2927_, v___x_2916_, v___x_2926_, v___x_2917_, v___x_2922_);
lean_dec_ref(v___x_2916_);
v___y_2892_ = v___x_2928_;
goto v___jp_2891_;
}
}
}
else
{
lean_object* v_val_2929_; lean_object* v_ext_2930_; uint8_t v___x_2931_; lean_object* v___x_2932_; lean_object* v___x_2933_; lean_object* v___x_2934_; lean_object* v___x_2935_; lean_object* v___x_2936_; lean_object* v___f_2937_; size_t v_sz_2938_; size_t v___x_2939_; lean_object* v___x_2940_; lean_object* v_fst_2941_; 
lean_dec(v_inst_2887_);
v_val_2929_ = lean_ctor_get(v___x_2904_, 0);
lean_inc(v_val_2929_);
lean_dec_ref(v___x_2904_);
v_ext_2930_ = lean_ctor_get(v_attr_2888_, 1);
v___x_2931_ = 0;
v___x_2932_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_2903_, v_ext_2930_, v_env_2889_, v_val_2929_, v___x_2931_);
lean_dec(v_val_2929_);
lean_dec_ref(v_env_2889_);
v___x_2933_ = ((lean_object*)(l_Lean_ParametricAttribute_getParam_x3f___redArg___closed__11));
v___x_2934_ = lean_box(0);
v___x_2935_ = lean_box(0);
v___x_2936_ = ((lean_object*)(l_Lean_ParametricAttribute_getParam_x3f___redArg___closed__12));
v___f_2937_ = lean_alloc_closure((void*)(l_Lean_ParametricAttribute_getParam_x3f___redArg___lam__1___boxed), 6, 3);
lean_closure_set(v___f_2937_, 0, v_decl_2890_);
lean_closure_set(v___f_2937_, 1, v___x_2936_);
lean_closure_set(v___f_2937_, 2, v___x_2935_);
v_sz_2938_ = lean_array_size(v___x_2932_);
v___x_2939_ = ((size_t)0ULL);
v___x_2940_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_2933_, v___x_2932_, v___f_2937_, v_sz_2938_, v___x_2939_, v___x_2936_);
v_fst_2941_ = lean_ctor_get(v___x_2940_, 0);
lean_inc(v_fst_2941_);
lean_dec(v___x_2940_);
if (lean_obj_tag(v_fst_2941_) == 0)
{
return v___x_2934_;
}
else
{
lean_object* v_val_2942_; 
v_val_2942_ = lean_ctor_get(v_fst_2941_, 0);
lean_inc(v_val_2942_);
lean_dec_ref(v_fst_2941_);
v___y_2892_ = v_val_2942_;
goto v___jp_2891_;
}
}
}
v___jp_2891_:
{
if (lean_obj_tag(v___y_2892_) == 0)
{
lean_object* v___x_2893_; 
v___x_2893_ = lean_box(0);
return v___x_2893_;
}
else
{
lean_object* v_val_2894_; lean_object* v___x_2896_; uint8_t v_isShared_2897_; uint8_t v_isSharedCheck_2902_; 
v_val_2894_ = lean_ctor_get(v___y_2892_, 0);
v_isSharedCheck_2902_ = !lean_is_exclusive(v___y_2892_);
if (v_isSharedCheck_2902_ == 0)
{
v___x_2896_ = v___y_2892_;
v_isShared_2897_ = v_isSharedCheck_2902_;
goto v_resetjp_2895_;
}
else
{
lean_inc(v_val_2894_);
lean_dec(v___y_2892_);
v___x_2896_ = lean_box(0);
v_isShared_2897_ = v_isSharedCheck_2902_;
goto v_resetjp_2895_;
}
v_resetjp_2895_:
{
lean_object* v_snd_2898_; lean_object* v___x_2900_; 
v_snd_2898_ = lean_ctor_get(v_val_2894_, 1);
lean_inc(v_snd_2898_);
lean_dec(v_val_2894_);
if (v_isShared_2897_ == 0)
{
lean_ctor_set(v___x_2896_, 0, v_snd_2898_);
v___x_2900_ = v___x_2896_;
goto v_reusejp_2899_;
}
else
{
lean_object* v_reuseFailAlloc_2901_; 
v_reuseFailAlloc_2901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2901_, 0, v_snd_2898_);
v___x_2900_ = v_reuseFailAlloc_2901_;
goto v_reusejp_2899_;
}
v_reusejp_2899_:
{
return v___x_2900_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParam_x3f___redArg___boxed(lean_object* v_inst_2943_, lean_object* v_attr_2944_, lean_object* v_env_2945_, lean_object* v_decl_2946_){
_start:
{
lean_object* v_res_2947_; 
v_res_2947_ = l_Lean_ParametricAttribute_getParam_x3f___redArg(v_inst_2943_, v_attr_2944_, v_env_2945_, v_decl_2946_);
lean_dec_ref(v_attr_2944_);
return v_res_2947_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParam_x3f(lean_object* v_00_u03b1_2948_, lean_object* v_inst_2949_, lean_object* v_attr_2950_, lean_object* v_env_2951_, lean_object* v_decl_2952_){
_start:
{
lean_object* v___x_2953_; 
v___x_2953_ = l_Lean_ParametricAttribute_getParam_x3f___redArg(v_inst_2949_, v_attr_2950_, v_env_2951_, v_decl_2952_);
return v___x_2953_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParam_x3f___boxed(lean_object* v_00_u03b1_2954_, lean_object* v_inst_2955_, lean_object* v_attr_2956_, lean_object* v_env_2957_, lean_object* v_decl_2958_){
_start:
{
lean_object* v_res_2959_; 
v_res_2959_ = l_Lean_ParametricAttribute_getParam_x3f(v_00_u03b1_2954_, v_inst_2955_, v_attr_2956_, v_env_2957_, v_decl_2958_);
lean_dec_ref(v_attr_2956_);
return v_res_2959_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_setParam___redArg(lean_object* v_attr_2964_, lean_object* v_env_2965_, lean_object* v_decl_2966_, lean_object* v_param_2967_){
_start:
{
lean_object* v___x_2968_; 
v___x_2968_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2965_, v_decl_2966_);
if (lean_obj_tag(v___x_2968_) == 0)
{
lean_object* v_ext_2969_; lean_object* v_toEnvExtension_2970_; lean_object* v_attr_2971_; lean_object* v_asyncMode_2972_; lean_object* v___x_2973_; lean_object* v___x_2974_; lean_object* v___x_2975_; lean_object* v_snd_2976_; lean_object* v___x_2978_; uint8_t v_isShared_2979_; uint8_t v_isSharedCheck_3006_; 
v_ext_2969_ = lean_ctor_get(v_attr_2964_, 1);
lean_inc_ref(v_ext_2969_);
v_toEnvExtension_2970_ = lean_ctor_get(v_ext_2969_, 0);
v_attr_2971_ = lean_ctor_get(v_attr_2964_, 0);
lean_inc_ref(v_attr_2971_);
lean_dec_ref(v_attr_2964_);
v_asyncMode_2972_ = lean_ctor_get(v_toEnvExtension_2970_, 2);
lean_inc(v_asyncMode_2972_);
v___x_2973_ = ((lean_object*)(l_Lean_ParametricAttribute_getParam_x3f___redArg___closed__0));
v___x_2974_ = lean_box(0);
lean_inc_ref(v_env_2965_);
v___x_2975_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2973_, v_ext_2969_, v_env_2965_, v_asyncMode_2972_, v___x_2974_);
v_snd_2976_ = lean_ctor_get(v___x_2975_, 1);
v_isSharedCheck_3006_ = !lean_is_exclusive(v___x_2975_);
if (v_isSharedCheck_3006_ == 0)
{
lean_object* v_unused_3007_; 
v_unused_3007_ = lean_ctor_get(v___x_2975_, 0);
lean_dec(v_unused_3007_);
v___x_2978_ = v___x_2975_;
v_isShared_2979_ = v_isSharedCheck_3006_;
goto v_resetjp_2977_;
}
else
{
lean_inc(v_snd_2976_);
lean_dec(v___x_2975_);
v___x_2978_ = lean_box(0);
v_isShared_2979_ = v_isSharedCheck_3006_;
goto v_resetjp_2977_;
}
v_resetjp_2977_:
{
lean_object* v___x_2980_; 
v___x_2980_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_snd_2976_, v_decl_2966_);
lean_dec(v_snd_2976_);
if (lean_obj_tag(v___x_2980_) == 0)
{
lean_object* v___x_2982_; 
lean_dec_ref(v_attr_2971_);
if (v_isShared_2979_ == 0)
{
lean_ctor_set(v___x_2978_, 1, v_param_2967_);
lean_ctor_set(v___x_2978_, 0, v_decl_2966_);
v___x_2982_ = v___x_2978_;
goto v_reusejp_2981_;
}
else
{
lean_object* v_reuseFailAlloc_2985_; 
v_reuseFailAlloc_2985_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2985_, 0, v_decl_2966_);
lean_ctor_set(v_reuseFailAlloc_2985_, 1, v_param_2967_);
v___x_2982_ = v_reuseFailAlloc_2985_;
goto v_reusejp_2981_;
}
v_reusejp_2981_:
{
lean_object* v___x_2983_; lean_object* v___x_2984_; 
v___x_2983_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_ext_2969_, v_env_2965_, v___x_2982_, v_asyncMode_2972_, v___x_2974_);
lean_dec(v_asyncMode_2972_);
v___x_2984_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2984_, 0, v___x_2983_);
return v___x_2984_;
}
}
else
{
lean_object* v___x_2987_; uint8_t v_isShared_2988_; uint8_t v_isSharedCheck_3004_; 
lean_del_object(v___x_2978_);
lean_dec(v_asyncMode_2972_);
lean_dec_ref(v_ext_2969_);
lean_dec(v_param_2967_);
lean_dec_ref(v_env_2965_);
v_isSharedCheck_3004_ = !lean_is_exclusive(v___x_2980_);
if (v_isSharedCheck_3004_ == 0)
{
lean_object* v_unused_3005_; 
v_unused_3005_ = lean_ctor_get(v___x_2980_, 0);
lean_dec(v_unused_3005_);
v___x_2987_ = v___x_2980_;
v_isShared_2988_ = v_isSharedCheck_3004_;
goto v_resetjp_2986_;
}
else
{
lean_dec(v___x_2980_);
v___x_2987_ = lean_box(0);
v_isShared_2988_ = v_isSharedCheck_3004_;
goto v_resetjp_2986_;
}
v_resetjp_2986_:
{
lean_object* v_toAttributeImplCore_2989_; lean_object* v_name_2990_; uint8_t v___x_2991_; lean_object* v___x_2992_; lean_object* v___x_2993_; lean_object* v___x_2994_; lean_object* v___x_2995_; lean_object* v___x_2996_; lean_object* v___x_2997_; lean_object* v___x_2998_; lean_object* v___x_2999_; lean_object* v___x_3000_; lean_object* v___x_3002_; 
v_toAttributeImplCore_2989_ = lean_ctor_get(v_attr_2971_, 0);
lean_inc_ref(v_toAttributeImplCore_2989_);
lean_dec_ref(v_attr_2971_);
v_name_2990_ = lean_ctor_get(v_toAttributeImplCore_2989_, 1);
lean_inc(v_name_2990_);
lean_dec_ref(v_toAttributeImplCore_2989_);
v___x_2991_ = 1;
v___x_2992_ = ((lean_object*)(l_Lean_ParametricAttribute_setParam___redArg___closed__0));
v___x_2993_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_2990_, v___x_2991_);
v___x_2994_ = lean_string_append(v___x_2992_, v___x_2993_);
lean_dec_ref(v___x_2993_);
v___x_2995_ = ((lean_object*)(l_Lean_ParametricAttribute_setParam___redArg___closed__1));
v___x_2996_ = lean_string_append(v___x_2994_, v___x_2995_);
v___x_2997_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_decl_2966_, v___x_2991_);
v___x_2998_ = lean_string_append(v___x_2996_, v___x_2997_);
lean_dec_ref(v___x_2997_);
v___x_2999_ = ((lean_object*)(l_Lean_ParametricAttribute_setParam___redArg___closed__2));
v___x_3000_ = lean_string_append(v___x_2998_, v___x_2999_);
if (v_isShared_2988_ == 0)
{
lean_ctor_set_tag(v___x_2987_, 0);
lean_ctor_set(v___x_2987_, 0, v___x_3000_);
v___x_3002_ = v___x_2987_;
goto v_reusejp_3001_;
}
else
{
lean_object* v_reuseFailAlloc_3003_; 
v_reuseFailAlloc_3003_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3003_, 0, v___x_3000_);
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
}
else
{
lean_object* v___x_3009_; uint8_t v_isShared_3010_; uint8_t v_isSharedCheck_3027_; 
lean_dec(v_param_2967_);
lean_dec_ref(v_env_2965_);
v_isSharedCheck_3027_ = !lean_is_exclusive(v___x_2968_);
if (v_isSharedCheck_3027_ == 0)
{
lean_object* v_unused_3028_; 
v_unused_3028_ = lean_ctor_get(v___x_2968_, 0);
lean_dec(v_unused_3028_);
v___x_3009_ = v___x_2968_;
v_isShared_3010_ = v_isSharedCheck_3027_;
goto v_resetjp_3008_;
}
else
{
lean_dec(v___x_2968_);
v___x_3009_ = lean_box(0);
v_isShared_3010_ = v_isSharedCheck_3027_;
goto v_resetjp_3008_;
}
v_resetjp_3008_:
{
lean_object* v_attr_3011_; lean_object* v_toAttributeImplCore_3012_; lean_object* v_name_3013_; uint8_t v___x_3014_; lean_object* v___x_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; lean_object* v___x_3018_; lean_object* v___x_3019_; lean_object* v___x_3020_; lean_object* v___x_3021_; lean_object* v___x_3022_; lean_object* v___x_3023_; lean_object* v___x_3025_; 
v_attr_3011_ = lean_ctor_get(v_attr_2964_, 0);
lean_inc_ref(v_attr_3011_);
lean_dec_ref(v_attr_2964_);
v_toAttributeImplCore_3012_ = lean_ctor_get(v_attr_3011_, 0);
lean_inc_ref(v_toAttributeImplCore_3012_);
lean_dec_ref(v_attr_3011_);
v_name_3013_ = lean_ctor_get(v_toAttributeImplCore_3012_, 1);
lean_inc(v_name_3013_);
lean_dec_ref(v_toAttributeImplCore_3012_);
v___x_3014_ = 1;
v___x_3015_ = ((lean_object*)(l_Lean_ParametricAttribute_setParam___redArg___closed__0));
v___x_3016_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_3013_, v___x_3014_);
v___x_3017_ = lean_string_append(v___x_3015_, v___x_3016_);
lean_dec_ref(v___x_3016_);
v___x_3018_ = ((lean_object*)(l_Lean_ParametricAttribute_setParam___redArg___closed__1));
v___x_3019_ = lean_string_append(v___x_3017_, v___x_3018_);
v___x_3020_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_decl_2966_, v___x_3014_);
v___x_3021_ = lean_string_append(v___x_3019_, v___x_3020_);
lean_dec_ref(v___x_3020_);
v___x_3022_ = ((lean_object*)(l_Lean_ParametricAttribute_setParam___redArg___closed__3));
v___x_3023_ = lean_string_append(v___x_3021_, v___x_3022_);
if (v_isShared_3010_ == 0)
{
lean_ctor_set_tag(v___x_3009_, 0);
lean_ctor_set(v___x_3009_, 0, v___x_3023_);
v___x_3025_ = v___x_3009_;
goto v_reusejp_3024_;
}
else
{
lean_object* v_reuseFailAlloc_3026_; 
v_reuseFailAlloc_3026_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3026_, 0, v___x_3023_);
v___x_3025_ = v_reuseFailAlloc_3026_;
goto v_reusejp_3024_;
}
v_reusejp_3024_:
{
return v___x_3025_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_setParam(lean_object* v_00_u03b1_3029_, lean_object* v_attr_3030_, lean_object* v_env_3031_, lean_object* v_decl_3032_, lean_object* v_param_3033_){
_start:
{
lean_object* v___x_3034_; 
v___x_3034_ = l_Lean_ParametricAttribute_setParam___redArg(v_attr_3030_, v_env_3031_, v_decl_3032_, v_param_3033_);
return v___x_3034_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___lam__0(lean_object* v_x_3035_, lean_object* v___y_3036_){
_start:
{
lean_object* v___x_3038_; lean_object* v___x_3039_; 
v___x_3038_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___lam__0___closed__1));
v___x_3039_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3039_, 0, v___x_3038_);
return v___x_3039_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___lam__0___boxed(lean_object* v_x_3040_, lean_object* v___y_3041_, lean_object* v___y_3042_){
_start:
{
lean_object* v_res_3043_; 
v_res_3043_ = l_Lean_instInhabitedEnumAttributes_default___lam__0(v_x_3040_, v___y_3041_);
lean_dec_ref(v___y_3041_);
lean_dec_ref(v_x_3040_);
return v_res_3043_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___lam__1(lean_object* v_s_3044_, lean_object* v_x_3045_){
_start:
{
lean_inc(v_s_3044_);
return v_s_3044_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___lam__1___boxed(lean_object* v_s_3046_, lean_object* v_x_3047_){
_start:
{
lean_object* v_res_3048_; 
v_res_3048_ = l_Lean_instInhabitedEnumAttributes_default___lam__1(v_s_3046_, v_x_3047_);
lean_dec_ref(v_x_3047_);
lean_dec(v_s_3046_);
return v_res_3048_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___lam__2(lean_object* v_x_3049_, lean_object* v_x_3050_){
_start:
{
lean_object* v___x_3051_; 
v___x_3051_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___lam__2___closed__1));
return v___x_3051_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___lam__2___boxed(lean_object* v_x_3052_, lean_object* v_x_3053_){
_start:
{
lean_object* v_res_3054_; 
v_res_3054_ = l_Lean_instInhabitedEnumAttributes_default___lam__2(v_x_3052_, v_x_3053_);
lean_dec(v_x_3053_);
lean_dec_ref(v_x_3052_);
return v_res_3054_;
}
}
static lean_object* _init_l_Lean_instInhabitedEnumAttributes_default___closed__3(void){
_start:
{
lean_object* v___x_3058_; 
v___x_3058_ = l_Lean_instInhabitedEnvExtension_default(lean_box(0));
return v___x_3058_;
}
}
static lean_object* _init_l_Lean_instInhabitedEnumAttributes_default___closed__4(void){
_start:
{
lean_object* v___f_3059_; lean_object* v___f_3060_; lean_object* v___f_3061_; lean_object* v___f_3062_; lean_object* v___x_3063_; lean_object* v___x_3064_; lean_object* v___x_3065_; 
v___f_3059_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___closed__3));
v___f_3060_ = ((lean_object*)(l_Lean_instInhabitedEnumAttributes_default___closed__2));
v___f_3061_ = ((lean_object*)(l_Lean_instInhabitedEnumAttributes_default___closed__1));
v___f_3062_ = ((lean_object*)(l_Lean_instInhabitedEnumAttributes_default___closed__0));
v___x_3063_ = lean_box(0);
v___x_3064_ = lean_obj_once(&l_Lean_instInhabitedEnumAttributes_default___closed__3, &l_Lean_instInhabitedEnumAttributes_default___closed__3_once, _init_l_Lean_instInhabitedEnumAttributes_default___closed__3);
v___x_3065_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3065_, 0, v___x_3064_);
lean_ctor_set(v___x_3065_, 1, v___x_3063_);
lean_ctor_set(v___x_3065_, 2, v___f_3062_);
lean_ctor_set(v___x_3065_, 3, v___f_3061_);
lean_ctor_set(v___x_3065_, 4, v___f_3060_);
lean_ctor_set(v___x_3065_, 5, v___f_3059_);
return v___x_3065_;
}
}
static lean_object* _init_l_Lean_instInhabitedEnumAttributes_default___closed__5(void){
_start:
{
lean_object* v___x_3066_; lean_object* v___x_3067_; lean_object* v___x_3068_; 
v___x_3066_ = lean_obj_once(&l_Lean_instInhabitedEnumAttributes_default___closed__4, &l_Lean_instInhabitedEnumAttributes_default___closed__4_once, _init_l_Lean_instInhabitedEnumAttributes_default___closed__4);
v___x_3067_ = lean_box(0);
v___x_3068_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3068_, 0, v___x_3067_);
lean_ctor_set(v___x_3068_, 1, v___x_3066_);
return v___x_3068_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default(lean_object* v_a_3069_){
_start:
{
lean_object* v___x_3070_; 
v___x_3070_ = lean_obj_once(&l_Lean_instInhabitedEnumAttributes_default___closed__5, &l_Lean_instInhabitedEnumAttributes_default___closed__5_once, _init_l_Lean_instInhabitedEnumAttributes_default___closed__5);
return v___x_3070_;
}
}
static lean_object* _init_l_Lean_instInhabitedEnumAttributes___closed__0(void){
_start:
{
lean_object* v___x_3071_; 
v___x_3071_ = l_Lean_instInhabitedEnumAttributes_default(lean_box(0));
return v___x_3071_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes(lean_object* v_a_3072_){
_start:
{
lean_object* v___x_3073_; 
v___x_3073_ = lean_obj_once(&l_Lean_instInhabitedEnumAttributes___closed__0, &l_Lean_instInhabitedEnumAttributes___closed__0_once, _init_l_Lean_instInhabitedEnumAttributes___closed__0);
return v___x_3073_;
}
}
static lean_object* _init_l_Lean_registerEnumAttributes___auto__1(void){
_start:
{
lean_object* v___x_3074_; 
v___x_3074_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__28, &l_Lean_AttributeImplCore_ref___autoParam___closed__28_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__28);
return v___x_3074_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__0(lean_object* v_x_3075_){
_start:
{
lean_object* v___x_3076_; 
v___x_3076_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___lam__2___closed__0));
return v___x_3076_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__0___boxed(lean_object* v_x_3077_){
_start:
{
lean_object* v_res_3078_; 
v_res_3078_ = l_Lean_registerEnumAttributes___redArg___lam__0(v_x_3077_);
lean_dec(v_x_3077_);
return v_res_3078_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___redArg(lean_object* v_newState_3079_, lean_object* v_x_3080_, lean_object* v_x_3081_){
_start:
{
if (lean_obj_tag(v_x_3081_) == 0)
{
return v_x_3080_;
}
else
{
lean_object* v_head_3082_; lean_object* v_tail_3083_; lean_object* v___x_3084_; 
v_head_3082_ = lean_ctor_get(v_x_3081_, 0);
lean_inc(v_head_3082_);
v_tail_3083_ = lean_ctor_get(v_x_3081_, 1);
lean_inc(v_tail_3083_);
lean_dec_ref(v_x_3081_);
v___x_3084_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_newState_3079_, v_head_3082_);
if (lean_obj_tag(v___x_3084_) == 1)
{
lean_object* v_val_3085_; lean_object* v___x_3086_; 
v_val_3085_ = lean_ctor_get(v___x_3084_, 0);
lean_inc(v_val_3085_);
lean_dec_ref(v___x_3084_);
v___x_3086_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_head_3082_, v_val_3085_, v_x_3080_);
v_x_3080_ = v___x_3086_;
v_x_3081_ = v_tail_3083_;
goto _start;
}
else
{
lean_dec(v___x_3084_);
lean_dec(v_head_3082_);
v_x_3081_ = v_tail_3083_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___redArg___boxed(lean_object* v_newState_3089_, lean_object* v_x_3090_, lean_object* v_x_3091_){
_start:
{
lean_object* v_res_3092_; 
v_res_3092_ = l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___redArg(v_newState_3089_, v_x_3090_, v_x_3091_);
lean_dec(v_newState_3089_);
return v_res_3092_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__1(lean_object* v_x_3093_, lean_object* v_newState_3094_, lean_object* v_consts_3095_, lean_object* v_st_3096_){
_start:
{
lean_object* v___x_3097_; 
v___x_3097_ = l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___redArg(v_newState_3094_, v_st_3096_, v_consts_3095_);
return v___x_3097_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__1___boxed(lean_object* v_x_3098_, lean_object* v_newState_3099_, lean_object* v_consts_3100_, lean_object* v_st_3101_){
_start:
{
lean_object* v_res_3102_; 
v_res_3102_ = l_Lean_registerEnumAttributes___redArg___lam__1(v_x_3098_, v_newState_3099_, v_consts_3100_, v_st_3101_);
lean_dec(v_newState_3099_);
lean_dec(v_x_3098_);
return v_res_3102_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__2(lean_object* v_s_3112_){
_start:
{
lean_object* v___x_3113_; lean_object* v___y_3115_; 
v___x_3113_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___lam__2___closed__3));
if (lean_obj_tag(v_s_3112_) == 0)
{
lean_object* v_size_3119_; 
v_size_3119_ = lean_ctor_get(v_s_3112_, 0);
lean_inc(v_size_3119_);
lean_dec_ref(v_s_3112_);
v___y_3115_ = v_size_3119_;
goto v___jp_3114_;
}
else
{
lean_object* v___x_3120_; 
v___x_3120_ = lean_unsigned_to_nat(0u);
v___y_3115_ = v___x_3120_;
goto v___jp_3114_;
}
v___jp_3114_:
{
lean_object* v___x_3116_; lean_object* v___x_3117_; lean_object* v___x_3118_; 
v___x_3116_ = l_Nat_reprFast(v___y_3115_);
v___x_3117_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3117_, 0, v___x_3116_);
v___x_3118_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3118_, 0, v___x_3113_);
lean_ctor_set(v___x_3118_, 1, v___x_3117_);
return v___x_3118_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg(lean_object* v_env_3121_, lean_object* v_as_3122_, size_t v_i_3123_, size_t v_stop_3124_, lean_object* v_b_3125_){
_start:
{
lean_object* v___y_3127_; uint8_t v___x_3131_; 
v___x_3131_ = lean_usize_dec_eq(v_i_3123_, v_stop_3124_);
if (v___x_3131_ == 0)
{
lean_object* v___x_3132_; lean_object* v_fst_3133_; uint8_t v___x_3134_; lean_object* v___x_3135_; uint8_t v___x_3136_; 
v___x_3132_ = lean_array_uget_borrowed(v_as_3122_, v_i_3123_);
v_fst_3133_ = lean_ctor_get(v___x_3132_, 0);
v___x_3134_ = 1;
lean_inc_ref(v_env_3121_);
v___x_3135_ = l_Lean_Environment_setExporting(v_env_3121_, v___x_3134_);
lean_inc(v_fst_3133_);
v___x_3136_ = l_Lean_Environment_contains(v___x_3135_, v_fst_3133_, v___x_3131_);
if (v___x_3136_ == 0)
{
v___y_3127_ = v_b_3125_;
goto v___jp_3126_;
}
else
{
lean_object* v___x_3137_; 
lean_inc(v___x_3132_);
v___x_3137_ = lean_array_push(v_b_3125_, v___x_3132_);
v___y_3127_ = v___x_3137_;
goto v___jp_3126_;
}
}
else
{
lean_dec_ref(v_env_3121_);
return v_b_3125_;
}
v___jp_3126_:
{
size_t v___x_3128_; size_t v___x_3129_; 
v___x_3128_ = ((size_t)1ULL);
v___x_3129_ = lean_usize_add(v_i_3123_, v___x_3128_);
v_i_3123_ = v___x_3129_;
v_b_3125_ = v___y_3127_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg___boxed(lean_object* v_env_3138_, lean_object* v_as_3139_, lean_object* v_i_3140_, lean_object* v_stop_3141_, lean_object* v_b_3142_){
_start:
{
size_t v_i_boxed_3143_; size_t v_stop_boxed_3144_; lean_object* v_res_3145_; 
v_i_boxed_3143_ = lean_unbox_usize(v_i_3140_);
lean_dec(v_i_3140_);
v_stop_boxed_3144_ = lean_unbox_usize(v_stop_3141_);
lean_dec(v_stop_3141_);
v_res_3145_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg(v_env_3138_, v_as_3139_, v_i_boxed_3143_, v_stop_boxed_3144_, v_b_3142_);
lean_dec_ref(v_as_3139_);
return v_res_3145_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__3(lean_object* v_env_3146_, lean_object* v_m_3147_){
_start:
{
lean_object* v___x_3148_; lean_object* v___x_3149_; lean_object* v___y_3151_; lean_object* v___x_3165_; lean_object* v___y_3167_; lean_object* v___y_3168_; lean_object* v___x_3170_; uint8_t v___x_3171_; 
v___x_3148_ = lean_unsigned_to_nat(0u);
v___x_3149_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___lam__2___closed__0));
v___x_3165_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1_spec__1___redArg(v___x_3149_, v_m_3147_);
v___x_3170_ = lean_array_get_size(v___x_3165_);
v___x_3171_ = lean_nat_dec_eq(v___x_3170_, v___x_3148_);
if (v___x_3171_ == 0)
{
lean_object* v___x_3172_; lean_object* v___x_3173_; lean_object* v___y_3175_; uint8_t v___x_3177_; 
v___x_3172_ = lean_unsigned_to_nat(1u);
v___x_3173_ = lean_nat_sub(v___x_3170_, v___x_3172_);
v___x_3177_ = lean_nat_dec_le(v___x_3148_, v___x_3173_);
if (v___x_3177_ == 0)
{
lean_inc(v___x_3173_);
v___y_3175_ = v___x_3173_;
goto v___jp_3174_;
}
else
{
v___y_3175_ = v___x_3148_;
goto v___jp_3174_;
}
v___jp_3174_:
{
uint8_t v___x_3176_; 
v___x_3176_ = lean_nat_dec_le(v___y_3175_, v___x_3173_);
if (v___x_3176_ == 0)
{
lean_dec(v___x_3173_);
lean_inc(v___y_3175_);
v___y_3167_ = v___y_3175_;
v___y_3168_ = v___y_3175_;
goto v___jp_3166_;
}
else
{
v___y_3167_ = v___y_3175_;
v___y_3168_ = v___x_3173_;
goto v___jp_3166_;
}
}
}
else
{
v___y_3151_ = v___x_3165_;
goto v___jp_3150_;
}
v___jp_3150_:
{
lean_object* v___x_3152_; uint8_t v___x_3153_; 
v___x_3152_ = lean_array_get_size(v___y_3151_);
v___x_3153_ = lean_nat_dec_lt(v___x_3148_, v___x_3152_);
if (v___x_3153_ == 0)
{
lean_object* v___x_3154_; 
lean_dec_ref(v_env_3146_);
v___x_3154_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3154_, 0, v___x_3149_);
lean_ctor_set(v___x_3154_, 1, v___x_3149_);
lean_ctor_set(v___x_3154_, 2, v___y_3151_);
return v___x_3154_;
}
else
{
uint8_t v___x_3155_; 
v___x_3155_ = lean_nat_dec_le(v___x_3152_, v___x_3152_);
if (v___x_3155_ == 0)
{
if (v___x_3153_ == 0)
{
lean_object* v___x_3156_; 
lean_dec_ref(v_env_3146_);
v___x_3156_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3156_, 0, v___x_3149_);
lean_ctor_set(v___x_3156_, 1, v___x_3149_);
lean_ctor_set(v___x_3156_, 2, v___y_3151_);
return v___x_3156_;
}
else
{
size_t v___x_3157_; size_t v___x_3158_; lean_object* v___x_3159_; lean_object* v___x_3160_; 
v___x_3157_ = ((size_t)0ULL);
v___x_3158_ = lean_usize_of_nat(v___x_3152_);
v___x_3159_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg(v_env_3146_, v___y_3151_, v___x_3157_, v___x_3158_, v___x_3149_);
lean_inc_ref(v___x_3159_);
v___x_3160_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3160_, 0, v___x_3159_);
lean_ctor_set(v___x_3160_, 1, v___x_3159_);
lean_ctor_set(v___x_3160_, 2, v___y_3151_);
return v___x_3160_;
}
}
else
{
size_t v___x_3161_; size_t v___x_3162_; lean_object* v___x_3163_; lean_object* v___x_3164_; 
v___x_3161_ = ((size_t)0ULL);
v___x_3162_ = lean_usize_of_nat(v___x_3152_);
v___x_3163_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg(v_env_3146_, v___y_3151_, v___x_3161_, v___x_3162_, v___x_3149_);
lean_inc_ref(v___x_3163_);
v___x_3164_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3164_, 0, v___x_3163_);
lean_ctor_set(v___x_3164_, 1, v___x_3163_);
lean_ctor_set(v___x_3164_, 2, v___y_3151_);
return v___x_3164_;
}
}
}
v___jp_3166_:
{
lean_object* v___x_3169_; 
v___x_3169_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2___redArg(v___x_3165_, v___y_3167_, v___y_3168_);
lean_dec(v___y_3168_);
v___y_3151_ = v___x_3169_;
goto v___jp_3150_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__3___boxed(lean_object* v_env_3178_, lean_object* v_m_3179_){
_start:
{
lean_object* v_res_3180_; 
v_res_3180_ = l_Lean_registerEnumAttributes___redArg___lam__3(v_env_3178_, v_m_3179_);
lean_dec(v_m_3179_);
return v_res_3180_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__4(lean_object* v_s_3181_, lean_object* v_p_3182_){
_start:
{
lean_object* v_fst_3183_; lean_object* v_snd_3184_; lean_object* v___x_3185_; 
v_fst_3183_ = lean_ctor_get(v_p_3182_, 0);
lean_inc(v_fst_3183_);
v_snd_3184_ = lean_ctor_get(v_p_3182_, 1);
lean_inc(v_snd_3184_);
lean_dec_ref(v_p_3182_);
v___x_3185_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_3183_, v_snd_3184_, v_s_3181_);
return v___x_3185_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__6(lean_object* v___x_3186_, lean_object* v_x_3187_, lean_object* v_x_3188_){
_start:
{
lean_object* v___x_3190_; 
v___x_3190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3190_, 0, v___x_3186_);
return v___x_3190_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__6___boxed(lean_object* v___x_3191_, lean_object* v_x_3192_, lean_object* v_x_3193_, lean_object* v___y_3194_){
_start:
{
lean_object* v_res_3195_; 
v_res_3195_ = l_Lean_registerEnumAttributes___redArg___lam__6(v___x_3191_, v_x_3192_, v_x_3193_);
lean_dec_ref(v_x_3193_);
lean_dec_ref(v_x_3192_);
return v_res_3195_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_registerEnumAttributes_spec__3(lean_object* v_as_3196_){
_start:
{
if (lean_obj_tag(v_as_3196_) == 0)
{
lean_object* v___x_3198_; lean_object* v___x_3199_; 
v___x_3198_ = lean_box(0);
v___x_3199_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3199_, 0, v___x_3198_);
return v___x_3199_;
}
else
{
lean_object* v_head_3200_; lean_object* v_tail_3201_; lean_object* v___x_3202_; 
v_head_3200_ = lean_ctor_get(v_as_3196_, 0);
lean_inc(v_head_3200_);
v_tail_3201_ = lean_ctor_get(v_as_3196_, 1);
lean_inc(v_tail_3201_);
lean_dec_ref(v_as_3196_);
v___x_3202_ = l_Lean_registerBuiltinAttribute(v_head_3200_);
if (lean_obj_tag(v___x_3202_) == 0)
{
lean_dec_ref(v___x_3202_);
v_as_3196_ = v_tail_3201_;
goto _start;
}
else
{
lean_dec(v_tail_3201_);
return v___x_3202_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_registerEnumAttributes_spec__3___boxed(lean_object* v_as_3204_, lean_object* v___y_3205_){
_start:
{
lean_object* v_res_3206_; 
v_res_3206_ = l_List_forM___at___00Lean_registerEnumAttributes_spec__3(v_as_3204_);
return v_res_3206_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__1(lean_object* v_validate_3207_, lean_object* v_snd_3208_, lean_object* v_a_3209_, lean_object* v_fst_3210_, lean_object* v_decl_3211_, lean_object* v_stx_3212_, uint8_t v_kind_3213_, lean_object* v___y_3214_, lean_object* v___y_3215_){
_start:
{
lean_object* v___y_3218_; lean_object* v___y_3219_; lean_object* v___y_3254_; lean_object* v___y_3255_; lean_object* v___x_3260_; 
v___x_3260_ = l_Lean_Attribute_Builtin_ensureNoArgs(v_stx_3212_, v___y_3214_, v___y_3215_);
if (lean_obj_tag(v___x_3260_) == 0)
{
uint8_t v___x_3261_; uint8_t v___x_3262_; 
lean_dec_ref(v___x_3260_);
v___x_3261_ = 0;
v___x_3262_ = l_Lean_instBEqAttributeKind_beq(v_kind_3213_, v___x_3261_);
if (v___x_3262_ == 0)
{
lean_object* v___x_3263_; 
lean_dec(v_decl_3211_);
lean_dec_ref(v_a_3209_);
lean_dec(v_snd_3208_);
lean_dec_ref(v_validate_3207_);
v___x_3263_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg(v_fst_3210_, v_kind_3213_, v___y_3214_, v___y_3215_);
return v___x_3263_;
}
else
{
v___y_3254_ = v___y_3214_;
v___y_3255_ = v___y_3215_;
goto v___jp_3253_;
}
}
else
{
lean_dec(v_decl_3211_);
lean_dec(v_fst_3210_);
lean_dec_ref(v_a_3209_);
lean_dec(v_snd_3208_);
lean_dec_ref(v_validate_3207_);
return v___x_3260_;
}
v___jp_3217_:
{
lean_object* v___x_3220_; 
lean_inc(v___y_3219_);
lean_inc_ref(v___y_3218_);
lean_inc(v_snd_3208_);
lean_inc(v_decl_3211_);
v___x_3220_ = lean_apply_5(v_validate_3207_, v_decl_3211_, v_snd_3208_, v___y_3218_, v___y_3219_, lean_box(0));
if (lean_obj_tag(v___x_3220_) == 0)
{
lean_object* v___x_3222_; uint8_t v_isShared_3223_; uint8_t v_isSharedCheck_3251_; 
v_isSharedCheck_3251_ = !lean_is_exclusive(v___x_3220_);
if (v_isSharedCheck_3251_ == 0)
{
lean_object* v_unused_3252_; 
v_unused_3252_ = lean_ctor_get(v___x_3220_, 0);
lean_dec(v_unused_3252_);
v___x_3222_ = v___x_3220_;
v_isShared_3223_ = v_isSharedCheck_3251_;
goto v_resetjp_3221_;
}
else
{
lean_dec(v___x_3220_);
v___x_3222_ = lean_box(0);
v_isShared_3223_ = v_isSharedCheck_3251_;
goto v_resetjp_3221_;
}
v_resetjp_3221_:
{
lean_object* v___x_3224_; lean_object* v_toEnvExtension_3225_; lean_object* v_env_3226_; lean_object* v_nextMacroScope_3227_; lean_object* v_ngen_3228_; lean_object* v_auxDeclNGen_3229_; lean_object* v_traceState_3230_; lean_object* v_messages_3231_; lean_object* v_infoState_3232_; lean_object* v_snapshotTasks_3233_; lean_object* v___x_3235_; uint8_t v_isShared_3236_; uint8_t v_isSharedCheck_3249_; 
v___x_3224_ = lean_st_ref_take(v___y_3219_);
v_toEnvExtension_3225_ = lean_ctor_get(v_a_3209_, 0);
v_env_3226_ = lean_ctor_get(v___x_3224_, 0);
v_nextMacroScope_3227_ = lean_ctor_get(v___x_3224_, 1);
v_ngen_3228_ = lean_ctor_get(v___x_3224_, 2);
v_auxDeclNGen_3229_ = lean_ctor_get(v___x_3224_, 3);
v_traceState_3230_ = lean_ctor_get(v___x_3224_, 4);
v_messages_3231_ = lean_ctor_get(v___x_3224_, 6);
v_infoState_3232_ = lean_ctor_get(v___x_3224_, 7);
v_snapshotTasks_3233_ = lean_ctor_get(v___x_3224_, 8);
v_isSharedCheck_3249_ = !lean_is_exclusive(v___x_3224_);
if (v_isSharedCheck_3249_ == 0)
{
lean_object* v_unused_3250_; 
v_unused_3250_ = lean_ctor_get(v___x_3224_, 5);
lean_dec(v_unused_3250_);
v___x_3235_ = v___x_3224_;
v_isShared_3236_ = v_isSharedCheck_3249_;
goto v_resetjp_3234_;
}
else
{
lean_inc(v_snapshotTasks_3233_);
lean_inc(v_infoState_3232_);
lean_inc(v_messages_3231_);
lean_inc(v_traceState_3230_);
lean_inc(v_auxDeclNGen_3229_);
lean_inc(v_ngen_3228_);
lean_inc(v_nextMacroScope_3227_);
lean_inc(v_env_3226_);
lean_dec(v___x_3224_);
v___x_3235_ = lean_box(0);
v_isShared_3236_ = v_isSharedCheck_3249_;
goto v_resetjp_3234_;
}
v_resetjp_3234_:
{
lean_object* v_asyncMode_3237_; lean_object* v___x_3238_; lean_object* v___x_3239_; lean_object* v___x_3240_; lean_object* v___x_3242_; 
v_asyncMode_3237_ = lean_ctor_get(v_toEnvExtension_3225_, 2);
lean_inc(v_asyncMode_3237_);
lean_inc(v_decl_3211_);
v___x_3238_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3238_, 0, v_decl_3211_);
lean_ctor_set(v___x_3238_, 1, v_snd_3208_);
v___x_3239_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_a_3209_, v_env_3226_, v___x_3238_, v_asyncMode_3237_, v_decl_3211_);
lean_dec(v_asyncMode_3237_);
v___x_3240_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2);
if (v_isShared_3236_ == 0)
{
lean_ctor_set(v___x_3235_, 5, v___x_3240_);
lean_ctor_set(v___x_3235_, 0, v___x_3239_);
v___x_3242_ = v___x_3235_;
goto v_reusejp_3241_;
}
else
{
lean_object* v_reuseFailAlloc_3248_; 
v_reuseFailAlloc_3248_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3248_, 0, v___x_3239_);
lean_ctor_set(v_reuseFailAlloc_3248_, 1, v_nextMacroScope_3227_);
lean_ctor_set(v_reuseFailAlloc_3248_, 2, v_ngen_3228_);
lean_ctor_set(v_reuseFailAlloc_3248_, 3, v_auxDeclNGen_3229_);
lean_ctor_set(v_reuseFailAlloc_3248_, 4, v_traceState_3230_);
lean_ctor_set(v_reuseFailAlloc_3248_, 5, v___x_3240_);
lean_ctor_set(v_reuseFailAlloc_3248_, 6, v_messages_3231_);
lean_ctor_set(v_reuseFailAlloc_3248_, 7, v_infoState_3232_);
lean_ctor_set(v_reuseFailAlloc_3248_, 8, v_snapshotTasks_3233_);
v___x_3242_ = v_reuseFailAlloc_3248_;
goto v_reusejp_3241_;
}
v_reusejp_3241_:
{
lean_object* v___x_3243_; lean_object* v___x_3244_; lean_object* v___x_3246_; 
v___x_3243_ = lean_st_ref_set(v___y_3219_, v___x_3242_);
v___x_3244_ = lean_box(0);
if (v_isShared_3223_ == 0)
{
lean_ctor_set(v___x_3222_, 0, v___x_3244_);
v___x_3246_ = v___x_3222_;
goto v_reusejp_3245_;
}
else
{
lean_object* v_reuseFailAlloc_3247_; 
v_reuseFailAlloc_3247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3247_, 0, v___x_3244_);
v___x_3246_ = v_reuseFailAlloc_3247_;
goto v_reusejp_3245_;
}
v_reusejp_3245_:
{
return v___x_3246_;
}
}
}
}
}
else
{
lean_dec(v_decl_3211_);
lean_dec_ref(v_a_3209_);
lean_dec(v_snd_3208_);
return v___x_3220_;
}
}
v___jp_3253_:
{
lean_object* v___x_3256_; lean_object* v_env_3257_; lean_object* v___x_3258_; 
v___x_3256_ = lean_st_ref_get(v___y_3255_);
v_env_3257_ = lean_ctor_get(v___x_3256_, 0);
lean_inc_ref(v_env_3257_);
lean_dec(v___x_3256_);
v___x_3258_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3257_, v_decl_3211_);
lean_dec_ref(v_env_3257_);
if (lean_obj_tag(v___x_3258_) == 0)
{
lean_dec(v_fst_3210_);
v___y_3218_ = v___y_3254_;
v___y_3219_ = v___y_3255_;
goto v___jp_3217_;
}
else
{
lean_object* v___x_3259_; 
lean_dec_ref(v___x_3258_);
lean_dec_ref(v_a_3209_);
lean_dec(v_snd_3208_);
lean_dec_ref(v_validate_3207_);
v___x_3259_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg(v_fst_3210_, v_decl_3211_, v___y_3254_, v___y_3255_);
return v___x_3259_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__1___boxed(lean_object* v_validate_3264_, lean_object* v_snd_3265_, lean_object* v_a_3266_, lean_object* v_fst_3267_, lean_object* v_decl_3268_, lean_object* v_stx_3269_, lean_object* v_kind_3270_, lean_object* v___y_3271_, lean_object* v___y_3272_, lean_object* v___y_3273_){
_start:
{
uint8_t v_kind_boxed_3274_; lean_object* v_res_3275_; 
v_kind_boxed_3274_ = lean_unbox(v_kind_3270_);
v_res_3275_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__1(v_validate_3264_, v_snd_3265_, v_a_3266_, v_fst_3267_, v_decl_3268_, v_stx_3269_, v_kind_boxed_3274_, v___y_3271_, v___y_3272_);
lean_dec(v___y_3272_);
lean_dec_ref(v___y_3271_);
return v_res_3275_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__0(lean_object* v_fst_3276_, lean_object* v_decl_3277_, lean_object* v___y_3278_, lean_object* v___y_3279_){
_start:
{
lean_object* v___x_3281_; lean_object* v___x_3282_; lean_object* v___x_3283_; lean_object* v___x_3284_; lean_object* v___x_3285_; lean_object* v___x_3286_; 
v___x_3281_ = lean_obj_once(&l_Lean_registerTagAttribute___lam__6___closed__1, &l_Lean_registerTagAttribute___lam__6___closed__1_once, _init_l_Lean_registerTagAttribute___lam__6___closed__1);
v___x_3282_ = l_Lean_MessageData_ofName(v_fst_3276_);
v___x_3283_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3283_, 0, v___x_3281_);
lean_ctor_set(v___x_3283_, 1, v___x_3282_);
v___x_3284_ = lean_obj_once(&l_Lean_registerTagAttribute___lam__6___closed__3, &l_Lean_registerTagAttribute___lam__6___closed__3_once, _init_l_Lean_registerTagAttribute___lam__6___closed__3);
v___x_3285_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3285_, 0, v___x_3283_);
lean_ctor_set(v___x_3285_, 1, v___x_3284_);
v___x_3286_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0_spec__0___redArg(v___x_3285_, v___y_3278_, v___y_3279_);
return v___x_3286_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__0___boxed(lean_object* v_fst_3287_, lean_object* v_decl_3288_, lean_object* v___y_3289_, lean_object* v___y_3290_, lean_object* v___y_3291_){
_start:
{
lean_object* v_res_3292_; 
v_res_3292_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__0(v_fst_3287_, v_decl_3288_, v___y_3289_, v___y_3290_);
lean_dec(v___y_3290_);
lean_dec_ref(v___y_3289_);
lean_dec(v_decl_3288_);
return v_res_3292_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg(lean_object* v_validate_3293_, lean_object* v_a_3294_, lean_object* v_ref_3295_, uint8_t v_applicationTime_3296_, lean_object* v_a_3297_, lean_object* v_a_3298_){
_start:
{
if (lean_obj_tag(v_a_3297_) == 0)
{
lean_object* v___x_3299_; 
lean_dec(v_ref_3295_);
lean_dec_ref(v_a_3294_);
lean_dec_ref(v_validate_3293_);
v___x_3299_ = l_List_reverse___redArg(v_a_3298_);
return v___x_3299_;
}
else
{
lean_object* v_head_3300_; lean_object* v_snd_3301_; lean_object* v_tail_3302_; lean_object* v___x_3304_; uint8_t v_isShared_3305_; uint8_t v_isSharedCheck_3317_; 
v_head_3300_ = lean_ctor_get(v_a_3297_, 0);
lean_inc(v_head_3300_);
v_snd_3301_ = lean_ctor_get(v_head_3300_, 1);
lean_inc(v_snd_3301_);
v_tail_3302_ = lean_ctor_get(v_a_3297_, 1);
v_isSharedCheck_3317_ = !lean_is_exclusive(v_a_3297_);
if (v_isSharedCheck_3317_ == 0)
{
lean_object* v_unused_3318_; 
v_unused_3318_ = lean_ctor_get(v_a_3297_, 0);
lean_dec(v_unused_3318_);
v___x_3304_ = v_a_3297_;
v_isShared_3305_ = v_isSharedCheck_3317_;
goto v_resetjp_3303_;
}
else
{
lean_inc(v_tail_3302_);
lean_dec(v_a_3297_);
v___x_3304_ = lean_box(0);
v_isShared_3305_ = v_isSharedCheck_3317_;
goto v_resetjp_3303_;
}
v_resetjp_3303_:
{
lean_object* v_fst_3306_; lean_object* v_fst_3307_; lean_object* v_snd_3308_; lean_object* v___f_3309_; lean_object* v___f_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3314_; 
v_fst_3306_ = lean_ctor_get(v_head_3300_, 0);
lean_inc_n(v_fst_3306_, 3);
lean_dec(v_head_3300_);
v_fst_3307_ = lean_ctor_get(v_snd_3301_, 0);
lean_inc(v_fst_3307_);
v_snd_3308_ = lean_ctor_get(v_snd_3301_, 1);
lean_inc(v_snd_3308_);
lean_dec(v_snd_3301_);
v___f_3309_ = lean_alloc_closure((void*)(l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__0___boxed), 5, 1);
lean_closure_set(v___f_3309_, 0, v_fst_3306_);
lean_inc_ref(v_a_3294_);
lean_inc_ref(v_validate_3293_);
v___f_3310_ = lean_alloc_closure((void*)(l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__1___boxed), 10, 4);
lean_closure_set(v___f_3310_, 0, v_validate_3293_);
lean_closure_set(v___f_3310_, 1, v_snd_3308_);
lean_closure_set(v___f_3310_, 2, v_a_3294_);
lean_closure_set(v___f_3310_, 3, v_fst_3306_);
lean_inc(v_ref_3295_);
v___x_3311_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_3311_, 0, v_ref_3295_);
lean_ctor_set(v___x_3311_, 1, v_fst_3306_);
lean_ctor_set(v___x_3311_, 2, v_fst_3307_);
lean_ctor_set_uint8(v___x_3311_, sizeof(void*)*3, v_applicationTime_3296_);
v___x_3312_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3312_, 0, v___x_3311_);
lean_ctor_set(v___x_3312_, 1, v___f_3310_);
lean_ctor_set(v___x_3312_, 2, v___f_3309_);
if (v_isShared_3305_ == 0)
{
lean_ctor_set(v___x_3304_, 1, v_a_3298_);
lean_ctor_set(v___x_3304_, 0, v___x_3312_);
v___x_3314_ = v___x_3304_;
goto v_reusejp_3313_;
}
else
{
lean_object* v_reuseFailAlloc_3316_; 
v_reuseFailAlloc_3316_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3316_, 0, v___x_3312_);
lean_ctor_set(v_reuseFailAlloc_3316_, 1, v_a_3298_);
v___x_3314_ = v_reuseFailAlloc_3316_;
goto v_reusejp_3313_;
}
v_reusejp_3313_:
{
v_a_3297_ = v_tail_3302_;
v_a_3298_ = v___x_3314_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___boxed(lean_object* v_validate_3319_, lean_object* v_a_3320_, lean_object* v_ref_3321_, lean_object* v_applicationTime_3322_, lean_object* v_a_3323_, lean_object* v_a_3324_){
_start:
{
uint8_t v_applicationTime_boxed_3325_; lean_object* v_res_3326_; 
v_applicationTime_boxed_3325_ = lean_unbox(v_applicationTime_3322_);
v_res_3326_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg(v_validate_3319_, v_a_3320_, v_ref_3321_, v_applicationTime_boxed_3325_, v_a_3323_, v_a_3324_);
return v_res_3326_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg(lean_object* v_attrDescrs_3340_, lean_object* v_validate_3341_, uint8_t v_applicationTime_3342_, lean_object* v_ref_3343_){
_start:
{
lean_object* v___f_3345_; lean_object* v___f_3346_; lean_object* v___f_3347_; lean_object* v___f_3348_; lean_object* v___f_3349_; lean_object* v___f_3350_; lean_object* v___x_3351_; lean_object* v___x_3352_; lean_object* v___x_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; 
v___f_3345_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__0));
v___f_3346_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__2));
v___f_3347_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__3));
v___f_3348_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__4));
v___f_3349_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__5));
v___f_3350_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__6));
v___x_3351_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__7));
v___x_3352_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__8));
lean_inc(v_ref_3343_);
v___x_3353_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_3353_, 0, v_ref_3343_);
lean_ctor_set(v___x_3353_, 1, v___f_3349_);
lean_ctor_set(v___x_3353_, 2, v___f_3350_);
lean_ctor_set(v___x_3353_, 3, v___f_3348_);
lean_ctor_set(v___x_3353_, 4, v___f_3347_);
lean_ctor_set(v___x_3353_, 5, v___f_3346_);
lean_ctor_set(v___x_3353_, 6, v___x_3351_);
lean_ctor_set(v___x_3353_, 7, v___x_3352_);
v___x_3354_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3354_, 0, v___x_3353_);
lean_ctor_set(v___x_3354_, 1, v___f_3345_);
v___x_3355_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_3354_);
if (lean_obj_tag(v___x_3355_) == 0)
{
lean_object* v_a_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; 
v_a_3356_ = lean_ctor_get(v___x_3355_, 0);
lean_inc_n(v_a_3356_, 2);
lean_dec_ref(v___x_3355_);
v___x_3357_ = lean_box(0);
v___x_3358_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg(v_validate_3341_, v_a_3356_, v_ref_3343_, v_applicationTime_3342_, v_attrDescrs_3340_, v___x_3357_);
lean_inc(v___x_3358_);
v___x_3359_ = l_List_forM___at___00Lean_registerEnumAttributes_spec__3(v___x_3358_);
if (lean_obj_tag(v___x_3359_) == 0)
{
lean_object* v___x_3361_; uint8_t v_isShared_3362_; uint8_t v_isSharedCheck_3367_; 
v_isSharedCheck_3367_ = !lean_is_exclusive(v___x_3359_);
if (v_isSharedCheck_3367_ == 0)
{
lean_object* v_unused_3368_; 
v_unused_3368_ = lean_ctor_get(v___x_3359_, 0);
lean_dec(v_unused_3368_);
v___x_3361_ = v___x_3359_;
v_isShared_3362_ = v_isSharedCheck_3367_;
goto v_resetjp_3360_;
}
else
{
lean_dec(v___x_3359_);
v___x_3361_ = lean_box(0);
v_isShared_3362_ = v_isSharedCheck_3367_;
goto v_resetjp_3360_;
}
v_resetjp_3360_:
{
lean_object* v___x_3363_; lean_object* v___x_3365_; 
v___x_3363_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3363_, 0, v___x_3358_);
lean_ctor_set(v___x_3363_, 1, v_a_3356_);
if (v_isShared_3362_ == 0)
{
lean_ctor_set(v___x_3361_, 0, v___x_3363_);
v___x_3365_ = v___x_3361_;
goto v_reusejp_3364_;
}
else
{
lean_object* v_reuseFailAlloc_3366_; 
v_reuseFailAlloc_3366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3366_, 0, v___x_3363_);
v___x_3365_ = v_reuseFailAlloc_3366_;
goto v_reusejp_3364_;
}
v_reusejp_3364_:
{
return v___x_3365_;
}
}
}
else
{
lean_object* v_a_3369_; lean_object* v___x_3371_; uint8_t v_isShared_3372_; uint8_t v_isSharedCheck_3376_; 
lean_dec(v___x_3358_);
lean_dec(v_a_3356_);
v_a_3369_ = lean_ctor_get(v___x_3359_, 0);
v_isSharedCheck_3376_ = !lean_is_exclusive(v___x_3359_);
if (v_isSharedCheck_3376_ == 0)
{
v___x_3371_ = v___x_3359_;
v_isShared_3372_ = v_isSharedCheck_3376_;
goto v_resetjp_3370_;
}
else
{
lean_inc(v_a_3369_);
lean_dec(v___x_3359_);
v___x_3371_ = lean_box(0);
v_isShared_3372_ = v_isSharedCheck_3376_;
goto v_resetjp_3370_;
}
v_resetjp_3370_:
{
lean_object* v___x_3374_; 
if (v_isShared_3372_ == 0)
{
v___x_3374_ = v___x_3371_;
goto v_reusejp_3373_;
}
else
{
lean_object* v_reuseFailAlloc_3375_; 
v_reuseFailAlloc_3375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3375_, 0, v_a_3369_);
v___x_3374_ = v_reuseFailAlloc_3375_;
goto v_reusejp_3373_;
}
v_reusejp_3373_:
{
return v___x_3374_;
}
}
}
}
else
{
lean_object* v_a_3377_; lean_object* v___x_3379_; uint8_t v_isShared_3380_; uint8_t v_isSharedCheck_3384_; 
lean_dec(v_ref_3343_);
lean_dec_ref(v_validate_3341_);
lean_dec(v_attrDescrs_3340_);
v_a_3377_ = lean_ctor_get(v___x_3355_, 0);
v_isSharedCheck_3384_ = !lean_is_exclusive(v___x_3355_);
if (v_isSharedCheck_3384_ == 0)
{
v___x_3379_ = v___x_3355_;
v_isShared_3380_ = v_isSharedCheck_3384_;
goto v_resetjp_3378_;
}
else
{
lean_inc(v_a_3377_);
lean_dec(v___x_3355_);
v___x_3379_ = lean_box(0);
v_isShared_3380_ = v_isSharedCheck_3384_;
goto v_resetjp_3378_;
}
v_resetjp_3378_:
{
lean_object* v___x_3382_; 
if (v_isShared_3380_ == 0)
{
v___x_3382_ = v___x_3379_;
goto v_reusejp_3381_;
}
else
{
lean_object* v_reuseFailAlloc_3383_; 
v_reuseFailAlloc_3383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3383_, 0, v_a_3377_);
v___x_3382_ = v_reuseFailAlloc_3383_;
goto v_reusejp_3381_;
}
v_reusejp_3381_:
{
return v___x_3382_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___boxed(lean_object* v_attrDescrs_3385_, lean_object* v_validate_3386_, lean_object* v_applicationTime_3387_, lean_object* v_ref_3388_, lean_object* v_a_3389_){
_start:
{
uint8_t v_applicationTime_boxed_3390_; lean_object* v_res_3391_; 
v_applicationTime_boxed_3390_ = lean_unbox(v_applicationTime_3387_);
v_res_3391_ = l_Lean_registerEnumAttributes___redArg(v_attrDescrs_3385_, v_validate_3386_, v_applicationTime_boxed_3390_, v_ref_3388_);
return v_res_3391_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes(lean_object* v_00_u03b1_3392_, lean_object* v_attrDescrs_3393_, lean_object* v_validate_3394_, uint8_t v_applicationTime_3395_, lean_object* v_ref_3396_){
_start:
{
lean_object* v___x_3398_; 
v___x_3398_ = l_Lean_registerEnumAttributes___redArg(v_attrDescrs_3393_, v_validate_3394_, v_applicationTime_3395_, v_ref_3396_);
return v___x_3398_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___boxed(lean_object* v_00_u03b1_3399_, lean_object* v_attrDescrs_3400_, lean_object* v_validate_3401_, lean_object* v_applicationTime_3402_, lean_object* v_ref_3403_, lean_object* v_a_3404_){
_start:
{
uint8_t v_applicationTime_boxed_3405_; lean_object* v_res_3406_; 
v_applicationTime_boxed_3405_ = lean_unbox(v_applicationTime_3402_);
v_res_3406_ = l_Lean_registerEnumAttributes(v_00_u03b1_3399_, v_attrDescrs_3400_, v_validate_3401_, v_applicationTime_boxed_3405_, v_ref_3403_);
return v_res_3406_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0(lean_object* v_00_u03b1_3407_, lean_object* v_env_3408_, lean_object* v_as_3409_, size_t v_i_3410_, size_t v_stop_3411_, lean_object* v_b_3412_){
_start:
{
lean_object* v___x_3413_; 
v___x_3413_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg(v_env_3408_, v_as_3409_, v_i_3410_, v_stop_3411_, v_b_3412_);
return v___x_3413_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___boxed(lean_object* v_00_u03b1_3414_, lean_object* v_env_3415_, lean_object* v_as_3416_, lean_object* v_i_3417_, lean_object* v_stop_3418_, lean_object* v_b_3419_){
_start:
{
size_t v_i_boxed_3420_; size_t v_stop_boxed_3421_; lean_object* v_res_3422_; 
v_i_boxed_3420_ = lean_unbox_usize(v_i_3417_);
lean_dec(v_i_3417_);
v_stop_boxed_3421_ = lean_unbox_usize(v_stop_3418_);
lean_dec(v_stop_3418_);
v_res_3422_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0(v_00_u03b1_3414_, v_env_3415_, v_as_3416_, v_i_boxed_3420_, v_stop_boxed_3421_, v_b_3419_);
lean_dec_ref(v_as_3416_);
return v_res_3422_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerEnumAttributes_spec__1(lean_object* v_00_u03b1_3423_, lean_object* v_newState_3424_, lean_object* v_x_3425_, lean_object* v_x_3426_){
_start:
{
lean_object* v___x_3427_; 
v___x_3427_ = l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___redArg(v_newState_3424_, v_x_3425_, v_x_3426_);
return v___x_3427_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___boxed(lean_object* v_00_u03b1_3428_, lean_object* v_newState_3429_, lean_object* v_x_3430_, lean_object* v_x_3431_){
_start:
{
lean_object* v_res_3432_; 
v_res_3432_ = l_List_foldl___at___00Lean_registerEnumAttributes_spec__1(v_00_u03b1_3428_, v_newState_3429_, v_x_3430_, v_x_3431_);
lean_dec(v_newState_3429_);
return v_res_3432_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2(lean_object* v_00_u03b1_3433_, lean_object* v_validate_3434_, lean_object* v_a_3435_, lean_object* v_ref_3436_, uint8_t v_applicationTime_3437_, lean_object* v_a_3438_, lean_object* v_a_3439_){
_start:
{
lean_object* v___x_3440_; 
v___x_3440_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg(v_validate_3434_, v_a_3435_, v_ref_3436_, v_applicationTime_3437_, v_a_3438_, v_a_3439_);
return v___x_3440_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___boxed(lean_object* v_00_u03b1_3441_, lean_object* v_validate_3442_, lean_object* v_a_3443_, lean_object* v_ref_3444_, lean_object* v_applicationTime_3445_, lean_object* v_a_3446_, lean_object* v_a_3447_){
_start:
{
uint8_t v_applicationTime_boxed_3448_; lean_object* v_res_3449_; 
v_applicationTime_boxed_3448_ = lean_unbox(v_applicationTime_3445_);
v_res_3449_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2(v_00_u03b1_3441_, v_validate_3442_, v_a_3443_, v_ref_3444_, v_applicationTime_boxed_3448_, v_a_3446_, v_a_3447_);
return v_res_3449_;
}
}
LEAN_EXPORT lean_object* l_Lean_EnumAttributes_getValue___redArg(lean_object* v_inst_3450_, lean_object* v_attr_3451_, lean_object* v_env_3452_, lean_object* v_decl_3453_){
_start:
{
lean_object* v___x_3454_; lean_object* v___x_3455_; 
v___x_3454_ = lean_box(1);
v___x_3455_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3452_, v_decl_3453_);
if (lean_obj_tag(v___x_3455_) == 0)
{
lean_object* v_ext_3456_; lean_object* v_toEnvExtension_3457_; lean_object* v_asyncMode_3458_; lean_object* v___x_3459_; lean_object* v___x_3460_; 
lean_dec(v_inst_3450_);
v_ext_3456_ = lean_ctor_get(v_attr_3451_, 1);
lean_inc_ref(v_ext_3456_);
lean_dec_ref(v_attr_3451_);
v_toEnvExtension_3457_ = lean_ctor_get(v_ext_3456_, 0);
v_asyncMode_3458_ = lean_ctor_get(v_toEnvExtension_3457_, 2);
lean_inc(v_asyncMode_3458_);
lean_inc(v_decl_3453_);
v___x_3459_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3454_, v_ext_3456_, v_env_3452_, v_asyncMode_3458_, v_decl_3453_);
lean_dec(v_asyncMode_3458_);
lean_dec_ref(v_ext_3456_);
v___x_3460_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_3459_, v_decl_3453_);
lean_dec(v_decl_3453_);
lean_dec(v___x_3459_);
return v___x_3460_;
}
else
{
lean_object* v_val_3461_; lean_object* v_ext_3462_; lean_object* v___x_3464_; uint8_t v_isShared_3465_; uint8_t v_isSharedCheck_3492_; 
v_val_3461_ = lean_ctor_get(v___x_3455_, 0);
lean_inc(v_val_3461_);
lean_dec_ref(v___x_3455_);
v_ext_3462_ = lean_ctor_get(v_attr_3451_, 1);
v_isSharedCheck_3492_ = !lean_is_exclusive(v_attr_3451_);
if (v_isSharedCheck_3492_ == 0)
{
lean_object* v_unused_3493_; 
v_unused_3493_ = lean_ctor_get(v_attr_3451_, 0);
lean_dec(v_unused_3493_);
v___x_3464_ = v_attr_3451_;
v_isShared_3465_ = v_isSharedCheck_3492_;
goto v_resetjp_3463_;
}
else
{
lean_inc(v_ext_3462_);
lean_dec(v_attr_3451_);
v___x_3464_ = lean_box(0);
v_isShared_3465_ = v_isSharedCheck_3492_;
goto v_resetjp_3463_;
}
v_resetjp_3463_:
{
uint8_t v___x_3466_; lean_object* v___x_3467_; lean_object* v___x_3468_; lean_object* v___x_3469_; uint8_t v___x_3470_; 
v___x_3466_ = 0;
v___x_3467_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_3454_, v_ext_3462_, v_env_3452_, v_val_3461_, v___x_3466_);
lean_dec(v_val_3461_);
lean_dec_ref(v_env_3452_);
lean_dec_ref(v_ext_3462_);
v___x_3468_ = lean_unsigned_to_nat(0u);
v___x_3469_ = lean_array_get_size(v___x_3467_);
v___x_3470_ = lean_nat_dec_lt(v___x_3468_, v___x_3469_);
if (v___x_3470_ == 0)
{
lean_object* v___x_3471_; 
lean_dec_ref(v___x_3467_);
lean_del_object(v___x_3464_);
lean_dec(v_decl_3453_);
lean_dec(v_inst_3450_);
v___x_3471_ = lean_box(0);
return v___x_3471_;
}
else
{
lean_object* v___x_3472_; lean_object* v___x_3473_; uint8_t v___x_3474_; 
v___x_3472_ = lean_unsigned_to_nat(1u);
v___x_3473_ = lean_nat_sub(v___x_3469_, v___x_3472_);
v___x_3474_ = lean_nat_dec_le(v___x_3468_, v___x_3473_);
if (v___x_3474_ == 0)
{
lean_object* v___x_3475_; 
lean_dec(v___x_3473_);
lean_dec_ref(v___x_3467_);
lean_del_object(v___x_3464_);
lean_dec(v_decl_3453_);
lean_dec(v_inst_3450_);
v___x_3475_ = lean_box(0);
return v___x_3475_;
}
else
{
lean_object* v___f_3476_; lean_object* v___x_3478_; 
v___f_3476_ = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2___redArg___closed__0));
if (v_isShared_3465_ == 0)
{
lean_ctor_set(v___x_3464_, 1, v_inst_3450_);
lean_ctor_set(v___x_3464_, 0, v_decl_3453_);
v___x_3478_ = v___x_3464_;
goto v_reusejp_3477_;
}
else
{
lean_object* v_reuseFailAlloc_3491_; 
v_reuseFailAlloc_3491_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3491_, 0, v_decl_3453_);
lean_ctor_set(v_reuseFailAlloc_3491_, 1, v_inst_3450_);
v___x_3478_ = v_reuseFailAlloc_3491_;
goto v_reusejp_3477_;
}
v_reusejp_3477_:
{
lean_object* v___x_3479_; lean_object* v___x_3480_; 
v___x_3479_ = ((lean_object*)(l_Lean_ParametricAttribute_getParam_x3f___redArg___closed__1));
v___x_3480_ = l_Array_binSearchAux___redArg(v___f_3476_, v___x_3479_, v___x_3467_, v___x_3478_, v___x_3468_, v___x_3473_);
lean_dec_ref(v___x_3467_);
if (lean_obj_tag(v___x_3480_) == 0)
{
lean_object* v___x_3481_; 
v___x_3481_ = lean_box(0);
return v___x_3481_;
}
else
{
lean_object* v_val_3482_; lean_object* v___x_3484_; uint8_t v_isShared_3485_; uint8_t v_isSharedCheck_3490_; 
v_val_3482_ = lean_ctor_get(v___x_3480_, 0);
v_isSharedCheck_3490_ = !lean_is_exclusive(v___x_3480_);
if (v_isSharedCheck_3490_ == 0)
{
v___x_3484_ = v___x_3480_;
v_isShared_3485_ = v_isSharedCheck_3490_;
goto v_resetjp_3483_;
}
else
{
lean_inc(v_val_3482_);
lean_dec(v___x_3480_);
v___x_3484_ = lean_box(0);
v_isShared_3485_ = v_isSharedCheck_3490_;
goto v_resetjp_3483_;
}
v_resetjp_3483_:
{
lean_object* v_snd_3486_; lean_object* v___x_3488_; 
v_snd_3486_ = lean_ctor_get(v_val_3482_, 1);
lean_inc(v_snd_3486_);
lean_dec(v_val_3482_);
if (v_isShared_3485_ == 0)
{
lean_ctor_set(v___x_3484_, 0, v_snd_3486_);
v___x_3488_ = v___x_3484_;
goto v_reusejp_3487_;
}
else
{
lean_object* v_reuseFailAlloc_3489_; 
v_reuseFailAlloc_3489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3489_, 0, v_snd_3486_);
v___x_3488_ = v_reuseFailAlloc_3489_;
goto v_reusejp_3487_;
}
v_reusejp_3487_:
{
return v___x_3488_;
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
LEAN_EXPORT lean_object* l_Lean_EnumAttributes_getValue(lean_object* v_00_u03b1_3494_, lean_object* v_inst_3495_, lean_object* v_attr_3496_, lean_object* v_env_3497_, lean_object* v_decl_3498_){
_start:
{
lean_object* v___x_3499_; 
v___x_3499_ = l_Lean_EnumAttributes_getValue___redArg(v_inst_3495_, v_attr_3496_, v_env_3497_, v_decl_3498_);
return v___x_3499_;
}
}
LEAN_EXPORT lean_object* l_Lean_EnumAttributes_setValue___redArg(lean_object* v_attrs_3508_, lean_object* v_env_3509_, lean_object* v_decl_3510_, lean_object* v_val_3511_){
_start:
{
lean_object* v_ext_3512_; lean_object* v___x_3514_; uint8_t v_isShared_3515_; uint8_t v_isSharedCheck_3576_; 
v_ext_3512_ = lean_ctor_get(v_attrs_3508_, 1);
v_isSharedCheck_3576_ = !lean_is_exclusive(v_attrs_3508_);
if (v_isSharedCheck_3576_ == 0)
{
lean_object* v_unused_3577_; 
v_unused_3577_ = lean_ctor_get(v_attrs_3508_, 0);
lean_dec(v_unused_3577_);
v___x_3514_ = v_attrs_3508_;
v_isShared_3515_ = v_isSharedCheck_3576_;
goto v_resetjp_3513_;
}
else
{
lean_inc(v_ext_3512_);
lean_dec(v_attrs_3508_);
v___x_3514_ = lean_box(0);
v_isShared_3515_ = v_isSharedCheck_3576_;
goto v_resetjp_3513_;
}
v_resetjp_3513_:
{
lean_object* v_toEnvExtension_3516_; lean_object* v_name_3517_; lean_object* v___x_3518_; uint8_t v___x_3519_; lean_object* v___x_3520_; lean_object* v___x_3521_; lean_object* v___x_3522_; lean_object* v___x_3523_; lean_object* v___x_3524_; lean_object* v___x_3525_; lean_object* v___x_3526_; lean_object* v_pfx_3527_; lean_object* v___x_3528_; 
v_toEnvExtension_3516_ = lean_ctor_get(v_ext_3512_, 0);
v_name_3517_ = lean_ctor_get(v_ext_3512_, 1);
v___x_3518_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__0));
v___x_3519_ = 1;
lean_inc(v_name_3517_);
v___x_3520_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_3517_, v___x_3519_);
v___x_3521_ = lean_string_append(v___x_3518_, v___x_3520_);
lean_dec_ref(v___x_3520_);
v___x_3522_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__1));
v___x_3523_ = lean_string_append(v___x_3521_, v___x_3522_);
lean_inc(v_decl_3510_);
v___x_3524_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_decl_3510_, v___x_3519_);
v___x_3525_ = lean_string_append(v___x_3523_, v___x_3524_);
lean_dec_ref(v___x_3524_);
v___x_3526_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__4));
v_pfx_3527_ = lean_string_append(v___x_3525_, v___x_3526_);
v___x_3528_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3509_, v_decl_3510_);
if (lean_obj_tag(v___x_3528_) == 0)
{
lean_object* v_asyncMode_3529_; uint8_t v___x_3536_; 
v_asyncMode_3529_ = lean_ctor_get(v_toEnvExtension_3516_, 2);
lean_inc(v_asyncMode_3529_);
lean_inc(v_decl_3510_);
lean_inc_ref(v_env_3509_);
v___x_3536_ = l_Lean_EnvExtension_asyncMayModify___redArg(v_env_3509_, v_decl_3510_, v_asyncMode_3529_);
if (v___x_3536_ == 0)
{
lean_object* v___x_3537_; lean_object* v___x_3538_; lean_object* v___y_3540_; lean_object* v___x_3544_; 
lean_dec(v_asyncMode_3529_);
lean_del_object(v___x_3514_);
lean_dec_ref(v_ext_3512_);
lean_dec(v_val_3511_);
lean_dec(v_decl_3510_);
v___x_3537_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__2));
v___x_3538_ = lean_string_append(v_pfx_3527_, v___x_3537_);
v___x_3544_ = l_Lean_Environment_asyncPrefix_x3f(v_env_3509_);
if (lean_obj_tag(v___x_3544_) == 0)
{
lean_object* v___x_3545_; 
v___x_3545_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__3));
v___y_3540_ = v___x_3545_;
goto v___jp_3539_;
}
else
{
lean_object* v_val_3546_; lean_object* v___x_3547_; lean_object* v___x_3548_; lean_object* v___x_3549_; lean_object* v___x_3550_; lean_object* v___x_3551_; lean_object* v___x_3552_; 
v_val_3546_ = lean_ctor_get(v___x_3544_, 0);
lean_inc(v_val_3546_);
lean_dec_ref(v___x_3544_);
v___x_3547_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__4));
v___x_3548_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_val_3546_, v___x_3519_);
v___x_3549_ = l_addParenHeuristic(v___x_3548_);
v___x_3550_ = lean_string_append(v___x_3547_, v___x_3549_);
lean_dec_ref(v___x_3549_);
v___x_3551_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__5));
v___x_3552_ = lean_string_append(v___x_3550_, v___x_3551_);
v___y_3540_ = v___x_3552_;
goto v___jp_3539_;
}
v___jp_3539_:
{
lean_object* v___x_3541_; lean_object* v___x_3542_; lean_object* v___x_3543_; 
v___x_3541_ = lean_string_append(v___x_3538_, v___y_3540_);
lean_dec_ref(v___y_3540_);
v___x_3542_ = lean_string_append(v___x_3541_, v___x_3526_);
v___x_3543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3543_, 0, v___x_3542_);
return v___x_3543_;
}
}
else
{
lean_object* v___x_3553_; lean_object* v___x_3554_; lean_object* v___x_3555_; 
v___x_3553_ = lean_box(1);
lean_inc(v_decl_3510_);
lean_inc_ref(v_env_3509_);
v___x_3554_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3553_, v_ext_3512_, v_env_3509_, v_asyncMode_3529_, v_decl_3510_);
v___x_3555_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_3554_, v_decl_3510_);
lean_dec(v___x_3554_);
if (lean_obj_tag(v___x_3555_) == 0)
{
lean_dec_ref(v_pfx_3527_);
goto v___jp_3530_;
}
else
{
lean_object* v___x_3557_; uint8_t v_isShared_3558_; uint8_t v_isSharedCheck_3564_; 
v_isSharedCheck_3564_ = !lean_is_exclusive(v___x_3555_);
if (v_isSharedCheck_3564_ == 0)
{
lean_object* v_unused_3565_; 
v_unused_3565_ = lean_ctor_get(v___x_3555_, 0);
lean_dec(v_unused_3565_);
v___x_3557_ = v___x_3555_;
v_isShared_3558_ = v_isSharedCheck_3564_;
goto v_resetjp_3556_;
}
else
{
lean_dec(v___x_3555_);
v___x_3557_ = lean_box(0);
v_isShared_3558_ = v_isSharedCheck_3564_;
goto v_resetjp_3556_;
}
v_resetjp_3556_:
{
if (v___x_3536_ == 0)
{
lean_del_object(v___x_3557_);
lean_dec_ref(v_pfx_3527_);
goto v___jp_3530_;
}
else
{
lean_object* v___x_3559_; lean_object* v___x_3560_; lean_object* v___x_3562_; 
lean_dec(v_asyncMode_3529_);
lean_del_object(v___x_3514_);
lean_dec_ref(v_ext_3512_);
lean_dec(v_val_3511_);
lean_dec(v_decl_3510_);
lean_dec_ref(v_env_3509_);
v___x_3559_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__6));
v___x_3560_ = lean_string_append(v_pfx_3527_, v___x_3559_);
if (v_isShared_3558_ == 0)
{
lean_ctor_set_tag(v___x_3557_, 0);
lean_ctor_set(v___x_3557_, 0, v___x_3560_);
v___x_3562_ = v___x_3557_;
goto v_reusejp_3561_;
}
else
{
lean_object* v_reuseFailAlloc_3563_; 
v_reuseFailAlloc_3563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3563_, 0, v___x_3560_);
v___x_3562_ = v_reuseFailAlloc_3563_;
goto v_reusejp_3561_;
}
v_reusejp_3561_:
{
return v___x_3562_;
}
}
}
}
}
v___jp_3530_:
{
lean_object* v___x_3532_; 
lean_inc(v_decl_3510_);
if (v_isShared_3515_ == 0)
{
lean_ctor_set(v___x_3514_, 1, v_val_3511_);
lean_ctor_set(v___x_3514_, 0, v_decl_3510_);
v___x_3532_ = v___x_3514_;
goto v_reusejp_3531_;
}
else
{
lean_object* v_reuseFailAlloc_3535_; 
v_reuseFailAlloc_3535_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3535_, 0, v_decl_3510_);
lean_ctor_set(v_reuseFailAlloc_3535_, 1, v_val_3511_);
v___x_3532_ = v_reuseFailAlloc_3535_;
goto v_reusejp_3531_;
}
v_reusejp_3531_:
{
lean_object* v___x_3533_; lean_object* v___x_3534_; 
v___x_3533_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_ext_3512_, v_env_3509_, v___x_3532_, v_asyncMode_3529_, v_decl_3510_);
lean_dec(v_asyncMode_3529_);
v___x_3534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3534_, 0, v___x_3533_);
return v___x_3534_;
}
}
}
else
{
lean_object* v___x_3567_; uint8_t v_isShared_3568_; uint8_t v_isSharedCheck_3574_; 
lean_del_object(v___x_3514_);
lean_dec_ref(v_ext_3512_);
lean_dec(v_val_3511_);
lean_dec(v_decl_3510_);
lean_dec_ref(v_env_3509_);
v_isSharedCheck_3574_ = !lean_is_exclusive(v___x_3528_);
if (v_isSharedCheck_3574_ == 0)
{
lean_object* v_unused_3575_; 
v_unused_3575_ = lean_ctor_get(v___x_3528_, 0);
lean_dec(v_unused_3575_);
v___x_3567_ = v___x_3528_;
v_isShared_3568_ = v_isSharedCheck_3574_;
goto v_resetjp_3566_;
}
else
{
lean_dec(v___x_3528_);
v___x_3567_ = lean_box(0);
v_isShared_3568_ = v_isSharedCheck_3574_;
goto v_resetjp_3566_;
}
v_resetjp_3566_:
{
lean_object* v___x_3569_; lean_object* v___x_3570_; lean_object* v___x_3572_; 
v___x_3569_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__7));
v___x_3570_ = lean_string_append(v_pfx_3527_, v___x_3569_);
if (v_isShared_3568_ == 0)
{
lean_ctor_set_tag(v___x_3567_, 0);
lean_ctor_set(v___x_3567_, 0, v___x_3570_);
v___x_3572_ = v___x_3567_;
goto v_reusejp_3571_;
}
else
{
lean_object* v_reuseFailAlloc_3573_; 
v_reuseFailAlloc_3573_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3573_, 0, v___x_3570_);
v___x_3572_ = v_reuseFailAlloc_3573_;
goto v_reusejp_3571_;
}
v_reusejp_3571_:
{
return v___x_3572_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_EnumAttributes_setValue(lean_object* v_00_u03b1_3578_, lean_object* v_attrs_3579_, lean_object* v_env_3580_, lean_object* v_decl_3581_, lean_object* v_val_3582_){
_start:
{
lean_object* v___x_3583_; 
v___x_3583_ = l_Lean_EnumAttributes_setValue___redArg(v_attrs_3579_, v_env_3580_, v_decl_3581_, v_val_3582_);
return v___x_3583_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_Attributes_2990505691____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3585_; lean_object* v___x_3586_; lean_object* v___x_3587_; 
v___x_3585_ = lean_obj_once(&l_Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_, &l_Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2__once, _init_l_Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_);
v___x_3586_ = lean_st_mk_ref(v___x_3585_);
v___x_3587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3587_, 0, v___x_3586_);
return v___x_3587_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_Attributes_2990505691____hygCtx___hyg_2____boxed(lean_object* v_a_3588_){
_start:
{
lean_object* v_res_3589_; 
v_res_3589_ = l_Lean_initFn_00___x40_Lean_Attributes_2990505691____hygCtx___hyg_2_();
return v_res_3589_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerAttributeImplBuilder(lean_object* v_builderId_3592_, lean_object* v_builder_3593_){
_start:
{
lean_object* v___x_3595_; lean_object* v___x_3596_; uint8_t v___x_3597_; 
v___x_3595_ = l_Lean_attributeImplBuilderTableRef;
v___x_3596_ = lean_st_ref_get(v___x_3595_);
v___x_3597_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(v___x_3596_, v_builderId_3592_);
lean_dec(v___x_3596_);
if (v___x_3597_ == 0)
{
lean_object* v___x_3598_; lean_object* v___x_3599_; lean_object* v___x_3600_; lean_object* v___x_3601_; 
v___x_3598_ = lean_st_ref_take(v___x_3595_);
v___x_3599_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1___redArg(v___x_3598_, v_builderId_3592_, v_builder_3593_);
v___x_3600_ = lean_st_ref_set(v___x_3595_, v___x_3599_);
v___x_3601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3601_, 0, v___x_3600_);
return v___x_3601_;
}
else
{
lean_object* v___x_3602_; lean_object* v___x_3603_; lean_object* v___x_3604_; lean_object* v___x_3605_; lean_object* v___x_3606_; lean_object* v___x_3607_; lean_object* v___x_3608_; 
lean_dec_ref(v_builder_3593_);
v___x_3602_ = ((lean_object*)(l_Lean_registerAttributeImplBuilder___closed__0));
v___x_3603_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_builderId_3592_, v___x_3597_);
v___x_3604_ = lean_string_append(v___x_3602_, v___x_3603_);
lean_dec_ref(v___x_3603_);
v___x_3605_ = ((lean_object*)(l_Lean_registerAttributeImplBuilder___closed__1));
v___x_3606_ = lean_string_append(v___x_3604_, v___x_3605_);
v___x_3607_ = lean_mk_io_user_error(v___x_3606_);
v___x_3608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3608_, 0, v___x_3607_);
return v___x_3608_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerAttributeImplBuilder___boxed(lean_object* v_builderId_3609_, lean_object* v_builder_3610_, lean_object* v_a_3611_){
_start:
{
lean_object* v_res_3612_; 
v_res_3612_ = l_Lean_registerAttributeImplBuilder(v_builderId_3609_, v_builder_3610_);
return v_res_3612_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___redArg(lean_object* v_e_3613_){
_start:
{
if (lean_obj_tag(v_e_3613_) == 0)
{
lean_object* v_a_3615_; lean_object* v___x_3617_; uint8_t v_isShared_3618_; uint8_t v_isSharedCheck_3623_; 
v_a_3615_ = lean_ctor_get(v_e_3613_, 0);
v_isSharedCheck_3623_ = !lean_is_exclusive(v_e_3613_);
if (v_isSharedCheck_3623_ == 0)
{
v___x_3617_ = v_e_3613_;
v_isShared_3618_ = v_isSharedCheck_3623_;
goto v_resetjp_3616_;
}
else
{
lean_inc(v_a_3615_);
lean_dec(v_e_3613_);
v___x_3617_ = lean_box(0);
v_isShared_3618_ = v_isSharedCheck_3623_;
goto v_resetjp_3616_;
}
v_resetjp_3616_:
{
lean_object* v___x_3619_; lean_object* v___x_3621_; 
v___x_3619_ = lean_mk_io_user_error(v_a_3615_);
if (v_isShared_3618_ == 0)
{
lean_ctor_set_tag(v___x_3617_, 1);
lean_ctor_set(v___x_3617_, 0, v___x_3619_);
v___x_3621_ = v___x_3617_;
goto v_reusejp_3620_;
}
else
{
lean_object* v_reuseFailAlloc_3622_; 
v_reuseFailAlloc_3622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3622_, 0, v___x_3619_);
v___x_3621_ = v_reuseFailAlloc_3622_;
goto v_reusejp_3620_;
}
v_reusejp_3620_:
{
return v___x_3621_;
}
}
}
else
{
lean_object* v_a_3624_; lean_object* v___x_3626_; uint8_t v_isShared_3627_; uint8_t v_isSharedCheck_3631_; 
v_a_3624_ = lean_ctor_get(v_e_3613_, 0);
v_isSharedCheck_3631_ = !lean_is_exclusive(v_e_3613_);
if (v_isSharedCheck_3631_ == 0)
{
v___x_3626_ = v_e_3613_;
v_isShared_3627_ = v_isSharedCheck_3631_;
goto v_resetjp_3625_;
}
else
{
lean_inc(v_a_3624_);
lean_dec(v_e_3613_);
v___x_3626_ = lean_box(0);
v_isShared_3627_ = v_isSharedCheck_3631_;
goto v_resetjp_3625_;
}
v_resetjp_3625_:
{
lean_object* v___x_3629_; 
if (v_isShared_3627_ == 0)
{
lean_ctor_set_tag(v___x_3626_, 0);
v___x_3629_ = v___x_3626_;
goto v_reusejp_3628_;
}
else
{
lean_object* v_reuseFailAlloc_3630_; 
v_reuseFailAlloc_3630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3630_, 0, v_a_3624_);
v___x_3629_ = v_reuseFailAlloc_3630_;
goto v_reusejp_3628_;
}
v_reusejp_3628_:
{
return v___x_3629_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___redArg___boxed(lean_object* v_e_3632_, lean_object* v_a_3633_){
_start:
{
lean_object* v_res_3634_; 
v_res_3634_ = l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___redArg(v_e_3632_);
return v_res_3634_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1(lean_object* v_00_u03b1_3635_, lean_object* v_e_3636_){
_start:
{
lean_object* v___x_3638_; 
v___x_3638_ = l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___redArg(v_e_3636_);
return v___x_3638_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___boxed(lean_object* v_00_u03b1_3639_, lean_object* v_e_3640_, lean_object* v_a_3641_){
_start:
{
lean_object* v_res_3642_; 
v_res_3642_ = l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1(v_00_u03b1_3639_, v_e_3640_);
return v_res_3642_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___redArg(lean_object* v_a_3643_, lean_object* v_x_3644_){
_start:
{
if (lean_obj_tag(v_x_3644_) == 0)
{
lean_object* v___x_3645_; 
v___x_3645_ = lean_box(0);
return v___x_3645_;
}
else
{
lean_object* v_key_3646_; lean_object* v_value_3647_; lean_object* v_tail_3648_; uint8_t v___x_3649_; 
v_key_3646_ = lean_ctor_get(v_x_3644_, 0);
v_value_3647_ = lean_ctor_get(v_x_3644_, 1);
v_tail_3648_ = lean_ctor_get(v_x_3644_, 2);
v___x_3649_ = lean_name_eq(v_key_3646_, v_a_3643_);
if (v___x_3649_ == 0)
{
v_x_3644_ = v_tail_3648_;
goto _start;
}
else
{
lean_object* v___x_3651_; 
lean_inc(v_value_3647_);
v___x_3651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3651_, 0, v_value_3647_);
return v___x_3651_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___redArg___boxed(lean_object* v_a_3652_, lean_object* v_x_3653_){
_start:
{
lean_object* v_res_3654_; 
v_res_3654_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___redArg(v_a_3652_, v_x_3653_);
lean_dec(v_x_3653_);
lean_dec(v_a_3652_);
return v_res_3654_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(lean_object* v_m_3655_, lean_object* v_a_3656_){
_start:
{
lean_object* v_buckets_3657_; lean_object* v___x_3658_; uint64_t v___y_3660_; 
v_buckets_3657_ = lean_ctor_get(v_m_3655_, 1);
v___x_3658_ = lean_array_get_size(v_buckets_3657_);
if (lean_obj_tag(v_a_3656_) == 0)
{
uint64_t v___x_3674_; 
v___x_3674_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg___closed__0);
v___y_3660_ = v___x_3674_;
goto v___jp_3659_;
}
else
{
uint64_t v_hash_3675_; 
v_hash_3675_ = lean_ctor_get_uint64(v_a_3656_, sizeof(void*)*2);
v___y_3660_ = v_hash_3675_;
goto v___jp_3659_;
}
v___jp_3659_:
{
uint64_t v___x_3661_; uint64_t v___x_3662_; uint64_t v_fold_3663_; uint64_t v___x_3664_; uint64_t v___x_3665_; uint64_t v___x_3666_; size_t v___x_3667_; size_t v___x_3668_; size_t v___x_3669_; size_t v___x_3670_; size_t v___x_3671_; lean_object* v___x_3672_; lean_object* v___x_3673_; 
v___x_3661_ = 32ULL;
v___x_3662_ = lean_uint64_shift_right(v___y_3660_, v___x_3661_);
v_fold_3663_ = lean_uint64_xor(v___y_3660_, v___x_3662_);
v___x_3664_ = 16ULL;
v___x_3665_ = lean_uint64_shift_right(v_fold_3663_, v___x_3664_);
v___x_3666_ = lean_uint64_xor(v_fold_3663_, v___x_3665_);
v___x_3667_ = lean_uint64_to_usize(v___x_3666_);
v___x_3668_ = lean_usize_of_nat(v___x_3658_);
v___x_3669_ = ((size_t)1ULL);
v___x_3670_ = lean_usize_sub(v___x_3668_, v___x_3669_);
v___x_3671_ = lean_usize_land(v___x_3667_, v___x_3670_);
v___x_3672_ = lean_array_uget_borrowed(v_buckets_3657_, v___x_3671_);
v___x_3673_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___redArg(v_a_3656_, v___x_3672_);
return v___x_3673_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg___boxed(lean_object* v_m_3676_, lean_object* v_a_3677_){
_start:
{
lean_object* v_res_3678_; 
v_res_3678_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(v_m_3676_, v_a_3677_);
lean_dec(v_a_3677_);
lean_dec_ref(v_m_3676_);
return v_res_3678_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAttributeImplOfEntry(lean_object* v_e_3680_){
_start:
{
lean_object* v___x_3682_; lean_object* v___x_3683_; lean_object* v_builderId_3684_; lean_object* v_ref_3685_; lean_object* v_args_3686_; lean_object* v___x_3687_; 
v___x_3682_ = l_Lean_attributeImplBuilderTableRef;
v___x_3683_ = lean_st_ref_get(v___x_3682_);
v_builderId_3684_ = lean_ctor_get(v_e_3680_, 0);
lean_inc(v_builderId_3684_);
v_ref_3685_ = lean_ctor_get(v_e_3680_, 1);
lean_inc(v_ref_3685_);
v_args_3686_ = lean_ctor_get(v_e_3680_, 2);
lean_inc(v_args_3686_);
lean_dec_ref(v_e_3680_);
v___x_3687_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(v___x_3683_, v_builderId_3684_);
lean_dec(v___x_3683_);
if (lean_obj_tag(v___x_3687_) == 0)
{
lean_object* v___x_3688_; uint8_t v___x_3689_; lean_object* v___x_3690_; lean_object* v___x_3691_; lean_object* v___x_3692_; lean_object* v___x_3693_; lean_object* v___x_3694_; lean_object* v___x_3695_; 
lean_dec(v_args_3686_);
lean_dec(v_ref_3685_);
v___x_3688_ = ((lean_object*)(l_Lean_mkAttributeImplOfEntry___closed__0));
v___x_3689_ = 1;
v___x_3690_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_builderId_3684_, v___x_3689_);
v___x_3691_ = lean_string_append(v___x_3688_, v___x_3690_);
lean_dec_ref(v___x_3690_);
v___x_3692_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__4));
v___x_3693_ = lean_string_append(v___x_3691_, v___x_3692_);
v___x_3694_ = lean_mk_io_user_error(v___x_3693_);
v___x_3695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3695_, 0, v___x_3694_);
return v___x_3695_;
}
else
{
lean_object* v_val_3696_; lean_object* v___x_3697_; lean_object* v___x_3698_; 
lean_dec(v_builderId_3684_);
v_val_3696_ = lean_ctor_get(v___x_3687_, 0);
lean_inc(v_val_3696_);
lean_dec_ref(v___x_3687_);
v___x_3697_ = lean_apply_2(v_val_3696_, v_ref_3685_, v_args_3686_);
v___x_3698_ = l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___redArg(v___x_3697_);
return v___x_3698_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkAttributeImplOfEntry___boxed(lean_object* v_e_3699_, lean_object* v_a_3700_){
_start:
{
lean_object* v_res_3701_; 
v_res_3701_ = l_Lean_mkAttributeImplOfEntry(v_e_3699_);
return v_res_3701_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0(lean_object* v_00_u03b2_3702_, lean_object* v_m_3703_, lean_object* v_a_3704_){
_start:
{
lean_object* v___x_3705_; 
v___x_3705_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(v_m_3703_, v_a_3704_);
return v___x_3705_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___boxed(lean_object* v_00_u03b2_3706_, lean_object* v_m_3707_, lean_object* v_a_3708_){
_start:
{
lean_object* v_res_3709_; 
v_res_3709_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0(v_00_u03b2_3706_, v_m_3707_, v_a_3708_);
lean_dec(v_a_3708_);
lean_dec_ref(v_m_3707_);
return v_res_3709_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0(lean_object* v_00_u03b2_3710_, lean_object* v_a_3711_, lean_object* v_x_3712_){
_start:
{
lean_object* v___x_3713_; 
v___x_3713_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___redArg(v_a_3711_, v_x_3712_);
return v___x_3713_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3714_, lean_object* v_a_3715_, lean_object* v_x_3716_){
_start:
{
lean_object* v_res_3717_; 
v_res_3717_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0(v_00_u03b2_3714_, v_a_3715_, v_x_3716_);
lean_dec(v_x_3716_);
lean_dec(v_a_3715_);
return v_res_3717_;
}
}
static lean_object* _init_l_Lean_instInhabitedAttributeExtensionState_default___closed__0(void){
_start:
{
lean_object* v___x_3718_; lean_object* v___x_3719_; lean_object* v___x_3720_; 
v___x_3718_ = lean_obj_once(&l_Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_, &l_Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2__once, _init_l_Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_);
v___x_3719_ = lean_box(0);
v___x_3720_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3720_, 0, v___x_3719_);
lean_ctor_set(v___x_3720_, 1, v___x_3718_);
return v___x_3720_;
}
}
static lean_object* _init_l_Lean_instInhabitedAttributeExtensionState_default(void){
_start:
{
lean_object* v___x_3721_; 
v___x_3721_ = lean_obj_once(&l_Lean_instInhabitedAttributeExtensionState_default___closed__0, &l_Lean_instInhabitedAttributeExtensionState_default___closed__0_once, _init_l_Lean_instInhabitedAttributeExtensionState_default___closed__0);
return v___x_3721_;
}
}
static lean_object* _init_l_Lean_instInhabitedAttributeExtensionState(void){
_start:
{
lean_object* v___x_3722_; 
v___x_3722_ = l_Lean_instInhabitedAttributeExtensionState_default;
return v___x_3722_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_AttributeExtension_mkInitial(){
_start:
{
lean_object* v___x_3724_; lean_object* v___x_3725_; lean_object* v___x_3726_; lean_object* v___x_3727_; lean_object* v___x_3728_; 
v___x_3724_ = l_Lean_attributeMapRef;
v___x_3725_ = lean_st_ref_get(v___x_3724_);
v___x_3726_ = lean_box(0);
v___x_3727_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3727_, 0, v___x_3726_);
lean_ctor_set(v___x_3727_, 1, v___x_3725_);
v___x_3728_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3728_, 0, v___x_3727_);
return v___x_3728_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_AttributeExtension_mkInitial___boxed(lean_object* v_a_3729_){
_start:
{
lean_object* v_res_3730_; 
v_res_3730_ = l___private_Lean_Attributes_0__Lean_AttributeExtension_mkInitial();
return v_res_3730_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAttributeImplOfConstantUnsafe(lean_object* v_env_3736_, lean_object* v_opts_3737_, lean_object* v_declName_3738_){
_start:
{
uint8_t v___x_3741_; lean_object* v___x_3742_; 
v___x_3741_ = 0;
lean_inc(v_declName_3738_);
lean_inc_ref(v_env_3736_);
v___x_3742_ = l_Lean_Environment_find_x3f(v_env_3736_, v_declName_3738_, v___x_3741_);
if (lean_obj_tag(v___x_3742_) == 0)
{
lean_object* v___x_3743_; uint8_t v___x_3744_; lean_object* v___x_3745_; lean_object* v___x_3746_; lean_object* v___x_3747_; lean_object* v___x_3748_; lean_object* v___x_3749_; 
lean_dec_ref(v_env_3736_);
v___x_3743_ = ((lean_object*)(l_Lean_mkAttributeImplOfConstantUnsafe___closed__2));
v___x_3744_ = 1;
v___x_3745_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_declName_3738_, v___x_3744_);
v___x_3746_ = lean_string_append(v___x_3743_, v___x_3745_);
lean_dec_ref(v___x_3745_);
v___x_3747_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__4));
v___x_3748_ = lean_string_append(v___x_3746_, v___x_3747_);
v___x_3749_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3749_, 0, v___x_3748_);
return v___x_3749_;
}
else
{
lean_object* v_val_3750_; lean_object* v___x_3751_; 
v_val_3750_ = lean_ctor_get(v___x_3742_, 0);
lean_inc(v_val_3750_);
lean_dec_ref(v___x_3742_);
v___x_3751_ = l_Lean_ConstantInfo_type(v_val_3750_);
lean_dec(v_val_3750_);
if (lean_obj_tag(v___x_3751_) == 4)
{
lean_object* v_declName_3752_; 
v_declName_3752_ = lean_ctor_get(v___x_3751_, 0);
lean_inc(v_declName_3752_);
lean_dec_ref(v___x_3751_);
if (lean_obj_tag(v_declName_3752_) == 1)
{
lean_object* v_pre_3753_; 
v_pre_3753_ = lean_ctor_get(v_declName_3752_, 0);
lean_inc(v_pre_3753_);
if (lean_obj_tag(v_pre_3753_) == 1)
{
lean_object* v_pre_3754_; 
v_pre_3754_ = lean_ctor_get(v_pre_3753_, 0);
if (lean_obj_tag(v_pre_3754_) == 0)
{
lean_object* v_str_3755_; lean_object* v_str_3756_; lean_object* v___x_3757_; uint8_t v___x_3758_; 
v_str_3755_ = lean_ctor_get(v_declName_3752_, 1);
lean_inc_ref(v_str_3755_);
lean_dec_ref(v_declName_3752_);
v_str_3756_ = lean_ctor_get(v_pre_3753_, 1);
lean_inc_ref(v_str_3756_);
lean_dec_ref(v_pre_3753_);
v___x_3757_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__0));
v___x_3758_ = lean_string_dec_eq(v_str_3756_, v___x_3757_);
lean_dec_ref(v_str_3756_);
if (v___x_3758_ == 0)
{
lean_dec_ref(v_str_3755_);
lean_dec(v_declName_3738_);
lean_dec_ref(v_env_3736_);
goto v___jp_3739_;
}
else
{
lean_object* v___x_3759_; uint8_t v___x_3760_; 
v___x_3759_ = ((lean_object*)(l_Lean_mkAttributeImplOfConstantUnsafe___closed__3));
v___x_3760_ = lean_string_dec_eq(v_str_3755_, v___x_3759_);
lean_dec_ref(v_str_3755_);
if (v___x_3760_ == 0)
{
lean_dec(v_declName_3738_);
lean_dec_ref(v_env_3736_);
goto v___jp_3739_;
}
else
{
lean_object* v___x_3761_; 
v___x_3761_ = l_Lean_Environment_evalConst___redArg(v_env_3736_, v_opts_3737_, v_declName_3738_, v___x_3760_);
lean_dec(v_declName_3738_);
lean_dec_ref(v_env_3736_);
return v___x_3761_;
}
}
}
else
{
lean_dec_ref(v_pre_3753_);
lean_dec_ref(v_declName_3752_);
lean_dec(v_declName_3738_);
lean_dec_ref(v_env_3736_);
goto v___jp_3739_;
}
}
else
{
lean_dec(v_pre_3753_);
lean_dec_ref(v_declName_3752_);
lean_dec(v_declName_3738_);
lean_dec_ref(v_env_3736_);
goto v___jp_3739_;
}
}
else
{
lean_dec(v_declName_3752_);
lean_dec(v_declName_3738_);
lean_dec_ref(v_env_3736_);
goto v___jp_3739_;
}
}
else
{
lean_dec_ref(v___x_3751_);
lean_dec(v_declName_3738_);
lean_dec_ref(v_env_3736_);
goto v___jp_3739_;
}
}
v___jp_3739_:
{
lean_object* v___x_3740_; 
v___x_3740_ = ((lean_object*)(l_Lean_mkAttributeImplOfConstantUnsafe___closed__1));
return v___x_3740_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkAttributeImplOfConstantUnsafe___boxed(lean_object* v_env_3762_, lean_object* v_opts_3763_, lean_object* v_declName_3764_){
_start:
{
lean_object* v_res_3765_; 
v_res_3765_ = l_Lean_mkAttributeImplOfConstantUnsafe(v_env_3762_, v_opts_3763_, v_declName_3764_);
lean_dec_ref(v_opts_3763_);
return v_res_3765_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg(lean_object* v_as_3766_, size_t v_i_3767_, size_t v_stop_3768_, lean_object* v_b_3769_){
_start:
{
uint8_t v___x_3771_; 
v___x_3771_ = lean_usize_dec_eq(v_i_3767_, v_stop_3768_);
if (v___x_3771_ == 0)
{
lean_object* v___x_3772_; lean_object* v___x_3773_; 
v___x_3772_ = lean_array_uget_borrowed(v_as_3766_, v_i_3767_);
lean_inc(v___x_3772_);
v___x_3773_ = l_Lean_mkAttributeImplOfEntry(v___x_3772_);
if (lean_obj_tag(v___x_3773_) == 0)
{
lean_object* v_a_3774_; lean_object* v_toAttributeImplCore_3775_; lean_object* v_name_3776_; lean_object* v___x_3777_; size_t v___x_3778_; size_t v___x_3779_; 
v_a_3774_ = lean_ctor_get(v___x_3773_, 0);
lean_inc(v_a_3774_);
lean_dec_ref(v___x_3773_);
v_toAttributeImplCore_3775_ = lean_ctor_get(v_a_3774_, 0);
v_name_3776_ = lean_ctor_get(v_toAttributeImplCore_3775_, 1);
lean_inc(v_name_3776_);
v___x_3777_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1___redArg(v_b_3769_, v_name_3776_, v_a_3774_);
v___x_3778_ = ((size_t)1ULL);
v___x_3779_ = lean_usize_add(v_i_3767_, v___x_3778_);
v_i_3767_ = v___x_3779_;
v_b_3769_ = v___x_3777_;
goto _start;
}
else
{
lean_object* v_a_3781_; lean_object* v___x_3783_; uint8_t v_isShared_3784_; uint8_t v_isSharedCheck_3788_; 
lean_dec_ref(v_b_3769_);
v_a_3781_ = lean_ctor_get(v___x_3773_, 0);
v_isSharedCheck_3788_ = !lean_is_exclusive(v___x_3773_);
if (v_isSharedCheck_3788_ == 0)
{
v___x_3783_ = v___x_3773_;
v_isShared_3784_ = v_isSharedCheck_3788_;
goto v_resetjp_3782_;
}
else
{
lean_inc(v_a_3781_);
lean_dec(v___x_3773_);
v___x_3783_ = lean_box(0);
v_isShared_3784_ = v_isSharedCheck_3788_;
goto v_resetjp_3782_;
}
v_resetjp_3782_:
{
lean_object* v___x_3786_; 
if (v_isShared_3784_ == 0)
{
v___x_3786_ = v___x_3783_;
goto v_reusejp_3785_;
}
else
{
lean_object* v_reuseFailAlloc_3787_; 
v_reuseFailAlloc_3787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3787_, 0, v_a_3781_);
v___x_3786_ = v_reuseFailAlloc_3787_;
goto v_reusejp_3785_;
}
v_reusejp_3785_:
{
return v___x_3786_;
}
}
}
}
else
{
lean_object* v___x_3789_; 
v___x_3789_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3789_, 0, v_b_3769_);
return v___x_3789_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg___boxed(lean_object* v_as_3790_, lean_object* v_i_3791_, lean_object* v_stop_3792_, lean_object* v_b_3793_, lean_object* v___y_3794_){
_start:
{
size_t v_i_boxed_3795_; size_t v_stop_boxed_3796_; lean_object* v_res_3797_; 
v_i_boxed_3795_ = lean_unbox_usize(v_i_3791_);
lean_dec(v_i_3791_);
v_stop_boxed_3796_ = lean_unbox_usize(v_stop_3792_);
lean_dec(v_stop_3792_);
v_res_3797_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg(v_as_3790_, v_i_boxed_3795_, v_stop_boxed_3796_, v_b_3793_);
lean_dec_ref(v_as_3790_);
return v_res_3797_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__1(lean_object* v_as_3798_, size_t v_i_3799_, size_t v_stop_3800_, lean_object* v_b_3801_, lean_object* v___y_3802_){
_start:
{
lean_object* v_a_3805_; lean_object* v___y_3810_; uint8_t v___x_3812_; 
v___x_3812_ = lean_usize_dec_eq(v_i_3799_, v_stop_3800_);
if (v___x_3812_ == 0)
{
lean_object* v___x_3813_; lean_object* v___x_3814_; lean_object* v___x_3815_; uint8_t v___x_3816_; 
v___x_3813_ = lean_array_uget_borrowed(v_as_3798_, v_i_3799_);
v___x_3814_ = lean_unsigned_to_nat(0u);
v___x_3815_ = lean_array_get_size(v___x_3813_);
v___x_3816_ = lean_nat_dec_lt(v___x_3814_, v___x_3815_);
if (v___x_3816_ == 0)
{
v_a_3805_ = v_b_3801_;
goto v___jp_3804_;
}
else
{
uint8_t v___x_3817_; 
v___x_3817_ = lean_nat_dec_le(v___x_3815_, v___x_3815_);
if (v___x_3817_ == 0)
{
if (v___x_3816_ == 0)
{
v_a_3805_ = v_b_3801_;
goto v___jp_3804_;
}
else
{
size_t v___x_3818_; size_t v___x_3819_; lean_object* v___x_3820_; 
v___x_3818_ = ((size_t)0ULL);
v___x_3819_ = lean_usize_of_nat(v___x_3815_);
v___x_3820_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg(v___x_3813_, v___x_3818_, v___x_3819_, v_b_3801_);
v___y_3810_ = v___x_3820_;
goto v___jp_3809_;
}
}
else
{
size_t v___x_3821_; size_t v___x_3822_; lean_object* v___x_3823_; 
v___x_3821_ = ((size_t)0ULL);
v___x_3822_ = lean_usize_of_nat(v___x_3815_);
v___x_3823_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg(v___x_3813_, v___x_3821_, v___x_3822_, v_b_3801_);
v___y_3810_ = v___x_3823_;
goto v___jp_3809_;
}
}
}
else
{
lean_object* v___x_3824_; 
v___x_3824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3824_, 0, v_b_3801_);
return v___x_3824_;
}
v___jp_3804_:
{
size_t v___x_3806_; size_t v___x_3807_; 
v___x_3806_ = ((size_t)1ULL);
v___x_3807_ = lean_usize_add(v_i_3799_, v___x_3806_);
v_i_3799_ = v___x_3807_;
v_b_3801_ = v_a_3805_;
goto _start;
}
v___jp_3809_:
{
if (lean_obj_tag(v___y_3810_) == 0)
{
lean_object* v_a_3811_; 
v_a_3811_ = lean_ctor_get(v___y_3810_, 0);
lean_inc(v_a_3811_);
lean_dec_ref(v___y_3810_);
v_a_3805_ = v_a_3811_;
goto v___jp_3804_;
}
else
{
return v___y_3810_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__1___boxed(lean_object* v_as_3825_, lean_object* v_i_3826_, lean_object* v_stop_3827_, lean_object* v_b_3828_, lean_object* v___y_3829_, lean_object* v___y_3830_){
_start:
{
size_t v_i_boxed_3831_; size_t v_stop_boxed_3832_; lean_object* v_res_3833_; 
v_i_boxed_3831_ = lean_unbox_usize(v_i_3826_);
lean_dec(v_i_3826_);
v_stop_boxed_3832_ = lean_unbox_usize(v_stop_3827_);
lean_dec(v_stop_3827_);
v_res_3833_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__1(v_as_3825_, v_i_boxed_3831_, v_stop_boxed_3832_, v_b_3828_, v___y_3829_);
lean_dec_ref(v___y_3829_);
lean_dec_ref(v_as_3825_);
return v_res_3833_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_AttributeExtension_addImported(lean_object* v_es_3834_, lean_object* v_a_3835_){
_start:
{
lean_object* v_a_3838_; lean_object* v___y_3843_; lean_object* v___x_3853_; lean_object* v___x_3854_; lean_object* v___x_3855_; lean_object* v___x_3856_; uint8_t v___x_3857_; 
v___x_3853_ = l_Lean_attributeMapRef;
v___x_3854_ = lean_st_ref_get(v___x_3853_);
v___x_3855_ = lean_unsigned_to_nat(0u);
v___x_3856_ = lean_array_get_size(v_es_3834_);
v___x_3857_ = lean_nat_dec_lt(v___x_3855_, v___x_3856_);
if (v___x_3857_ == 0)
{
v_a_3838_ = v___x_3854_;
goto v___jp_3837_;
}
else
{
uint8_t v___x_3858_; 
v___x_3858_ = lean_nat_dec_le(v___x_3856_, v___x_3856_);
if (v___x_3858_ == 0)
{
if (v___x_3857_ == 0)
{
v_a_3838_ = v___x_3854_;
goto v___jp_3837_;
}
else
{
size_t v___x_3859_; size_t v___x_3860_; lean_object* v___x_3861_; 
v___x_3859_ = ((size_t)0ULL);
v___x_3860_ = lean_usize_of_nat(v___x_3856_);
v___x_3861_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__1(v_es_3834_, v___x_3859_, v___x_3860_, v___x_3854_, v_a_3835_);
v___y_3843_ = v___x_3861_;
goto v___jp_3842_;
}
}
else
{
size_t v___x_3862_; size_t v___x_3863_; lean_object* v___x_3864_; 
v___x_3862_ = ((size_t)0ULL);
v___x_3863_ = lean_usize_of_nat(v___x_3856_);
v___x_3864_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__1(v_es_3834_, v___x_3862_, v___x_3863_, v___x_3854_, v_a_3835_);
v___y_3843_ = v___x_3864_;
goto v___jp_3842_;
}
}
v___jp_3837_:
{
lean_object* v___x_3839_; lean_object* v___x_3840_; lean_object* v___x_3841_; 
v___x_3839_ = lean_box(0);
v___x_3840_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3840_, 0, v___x_3839_);
lean_ctor_set(v___x_3840_, 1, v_a_3838_);
v___x_3841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3841_, 0, v___x_3840_);
return v___x_3841_;
}
v___jp_3842_:
{
if (lean_obj_tag(v___y_3843_) == 0)
{
lean_object* v_a_3844_; 
v_a_3844_ = lean_ctor_get(v___y_3843_, 0);
lean_inc(v_a_3844_);
lean_dec_ref(v___y_3843_);
v_a_3838_ = v_a_3844_;
goto v___jp_3837_;
}
else
{
lean_object* v_a_3845_; lean_object* v___x_3847_; uint8_t v_isShared_3848_; uint8_t v_isSharedCheck_3852_; 
v_a_3845_ = lean_ctor_get(v___y_3843_, 0);
v_isSharedCheck_3852_ = !lean_is_exclusive(v___y_3843_);
if (v_isSharedCheck_3852_ == 0)
{
v___x_3847_ = v___y_3843_;
v_isShared_3848_ = v_isSharedCheck_3852_;
goto v_resetjp_3846_;
}
else
{
lean_inc(v_a_3845_);
lean_dec(v___y_3843_);
v___x_3847_ = lean_box(0);
v_isShared_3848_ = v_isSharedCheck_3852_;
goto v_resetjp_3846_;
}
v_resetjp_3846_:
{
lean_object* v___x_3850_; 
if (v_isShared_3848_ == 0)
{
v___x_3850_ = v___x_3847_;
goto v_reusejp_3849_;
}
else
{
lean_object* v_reuseFailAlloc_3851_; 
v_reuseFailAlloc_3851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3851_, 0, v_a_3845_);
v___x_3850_ = v_reuseFailAlloc_3851_;
goto v_reusejp_3849_;
}
v_reusejp_3849_:
{
return v___x_3850_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_AttributeExtension_addImported___boxed(lean_object* v_es_3865_, lean_object* v_a_3866_, lean_object* v_a_3867_){
_start:
{
lean_object* v_res_3868_; 
v_res_3868_ = l___private_Lean_Attributes_0__Lean_AttributeExtension_addImported(v_es_3865_, v_a_3866_);
lean_dec_ref(v_a_3866_);
lean_dec_ref(v_es_3865_);
return v_res_3868_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0(lean_object* v_as_3869_, size_t v_i_3870_, size_t v_stop_3871_, lean_object* v_b_3872_, lean_object* v___y_3873_){
_start:
{
lean_object* v___x_3875_; 
v___x_3875_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg(v_as_3869_, v_i_3870_, v_stop_3871_, v_b_3872_);
return v___x_3875_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___boxed(lean_object* v_as_3876_, lean_object* v_i_3877_, lean_object* v_stop_3878_, lean_object* v_b_3879_, lean_object* v___y_3880_, lean_object* v___y_3881_){
_start:
{
size_t v_i_boxed_3882_; size_t v_stop_boxed_3883_; lean_object* v_res_3884_; 
v_i_boxed_3882_ = lean_unbox_usize(v_i_3877_);
lean_dec(v_i_3877_);
v_stop_boxed_3883_ = lean_unbox_usize(v_stop_3878_);
lean_dec(v_stop_3878_);
v_res_3884_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0(v_as_3876_, v_i_boxed_3882_, v_stop_boxed_3883_, v_b_3879_, v___y_3880_);
lean_dec_ref(v___y_3880_);
lean_dec_ref(v_as_3876_);
return v_res_3884_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_addAttrEntry(lean_object* v_s_3885_, lean_object* v_e_3886_){
_start:
{
lean_object* v_snd_3887_; lean_object* v_toAttributeImplCore_3888_; lean_object* v_fst_3889_; lean_object* v___x_3891_; uint8_t v_isShared_3892_; uint8_t v_isSharedCheck_3907_; 
v_snd_3887_ = lean_ctor_get(v_e_3886_, 1);
lean_inc(v_snd_3887_);
v_toAttributeImplCore_3888_ = lean_ctor_get(v_snd_3887_, 0);
v_fst_3889_ = lean_ctor_get(v_e_3886_, 0);
v_isSharedCheck_3907_ = !lean_is_exclusive(v_e_3886_);
if (v_isSharedCheck_3907_ == 0)
{
lean_object* v_unused_3908_; 
v_unused_3908_ = lean_ctor_get(v_e_3886_, 1);
lean_dec(v_unused_3908_);
v___x_3891_ = v_e_3886_;
v_isShared_3892_ = v_isSharedCheck_3907_;
goto v_resetjp_3890_;
}
else
{
lean_inc(v_fst_3889_);
lean_dec(v_e_3886_);
v___x_3891_ = lean_box(0);
v_isShared_3892_ = v_isSharedCheck_3907_;
goto v_resetjp_3890_;
}
v_resetjp_3890_:
{
lean_object* v_newEntries_3893_; lean_object* v_map_3894_; lean_object* v___x_3896_; uint8_t v_isShared_3897_; uint8_t v_isSharedCheck_3906_; 
v_newEntries_3893_ = lean_ctor_get(v_s_3885_, 0);
v_map_3894_ = lean_ctor_get(v_s_3885_, 1);
v_isSharedCheck_3906_ = !lean_is_exclusive(v_s_3885_);
if (v_isSharedCheck_3906_ == 0)
{
v___x_3896_ = v_s_3885_;
v_isShared_3897_ = v_isSharedCheck_3906_;
goto v_resetjp_3895_;
}
else
{
lean_inc(v_map_3894_);
lean_inc(v_newEntries_3893_);
lean_dec(v_s_3885_);
v___x_3896_ = lean_box(0);
v_isShared_3897_ = v_isSharedCheck_3906_;
goto v_resetjp_3895_;
}
v_resetjp_3895_:
{
lean_object* v_name_3898_; lean_object* v___x_3900_; 
v_name_3898_ = lean_ctor_get(v_toAttributeImplCore_3888_, 1);
lean_inc(v_name_3898_);
if (v_isShared_3892_ == 0)
{
lean_ctor_set_tag(v___x_3891_, 1);
lean_ctor_set(v___x_3891_, 1, v_newEntries_3893_);
v___x_3900_ = v___x_3891_;
goto v_reusejp_3899_;
}
else
{
lean_object* v_reuseFailAlloc_3905_; 
v_reuseFailAlloc_3905_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3905_, 0, v_fst_3889_);
lean_ctor_set(v_reuseFailAlloc_3905_, 1, v_newEntries_3893_);
v___x_3900_ = v_reuseFailAlloc_3905_;
goto v_reusejp_3899_;
}
v_reusejp_3899_:
{
lean_object* v___x_3901_; lean_object* v___x_3903_; 
v___x_3901_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1___redArg(v_map_3894_, v_name_3898_, v_snd_3887_);
if (v_isShared_3897_ == 0)
{
lean_ctor_set(v___x_3896_, 1, v___x_3901_);
lean_ctor_set(v___x_3896_, 0, v___x_3900_);
v___x_3903_ = v___x_3896_;
goto v_reusejp_3902_;
}
else
{
lean_object* v_reuseFailAlloc_3904_; 
v_reuseFailAlloc_3904_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3904_, 0, v___x_3900_);
lean_ctor_set(v_reuseFailAlloc_3904_, 1, v___x_3901_);
v___x_3903_ = v_reuseFailAlloc_3904_;
goto v_reusejp_3902_;
}
v_reusejp_3902_:
{
return v___x_3903_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(lean_object* v_x_3909_, lean_object* v_s_3910_){
_start:
{
lean_object* v_newEntries_3911_; lean_object* v___x_3912_; lean_object* v___x_3913_; lean_object* v___x_3914_; 
v_newEntries_3911_ = lean_ctor_get(v_s_3910_, 0);
lean_inc(v_newEntries_3911_);
lean_dec_ref(v_s_3910_);
v___x_3912_ = l_List_reverse___redArg(v_newEntries_3911_);
v___x_3913_ = lean_array_mk(v___x_3912_);
lean_inc_ref_n(v___x_3913_, 2);
v___x_3914_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3914_, 0, v___x_3913_);
lean_ctor_set(v___x_3914_, 1, v___x_3913_);
lean_ctor_set(v___x_3914_, 2, v___x_3913_);
return v___x_3914_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2____boxed(lean_object* v_x_3915_, lean_object* v_s_3916_){
_start:
{
lean_object* v_res_3917_; 
v_res_3917_ = l_Lean_initFn___lam__0_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(v_x_3915_, v_s_3916_);
lean_dec_ref(v_x_3915_);
return v_res_3917_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__1_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(lean_object* v_s_3918_){
_start:
{
lean_object* v_newEntries_3919_; lean_object* v___x_3921_; uint8_t v_isShared_3922_; uint8_t v_isSharedCheck_3930_; 
v_newEntries_3919_ = lean_ctor_get(v_s_3918_, 0);
v_isSharedCheck_3930_ = !lean_is_exclusive(v_s_3918_);
if (v_isSharedCheck_3930_ == 0)
{
lean_object* v_unused_3931_; 
v_unused_3931_ = lean_ctor_get(v_s_3918_, 1);
lean_dec(v_unused_3931_);
v___x_3921_ = v_s_3918_;
v_isShared_3922_ = v_isSharedCheck_3930_;
goto v_resetjp_3920_;
}
else
{
lean_inc(v_newEntries_3919_);
lean_dec(v_s_3918_);
v___x_3921_ = lean_box(0);
v_isShared_3922_ = v_isSharedCheck_3930_;
goto v_resetjp_3920_;
}
v_resetjp_3920_:
{
lean_object* v___x_3923_; lean_object* v___x_3924_; lean_object* v___x_3925_; lean_object* v___x_3926_; lean_object* v___x_3928_; 
v___x_3923_ = ((lean_object*)(l_Lean_registerTagAttribute___lam__2___closed__4));
v___x_3924_ = l_List_lengthTR___redArg(v_newEntries_3919_);
lean_dec(v_newEntries_3919_);
v___x_3925_ = l_Nat_reprFast(v___x_3924_);
v___x_3926_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3926_, 0, v___x_3925_);
if (v_isShared_3922_ == 0)
{
lean_ctor_set_tag(v___x_3921_, 5);
lean_ctor_set(v___x_3921_, 1, v___x_3926_);
lean_ctor_set(v___x_3921_, 0, v___x_3923_);
v___x_3928_ = v___x_3921_;
goto v_reusejp_3927_;
}
else
{
lean_object* v_reuseFailAlloc_3929_; 
v_reuseFailAlloc_3929_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3929_, 0, v___x_3923_);
lean_ctor_set(v_reuseFailAlloc_3929_, 1, v___x_3926_);
v___x_3928_ = v_reuseFailAlloc_3929_;
goto v_reusejp_3927_;
}
v_reusejp_3927_:
{
return v___x_3928_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__2_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(lean_object* v_s_3932_){
_start:
{
lean_object* v_newEntries_3933_; lean_object* v___x_3934_; lean_object* v___x_3935_; 
v_newEntries_3933_ = lean_ctor_get(v_s_3932_, 0);
lean_inc(v_newEntries_3933_);
lean_dec_ref(v_s_3932_);
v___x_3934_ = l_List_reverse___redArg(v_newEntries_3933_);
v___x_3935_ = lean_array_mk(v___x_3934_);
return v___x_3935_;
}
}
static lean_object* _init_l_Lean_initFn___closed__7_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3945_; lean_object* v___x_3946_; lean_object* v___f_3947_; lean_object* v___f_3948_; lean_object* v___x_3949_; lean_object* v___x_3950_; lean_object* v___x_3951_; lean_object* v___x_3952_; lean_object* v___x_3953_; 
v___x_3945_ = lean_box(0);
v___x_3946_ = lean_box(2);
v___f_3947_ = ((lean_object*)(l_Lean_initFn___closed__1_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___f_3948_ = ((lean_object*)(l_Lean_initFn___closed__0_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___x_3949_ = ((lean_object*)(l_Lean_initFn___closed__6_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___x_3950_ = ((lean_object*)(l_Lean_initFn___closed__5_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___x_3951_ = lean_alloc_closure((void*)(l___private_Lean_Attributes_0__Lean_AttributeExtension_mkInitial___boxed), 1, 0);
v___x_3952_ = ((lean_object*)(l_Lean_initFn___closed__4_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___x_3953_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_3953_, 0, v___x_3952_);
lean_ctor_set(v___x_3953_, 1, v___x_3951_);
lean_ctor_set(v___x_3953_, 2, v___x_3950_);
lean_ctor_set(v___x_3953_, 3, v___x_3949_);
lean_ctor_set(v___x_3953_, 4, v___f_3948_);
lean_ctor_set(v___x_3953_, 5, v___f_3947_);
lean_ctor_set(v___x_3953_, 6, v___x_3946_);
lean_ctor_set(v___x_3953_, 7, v___x_3945_);
return v___x_3953_;
}
}
static lean_object* _init_l_Lean_initFn___closed__8_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_3954_; lean_object* v___x_3955_; lean_object* v___x_3956_; 
v___f_3954_ = ((lean_object*)(l_Lean_initFn___closed__2_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___x_3955_ = lean_obj_once(&l_Lean_initFn___closed__7_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_, &l_Lean_initFn___closed__7_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2__once, _init_l_Lean_initFn___closed__7_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_);
v___x_3956_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3956_, 0, v___x_3955_);
lean_ctor_set(v___x_3956_, 1, v___f_3954_);
return v___x_3956_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3958_; lean_object* v___x_3959_; 
v___x_3958_ = lean_obj_once(&l_Lean_initFn___closed__8_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_, &l_Lean_initFn___closed__8_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2__once, _init_l_Lean_initFn___closed__8_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_);
v___x_3959_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_3958_);
return v___x_3959_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2____boxed(lean_object* v_a_3960_){
_start:
{
lean_object* v_res_3961_; 
v_res_3961_ = l_Lean_initFn_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_();
return v_res_3961_;
}
}
LEAN_EXPORT lean_object* lean_is_attribute(lean_object* v_n_3962_){
_start:
{
lean_object* v___x_3964_; lean_object* v___x_3965_; uint8_t v___x_3966_; lean_object* v___x_3967_; lean_object* v___x_3968_; 
v___x_3964_ = l_Lean_attributeMapRef;
v___x_3965_ = lean_st_ref_get(v___x_3964_);
v___x_3966_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(v___x_3965_, v_n_3962_);
lean_dec(v_n_3962_);
lean_dec(v___x_3965_);
v___x_3967_ = lean_box(v___x_3966_);
v___x_3968_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3968_, 0, v___x_3967_);
return v___x_3968_;
}
}
LEAN_EXPORT lean_object* l_Lean_isBuiltinAttribute___boxed(lean_object* v_n_3969_, lean_object* v_a_3970_){
_start:
{
lean_object* v_res_3971_; 
v_res_3971_ = lean_is_attribute(v_n_3969_);
return v_res_3971_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_getBuiltinAttributeNames_spec__0(lean_object* v_x_3972_, lean_object* v_x_3973_){
_start:
{
if (lean_obj_tag(v_x_3973_) == 0)
{
return v_x_3972_;
}
else
{
lean_object* v_key_3974_; lean_object* v_tail_3975_; lean_object* v___x_3976_; 
v_key_3974_ = lean_ctor_get(v_x_3973_, 0);
v_tail_3975_ = lean_ctor_get(v_x_3973_, 2);
lean_inc(v_key_3974_);
v___x_3976_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3976_, 0, v_key_3974_);
lean_ctor_set(v___x_3976_, 1, v_x_3972_);
v_x_3972_ = v___x_3976_;
v_x_3973_ = v_tail_3975_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_getBuiltinAttributeNames_spec__0___boxed(lean_object* v_x_3978_, lean_object* v_x_3979_){
_start:
{
lean_object* v_res_3980_; 
v_res_3980_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_getBuiltinAttributeNames_spec__0(v_x_3978_, v_x_3979_);
lean_dec(v_x_3979_);
return v_res_3980_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1(lean_object* v_as_3981_, size_t v_i_3982_, size_t v_stop_3983_, lean_object* v_b_3984_){
_start:
{
uint8_t v___x_3985_; 
v___x_3985_ = lean_usize_dec_eq(v_i_3982_, v_stop_3983_);
if (v___x_3985_ == 0)
{
lean_object* v___x_3986_; lean_object* v___x_3987_; size_t v___x_3988_; size_t v___x_3989_; 
v___x_3986_ = lean_array_uget_borrowed(v_as_3981_, v_i_3982_);
v___x_3987_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_getBuiltinAttributeNames_spec__0(v_b_3984_, v___x_3986_);
v___x_3988_ = ((size_t)1ULL);
v___x_3989_ = lean_usize_add(v_i_3982_, v___x_3988_);
v_i_3982_ = v___x_3989_;
v_b_3984_ = v___x_3987_;
goto _start;
}
else
{
return v_b_3984_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1___boxed(lean_object* v_as_3991_, lean_object* v_i_3992_, lean_object* v_stop_3993_, lean_object* v_b_3994_){
_start:
{
size_t v_i_boxed_3995_; size_t v_stop_boxed_3996_; lean_object* v_res_3997_; 
v_i_boxed_3995_ = lean_unbox_usize(v_i_3992_);
lean_dec(v_i_3992_);
v_stop_boxed_3996_ = lean_unbox_usize(v_stop_3993_);
lean_dec(v_stop_3993_);
v_res_3997_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1(v_as_3991_, v_i_boxed_3995_, v_stop_boxed_3996_, v_b_3994_);
lean_dec_ref(v_as_3991_);
return v_res_3997_;
}
}
LEAN_EXPORT lean_object* l_Lean_getBuiltinAttributeNames(){
_start:
{
lean_object* v___x_3999_; lean_object* v___x_4000_; lean_object* v_buckets_4001_; lean_object* v___x_4002_; lean_object* v___x_4003_; lean_object* v___x_4004_; uint8_t v___x_4005_; 
v___x_3999_ = l_Lean_attributeMapRef;
v___x_4000_ = lean_st_ref_get(v___x_3999_);
v_buckets_4001_ = lean_ctor_get(v___x_4000_, 1);
lean_inc_ref(v_buckets_4001_);
lean_dec(v___x_4000_);
v___x_4002_ = lean_box(0);
v___x_4003_ = lean_unsigned_to_nat(0u);
v___x_4004_ = lean_array_get_size(v_buckets_4001_);
v___x_4005_ = lean_nat_dec_lt(v___x_4003_, v___x_4004_);
if (v___x_4005_ == 0)
{
lean_object* v___x_4006_; 
lean_dec_ref(v_buckets_4001_);
v___x_4006_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4006_, 0, v___x_4002_);
return v___x_4006_;
}
else
{
uint8_t v___x_4007_; 
v___x_4007_ = lean_nat_dec_le(v___x_4004_, v___x_4004_);
if (v___x_4007_ == 0)
{
if (v___x_4005_ == 0)
{
lean_object* v___x_4008_; 
lean_dec_ref(v_buckets_4001_);
v___x_4008_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4008_, 0, v___x_4002_);
return v___x_4008_;
}
else
{
size_t v___x_4009_; size_t v___x_4010_; lean_object* v___x_4011_; lean_object* v___x_4012_; 
v___x_4009_ = ((size_t)0ULL);
v___x_4010_ = lean_usize_of_nat(v___x_4004_);
v___x_4011_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1(v_buckets_4001_, v___x_4009_, v___x_4010_, v___x_4002_);
lean_dec_ref(v_buckets_4001_);
v___x_4012_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4012_, 0, v___x_4011_);
return v___x_4012_;
}
}
else
{
size_t v___x_4013_; size_t v___x_4014_; lean_object* v___x_4015_; lean_object* v___x_4016_; 
v___x_4013_ = ((size_t)0ULL);
v___x_4014_ = lean_usize_of_nat(v___x_4004_);
v___x_4015_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1(v_buckets_4001_, v___x_4013_, v___x_4014_, v___x_4002_);
lean_dec_ref(v_buckets_4001_);
v___x_4016_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4016_, 0, v___x_4015_);
return v___x_4016_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getBuiltinAttributeNames___boxed(lean_object* v_a_4017_){
_start:
{
lean_object* v_res_4018_; 
v_res_4018_ = l_Lean_getBuiltinAttributeNames();
return v_res_4018_;
}
}
LEAN_EXPORT lean_object* l_Lean_getBuiltinAttributeImpl(lean_object* v_attrName_4020_){
_start:
{
lean_object* v___x_4022_; lean_object* v___x_4023_; lean_object* v___x_4024_; 
v___x_4022_ = l_Lean_attributeMapRef;
v___x_4023_ = lean_st_ref_get(v___x_4022_);
v___x_4024_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(v___x_4023_, v_attrName_4020_);
lean_dec(v___x_4023_);
if (lean_obj_tag(v___x_4024_) == 0)
{
lean_object* v___x_4025_; uint8_t v___x_4026_; lean_object* v___x_4027_; lean_object* v___x_4028_; lean_object* v___x_4029_; lean_object* v___x_4030_; lean_object* v___x_4031_; lean_object* v___x_4032_; 
v___x_4025_ = ((lean_object*)(l_Lean_getBuiltinAttributeImpl___closed__0));
v___x_4026_ = 1;
v___x_4027_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_attrName_4020_, v___x_4026_);
v___x_4028_ = lean_string_append(v___x_4025_, v___x_4027_);
lean_dec_ref(v___x_4027_);
v___x_4029_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__4));
v___x_4030_ = lean_string_append(v___x_4028_, v___x_4029_);
v___x_4031_ = lean_mk_io_user_error(v___x_4030_);
v___x_4032_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4032_, 0, v___x_4031_);
return v___x_4032_;
}
else
{
lean_object* v_val_4033_; lean_object* v___x_4035_; uint8_t v_isShared_4036_; uint8_t v_isSharedCheck_4040_; 
lean_dec(v_attrName_4020_);
v_val_4033_ = lean_ctor_get(v___x_4024_, 0);
v_isSharedCheck_4040_ = !lean_is_exclusive(v___x_4024_);
if (v_isSharedCheck_4040_ == 0)
{
v___x_4035_ = v___x_4024_;
v_isShared_4036_ = v_isSharedCheck_4040_;
goto v_resetjp_4034_;
}
else
{
lean_inc(v_val_4033_);
lean_dec(v___x_4024_);
v___x_4035_ = lean_box(0);
v_isShared_4036_ = v_isSharedCheck_4040_;
goto v_resetjp_4034_;
}
v_resetjp_4034_:
{
lean_object* v___x_4038_; 
if (v_isShared_4036_ == 0)
{
lean_ctor_set_tag(v___x_4035_, 0);
v___x_4038_ = v___x_4035_;
goto v_reusejp_4037_;
}
else
{
lean_object* v_reuseFailAlloc_4039_; 
v_reuseFailAlloc_4039_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4039_, 0, v_val_4033_);
v___x_4038_ = v_reuseFailAlloc_4039_;
goto v_reusejp_4037_;
}
v_reusejp_4037_:
{
return v___x_4038_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getBuiltinAttributeImpl___boxed(lean_object* v_attrName_4041_, lean_object* v_a_4042_){
_start:
{
lean_object* v_res_4043_; 
v_res_4043_ = l_Lean_getBuiltinAttributeImpl(v_attrName_4041_);
return v_res_4043_;
}
}
LEAN_EXPORT lean_object* lean_attribute_application_time(lean_object* v_n_4044_){
_start:
{
lean_object* v___x_4046_; 
v___x_4046_ = l_Lean_getBuiltinAttributeImpl(v_n_4044_);
if (lean_obj_tag(v___x_4046_) == 0)
{
lean_object* v_a_4047_; lean_object* v___x_4049_; uint8_t v_isShared_4050_; uint8_t v_isSharedCheck_4057_; 
v_a_4047_ = lean_ctor_get(v___x_4046_, 0);
v_isSharedCheck_4057_ = !lean_is_exclusive(v___x_4046_);
if (v_isSharedCheck_4057_ == 0)
{
v___x_4049_ = v___x_4046_;
v_isShared_4050_ = v_isSharedCheck_4057_;
goto v_resetjp_4048_;
}
else
{
lean_inc(v_a_4047_);
lean_dec(v___x_4046_);
v___x_4049_ = lean_box(0);
v_isShared_4050_ = v_isSharedCheck_4057_;
goto v_resetjp_4048_;
}
v_resetjp_4048_:
{
lean_object* v_toAttributeImplCore_4051_; uint8_t v_applicationTime_4052_; lean_object* v___x_4053_; lean_object* v___x_4055_; 
v_toAttributeImplCore_4051_ = lean_ctor_get(v_a_4047_, 0);
lean_inc_ref(v_toAttributeImplCore_4051_);
lean_dec(v_a_4047_);
v_applicationTime_4052_ = lean_ctor_get_uint8(v_toAttributeImplCore_4051_, sizeof(void*)*3);
lean_dec_ref(v_toAttributeImplCore_4051_);
v___x_4053_ = lean_box(v_applicationTime_4052_);
if (v_isShared_4050_ == 0)
{
lean_ctor_set(v___x_4049_, 0, v___x_4053_);
v___x_4055_ = v___x_4049_;
goto v_reusejp_4054_;
}
else
{
lean_object* v_reuseFailAlloc_4056_; 
v_reuseFailAlloc_4056_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4056_, 0, v___x_4053_);
v___x_4055_ = v_reuseFailAlloc_4056_;
goto v_reusejp_4054_;
}
v_reusejp_4054_:
{
return v___x_4055_;
}
}
}
else
{
lean_object* v_a_4058_; lean_object* v___x_4060_; uint8_t v_isShared_4061_; uint8_t v_isSharedCheck_4065_; 
v_a_4058_ = lean_ctor_get(v___x_4046_, 0);
v_isSharedCheck_4065_ = !lean_is_exclusive(v___x_4046_);
if (v_isSharedCheck_4065_ == 0)
{
v___x_4060_ = v___x_4046_;
v_isShared_4061_ = v_isSharedCheck_4065_;
goto v_resetjp_4059_;
}
else
{
lean_inc(v_a_4058_);
lean_dec(v___x_4046_);
v___x_4060_ = lean_box(0);
v_isShared_4061_ = v_isSharedCheck_4065_;
goto v_resetjp_4059_;
}
v_resetjp_4059_:
{
lean_object* v___x_4063_; 
if (v_isShared_4061_ == 0)
{
v___x_4063_ = v___x_4060_;
goto v_reusejp_4062_;
}
else
{
lean_object* v_reuseFailAlloc_4064_; 
v_reuseFailAlloc_4064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4064_, 0, v_a_4058_);
v___x_4063_ = v_reuseFailAlloc_4064_;
goto v_reusejp_4062_;
}
v_reusejp_4062_:
{
return v___x_4063_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getBuiltinAttributeApplicationTime___boxed(lean_object* v_n_4066_, lean_object* v_a_4067_){
_start:
{
lean_object* v_res_4068_; 
v_res_4068_ = lean_attribute_application_time(v_n_4066_);
return v_res_4068_;
}
}
LEAN_EXPORT uint8_t l_Lean_isAttribute(lean_object* v_env_4069_, lean_object* v_attrName_4070_){
_start:
{
lean_object* v___x_4071_; lean_object* v_toEnvExtension_4072_; lean_object* v_asyncMode_4073_; lean_object* v___x_4074_; lean_object* v___x_4075_; lean_object* v___x_4076_; lean_object* v_map_4077_; uint8_t v___x_4078_; 
v___x_4071_ = l_Lean_attributeExtension;
v_toEnvExtension_4072_ = lean_ctor_get(v___x_4071_, 0);
v_asyncMode_4073_ = lean_ctor_get(v_toEnvExtension_4072_, 2);
v___x_4074_ = l_Lean_instInhabitedAttributeExtensionState_default;
v___x_4075_ = lean_box(0);
v___x_4076_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_4074_, v___x_4071_, v_env_4069_, v_asyncMode_4073_, v___x_4075_);
v_map_4077_ = lean_ctor_get(v___x_4076_, 1);
lean_inc_ref(v_map_4077_);
lean_dec(v___x_4076_);
v___x_4078_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(v_map_4077_, v_attrName_4070_);
lean_dec_ref(v_map_4077_);
return v___x_4078_;
}
}
LEAN_EXPORT lean_object* l_Lean_isAttribute___boxed(lean_object* v_env_4079_, lean_object* v_attrName_4080_){
_start:
{
uint8_t v_res_4081_; lean_object* v_r_4082_; 
v_res_4081_ = l_Lean_isAttribute(v_env_4079_, v_attrName_4080_);
lean_dec(v_attrName_4080_);
v_r_4082_ = lean_box(v_res_4081_);
return v_r_4082_;
}
}
LEAN_EXPORT lean_object* l_Lean_getAttributeNames(lean_object* v_env_4083_){
_start:
{
lean_object* v___x_4084_; lean_object* v_toEnvExtension_4085_; lean_object* v_asyncMode_4086_; lean_object* v___x_4087_; lean_object* v___x_4088_; lean_object* v___x_4089_; lean_object* v_map_4090_; lean_object* v_buckets_4091_; lean_object* v___x_4092_; lean_object* v___x_4093_; lean_object* v___x_4094_; uint8_t v___x_4095_; 
v___x_4084_ = l_Lean_attributeExtension;
v_toEnvExtension_4085_ = lean_ctor_get(v___x_4084_, 0);
v_asyncMode_4086_ = lean_ctor_get(v_toEnvExtension_4085_, 2);
v___x_4087_ = l_Lean_instInhabitedAttributeExtensionState_default;
v___x_4088_ = lean_box(0);
v___x_4089_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_4087_, v___x_4084_, v_env_4083_, v_asyncMode_4086_, v___x_4088_);
v_map_4090_ = lean_ctor_get(v___x_4089_, 1);
lean_inc_ref(v_map_4090_);
lean_dec(v___x_4089_);
v_buckets_4091_ = lean_ctor_get(v_map_4090_, 1);
lean_inc_ref(v_buckets_4091_);
lean_dec_ref(v_map_4090_);
v___x_4092_ = lean_box(0);
v___x_4093_ = lean_unsigned_to_nat(0u);
v___x_4094_ = lean_array_get_size(v_buckets_4091_);
v___x_4095_ = lean_nat_dec_lt(v___x_4093_, v___x_4094_);
if (v___x_4095_ == 0)
{
lean_dec_ref(v_buckets_4091_);
return v___x_4092_;
}
else
{
uint8_t v___x_4096_; 
v___x_4096_ = lean_nat_dec_le(v___x_4094_, v___x_4094_);
if (v___x_4096_ == 0)
{
if (v___x_4095_ == 0)
{
lean_dec_ref(v_buckets_4091_);
return v___x_4092_;
}
else
{
size_t v___x_4097_; size_t v___x_4098_; lean_object* v___x_4099_; 
v___x_4097_ = ((size_t)0ULL);
v___x_4098_ = lean_usize_of_nat(v___x_4094_);
v___x_4099_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1(v_buckets_4091_, v___x_4097_, v___x_4098_, v___x_4092_);
lean_dec_ref(v_buckets_4091_);
return v___x_4099_;
}
}
else
{
size_t v___x_4100_; size_t v___x_4101_; lean_object* v___x_4102_; 
v___x_4100_ = ((size_t)0ULL);
v___x_4101_ = lean_usize_of_nat(v___x_4094_);
v___x_4102_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1(v_buckets_4091_, v___x_4100_, v___x_4101_, v___x_4092_);
lean_dec_ref(v_buckets_4091_);
return v___x_4102_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getAttributeImpl(lean_object* v_env_4103_, lean_object* v_attrName_4104_){
_start:
{
lean_object* v___x_4105_; lean_object* v_toEnvExtension_4106_; lean_object* v_asyncMode_4107_; lean_object* v___x_4108_; lean_object* v___x_4109_; lean_object* v___x_4110_; lean_object* v_map_4111_; lean_object* v___x_4112_; 
v___x_4105_ = l_Lean_attributeExtension;
v_toEnvExtension_4106_ = lean_ctor_get(v___x_4105_, 0);
v_asyncMode_4107_ = lean_ctor_get(v_toEnvExtension_4106_, 2);
v___x_4108_ = l_Lean_instInhabitedAttributeExtensionState_default;
v___x_4109_ = lean_box(0);
v___x_4110_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_4108_, v___x_4105_, v_env_4103_, v_asyncMode_4107_, v___x_4109_);
v_map_4111_ = lean_ctor_get(v___x_4110_, 1);
lean_inc_ref(v_map_4111_);
lean_dec(v___x_4110_);
v___x_4112_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(v_map_4111_, v_attrName_4104_);
lean_dec_ref(v_map_4111_);
if (lean_obj_tag(v___x_4112_) == 0)
{
lean_object* v___x_4113_; uint8_t v___x_4114_; lean_object* v___x_4115_; lean_object* v___x_4116_; lean_object* v___x_4117_; lean_object* v___x_4118_; lean_object* v___x_4119_; 
v___x_4113_ = ((lean_object*)(l_Lean_getBuiltinAttributeImpl___closed__0));
v___x_4114_ = 1;
v___x_4115_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_attrName_4104_, v___x_4114_);
v___x_4116_ = lean_string_append(v___x_4113_, v___x_4115_);
lean_dec_ref(v___x_4115_);
v___x_4117_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__4));
v___x_4118_ = lean_string_append(v___x_4116_, v___x_4117_);
v___x_4119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4119_, 0, v___x_4118_);
return v___x_4119_;
}
else
{
lean_object* v_val_4120_; lean_object* v___x_4122_; uint8_t v_isShared_4123_; uint8_t v_isSharedCheck_4127_; 
lean_dec(v_attrName_4104_);
v_val_4120_ = lean_ctor_get(v___x_4112_, 0);
v_isSharedCheck_4127_ = !lean_is_exclusive(v___x_4112_);
if (v_isSharedCheck_4127_ == 0)
{
v___x_4122_ = v___x_4112_;
v_isShared_4123_ = v_isSharedCheck_4127_;
goto v_resetjp_4121_;
}
else
{
lean_inc(v_val_4120_);
lean_dec(v___x_4112_);
v___x_4122_ = lean_box(0);
v_isShared_4123_ = v_isSharedCheck_4127_;
goto v_resetjp_4121_;
}
v_resetjp_4121_:
{
lean_object* v___x_4125_; 
if (v_isShared_4123_ == 0)
{
v___x_4125_ = v___x_4122_;
goto v_reusejp_4124_;
}
else
{
lean_object* v_reuseFailAlloc_4126_; 
v_reuseFailAlloc_4126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4126_, 0, v_val_4120_);
v___x_4125_ = v_reuseFailAlloc_4126_;
goto v_reusejp_4124_;
}
v_reusejp_4124_:
{
return v___x_4125_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerAttributeOfBuilder(lean_object* v_env_4128_, lean_object* v_builderId_4129_, lean_object* v_ref_4130_, lean_object* v_args_4131_){
_start:
{
lean_object* v_entry_4133_; lean_object* v___x_4134_; 
v_entry_4133_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_entry_4133_, 0, v_builderId_4129_);
lean_ctor_set(v_entry_4133_, 1, v_ref_4130_);
lean_ctor_set(v_entry_4133_, 2, v_args_4131_);
lean_inc_ref(v_entry_4133_);
v___x_4134_ = l_Lean_mkAttributeImplOfEntry(v_entry_4133_);
if (lean_obj_tag(v___x_4134_) == 0)
{
lean_object* v_a_4135_; lean_object* v___x_4137_; uint8_t v_isShared_4138_; uint8_t v_isSharedCheck_4160_; 
v_a_4135_ = lean_ctor_get(v___x_4134_, 0);
v_isSharedCheck_4160_ = !lean_is_exclusive(v___x_4134_);
if (v_isSharedCheck_4160_ == 0)
{
v___x_4137_ = v___x_4134_;
v_isShared_4138_ = v_isSharedCheck_4160_;
goto v_resetjp_4136_;
}
else
{
lean_inc(v_a_4135_);
lean_dec(v___x_4134_);
v___x_4137_ = lean_box(0);
v_isShared_4138_ = v_isSharedCheck_4160_;
goto v_resetjp_4136_;
}
v_resetjp_4136_:
{
lean_object* v_toAttributeImplCore_4139_; lean_object* v_name_4140_; uint8_t v___x_4141_; 
v_toAttributeImplCore_4139_ = lean_ctor_get(v_a_4135_, 0);
v_name_4140_ = lean_ctor_get(v_toAttributeImplCore_4139_, 1);
lean_inc_ref(v_env_4128_);
v___x_4141_ = l_Lean_isAttribute(v_env_4128_, v_name_4140_);
if (v___x_4141_ == 0)
{
lean_object* v___x_4142_; lean_object* v_toEnvExtension_4143_; lean_object* v_asyncMode_4144_; lean_object* v___x_4145_; lean_object* v___x_4146_; lean_object* v___x_4147_; lean_object* v___x_4149_; 
v___x_4142_ = l_Lean_attributeExtension;
v_toEnvExtension_4143_ = lean_ctor_get(v___x_4142_, 0);
v_asyncMode_4144_ = lean_ctor_get(v_toEnvExtension_4143_, 2);
v___x_4145_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4145_, 0, v_entry_4133_);
lean_ctor_set(v___x_4145_, 1, v_a_4135_);
v___x_4146_ = lean_box(0);
v___x_4147_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_4142_, v_env_4128_, v___x_4145_, v_asyncMode_4144_, v___x_4146_);
if (v_isShared_4138_ == 0)
{
lean_ctor_set(v___x_4137_, 0, v___x_4147_);
v___x_4149_ = v___x_4137_;
goto v_reusejp_4148_;
}
else
{
lean_object* v_reuseFailAlloc_4150_; 
v_reuseFailAlloc_4150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4150_, 0, v___x_4147_);
v___x_4149_ = v_reuseFailAlloc_4150_;
goto v_reusejp_4148_;
}
v_reusejp_4148_:
{
return v___x_4149_;
}
}
else
{
lean_object* v___x_4151_; lean_object* v___x_4152_; lean_object* v___x_4153_; lean_object* v___x_4154_; lean_object* v___x_4155_; lean_object* v___x_4156_; lean_object* v___x_4158_; 
lean_inc(v_name_4140_);
lean_dec(v_a_4135_);
lean_dec_ref(v_entry_4133_);
lean_dec_ref(v_env_4128_);
v___x_4151_ = ((lean_object*)(l_Lean_registerBuiltinAttribute___closed__2));
v___x_4152_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_4140_, v___x_4141_);
v___x_4153_ = lean_string_append(v___x_4151_, v___x_4152_);
lean_dec_ref(v___x_4152_);
v___x_4154_ = ((lean_object*)(l_Lean_registerBuiltinAttribute___closed__3));
v___x_4155_ = lean_string_append(v___x_4153_, v___x_4154_);
v___x_4156_ = lean_mk_io_user_error(v___x_4155_);
if (v_isShared_4138_ == 0)
{
lean_ctor_set_tag(v___x_4137_, 1);
lean_ctor_set(v___x_4137_, 0, v___x_4156_);
v___x_4158_ = v___x_4137_;
goto v_reusejp_4157_;
}
else
{
lean_object* v_reuseFailAlloc_4159_; 
v_reuseFailAlloc_4159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4159_, 0, v___x_4156_);
v___x_4158_ = v_reuseFailAlloc_4159_;
goto v_reusejp_4157_;
}
v_reusejp_4157_:
{
return v___x_4158_;
}
}
}
}
else
{
lean_object* v_a_4161_; lean_object* v___x_4163_; uint8_t v_isShared_4164_; uint8_t v_isSharedCheck_4168_; 
lean_dec_ref(v_entry_4133_);
lean_dec_ref(v_env_4128_);
v_a_4161_ = lean_ctor_get(v___x_4134_, 0);
v_isSharedCheck_4168_ = !lean_is_exclusive(v___x_4134_);
if (v_isSharedCheck_4168_ == 0)
{
v___x_4163_ = v___x_4134_;
v_isShared_4164_ = v_isSharedCheck_4168_;
goto v_resetjp_4162_;
}
else
{
lean_inc(v_a_4161_);
lean_dec(v___x_4134_);
v___x_4163_ = lean_box(0);
v_isShared_4164_ = v_isSharedCheck_4168_;
goto v_resetjp_4162_;
}
v_resetjp_4162_:
{
lean_object* v___x_4166_; 
if (v_isShared_4164_ == 0)
{
v___x_4166_ = v___x_4163_;
goto v_reusejp_4165_;
}
else
{
lean_object* v_reuseFailAlloc_4167_; 
v_reuseFailAlloc_4167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4167_, 0, v_a_4161_);
v___x_4166_ = v_reuseFailAlloc_4167_;
goto v_reusejp_4165_;
}
v_reusejp_4165_:
{
return v___x_4166_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerAttributeOfBuilder___boxed(lean_object* v_env_4169_, lean_object* v_builderId_4170_, lean_object* v_ref_4171_, lean_object* v_args_4172_, lean_object* v_a_4173_){
_start:
{
lean_object* v_res_4174_; 
v_res_4174_ = l_Lean_registerAttributeOfBuilder(v_env_4169_, v_builderId_4170_, v_ref_4171_, v_args_4172_);
return v_res_4174_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg(lean_object* v_x_4175_, lean_object* v___y_4176_, lean_object* v___y_4177_){
_start:
{
if (lean_obj_tag(v_x_4175_) == 0)
{
lean_object* v_a_4179_; lean_object* v___x_4180_; lean_object* v___x_4181_; 
v_a_4179_ = lean_ctor_get(v_x_4175_, 0);
lean_inc(v_a_4179_);
lean_dec_ref(v_x_4175_);
v___x_4180_ = l_Lean_stringToMessageData(v_a_4179_);
v___x_4181_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0_spec__0___redArg(v___x_4180_, v___y_4176_, v___y_4177_);
return v___x_4181_;
}
else
{
lean_object* v_a_4182_; lean_object* v___x_4184_; uint8_t v_isShared_4185_; uint8_t v_isSharedCheck_4189_; 
v_a_4182_ = lean_ctor_get(v_x_4175_, 0);
v_isSharedCheck_4189_ = !lean_is_exclusive(v_x_4175_);
if (v_isSharedCheck_4189_ == 0)
{
v___x_4184_ = v_x_4175_;
v_isShared_4185_ = v_isSharedCheck_4189_;
goto v_resetjp_4183_;
}
else
{
lean_inc(v_a_4182_);
lean_dec(v_x_4175_);
v___x_4184_ = lean_box(0);
v_isShared_4185_ = v_isSharedCheck_4189_;
goto v_resetjp_4183_;
}
v_resetjp_4183_:
{
lean_object* v___x_4187_; 
if (v_isShared_4185_ == 0)
{
lean_ctor_set_tag(v___x_4184_, 0);
v___x_4187_ = v___x_4184_;
goto v_reusejp_4186_;
}
else
{
lean_object* v_reuseFailAlloc_4188_; 
v_reuseFailAlloc_4188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4188_, 0, v_a_4182_);
v___x_4187_ = v_reuseFailAlloc_4188_;
goto v_reusejp_4186_;
}
v_reusejp_4186_:
{
return v___x_4187_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg___boxed(lean_object* v_x_4190_, lean_object* v___y_4191_, lean_object* v___y_4192_, lean_object* v___y_4193_){
_start:
{
lean_object* v_res_4194_; 
v_res_4194_ = l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg(v_x_4190_, v___y_4191_, v___y_4192_);
lean_dec(v___y_4192_);
lean_dec_ref(v___y_4191_);
return v_res_4194_;
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_add(lean_object* v_declName_4195_, lean_object* v_attrName_4196_, lean_object* v_stx_4197_, uint8_t v_kind_4198_, lean_object* v_a_4199_, lean_object* v_a_4200_){
_start:
{
lean_object* v___x_4202_; lean_object* v_env_4203_; lean_object* v___x_4204_; lean_object* v___x_4205_; 
v___x_4202_ = lean_st_ref_get(v_a_4200_);
v_env_4203_ = lean_ctor_get(v___x_4202_, 0);
lean_inc_ref(v_env_4203_);
lean_dec(v___x_4202_);
v___x_4204_ = l_Lean_getAttributeImpl(v_env_4203_, v_attrName_4196_);
v___x_4205_ = l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg(v___x_4204_, v_a_4199_, v_a_4200_);
if (lean_obj_tag(v___x_4205_) == 0)
{
lean_object* v_a_4206_; lean_object* v_add_4207_; lean_object* v___x_4208_; lean_object* v___x_4209_; 
v_a_4206_ = lean_ctor_get(v___x_4205_, 0);
lean_inc(v_a_4206_);
lean_dec_ref(v___x_4205_);
v_add_4207_ = lean_ctor_get(v_a_4206_, 1);
lean_inc_ref(v_add_4207_);
lean_dec(v_a_4206_);
v___x_4208_ = lean_box(v_kind_4198_);
lean_inc(v_a_4200_);
lean_inc_ref(v_a_4199_);
v___x_4209_ = lean_apply_6(v_add_4207_, v_declName_4195_, v_stx_4197_, v___x_4208_, v_a_4199_, v_a_4200_, lean_box(0));
return v___x_4209_;
}
else
{
lean_object* v_a_4210_; lean_object* v___x_4212_; uint8_t v_isShared_4213_; uint8_t v_isSharedCheck_4217_; 
lean_dec(v_stx_4197_);
lean_dec(v_declName_4195_);
v_a_4210_ = lean_ctor_get(v___x_4205_, 0);
v_isSharedCheck_4217_ = !lean_is_exclusive(v___x_4205_);
if (v_isSharedCheck_4217_ == 0)
{
v___x_4212_ = v___x_4205_;
v_isShared_4213_ = v_isSharedCheck_4217_;
goto v_resetjp_4211_;
}
else
{
lean_inc(v_a_4210_);
lean_dec(v___x_4205_);
v___x_4212_ = lean_box(0);
v_isShared_4213_ = v_isSharedCheck_4217_;
goto v_resetjp_4211_;
}
v_resetjp_4211_:
{
lean_object* v___x_4215_; 
if (v_isShared_4213_ == 0)
{
v___x_4215_ = v___x_4212_;
goto v_reusejp_4214_;
}
else
{
lean_object* v_reuseFailAlloc_4216_; 
v_reuseFailAlloc_4216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4216_, 0, v_a_4210_);
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
LEAN_EXPORT lean_object* l_Lean_Attribute_add___boxed(lean_object* v_declName_4218_, lean_object* v_attrName_4219_, lean_object* v_stx_4220_, lean_object* v_kind_4221_, lean_object* v_a_4222_, lean_object* v_a_4223_, lean_object* v_a_4224_){
_start:
{
uint8_t v_kind_boxed_4225_; lean_object* v_res_4226_; 
v_kind_boxed_4225_ = lean_unbox(v_kind_4221_);
v_res_4226_ = l_Lean_Attribute_add(v_declName_4218_, v_attrName_4219_, v_stx_4220_, v_kind_boxed_4225_, v_a_4222_, v_a_4223_);
lean_dec(v_a_4223_);
lean_dec_ref(v_a_4222_);
return v_res_4226_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0(lean_object* v_00_u03b1_4227_, lean_object* v_x_4228_, lean_object* v___y_4229_, lean_object* v___y_4230_){
_start:
{
lean_object* v___x_4232_; 
v___x_4232_ = l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg(v_x_4228_, v___y_4229_, v___y_4230_);
return v___x_4232_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___boxed(lean_object* v_00_u03b1_4233_, lean_object* v_x_4234_, lean_object* v___y_4235_, lean_object* v___y_4236_, lean_object* v___y_4237_){
_start:
{
lean_object* v_res_4238_; 
v_res_4238_ = l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0(v_00_u03b1_4233_, v_x_4234_, v___y_4235_, v___y_4236_);
lean_dec(v___y_4236_);
lean_dec_ref(v___y_4235_);
return v_res_4238_;
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_erase(lean_object* v_declName_4239_, lean_object* v_attrName_4240_, lean_object* v_a_4241_, lean_object* v_a_4242_){
_start:
{
lean_object* v___x_4244_; lean_object* v_env_4245_; lean_object* v___x_4246_; lean_object* v___x_4247_; 
v___x_4244_ = lean_st_ref_get(v_a_4242_);
v_env_4245_ = lean_ctor_get(v___x_4244_, 0);
lean_inc_ref(v_env_4245_);
lean_dec(v___x_4244_);
v___x_4246_ = l_Lean_getAttributeImpl(v_env_4245_, v_attrName_4240_);
v___x_4247_ = l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg(v___x_4246_, v_a_4241_, v_a_4242_);
if (lean_obj_tag(v___x_4247_) == 0)
{
lean_object* v_a_4248_; lean_object* v_erase_4249_; lean_object* v___x_4250_; 
v_a_4248_ = lean_ctor_get(v___x_4247_, 0);
lean_inc(v_a_4248_);
lean_dec_ref(v___x_4247_);
v_erase_4249_ = lean_ctor_get(v_a_4248_, 2);
lean_inc_ref(v_erase_4249_);
lean_dec(v_a_4248_);
lean_inc(v_a_4242_);
lean_inc_ref(v_a_4241_);
v___x_4250_ = lean_apply_4(v_erase_4249_, v_declName_4239_, v_a_4241_, v_a_4242_, lean_box(0));
return v___x_4250_;
}
else
{
lean_object* v_a_4251_; lean_object* v___x_4253_; uint8_t v_isShared_4254_; uint8_t v_isSharedCheck_4258_; 
lean_dec(v_declName_4239_);
v_a_4251_ = lean_ctor_get(v___x_4247_, 0);
v_isSharedCheck_4258_ = !lean_is_exclusive(v___x_4247_);
if (v_isSharedCheck_4258_ == 0)
{
v___x_4253_ = v___x_4247_;
v_isShared_4254_ = v_isSharedCheck_4258_;
goto v_resetjp_4252_;
}
else
{
lean_inc(v_a_4251_);
lean_dec(v___x_4247_);
v___x_4253_ = lean_box(0);
v_isShared_4254_ = v_isSharedCheck_4258_;
goto v_resetjp_4252_;
}
v_resetjp_4252_:
{
lean_object* v___x_4256_; 
if (v_isShared_4254_ == 0)
{
v___x_4256_ = v___x_4253_;
goto v_reusejp_4255_;
}
else
{
lean_object* v_reuseFailAlloc_4257_; 
v_reuseFailAlloc_4257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4257_, 0, v_a_4251_);
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
LEAN_EXPORT lean_object* l_Lean_Attribute_erase___boxed(lean_object* v_declName_4259_, lean_object* v_attrName_4260_, lean_object* v_a_4261_, lean_object* v_a_4262_, lean_object* v_a_4263_){
_start:
{
lean_object* v_res_4264_; 
v_res_4264_ = l_Lean_Attribute_erase(v_declName_4259_, v_attrName_4260_, v_a_4261_, v_a_4262_);
lean_dec(v_a_4262_);
lean_dec_ref(v_a_4261_);
return v_res_4264_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_updateEnvAttributesImpl_spec__0(lean_object* v_x_4265_, lean_object* v_x_4266_){
_start:
{
if (lean_obj_tag(v_x_4266_) == 0)
{
return v_x_4265_;
}
else
{
lean_object* v_key_4267_; lean_object* v_value_4268_; lean_object* v_tail_4269_; lean_object* v_newEntries_4270_; lean_object* v_map_4271_; uint8_t v___x_4272_; 
v_key_4267_ = lean_ctor_get(v_x_4266_, 0);
lean_inc(v_key_4267_);
v_value_4268_ = lean_ctor_get(v_x_4266_, 1);
lean_inc(v_value_4268_);
v_tail_4269_ = lean_ctor_get(v_x_4266_, 2);
lean_inc(v_tail_4269_);
lean_dec_ref(v_x_4266_);
v_newEntries_4270_ = lean_ctor_get(v_x_4265_, 0);
v_map_4271_ = lean_ctor_get(v_x_4265_, 1);
v___x_4272_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(v_map_4271_, v_key_4267_);
if (v___x_4272_ == 0)
{
lean_object* v___x_4274_; uint8_t v_isShared_4275_; uint8_t v_isSharedCheck_4281_; 
lean_inc_ref(v_map_4271_);
lean_inc(v_newEntries_4270_);
v_isSharedCheck_4281_ = !lean_is_exclusive(v_x_4265_);
if (v_isSharedCheck_4281_ == 0)
{
lean_object* v_unused_4282_; lean_object* v_unused_4283_; 
v_unused_4282_ = lean_ctor_get(v_x_4265_, 1);
lean_dec(v_unused_4282_);
v_unused_4283_ = lean_ctor_get(v_x_4265_, 0);
lean_dec(v_unused_4283_);
v___x_4274_ = v_x_4265_;
v_isShared_4275_ = v_isSharedCheck_4281_;
goto v_resetjp_4273_;
}
else
{
lean_dec(v_x_4265_);
v___x_4274_ = lean_box(0);
v_isShared_4275_ = v_isSharedCheck_4281_;
goto v_resetjp_4273_;
}
v_resetjp_4273_:
{
lean_object* v___x_4276_; lean_object* v___x_4278_; 
v___x_4276_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1___redArg(v_map_4271_, v_key_4267_, v_value_4268_);
if (v_isShared_4275_ == 0)
{
lean_ctor_set(v___x_4274_, 1, v___x_4276_);
v___x_4278_ = v___x_4274_;
goto v_reusejp_4277_;
}
else
{
lean_object* v_reuseFailAlloc_4280_; 
v_reuseFailAlloc_4280_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4280_, 0, v_newEntries_4270_);
lean_ctor_set(v_reuseFailAlloc_4280_, 1, v___x_4276_);
v___x_4278_ = v_reuseFailAlloc_4280_;
goto v_reusejp_4277_;
}
v_reusejp_4277_:
{
v_x_4265_ = v___x_4278_;
v_x_4266_ = v_tail_4269_;
goto _start;
}
}
}
else
{
lean_dec(v_value_4268_);
lean_dec(v_key_4267_);
v_x_4266_ = v_tail_4269_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_updateEnvAttributesImpl_spec__1(lean_object* v_as_4285_, size_t v_i_4286_, size_t v_stop_4287_, lean_object* v_b_4288_){
_start:
{
uint8_t v___x_4289_; 
v___x_4289_ = lean_usize_dec_eq(v_i_4286_, v_stop_4287_);
if (v___x_4289_ == 0)
{
lean_object* v___x_4290_; lean_object* v___x_4291_; size_t v___x_4292_; size_t v___x_4293_; 
v___x_4290_ = lean_array_uget_borrowed(v_as_4285_, v_i_4286_);
lean_inc(v___x_4290_);
v___x_4291_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_updateEnvAttributesImpl_spec__0(v_b_4288_, v___x_4290_);
v___x_4292_ = ((size_t)1ULL);
v___x_4293_ = lean_usize_add(v_i_4286_, v___x_4292_);
v_i_4286_ = v___x_4293_;
v_b_4288_ = v___x_4291_;
goto _start;
}
else
{
return v_b_4288_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_updateEnvAttributesImpl_spec__1___boxed(lean_object* v_as_4295_, lean_object* v_i_4296_, lean_object* v_stop_4297_, lean_object* v_b_4298_){
_start:
{
size_t v_i_boxed_4299_; size_t v_stop_boxed_4300_; lean_object* v_res_4301_; 
v_i_boxed_4299_ = lean_unbox_usize(v_i_4296_);
lean_dec(v_i_4296_);
v_stop_boxed_4300_ = lean_unbox_usize(v_stop_4297_);
lean_dec(v_stop_4297_);
v_res_4301_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_updateEnvAttributesImpl_spec__1(v_as_4295_, v_i_boxed_4299_, v_stop_boxed_4300_, v_b_4298_);
lean_dec_ref(v_as_4295_);
return v_res_4301_;
}
}
LEAN_EXPORT lean_object* lean_update_env_attributes(lean_object* v_env_4302_){
_start:
{
lean_object* v___x_4304_; lean_object* v___x_4305_; lean_object* v___x_4306_; lean_object* v___y_4308_; lean_object* v_toEnvExtension_4311_; lean_object* v_asyncMode_4312_; lean_object* v_buckets_4313_; lean_object* v___x_4314_; lean_object* v___x_4315_; lean_object* v___x_4316_; lean_object* v___x_4317_; lean_object* v___x_4318_; uint8_t v___x_4319_; 
v___x_4304_ = l_Lean_attributeMapRef;
v___x_4305_ = lean_st_ref_get(v___x_4304_);
v___x_4306_ = l_Lean_attributeExtension;
v_toEnvExtension_4311_ = lean_ctor_get(v___x_4306_, 0);
v_asyncMode_4312_ = lean_ctor_get(v_toEnvExtension_4311_, 2);
v_buckets_4313_ = lean_ctor_get(v___x_4305_, 1);
lean_inc_ref(v_buckets_4313_);
lean_dec(v___x_4305_);
v___x_4314_ = l_Lean_instInhabitedAttributeExtensionState_default;
v___x_4315_ = lean_box(0);
lean_inc_ref(v_env_4302_);
v___x_4316_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_4314_, v___x_4306_, v_env_4302_, v_asyncMode_4312_, v___x_4315_);
v___x_4317_ = lean_unsigned_to_nat(0u);
v___x_4318_ = lean_array_get_size(v_buckets_4313_);
v___x_4319_ = lean_nat_dec_lt(v___x_4317_, v___x_4318_);
if (v___x_4319_ == 0)
{
lean_dec_ref(v_buckets_4313_);
v___y_4308_ = v___x_4316_;
goto v___jp_4307_;
}
else
{
uint8_t v___x_4320_; 
v___x_4320_ = lean_nat_dec_le(v___x_4318_, v___x_4318_);
if (v___x_4320_ == 0)
{
if (v___x_4319_ == 0)
{
lean_dec_ref(v_buckets_4313_);
v___y_4308_ = v___x_4316_;
goto v___jp_4307_;
}
else
{
size_t v___x_4321_; size_t v___x_4322_; lean_object* v___x_4323_; 
v___x_4321_ = ((size_t)0ULL);
v___x_4322_ = lean_usize_of_nat(v___x_4318_);
v___x_4323_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_updateEnvAttributesImpl_spec__1(v_buckets_4313_, v___x_4321_, v___x_4322_, v___x_4316_);
lean_dec_ref(v_buckets_4313_);
v___y_4308_ = v___x_4323_;
goto v___jp_4307_;
}
}
else
{
size_t v___x_4324_; size_t v___x_4325_; lean_object* v___x_4326_; 
v___x_4324_ = ((size_t)0ULL);
v___x_4325_ = lean_usize_of_nat(v___x_4318_);
v___x_4326_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_updateEnvAttributesImpl_spec__1(v_buckets_4313_, v___x_4324_, v___x_4325_, v___x_4316_);
lean_dec_ref(v_buckets_4313_);
v___y_4308_ = v___x_4326_;
goto v___jp_4307_;
}
}
v___jp_4307_:
{
lean_object* v___x_4309_; lean_object* v___x_4310_; 
v___x_4309_ = l_Lean_PersistentEnvExtension_setState___redArg(v___x_4306_, v_env_4302_, v___y_4308_);
v___x_4310_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4310_, 0, v___x_4309_);
return v___x_4310_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_updateEnvAttributesImpl___boxed(lean_object* v_env_4327_, lean_object* v_a_4328_){
_start:
{
lean_object* v_res_4329_; 
v_res_4329_ = lean_update_env_attributes(v_env_4327_);
return v_res_4329_;
}
}
LEAN_EXPORT lean_object* lean_get_num_attributes(){
_start:
{
lean_object* v___x_4331_; lean_object* v___x_4332_; lean_object* v_size_4333_; lean_object* v___x_4334_; 
v___x_4331_ = l_Lean_attributeMapRef;
v___x_4332_ = lean_st_ref_get(v___x_4331_);
v_size_4333_ = lean_ctor_get(v___x_4332_, 0);
lean_inc(v_size_4333_);
lean_dec(v___x_4332_);
v___x_4334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4334_, 0, v_size_4333_);
return v___x_4334_;
}
}
LEAN_EXPORT lean_object* l_Lean_getNumBuiltinAttributesImpl___boxed(lean_object* v_a_4335_){
_start:
{
lean_object* v_res_4336_; 
v_res_4336_ = lean_get_num_attributes();
return v_res_4336_;
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
res = l_Lean_initFn_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_attributeMapRef = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_attributeMapRef);
lean_dec_ref(res);
l_Lean_instInhabitedTagAttribute_default = _init_l_Lean_instInhabitedTagAttribute_default();
lean_mark_persistent(l_Lean_instInhabitedTagAttribute_default);
l_Lean_instInhabitedTagAttribute = _init_l_Lean_instInhabitedTagAttribute();
lean_mark_persistent(l_Lean_instInhabitedTagAttribute);
res = l_Lean_initFn_00___x40_Lean_Attributes_2990505691____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_attributeImplBuilderTableRef = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_attributeImplBuilderTableRef);
lean_dec_ref(res);
l_Lean_instInhabitedAttributeExtensionState_default = _init_l_Lean_instInhabitedAttributeExtensionState_default();
lean_mark_persistent(l_Lean_instInhabitedAttributeExtensionState_default);
l_Lean_instInhabitedAttributeExtensionState = _init_l_Lean_instInhabitedAttributeExtensionState();
lean_mark_persistent(l_Lean_instInhabitedAttributeExtensionState);
res = l_Lean_initFn_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_();
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
