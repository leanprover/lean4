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
lean_object* l_Lean_Name_quickLt___boxed(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedMessageData_default;
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Environment_evalConst___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instInhabitedEnvExtension_default(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
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
uint8_t l_Lean_instDecidableEqOLeanLevel(uint8_t, uint8_t);
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
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__2(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__3(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__3___boxed(lean_object*);
static const lean_closure_object l_Lean_instInhabitedTagAttribute_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instInhabitedTagAttribute_default___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instInhabitedTagAttribute_default___closed__0 = (const lean_object*)&l_Lean_instInhabitedTagAttribute_default___closed__0_value;
static const lean_closure_object l_Lean_instInhabitedTagAttribute_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instInhabitedTagAttribute_default___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instInhabitedTagAttribute_default___closed__1 = (const lean_object*)&l_Lean_instInhabitedTagAttribute_default___closed__1_value;
static const lean_closure_object l_Lean_instInhabitedTagAttribute_default___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instInhabitedTagAttribute_default___lam__2___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
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
static const lean_closure_object l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_quickLt___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__2___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__2___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerTagAttribute_spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerTagAttribute_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerTagAttribute_spec__1_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__3(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__3___boxed(lean_object*, lean_object*, lean_object*);
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
static const lean_closure_object l_Lean_registerTagAttribute___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_registerTagAttribute___lam__3___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__2(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__3(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__3___boxed(lean_object*);
static const lean_closure_object l_Lean_instInhabitedParametricAttribute_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instInhabitedParametricAttribute_default___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instInhabitedParametricAttribute_default___closed__0 = (const lean_object*)&l_Lean_instInhabitedParametricAttribute_default___closed__0_value;
static const lean_closure_object l_Lean_instInhabitedParametricAttribute_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instInhabitedParametricAttribute_default___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instInhabitedParametricAttribute_default___closed__1 = (const lean_object*)&l_Lean_instInhabitedParametricAttribute_default___closed__1_value;
static const lean_closure_object l_Lean_instInhabitedParametricAttribute_default___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instInhabitedParametricAttribute_default___lam__2___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
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
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___lam__1(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___lam__2(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___lam__2___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_instInhabitedEnumAttributes_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instInhabitedEnumAttributes_default___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instInhabitedEnumAttributes_default___closed__0 = (const lean_object*)&l_Lean_instInhabitedEnumAttributes_default___closed__0_value;
static const lean_closure_object l_Lean_instInhabitedEnumAttributes_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instInhabitedEnumAttributes_default___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instInhabitedEnumAttributes_default___closed__1 = (const lean_object*)&l_Lean_instInhabitedEnumAttributes_default___closed__1_value;
static const lean_closure_object l_Lean_instInhabitedEnumAttributes_default___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instInhabitedEnumAttributes_default___lam__2___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
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
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__3(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*);
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
static const lean_closure_object l_Lean_registerEnumAttributes___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_registerEnumAttributes___redArg___lam__3___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
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
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn___lam__1_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn___lam__2_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(lean_object*);
static const lean_closure_object l_Lean_initFn___closed__0_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_initFn___lam__0_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2____boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
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
v___x_598_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_598_, 0, v___x_597_);
lean_ctor_set(v___x_598_, 1, v___x_597_);
lean_ctor_set(v___x_598_, 2, v___x_597_);
lean_ctor_set(v___x_598_, 3, v___x_596_);
lean_ctor_set(v___x_598_, 4, v___x_596_);
lean_ctor_set(v___x_598_, 5, v___x_596_);
lean_ctor_set(v___x_598_, 6, v___x_596_);
lean_ctor_set(v___x_598_, 7, v___x_596_);
lean_ctor_set(v___x_598_, 8, v___x_596_);
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
lean_object* v___y_1333_; lean_object* v___y_1334_; uint8_t v___y_1335_; lean_object* v___y_1336_; lean_object* v___y_1337_; uint8_t v___y_1338_; lean_object* v___y_1339_; lean_object* v___y_1340_; lean_object* v___y_1341_; lean_object* v___y_1369_; lean_object* v___y_1370_; uint8_t v___y_1371_; lean_object* v___y_1372_; lean_object* v___y_1373_; uint8_t v___y_1374_; uint8_t v___y_1375_; lean_object* v___y_1376_; lean_object* v___y_1394_; uint8_t v___y_1395_; lean_object* v___y_1396_; lean_object* v___y_1397_; uint8_t v___y_1398_; lean_object* v___y_1399_; uint8_t v___y_1400_; lean_object* v___y_1401_; lean_object* v___y_1405_; lean_object* v___y_1406_; uint8_t v___y_1407_; lean_object* v___y_1408_; lean_object* v___y_1409_; uint8_t v___y_1410_; uint8_t v___y_1411_; uint8_t v___x_1416_; lean_object* v___y_1418_; lean_object* v___y_1419_; lean_object* v___y_1420_; lean_object* v___y_1421_; uint8_t v___y_1422_; uint8_t v___y_1423_; uint8_t v___y_1424_; uint8_t v___y_1426_; uint8_t v___x_1441_; 
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
lean_ctor_set(v___x_1358_, 1, v___y_1339_);
lean_inc_ref(v___y_1337_);
v___x_1359_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1359_, 0, v___y_1337_);
lean_ctor_set(v___x_1359_, 1, v___y_1333_);
lean_ctor_set(v___x_1359_, 2, v___y_1336_);
lean_ctor_set(v___x_1359_, 3, v___y_1334_);
lean_ctor_set(v___x_1359_, 4, v___x_1358_);
lean_ctor_set_uint8(v___x_1359_, sizeof(void*)*5, v___y_1335_);
lean_ctor_set_uint8(v___x_1359_, sizeof(void*)*5 + 1, v___y_1338_);
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
lean_inc_ref(v___y_1372_);
v___x_1383_ = l_Lean_FileMap_toPosition(v___y_1372_, v___y_1370_);
lean_dec(v___y_1370_);
lean_inc_ref(v___y_1372_);
v___x_1384_ = l_Lean_FileMap_toPosition(v___y_1372_, v___y_1376_);
lean_dec(v___y_1376_);
v___x_1385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1385_, 0, v___x_1384_);
v___x_1386_ = ((lean_object*)(l_Lean_instInhabitedAttributeImplCore_default___closed__0));
if (v___y_1374_ == 0)
{
lean_del_object(v___x_1381_);
lean_dec_ref(v___y_1369_);
v___y_1333_ = v___x_1383_;
v___y_1334_ = v___x_1386_;
v___y_1335_ = v___y_1371_;
v___y_1336_ = v___x_1385_;
v___y_1337_ = v___y_1373_;
v___y_1338_ = v___y_1375_;
v___y_1339_ = v_a_1379_;
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
v___y_1333_ = v___x_1383_;
v___y_1334_ = v___x_1386_;
v___y_1335_ = v___y_1371_;
v___y_1336_ = v___x_1385_;
v___y_1337_ = v___y_1373_;
v___y_1338_ = v___y_1375_;
v___y_1339_ = v_a_1379_;
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
v___x_1402_ = l_Lean_Syntax_getTailPos_x3f(v___y_1399_, v___y_1395_);
lean_dec(v___y_1399_);
if (lean_obj_tag(v___x_1402_) == 0)
{
lean_inc(v___y_1401_);
v___y_1369_ = v___y_1394_;
v___y_1370_ = v___y_1401_;
v___y_1371_ = v___y_1395_;
v___y_1372_ = v___y_1396_;
v___y_1373_ = v___y_1397_;
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
v___y_1372_ = v___y_1396_;
v___y_1373_ = v___y_1397_;
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
v___x_1413_ = l_Lean_Syntax_getPos_x3f(v_ref_1412_, v___y_1407_);
if (lean_obj_tag(v___x_1413_) == 0)
{
lean_object* v___x_1414_; 
v___x_1414_ = lean_unsigned_to_nat(0u);
v___y_1394_ = v___y_1405_;
v___y_1395_ = v___y_1407_;
v___y_1396_ = v___y_1408_;
v___y_1397_ = v___y_1409_;
v___y_1398_ = v___y_1410_;
v___y_1399_ = v_ref_1412_;
v___y_1400_ = v___y_1411_;
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
v___y_1396_ = v___y_1408_;
v___y_1397_ = v___y_1409_;
v___y_1398_ = v___y_1410_;
v___y_1399_ = v_ref_1412_;
v___y_1400_ = v___y_1411_;
v___y_1401_ = v_val_1415_;
goto v___jp_1393_;
}
}
v___jp_1417_:
{
if (v___y_1424_ == 0)
{
v___y_1405_ = v___y_1421_;
v___y_1406_ = v___y_1418_;
v___y_1407_ = v___y_1423_;
v___y_1408_ = v___y_1419_;
v___y_1409_ = v___y_1420_;
v___y_1410_ = v___y_1422_;
v___y_1411_ = v_severity_1327_;
goto v___jp_1404_;
}
else
{
v___y_1405_ = v___y_1421_;
v___y_1406_ = v___y_1418_;
v___y_1407_ = v___y_1423_;
v___y_1408_ = v___y_1419_;
v___y_1409_ = v___y_1420_;
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
v___y_1419_ = v_fileMap_1428_;
v___y_1420_ = v_fileName_1427_;
v___y_1421_ = v___f_1434_;
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
v___y_1419_ = v_fileMap_1428_;
v___y_1420_ = v_fileName_1427_;
v___y_1421_ = v___f_1434_;
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
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__2(lean_object* v_x_1663_, lean_object* v_x_1664_, uint8_t v_x_1665_){
_start:
{
lean_object* v___x_1666_; 
v___x_1666_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___lam__2___closed__0));
return v___x_1666_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__2___boxed(lean_object* v_x_1667_, lean_object* v_x_1668_, lean_object* v_x_1669_){
_start:
{
uint8_t v_x_77__boxed_1670_; lean_object* v_res_1671_; 
v_x_77__boxed_1670_ = lean_unbox(v_x_1669_);
v_res_1671_ = l_Lean_instInhabitedTagAttribute_default___lam__2(v_x_1667_, v_x_1668_, v_x_77__boxed_1670_);
lean_dec(v_x_1668_);
lean_dec_ref(v_x_1667_);
return v_res_1671_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__3(lean_object* v_x_1672_){
_start:
{
lean_object* v___x_1673_; 
v___x_1673_ = lean_box(0);
return v___x_1673_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__3___boxed(lean_object* v_x_1674_){
_start:
{
lean_object* v_res_1675_; 
v_res_1675_ = l_Lean_instInhabitedTagAttribute_default___lam__3(v_x_1674_);
lean_dec(v_x_1674_);
return v_res_1675_;
}
}
static lean_object* _init_l_Lean_instInhabitedTagAttribute_default___closed__4(void){
_start:
{
lean_object* v___x_1680_; 
v___x_1680_ = l_Lean_instInhabitedEnvExtension_default(lean_box(0));
return v___x_1680_;
}
}
static lean_object* _init_l_Lean_instInhabitedTagAttribute_default___closed__5(void){
_start:
{
lean_object* v___f_1681_; lean_object* v___f_1682_; lean_object* v___f_1683_; lean_object* v___f_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; 
v___f_1681_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___closed__3));
v___f_1682_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___closed__2));
v___f_1683_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___closed__1));
v___f_1684_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___closed__0));
v___x_1685_ = lean_box(0);
v___x_1686_ = lean_obj_once(&l_Lean_instInhabitedTagAttribute_default___closed__4, &l_Lean_instInhabitedTagAttribute_default___closed__4_once, _init_l_Lean_instInhabitedTagAttribute_default___closed__4);
v___x_1687_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1687_, 0, v___x_1686_);
lean_ctor_set(v___x_1687_, 1, v___x_1685_);
lean_ctor_set(v___x_1687_, 2, v___f_1684_);
lean_ctor_set(v___x_1687_, 3, v___f_1683_);
lean_ctor_set(v___x_1687_, 4, v___f_1682_);
lean_ctor_set(v___x_1687_, 5, v___f_1681_);
return v___x_1687_;
}
}
static lean_object* _init_l_Lean_instInhabitedTagAttribute_default___closed__6(void){
_start:
{
lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; 
v___x_1688_ = lean_obj_once(&l_Lean_instInhabitedTagAttribute_default___closed__5, &l_Lean_instInhabitedTagAttribute_default___closed__5_once, _init_l_Lean_instInhabitedTagAttribute_default___closed__5);
v___x_1689_ = ((lean_object*)(l_Lean_instInhabitedAttributeImpl_default));
v___x_1690_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1690_, 0, v___x_1689_);
lean_ctor_set(v___x_1690_, 1, v___x_1688_);
return v___x_1690_;
}
}
static lean_object* _init_l_Lean_instInhabitedTagAttribute_default(void){
_start:
{
lean_object* v___x_1691_; 
v___x_1691_ = lean_obj_once(&l_Lean_instInhabitedTagAttribute_default___closed__6, &l_Lean_instInhabitedTagAttribute_default___closed__6_once, _init_l_Lean_instInhabitedTagAttribute_default___closed__6);
return v___x_1691_;
}
}
static lean_object* _init_l_Lean_instInhabitedTagAttribute(void){
_start:
{
lean_object* v___x_1692_; 
v___x_1692_ = l_Lean_instInhabitedTagAttribute_default;
return v___x_1692_;
}
}
static lean_object* _init_l_Lean_registerTagAttribute___auto__1(void){
_start:
{
lean_object* v___x_1693_; 
v___x_1693_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__28, &l_Lean_AttributeImplCore_ref___autoParam___closed__28_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__28);
return v___x_1693_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__0(lean_object* v_x_1694_){
_start:
{
lean_object* v___x_1695_; 
v___x_1695_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___lam__2___closed__0));
return v___x_1695_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__0___boxed(lean_object* v_x_1696_){
_start:
{
lean_object* v_res_1697_; 
v_res_1697_ = l_Lean_registerTagAttribute___lam__0(v_x_1696_);
lean_dec(v_x_1696_);
return v_res_1697_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerTagAttribute_spec__0(lean_object* v_newState_1698_, lean_object* v_x_1699_, lean_object* v_x_1700_){
_start:
{
if (lean_obj_tag(v_x_1700_) == 0)
{
return v_x_1699_;
}
else
{
lean_object* v_head_1701_; lean_object* v_tail_1702_; uint8_t v___x_1703_; 
v_head_1701_ = lean_ctor_get(v_x_1700_, 0);
lean_inc(v_head_1701_);
v_tail_1702_ = lean_ctor_get(v_x_1700_, 1);
lean_inc(v_tail_1702_);
lean_dec_ref(v_x_1700_);
v___x_1703_ = l_Lean_NameSet_contains(v_newState_1698_, v_head_1701_);
if (v___x_1703_ == 0)
{
lean_dec(v_head_1701_);
v_x_1700_ = v_tail_1702_;
goto _start;
}
else
{
lean_object* v___x_1705_; 
v___x_1705_ = l_Lean_NameSet_insert(v_x_1699_, v_head_1701_);
v_x_1699_ = v___x_1705_;
v_x_1700_ = v_tail_1702_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerTagAttribute_spec__0___boxed(lean_object* v_newState_1707_, lean_object* v_x_1708_, lean_object* v_x_1709_){
_start:
{
lean_object* v_res_1710_; 
v_res_1710_ = l_List_foldl___at___00Lean_registerTagAttribute_spec__0(v_newState_1707_, v_x_1708_, v_x_1709_);
lean_dec(v_newState_1707_);
return v_res_1710_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__1(lean_object* v_x_1711_, lean_object* v_newState_1712_, lean_object* v_newConsts_1713_, lean_object* v_s_1714_){
_start:
{
lean_object* v___x_1715_; 
v___x_1715_ = l_List_foldl___at___00Lean_registerTagAttribute_spec__0(v_newState_1712_, v_s_1714_, v_newConsts_1713_);
return v___x_1715_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__1___boxed(lean_object* v_x_1716_, lean_object* v_newState_1717_, lean_object* v_newConsts_1718_, lean_object* v_s_1719_){
_start:
{
lean_object* v_res_1720_; 
v_res_1720_ = l_Lean_registerTagAttribute___lam__1(v_x_1716_, v_newState_1717_, v_newConsts_1718_, v_s_1719_);
lean_dec(v_newState_1717_);
lean_dec(v_x_1716_);
return v_res_1720_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__2(lean_object* v_s_1733_){
_start:
{
lean_object* v___x_1734_; lean_object* v___y_1736_; 
v___x_1734_ = ((lean_object*)(l_Lean_registerTagAttribute___lam__2___closed__5));
if (lean_obj_tag(v_s_1733_) == 0)
{
lean_object* v_size_1740_; 
v_size_1740_ = lean_ctor_get(v_s_1733_, 0);
lean_inc(v_size_1740_);
lean_dec_ref(v_s_1733_);
v___y_1736_ = v_size_1740_;
goto v___jp_1735_;
}
else
{
lean_object* v___x_1741_; 
v___x_1741_ = lean_unsigned_to_nat(0u);
v___y_1736_ = v___x_1741_;
goto v___jp_1735_;
}
v___jp_1735_:
{
lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; 
v___x_1737_ = l_Nat_reprFast(v___y_1736_);
v___x_1738_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1738_, 0, v___x_1737_);
v___x_1739_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1739_, 0, v___x_1734_);
lean_ctor_set(v___x_1739_, 1, v___x_1738_);
return v___x_1739_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__2___redArg(lean_object* v_as_1743_, lean_object* v_lo_1744_, lean_object* v_hi_1745_){
_start:
{
uint8_t v___x_1746_; 
v___x_1746_ = lean_nat_dec_lt(v_lo_1744_, v_hi_1745_);
if (v___x_1746_ == 0)
{
lean_dec(v_lo_1744_);
return v_as_1743_;
}
else
{
lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v_fst_1749_; lean_object* v_snd_1750_; uint8_t v___x_1751_; 
v___x_1747_ = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__2___redArg___closed__0));
lean_inc(v_lo_1744_);
v___x_1748_ = l_Array_qpartition___redArg(v_as_1743_, v___x_1747_, v_lo_1744_, v_hi_1745_);
v_fst_1749_ = lean_ctor_get(v___x_1748_, 0);
lean_inc(v_fst_1749_);
v_snd_1750_ = lean_ctor_get(v___x_1748_, 1);
lean_inc(v_snd_1750_);
lean_dec_ref(v___x_1748_);
v___x_1751_ = lean_nat_dec_le(v_hi_1745_, v_fst_1749_);
if (v___x_1751_ == 0)
{
lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; 
v___x_1752_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__2___redArg(v_snd_1750_, v_lo_1744_, v_fst_1749_);
v___x_1753_ = lean_unsigned_to_nat(1u);
v___x_1754_ = lean_nat_add(v_fst_1749_, v___x_1753_);
lean_dec(v_fst_1749_);
v_as_1743_ = v___x_1752_;
v_lo_1744_ = v___x_1754_;
goto _start;
}
else
{
lean_dec(v_fst_1749_);
lean_dec(v_lo_1744_);
return v_snd_1750_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__2___redArg___boxed(lean_object* v_as_1756_, lean_object* v_lo_1757_, lean_object* v_hi_1758_){
_start:
{
lean_object* v_res_1759_; 
v_res_1759_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__2___redArg(v_as_1756_, v_lo_1757_, v_hi_1758_);
lean_dec(v_hi_1758_);
return v_res_1759_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerTagAttribute_spec__3(lean_object* v_env_1760_, lean_object* v_as_1761_, size_t v_i_1762_, size_t v_stop_1763_, lean_object* v_b_1764_){
_start:
{
lean_object* v___y_1766_; uint8_t v___x_1770_; 
v___x_1770_ = lean_usize_dec_eq(v_i_1762_, v_stop_1763_);
if (v___x_1770_ == 0)
{
lean_object* v___x_1771_; uint8_t v___x_1772_; 
v___x_1771_ = lean_array_uget_borrowed(v_as_1761_, v_i_1762_);
lean_inc(v___x_1771_);
lean_inc_ref(v_env_1760_);
v___x_1772_ = l_Lean_Environment_contains(v_env_1760_, v___x_1771_, v___x_1770_);
if (v___x_1772_ == 0)
{
v___y_1766_ = v_b_1764_;
goto v___jp_1765_;
}
else
{
lean_object* v___x_1773_; 
lean_inc(v___x_1771_);
v___x_1773_ = lean_array_push(v_b_1764_, v___x_1771_);
v___y_1766_ = v___x_1773_;
goto v___jp_1765_;
}
}
else
{
lean_dec_ref(v_env_1760_);
return v_b_1764_;
}
v___jp_1765_:
{
size_t v___x_1767_; size_t v___x_1768_; 
v___x_1767_ = ((size_t)1ULL);
v___x_1768_ = lean_usize_add(v_i_1762_, v___x_1767_);
v_i_1762_ = v___x_1768_;
v_b_1764_ = v___y_1766_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerTagAttribute_spec__3___boxed(lean_object* v_env_1774_, lean_object* v_as_1775_, lean_object* v_i_1776_, lean_object* v_stop_1777_, lean_object* v_b_1778_){
_start:
{
size_t v_i_boxed_1779_; size_t v_stop_boxed_1780_; lean_object* v_res_1781_; 
v_i_boxed_1779_ = lean_unbox_usize(v_i_1776_);
lean_dec(v_i_1776_);
v_stop_boxed_1780_ = lean_unbox_usize(v_stop_1777_);
lean_dec(v_stop_1777_);
v_res_1781_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerTagAttribute_spec__3(v_env_1774_, v_as_1775_, v_i_boxed_1779_, v_stop_boxed_1780_, v_b_1778_);
lean_dec_ref(v_as_1775_);
return v_res_1781_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerTagAttribute_spec__1_spec__1(lean_object* v_init_1782_, lean_object* v_x_1783_){
_start:
{
if (lean_obj_tag(v_x_1783_) == 0)
{
lean_object* v_k_1784_; lean_object* v_l_1785_; lean_object* v_r_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; 
v_k_1784_ = lean_ctor_get(v_x_1783_, 1);
lean_inc(v_k_1784_);
v_l_1785_ = lean_ctor_get(v_x_1783_, 3);
lean_inc(v_l_1785_);
v_r_1786_ = lean_ctor_get(v_x_1783_, 4);
lean_inc(v_r_1786_);
lean_dec_ref(v_x_1783_);
v___x_1787_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerTagAttribute_spec__1_spec__1(v_init_1782_, v_l_1785_);
v___x_1788_ = lean_array_push(v___x_1787_, v_k_1784_);
v_init_1782_ = v___x_1788_;
v_x_1783_ = v_r_1786_;
goto _start;
}
else
{
return v_init_1782_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__3(lean_object* v_env_1790_, lean_object* v_es_1791_, uint8_t v_x_1792_){
_start:
{
lean_object* v___y_1794_; lean_object* v___y_1795_; lean_object* v___y_1796_; lean_object* v___y_1797_; lean_object* v___x_1801_; lean_object* v___y_1803_; lean_object* v___x_1809_; lean_object* v_r_1810_; lean_object* v___x_1811_; uint8_t v___x_1812_; 
v___x_1801_ = lean_unsigned_to_nat(0u);
v___x_1809_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___lam__2___closed__0));
v_r_1810_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerTagAttribute_spec__1_spec__1(v___x_1809_, v_es_1791_);
v___x_1811_ = lean_array_get_size(v_r_1810_);
v___x_1812_ = lean_nat_dec_lt(v___x_1801_, v___x_1811_);
if (v___x_1812_ == 0)
{
lean_dec_ref(v_r_1810_);
lean_dec_ref(v_env_1790_);
v___y_1803_ = v___x_1809_;
goto v___jp_1802_;
}
else
{
uint8_t v___x_1813_; 
v___x_1813_ = lean_nat_dec_le(v___x_1811_, v___x_1811_);
if (v___x_1813_ == 0)
{
if (v___x_1812_ == 0)
{
lean_dec_ref(v_r_1810_);
lean_dec_ref(v_env_1790_);
v___y_1803_ = v___x_1809_;
goto v___jp_1802_;
}
else
{
size_t v___x_1814_; size_t v___x_1815_; lean_object* v___x_1816_; 
v___x_1814_ = ((size_t)0ULL);
v___x_1815_ = lean_usize_of_nat(v___x_1811_);
v___x_1816_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerTagAttribute_spec__3(v_env_1790_, v_r_1810_, v___x_1814_, v___x_1815_, v___x_1809_);
lean_dec_ref(v_r_1810_);
v___y_1803_ = v___x_1816_;
goto v___jp_1802_;
}
}
else
{
size_t v___x_1817_; size_t v___x_1818_; lean_object* v___x_1819_; 
v___x_1817_ = ((size_t)0ULL);
v___x_1818_ = lean_usize_of_nat(v___x_1811_);
v___x_1819_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerTagAttribute_spec__3(v_env_1790_, v_r_1810_, v___x_1817_, v___x_1818_, v___x_1809_);
lean_dec_ref(v_r_1810_);
v___y_1803_ = v___x_1819_;
goto v___jp_1802_;
}
}
v___jp_1793_:
{
uint8_t v___x_1798_; 
lean_dec(v___y_1796_);
v___x_1798_ = lean_nat_dec_le(v___y_1797_, v___y_1795_);
if (v___x_1798_ == 0)
{
lean_object* v___x_1799_; 
lean_dec(v___y_1795_);
lean_inc(v___y_1797_);
v___x_1799_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__2___redArg(v___y_1794_, v___y_1797_, v___y_1797_);
lean_dec(v___y_1797_);
return v___x_1799_;
}
else
{
lean_object* v___x_1800_; 
v___x_1800_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__2___redArg(v___y_1794_, v___y_1797_, v___y_1795_);
lean_dec(v___y_1795_);
return v___x_1800_;
}
}
v___jp_1802_:
{
lean_object* v___x_1804_; uint8_t v___x_1805_; 
v___x_1804_ = lean_array_get_size(v___y_1803_);
v___x_1805_ = lean_nat_dec_eq(v___x_1804_, v___x_1801_);
if (v___x_1805_ == 0)
{
lean_object* v___x_1806_; lean_object* v___x_1807_; uint8_t v___x_1808_; 
v___x_1806_ = lean_unsigned_to_nat(1u);
v___x_1807_ = lean_nat_sub(v___x_1804_, v___x_1806_);
v___x_1808_ = lean_nat_dec_le(v___x_1801_, v___x_1807_);
if (v___x_1808_ == 0)
{
lean_inc(v___x_1807_);
v___y_1794_ = v___y_1803_;
v___y_1795_ = v___x_1807_;
v___y_1796_ = v___x_1804_;
v___y_1797_ = v___x_1807_;
goto v___jp_1793_;
}
else
{
v___y_1794_ = v___y_1803_;
v___y_1795_ = v___x_1807_;
v___y_1796_ = v___x_1804_;
v___y_1797_ = v___x_1801_;
goto v___jp_1793_;
}
}
else
{
return v___y_1803_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__3___boxed(lean_object* v_env_1820_, lean_object* v_es_1821_, lean_object* v_x_1822_){
_start:
{
uint8_t v_x_2216__boxed_1823_; lean_object* v_res_1824_; 
v_x_2216__boxed_1823_ = lean_unbox(v_x_1822_);
v_res_1824_ = l_Lean_registerTagAttribute___lam__3(v_env_1820_, v_es_1821_, v_x_2216__boxed_1823_);
return v_res_1824_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__4(lean_object* v___x_1825_, lean_object* v_x_1826_, lean_object* v_x_1827_){
_start:
{
lean_object* v___x_1829_; 
v___x_1829_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1829_, 0, v___x_1825_);
return v___x_1829_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__4___boxed(lean_object* v___x_1830_, lean_object* v_x_1831_, lean_object* v_x_1832_, lean_object* v___y_1833_){
_start:
{
lean_object* v_res_1834_; 
v_res_1834_ = l_Lean_registerTagAttribute___lam__4(v___x_1830_, v_x_1831_, v_x_1832_);
lean_dec_ref(v_x_1832_);
lean_dec_ref(v_x_1831_);
return v_res_1834_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__5(lean_object* v___x_1835_){
_start:
{
lean_object* v___x_1837_; 
v___x_1837_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1837_, 0, v___x_1835_);
return v___x_1837_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__5___boxed(lean_object* v___x_1838_, lean_object* v___y_1839_){
_start:
{
lean_object* v_res_1840_; 
v_res_1840_ = l_Lean_registerTagAttribute___lam__5(v___x_1838_);
return v_res_1840_;
}
}
static lean_object* _init_l_Lean_registerTagAttribute___lam__6___closed__1(void){
_start:
{
lean_object* v___x_1842_; lean_object* v___x_1843_; 
v___x_1842_ = ((lean_object*)(l_Lean_registerTagAttribute___lam__6___closed__0));
v___x_1843_ = l_Lean_stringToMessageData(v___x_1842_);
return v___x_1843_;
}
}
static lean_object* _init_l_Lean_registerTagAttribute___lam__6___closed__3(void){
_start:
{
lean_object* v___x_1845_; lean_object* v___x_1846_; 
v___x_1845_ = ((lean_object*)(l_Lean_registerTagAttribute___lam__6___closed__2));
v___x_1846_ = l_Lean_stringToMessageData(v___x_1845_);
return v___x_1846_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__6(lean_object* v_name_1847_, lean_object* v_decl_1848_, lean_object* v___y_1849_, lean_object* v___y_1850_){
_start:
{
lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; 
v___x_1852_ = lean_obj_once(&l_Lean_registerTagAttribute___lam__6___closed__1, &l_Lean_registerTagAttribute___lam__6___closed__1_once, _init_l_Lean_registerTagAttribute___lam__6___closed__1);
v___x_1853_ = l_Lean_MessageData_ofName(v_name_1847_);
v___x_1854_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1854_, 0, v___x_1852_);
lean_ctor_set(v___x_1854_, 1, v___x_1853_);
v___x_1855_ = lean_obj_once(&l_Lean_registerTagAttribute___lam__6___closed__3, &l_Lean_registerTagAttribute___lam__6___closed__3_once, _init_l_Lean_registerTagAttribute___lam__6___closed__3);
v___x_1856_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1856_, 0, v___x_1854_);
lean_ctor_set(v___x_1856_, 1, v___x_1855_);
v___x_1857_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0_spec__0___redArg(v___x_1856_, v___y_1849_, v___y_1850_);
return v___x_1857_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__6___boxed(lean_object* v_name_1858_, lean_object* v_decl_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_){
_start:
{
lean_object* v_res_1863_; 
v_res_1863_ = l_Lean_registerTagAttribute___lam__6(v_name_1858_, v_decl_1859_, v___y_1860_, v___y_1861_);
lean_dec(v___y_1861_);
lean_dec_ref(v___y_1860_);
lean_dec(v_decl_1859_);
return v_res_1863_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg(lean_object* v_attrName_1864_, lean_object* v_declName_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_){
_start:
{
lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; uint8_t v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; 
v___x_1869_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1);
v___x_1870_ = l_Lean_MessageData_ofName(v_attrName_1864_);
v___x_1871_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1871_, 0, v___x_1869_);
lean_ctor_set(v___x_1871_, 1, v___x_1870_);
v___x_1872_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__3, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__3_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__3);
v___x_1873_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1873_, 0, v___x_1871_);
lean_ctor_set(v___x_1873_, 1, v___x_1872_);
v___x_1874_ = 0;
v___x_1875_ = l_Lean_MessageData_ofConstName(v_declName_1865_, v___x_1874_);
v___x_1876_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1876_, 0, v___x_1873_);
lean_ctor_set(v___x_1876_, 1, v___x_1875_);
v___x_1877_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__5, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__5_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__5);
v___x_1878_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1878_, 0, v___x_1876_);
lean_ctor_set(v___x_1878_, 1, v___x_1877_);
v___x_1879_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0_spec__0___redArg(v___x_1878_, v___y_1866_, v___y_1867_);
return v___x_1879_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg___boxed(lean_object* v_attrName_1880_, lean_object* v_declName_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_){
_start:
{
lean_object* v_res_1885_; 
v_res_1885_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg(v_attrName_1880_, v_declName_1881_, v___y_1882_, v___y_1883_);
lean_dec(v___y_1883_);
lean_dec_ref(v___y_1882_);
return v_res_1885_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___redArg(lean_object* v_attrName_1886_, lean_object* v_declName_1887_, lean_object* v_asyncPrefix_x3f_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_){
_start:
{
lean_object* v___y_1893_; 
if (lean_obj_tag(v_asyncPrefix_x3f_1888_) == 0)
{
lean_object* v___x_1906_; 
v___x_1906_ = l_Lean_MessageData_nil;
v___y_1893_ = v___x_1906_;
goto v___jp_1892_;
}
else
{
lean_object* v_val_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; 
v_val_1907_ = lean_ctor_get(v_asyncPrefix_x3f_1888_, 0);
lean_inc(v_val_1907_);
lean_dec_ref(v_asyncPrefix_x3f_1888_);
v___x_1908_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___redArg___closed__3, &l_Lean_throwAttrNotInAsyncCtx___redArg___closed__3_once, _init_l_Lean_throwAttrNotInAsyncCtx___redArg___closed__3);
v___x_1909_ = l_Lean_MessageData_ofName(v_val_1907_);
v___x_1910_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1910_, 0, v___x_1908_);
lean_ctor_set(v___x_1910_, 1, v___x_1909_);
v___x_1911_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__5, &l_Lean_throwAttrMustBeGlobal___redArg___closed__5_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__5);
v___x_1912_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1912_, 0, v___x_1910_);
lean_ctor_set(v___x_1912_, 1, v___x_1911_);
v___y_1893_ = v___x_1912_;
goto v___jp_1892_;
}
v___jp_1892_:
{
lean_object* v___x_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; uint8_t v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; 
v___x_1894_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1);
v___x_1895_ = l_Lean_MessageData_ofName(v_attrName_1886_);
v___x_1896_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1896_, 0, v___x_1894_);
lean_ctor_set(v___x_1896_, 1, v___x_1895_);
v___x_1897_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__3, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__3_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__3);
v___x_1898_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1898_, 0, v___x_1896_);
lean_ctor_set(v___x_1898_, 1, v___x_1897_);
v___x_1899_ = 0;
v___x_1900_ = l_Lean_MessageData_ofConstName(v_declName_1887_, v___x_1899_);
v___x_1901_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1901_, 0, v___x_1898_);
lean_ctor_set(v___x_1901_, 1, v___x_1900_);
v___x_1902_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___redArg___closed__1, &l_Lean_throwAttrNotInAsyncCtx___redArg___closed__1_once, _init_l_Lean_throwAttrNotInAsyncCtx___redArg___closed__1);
v___x_1903_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1903_, 0, v___x_1901_);
lean_ctor_set(v___x_1903_, 1, v___x_1902_);
v___x_1904_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1904_, 0, v___x_1903_);
lean_ctor_set(v___x_1904_, 1, v___y_1893_);
v___x_1905_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0_spec__0___redArg(v___x_1904_, v___y_1889_, v___y_1890_);
return v___x_1905_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___redArg___boxed(lean_object* v_attrName_1913_, lean_object* v_declName_1914_, lean_object* v_asyncPrefix_x3f_1915_, lean_object* v___y_1916_, lean_object* v___y_1917_, lean_object* v___y_1918_){
_start:
{
lean_object* v_res_1919_; 
v_res_1919_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___redArg(v_attrName_1913_, v_declName_1914_, v_asyncPrefix_x3f_1915_, v___y_1916_, v___y_1917_);
lean_dec(v___y_1917_);
lean_dec_ref(v___y_1916_);
return v_res_1919_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg(lean_object* v_name_1920_, uint8_t v_kind_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_){
_start:
{
lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___y_1931_; 
v___x_1925_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__1, &l_Lean_throwAttrMustBeGlobal___redArg___closed__1_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__1);
v___x_1926_ = l_Lean_MessageData_ofName(v_name_1920_);
v___x_1927_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1927_, 0, v___x_1925_);
lean_ctor_set(v___x_1927_, 1, v___x_1926_);
v___x_1928_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__3, &l_Lean_throwAttrMustBeGlobal___redArg___closed__3_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__3);
v___x_1929_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1929_, 0, v___x_1927_);
lean_ctor_set(v___x_1929_, 1, v___x_1928_);
switch(v_kind_1921_)
{
case 0:
{
lean_object* v___x_1938_; 
v___x_1938_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__0));
v___y_1931_ = v___x_1938_;
goto v___jp_1930_;
}
case 1:
{
lean_object* v___x_1939_; 
v___x_1939_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__1));
v___y_1931_ = v___x_1939_;
goto v___jp_1930_;
}
default: 
{
lean_object* v___x_1940_; 
v___x_1940_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__2));
v___y_1931_ = v___x_1940_;
goto v___jp_1930_;
}
}
v___jp_1930_:
{
lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; 
v___x_1932_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1932_, 0, v___y_1931_);
v___x_1933_ = l_Lean_MessageData_ofFormat(v___x_1932_);
v___x_1934_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1934_, 0, v___x_1929_);
lean_ctor_set(v___x_1934_, 1, v___x_1933_);
v___x_1935_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__5, &l_Lean_throwAttrMustBeGlobal___redArg___closed__5_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__5);
v___x_1936_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1936_, 0, v___x_1934_);
lean_ctor_set(v___x_1936_, 1, v___x_1935_);
v___x_1937_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0_spec__0___redArg(v___x_1936_, v___y_1922_, v___y_1923_);
return v___x_1937_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg___boxed(lean_object* v_name_1941_, lean_object* v_kind_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_){
_start:
{
uint8_t v_kind_boxed_1946_; lean_object* v_res_1947_; 
v_kind_boxed_1946_ = lean_unbox(v_kind_1942_);
v_res_1947_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg(v_name_1941_, v_kind_boxed_1946_, v___y_1943_, v___y_1944_);
lean_dec(v___y_1944_);
lean_dec_ref(v___y_1943_);
return v_res_1947_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__7(lean_object* v_validate_1948_, lean_object* v_a_1949_, lean_object* v_name_1950_, lean_object* v_decl_1951_, lean_object* v_stx_1952_, uint8_t v_kind_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_){
_start:
{
lean_object* v___y_1958_; lean_object* v___y_1959_; lean_object* v___y_1993_; lean_object* v___y_1994_; lean_object* v___y_1995_; lean_object* v___y_2002_; lean_object* v___y_2003_; lean_object* v___x_2008_; 
v___x_2008_ = l_Lean_Attribute_Builtin_ensureNoArgs(v_stx_1952_, v___y_1954_, v___y_1955_);
if (lean_obj_tag(v___x_2008_) == 0)
{
uint8_t v___x_2009_; uint8_t v___x_2010_; 
lean_dec_ref(v___x_2008_);
v___x_2009_ = 0;
v___x_2010_ = l_Lean_instBEqAttributeKind_beq(v_kind_1953_, v___x_2009_);
if (v___x_2010_ == 0)
{
lean_object* v___x_2011_; 
lean_dec(v_decl_1951_);
lean_dec_ref(v_a_1949_);
lean_dec_ref(v_validate_1948_);
v___x_2011_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg(v_name_1950_, v_kind_1953_, v___y_1954_, v___y_1955_);
return v___x_2011_;
}
else
{
v___y_2002_ = v___y_1954_;
v___y_2003_ = v___y_1955_;
goto v___jp_2001_;
}
}
else
{
lean_dec(v_decl_1951_);
lean_dec(v_name_1950_);
lean_dec_ref(v_a_1949_);
lean_dec_ref(v_validate_1948_);
return v___x_2008_;
}
v___jp_1957_:
{
lean_object* v___x_1960_; 
lean_inc(v___y_1959_);
lean_inc_ref(v___y_1958_);
lean_inc(v_decl_1951_);
v___x_1960_ = lean_apply_4(v_validate_1948_, v_decl_1951_, v___y_1958_, v___y_1959_, lean_box(0));
if (lean_obj_tag(v___x_1960_) == 0)
{
lean_object* v___x_1962_; uint8_t v_isShared_1963_; uint8_t v_isSharedCheck_1990_; 
v_isSharedCheck_1990_ = !lean_is_exclusive(v___x_1960_);
if (v_isSharedCheck_1990_ == 0)
{
lean_object* v_unused_1991_; 
v_unused_1991_ = lean_ctor_get(v___x_1960_, 0);
lean_dec(v_unused_1991_);
v___x_1962_ = v___x_1960_;
v_isShared_1963_ = v_isSharedCheck_1990_;
goto v_resetjp_1961_;
}
else
{
lean_dec(v___x_1960_);
v___x_1962_ = lean_box(0);
v_isShared_1963_ = v_isSharedCheck_1990_;
goto v_resetjp_1961_;
}
v_resetjp_1961_:
{
lean_object* v___x_1964_; lean_object* v_toEnvExtension_1965_; lean_object* v_env_1966_; lean_object* v_nextMacroScope_1967_; lean_object* v_ngen_1968_; lean_object* v_auxDeclNGen_1969_; lean_object* v_traceState_1970_; lean_object* v_messages_1971_; lean_object* v_infoState_1972_; lean_object* v_snapshotTasks_1973_; lean_object* v___x_1975_; uint8_t v_isShared_1976_; uint8_t v_isSharedCheck_1988_; 
v___x_1964_ = lean_st_ref_take(v___y_1959_);
v_toEnvExtension_1965_ = lean_ctor_get(v_a_1949_, 0);
v_env_1966_ = lean_ctor_get(v___x_1964_, 0);
v_nextMacroScope_1967_ = lean_ctor_get(v___x_1964_, 1);
v_ngen_1968_ = lean_ctor_get(v___x_1964_, 2);
v_auxDeclNGen_1969_ = lean_ctor_get(v___x_1964_, 3);
v_traceState_1970_ = lean_ctor_get(v___x_1964_, 4);
v_messages_1971_ = lean_ctor_get(v___x_1964_, 6);
v_infoState_1972_ = lean_ctor_get(v___x_1964_, 7);
v_snapshotTasks_1973_ = lean_ctor_get(v___x_1964_, 8);
v_isSharedCheck_1988_ = !lean_is_exclusive(v___x_1964_);
if (v_isSharedCheck_1988_ == 0)
{
lean_object* v_unused_1989_; 
v_unused_1989_ = lean_ctor_get(v___x_1964_, 5);
lean_dec(v_unused_1989_);
v___x_1975_ = v___x_1964_;
v_isShared_1976_ = v_isSharedCheck_1988_;
goto v_resetjp_1974_;
}
else
{
lean_inc(v_snapshotTasks_1973_);
lean_inc(v_infoState_1972_);
lean_inc(v_messages_1971_);
lean_inc(v_traceState_1970_);
lean_inc(v_auxDeclNGen_1969_);
lean_inc(v_ngen_1968_);
lean_inc(v_nextMacroScope_1967_);
lean_inc(v_env_1966_);
lean_dec(v___x_1964_);
v___x_1975_ = lean_box(0);
v_isShared_1976_ = v_isSharedCheck_1988_;
goto v_resetjp_1974_;
}
v_resetjp_1974_:
{
lean_object* v_asyncMode_1977_; lean_object* v___x_1978_; lean_object* v___x_1979_; lean_object* v___x_1981_; 
v_asyncMode_1977_ = lean_ctor_get(v_toEnvExtension_1965_, 2);
lean_inc(v_asyncMode_1977_);
lean_inc(v_decl_1951_);
v___x_1978_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_a_1949_, v_env_1966_, v_decl_1951_, v_asyncMode_1977_, v_decl_1951_);
lean_dec(v_asyncMode_1977_);
v___x_1979_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2);
if (v_isShared_1976_ == 0)
{
lean_ctor_set(v___x_1975_, 5, v___x_1979_);
lean_ctor_set(v___x_1975_, 0, v___x_1978_);
v___x_1981_ = v___x_1975_;
goto v_reusejp_1980_;
}
else
{
lean_object* v_reuseFailAlloc_1987_; 
v_reuseFailAlloc_1987_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1987_, 0, v___x_1978_);
lean_ctor_set(v_reuseFailAlloc_1987_, 1, v_nextMacroScope_1967_);
lean_ctor_set(v_reuseFailAlloc_1987_, 2, v_ngen_1968_);
lean_ctor_set(v_reuseFailAlloc_1987_, 3, v_auxDeclNGen_1969_);
lean_ctor_set(v_reuseFailAlloc_1987_, 4, v_traceState_1970_);
lean_ctor_set(v_reuseFailAlloc_1987_, 5, v___x_1979_);
lean_ctor_set(v_reuseFailAlloc_1987_, 6, v_messages_1971_);
lean_ctor_set(v_reuseFailAlloc_1987_, 7, v_infoState_1972_);
lean_ctor_set(v_reuseFailAlloc_1987_, 8, v_snapshotTasks_1973_);
v___x_1981_ = v_reuseFailAlloc_1987_;
goto v_reusejp_1980_;
}
v_reusejp_1980_:
{
lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1985_; 
v___x_1982_ = lean_st_ref_set(v___y_1959_, v___x_1981_);
v___x_1983_ = lean_box(0);
if (v_isShared_1963_ == 0)
{
lean_ctor_set(v___x_1962_, 0, v___x_1983_);
v___x_1985_ = v___x_1962_;
goto v_reusejp_1984_;
}
else
{
lean_object* v_reuseFailAlloc_1986_; 
v_reuseFailAlloc_1986_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1986_, 0, v___x_1983_);
v___x_1985_ = v_reuseFailAlloc_1986_;
goto v_reusejp_1984_;
}
v_reusejp_1984_:
{
return v___x_1985_;
}
}
}
}
}
else
{
lean_dec(v_decl_1951_);
lean_dec_ref(v_a_1949_);
return v___x_1960_;
}
}
v___jp_1992_:
{
lean_object* v_toEnvExtension_1996_; lean_object* v_asyncMode_1997_; uint8_t v___x_1998_; 
v_toEnvExtension_1996_ = lean_ctor_get(v_a_1949_, 0);
v_asyncMode_1997_ = lean_ctor_get(v_toEnvExtension_1996_, 2);
lean_inc(v_decl_1951_);
lean_inc_ref(v___y_1993_);
v___x_1998_ = l_Lean_EnvExtension_asyncMayModify___redArg(v___y_1993_, v_decl_1951_, v_asyncMode_1997_);
if (v___x_1998_ == 0)
{
lean_object* v___x_1999_; lean_object* v___x_2000_; 
lean_dec_ref(v_a_1949_);
lean_dec_ref(v_validate_1948_);
v___x_1999_ = l_Lean_Environment_asyncPrefix_x3f(v___y_1993_);
v___x_2000_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___redArg(v_name_1950_, v_decl_1951_, v___x_1999_, v___y_1994_, v___y_1995_);
return v___x_2000_;
}
else
{
lean_dec_ref(v___y_1993_);
lean_dec(v_name_1950_);
v___y_1958_ = v___y_1994_;
v___y_1959_ = v___y_1995_;
goto v___jp_1957_;
}
}
v___jp_2001_:
{
lean_object* v___x_2004_; lean_object* v_env_2005_; lean_object* v___x_2006_; 
v___x_2004_ = lean_st_ref_get(v___y_2003_);
v_env_2005_ = lean_ctor_get(v___x_2004_, 0);
lean_inc_ref(v_env_2005_);
lean_dec(v___x_2004_);
v___x_2006_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2005_, v_decl_1951_);
if (lean_obj_tag(v___x_2006_) == 0)
{
v___y_1993_ = v_env_2005_;
v___y_1994_ = v___y_2002_;
v___y_1995_ = v___y_2003_;
goto v___jp_1992_;
}
else
{
lean_object* v___x_2007_; 
lean_dec_ref(v___x_2006_);
lean_dec_ref(v_env_2005_);
lean_dec_ref(v_a_1949_);
lean_dec_ref(v_validate_1948_);
v___x_2007_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg(v_name_1950_, v_decl_1951_, v___y_2002_, v___y_2003_);
return v___x_2007_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__7___boxed(lean_object* v_validate_2012_, lean_object* v_a_2013_, lean_object* v_name_2014_, lean_object* v_decl_2015_, lean_object* v_stx_2016_, lean_object* v_kind_2017_, lean_object* v___y_2018_, lean_object* v___y_2019_, lean_object* v___y_2020_){
_start:
{
uint8_t v_kind_boxed_2021_; lean_object* v_res_2022_; 
v_kind_boxed_2021_ = lean_unbox(v_kind_2017_);
v_res_2022_ = l_Lean_registerTagAttribute___lam__7(v_validate_2012_, v_a_2013_, v_name_2014_, v_decl_2015_, v_stx_2016_, v_kind_boxed_2021_, v___y_2018_, v___y_2019_);
lean_dec(v___y_2019_);
lean_dec_ref(v___y_2018_);
return v_res_2022_;
}
}
static lean_object* _init_l_Lean_registerTagAttribute___closed__5(void){
_start:
{
lean_object* v___x_2028_; lean_object* v___f_2029_; 
v___x_2028_ = l_Lean_NameSet_empty;
v___f_2029_ = lean_alloc_closure((void*)(l_Lean_registerTagAttribute___lam__4___boxed), 4, 1);
lean_closure_set(v___f_2029_, 0, v___x_2028_);
return v___f_2029_;
}
}
static lean_object* _init_l_Lean_registerTagAttribute___closed__6(void){
_start:
{
lean_object* v___x_2030_; lean_object* v___f_2031_; 
v___x_2030_ = l_Lean_NameSet_empty;
v___f_2031_ = lean_alloc_closure((void*)(l_Lean_registerTagAttribute___lam__5___boxed), 2, 1);
lean_closure_set(v___f_2031_, 0, v___x_2030_);
return v___f_2031_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute(lean_object* v_name_2034_, lean_object* v_descr_2035_, lean_object* v_validate_2036_, lean_object* v_ref_2037_, uint8_t v_applicationTime_2038_, lean_object* v_asyncMode_2039_){
_start:
{
lean_object* v___f_2041_; lean_object* v___f_2042_; lean_object* v___f_2043_; lean_object* v___f_2044_; lean_object* v___f_2045_; lean_object* v___f_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; 
v___f_2041_ = ((lean_object*)(l_Lean_registerTagAttribute___closed__0));
v___f_2042_ = ((lean_object*)(l_Lean_registerTagAttribute___closed__2));
v___f_2043_ = ((lean_object*)(l_Lean_registerTagAttribute___closed__3));
v___f_2044_ = ((lean_object*)(l_Lean_registerTagAttribute___closed__4));
v___f_2045_ = lean_obj_once(&l_Lean_registerTagAttribute___closed__5, &l_Lean_registerTagAttribute___closed__5_once, _init_l_Lean_registerTagAttribute___closed__5);
v___f_2046_ = lean_obj_once(&l_Lean_registerTagAttribute___closed__6, &l_Lean_registerTagAttribute___closed__6_once, _init_l_Lean_registerTagAttribute___closed__6);
v___x_2047_ = ((lean_object*)(l_Lean_registerTagAttribute___closed__7));
lean_inc(v_ref_2037_);
v___x_2048_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_2048_, 0, v_ref_2037_);
lean_ctor_set(v___x_2048_, 1, v___f_2046_);
lean_ctor_set(v___x_2048_, 2, v___f_2045_);
lean_ctor_set(v___x_2048_, 3, v___f_2044_);
lean_ctor_set(v___x_2048_, 4, v___f_2043_);
lean_ctor_set(v___x_2048_, 5, v___f_2042_);
lean_ctor_set(v___x_2048_, 6, v_asyncMode_2039_);
lean_ctor_set(v___x_2048_, 7, v___x_2047_);
v___x_2049_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2049_, 0, v___x_2048_);
lean_ctor_set(v___x_2049_, 1, v___f_2041_);
v___x_2050_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_2049_);
if (lean_obj_tag(v___x_2050_) == 0)
{
lean_object* v_a_2051_; lean_object* v___f_2052_; lean_object* v___f_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; 
v_a_2051_ = lean_ctor_get(v___x_2050_, 0);
lean_inc(v_a_2051_);
lean_dec_ref(v___x_2050_);
lean_inc(v_name_2034_);
v___f_2052_ = lean_alloc_closure((void*)(l_Lean_registerTagAttribute___lam__6___boxed), 5, 1);
lean_closure_set(v___f_2052_, 0, v_name_2034_);
lean_inc(v_name_2034_);
lean_inc(v_a_2051_);
v___f_2053_ = lean_alloc_closure((void*)(l_Lean_registerTagAttribute___lam__7___boxed), 9, 3);
lean_closure_set(v___f_2053_, 0, v_validate_2036_);
lean_closure_set(v___f_2053_, 1, v_a_2051_);
lean_closure_set(v___f_2053_, 2, v_name_2034_);
v___x_2054_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2054_, 0, v_ref_2037_);
lean_ctor_set(v___x_2054_, 1, v_name_2034_);
lean_ctor_set(v___x_2054_, 2, v_descr_2035_);
lean_ctor_set_uint8(v___x_2054_, sizeof(void*)*3, v_applicationTime_2038_);
v___x_2055_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2055_, 0, v___x_2054_);
lean_ctor_set(v___x_2055_, 1, v___f_2053_);
lean_ctor_set(v___x_2055_, 2, v___f_2052_);
lean_inc_ref(v___x_2055_);
v___x_2056_ = l_Lean_registerBuiltinAttribute(v___x_2055_);
if (lean_obj_tag(v___x_2056_) == 0)
{
lean_object* v___x_2058_; uint8_t v_isShared_2059_; uint8_t v_isSharedCheck_2064_; 
v_isSharedCheck_2064_ = !lean_is_exclusive(v___x_2056_);
if (v_isSharedCheck_2064_ == 0)
{
lean_object* v_unused_2065_; 
v_unused_2065_ = lean_ctor_get(v___x_2056_, 0);
lean_dec(v_unused_2065_);
v___x_2058_ = v___x_2056_;
v_isShared_2059_ = v_isSharedCheck_2064_;
goto v_resetjp_2057_;
}
else
{
lean_dec(v___x_2056_);
v___x_2058_ = lean_box(0);
v_isShared_2059_ = v_isSharedCheck_2064_;
goto v_resetjp_2057_;
}
v_resetjp_2057_:
{
lean_object* v___x_2060_; lean_object* v___x_2062_; 
v___x_2060_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2060_, 0, v___x_2055_);
lean_ctor_set(v___x_2060_, 1, v_a_2051_);
if (v_isShared_2059_ == 0)
{
lean_ctor_set(v___x_2058_, 0, v___x_2060_);
v___x_2062_ = v___x_2058_;
goto v_reusejp_2061_;
}
else
{
lean_object* v_reuseFailAlloc_2063_; 
v_reuseFailAlloc_2063_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2063_, 0, v___x_2060_);
v___x_2062_ = v_reuseFailAlloc_2063_;
goto v_reusejp_2061_;
}
v_reusejp_2061_:
{
return v___x_2062_;
}
}
}
else
{
lean_object* v_a_2066_; lean_object* v___x_2068_; uint8_t v_isShared_2069_; uint8_t v_isSharedCheck_2073_; 
lean_dec_ref(v___x_2055_);
lean_dec(v_a_2051_);
v_a_2066_ = lean_ctor_get(v___x_2056_, 0);
v_isSharedCheck_2073_ = !lean_is_exclusive(v___x_2056_);
if (v_isSharedCheck_2073_ == 0)
{
v___x_2068_ = v___x_2056_;
v_isShared_2069_ = v_isSharedCheck_2073_;
goto v_resetjp_2067_;
}
else
{
lean_inc(v_a_2066_);
lean_dec(v___x_2056_);
v___x_2068_ = lean_box(0);
v_isShared_2069_ = v_isSharedCheck_2073_;
goto v_resetjp_2067_;
}
v_resetjp_2067_:
{
lean_object* v___x_2071_; 
if (v_isShared_2069_ == 0)
{
v___x_2071_ = v___x_2068_;
goto v_reusejp_2070_;
}
else
{
lean_object* v_reuseFailAlloc_2072_; 
v_reuseFailAlloc_2072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2072_, 0, v_a_2066_);
v___x_2071_ = v_reuseFailAlloc_2072_;
goto v_reusejp_2070_;
}
v_reusejp_2070_:
{
return v___x_2071_;
}
}
}
}
else
{
lean_object* v_a_2074_; lean_object* v___x_2076_; uint8_t v_isShared_2077_; uint8_t v_isSharedCheck_2081_; 
lean_dec(v_ref_2037_);
lean_dec_ref(v_validate_2036_);
lean_dec_ref(v_descr_2035_);
lean_dec(v_name_2034_);
v_a_2074_ = lean_ctor_get(v___x_2050_, 0);
v_isSharedCheck_2081_ = !lean_is_exclusive(v___x_2050_);
if (v_isSharedCheck_2081_ == 0)
{
v___x_2076_ = v___x_2050_;
v_isShared_2077_ = v_isSharedCheck_2081_;
goto v_resetjp_2075_;
}
else
{
lean_inc(v_a_2074_);
lean_dec(v___x_2050_);
v___x_2076_ = lean_box(0);
v_isShared_2077_ = v_isSharedCheck_2081_;
goto v_resetjp_2075_;
}
v_resetjp_2075_:
{
lean_object* v___x_2079_; 
if (v_isShared_2077_ == 0)
{
v___x_2079_ = v___x_2076_;
goto v_reusejp_2078_;
}
else
{
lean_object* v_reuseFailAlloc_2080_; 
v_reuseFailAlloc_2080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2080_, 0, v_a_2074_);
v___x_2079_ = v_reuseFailAlloc_2080_;
goto v_reusejp_2078_;
}
v_reusejp_2078_:
{
return v___x_2079_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___boxed(lean_object* v_name_2082_, lean_object* v_descr_2083_, lean_object* v_validate_2084_, lean_object* v_ref_2085_, lean_object* v_applicationTime_2086_, lean_object* v_asyncMode_2087_, lean_object* v_a_2088_){
_start:
{
uint8_t v_applicationTime_boxed_2089_; lean_object* v_res_2090_; 
v_applicationTime_boxed_2089_ = lean_unbox(v_applicationTime_2086_);
v_res_2090_ = l_Lean_registerTagAttribute(v_name_2082_, v_descr_2083_, v_validate_2084_, v_ref_2085_, v_applicationTime_boxed_2089_, v_asyncMode_2087_);
return v_res_2090_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerTagAttribute_spec__1(lean_object* v_init_2091_, lean_object* v_t_2092_){
_start:
{
lean_object* v___x_2093_; 
v___x_2093_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerTagAttribute_spec__1_spec__1(v_init_2091_, v_t_2092_);
return v___x_2093_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__2(lean_object* v_n_2094_, lean_object* v_as_2095_, lean_object* v_lo_2096_, lean_object* v_hi_2097_, lean_object* v_w_2098_, lean_object* v_hlo_2099_, lean_object* v_hhi_2100_){
_start:
{
lean_object* v___x_2101_; 
v___x_2101_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__2___redArg(v_as_2095_, v_lo_2096_, v_hi_2097_);
return v___x_2101_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__2___boxed(lean_object* v_n_2102_, lean_object* v_as_2103_, lean_object* v_lo_2104_, lean_object* v_hi_2105_, lean_object* v_w_2106_, lean_object* v_hlo_2107_, lean_object* v_hhi_2108_){
_start:
{
lean_object* v_res_2109_; 
v_res_2109_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__2(v_n_2102_, v_as_2103_, v_lo_2104_, v_hi_2105_, v_w_2106_, v_hlo_2107_, v_hhi_2108_);
lean_dec(v_hi_2105_);
lean_dec(v_n_2102_);
return v_res_2109_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4(lean_object* v_00_u03b1_2110_, lean_object* v_attrName_2111_, lean_object* v_declName_2112_, lean_object* v_asyncPrefix_x3f_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_){
_start:
{
lean_object* v___x_2117_; 
v___x_2117_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___redArg(v_attrName_2111_, v_declName_2112_, v_asyncPrefix_x3f_2113_, v___y_2114_, v___y_2115_);
return v___x_2117_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___boxed(lean_object* v_00_u03b1_2118_, lean_object* v_attrName_2119_, lean_object* v_declName_2120_, lean_object* v_asyncPrefix_x3f_2121_, lean_object* v___y_2122_, lean_object* v___y_2123_, lean_object* v___y_2124_){
_start:
{
lean_object* v_res_2125_; 
v_res_2125_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4(v_00_u03b1_2118_, v_attrName_2119_, v_declName_2120_, v_asyncPrefix_x3f_2121_, v___y_2122_, v___y_2123_);
lean_dec(v___y_2123_);
lean_dec_ref(v___y_2122_);
return v_res_2125_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5(lean_object* v_00_u03b1_2126_, lean_object* v_attrName_2127_, lean_object* v_declName_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_){
_start:
{
lean_object* v___x_2132_; 
v___x_2132_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg(v_attrName_2127_, v_declName_2128_, v___y_2129_, v___y_2130_);
return v___x_2132_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___boxed(lean_object* v_00_u03b1_2133_, lean_object* v_attrName_2134_, lean_object* v_declName_2135_, lean_object* v___y_2136_, lean_object* v___y_2137_, lean_object* v___y_2138_){
_start:
{
lean_object* v_res_2139_; 
v_res_2139_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5(v_00_u03b1_2133_, v_attrName_2134_, v_declName_2135_, v___y_2136_, v___y_2137_);
lean_dec(v___y_2137_);
lean_dec_ref(v___y_2136_);
return v_res_2139_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6(lean_object* v_00_u03b1_2140_, lean_object* v_name_2141_, uint8_t v_kind_2142_, lean_object* v___y_2143_, lean_object* v___y_2144_){
_start:
{
lean_object* v___x_2146_; 
v___x_2146_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg(v_name_2141_, v_kind_2142_, v___y_2143_, v___y_2144_);
return v___x_2146_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___boxed(lean_object* v_00_u03b1_2147_, lean_object* v_name_2148_, lean_object* v_kind_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_){
_start:
{
uint8_t v_kind_boxed_2153_; lean_object* v_res_2154_; 
v_kind_boxed_2153_ = lean_unbox(v_kind_2149_);
v_res_2154_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6(v_00_u03b1_2147_, v_name_2148_, v_kind_boxed_2153_, v___y_2150_, v___y_2151_);
lean_dec(v___y_2151_);
lean_dec_ref(v___y_2150_);
return v_res_2154_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg___lam__0(lean_object* v_attr_2155_, lean_object* v_decl_2156_, lean_object* v_env_2157_){
_start:
{
lean_object* v_ext_2158_; lean_object* v_toEnvExtension_2159_; lean_object* v_asyncMode_2160_; lean_object* v___x_2161_; 
v_ext_2158_ = lean_ctor_get(v_attr_2155_, 1);
lean_inc_ref(v_ext_2158_);
lean_dec_ref(v_attr_2155_);
v_toEnvExtension_2159_ = lean_ctor_get(v_ext_2158_, 0);
v_asyncMode_2160_ = lean_ctor_get(v_toEnvExtension_2159_, 2);
lean_inc(v_asyncMode_2160_);
lean_inc(v_decl_2156_);
v___x_2161_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_ext_2158_, v_env_2157_, v_decl_2156_, v_asyncMode_2160_, v_decl_2156_);
lean_dec(v_asyncMode_2160_);
return v___x_2161_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg___lam__1(lean_object* v_modifyEnv_2162_, lean_object* v___f_2163_, lean_object* v_____r_2164_){
_start:
{
lean_object* v___x_2165_; 
v___x_2165_ = lean_apply_1(v_modifyEnv_2162_, v___f_2163_);
return v___x_2165_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg___lam__2(lean_object* v_attr_2166_, lean_object* v_env_2167_, lean_object* v_decl_2168_, lean_object* v_inst_2169_, lean_object* v_inst_2170_, lean_object* v_toBind_2171_, lean_object* v___f_2172_, lean_object* v_modifyEnv_2173_, lean_object* v___f_2174_, lean_object* v_____r_2175_){
_start:
{
lean_object* v_ext_2176_; lean_object* v_toEnvExtension_2177_; lean_object* v_attr_2178_; lean_object* v_asyncMode_2179_; uint8_t v___x_2180_; 
v_ext_2176_ = lean_ctor_get(v_attr_2166_, 1);
v_toEnvExtension_2177_ = lean_ctor_get(v_ext_2176_, 0);
lean_inc_ref(v_toEnvExtension_2177_);
v_attr_2178_ = lean_ctor_get(v_attr_2166_, 0);
lean_inc_ref(v_attr_2178_);
lean_dec_ref(v_attr_2166_);
v_asyncMode_2179_ = lean_ctor_get(v_toEnvExtension_2177_, 2);
lean_inc(v_asyncMode_2179_);
lean_dec_ref(v_toEnvExtension_2177_);
lean_inc(v_decl_2168_);
lean_inc_ref(v_env_2167_);
v___x_2180_ = l_Lean_EnvExtension_asyncMayModify___redArg(v_env_2167_, v_decl_2168_, v_asyncMode_2179_);
lean_dec(v_asyncMode_2179_);
if (v___x_2180_ == 0)
{
lean_object* v_toAttributeImplCore_2181_; lean_object* v_name_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; 
lean_dec_ref(v___f_2174_);
lean_dec(v_modifyEnv_2173_);
v_toAttributeImplCore_2181_ = lean_ctor_get(v_attr_2178_, 0);
lean_inc_ref(v_toAttributeImplCore_2181_);
lean_dec_ref(v_attr_2178_);
v_name_2182_ = lean_ctor_get(v_toAttributeImplCore_2181_, 1);
lean_inc(v_name_2182_);
lean_dec_ref(v_toAttributeImplCore_2181_);
v___x_2183_ = l_Lean_Environment_asyncPrefix_x3f(v_env_2167_);
v___x_2184_ = l_Lean_throwAttrNotInAsyncCtx___redArg(v_inst_2169_, v_inst_2170_, v_name_2182_, v_decl_2168_, v___x_2183_);
v___x_2185_ = lean_apply_4(v_toBind_2171_, lean_box(0), lean_box(0), v___x_2184_, v___f_2172_);
return v___x_2185_;
}
else
{
lean_object* v___x_2186_; 
lean_dec_ref(v_attr_2178_);
lean_dec(v___f_2172_);
lean_dec(v_toBind_2171_);
lean_dec_ref(v_inst_2170_);
lean_dec_ref(v_inst_2169_);
lean_dec(v_decl_2168_);
lean_dec_ref(v_env_2167_);
v___x_2186_ = lean_apply_1(v_modifyEnv_2173_, v___f_2174_);
return v___x_2186_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg___lam__3(lean_object* v___f_2187_, lean_object* v_____r_2188_){
_start:
{
lean_object* v___x_2189_; 
v___x_2189_ = lean_apply_1(v___f_2187_, v_____r_2188_);
return v___x_2189_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg___lam__4(lean_object* v_attr_2190_, lean_object* v_decl_2191_, lean_object* v_inst_2192_, lean_object* v_inst_2193_, lean_object* v_toBind_2194_, lean_object* v___f_2195_, lean_object* v_modifyEnv_2196_, lean_object* v___f_2197_, lean_object* v_env_2198_){
_start:
{
lean_object* v___f_2199_; lean_object* v___x_2200_; 
lean_inc_ref(v___f_2197_);
lean_inc(v_modifyEnv_2196_);
lean_inc(v___f_2195_);
lean_inc(v_toBind_2194_);
lean_inc_ref(v_inst_2193_);
lean_inc_ref(v_inst_2192_);
lean_inc(v_decl_2191_);
lean_inc_ref(v_env_2198_);
lean_inc_ref(v_attr_2190_);
v___f_2199_ = lean_alloc_closure((void*)(l_Lean_TagAttribute_setTag___redArg___lam__2), 10, 9);
lean_closure_set(v___f_2199_, 0, v_attr_2190_);
lean_closure_set(v___f_2199_, 1, v_env_2198_);
lean_closure_set(v___f_2199_, 2, v_decl_2191_);
lean_closure_set(v___f_2199_, 3, v_inst_2192_);
lean_closure_set(v___f_2199_, 4, v_inst_2193_);
lean_closure_set(v___f_2199_, 5, v_toBind_2194_);
lean_closure_set(v___f_2199_, 6, v___f_2195_);
lean_closure_set(v___f_2199_, 7, v_modifyEnv_2196_);
lean_closure_set(v___f_2199_, 8, v___f_2197_);
v___x_2200_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2198_, v_decl_2191_);
if (lean_obj_tag(v___x_2200_) == 0)
{
lean_object* v___x_2201_; lean_object* v___x_2202_; 
lean_dec_ref(v___f_2199_);
v___x_2201_ = lean_box(0);
v___x_2202_ = l_Lean_TagAttribute_setTag___redArg___lam__2(v_attr_2190_, v_env_2198_, v_decl_2191_, v_inst_2192_, v_inst_2193_, v_toBind_2194_, v___f_2195_, v_modifyEnv_2196_, v___f_2197_, v___x_2201_);
return v___x_2202_;
}
else
{
lean_object* v_attr_2203_; lean_object* v_toAttributeImplCore_2204_; lean_object* v_name_2205_; lean_object* v___f_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; 
lean_dec_ref(v___x_2200_);
lean_dec_ref(v_env_2198_);
lean_dec_ref(v___f_2197_);
lean_dec(v_modifyEnv_2196_);
lean_dec(v___f_2195_);
v_attr_2203_ = lean_ctor_get(v_attr_2190_, 0);
lean_inc_ref(v_attr_2203_);
lean_dec_ref(v_attr_2190_);
v_toAttributeImplCore_2204_ = lean_ctor_get(v_attr_2203_, 0);
lean_inc_ref(v_toAttributeImplCore_2204_);
lean_dec_ref(v_attr_2203_);
v_name_2205_ = lean_ctor_get(v_toAttributeImplCore_2204_, 1);
lean_inc(v_name_2205_);
lean_dec_ref(v_toAttributeImplCore_2204_);
v___f_2206_ = lean_alloc_closure((void*)(l_Lean_TagAttribute_setTag___redArg___lam__3), 2, 1);
lean_closure_set(v___f_2206_, 0, v___f_2199_);
v___x_2207_ = l_Lean_throwAttrDeclInImportedModule___redArg(v_inst_2192_, v_inst_2193_, v_name_2205_, v_decl_2191_);
v___x_2208_ = lean_apply_4(v_toBind_2194_, lean_box(0), lean_box(0), v___x_2207_, v___f_2206_);
return v___x_2208_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg(lean_object* v_inst_2209_, lean_object* v_inst_2210_, lean_object* v_inst_2211_, lean_object* v_attr_2212_, lean_object* v_decl_2213_){
_start:
{
lean_object* v_toBind_2214_; lean_object* v_getEnv_2215_; lean_object* v_modifyEnv_2216_; lean_object* v___f_2217_; lean_object* v___f_2218_; lean_object* v___f_2219_; lean_object* v___x_2220_; 
v_toBind_2214_ = lean_ctor_get(v_inst_2209_, 1);
lean_inc(v_toBind_2214_);
v_getEnv_2215_ = lean_ctor_get(v_inst_2211_, 0);
lean_inc(v_getEnv_2215_);
v_modifyEnv_2216_ = lean_ctor_get(v_inst_2211_, 1);
lean_inc(v_modifyEnv_2216_);
lean_dec_ref(v_inst_2211_);
lean_inc(v_decl_2213_);
lean_inc_ref(v_attr_2212_);
v___f_2217_ = lean_alloc_closure((void*)(l_Lean_TagAttribute_setTag___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2217_, 0, v_attr_2212_);
lean_closure_set(v___f_2217_, 1, v_decl_2213_);
lean_inc_ref(v___f_2217_);
lean_inc(v_modifyEnv_2216_);
v___f_2218_ = lean_alloc_closure((void*)(l_Lean_TagAttribute_setTag___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2218_, 0, v_modifyEnv_2216_);
lean_closure_set(v___f_2218_, 1, v___f_2217_);
lean_inc(v_toBind_2214_);
v___f_2219_ = lean_alloc_closure((void*)(l_Lean_TagAttribute_setTag___redArg___lam__4), 9, 8);
lean_closure_set(v___f_2219_, 0, v_attr_2212_);
lean_closure_set(v___f_2219_, 1, v_decl_2213_);
lean_closure_set(v___f_2219_, 2, v_inst_2209_);
lean_closure_set(v___f_2219_, 3, v_inst_2210_);
lean_closure_set(v___f_2219_, 4, v_toBind_2214_);
lean_closure_set(v___f_2219_, 5, v___f_2218_);
lean_closure_set(v___f_2219_, 6, v_modifyEnv_2216_);
lean_closure_set(v___f_2219_, 7, v___f_2217_);
v___x_2220_ = lean_apply_4(v_toBind_2214_, lean_box(0), lean_box(0), v_getEnv_2215_, v___f_2219_);
return v___x_2220_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag(lean_object* v_m_2221_, lean_object* v_inst_2222_, lean_object* v_inst_2223_, lean_object* v_inst_2224_, lean_object* v_attr_2225_, lean_object* v_decl_2226_){
_start:
{
lean_object* v___x_2227_; 
v___x_2227_ = l_Lean_TagAttribute_setTag___redArg(v_inst_2222_, v_inst_2223_, v_inst_2224_, v_attr_2225_, v_decl_2226_);
return v___x_2227_;
}
}
LEAN_EXPORT uint8_t l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___redArg(lean_object* v_as_2228_, lean_object* v_k_2229_, lean_object* v_x_2230_, lean_object* v_x_2231_){
_start:
{
lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v_m_2234_; lean_object* v_a_2235_; uint8_t v___x_2236_; 
v___x_2232_ = lean_nat_add(v_x_2230_, v_x_2231_);
v___x_2233_ = lean_unsigned_to_nat(1u);
v_m_2234_ = lean_nat_shiftr(v___x_2232_, v___x_2233_);
lean_dec(v___x_2232_);
v_a_2235_ = lean_array_fget_borrowed(v_as_2228_, v_m_2234_);
v___x_2236_ = l_Lean_Name_quickLt(v_a_2235_, v_k_2229_);
if (v___x_2236_ == 0)
{
uint8_t v___x_2237_; 
lean_dec(v_x_2231_);
v___x_2237_ = l_Lean_Name_quickLt(v_k_2229_, v_a_2235_);
if (v___x_2237_ == 0)
{
uint8_t v___x_2238_; 
lean_dec(v_m_2234_);
lean_dec(v_x_2230_);
v___x_2238_ = 1;
return v___x_2238_;
}
else
{
lean_object* v___x_2239_; uint8_t v___x_2240_; 
v___x_2239_ = lean_unsigned_to_nat(0u);
v___x_2240_ = lean_nat_dec_eq(v_m_2234_, v___x_2239_);
if (v___x_2240_ == 0)
{
lean_object* v___x_2241_; uint8_t v___x_2242_; 
v___x_2241_ = lean_nat_sub(v_m_2234_, v___x_2233_);
lean_dec(v_m_2234_);
v___x_2242_ = lean_nat_dec_lt(v___x_2241_, v_x_2230_);
if (v___x_2242_ == 0)
{
v_x_2231_ = v___x_2241_;
goto _start;
}
else
{
lean_dec(v___x_2241_);
lean_dec(v_x_2230_);
return v___x_2236_;
}
}
else
{
lean_dec(v_m_2234_);
lean_dec(v_x_2230_);
return v___x_2236_;
}
}
}
else
{
lean_object* v___x_2244_; uint8_t v___x_2245_; 
lean_dec(v_x_2230_);
v___x_2244_ = lean_nat_add(v_m_2234_, v___x_2233_);
lean_dec(v_m_2234_);
v___x_2245_ = lean_nat_dec_le(v___x_2244_, v_x_2231_);
if (v___x_2245_ == 0)
{
lean_dec(v___x_2244_);
lean_dec(v_x_2231_);
return v___x_2245_;
}
else
{
v_x_2230_ = v___x_2244_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___redArg___boxed(lean_object* v_as_2247_, lean_object* v_k_2248_, lean_object* v_x_2249_, lean_object* v_x_2250_){
_start:
{
uint8_t v_res_2251_; lean_object* v_r_2252_; 
v_res_2251_ = l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___redArg(v_as_2247_, v_k_2248_, v_x_2249_, v_x_2250_);
lean_dec(v_k_2248_);
lean_dec_ref(v_as_2247_);
v_r_2252_ = lean_box(v_res_2251_);
return v_r_2252_;
}
}
LEAN_EXPORT uint8_t l_Lean_TagAttribute_hasTag(lean_object* v_attr_2253_, lean_object* v_env_2254_, lean_object* v_decl_2255_){
_start:
{
lean_object* v___x_2256_; lean_object* v___x_2257_; 
v___x_2256_ = lean_box(1);
v___x_2257_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2254_, v_decl_2255_);
if (lean_obj_tag(v___x_2257_) == 0)
{
lean_object* v_ext_2258_; lean_object* v_toEnvExtension_2259_; lean_object* v_asyncMode_2260_; lean_object* v___x_2261_; uint8_t v___x_2262_; 
v_ext_2258_ = lean_ctor_get(v_attr_2253_, 1);
v_toEnvExtension_2259_ = lean_ctor_get(v_ext_2258_, 0);
v_asyncMode_2260_ = lean_ctor_get(v_toEnvExtension_2259_, 2);
lean_inc(v_decl_2255_);
v___x_2261_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2256_, v_ext_2258_, v_env_2254_, v_asyncMode_2260_, v_decl_2255_);
v___x_2262_ = l_Lean_NameSet_contains(v___x_2261_, v_decl_2255_);
lean_dec(v_decl_2255_);
lean_dec(v___x_2261_);
return v___x_2262_;
}
else
{
lean_object* v_val_2263_; lean_object* v_ext_2264_; uint8_t v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; uint8_t v___x_2269_; 
v_val_2263_ = lean_ctor_get(v___x_2257_, 0);
lean_inc(v_val_2263_);
lean_dec_ref(v___x_2257_);
v_ext_2264_ = lean_ctor_get(v_attr_2253_, 1);
v___x_2265_ = 0;
v___x_2266_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_2256_, v_ext_2264_, v_env_2254_, v_val_2263_, v___x_2265_);
lean_dec(v_val_2263_);
lean_dec_ref(v_env_2254_);
v___x_2267_ = lean_unsigned_to_nat(0u);
v___x_2268_ = lean_array_get_size(v___x_2266_);
v___x_2269_ = lean_nat_dec_lt(v___x_2267_, v___x_2268_);
if (v___x_2269_ == 0)
{
lean_dec_ref(v___x_2266_);
lean_dec(v_decl_2255_);
return v___x_2269_;
}
else
{
lean_object* v___x_2270_; lean_object* v___x_2271_; uint8_t v___x_2272_; 
v___x_2270_ = lean_unsigned_to_nat(1u);
v___x_2271_ = lean_nat_sub(v___x_2268_, v___x_2270_);
v___x_2272_ = lean_nat_dec_le(v___x_2267_, v___x_2271_);
if (v___x_2272_ == 0)
{
lean_dec(v___x_2271_);
lean_dec_ref(v___x_2266_);
lean_dec(v_decl_2255_);
return v___x_2272_;
}
else
{
uint8_t v___x_2273_; 
v___x_2273_ = l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___redArg(v___x_2266_, v_decl_2255_, v___x_2267_, v___x_2271_);
lean_dec(v_decl_2255_);
lean_dec_ref(v___x_2266_);
return v___x_2273_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_hasTag___boxed(lean_object* v_attr_2274_, lean_object* v_env_2275_, lean_object* v_decl_2276_){
_start:
{
uint8_t v_res_2277_; lean_object* v_r_2278_; 
v_res_2277_ = l_Lean_TagAttribute_hasTag(v_attr_2274_, v_env_2275_, v_decl_2276_);
lean_dec_ref(v_attr_2274_);
v_r_2278_ = lean_box(v_res_2277_);
return v_r_2278_;
}
}
LEAN_EXPORT uint8_t l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0(lean_object* v_as_2279_, lean_object* v_k_2280_, lean_object* v_x_2281_, lean_object* v_x_2282_, lean_object* v_x_2283_){
_start:
{
uint8_t v___x_2284_; 
v___x_2284_ = l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___redArg(v_as_2279_, v_k_2280_, v_x_2281_, v_x_2282_);
return v___x_2284_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___boxed(lean_object* v_as_2285_, lean_object* v_k_2286_, lean_object* v_x_2287_, lean_object* v_x_2288_, lean_object* v_x_2289_){
_start:
{
uint8_t v_res_2290_; lean_object* v_r_2291_; 
v_res_2290_ = l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0(v_as_2285_, v_k_2286_, v_x_2287_, v_x_2288_, v_x_2289_);
lean_dec(v_k_2286_);
lean_dec_ref(v_as_2285_);
v_r_2291_ = lean_box(v_res_2290_);
return v_r_2291_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__0(lean_object* v_x_2292_, lean_object* v___y_2293_){
_start:
{
lean_object* v___x_2295_; lean_object* v___x_2296_; 
v___x_2295_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___lam__0___closed__1));
v___x_2296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2296_, 0, v___x_2295_);
return v___x_2296_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__0___boxed(lean_object* v_x_2297_, lean_object* v___y_2298_, lean_object* v___y_2299_){
_start:
{
lean_object* v_res_2300_; 
v_res_2300_ = l_Lean_instInhabitedParametricAttribute_default___lam__0(v_x_2297_, v___y_2298_);
lean_dec_ref(v___y_2298_);
lean_dec_ref(v_x_2297_);
return v_res_2300_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__1(lean_object* v_s_2301_, lean_object* v_x_2302_){
_start:
{
lean_inc_ref(v_s_2301_);
return v_s_2301_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__1___boxed(lean_object* v_s_2303_, lean_object* v_x_2304_){
_start:
{
lean_object* v_res_2305_; 
v_res_2305_ = l_Lean_instInhabitedParametricAttribute_default___lam__1(v_s_2303_, v_x_2304_);
lean_dec_ref(v_x_2304_);
lean_dec_ref(v_s_2303_);
return v_res_2305_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__2(lean_object* v_x_2308_, lean_object* v_x_2309_, uint8_t v_x_2310_){
_start:
{
lean_object* v___x_2311_; 
v___x_2311_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___lam__2___closed__0));
return v___x_2311_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__2___boxed(lean_object* v_x_2312_, lean_object* v_x_2313_, lean_object* v_x_2314_){
_start:
{
uint8_t v_x_80__boxed_2315_; lean_object* v_res_2316_; 
v_x_80__boxed_2315_ = lean_unbox(v_x_2314_);
v_res_2316_ = l_Lean_instInhabitedParametricAttribute_default___lam__2(v_x_2312_, v_x_2313_, v_x_80__boxed_2315_);
lean_dec_ref(v_x_2313_);
lean_dec_ref(v_x_2312_);
return v_res_2316_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__3(lean_object* v_x_2317_){
_start:
{
lean_object* v___x_2318_; 
v___x_2318_ = lean_box(0);
return v___x_2318_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__3___boxed(lean_object* v_x_2319_){
_start:
{
lean_object* v_res_2320_; 
v_res_2320_ = l_Lean_instInhabitedParametricAttribute_default___lam__3(v_x_2319_);
lean_dec_ref(v_x_2319_);
return v_res_2320_;
}
}
static lean_object* _init_l_Lean_instInhabitedParametricAttribute_default___closed__4(void){
_start:
{
lean_object* v___x_2325_; 
v___x_2325_ = l_Lean_instInhabitedEnvExtension_default(lean_box(0));
return v___x_2325_;
}
}
static lean_object* _init_l_Lean_instInhabitedParametricAttribute_default___closed__5(void){
_start:
{
lean_object* v___f_2326_; lean_object* v___f_2327_; lean_object* v___f_2328_; lean_object* v___f_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; 
v___f_2326_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___closed__3));
v___f_2327_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___closed__2));
v___f_2328_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___closed__1));
v___f_2329_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___closed__0));
v___x_2330_ = lean_box(0);
v___x_2331_ = lean_obj_once(&l_Lean_instInhabitedParametricAttribute_default___closed__4, &l_Lean_instInhabitedParametricAttribute_default___closed__4_once, _init_l_Lean_instInhabitedParametricAttribute_default___closed__4);
v___x_2332_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2332_, 0, v___x_2331_);
lean_ctor_set(v___x_2332_, 1, v___x_2330_);
lean_ctor_set(v___x_2332_, 2, v___f_2329_);
lean_ctor_set(v___x_2332_, 3, v___f_2328_);
lean_ctor_set(v___x_2332_, 4, v___f_2327_);
lean_ctor_set(v___x_2332_, 5, v___f_2326_);
return v___x_2332_;
}
}
static lean_object* _init_l_Lean_instInhabitedParametricAttribute_default___closed__6(void){
_start:
{
uint8_t v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; 
v___x_2333_ = 0;
v___x_2334_ = lean_obj_once(&l_Lean_instInhabitedParametricAttribute_default___closed__5, &l_Lean_instInhabitedParametricAttribute_default___closed__5_once, _init_l_Lean_instInhabitedParametricAttribute_default___closed__5);
v___x_2335_ = ((lean_object*)(l_Lean_instInhabitedAttributeImpl_default));
v___x_2336_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2336_, 0, v___x_2335_);
lean_ctor_set(v___x_2336_, 1, v___x_2334_);
lean_ctor_set_uint8(v___x_2336_, sizeof(void*)*2, v___x_2333_);
return v___x_2336_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default(lean_object* v_a_2337_){
_start:
{
lean_object* v___x_2338_; 
v___x_2338_ = lean_obj_once(&l_Lean_instInhabitedParametricAttribute_default___closed__6, &l_Lean_instInhabitedParametricAttribute_default___closed__6_once, _init_l_Lean_instInhabitedParametricAttribute_default___closed__6);
return v___x_2338_;
}
}
static lean_object* _init_l_Lean_instInhabitedParametricAttribute___closed__0(void){
_start:
{
lean_object* v___x_2339_; 
v___x_2339_ = l_Lean_instInhabitedParametricAttribute_default(lean_box(0));
return v___x_2339_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute(lean_object* v_a_2340_){
_start:
{
lean_object* v___x_2341_; 
v___x_2341_ = lean_obj_once(&l_Lean_instInhabitedParametricAttribute___closed__0, &l_Lean_instInhabitedParametricAttribute___closed__0_once, _init_l_Lean_instInhabitedParametricAttribute___closed__0);
return v___x_2341_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_registerParametricAttribute_spec__4___redArg(lean_object* v_env_2342_, lean_object* v___y_2343_){
_start:
{
lean_object* v___x_2345_; lean_object* v_nextMacroScope_2346_; lean_object* v_ngen_2347_; lean_object* v_auxDeclNGen_2348_; lean_object* v_traceState_2349_; lean_object* v_messages_2350_; lean_object* v_infoState_2351_; lean_object* v_snapshotTasks_2352_; lean_object* v___x_2354_; uint8_t v_isShared_2355_; uint8_t v_isSharedCheck_2363_; 
v___x_2345_ = lean_st_ref_take(v___y_2343_);
v_nextMacroScope_2346_ = lean_ctor_get(v___x_2345_, 1);
v_ngen_2347_ = lean_ctor_get(v___x_2345_, 2);
v_auxDeclNGen_2348_ = lean_ctor_get(v___x_2345_, 3);
v_traceState_2349_ = lean_ctor_get(v___x_2345_, 4);
v_messages_2350_ = lean_ctor_get(v___x_2345_, 6);
v_infoState_2351_ = lean_ctor_get(v___x_2345_, 7);
v_snapshotTasks_2352_ = lean_ctor_get(v___x_2345_, 8);
v_isSharedCheck_2363_ = !lean_is_exclusive(v___x_2345_);
if (v_isSharedCheck_2363_ == 0)
{
lean_object* v_unused_2364_; lean_object* v_unused_2365_; 
v_unused_2364_ = lean_ctor_get(v___x_2345_, 5);
lean_dec(v_unused_2364_);
v_unused_2365_ = lean_ctor_get(v___x_2345_, 0);
lean_dec(v_unused_2365_);
v___x_2354_ = v___x_2345_;
v_isShared_2355_ = v_isSharedCheck_2363_;
goto v_resetjp_2353_;
}
else
{
lean_inc(v_snapshotTasks_2352_);
lean_inc(v_infoState_2351_);
lean_inc(v_messages_2350_);
lean_inc(v_traceState_2349_);
lean_inc(v_auxDeclNGen_2348_);
lean_inc(v_ngen_2347_);
lean_inc(v_nextMacroScope_2346_);
lean_dec(v___x_2345_);
v___x_2354_ = lean_box(0);
v_isShared_2355_ = v_isSharedCheck_2363_;
goto v_resetjp_2353_;
}
v_resetjp_2353_:
{
lean_object* v___x_2356_; lean_object* v___x_2358_; 
v___x_2356_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2);
if (v_isShared_2355_ == 0)
{
lean_ctor_set(v___x_2354_, 5, v___x_2356_);
lean_ctor_set(v___x_2354_, 0, v_env_2342_);
v___x_2358_ = v___x_2354_;
goto v_reusejp_2357_;
}
else
{
lean_object* v_reuseFailAlloc_2362_; 
v_reuseFailAlloc_2362_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2362_, 0, v_env_2342_);
lean_ctor_set(v_reuseFailAlloc_2362_, 1, v_nextMacroScope_2346_);
lean_ctor_set(v_reuseFailAlloc_2362_, 2, v_ngen_2347_);
lean_ctor_set(v_reuseFailAlloc_2362_, 3, v_auxDeclNGen_2348_);
lean_ctor_set(v_reuseFailAlloc_2362_, 4, v_traceState_2349_);
lean_ctor_set(v_reuseFailAlloc_2362_, 5, v___x_2356_);
lean_ctor_set(v_reuseFailAlloc_2362_, 6, v_messages_2350_);
lean_ctor_set(v_reuseFailAlloc_2362_, 7, v_infoState_2351_);
lean_ctor_set(v_reuseFailAlloc_2362_, 8, v_snapshotTasks_2352_);
v___x_2358_ = v_reuseFailAlloc_2362_;
goto v_reusejp_2357_;
}
v_reusejp_2357_:
{
lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; 
v___x_2359_ = lean_st_ref_set(v___y_2343_, v___x_2358_);
v___x_2360_ = lean_box(0);
v___x_2361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2361_, 0, v___x_2360_);
return v___x_2361_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_registerParametricAttribute_spec__4___redArg___boxed(lean_object* v_env_2366_, lean_object* v___y_2367_, lean_object* v___y_2368_){
_start:
{
lean_object* v_res_2369_; 
v_res_2369_ = l_Lean_setEnv___at___00Lean_registerParametricAttribute_spec__4___redArg(v_env_2366_, v___y_2367_);
lean_dec(v___y_2367_);
return v_res_2369_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_registerParametricAttribute_spec__4(lean_object* v_env_2370_, lean_object* v___y_2371_, lean_object* v___y_2372_){
_start:
{
lean_object* v___x_2374_; 
v___x_2374_ = l_Lean_setEnv___at___00Lean_registerParametricAttribute_spec__4___redArg(v_env_2370_, v___y_2372_);
return v___x_2374_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_registerParametricAttribute_spec__4___boxed(lean_object* v_env_2375_, lean_object* v___y_2376_, lean_object* v___y_2377_, lean_object* v___y_2378_){
_start:
{
lean_object* v_res_2379_; 
v_res_2379_ = l_Lean_setEnv___at___00Lean_registerParametricAttribute_spec__4(v_env_2375_, v___y_2376_, v___y_2377_);
lean_dec(v___y_2377_);
lean_dec_ref(v___y_2376_);
return v_res_2379_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___lam__0(lean_object* v_x_2380_, lean_object* v_p_2381_){
_start:
{
lean_object* v_fst_2382_; lean_object* v_snd_2383_; lean_object* v___x_2385_; uint8_t v_isShared_2386_; uint8_t v_isSharedCheck_2400_; 
v_fst_2382_ = lean_ctor_get(v_x_2380_, 0);
v_snd_2383_ = lean_ctor_get(v_x_2380_, 1);
v_isSharedCheck_2400_ = !lean_is_exclusive(v_x_2380_);
if (v_isSharedCheck_2400_ == 0)
{
v___x_2385_ = v_x_2380_;
v_isShared_2386_ = v_isSharedCheck_2400_;
goto v_resetjp_2384_;
}
else
{
lean_inc(v_snd_2383_);
lean_inc(v_fst_2382_);
lean_dec(v_x_2380_);
v___x_2385_ = lean_box(0);
v_isShared_2386_ = v_isSharedCheck_2400_;
goto v_resetjp_2384_;
}
v_resetjp_2384_:
{
lean_object* v_fst_2387_; lean_object* v_snd_2388_; lean_object* v___x_2390_; uint8_t v_isShared_2391_; uint8_t v_isSharedCheck_2399_; 
v_fst_2387_ = lean_ctor_get(v_p_2381_, 0);
v_snd_2388_ = lean_ctor_get(v_p_2381_, 1);
v_isSharedCheck_2399_ = !lean_is_exclusive(v_p_2381_);
if (v_isSharedCheck_2399_ == 0)
{
v___x_2390_ = v_p_2381_;
v_isShared_2391_ = v_isSharedCheck_2399_;
goto v_resetjp_2389_;
}
else
{
lean_inc(v_snd_2388_);
lean_inc(v_fst_2387_);
lean_dec(v_p_2381_);
v___x_2390_ = lean_box(0);
v_isShared_2391_ = v_isSharedCheck_2399_;
goto v_resetjp_2389_;
}
v_resetjp_2389_:
{
lean_object* v___x_2393_; 
lean_inc(v_fst_2387_);
if (v_isShared_2386_ == 0)
{
lean_ctor_set_tag(v___x_2385_, 1);
lean_ctor_set(v___x_2385_, 1, v_fst_2382_);
lean_ctor_set(v___x_2385_, 0, v_fst_2387_);
v___x_2393_ = v___x_2385_;
goto v_reusejp_2392_;
}
else
{
lean_object* v_reuseFailAlloc_2398_; 
v_reuseFailAlloc_2398_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2398_, 0, v_fst_2387_);
lean_ctor_set(v_reuseFailAlloc_2398_, 1, v_fst_2382_);
v___x_2393_ = v_reuseFailAlloc_2398_;
goto v_reusejp_2392_;
}
v_reusejp_2392_:
{
lean_object* v___x_2394_; lean_object* v___x_2396_; 
v___x_2394_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_2387_, v_snd_2388_, v_snd_2383_);
if (v_isShared_2391_ == 0)
{
lean_ctor_set(v___x_2390_, 1, v___x_2394_);
lean_ctor_set(v___x_2390_, 0, v___x_2393_);
v___x_2396_ = v___x_2390_;
goto v_reusejp_2395_;
}
else
{
lean_object* v_reuseFailAlloc_2397_; 
v_reuseFailAlloc_2397_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2397_, 0, v___x_2393_);
lean_ctor_set(v_reuseFailAlloc_2397_, 1, v___x_2394_);
v___x_2396_ = v_reuseFailAlloc_2397_;
goto v_reusejp_2395_;
}
v_reusejp_2395_:
{
return v___x_2396_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1_spec__1___redArg(lean_object* v_init_2401_, lean_object* v_x_2402_){
_start:
{
if (lean_obj_tag(v_x_2402_) == 0)
{
lean_object* v_k_2403_; lean_object* v_v_2404_; lean_object* v_l_2405_; lean_object* v_r_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; 
v_k_2403_ = lean_ctor_get(v_x_2402_, 1);
v_v_2404_ = lean_ctor_get(v_x_2402_, 2);
v_l_2405_ = lean_ctor_get(v_x_2402_, 3);
v_r_2406_ = lean_ctor_get(v_x_2402_, 4);
v___x_2407_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1_spec__1___redArg(v_init_2401_, v_l_2405_);
lean_inc(v_v_2404_);
lean_inc(v_k_2403_);
v___x_2408_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2408_, 0, v_k_2403_);
lean_ctor_set(v___x_2408_, 1, v_v_2404_);
v___x_2409_ = lean_array_push(v___x_2407_, v___x_2408_);
v_init_2401_ = v___x_2409_;
v_x_2402_ = v_r_2406_;
goto _start;
}
else
{
return v_init_2401_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1_spec__1___redArg___boxed(lean_object* v_init_2411_, lean_object* v_x_2412_){
_start:
{
lean_object* v_res_2413_; 
v_res_2413_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1_spec__1___redArg(v_init_2411_, v_x_2412_);
lean_dec(v_x_2412_);
return v_res_2413_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2___redArg___lam__0(lean_object* v_a_2414_, lean_object* v_b_2415_){
_start:
{
lean_object* v_fst_2416_; lean_object* v_fst_2417_; uint8_t v___x_2418_; 
v_fst_2416_ = lean_ctor_get(v_a_2414_, 0);
v_fst_2417_ = lean_ctor_get(v_b_2415_, 0);
v___x_2418_ = l_Lean_Name_quickLt(v_fst_2416_, v_fst_2417_);
return v___x_2418_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2___redArg___lam__0___boxed(lean_object* v_a_2419_, lean_object* v_b_2420_){
_start:
{
uint8_t v_res_2421_; lean_object* v_r_2422_; 
v_res_2421_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2___redArg___lam__0(v_a_2419_, v_b_2420_);
lean_dec_ref(v_b_2420_);
lean_dec_ref(v_a_2419_);
v_r_2422_ = lean_box(v_res_2421_);
return v_r_2422_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2___redArg(lean_object* v_as_2424_, lean_object* v_lo_2425_, lean_object* v_hi_2426_){
_start:
{
uint8_t v___x_2427_; 
v___x_2427_ = lean_nat_dec_lt(v_lo_2425_, v_hi_2426_);
if (v___x_2427_ == 0)
{
lean_dec(v_lo_2425_);
return v_as_2424_;
}
else
{
lean_object* v___f_2428_; lean_object* v___x_2429_; lean_object* v_fst_2430_; lean_object* v_snd_2431_; uint8_t v___x_2432_; 
v___f_2428_ = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2___redArg___closed__0));
lean_inc(v_lo_2425_);
v___x_2429_ = l_Array_qpartition___redArg(v_as_2424_, v___f_2428_, v_lo_2425_, v_hi_2426_);
v_fst_2430_ = lean_ctor_get(v___x_2429_, 0);
lean_inc(v_fst_2430_);
v_snd_2431_ = lean_ctor_get(v___x_2429_, 1);
lean_inc(v_snd_2431_);
lean_dec_ref(v___x_2429_);
v___x_2432_ = lean_nat_dec_le(v_hi_2426_, v_fst_2430_);
if (v___x_2432_ == 0)
{
lean_object* v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; 
v___x_2433_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2___redArg(v_snd_2431_, v_lo_2425_, v_fst_2430_);
v___x_2434_ = lean_unsigned_to_nat(1u);
v___x_2435_ = lean_nat_add(v_fst_2430_, v___x_2434_);
lean_dec(v_fst_2430_);
v_as_2424_ = v___x_2433_;
v_lo_2425_ = v___x_2435_;
goto _start;
}
else
{
lean_dec(v_fst_2430_);
lean_dec(v_lo_2425_);
return v_snd_2431_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2___redArg___boxed(lean_object* v_as_2437_, lean_object* v_lo_2438_, lean_object* v_hi_2439_){
_start:
{
lean_object* v_res_2440_; 
v_res_2440_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2___redArg(v_as_2437_, v_lo_2438_, v_hi_2439_);
lean_dec(v_hi_2439_);
return v_res_2440_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3_spec__4___redArg(lean_object* v_snd_2441_, lean_object* v_as_2442_, size_t v_i_2443_, size_t v_stop_2444_, lean_object* v_b_2445_){
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
lean_dec_ref(v___x_2453_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3_spec__4___redArg___boxed(lean_object* v_snd_2457_, lean_object* v_as_2458_, lean_object* v_i_2459_, lean_object* v_stop_2460_, lean_object* v_b_2461_){
_start:
{
size_t v_i_boxed_2462_; size_t v_stop_boxed_2463_; lean_object* v_res_2464_; 
v_i_boxed_2462_ = lean_unbox_usize(v_i_2459_);
lean_dec(v_i_2459_);
v_stop_boxed_2463_ = lean_unbox_usize(v_stop_2460_);
lean_dec(v_stop_2460_);
v_res_2464_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3_spec__4___redArg(v_snd_2457_, v_as_2458_, v_i_boxed_2462_, v_stop_boxed_2463_, v_b_2461_);
lean_dec_ref(v_as_2458_);
lean_dec(v_snd_2457_);
return v_res_2464_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3___redArg(lean_object* v_snd_2465_, lean_object* v_as_2466_, lean_object* v_start_2467_, lean_object* v_stop_2468_){
_start:
{
lean_object* v___x_2469_; uint8_t v___x_2470_; 
v___x_2469_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___lam__2___closed__0));
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
v___x_2476_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3_spec__4___redArg(v_snd_2465_, v_as_2466_, v___x_2474_, v___x_2475_, v___x_2469_);
return v___x_2476_;
}
}
else
{
size_t v___x_2477_; size_t v___x_2478_; lean_object* v___x_2479_; 
v___x_2477_ = lean_usize_of_nat(v_start_2467_);
v___x_2478_ = lean_usize_of_nat(v_stop_2468_);
v___x_2479_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3_spec__4___redArg(v_snd_2465_, v_as_2466_, v___x_2477_, v___x_2478_, v___x_2469_);
return v___x_2479_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3___redArg___boxed(lean_object* v_snd_2480_, lean_object* v_as_2481_, lean_object* v_start_2482_, lean_object* v_stop_2483_){
_start:
{
lean_object* v_res_2484_; 
v_res_2484_ = l_Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3___redArg(v_snd_2480_, v_as_2481_, v_start_2482_, v_stop_2483_);
lean_dec(v_stop_2483_);
lean_dec(v_start_2482_);
lean_dec_ref(v_as_2481_);
lean_dec(v_snd_2480_);
return v_res_2484_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttribute_spec__0___redArg(lean_object* v_impl_2485_, lean_object* v_env_2486_, lean_object* v_as_2487_, size_t v_i_2488_, size_t v_stop_2489_, lean_object* v_b_2490_){
_start:
{
lean_object* v___y_2492_; uint8_t v___x_2496_; 
v___x_2496_ = lean_usize_dec_eq(v_i_2488_, v_stop_2489_);
if (v___x_2496_ == 0)
{
lean_object* v___x_2497_; lean_object* v_fst_2498_; lean_object* v_snd_2499_; lean_object* v_filterExport_2500_; lean_object* v___x_2501_; uint8_t v___x_2502_; 
v___x_2497_ = lean_array_uget_borrowed(v_as_2487_, v_i_2488_);
v_fst_2498_ = lean_ctor_get(v___x_2497_, 0);
v_snd_2499_ = lean_ctor_get(v___x_2497_, 1);
v_filterExport_2500_ = lean_ctor_get(v_impl_2485_, 3);
lean_inc_ref(v_filterExport_2500_);
lean_inc(v_snd_2499_);
lean_inc(v_fst_2498_);
lean_inc_ref(v_env_2486_);
v___x_2501_ = lean_apply_3(v_filterExport_2500_, v_env_2486_, v_fst_2498_, v_snd_2499_);
v___x_2502_ = lean_unbox(v___x_2501_);
if (v___x_2502_ == 0)
{
v___y_2492_ = v_b_2490_;
goto v___jp_2491_;
}
else
{
lean_object* v___x_2503_; 
lean_inc(v___x_2497_);
v___x_2503_ = lean_array_push(v_b_2490_, v___x_2497_);
v___y_2492_ = v___x_2503_;
goto v___jp_2491_;
}
}
else
{
lean_dec_ref(v_env_2486_);
lean_dec_ref(v_impl_2485_);
return v_b_2490_;
}
v___jp_2491_:
{
size_t v___x_2493_; size_t v___x_2494_; 
v___x_2493_ = ((size_t)1ULL);
v___x_2494_ = lean_usize_add(v_i_2488_, v___x_2493_);
v_i_2488_ = v___x_2494_;
v_b_2490_ = v___y_2492_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttribute_spec__0___redArg___boxed(lean_object* v_impl_2504_, lean_object* v_env_2505_, lean_object* v_as_2506_, lean_object* v_i_2507_, lean_object* v_stop_2508_, lean_object* v_b_2509_){
_start:
{
size_t v_i_boxed_2510_; size_t v_stop_boxed_2511_; lean_object* v_res_2512_; 
v_i_boxed_2510_ = lean_unbox_usize(v_i_2507_);
lean_dec(v_i_2507_);
v_stop_boxed_2511_ = lean_unbox_usize(v_stop_2508_);
lean_dec(v_stop_2508_);
v_res_2512_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttribute_spec__0___redArg(v_impl_2504_, v_env_2505_, v_as_2506_, v_i_boxed_2510_, v_stop_boxed_2511_, v_b_2509_);
lean_dec_ref(v_as_2506_);
return v_res_2512_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___lam__1(lean_object* v_impl_2513_, uint8_t v_preserveOrder_2514_, lean_object* v_env_2515_, lean_object* v_x_2516_, uint8_t v_lvl_2517_){
_start:
{
lean_object* v___y_2519_; 
if (v_preserveOrder_2514_ == 0)
{
lean_object* v_snd_2533_; lean_object* v___x_2534_; lean_object* v___x_2535_; lean_object* v_r_2536_; lean_object* v___y_2538_; lean_object* v___y_2539_; lean_object* v___x_2541_; uint8_t v___x_2542_; 
v_snd_2533_ = lean_ctor_get(v_x_2516_, 1);
lean_inc(v_snd_2533_);
lean_dec_ref(v_x_2516_);
v___x_2534_ = lean_unsigned_to_nat(0u);
v___x_2535_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___lam__2___closed__0));
v_r_2536_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1_spec__1___redArg(v___x_2535_, v_snd_2533_);
lean_dec(v_snd_2533_);
v___x_2541_ = lean_array_get_size(v_r_2536_);
v___x_2542_ = lean_nat_dec_eq(v___x_2541_, v___x_2534_);
if (v___x_2542_ == 0)
{
lean_object* v___x_2543_; lean_object* v___x_2544_; lean_object* v___y_2546_; uint8_t v___x_2548_; 
v___x_2543_ = lean_unsigned_to_nat(1u);
v___x_2544_ = lean_nat_sub(v___x_2541_, v___x_2543_);
v___x_2548_ = lean_nat_dec_le(v___x_2534_, v___x_2544_);
if (v___x_2548_ == 0)
{
lean_inc(v___x_2544_);
v___y_2546_ = v___x_2544_;
goto v___jp_2545_;
}
else
{
v___y_2546_ = v___x_2534_;
goto v___jp_2545_;
}
v___jp_2545_:
{
uint8_t v___x_2547_; 
v___x_2547_ = lean_nat_dec_le(v___y_2546_, v___x_2544_);
if (v___x_2547_ == 0)
{
lean_dec(v___x_2544_);
lean_inc(v___y_2546_);
v___y_2538_ = v___y_2546_;
v___y_2539_ = v___y_2546_;
goto v___jp_2537_;
}
else
{
v___y_2538_ = v___y_2546_;
v___y_2539_ = v___x_2544_;
goto v___jp_2537_;
}
}
}
else
{
v___y_2519_ = v_r_2536_;
goto v___jp_2518_;
}
v___jp_2537_:
{
lean_object* v___x_2540_; 
v___x_2540_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2___redArg(v_r_2536_, v___y_2538_, v___y_2539_);
lean_dec(v___y_2539_);
v___y_2519_ = v___x_2540_;
goto v___jp_2518_;
}
}
else
{
lean_object* v_fst_2549_; lean_object* v_snd_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; 
v_fst_2549_ = lean_ctor_get(v_x_2516_, 0);
lean_inc(v_fst_2549_);
v_snd_2550_ = lean_ctor_get(v_x_2516_, 1);
lean_inc(v_snd_2550_);
lean_dec_ref(v_x_2516_);
v___x_2551_ = lean_array_mk(v_fst_2549_);
v___x_2552_ = l_Array_reverse___redArg(v___x_2551_);
v___x_2553_ = lean_unsigned_to_nat(0u);
v___x_2554_ = lean_array_get_size(v___x_2552_);
v___x_2555_ = l_Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3___redArg(v_snd_2550_, v___x_2552_, v___x_2553_, v___x_2554_);
lean_dec_ref(v___x_2552_);
lean_dec(v_snd_2550_);
v___y_2519_ = v___x_2555_;
goto v___jp_2518_;
}
v___jp_2518_:
{
uint8_t v___x_2520_; uint8_t v___x_2521_; 
v___x_2520_ = 2;
v___x_2521_ = l_Lean_instDecidableEqOLeanLevel(v_lvl_2517_, v___x_2520_);
if (v___x_2521_ == 0)
{
lean_object* v___x_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; uint8_t v___x_2525_; 
v___x_2522_ = lean_unsigned_to_nat(0u);
v___x_2523_ = lean_array_get_size(v___y_2519_);
v___x_2524_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___lam__2___closed__0));
v___x_2525_ = lean_nat_dec_lt(v___x_2522_, v___x_2523_);
if (v___x_2525_ == 0)
{
lean_dec_ref(v___y_2519_);
lean_dec_ref(v_env_2515_);
lean_dec_ref(v_impl_2513_);
return v___x_2524_;
}
else
{
uint8_t v___x_2526_; 
v___x_2526_ = lean_nat_dec_le(v___x_2523_, v___x_2523_);
if (v___x_2526_ == 0)
{
if (v___x_2525_ == 0)
{
lean_dec_ref(v___y_2519_);
lean_dec_ref(v_env_2515_);
lean_dec_ref(v_impl_2513_);
return v___x_2524_;
}
else
{
size_t v___x_2527_; size_t v___x_2528_; lean_object* v___x_2529_; 
v___x_2527_ = ((size_t)0ULL);
v___x_2528_ = lean_usize_of_nat(v___x_2523_);
v___x_2529_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttribute_spec__0___redArg(v_impl_2513_, v_env_2515_, v___y_2519_, v___x_2527_, v___x_2528_, v___x_2524_);
lean_dec_ref(v___y_2519_);
return v___x_2529_;
}
}
else
{
size_t v___x_2530_; size_t v___x_2531_; lean_object* v___x_2532_; 
v___x_2530_ = ((size_t)0ULL);
v___x_2531_ = lean_usize_of_nat(v___x_2523_);
v___x_2532_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttribute_spec__0___redArg(v_impl_2513_, v_env_2515_, v___y_2519_, v___x_2530_, v___x_2531_, v___x_2524_);
lean_dec_ref(v___y_2519_);
return v___x_2532_;
}
}
}
else
{
lean_dec_ref(v_env_2515_);
lean_dec_ref(v_impl_2513_);
return v___y_2519_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___lam__1___boxed(lean_object* v_impl_2556_, lean_object* v_preserveOrder_2557_, lean_object* v_env_2558_, lean_object* v_x_2559_, lean_object* v_lvl_2560_){
_start:
{
uint8_t v_preserveOrder_boxed_2561_; uint8_t v_lvl_boxed_2562_; lean_object* v_res_2563_; 
v_preserveOrder_boxed_2561_ = lean_unbox(v_preserveOrder_2557_);
v_lvl_boxed_2562_ = lean_unbox(v_lvl_2560_);
v_res_2563_ = l_Lean_registerParametricAttribute___redArg___lam__1(v_impl_2556_, v_preserveOrder_boxed_2561_, v_env_2558_, v_x_2559_, v_lvl_boxed_2562_);
return v_res_2563_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___lam__2(lean_object* v_x_2573_){
_start:
{
lean_object* v_snd_2574_; lean_object* v___x_2576_; uint8_t v_isShared_2577_; uint8_t v_isSharedCheck_2588_; 
v_snd_2574_ = lean_ctor_get(v_x_2573_, 1);
v_isSharedCheck_2588_ = !lean_is_exclusive(v_x_2573_);
if (v_isSharedCheck_2588_ == 0)
{
lean_object* v_unused_2589_; 
v_unused_2589_ = lean_ctor_get(v_x_2573_, 0);
lean_dec(v_unused_2589_);
v___x_2576_ = v_x_2573_;
v_isShared_2577_ = v_isSharedCheck_2588_;
goto v_resetjp_2575_;
}
else
{
lean_inc(v_snd_2574_);
lean_dec(v_x_2573_);
v___x_2576_ = lean_box(0);
v_isShared_2577_ = v_isSharedCheck_2588_;
goto v_resetjp_2575_;
}
v_resetjp_2575_:
{
lean_object* v___x_2578_; lean_object* v___y_2580_; 
v___x_2578_ = ((lean_object*)(l_Lean_registerParametricAttribute___redArg___lam__2___closed__3));
if (lean_obj_tag(v_snd_2574_) == 0)
{
lean_object* v_size_2586_; 
v_size_2586_ = lean_ctor_get(v_snd_2574_, 0);
lean_inc(v_size_2586_);
lean_dec_ref(v_snd_2574_);
v___y_2580_ = v_size_2586_;
goto v___jp_2579_;
}
else
{
lean_object* v___x_2587_; 
v___x_2587_ = lean_unsigned_to_nat(0u);
v___y_2580_ = v___x_2587_;
goto v___jp_2579_;
}
v___jp_2579_:
{
lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2584_; 
v___x_2581_ = l_Nat_reprFast(v___y_2580_);
v___x_2582_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2582_, 0, v___x_2581_);
if (v_isShared_2577_ == 0)
{
lean_ctor_set_tag(v___x_2576_, 5);
lean_ctor_set(v___x_2576_, 1, v___x_2582_);
lean_ctor_set(v___x_2576_, 0, v___x_2578_);
v___x_2584_ = v___x_2576_;
goto v_reusejp_2583_;
}
else
{
lean_object* v_reuseFailAlloc_2585_; 
v_reuseFailAlloc_2585_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2585_, 0, v___x_2578_);
lean_ctor_set(v_reuseFailAlloc_2585_, 1, v___x_2582_);
v___x_2584_ = v_reuseFailAlloc_2585_;
goto v_reusejp_2583_;
}
v_reusejp_2583_:
{
return v___x_2584_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___lam__3(lean_object* v_x_2590_){
_start:
{
lean_object* v___x_2591_; 
v___x_2591_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___lam__2___closed__0));
return v___x_2591_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___lam__3___boxed(lean_object* v_x_2592_){
_start:
{
lean_object* v_res_2593_; 
v_res_2593_ = l_Lean_registerParametricAttribute___redArg___lam__3(v_x_2592_);
lean_dec_ref(v_x_2592_);
return v_res_2593_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___lam__4(lean_object* v___x_2594_, lean_object* v_x_2595_, lean_object* v___y_2596_){
_start:
{
lean_object* v___x_2598_; 
v___x_2598_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2598_, 0, v___x_2594_);
return v___x_2598_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___lam__4___boxed(lean_object* v___x_2599_, lean_object* v_x_2600_, lean_object* v___y_2601_, lean_object* v___y_2602_){
_start:
{
lean_object* v_res_2603_; 
v_res_2603_ = l_Lean_registerParametricAttribute___redArg___lam__4(v___x_2599_, v_x_2600_, v___y_2601_);
lean_dec_ref(v___y_2601_);
lean_dec_ref(v_x_2600_);
return v_res_2603_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___lam__5(lean_object* v___x_2604_){
_start:
{
lean_object* v___x_2606_; 
v___x_2606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2606_, 0, v___x_2604_);
return v___x_2606_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___lam__5___boxed(lean_object* v___x_2607_, lean_object* v___y_2608_){
_start:
{
lean_object* v_res_2609_; 
v_res_2609_ = l_Lean_registerParametricAttribute___redArg___lam__5(v___x_2607_);
return v_res_2609_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___lam__7(lean_object* v_getParam_2610_, lean_object* v_a_2611_, lean_object* v_afterSet_2612_, lean_object* v_name_2613_, lean_object* v_decl_2614_, lean_object* v_stx_2615_, uint8_t v_kind_2616_, lean_object* v___y_2617_, lean_object* v___y_2618_){
_start:
{
lean_object* v___y_2621_; lean_object* v___y_2622_; lean_object* v___y_2623_; lean_object* v___y_2624_; uint8_t v___y_2625_; lean_object* v___y_2628_; lean_object* v___y_2629_; lean_object* v___y_2630_; uint8_t v___x_2673_; uint8_t v___x_2674_; 
v___x_2673_ = 0;
v___x_2674_ = l_Lean_instBEqAttributeKind_beq(v_kind_2616_, v___x_2673_);
if (v___x_2674_ == 0)
{
lean_object* v___x_2675_; 
lean_dec(v_stx_2615_);
lean_dec(v_decl_2614_);
lean_dec_ref(v_afterSet_2612_);
lean_dec_ref(v_a_2611_);
lean_dec_ref(v_getParam_2610_);
v___x_2675_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg(v_name_2613_, v_kind_2616_, v___y_2617_, v___y_2618_);
return v___x_2675_;
}
else
{
goto v___jp_2668_;
}
v___jp_2620_:
{
if (v___y_2625_ == 0)
{
lean_object* v___x_2626_; 
lean_dec_ref(v___y_2622_);
v___x_2626_ = l_Lean_setEnv___at___00Lean_registerParametricAttribute_spec__4___redArg(v___y_2623_, v___y_2621_);
return v___x_2626_;
}
else
{
lean_dec_ref(v___y_2623_);
return v___y_2622_;
}
}
v___jp_2627_:
{
lean_object* v___x_2631_; 
lean_inc(v___y_2630_);
lean_inc_ref(v___y_2629_);
lean_inc(v_decl_2614_);
v___x_2631_ = lean_apply_5(v_getParam_2610_, v_decl_2614_, v_stx_2615_, v___y_2629_, v___y_2630_, lean_box(0));
if (lean_obj_tag(v___x_2631_) == 0)
{
lean_object* v_a_2632_; lean_object* v___x_2633_; lean_object* v_toEnvExtension_2634_; lean_object* v_env_2635_; lean_object* v_nextMacroScope_2636_; lean_object* v_ngen_2637_; lean_object* v_auxDeclNGen_2638_; lean_object* v_traceState_2639_; lean_object* v_messages_2640_; lean_object* v_infoState_2641_; lean_object* v_snapshotTasks_2642_; lean_object* v___x_2644_; uint8_t v_isShared_2645_; uint8_t v_isSharedCheck_2658_; 
v_a_2632_ = lean_ctor_get(v___x_2631_, 0);
lean_inc(v_a_2632_);
lean_dec_ref(v___x_2631_);
v___x_2633_ = lean_st_ref_take(v___y_2630_);
v_toEnvExtension_2634_ = lean_ctor_get(v_a_2611_, 0);
v_env_2635_ = lean_ctor_get(v___x_2633_, 0);
v_nextMacroScope_2636_ = lean_ctor_get(v___x_2633_, 1);
v_ngen_2637_ = lean_ctor_get(v___x_2633_, 2);
v_auxDeclNGen_2638_ = lean_ctor_get(v___x_2633_, 3);
v_traceState_2639_ = lean_ctor_get(v___x_2633_, 4);
v_messages_2640_ = lean_ctor_get(v___x_2633_, 6);
v_infoState_2641_ = lean_ctor_get(v___x_2633_, 7);
v_snapshotTasks_2642_ = lean_ctor_get(v___x_2633_, 8);
v_isSharedCheck_2658_ = !lean_is_exclusive(v___x_2633_);
if (v_isSharedCheck_2658_ == 0)
{
lean_object* v_unused_2659_; 
v_unused_2659_ = lean_ctor_get(v___x_2633_, 5);
lean_dec(v_unused_2659_);
v___x_2644_ = v___x_2633_;
v_isShared_2645_ = v_isSharedCheck_2658_;
goto v_resetjp_2643_;
}
else
{
lean_inc(v_snapshotTasks_2642_);
lean_inc(v_infoState_2641_);
lean_inc(v_messages_2640_);
lean_inc(v_traceState_2639_);
lean_inc(v_auxDeclNGen_2638_);
lean_inc(v_ngen_2637_);
lean_inc(v_nextMacroScope_2636_);
lean_inc(v_env_2635_);
lean_dec(v___x_2633_);
v___x_2644_ = lean_box(0);
v_isShared_2645_ = v_isSharedCheck_2658_;
goto v_resetjp_2643_;
}
v_resetjp_2643_:
{
lean_object* v_asyncMode_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; lean_object* v___x_2651_; 
v_asyncMode_2646_ = lean_ctor_get(v_toEnvExtension_2634_, 2);
lean_inc(v_asyncMode_2646_);
lean_inc(v_a_2632_);
lean_inc(v_decl_2614_);
v___x_2647_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2647_, 0, v_decl_2614_);
lean_ctor_set(v___x_2647_, 1, v_a_2632_);
lean_inc(v_decl_2614_);
v___x_2648_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_a_2611_, v_env_2635_, v___x_2647_, v_asyncMode_2646_, v_decl_2614_);
lean_dec(v_asyncMode_2646_);
v___x_2649_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2);
if (v_isShared_2645_ == 0)
{
lean_ctor_set(v___x_2644_, 5, v___x_2649_);
lean_ctor_set(v___x_2644_, 0, v___x_2648_);
v___x_2651_ = v___x_2644_;
goto v_reusejp_2650_;
}
else
{
lean_object* v_reuseFailAlloc_2657_; 
v_reuseFailAlloc_2657_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2657_, 0, v___x_2648_);
lean_ctor_set(v_reuseFailAlloc_2657_, 1, v_nextMacroScope_2636_);
lean_ctor_set(v_reuseFailAlloc_2657_, 2, v_ngen_2637_);
lean_ctor_set(v_reuseFailAlloc_2657_, 3, v_auxDeclNGen_2638_);
lean_ctor_set(v_reuseFailAlloc_2657_, 4, v_traceState_2639_);
lean_ctor_set(v_reuseFailAlloc_2657_, 5, v___x_2649_);
lean_ctor_set(v_reuseFailAlloc_2657_, 6, v_messages_2640_);
lean_ctor_set(v_reuseFailAlloc_2657_, 7, v_infoState_2641_);
lean_ctor_set(v_reuseFailAlloc_2657_, 8, v_snapshotTasks_2642_);
v___x_2651_ = v_reuseFailAlloc_2657_;
goto v_reusejp_2650_;
}
v_reusejp_2650_:
{
lean_object* v___x_2652_; lean_object* v___x_2653_; 
v___x_2652_ = lean_st_ref_set(v___y_2630_, v___x_2651_);
lean_inc(v___y_2630_);
lean_inc_ref(v___y_2629_);
v___x_2653_ = lean_apply_5(v_afterSet_2612_, v_decl_2614_, v_a_2632_, v___y_2629_, v___y_2630_, lean_box(0));
if (lean_obj_tag(v___x_2653_) == 0)
{
lean_dec_ref(v___y_2628_);
return v___x_2653_;
}
else
{
lean_object* v_a_2654_; uint8_t v___x_2655_; 
v_a_2654_ = lean_ctor_get(v___x_2653_, 0);
lean_inc(v_a_2654_);
v___x_2655_ = l_Lean_Exception_isInterrupt(v_a_2654_);
if (v___x_2655_ == 0)
{
uint8_t v___x_2656_; 
v___x_2656_ = l_Lean_Exception_isRuntime(v_a_2654_);
v___y_2621_ = v___y_2630_;
v___y_2622_ = v___x_2653_;
v___y_2623_ = v___y_2628_;
v___y_2624_ = v___y_2629_;
v___y_2625_ = v___x_2656_;
goto v___jp_2620_;
}
else
{
lean_dec(v_a_2654_);
v___y_2621_ = v___y_2630_;
v___y_2622_ = v___x_2653_;
v___y_2623_ = v___y_2628_;
v___y_2624_ = v___y_2629_;
v___y_2625_ = v___x_2655_;
goto v___jp_2620_;
}
}
}
}
}
else
{
lean_object* v_a_2660_; lean_object* v___x_2662_; uint8_t v_isShared_2663_; uint8_t v_isSharedCheck_2667_; 
lean_dec_ref(v___y_2628_);
lean_dec(v_decl_2614_);
lean_dec_ref(v_afterSet_2612_);
lean_dec_ref(v_a_2611_);
v_a_2660_ = lean_ctor_get(v___x_2631_, 0);
v_isSharedCheck_2667_ = !lean_is_exclusive(v___x_2631_);
if (v_isSharedCheck_2667_ == 0)
{
v___x_2662_ = v___x_2631_;
v_isShared_2663_ = v_isSharedCheck_2667_;
goto v_resetjp_2661_;
}
else
{
lean_inc(v_a_2660_);
lean_dec(v___x_2631_);
v___x_2662_ = lean_box(0);
v_isShared_2663_ = v_isSharedCheck_2667_;
goto v_resetjp_2661_;
}
v_resetjp_2661_:
{
lean_object* v___x_2665_; 
if (v_isShared_2663_ == 0)
{
v___x_2665_ = v___x_2662_;
goto v_reusejp_2664_;
}
else
{
lean_object* v_reuseFailAlloc_2666_; 
v_reuseFailAlloc_2666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2666_, 0, v_a_2660_);
v___x_2665_ = v_reuseFailAlloc_2666_;
goto v_reusejp_2664_;
}
v_reusejp_2664_:
{
return v___x_2665_;
}
}
}
}
v___jp_2668_:
{
lean_object* v___x_2669_; lean_object* v_env_2670_; lean_object* v___x_2671_; 
v___x_2669_ = lean_st_ref_get(v___y_2618_);
v_env_2670_ = lean_ctor_get(v___x_2669_, 0);
lean_inc_ref(v_env_2670_);
lean_dec(v___x_2669_);
v___x_2671_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2670_, v_decl_2614_);
if (lean_obj_tag(v___x_2671_) == 0)
{
lean_dec(v_name_2613_);
v___y_2628_ = v_env_2670_;
v___y_2629_ = v___y_2617_;
v___y_2630_ = v___y_2618_;
goto v___jp_2627_;
}
else
{
lean_object* v___x_2672_; 
lean_dec_ref(v___x_2671_);
lean_dec_ref(v_env_2670_);
lean_dec(v_stx_2615_);
lean_dec_ref(v_afterSet_2612_);
lean_dec_ref(v_a_2611_);
lean_dec_ref(v_getParam_2610_);
v___x_2672_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg(v_name_2613_, v_decl_2614_, v___y_2617_, v___y_2618_);
return v___x_2672_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___lam__7___boxed(lean_object* v_getParam_2676_, lean_object* v_a_2677_, lean_object* v_afterSet_2678_, lean_object* v_name_2679_, lean_object* v_decl_2680_, lean_object* v_stx_2681_, lean_object* v_kind_2682_, lean_object* v___y_2683_, lean_object* v___y_2684_, lean_object* v___y_2685_){
_start:
{
uint8_t v_kind_boxed_2686_; lean_object* v_res_2687_; 
v_kind_boxed_2686_ = lean_unbox(v_kind_2682_);
v_res_2687_ = l_Lean_registerParametricAttribute___redArg___lam__7(v_getParam_2676_, v_a_2677_, v_afterSet_2678_, v_name_2679_, v_decl_2680_, v_stx_2681_, v_kind_boxed_2686_, v___y_2683_, v___y_2684_);
lean_dec(v___y_2684_);
lean_dec_ref(v___y_2683_);
return v_res_2687_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg(lean_object* v_impl_2698_){
_start:
{
lean_object* v_toAttributeImplCore_2700_; lean_object* v_getParam_2701_; lean_object* v_afterSet_2702_; uint8_t v_preserveOrder_2703_; lean_object* v_ref_2704_; lean_object* v_name_2705_; lean_object* v___f_2706_; lean_object* v___x_2707_; lean_object* v___f_2708_; lean_object* v___f_2709_; lean_object* v___f_2710_; lean_object* v___f_2711_; lean_object* v___f_2712_; lean_object* v___x_2713_; lean_object* v___x_2714_; lean_object* v___x_2715_; lean_object* v___x_2716_; lean_object* v___x_2717_; 
v_toAttributeImplCore_2700_ = lean_ctor_get(v_impl_2698_, 0);
lean_inc_ref(v_toAttributeImplCore_2700_);
v_getParam_2701_ = lean_ctor_get(v_impl_2698_, 1);
lean_inc_ref(v_getParam_2701_);
v_afterSet_2702_ = lean_ctor_get(v_impl_2698_, 2);
lean_inc_ref(v_afterSet_2702_);
v_preserveOrder_2703_ = lean_ctor_get_uint8(v_impl_2698_, sizeof(void*)*4);
v_ref_2704_ = lean_ctor_get(v_toAttributeImplCore_2700_, 0);
v_name_2705_ = lean_ctor_get(v_toAttributeImplCore_2700_, 1);
v___f_2706_ = ((lean_object*)(l_Lean_registerParametricAttribute___redArg___closed__0));
v___x_2707_ = lean_box(v_preserveOrder_2703_);
v___f_2708_ = lean_alloc_closure((void*)(l_Lean_registerParametricAttribute___redArg___lam__1___boxed), 5, 2);
lean_closure_set(v___f_2708_, 0, v_impl_2698_);
lean_closure_set(v___f_2708_, 1, v___x_2707_);
v___f_2709_ = ((lean_object*)(l_Lean_registerParametricAttribute___redArg___closed__1));
v___f_2710_ = ((lean_object*)(l_Lean_registerParametricAttribute___redArg___closed__2));
v___f_2711_ = ((lean_object*)(l_Lean_registerParametricAttribute___redArg___closed__4));
v___f_2712_ = ((lean_object*)(l_Lean_registerParametricAttribute___redArg___closed__5));
v___x_2713_ = lean_box(2);
v___x_2714_ = lean_box(0);
lean_inc(v_ref_2704_);
v___x_2715_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_2715_, 0, v_ref_2704_);
lean_ctor_set(v___x_2715_, 1, v___f_2712_);
lean_ctor_set(v___x_2715_, 2, v___f_2711_);
lean_ctor_set(v___x_2715_, 3, v___f_2706_);
lean_ctor_set(v___x_2715_, 4, v___f_2708_);
lean_ctor_set(v___x_2715_, 5, v___f_2709_);
lean_ctor_set(v___x_2715_, 6, v___x_2713_);
lean_ctor_set(v___x_2715_, 7, v___x_2714_);
v___x_2716_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2716_, 0, v___x_2715_);
lean_ctor_set(v___x_2716_, 1, v___f_2710_);
v___x_2717_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_2716_);
if (lean_obj_tag(v___x_2717_) == 0)
{
lean_object* v_a_2718_; lean_object* v___f_2719_; lean_object* v___f_2720_; lean_object* v___x_2721_; lean_object* v___x_2722_; 
v_a_2718_ = lean_ctor_get(v___x_2717_, 0);
lean_inc(v_a_2718_);
lean_dec_ref(v___x_2717_);
lean_inc(v_name_2705_);
v___f_2719_ = lean_alloc_closure((void*)(l_Lean_registerTagAttribute___lam__6___boxed), 5, 1);
lean_closure_set(v___f_2719_, 0, v_name_2705_);
lean_inc(v_name_2705_);
lean_inc(v_a_2718_);
v___f_2720_ = lean_alloc_closure((void*)(l_Lean_registerParametricAttribute___redArg___lam__7___boxed), 10, 4);
lean_closure_set(v___f_2720_, 0, v_getParam_2701_);
lean_closure_set(v___f_2720_, 1, v_a_2718_);
lean_closure_set(v___f_2720_, 2, v_afterSet_2702_);
lean_closure_set(v___f_2720_, 3, v_name_2705_);
v___x_2721_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2721_, 0, v_toAttributeImplCore_2700_);
lean_ctor_set(v___x_2721_, 1, v___f_2720_);
lean_ctor_set(v___x_2721_, 2, v___f_2719_);
lean_inc_ref(v___x_2721_);
v___x_2722_ = l_Lean_registerBuiltinAttribute(v___x_2721_);
if (lean_obj_tag(v___x_2722_) == 0)
{
lean_object* v___x_2724_; uint8_t v_isShared_2725_; uint8_t v_isSharedCheck_2730_; 
v_isSharedCheck_2730_ = !lean_is_exclusive(v___x_2722_);
if (v_isSharedCheck_2730_ == 0)
{
lean_object* v_unused_2731_; 
v_unused_2731_ = lean_ctor_get(v___x_2722_, 0);
lean_dec(v_unused_2731_);
v___x_2724_ = v___x_2722_;
v_isShared_2725_ = v_isSharedCheck_2730_;
goto v_resetjp_2723_;
}
else
{
lean_dec(v___x_2722_);
v___x_2724_ = lean_box(0);
v_isShared_2725_ = v_isSharedCheck_2730_;
goto v_resetjp_2723_;
}
v_resetjp_2723_:
{
lean_object* v___x_2726_; lean_object* v___x_2728_; 
v___x_2726_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2726_, 0, v___x_2721_);
lean_ctor_set(v___x_2726_, 1, v_a_2718_);
lean_ctor_set_uint8(v___x_2726_, sizeof(void*)*2, v_preserveOrder_2703_);
if (v_isShared_2725_ == 0)
{
lean_ctor_set(v___x_2724_, 0, v___x_2726_);
v___x_2728_ = v___x_2724_;
goto v_reusejp_2727_;
}
else
{
lean_object* v_reuseFailAlloc_2729_; 
v_reuseFailAlloc_2729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2729_, 0, v___x_2726_);
v___x_2728_ = v_reuseFailAlloc_2729_;
goto v_reusejp_2727_;
}
v_reusejp_2727_:
{
return v___x_2728_;
}
}
}
else
{
lean_object* v_a_2732_; lean_object* v___x_2734_; uint8_t v_isShared_2735_; uint8_t v_isSharedCheck_2739_; 
lean_dec_ref(v___x_2721_);
lean_dec(v_a_2718_);
v_a_2732_ = lean_ctor_get(v___x_2722_, 0);
v_isSharedCheck_2739_ = !lean_is_exclusive(v___x_2722_);
if (v_isSharedCheck_2739_ == 0)
{
v___x_2734_ = v___x_2722_;
v_isShared_2735_ = v_isSharedCheck_2739_;
goto v_resetjp_2733_;
}
else
{
lean_inc(v_a_2732_);
lean_dec(v___x_2722_);
v___x_2734_ = lean_box(0);
v_isShared_2735_ = v_isSharedCheck_2739_;
goto v_resetjp_2733_;
}
v_resetjp_2733_:
{
lean_object* v___x_2737_; 
if (v_isShared_2735_ == 0)
{
v___x_2737_ = v___x_2734_;
goto v_reusejp_2736_;
}
else
{
lean_object* v_reuseFailAlloc_2738_; 
v_reuseFailAlloc_2738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2738_, 0, v_a_2732_);
v___x_2737_ = v_reuseFailAlloc_2738_;
goto v_reusejp_2736_;
}
v_reusejp_2736_:
{
return v___x_2737_;
}
}
}
}
else
{
lean_object* v_a_2740_; lean_object* v___x_2742_; uint8_t v_isShared_2743_; uint8_t v_isSharedCheck_2747_; 
lean_dec_ref(v_afterSet_2702_);
lean_dec_ref(v_getParam_2701_);
lean_dec_ref(v_toAttributeImplCore_2700_);
v_a_2740_ = lean_ctor_get(v___x_2717_, 0);
v_isSharedCheck_2747_ = !lean_is_exclusive(v___x_2717_);
if (v_isSharedCheck_2747_ == 0)
{
v___x_2742_ = v___x_2717_;
v_isShared_2743_ = v_isSharedCheck_2747_;
goto v_resetjp_2741_;
}
else
{
lean_inc(v_a_2740_);
lean_dec(v___x_2717_);
v___x_2742_ = lean_box(0);
v_isShared_2743_ = v_isSharedCheck_2747_;
goto v_resetjp_2741_;
}
v_resetjp_2741_:
{
lean_object* v___x_2745_; 
if (v_isShared_2743_ == 0)
{
v___x_2745_ = v___x_2742_;
goto v_reusejp_2744_;
}
else
{
lean_object* v_reuseFailAlloc_2746_; 
v_reuseFailAlloc_2746_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2746_, 0, v_a_2740_);
v___x_2745_ = v_reuseFailAlloc_2746_;
goto v_reusejp_2744_;
}
v_reusejp_2744_:
{
return v___x_2745_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___boxed(lean_object* v_impl_2748_, lean_object* v_a_2749_){
_start:
{
lean_object* v_res_2750_; 
v_res_2750_ = l_Lean_registerParametricAttribute___redArg(v_impl_2748_);
return v_res_2750_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute(lean_object* v_00_u03b1_2751_, lean_object* v_impl_2752_){
_start:
{
lean_object* v___x_2754_; 
v___x_2754_ = l_Lean_registerParametricAttribute___redArg(v_impl_2752_);
return v___x_2754_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___boxed(lean_object* v_00_u03b1_2755_, lean_object* v_impl_2756_, lean_object* v_a_2757_){
_start:
{
lean_object* v_res_2758_; 
v_res_2758_ = l_Lean_registerParametricAttribute(v_00_u03b1_2755_, v_impl_2756_);
return v_res_2758_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttribute_spec__0(lean_object* v_00_u03b1_2759_, lean_object* v_impl_2760_, lean_object* v_env_2761_, lean_object* v_as_2762_, size_t v_i_2763_, size_t v_stop_2764_, lean_object* v_b_2765_){
_start:
{
lean_object* v___x_2766_; 
v___x_2766_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttribute_spec__0___redArg(v_impl_2760_, v_env_2761_, v_as_2762_, v_i_2763_, v_stop_2764_, v_b_2765_);
return v___x_2766_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttribute_spec__0___boxed(lean_object* v_00_u03b1_2767_, lean_object* v_impl_2768_, lean_object* v_env_2769_, lean_object* v_as_2770_, lean_object* v_i_2771_, lean_object* v_stop_2772_, lean_object* v_b_2773_){
_start:
{
size_t v_i_boxed_2774_; size_t v_stop_boxed_2775_; lean_object* v_res_2776_; 
v_i_boxed_2774_ = lean_unbox_usize(v_i_2771_);
lean_dec(v_i_2771_);
v_stop_boxed_2775_ = lean_unbox_usize(v_stop_2772_);
lean_dec(v_stop_2772_);
v_res_2776_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttribute_spec__0(v_00_u03b1_2767_, v_impl_2768_, v_env_2769_, v_as_2770_, v_i_boxed_2774_, v_stop_boxed_2775_, v_b_2773_);
lean_dec_ref(v_as_2770_);
return v_res_2776_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1___redArg(lean_object* v_init_2777_, lean_object* v_t_2778_){
_start:
{
lean_object* v___x_2779_; 
v___x_2779_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1_spec__1___redArg(v_init_2777_, v_t_2778_);
return v___x_2779_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1___redArg___boxed(lean_object* v_init_2780_, lean_object* v_t_2781_){
_start:
{
lean_object* v_res_2782_; 
v_res_2782_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1___redArg(v_init_2780_, v_t_2781_);
lean_dec(v_t_2781_);
return v_res_2782_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1(lean_object* v_00_u03b1_2783_, lean_object* v_init_2784_, lean_object* v_t_2785_){
_start:
{
lean_object* v___x_2786_; 
v___x_2786_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1_spec__1___redArg(v_init_2784_, v_t_2785_);
return v___x_2786_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1___boxed(lean_object* v_00_u03b1_2787_, lean_object* v_init_2788_, lean_object* v_t_2789_){
_start:
{
lean_object* v_res_2790_; 
v_res_2790_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1(v_00_u03b1_2787_, v_init_2788_, v_t_2789_);
lean_dec(v_t_2789_);
return v_res_2790_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2(lean_object* v_00_u03b1_2791_, lean_object* v_n_2792_, lean_object* v_as_2793_, lean_object* v_lo_2794_, lean_object* v_hi_2795_, lean_object* v_w_2796_, lean_object* v_hlo_2797_, lean_object* v_hhi_2798_){
_start:
{
lean_object* v___x_2799_; 
v___x_2799_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2___redArg(v_as_2793_, v_lo_2794_, v_hi_2795_);
return v___x_2799_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2___boxed(lean_object* v_00_u03b1_2800_, lean_object* v_n_2801_, lean_object* v_as_2802_, lean_object* v_lo_2803_, lean_object* v_hi_2804_, lean_object* v_w_2805_, lean_object* v_hlo_2806_, lean_object* v_hhi_2807_){
_start:
{
lean_object* v_res_2808_; 
v_res_2808_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2(v_00_u03b1_2800_, v_n_2801_, v_as_2802_, v_lo_2803_, v_hi_2804_, v_w_2805_, v_hlo_2806_, v_hhi_2807_);
lean_dec(v_hi_2804_);
lean_dec(v_n_2801_);
return v_res_2808_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3(lean_object* v_00_u03b1_2809_, lean_object* v_snd_2810_, lean_object* v_as_2811_, lean_object* v_start_2812_, lean_object* v_stop_2813_){
_start:
{
lean_object* v___x_2814_; 
v___x_2814_ = l_Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3___redArg(v_snd_2810_, v_as_2811_, v_start_2812_, v_stop_2813_);
return v___x_2814_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3___boxed(lean_object* v_00_u03b1_2815_, lean_object* v_snd_2816_, lean_object* v_as_2817_, lean_object* v_start_2818_, lean_object* v_stop_2819_){
_start:
{
lean_object* v_res_2820_; 
v_res_2820_ = l_Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3(v_00_u03b1_2815_, v_snd_2816_, v_as_2817_, v_start_2818_, v_stop_2819_);
lean_dec(v_stop_2819_);
lean_dec(v_start_2818_);
lean_dec_ref(v_as_2817_);
lean_dec(v_snd_2816_);
return v_res_2820_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1_spec__1(lean_object* v_00_u03b1_2821_, lean_object* v_init_2822_, lean_object* v_x_2823_){
_start:
{
lean_object* v___x_2824_; 
v___x_2824_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1_spec__1___redArg(v_init_2822_, v_x_2823_);
return v___x_2824_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1_spec__1___boxed(lean_object* v_00_u03b1_2825_, lean_object* v_init_2826_, lean_object* v_x_2827_){
_start:
{
lean_object* v_res_2828_; 
v_res_2828_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1_spec__1(v_00_u03b1_2825_, v_init_2826_, v_x_2827_);
lean_dec(v_x_2827_);
return v_res_2828_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3_spec__4(lean_object* v_00_u03b1_2829_, lean_object* v_snd_2830_, lean_object* v_as_2831_, size_t v_i_2832_, size_t v_stop_2833_, lean_object* v_b_2834_){
_start:
{
lean_object* v___x_2835_; 
v___x_2835_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3_spec__4___redArg(v_snd_2830_, v_as_2831_, v_i_2832_, v_stop_2833_, v_b_2834_);
return v___x_2835_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3_spec__4___boxed(lean_object* v_00_u03b1_2836_, lean_object* v_snd_2837_, lean_object* v_as_2838_, lean_object* v_i_2839_, lean_object* v_stop_2840_, lean_object* v_b_2841_){
_start:
{
size_t v_i_boxed_2842_; size_t v_stop_boxed_2843_; lean_object* v_res_2844_; 
v_i_boxed_2842_ = lean_unbox_usize(v_i_2839_);
lean_dec(v_i_2839_);
v_stop_boxed_2843_ = lean_unbox_usize(v_stop_2840_);
lean_dec(v_stop_2840_);
v_res_2844_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3_spec__4(v_00_u03b1_2836_, v_snd_2837_, v_as_2838_, v_i_boxed_2842_, v_stop_boxed_2843_, v_b_2841_);
lean_dec_ref(v_as_2838_);
lean_dec(v_snd_2837_);
return v_res_2844_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParam_x3f___redArg___lam__1(lean_object* v_decl_2845_, lean_object* v___x_2846_, lean_object* v___x_2847_, lean_object* v_a_2848_, lean_object* v_x_2849_, lean_object* v___y_2850_){
_start:
{
lean_object* v_fst_2851_; uint8_t v___x_2852_; 
v_fst_2851_ = lean_ctor_get(v_a_2848_, 0);
v___x_2852_ = lean_name_eq(v_fst_2851_, v_decl_2845_);
if (v___x_2852_ == 0)
{
lean_object* v___x_2853_; 
lean_dec_ref(v_a_2848_);
v___x_2853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2853_, 0, v___x_2846_);
return v___x_2853_;
}
else
{
lean_object* v___x_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; 
lean_dec_ref(v___x_2846_);
v___x_2854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2854_, 0, v_a_2848_);
v___x_2855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2855_, 0, v___x_2854_);
v___x_2856_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2856_, 0, v___x_2855_);
lean_ctor_set(v___x_2856_, 1, v___x_2847_);
v___x_2857_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2857_, 0, v___x_2856_);
return v___x_2857_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParam_x3f___redArg___lam__1___boxed(lean_object* v_decl_2858_, lean_object* v___x_2859_, lean_object* v___x_2860_, lean_object* v_a_2861_, lean_object* v_x_2862_, lean_object* v___y_2863_){
_start:
{
lean_object* v_res_2864_; 
v_res_2864_ = l_Lean_ParametricAttribute_getParam_x3f___redArg___lam__1(v_decl_2858_, v___x_2859_, v___x_2860_, v_a_2861_, v_x_2862_, v___y_2863_);
lean_dec_ref(v___y_2863_);
lean_dec(v_decl_2858_);
return v_res_2864_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParam_x3f___redArg(lean_object* v_inst_2891_, lean_object* v_attr_2892_, lean_object* v_env_2893_, lean_object* v_decl_2894_){
_start:
{
lean_object* v___y_2896_; lean_object* v___x_2907_; lean_object* v___x_2908_; 
v___x_2907_ = ((lean_object*)(l_Lean_ParametricAttribute_getParam_x3f___redArg___closed__0));
v___x_2908_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2893_, v_decl_2894_);
if (lean_obj_tag(v___x_2908_) == 0)
{
lean_object* v_ext_2909_; lean_object* v_toEnvExtension_2910_; lean_object* v_asyncMode_2911_; lean_object* v___x_2912_; lean_object* v___x_2913_; lean_object* v_snd_2914_; lean_object* v___x_2915_; 
lean_dec(v_inst_2891_);
v_ext_2909_ = lean_ctor_get(v_attr_2892_, 1);
v_toEnvExtension_2910_ = lean_ctor_get(v_ext_2909_, 0);
v_asyncMode_2911_ = lean_ctor_get(v_toEnvExtension_2910_, 2);
v___x_2912_ = lean_box(0);
v___x_2913_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2907_, v_ext_2909_, v_env_2893_, v_asyncMode_2911_, v___x_2912_);
v_snd_2914_ = lean_ctor_get(v___x_2913_, 1);
lean_inc(v_snd_2914_);
lean_dec(v___x_2913_);
v___x_2915_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_snd_2914_, v_decl_2894_);
lean_dec(v_decl_2894_);
lean_dec(v_snd_2914_);
return v___x_2915_;
}
else
{
uint8_t v_preserveOrder_2916_; 
v_preserveOrder_2916_ = lean_ctor_get_uint8(v_attr_2892_, sizeof(void*)*2);
if (v_preserveOrder_2916_ == 0)
{
lean_object* v_val_2917_; lean_object* v_ext_2918_; uint8_t v___x_2919_; lean_object* v___x_2920_; lean_object* v___x_2921_; lean_object* v___x_2922_; uint8_t v___x_2923_; 
v_val_2917_ = lean_ctor_get(v___x_2908_, 0);
lean_inc(v_val_2917_);
lean_dec_ref(v___x_2908_);
v_ext_2918_ = lean_ctor_get(v_attr_2892_, 1);
v___x_2919_ = 0;
v___x_2920_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_2907_, v_ext_2918_, v_env_2893_, v_val_2917_, v___x_2919_);
lean_dec(v_val_2917_);
lean_dec_ref(v_env_2893_);
v___x_2921_ = lean_unsigned_to_nat(0u);
v___x_2922_ = lean_array_get_size(v___x_2920_);
v___x_2923_ = lean_nat_dec_lt(v___x_2921_, v___x_2922_);
if (v___x_2923_ == 0)
{
lean_object* v___x_2924_; 
lean_dec_ref(v___x_2920_);
lean_dec(v_decl_2894_);
lean_dec(v_inst_2891_);
v___x_2924_ = lean_box(0);
return v___x_2924_;
}
else
{
lean_object* v___x_2925_; lean_object* v___x_2926_; uint8_t v___x_2927_; 
v___x_2925_ = lean_unsigned_to_nat(1u);
v___x_2926_ = lean_nat_sub(v___x_2922_, v___x_2925_);
v___x_2927_ = lean_nat_dec_le(v___x_2921_, v___x_2926_);
if (v___x_2927_ == 0)
{
lean_object* v___x_2928_; 
lean_dec(v___x_2926_);
lean_dec_ref(v___x_2920_);
lean_dec(v_decl_2894_);
lean_dec(v_inst_2891_);
v___x_2928_ = lean_box(0);
return v___x_2928_;
}
else
{
lean_object* v___f_2929_; lean_object* v___x_2930_; lean_object* v___x_2931_; lean_object* v___x_2932_; 
v___f_2929_ = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2___redArg___closed__0));
v___x_2930_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2930_, 0, v_decl_2894_);
lean_ctor_set(v___x_2930_, 1, v_inst_2891_);
v___x_2931_ = ((lean_object*)(l_Lean_ParametricAttribute_getParam_x3f___redArg___closed__1));
v___x_2932_ = l_Array_binSearchAux___redArg(v___f_2929_, v___x_2931_, v___x_2920_, v___x_2930_, v___x_2921_, v___x_2926_);
lean_dec_ref(v___x_2920_);
v___y_2896_ = v___x_2932_;
goto v___jp_2895_;
}
}
}
else
{
lean_object* v_val_2933_; lean_object* v_ext_2934_; uint8_t v___x_2935_; lean_object* v___x_2936_; lean_object* v___x_2937_; lean_object* v___x_2938_; lean_object* v___x_2939_; lean_object* v___x_2940_; lean_object* v___f_2941_; size_t v_sz_2942_; size_t v___x_2943_; lean_object* v___x_2944_; lean_object* v_fst_2945_; 
lean_dec(v_inst_2891_);
v_val_2933_ = lean_ctor_get(v___x_2908_, 0);
lean_inc(v_val_2933_);
lean_dec_ref(v___x_2908_);
v_ext_2934_ = lean_ctor_get(v_attr_2892_, 1);
v___x_2935_ = 0;
v___x_2936_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_2907_, v_ext_2934_, v_env_2893_, v_val_2933_, v___x_2935_);
lean_dec(v_val_2933_);
lean_dec_ref(v_env_2893_);
v___x_2937_ = ((lean_object*)(l_Lean_ParametricAttribute_getParam_x3f___redArg___closed__11));
v___x_2938_ = lean_box(0);
v___x_2939_ = lean_box(0);
v___x_2940_ = ((lean_object*)(l_Lean_ParametricAttribute_getParam_x3f___redArg___closed__12));
v___f_2941_ = lean_alloc_closure((void*)(l_Lean_ParametricAttribute_getParam_x3f___redArg___lam__1___boxed), 6, 3);
lean_closure_set(v___f_2941_, 0, v_decl_2894_);
lean_closure_set(v___f_2941_, 1, v___x_2940_);
lean_closure_set(v___f_2941_, 2, v___x_2939_);
v_sz_2942_ = lean_array_size(v___x_2936_);
v___x_2943_ = ((size_t)0ULL);
v___x_2944_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_2937_, v___x_2936_, v___f_2941_, v_sz_2942_, v___x_2943_, v___x_2940_);
v_fst_2945_ = lean_ctor_get(v___x_2944_, 0);
lean_inc(v_fst_2945_);
lean_dec(v___x_2944_);
if (lean_obj_tag(v_fst_2945_) == 0)
{
return v___x_2938_;
}
else
{
lean_object* v_val_2946_; 
v_val_2946_ = lean_ctor_get(v_fst_2945_, 0);
lean_inc(v_val_2946_);
lean_dec_ref(v_fst_2945_);
v___y_2896_ = v_val_2946_;
goto v___jp_2895_;
}
}
}
v___jp_2895_:
{
if (lean_obj_tag(v___y_2896_) == 0)
{
lean_object* v___x_2897_; 
v___x_2897_ = lean_box(0);
return v___x_2897_;
}
else
{
lean_object* v_val_2898_; lean_object* v___x_2900_; uint8_t v_isShared_2901_; uint8_t v_isSharedCheck_2906_; 
v_val_2898_ = lean_ctor_get(v___y_2896_, 0);
v_isSharedCheck_2906_ = !lean_is_exclusive(v___y_2896_);
if (v_isSharedCheck_2906_ == 0)
{
v___x_2900_ = v___y_2896_;
v_isShared_2901_ = v_isSharedCheck_2906_;
goto v_resetjp_2899_;
}
else
{
lean_inc(v_val_2898_);
lean_dec(v___y_2896_);
v___x_2900_ = lean_box(0);
v_isShared_2901_ = v_isSharedCheck_2906_;
goto v_resetjp_2899_;
}
v_resetjp_2899_:
{
lean_object* v_snd_2902_; lean_object* v___x_2904_; 
v_snd_2902_ = lean_ctor_get(v_val_2898_, 1);
lean_inc(v_snd_2902_);
lean_dec(v_val_2898_);
if (v_isShared_2901_ == 0)
{
lean_ctor_set(v___x_2900_, 0, v_snd_2902_);
v___x_2904_ = v___x_2900_;
goto v_reusejp_2903_;
}
else
{
lean_object* v_reuseFailAlloc_2905_; 
v_reuseFailAlloc_2905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2905_, 0, v_snd_2902_);
v___x_2904_ = v_reuseFailAlloc_2905_;
goto v_reusejp_2903_;
}
v_reusejp_2903_:
{
return v___x_2904_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParam_x3f___redArg___boxed(lean_object* v_inst_2947_, lean_object* v_attr_2948_, lean_object* v_env_2949_, lean_object* v_decl_2950_){
_start:
{
lean_object* v_res_2951_; 
v_res_2951_ = l_Lean_ParametricAttribute_getParam_x3f___redArg(v_inst_2947_, v_attr_2948_, v_env_2949_, v_decl_2950_);
lean_dec_ref(v_attr_2948_);
return v_res_2951_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParam_x3f(lean_object* v_00_u03b1_2952_, lean_object* v_inst_2953_, lean_object* v_attr_2954_, lean_object* v_env_2955_, lean_object* v_decl_2956_){
_start:
{
lean_object* v___x_2957_; 
v___x_2957_ = l_Lean_ParametricAttribute_getParam_x3f___redArg(v_inst_2953_, v_attr_2954_, v_env_2955_, v_decl_2956_);
return v___x_2957_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParam_x3f___boxed(lean_object* v_00_u03b1_2958_, lean_object* v_inst_2959_, lean_object* v_attr_2960_, lean_object* v_env_2961_, lean_object* v_decl_2962_){
_start:
{
lean_object* v_res_2963_; 
v_res_2963_ = l_Lean_ParametricAttribute_getParam_x3f(v_00_u03b1_2958_, v_inst_2959_, v_attr_2960_, v_env_2961_, v_decl_2962_);
lean_dec_ref(v_attr_2960_);
return v_res_2963_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_setParam___redArg(lean_object* v_attr_2968_, lean_object* v_env_2969_, lean_object* v_decl_2970_, lean_object* v_param_2971_){
_start:
{
lean_object* v___x_2972_; 
v___x_2972_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2969_, v_decl_2970_);
if (lean_obj_tag(v___x_2972_) == 0)
{
lean_object* v_ext_2973_; lean_object* v_toEnvExtension_2974_; lean_object* v_attr_2975_; lean_object* v_asyncMode_2976_; lean_object* v___x_2977_; lean_object* v___x_2978_; lean_object* v___x_2979_; lean_object* v_snd_2980_; lean_object* v___x_2982_; uint8_t v_isShared_2983_; uint8_t v_isSharedCheck_3010_; 
v_ext_2973_ = lean_ctor_get(v_attr_2968_, 1);
lean_inc_ref(v_ext_2973_);
v_toEnvExtension_2974_ = lean_ctor_get(v_ext_2973_, 0);
v_attr_2975_ = lean_ctor_get(v_attr_2968_, 0);
lean_inc_ref(v_attr_2975_);
lean_dec_ref(v_attr_2968_);
v_asyncMode_2976_ = lean_ctor_get(v_toEnvExtension_2974_, 2);
lean_inc(v_asyncMode_2976_);
v___x_2977_ = ((lean_object*)(l_Lean_ParametricAttribute_getParam_x3f___redArg___closed__0));
v___x_2978_ = lean_box(0);
lean_inc_ref(v_env_2969_);
v___x_2979_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2977_, v_ext_2973_, v_env_2969_, v_asyncMode_2976_, v___x_2978_);
v_snd_2980_ = lean_ctor_get(v___x_2979_, 1);
v_isSharedCheck_3010_ = !lean_is_exclusive(v___x_2979_);
if (v_isSharedCheck_3010_ == 0)
{
lean_object* v_unused_3011_; 
v_unused_3011_ = lean_ctor_get(v___x_2979_, 0);
lean_dec(v_unused_3011_);
v___x_2982_ = v___x_2979_;
v_isShared_2983_ = v_isSharedCheck_3010_;
goto v_resetjp_2981_;
}
else
{
lean_inc(v_snd_2980_);
lean_dec(v___x_2979_);
v___x_2982_ = lean_box(0);
v_isShared_2983_ = v_isSharedCheck_3010_;
goto v_resetjp_2981_;
}
v_resetjp_2981_:
{
lean_object* v___x_2984_; 
v___x_2984_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_snd_2980_, v_decl_2970_);
lean_dec(v_snd_2980_);
if (lean_obj_tag(v___x_2984_) == 0)
{
lean_object* v___x_2986_; 
lean_dec_ref(v_attr_2975_);
if (v_isShared_2983_ == 0)
{
lean_ctor_set(v___x_2982_, 1, v_param_2971_);
lean_ctor_set(v___x_2982_, 0, v_decl_2970_);
v___x_2986_ = v___x_2982_;
goto v_reusejp_2985_;
}
else
{
lean_object* v_reuseFailAlloc_2989_; 
v_reuseFailAlloc_2989_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2989_, 0, v_decl_2970_);
lean_ctor_set(v_reuseFailAlloc_2989_, 1, v_param_2971_);
v___x_2986_ = v_reuseFailAlloc_2989_;
goto v_reusejp_2985_;
}
v_reusejp_2985_:
{
lean_object* v___x_2987_; lean_object* v___x_2988_; 
v___x_2987_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_ext_2973_, v_env_2969_, v___x_2986_, v_asyncMode_2976_, v___x_2978_);
lean_dec(v_asyncMode_2976_);
v___x_2988_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2988_, 0, v___x_2987_);
return v___x_2988_;
}
}
else
{
lean_object* v___x_2991_; uint8_t v_isShared_2992_; uint8_t v_isSharedCheck_3008_; 
lean_del_object(v___x_2982_);
lean_dec(v_asyncMode_2976_);
lean_dec_ref(v_ext_2973_);
lean_dec(v_param_2971_);
lean_dec_ref(v_env_2969_);
v_isSharedCheck_3008_ = !lean_is_exclusive(v___x_2984_);
if (v_isSharedCheck_3008_ == 0)
{
lean_object* v_unused_3009_; 
v_unused_3009_ = lean_ctor_get(v___x_2984_, 0);
lean_dec(v_unused_3009_);
v___x_2991_ = v___x_2984_;
v_isShared_2992_ = v_isSharedCheck_3008_;
goto v_resetjp_2990_;
}
else
{
lean_dec(v___x_2984_);
v___x_2991_ = lean_box(0);
v_isShared_2992_ = v_isSharedCheck_3008_;
goto v_resetjp_2990_;
}
v_resetjp_2990_:
{
lean_object* v_toAttributeImplCore_2993_; lean_object* v_name_2994_; uint8_t v___x_2995_; lean_object* v___x_2996_; lean_object* v___x_2997_; lean_object* v___x_2998_; lean_object* v___x_2999_; lean_object* v___x_3000_; lean_object* v___x_3001_; lean_object* v___x_3002_; lean_object* v___x_3003_; lean_object* v___x_3004_; lean_object* v___x_3006_; 
v_toAttributeImplCore_2993_ = lean_ctor_get(v_attr_2975_, 0);
lean_inc_ref(v_toAttributeImplCore_2993_);
lean_dec_ref(v_attr_2975_);
v_name_2994_ = lean_ctor_get(v_toAttributeImplCore_2993_, 1);
lean_inc(v_name_2994_);
lean_dec_ref(v_toAttributeImplCore_2993_);
v___x_2995_ = 1;
v___x_2996_ = ((lean_object*)(l_Lean_ParametricAttribute_setParam___redArg___closed__0));
v___x_2997_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_2994_, v___x_2995_);
v___x_2998_ = lean_string_append(v___x_2996_, v___x_2997_);
lean_dec_ref(v___x_2997_);
v___x_2999_ = ((lean_object*)(l_Lean_ParametricAttribute_setParam___redArg___closed__1));
v___x_3000_ = lean_string_append(v___x_2998_, v___x_2999_);
v___x_3001_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_decl_2970_, v___x_2995_);
v___x_3002_ = lean_string_append(v___x_3000_, v___x_3001_);
lean_dec_ref(v___x_3001_);
v___x_3003_ = ((lean_object*)(l_Lean_ParametricAttribute_setParam___redArg___closed__2));
v___x_3004_ = lean_string_append(v___x_3002_, v___x_3003_);
if (v_isShared_2992_ == 0)
{
lean_ctor_set_tag(v___x_2991_, 0);
lean_ctor_set(v___x_2991_, 0, v___x_3004_);
v___x_3006_ = v___x_2991_;
goto v_reusejp_3005_;
}
else
{
lean_object* v_reuseFailAlloc_3007_; 
v_reuseFailAlloc_3007_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3007_, 0, v___x_3004_);
v___x_3006_ = v_reuseFailAlloc_3007_;
goto v_reusejp_3005_;
}
v_reusejp_3005_:
{
return v___x_3006_;
}
}
}
}
}
else
{
lean_object* v___x_3013_; uint8_t v_isShared_3014_; uint8_t v_isSharedCheck_3031_; 
lean_dec(v_param_2971_);
lean_dec_ref(v_env_2969_);
v_isSharedCheck_3031_ = !lean_is_exclusive(v___x_2972_);
if (v_isSharedCheck_3031_ == 0)
{
lean_object* v_unused_3032_; 
v_unused_3032_ = lean_ctor_get(v___x_2972_, 0);
lean_dec(v_unused_3032_);
v___x_3013_ = v___x_2972_;
v_isShared_3014_ = v_isSharedCheck_3031_;
goto v_resetjp_3012_;
}
else
{
lean_dec(v___x_2972_);
v___x_3013_ = lean_box(0);
v_isShared_3014_ = v_isSharedCheck_3031_;
goto v_resetjp_3012_;
}
v_resetjp_3012_:
{
lean_object* v_attr_3015_; lean_object* v_toAttributeImplCore_3016_; lean_object* v_name_3017_; uint8_t v___x_3018_; lean_object* v___x_3019_; lean_object* v___x_3020_; lean_object* v___x_3021_; lean_object* v___x_3022_; lean_object* v___x_3023_; lean_object* v___x_3024_; lean_object* v___x_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; lean_object* v___x_3029_; 
v_attr_3015_ = lean_ctor_get(v_attr_2968_, 0);
lean_inc_ref(v_attr_3015_);
lean_dec_ref(v_attr_2968_);
v_toAttributeImplCore_3016_ = lean_ctor_get(v_attr_3015_, 0);
lean_inc_ref(v_toAttributeImplCore_3016_);
lean_dec_ref(v_attr_3015_);
v_name_3017_ = lean_ctor_get(v_toAttributeImplCore_3016_, 1);
lean_inc(v_name_3017_);
lean_dec_ref(v_toAttributeImplCore_3016_);
v___x_3018_ = 1;
v___x_3019_ = ((lean_object*)(l_Lean_ParametricAttribute_setParam___redArg___closed__0));
v___x_3020_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_3017_, v___x_3018_);
v___x_3021_ = lean_string_append(v___x_3019_, v___x_3020_);
lean_dec_ref(v___x_3020_);
v___x_3022_ = ((lean_object*)(l_Lean_ParametricAttribute_setParam___redArg___closed__1));
v___x_3023_ = lean_string_append(v___x_3021_, v___x_3022_);
v___x_3024_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_decl_2970_, v___x_3018_);
v___x_3025_ = lean_string_append(v___x_3023_, v___x_3024_);
lean_dec_ref(v___x_3024_);
v___x_3026_ = ((lean_object*)(l_Lean_ParametricAttribute_setParam___redArg___closed__3));
v___x_3027_ = lean_string_append(v___x_3025_, v___x_3026_);
if (v_isShared_3014_ == 0)
{
lean_ctor_set_tag(v___x_3013_, 0);
lean_ctor_set(v___x_3013_, 0, v___x_3027_);
v___x_3029_ = v___x_3013_;
goto v_reusejp_3028_;
}
else
{
lean_object* v_reuseFailAlloc_3030_; 
v_reuseFailAlloc_3030_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3030_, 0, v___x_3027_);
v___x_3029_ = v_reuseFailAlloc_3030_;
goto v_reusejp_3028_;
}
v_reusejp_3028_:
{
return v___x_3029_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_setParam(lean_object* v_00_u03b1_3033_, lean_object* v_attr_3034_, lean_object* v_env_3035_, lean_object* v_decl_3036_, lean_object* v_param_3037_){
_start:
{
lean_object* v___x_3038_; 
v___x_3038_ = l_Lean_ParametricAttribute_setParam___redArg(v_attr_3034_, v_env_3035_, v_decl_3036_, v_param_3037_);
return v___x_3038_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___lam__0(lean_object* v_x_3039_, lean_object* v___y_3040_){
_start:
{
lean_object* v___x_3042_; lean_object* v___x_3043_; 
v___x_3042_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___lam__0___closed__1));
v___x_3043_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3043_, 0, v___x_3042_);
return v___x_3043_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___lam__0___boxed(lean_object* v_x_3044_, lean_object* v___y_3045_, lean_object* v___y_3046_){
_start:
{
lean_object* v_res_3047_; 
v_res_3047_ = l_Lean_instInhabitedEnumAttributes_default___lam__0(v_x_3044_, v___y_3045_);
lean_dec_ref(v___y_3045_);
lean_dec_ref(v_x_3044_);
return v_res_3047_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___lam__1(lean_object* v_s_3048_, lean_object* v_x_3049_){
_start:
{
lean_inc(v_s_3048_);
return v_s_3048_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___lam__1___boxed(lean_object* v_s_3050_, lean_object* v_x_3051_){
_start:
{
lean_object* v_res_3052_; 
v_res_3052_ = l_Lean_instInhabitedEnumAttributes_default___lam__1(v_s_3050_, v_x_3051_);
lean_dec_ref(v_x_3051_);
lean_dec(v_s_3050_);
return v_res_3052_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___lam__2(lean_object* v_x_3053_, lean_object* v_x_3054_, uint8_t v_x_3055_){
_start:
{
lean_object* v___x_3056_; 
v___x_3056_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___lam__2___closed__0));
return v___x_3056_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___lam__2___boxed(lean_object* v_x_3057_, lean_object* v_x_3058_, lean_object* v_x_3059_){
_start:
{
uint8_t v_x_72__boxed_3060_; lean_object* v_res_3061_; 
v_x_72__boxed_3060_ = lean_unbox(v_x_3059_);
v_res_3061_ = l_Lean_instInhabitedEnumAttributes_default___lam__2(v_x_3057_, v_x_3058_, v_x_72__boxed_3060_);
lean_dec(v_x_3058_);
lean_dec_ref(v_x_3057_);
return v_res_3061_;
}
}
static lean_object* _init_l_Lean_instInhabitedEnumAttributes_default___closed__3(void){
_start:
{
lean_object* v___x_3065_; 
v___x_3065_ = l_Lean_instInhabitedEnvExtension_default(lean_box(0));
return v___x_3065_;
}
}
static lean_object* _init_l_Lean_instInhabitedEnumAttributes_default___closed__4(void){
_start:
{
lean_object* v___f_3066_; lean_object* v___f_3067_; lean_object* v___f_3068_; lean_object* v___f_3069_; lean_object* v___x_3070_; lean_object* v___x_3071_; lean_object* v___x_3072_; 
v___f_3066_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___closed__3));
v___f_3067_ = ((lean_object*)(l_Lean_instInhabitedEnumAttributes_default___closed__2));
v___f_3068_ = ((lean_object*)(l_Lean_instInhabitedEnumAttributes_default___closed__1));
v___f_3069_ = ((lean_object*)(l_Lean_instInhabitedEnumAttributes_default___closed__0));
v___x_3070_ = lean_box(0);
v___x_3071_ = lean_obj_once(&l_Lean_instInhabitedEnumAttributes_default___closed__3, &l_Lean_instInhabitedEnumAttributes_default___closed__3_once, _init_l_Lean_instInhabitedEnumAttributes_default___closed__3);
v___x_3072_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3072_, 0, v___x_3071_);
lean_ctor_set(v___x_3072_, 1, v___x_3070_);
lean_ctor_set(v___x_3072_, 2, v___f_3069_);
lean_ctor_set(v___x_3072_, 3, v___f_3068_);
lean_ctor_set(v___x_3072_, 4, v___f_3067_);
lean_ctor_set(v___x_3072_, 5, v___f_3066_);
return v___x_3072_;
}
}
static lean_object* _init_l_Lean_instInhabitedEnumAttributes_default___closed__5(void){
_start:
{
lean_object* v___x_3073_; lean_object* v___x_3074_; lean_object* v___x_3075_; 
v___x_3073_ = lean_obj_once(&l_Lean_instInhabitedEnumAttributes_default___closed__4, &l_Lean_instInhabitedEnumAttributes_default___closed__4_once, _init_l_Lean_instInhabitedEnumAttributes_default___closed__4);
v___x_3074_ = lean_box(0);
v___x_3075_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3075_, 0, v___x_3074_);
lean_ctor_set(v___x_3075_, 1, v___x_3073_);
return v___x_3075_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default(lean_object* v_a_3076_){
_start:
{
lean_object* v___x_3077_; 
v___x_3077_ = lean_obj_once(&l_Lean_instInhabitedEnumAttributes_default___closed__5, &l_Lean_instInhabitedEnumAttributes_default___closed__5_once, _init_l_Lean_instInhabitedEnumAttributes_default___closed__5);
return v___x_3077_;
}
}
static lean_object* _init_l_Lean_instInhabitedEnumAttributes___closed__0(void){
_start:
{
lean_object* v___x_3078_; 
v___x_3078_ = l_Lean_instInhabitedEnumAttributes_default(lean_box(0));
return v___x_3078_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes(lean_object* v_a_3079_){
_start:
{
lean_object* v___x_3080_; 
v___x_3080_ = lean_obj_once(&l_Lean_instInhabitedEnumAttributes___closed__0, &l_Lean_instInhabitedEnumAttributes___closed__0_once, _init_l_Lean_instInhabitedEnumAttributes___closed__0);
return v___x_3080_;
}
}
static lean_object* _init_l_Lean_registerEnumAttributes___auto__1(void){
_start:
{
lean_object* v___x_3081_; 
v___x_3081_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__28, &l_Lean_AttributeImplCore_ref___autoParam___closed__28_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__28);
return v___x_3081_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__0(lean_object* v_x_3082_){
_start:
{
lean_object* v___x_3083_; 
v___x_3083_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___lam__2___closed__0));
return v___x_3083_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__0___boxed(lean_object* v_x_3084_){
_start:
{
lean_object* v_res_3085_; 
v_res_3085_ = l_Lean_registerEnumAttributes___redArg___lam__0(v_x_3084_);
lean_dec(v_x_3084_);
return v_res_3085_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___redArg(lean_object* v_newState_3086_, lean_object* v_x_3087_, lean_object* v_x_3088_){
_start:
{
if (lean_obj_tag(v_x_3088_) == 0)
{
return v_x_3087_;
}
else
{
lean_object* v_head_3089_; lean_object* v_tail_3090_; lean_object* v___x_3091_; 
v_head_3089_ = lean_ctor_get(v_x_3088_, 0);
lean_inc(v_head_3089_);
v_tail_3090_ = lean_ctor_get(v_x_3088_, 1);
lean_inc(v_tail_3090_);
lean_dec_ref(v_x_3088_);
v___x_3091_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_newState_3086_, v_head_3089_);
if (lean_obj_tag(v___x_3091_) == 1)
{
lean_object* v_val_3092_; lean_object* v___x_3093_; 
v_val_3092_ = lean_ctor_get(v___x_3091_, 0);
lean_inc(v_val_3092_);
lean_dec_ref(v___x_3091_);
v___x_3093_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_head_3089_, v_val_3092_, v_x_3087_);
v_x_3087_ = v___x_3093_;
v_x_3088_ = v_tail_3090_;
goto _start;
}
else
{
lean_dec(v___x_3091_);
lean_dec(v_head_3089_);
v_x_3088_ = v_tail_3090_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___redArg___boxed(lean_object* v_newState_3096_, lean_object* v_x_3097_, lean_object* v_x_3098_){
_start:
{
lean_object* v_res_3099_; 
v_res_3099_ = l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___redArg(v_newState_3096_, v_x_3097_, v_x_3098_);
lean_dec(v_newState_3096_);
return v_res_3099_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__1(lean_object* v_x_3100_, lean_object* v_newState_3101_, lean_object* v_consts_3102_, lean_object* v_st_3103_){
_start:
{
lean_object* v___x_3104_; 
v___x_3104_ = l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___redArg(v_newState_3101_, v_st_3103_, v_consts_3102_);
return v___x_3104_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__1___boxed(lean_object* v_x_3105_, lean_object* v_newState_3106_, lean_object* v_consts_3107_, lean_object* v_st_3108_){
_start:
{
lean_object* v_res_3109_; 
v_res_3109_ = l_Lean_registerEnumAttributes___redArg___lam__1(v_x_3105_, v_newState_3106_, v_consts_3107_, v_st_3108_);
lean_dec(v_newState_3106_);
lean_dec(v_x_3105_);
return v_res_3109_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__2(lean_object* v_s_3119_){
_start:
{
lean_object* v___x_3120_; lean_object* v___y_3122_; 
v___x_3120_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___lam__2___closed__3));
if (lean_obj_tag(v_s_3119_) == 0)
{
lean_object* v_size_3126_; 
v_size_3126_ = lean_ctor_get(v_s_3119_, 0);
lean_inc(v_size_3126_);
lean_dec_ref(v_s_3119_);
v___y_3122_ = v_size_3126_;
goto v___jp_3121_;
}
else
{
lean_object* v___x_3127_; 
v___x_3127_ = lean_unsigned_to_nat(0u);
v___y_3122_ = v___x_3127_;
goto v___jp_3121_;
}
v___jp_3121_:
{
lean_object* v___x_3123_; lean_object* v___x_3124_; lean_object* v___x_3125_; 
v___x_3123_ = l_Nat_reprFast(v___y_3122_);
v___x_3124_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3124_, 0, v___x_3123_);
v___x_3125_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3125_, 0, v___x_3120_);
lean_ctor_set(v___x_3125_, 1, v___x_3124_);
return v___x_3125_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg(lean_object* v_env_3128_, lean_object* v_as_3129_, size_t v_i_3130_, size_t v_stop_3131_, lean_object* v_b_3132_){
_start:
{
lean_object* v___y_3134_; uint8_t v___x_3138_; 
v___x_3138_ = lean_usize_dec_eq(v_i_3130_, v_stop_3131_);
if (v___x_3138_ == 0)
{
lean_object* v___x_3139_; lean_object* v_fst_3140_; uint8_t v___x_3141_; 
v___x_3139_ = lean_array_uget_borrowed(v_as_3129_, v_i_3130_);
v_fst_3140_ = lean_ctor_get(v___x_3139_, 0);
lean_inc(v_fst_3140_);
lean_inc_ref(v_env_3128_);
v___x_3141_ = l_Lean_Environment_contains(v_env_3128_, v_fst_3140_, v___x_3138_);
if (v___x_3141_ == 0)
{
v___y_3134_ = v_b_3132_;
goto v___jp_3133_;
}
else
{
lean_object* v___x_3142_; 
lean_inc(v___x_3139_);
v___x_3142_ = lean_array_push(v_b_3132_, v___x_3139_);
v___y_3134_ = v___x_3142_;
goto v___jp_3133_;
}
}
else
{
lean_dec_ref(v_env_3128_);
return v_b_3132_;
}
v___jp_3133_:
{
size_t v___x_3135_; size_t v___x_3136_; 
v___x_3135_ = ((size_t)1ULL);
v___x_3136_ = lean_usize_add(v_i_3130_, v___x_3135_);
v_i_3130_ = v___x_3136_;
v_b_3132_ = v___y_3134_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg___boxed(lean_object* v_env_3143_, lean_object* v_as_3144_, lean_object* v_i_3145_, lean_object* v_stop_3146_, lean_object* v_b_3147_){
_start:
{
size_t v_i_boxed_3148_; size_t v_stop_boxed_3149_; lean_object* v_res_3150_; 
v_i_boxed_3148_ = lean_unbox_usize(v_i_3145_);
lean_dec(v_i_3145_);
v_stop_boxed_3149_ = lean_unbox_usize(v_stop_3146_);
lean_dec(v_stop_3146_);
v_res_3150_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg(v_env_3143_, v_as_3144_, v_i_boxed_3148_, v_stop_boxed_3149_, v_b_3147_);
lean_dec_ref(v_as_3144_);
return v_res_3150_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__3(lean_object* v_env_3151_, lean_object* v_m_3152_, uint8_t v_x_3153_){
_start:
{
lean_object* v___y_3155_; lean_object* v___y_3156_; lean_object* v___y_3157_; lean_object* v___x_3161_; lean_object* v___y_3163_; lean_object* v___x_3169_; lean_object* v_r_3170_; lean_object* v___x_3171_; uint8_t v___x_3172_; 
v___x_3161_ = lean_unsigned_to_nat(0u);
v___x_3169_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___lam__2___closed__0));
v_r_3170_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1_spec__1___redArg(v___x_3169_, v_m_3152_);
v___x_3171_ = lean_array_get_size(v_r_3170_);
v___x_3172_ = lean_nat_dec_lt(v___x_3161_, v___x_3171_);
if (v___x_3172_ == 0)
{
lean_dec_ref(v_r_3170_);
lean_dec_ref(v_env_3151_);
v___y_3163_ = v___x_3169_;
goto v___jp_3162_;
}
else
{
uint8_t v___x_3173_; 
v___x_3173_ = lean_nat_dec_le(v___x_3171_, v___x_3171_);
if (v___x_3173_ == 0)
{
if (v___x_3172_ == 0)
{
lean_dec_ref(v_r_3170_);
lean_dec_ref(v_env_3151_);
v___y_3163_ = v___x_3169_;
goto v___jp_3162_;
}
else
{
size_t v___x_3174_; size_t v___x_3175_; lean_object* v___x_3176_; 
v___x_3174_ = ((size_t)0ULL);
v___x_3175_ = lean_usize_of_nat(v___x_3171_);
v___x_3176_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg(v_env_3151_, v_r_3170_, v___x_3174_, v___x_3175_, v___x_3169_);
lean_dec_ref(v_r_3170_);
v___y_3163_ = v___x_3176_;
goto v___jp_3162_;
}
}
else
{
size_t v___x_3177_; size_t v___x_3178_; lean_object* v___x_3179_; 
v___x_3177_ = ((size_t)0ULL);
v___x_3178_ = lean_usize_of_nat(v___x_3171_);
v___x_3179_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg(v_env_3151_, v_r_3170_, v___x_3177_, v___x_3178_, v___x_3169_);
lean_dec_ref(v_r_3170_);
v___y_3163_ = v___x_3179_;
goto v___jp_3162_;
}
}
v___jp_3154_:
{
uint8_t v___x_3158_; 
v___x_3158_ = lean_nat_dec_le(v___y_3157_, v___y_3155_);
if (v___x_3158_ == 0)
{
lean_object* v___x_3159_; 
lean_dec(v___y_3155_);
lean_inc(v___y_3157_);
v___x_3159_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2___redArg(v___y_3156_, v___y_3157_, v___y_3157_);
lean_dec(v___y_3157_);
return v___x_3159_;
}
else
{
lean_object* v___x_3160_; 
v___x_3160_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2___redArg(v___y_3156_, v___y_3157_, v___y_3155_);
lean_dec(v___y_3155_);
return v___x_3160_;
}
}
v___jp_3162_:
{
lean_object* v___x_3164_; uint8_t v___x_3165_; 
v___x_3164_ = lean_array_get_size(v___y_3163_);
v___x_3165_ = lean_nat_dec_eq(v___x_3164_, v___x_3161_);
if (v___x_3165_ == 0)
{
lean_object* v___x_3166_; lean_object* v___x_3167_; uint8_t v___x_3168_; 
v___x_3166_ = lean_unsigned_to_nat(1u);
v___x_3167_ = lean_nat_sub(v___x_3164_, v___x_3166_);
v___x_3168_ = lean_nat_dec_le(v___x_3161_, v___x_3167_);
if (v___x_3168_ == 0)
{
lean_inc(v___x_3167_);
v___y_3155_ = v___x_3167_;
v___y_3156_ = v___y_3163_;
v___y_3157_ = v___x_3167_;
goto v___jp_3154_;
}
else
{
v___y_3155_ = v___x_3167_;
v___y_3156_ = v___y_3163_;
v___y_3157_ = v___x_3161_;
goto v___jp_3154_;
}
}
else
{
return v___y_3163_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__3___boxed(lean_object* v_env_3180_, lean_object* v_m_3181_, lean_object* v_x_3182_){
_start:
{
uint8_t v_x_2060__boxed_3183_; lean_object* v_res_3184_; 
v_x_2060__boxed_3183_ = lean_unbox(v_x_3182_);
v_res_3184_ = l_Lean_registerEnumAttributes___redArg___lam__3(v_env_3180_, v_m_3181_, v_x_2060__boxed_3183_);
lean_dec(v_m_3181_);
return v_res_3184_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__4(lean_object* v_s_3185_, lean_object* v_p_3186_){
_start:
{
lean_object* v_fst_3187_; lean_object* v_snd_3188_; lean_object* v___x_3189_; 
v_fst_3187_ = lean_ctor_get(v_p_3186_, 0);
lean_inc(v_fst_3187_);
v_snd_3188_ = lean_ctor_get(v_p_3186_, 1);
lean_inc(v_snd_3188_);
lean_dec_ref(v_p_3186_);
v___x_3189_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_3187_, v_snd_3188_, v_s_3185_);
return v___x_3189_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__6(lean_object* v___x_3190_, lean_object* v_x_3191_, lean_object* v_x_3192_){
_start:
{
lean_object* v___x_3194_; 
v___x_3194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3194_, 0, v___x_3190_);
return v___x_3194_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__6___boxed(lean_object* v___x_3195_, lean_object* v_x_3196_, lean_object* v_x_3197_, lean_object* v___y_3198_){
_start:
{
lean_object* v_res_3199_; 
v_res_3199_ = l_Lean_registerEnumAttributes___redArg___lam__6(v___x_3195_, v_x_3196_, v_x_3197_);
lean_dec_ref(v_x_3197_);
lean_dec_ref(v_x_3196_);
return v_res_3199_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_registerEnumAttributes_spec__3(lean_object* v_as_3200_){
_start:
{
if (lean_obj_tag(v_as_3200_) == 0)
{
lean_object* v___x_3202_; lean_object* v___x_3203_; 
v___x_3202_ = lean_box(0);
v___x_3203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3203_, 0, v___x_3202_);
return v___x_3203_;
}
else
{
lean_object* v_head_3204_; lean_object* v_tail_3205_; lean_object* v___x_3206_; 
v_head_3204_ = lean_ctor_get(v_as_3200_, 0);
lean_inc(v_head_3204_);
v_tail_3205_ = lean_ctor_get(v_as_3200_, 1);
lean_inc(v_tail_3205_);
lean_dec_ref(v_as_3200_);
v___x_3206_ = l_Lean_registerBuiltinAttribute(v_head_3204_);
if (lean_obj_tag(v___x_3206_) == 0)
{
lean_dec_ref(v___x_3206_);
v_as_3200_ = v_tail_3205_;
goto _start;
}
else
{
lean_dec(v_tail_3205_);
return v___x_3206_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_registerEnumAttributes_spec__3___boxed(lean_object* v_as_3208_, lean_object* v___y_3209_){
_start:
{
lean_object* v_res_3210_; 
v_res_3210_ = l_List_forM___at___00Lean_registerEnumAttributes_spec__3(v_as_3208_);
return v_res_3210_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__1(lean_object* v_validate_3211_, lean_object* v_snd_3212_, lean_object* v_a_3213_, lean_object* v_fst_3214_, lean_object* v_decl_3215_, lean_object* v_stx_3216_, uint8_t v_kind_3217_, lean_object* v___y_3218_, lean_object* v___y_3219_){
_start:
{
lean_object* v___y_3222_; lean_object* v___y_3223_; lean_object* v___y_3258_; lean_object* v___y_3259_; lean_object* v___x_3264_; 
v___x_3264_ = l_Lean_Attribute_Builtin_ensureNoArgs(v_stx_3216_, v___y_3218_, v___y_3219_);
if (lean_obj_tag(v___x_3264_) == 0)
{
uint8_t v___x_3265_; uint8_t v___x_3266_; 
lean_dec_ref(v___x_3264_);
v___x_3265_ = 0;
v___x_3266_ = l_Lean_instBEqAttributeKind_beq(v_kind_3217_, v___x_3265_);
if (v___x_3266_ == 0)
{
lean_object* v___x_3267_; 
lean_dec(v_decl_3215_);
lean_dec_ref(v_a_3213_);
lean_dec(v_snd_3212_);
lean_dec_ref(v_validate_3211_);
v___x_3267_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg(v_fst_3214_, v_kind_3217_, v___y_3218_, v___y_3219_);
return v___x_3267_;
}
else
{
v___y_3258_ = v___y_3218_;
v___y_3259_ = v___y_3219_;
goto v___jp_3257_;
}
}
else
{
lean_dec(v_decl_3215_);
lean_dec(v_fst_3214_);
lean_dec_ref(v_a_3213_);
lean_dec(v_snd_3212_);
lean_dec_ref(v_validate_3211_);
return v___x_3264_;
}
v___jp_3221_:
{
lean_object* v___x_3224_; 
lean_inc(v___y_3223_);
lean_inc_ref(v___y_3222_);
lean_inc(v_snd_3212_);
lean_inc(v_decl_3215_);
v___x_3224_ = lean_apply_5(v_validate_3211_, v_decl_3215_, v_snd_3212_, v___y_3222_, v___y_3223_, lean_box(0));
if (lean_obj_tag(v___x_3224_) == 0)
{
lean_object* v___x_3226_; uint8_t v_isShared_3227_; uint8_t v_isSharedCheck_3255_; 
v_isSharedCheck_3255_ = !lean_is_exclusive(v___x_3224_);
if (v_isSharedCheck_3255_ == 0)
{
lean_object* v_unused_3256_; 
v_unused_3256_ = lean_ctor_get(v___x_3224_, 0);
lean_dec(v_unused_3256_);
v___x_3226_ = v___x_3224_;
v_isShared_3227_ = v_isSharedCheck_3255_;
goto v_resetjp_3225_;
}
else
{
lean_dec(v___x_3224_);
v___x_3226_ = lean_box(0);
v_isShared_3227_ = v_isSharedCheck_3255_;
goto v_resetjp_3225_;
}
v_resetjp_3225_:
{
lean_object* v___x_3228_; lean_object* v_toEnvExtension_3229_; lean_object* v_env_3230_; lean_object* v_nextMacroScope_3231_; lean_object* v_ngen_3232_; lean_object* v_auxDeclNGen_3233_; lean_object* v_traceState_3234_; lean_object* v_messages_3235_; lean_object* v_infoState_3236_; lean_object* v_snapshotTasks_3237_; lean_object* v___x_3239_; uint8_t v_isShared_3240_; uint8_t v_isSharedCheck_3253_; 
v___x_3228_ = lean_st_ref_take(v___y_3223_);
v_toEnvExtension_3229_ = lean_ctor_get(v_a_3213_, 0);
v_env_3230_ = lean_ctor_get(v___x_3228_, 0);
v_nextMacroScope_3231_ = lean_ctor_get(v___x_3228_, 1);
v_ngen_3232_ = lean_ctor_get(v___x_3228_, 2);
v_auxDeclNGen_3233_ = lean_ctor_get(v___x_3228_, 3);
v_traceState_3234_ = lean_ctor_get(v___x_3228_, 4);
v_messages_3235_ = lean_ctor_get(v___x_3228_, 6);
v_infoState_3236_ = lean_ctor_get(v___x_3228_, 7);
v_snapshotTasks_3237_ = lean_ctor_get(v___x_3228_, 8);
v_isSharedCheck_3253_ = !lean_is_exclusive(v___x_3228_);
if (v_isSharedCheck_3253_ == 0)
{
lean_object* v_unused_3254_; 
v_unused_3254_ = lean_ctor_get(v___x_3228_, 5);
lean_dec(v_unused_3254_);
v___x_3239_ = v___x_3228_;
v_isShared_3240_ = v_isSharedCheck_3253_;
goto v_resetjp_3238_;
}
else
{
lean_inc(v_snapshotTasks_3237_);
lean_inc(v_infoState_3236_);
lean_inc(v_messages_3235_);
lean_inc(v_traceState_3234_);
lean_inc(v_auxDeclNGen_3233_);
lean_inc(v_ngen_3232_);
lean_inc(v_nextMacroScope_3231_);
lean_inc(v_env_3230_);
lean_dec(v___x_3228_);
v___x_3239_ = lean_box(0);
v_isShared_3240_ = v_isSharedCheck_3253_;
goto v_resetjp_3238_;
}
v_resetjp_3238_:
{
lean_object* v_asyncMode_3241_; lean_object* v___x_3242_; lean_object* v___x_3243_; lean_object* v___x_3244_; lean_object* v___x_3246_; 
v_asyncMode_3241_ = lean_ctor_get(v_toEnvExtension_3229_, 2);
lean_inc(v_asyncMode_3241_);
lean_inc(v_decl_3215_);
v___x_3242_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3242_, 0, v_decl_3215_);
lean_ctor_set(v___x_3242_, 1, v_snd_3212_);
v___x_3243_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_a_3213_, v_env_3230_, v___x_3242_, v_asyncMode_3241_, v_decl_3215_);
lean_dec(v_asyncMode_3241_);
v___x_3244_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2);
if (v_isShared_3240_ == 0)
{
lean_ctor_set(v___x_3239_, 5, v___x_3244_);
lean_ctor_set(v___x_3239_, 0, v___x_3243_);
v___x_3246_ = v___x_3239_;
goto v_reusejp_3245_;
}
else
{
lean_object* v_reuseFailAlloc_3252_; 
v_reuseFailAlloc_3252_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3252_, 0, v___x_3243_);
lean_ctor_set(v_reuseFailAlloc_3252_, 1, v_nextMacroScope_3231_);
lean_ctor_set(v_reuseFailAlloc_3252_, 2, v_ngen_3232_);
lean_ctor_set(v_reuseFailAlloc_3252_, 3, v_auxDeclNGen_3233_);
lean_ctor_set(v_reuseFailAlloc_3252_, 4, v_traceState_3234_);
lean_ctor_set(v_reuseFailAlloc_3252_, 5, v___x_3244_);
lean_ctor_set(v_reuseFailAlloc_3252_, 6, v_messages_3235_);
lean_ctor_set(v_reuseFailAlloc_3252_, 7, v_infoState_3236_);
lean_ctor_set(v_reuseFailAlloc_3252_, 8, v_snapshotTasks_3237_);
v___x_3246_ = v_reuseFailAlloc_3252_;
goto v_reusejp_3245_;
}
v_reusejp_3245_:
{
lean_object* v___x_3247_; lean_object* v___x_3248_; lean_object* v___x_3250_; 
v___x_3247_ = lean_st_ref_set(v___y_3223_, v___x_3246_);
v___x_3248_ = lean_box(0);
if (v_isShared_3227_ == 0)
{
lean_ctor_set(v___x_3226_, 0, v___x_3248_);
v___x_3250_ = v___x_3226_;
goto v_reusejp_3249_;
}
else
{
lean_object* v_reuseFailAlloc_3251_; 
v_reuseFailAlloc_3251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3251_, 0, v___x_3248_);
v___x_3250_ = v_reuseFailAlloc_3251_;
goto v_reusejp_3249_;
}
v_reusejp_3249_:
{
return v___x_3250_;
}
}
}
}
}
else
{
lean_dec(v_decl_3215_);
lean_dec_ref(v_a_3213_);
lean_dec(v_snd_3212_);
return v___x_3224_;
}
}
v___jp_3257_:
{
lean_object* v___x_3260_; lean_object* v_env_3261_; lean_object* v___x_3262_; 
v___x_3260_ = lean_st_ref_get(v___y_3259_);
v_env_3261_ = lean_ctor_get(v___x_3260_, 0);
lean_inc_ref(v_env_3261_);
lean_dec(v___x_3260_);
v___x_3262_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3261_, v_decl_3215_);
lean_dec_ref(v_env_3261_);
if (lean_obj_tag(v___x_3262_) == 0)
{
lean_dec(v_fst_3214_);
v___y_3222_ = v___y_3258_;
v___y_3223_ = v___y_3259_;
goto v___jp_3221_;
}
else
{
lean_object* v___x_3263_; 
lean_dec_ref(v___x_3262_);
lean_dec_ref(v_a_3213_);
lean_dec(v_snd_3212_);
lean_dec_ref(v_validate_3211_);
v___x_3263_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg(v_fst_3214_, v_decl_3215_, v___y_3258_, v___y_3259_);
return v___x_3263_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__1___boxed(lean_object* v_validate_3268_, lean_object* v_snd_3269_, lean_object* v_a_3270_, lean_object* v_fst_3271_, lean_object* v_decl_3272_, lean_object* v_stx_3273_, lean_object* v_kind_3274_, lean_object* v___y_3275_, lean_object* v___y_3276_, lean_object* v___y_3277_){
_start:
{
uint8_t v_kind_boxed_3278_; lean_object* v_res_3279_; 
v_kind_boxed_3278_ = lean_unbox(v_kind_3274_);
v_res_3279_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__1(v_validate_3268_, v_snd_3269_, v_a_3270_, v_fst_3271_, v_decl_3272_, v_stx_3273_, v_kind_boxed_3278_, v___y_3275_, v___y_3276_);
lean_dec(v___y_3276_);
lean_dec_ref(v___y_3275_);
return v_res_3279_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__0(lean_object* v_fst_3280_, lean_object* v_decl_3281_, lean_object* v___y_3282_, lean_object* v___y_3283_){
_start:
{
lean_object* v___x_3285_; lean_object* v___x_3286_; lean_object* v___x_3287_; lean_object* v___x_3288_; lean_object* v___x_3289_; lean_object* v___x_3290_; 
v___x_3285_ = lean_obj_once(&l_Lean_registerTagAttribute___lam__6___closed__1, &l_Lean_registerTagAttribute___lam__6___closed__1_once, _init_l_Lean_registerTagAttribute___lam__6___closed__1);
v___x_3286_ = l_Lean_MessageData_ofName(v_fst_3280_);
v___x_3287_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3287_, 0, v___x_3285_);
lean_ctor_set(v___x_3287_, 1, v___x_3286_);
v___x_3288_ = lean_obj_once(&l_Lean_registerTagAttribute___lam__6___closed__3, &l_Lean_registerTagAttribute___lam__6___closed__3_once, _init_l_Lean_registerTagAttribute___lam__6___closed__3);
v___x_3289_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3289_, 0, v___x_3287_);
lean_ctor_set(v___x_3289_, 1, v___x_3288_);
v___x_3290_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0_spec__0___redArg(v___x_3289_, v___y_3282_, v___y_3283_);
return v___x_3290_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__0___boxed(lean_object* v_fst_3291_, lean_object* v_decl_3292_, lean_object* v___y_3293_, lean_object* v___y_3294_, lean_object* v___y_3295_){
_start:
{
lean_object* v_res_3296_; 
v_res_3296_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__0(v_fst_3291_, v_decl_3292_, v___y_3293_, v___y_3294_);
lean_dec(v___y_3294_);
lean_dec_ref(v___y_3293_);
lean_dec(v_decl_3292_);
return v_res_3296_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg(lean_object* v_validate_3297_, lean_object* v_a_3298_, lean_object* v_ref_3299_, uint8_t v_applicationTime_3300_, lean_object* v_a_3301_, lean_object* v_a_3302_){
_start:
{
if (lean_obj_tag(v_a_3301_) == 0)
{
lean_object* v___x_3303_; 
lean_dec(v_ref_3299_);
lean_dec_ref(v_a_3298_);
lean_dec_ref(v_validate_3297_);
v___x_3303_ = l_List_reverse___redArg(v_a_3302_);
return v___x_3303_;
}
else
{
lean_object* v_head_3304_; lean_object* v_snd_3305_; lean_object* v_tail_3306_; lean_object* v___x_3308_; uint8_t v_isShared_3309_; uint8_t v_isSharedCheck_3321_; 
v_head_3304_ = lean_ctor_get(v_a_3301_, 0);
lean_inc(v_head_3304_);
v_snd_3305_ = lean_ctor_get(v_head_3304_, 1);
lean_inc(v_snd_3305_);
v_tail_3306_ = lean_ctor_get(v_a_3301_, 1);
v_isSharedCheck_3321_ = !lean_is_exclusive(v_a_3301_);
if (v_isSharedCheck_3321_ == 0)
{
lean_object* v_unused_3322_; 
v_unused_3322_ = lean_ctor_get(v_a_3301_, 0);
lean_dec(v_unused_3322_);
v___x_3308_ = v_a_3301_;
v_isShared_3309_ = v_isSharedCheck_3321_;
goto v_resetjp_3307_;
}
else
{
lean_inc(v_tail_3306_);
lean_dec(v_a_3301_);
v___x_3308_ = lean_box(0);
v_isShared_3309_ = v_isSharedCheck_3321_;
goto v_resetjp_3307_;
}
v_resetjp_3307_:
{
lean_object* v_fst_3310_; lean_object* v_fst_3311_; lean_object* v_snd_3312_; lean_object* v___f_3313_; lean_object* v___f_3314_; lean_object* v___x_3315_; lean_object* v___x_3316_; lean_object* v___x_3318_; 
v_fst_3310_ = lean_ctor_get(v_head_3304_, 0);
lean_inc(v_fst_3310_);
lean_dec(v_head_3304_);
v_fst_3311_ = lean_ctor_get(v_snd_3305_, 0);
lean_inc(v_fst_3311_);
v_snd_3312_ = lean_ctor_get(v_snd_3305_, 1);
lean_inc(v_snd_3312_);
lean_dec(v_snd_3305_);
lean_inc(v_fst_3310_);
v___f_3313_ = lean_alloc_closure((void*)(l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__0___boxed), 5, 1);
lean_closure_set(v___f_3313_, 0, v_fst_3310_);
lean_inc(v_fst_3310_);
lean_inc_ref(v_a_3298_);
lean_inc_ref(v_validate_3297_);
v___f_3314_ = lean_alloc_closure((void*)(l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__1___boxed), 10, 4);
lean_closure_set(v___f_3314_, 0, v_validate_3297_);
lean_closure_set(v___f_3314_, 1, v_snd_3312_);
lean_closure_set(v___f_3314_, 2, v_a_3298_);
lean_closure_set(v___f_3314_, 3, v_fst_3310_);
lean_inc(v_ref_3299_);
v___x_3315_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_3315_, 0, v_ref_3299_);
lean_ctor_set(v___x_3315_, 1, v_fst_3310_);
lean_ctor_set(v___x_3315_, 2, v_fst_3311_);
lean_ctor_set_uint8(v___x_3315_, sizeof(void*)*3, v_applicationTime_3300_);
v___x_3316_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3316_, 0, v___x_3315_);
lean_ctor_set(v___x_3316_, 1, v___f_3314_);
lean_ctor_set(v___x_3316_, 2, v___f_3313_);
if (v_isShared_3309_ == 0)
{
lean_ctor_set(v___x_3308_, 1, v_a_3302_);
lean_ctor_set(v___x_3308_, 0, v___x_3316_);
v___x_3318_ = v___x_3308_;
goto v_reusejp_3317_;
}
else
{
lean_object* v_reuseFailAlloc_3320_; 
v_reuseFailAlloc_3320_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3320_, 0, v___x_3316_);
lean_ctor_set(v_reuseFailAlloc_3320_, 1, v_a_3302_);
v___x_3318_ = v_reuseFailAlloc_3320_;
goto v_reusejp_3317_;
}
v_reusejp_3317_:
{
v_a_3301_ = v_tail_3306_;
v_a_3302_ = v___x_3318_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___boxed(lean_object* v_validate_3323_, lean_object* v_a_3324_, lean_object* v_ref_3325_, lean_object* v_applicationTime_3326_, lean_object* v_a_3327_, lean_object* v_a_3328_){
_start:
{
uint8_t v_applicationTime_boxed_3329_; lean_object* v_res_3330_; 
v_applicationTime_boxed_3329_ = lean_unbox(v_applicationTime_3326_);
v_res_3330_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg(v_validate_3323_, v_a_3324_, v_ref_3325_, v_applicationTime_boxed_3329_, v_a_3327_, v_a_3328_);
return v_res_3330_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg(lean_object* v_attrDescrs_3344_, lean_object* v_validate_3345_, uint8_t v_applicationTime_3346_, lean_object* v_ref_3347_){
_start:
{
lean_object* v___f_3349_; lean_object* v___f_3350_; lean_object* v___f_3351_; lean_object* v___f_3352_; lean_object* v___f_3353_; lean_object* v___f_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; 
v___f_3349_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__0));
v___f_3350_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__2));
v___f_3351_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__3));
v___f_3352_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__4));
v___f_3353_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__5));
v___f_3354_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__6));
v___x_3355_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__7));
v___x_3356_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__8));
lean_inc(v_ref_3347_);
v___x_3357_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_3357_, 0, v_ref_3347_);
lean_ctor_set(v___x_3357_, 1, v___f_3353_);
lean_ctor_set(v___x_3357_, 2, v___f_3354_);
lean_ctor_set(v___x_3357_, 3, v___f_3352_);
lean_ctor_set(v___x_3357_, 4, v___f_3351_);
lean_ctor_set(v___x_3357_, 5, v___f_3350_);
lean_ctor_set(v___x_3357_, 6, v___x_3355_);
lean_ctor_set(v___x_3357_, 7, v___x_3356_);
v___x_3358_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3358_, 0, v___x_3357_);
lean_ctor_set(v___x_3358_, 1, v___f_3349_);
v___x_3359_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_3358_);
if (lean_obj_tag(v___x_3359_) == 0)
{
lean_object* v_a_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; 
v_a_3360_ = lean_ctor_get(v___x_3359_, 0);
lean_inc(v_a_3360_);
lean_dec_ref(v___x_3359_);
v___x_3361_ = lean_box(0);
lean_inc(v_a_3360_);
v___x_3362_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg(v_validate_3345_, v_a_3360_, v_ref_3347_, v_applicationTime_3346_, v_attrDescrs_3344_, v___x_3361_);
lean_inc(v___x_3362_);
v___x_3363_ = l_List_forM___at___00Lean_registerEnumAttributes_spec__3(v___x_3362_);
if (lean_obj_tag(v___x_3363_) == 0)
{
lean_object* v___x_3365_; uint8_t v_isShared_3366_; uint8_t v_isSharedCheck_3371_; 
v_isSharedCheck_3371_ = !lean_is_exclusive(v___x_3363_);
if (v_isSharedCheck_3371_ == 0)
{
lean_object* v_unused_3372_; 
v_unused_3372_ = lean_ctor_get(v___x_3363_, 0);
lean_dec(v_unused_3372_);
v___x_3365_ = v___x_3363_;
v_isShared_3366_ = v_isSharedCheck_3371_;
goto v_resetjp_3364_;
}
else
{
lean_dec(v___x_3363_);
v___x_3365_ = lean_box(0);
v_isShared_3366_ = v_isSharedCheck_3371_;
goto v_resetjp_3364_;
}
v_resetjp_3364_:
{
lean_object* v___x_3367_; lean_object* v___x_3369_; 
v___x_3367_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3367_, 0, v___x_3362_);
lean_ctor_set(v___x_3367_, 1, v_a_3360_);
if (v_isShared_3366_ == 0)
{
lean_ctor_set(v___x_3365_, 0, v___x_3367_);
v___x_3369_ = v___x_3365_;
goto v_reusejp_3368_;
}
else
{
lean_object* v_reuseFailAlloc_3370_; 
v_reuseFailAlloc_3370_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3370_, 0, v___x_3367_);
v___x_3369_ = v_reuseFailAlloc_3370_;
goto v_reusejp_3368_;
}
v_reusejp_3368_:
{
return v___x_3369_;
}
}
}
else
{
lean_object* v_a_3373_; lean_object* v___x_3375_; uint8_t v_isShared_3376_; uint8_t v_isSharedCheck_3380_; 
lean_dec(v___x_3362_);
lean_dec(v_a_3360_);
v_a_3373_ = lean_ctor_get(v___x_3363_, 0);
v_isSharedCheck_3380_ = !lean_is_exclusive(v___x_3363_);
if (v_isSharedCheck_3380_ == 0)
{
v___x_3375_ = v___x_3363_;
v_isShared_3376_ = v_isSharedCheck_3380_;
goto v_resetjp_3374_;
}
else
{
lean_inc(v_a_3373_);
lean_dec(v___x_3363_);
v___x_3375_ = lean_box(0);
v_isShared_3376_ = v_isSharedCheck_3380_;
goto v_resetjp_3374_;
}
v_resetjp_3374_:
{
lean_object* v___x_3378_; 
if (v_isShared_3376_ == 0)
{
v___x_3378_ = v___x_3375_;
goto v_reusejp_3377_;
}
else
{
lean_object* v_reuseFailAlloc_3379_; 
v_reuseFailAlloc_3379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3379_, 0, v_a_3373_);
v___x_3378_ = v_reuseFailAlloc_3379_;
goto v_reusejp_3377_;
}
v_reusejp_3377_:
{
return v___x_3378_;
}
}
}
}
else
{
lean_object* v_a_3381_; lean_object* v___x_3383_; uint8_t v_isShared_3384_; uint8_t v_isSharedCheck_3388_; 
lean_dec(v_ref_3347_);
lean_dec_ref(v_validate_3345_);
lean_dec(v_attrDescrs_3344_);
v_a_3381_ = lean_ctor_get(v___x_3359_, 0);
v_isSharedCheck_3388_ = !lean_is_exclusive(v___x_3359_);
if (v_isSharedCheck_3388_ == 0)
{
v___x_3383_ = v___x_3359_;
v_isShared_3384_ = v_isSharedCheck_3388_;
goto v_resetjp_3382_;
}
else
{
lean_inc(v_a_3381_);
lean_dec(v___x_3359_);
v___x_3383_ = lean_box(0);
v_isShared_3384_ = v_isSharedCheck_3388_;
goto v_resetjp_3382_;
}
v_resetjp_3382_:
{
lean_object* v___x_3386_; 
if (v_isShared_3384_ == 0)
{
v___x_3386_ = v___x_3383_;
goto v_reusejp_3385_;
}
else
{
lean_object* v_reuseFailAlloc_3387_; 
v_reuseFailAlloc_3387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3387_, 0, v_a_3381_);
v___x_3386_ = v_reuseFailAlloc_3387_;
goto v_reusejp_3385_;
}
v_reusejp_3385_:
{
return v___x_3386_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___boxed(lean_object* v_attrDescrs_3389_, lean_object* v_validate_3390_, lean_object* v_applicationTime_3391_, lean_object* v_ref_3392_, lean_object* v_a_3393_){
_start:
{
uint8_t v_applicationTime_boxed_3394_; lean_object* v_res_3395_; 
v_applicationTime_boxed_3394_ = lean_unbox(v_applicationTime_3391_);
v_res_3395_ = l_Lean_registerEnumAttributes___redArg(v_attrDescrs_3389_, v_validate_3390_, v_applicationTime_boxed_3394_, v_ref_3392_);
return v_res_3395_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes(lean_object* v_00_u03b1_3396_, lean_object* v_attrDescrs_3397_, lean_object* v_validate_3398_, uint8_t v_applicationTime_3399_, lean_object* v_ref_3400_){
_start:
{
lean_object* v___x_3402_; 
v___x_3402_ = l_Lean_registerEnumAttributes___redArg(v_attrDescrs_3397_, v_validate_3398_, v_applicationTime_3399_, v_ref_3400_);
return v___x_3402_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___boxed(lean_object* v_00_u03b1_3403_, lean_object* v_attrDescrs_3404_, lean_object* v_validate_3405_, lean_object* v_applicationTime_3406_, lean_object* v_ref_3407_, lean_object* v_a_3408_){
_start:
{
uint8_t v_applicationTime_boxed_3409_; lean_object* v_res_3410_; 
v_applicationTime_boxed_3409_ = lean_unbox(v_applicationTime_3406_);
v_res_3410_ = l_Lean_registerEnumAttributes(v_00_u03b1_3403_, v_attrDescrs_3404_, v_validate_3405_, v_applicationTime_boxed_3409_, v_ref_3407_);
return v_res_3410_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0(lean_object* v_00_u03b1_3411_, lean_object* v_env_3412_, lean_object* v_as_3413_, size_t v_i_3414_, size_t v_stop_3415_, lean_object* v_b_3416_){
_start:
{
lean_object* v___x_3417_; 
v___x_3417_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg(v_env_3412_, v_as_3413_, v_i_3414_, v_stop_3415_, v_b_3416_);
return v___x_3417_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___boxed(lean_object* v_00_u03b1_3418_, lean_object* v_env_3419_, lean_object* v_as_3420_, lean_object* v_i_3421_, lean_object* v_stop_3422_, lean_object* v_b_3423_){
_start:
{
size_t v_i_boxed_3424_; size_t v_stop_boxed_3425_; lean_object* v_res_3426_; 
v_i_boxed_3424_ = lean_unbox_usize(v_i_3421_);
lean_dec(v_i_3421_);
v_stop_boxed_3425_ = lean_unbox_usize(v_stop_3422_);
lean_dec(v_stop_3422_);
v_res_3426_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0(v_00_u03b1_3418_, v_env_3419_, v_as_3420_, v_i_boxed_3424_, v_stop_boxed_3425_, v_b_3423_);
lean_dec_ref(v_as_3420_);
return v_res_3426_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerEnumAttributes_spec__1(lean_object* v_00_u03b1_3427_, lean_object* v_newState_3428_, lean_object* v_x_3429_, lean_object* v_x_3430_){
_start:
{
lean_object* v___x_3431_; 
v___x_3431_ = l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___redArg(v_newState_3428_, v_x_3429_, v_x_3430_);
return v___x_3431_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___boxed(lean_object* v_00_u03b1_3432_, lean_object* v_newState_3433_, lean_object* v_x_3434_, lean_object* v_x_3435_){
_start:
{
lean_object* v_res_3436_; 
v_res_3436_ = l_List_foldl___at___00Lean_registerEnumAttributes_spec__1(v_00_u03b1_3432_, v_newState_3433_, v_x_3434_, v_x_3435_);
lean_dec(v_newState_3433_);
return v_res_3436_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2(lean_object* v_00_u03b1_3437_, lean_object* v_validate_3438_, lean_object* v_a_3439_, lean_object* v_ref_3440_, uint8_t v_applicationTime_3441_, lean_object* v_a_3442_, lean_object* v_a_3443_){
_start:
{
lean_object* v___x_3444_; 
v___x_3444_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg(v_validate_3438_, v_a_3439_, v_ref_3440_, v_applicationTime_3441_, v_a_3442_, v_a_3443_);
return v___x_3444_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___boxed(lean_object* v_00_u03b1_3445_, lean_object* v_validate_3446_, lean_object* v_a_3447_, lean_object* v_ref_3448_, lean_object* v_applicationTime_3449_, lean_object* v_a_3450_, lean_object* v_a_3451_){
_start:
{
uint8_t v_applicationTime_boxed_3452_; lean_object* v_res_3453_; 
v_applicationTime_boxed_3452_ = lean_unbox(v_applicationTime_3449_);
v_res_3453_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2(v_00_u03b1_3445_, v_validate_3446_, v_a_3447_, v_ref_3448_, v_applicationTime_boxed_3452_, v_a_3450_, v_a_3451_);
return v_res_3453_;
}
}
LEAN_EXPORT lean_object* l_Lean_EnumAttributes_getValue___redArg(lean_object* v_inst_3454_, lean_object* v_attr_3455_, lean_object* v_env_3456_, lean_object* v_decl_3457_){
_start:
{
lean_object* v___x_3458_; lean_object* v___x_3459_; 
v___x_3458_ = lean_box(1);
v___x_3459_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3456_, v_decl_3457_);
if (lean_obj_tag(v___x_3459_) == 0)
{
lean_object* v_ext_3460_; lean_object* v_toEnvExtension_3461_; lean_object* v_asyncMode_3462_; lean_object* v___x_3463_; lean_object* v___x_3464_; 
lean_dec(v_inst_3454_);
v_ext_3460_ = lean_ctor_get(v_attr_3455_, 1);
lean_inc_ref(v_ext_3460_);
lean_dec_ref(v_attr_3455_);
v_toEnvExtension_3461_ = lean_ctor_get(v_ext_3460_, 0);
v_asyncMode_3462_ = lean_ctor_get(v_toEnvExtension_3461_, 2);
lean_inc(v_asyncMode_3462_);
lean_inc(v_decl_3457_);
v___x_3463_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3458_, v_ext_3460_, v_env_3456_, v_asyncMode_3462_, v_decl_3457_);
lean_dec(v_asyncMode_3462_);
lean_dec_ref(v_ext_3460_);
v___x_3464_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_3463_, v_decl_3457_);
lean_dec(v_decl_3457_);
lean_dec(v___x_3463_);
return v___x_3464_;
}
else
{
lean_object* v_val_3465_; lean_object* v_ext_3466_; lean_object* v___x_3468_; uint8_t v_isShared_3469_; uint8_t v_isSharedCheck_3496_; 
v_val_3465_ = lean_ctor_get(v___x_3459_, 0);
lean_inc(v_val_3465_);
lean_dec_ref(v___x_3459_);
v_ext_3466_ = lean_ctor_get(v_attr_3455_, 1);
v_isSharedCheck_3496_ = !lean_is_exclusive(v_attr_3455_);
if (v_isSharedCheck_3496_ == 0)
{
lean_object* v_unused_3497_; 
v_unused_3497_ = lean_ctor_get(v_attr_3455_, 0);
lean_dec(v_unused_3497_);
v___x_3468_ = v_attr_3455_;
v_isShared_3469_ = v_isSharedCheck_3496_;
goto v_resetjp_3467_;
}
else
{
lean_inc(v_ext_3466_);
lean_dec(v_attr_3455_);
v___x_3468_ = lean_box(0);
v_isShared_3469_ = v_isSharedCheck_3496_;
goto v_resetjp_3467_;
}
v_resetjp_3467_:
{
uint8_t v___x_3470_; lean_object* v___x_3471_; lean_object* v___x_3472_; lean_object* v___x_3473_; uint8_t v___x_3474_; 
v___x_3470_ = 0;
v___x_3471_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_3458_, v_ext_3466_, v_env_3456_, v_val_3465_, v___x_3470_);
lean_dec(v_val_3465_);
lean_dec_ref(v_env_3456_);
lean_dec_ref(v_ext_3466_);
v___x_3472_ = lean_unsigned_to_nat(0u);
v___x_3473_ = lean_array_get_size(v___x_3471_);
v___x_3474_ = lean_nat_dec_lt(v___x_3472_, v___x_3473_);
if (v___x_3474_ == 0)
{
lean_object* v___x_3475_; 
lean_dec_ref(v___x_3471_);
lean_del_object(v___x_3468_);
lean_dec(v_decl_3457_);
lean_dec(v_inst_3454_);
v___x_3475_ = lean_box(0);
return v___x_3475_;
}
else
{
lean_object* v___x_3476_; lean_object* v___x_3477_; uint8_t v___x_3478_; 
v___x_3476_ = lean_unsigned_to_nat(1u);
v___x_3477_ = lean_nat_sub(v___x_3473_, v___x_3476_);
v___x_3478_ = lean_nat_dec_le(v___x_3472_, v___x_3477_);
if (v___x_3478_ == 0)
{
lean_object* v___x_3479_; 
lean_dec(v___x_3477_);
lean_dec_ref(v___x_3471_);
lean_del_object(v___x_3468_);
lean_dec(v_decl_3457_);
lean_dec(v_inst_3454_);
v___x_3479_ = lean_box(0);
return v___x_3479_;
}
else
{
lean_object* v___f_3480_; lean_object* v___x_3482_; 
v___f_3480_ = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2___redArg___closed__0));
if (v_isShared_3469_ == 0)
{
lean_ctor_set(v___x_3468_, 1, v_inst_3454_);
lean_ctor_set(v___x_3468_, 0, v_decl_3457_);
v___x_3482_ = v___x_3468_;
goto v_reusejp_3481_;
}
else
{
lean_object* v_reuseFailAlloc_3495_; 
v_reuseFailAlloc_3495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3495_, 0, v_decl_3457_);
lean_ctor_set(v_reuseFailAlloc_3495_, 1, v_inst_3454_);
v___x_3482_ = v_reuseFailAlloc_3495_;
goto v_reusejp_3481_;
}
v_reusejp_3481_:
{
lean_object* v___x_3483_; lean_object* v___x_3484_; 
v___x_3483_ = ((lean_object*)(l_Lean_ParametricAttribute_getParam_x3f___redArg___closed__1));
v___x_3484_ = l_Array_binSearchAux___redArg(v___f_3480_, v___x_3483_, v___x_3471_, v___x_3482_, v___x_3472_, v___x_3477_);
lean_dec_ref(v___x_3471_);
if (lean_obj_tag(v___x_3484_) == 0)
{
lean_object* v___x_3485_; 
v___x_3485_ = lean_box(0);
return v___x_3485_;
}
else
{
lean_object* v_val_3486_; lean_object* v___x_3488_; uint8_t v_isShared_3489_; uint8_t v_isSharedCheck_3494_; 
v_val_3486_ = lean_ctor_get(v___x_3484_, 0);
v_isSharedCheck_3494_ = !lean_is_exclusive(v___x_3484_);
if (v_isSharedCheck_3494_ == 0)
{
v___x_3488_ = v___x_3484_;
v_isShared_3489_ = v_isSharedCheck_3494_;
goto v_resetjp_3487_;
}
else
{
lean_inc(v_val_3486_);
lean_dec(v___x_3484_);
v___x_3488_ = lean_box(0);
v_isShared_3489_ = v_isSharedCheck_3494_;
goto v_resetjp_3487_;
}
v_resetjp_3487_:
{
lean_object* v_snd_3490_; lean_object* v___x_3492_; 
v_snd_3490_ = lean_ctor_get(v_val_3486_, 1);
lean_inc(v_snd_3490_);
lean_dec(v_val_3486_);
if (v_isShared_3489_ == 0)
{
lean_ctor_set(v___x_3488_, 0, v_snd_3490_);
v___x_3492_ = v___x_3488_;
goto v_reusejp_3491_;
}
else
{
lean_object* v_reuseFailAlloc_3493_; 
v_reuseFailAlloc_3493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3493_, 0, v_snd_3490_);
v___x_3492_ = v_reuseFailAlloc_3493_;
goto v_reusejp_3491_;
}
v_reusejp_3491_:
{
return v___x_3492_;
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
LEAN_EXPORT lean_object* l_Lean_EnumAttributes_getValue(lean_object* v_00_u03b1_3498_, lean_object* v_inst_3499_, lean_object* v_attr_3500_, lean_object* v_env_3501_, lean_object* v_decl_3502_){
_start:
{
lean_object* v___x_3503_; 
v___x_3503_ = l_Lean_EnumAttributes_getValue___redArg(v_inst_3499_, v_attr_3500_, v_env_3501_, v_decl_3502_);
return v___x_3503_;
}
}
LEAN_EXPORT lean_object* l_Lean_EnumAttributes_setValue___redArg(lean_object* v_attrs_3512_, lean_object* v_env_3513_, lean_object* v_decl_3514_, lean_object* v_val_3515_){
_start:
{
lean_object* v_ext_3516_; lean_object* v___x_3518_; uint8_t v_isShared_3519_; uint8_t v_isSharedCheck_3580_; 
v_ext_3516_ = lean_ctor_get(v_attrs_3512_, 1);
v_isSharedCheck_3580_ = !lean_is_exclusive(v_attrs_3512_);
if (v_isSharedCheck_3580_ == 0)
{
lean_object* v_unused_3581_; 
v_unused_3581_ = lean_ctor_get(v_attrs_3512_, 0);
lean_dec(v_unused_3581_);
v___x_3518_ = v_attrs_3512_;
v_isShared_3519_ = v_isSharedCheck_3580_;
goto v_resetjp_3517_;
}
else
{
lean_inc(v_ext_3516_);
lean_dec(v_attrs_3512_);
v___x_3518_ = lean_box(0);
v_isShared_3519_ = v_isSharedCheck_3580_;
goto v_resetjp_3517_;
}
v_resetjp_3517_:
{
lean_object* v_toEnvExtension_3520_; lean_object* v_name_3521_; lean_object* v___x_3522_; uint8_t v___x_3523_; lean_object* v___x_3524_; lean_object* v___x_3525_; lean_object* v___x_3526_; lean_object* v___x_3527_; lean_object* v___x_3528_; lean_object* v___x_3529_; lean_object* v___x_3530_; lean_object* v_pfx_3531_; lean_object* v___x_3532_; 
v_toEnvExtension_3520_ = lean_ctor_get(v_ext_3516_, 0);
v_name_3521_ = lean_ctor_get(v_ext_3516_, 1);
v___x_3522_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__0));
v___x_3523_ = 1;
lean_inc(v_name_3521_);
v___x_3524_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_3521_, v___x_3523_);
v___x_3525_ = lean_string_append(v___x_3522_, v___x_3524_);
lean_dec_ref(v___x_3524_);
v___x_3526_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__1));
v___x_3527_ = lean_string_append(v___x_3525_, v___x_3526_);
lean_inc(v_decl_3514_);
v___x_3528_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_decl_3514_, v___x_3523_);
v___x_3529_ = lean_string_append(v___x_3527_, v___x_3528_);
lean_dec_ref(v___x_3528_);
v___x_3530_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__4));
v_pfx_3531_ = lean_string_append(v___x_3529_, v___x_3530_);
v___x_3532_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3513_, v_decl_3514_);
if (lean_obj_tag(v___x_3532_) == 0)
{
lean_object* v_asyncMode_3533_; uint8_t v___x_3540_; 
v_asyncMode_3533_ = lean_ctor_get(v_toEnvExtension_3520_, 2);
lean_inc(v_asyncMode_3533_);
lean_inc(v_decl_3514_);
lean_inc_ref(v_env_3513_);
v___x_3540_ = l_Lean_EnvExtension_asyncMayModify___redArg(v_env_3513_, v_decl_3514_, v_asyncMode_3533_);
if (v___x_3540_ == 0)
{
lean_object* v___x_3541_; lean_object* v___x_3542_; lean_object* v___y_3544_; lean_object* v___x_3548_; 
lean_dec(v_asyncMode_3533_);
lean_del_object(v___x_3518_);
lean_dec_ref(v_ext_3516_);
lean_dec(v_val_3515_);
lean_dec(v_decl_3514_);
v___x_3541_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__2));
v___x_3542_ = lean_string_append(v_pfx_3531_, v___x_3541_);
v___x_3548_ = l_Lean_Environment_asyncPrefix_x3f(v_env_3513_);
if (lean_obj_tag(v___x_3548_) == 0)
{
lean_object* v___x_3549_; 
v___x_3549_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__3));
v___y_3544_ = v___x_3549_;
goto v___jp_3543_;
}
else
{
lean_object* v_val_3550_; lean_object* v___x_3551_; lean_object* v___x_3552_; lean_object* v___x_3553_; lean_object* v___x_3554_; lean_object* v___x_3555_; lean_object* v___x_3556_; 
v_val_3550_ = lean_ctor_get(v___x_3548_, 0);
lean_inc(v_val_3550_);
lean_dec_ref(v___x_3548_);
v___x_3551_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__4));
v___x_3552_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_val_3550_, v___x_3523_);
v___x_3553_ = l_addParenHeuristic(v___x_3552_);
v___x_3554_ = lean_string_append(v___x_3551_, v___x_3553_);
lean_dec_ref(v___x_3553_);
v___x_3555_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__5));
v___x_3556_ = lean_string_append(v___x_3554_, v___x_3555_);
v___y_3544_ = v___x_3556_;
goto v___jp_3543_;
}
v___jp_3543_:
{
lean_object* v___x_3545_; lean_object* v___x_3546_; lean_object* v___x_3547_; 
v___x_3545_ = lean_string_append(v___x_3542_, v___y_3544_);
lean_dec_ref(v___y_3544_);
v___x_3546_ = lean_string_append(v___x_3545_, v___x_3530_);
v___x_3547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3547_, 0, v___x_3546_);
return v___x_3547_;
}
}
else
{
lean_object* v___x_3557_; lean_object* v___x_3558_; lean_object* v___x_3559_; 
v___x_3557_ = lean_box(1);
lean_inc(v_decl_3514_);
lean_inc_ref(v_env_3513_);
v___x_3558_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3557_, v_ext_3516_, v_env_3513_, v_asyncMode_3533_, v_decl_3514_);
v___x_3559_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_3558_, v_decl_3514_);
lean_dec(v___x_3558_);
if (lean_obj_tag(v___x_3559_) == 0)
{
lean_dec_ref(v_pfx_3531_);
goto v___jp_3534_;
}
else
{
lean_object* v___x_3561_; uint8_t v_isShared_3562_; uint8_t v_isSharedCheck_3568_; 
v_isSharedCheck_3568_ = !lean_is_exclusive(v___x_3559_);
if (v_isSharedCheck_3568_ == 0)
{
lean_object* v_unused_3569_; 
v_unused_3569_ = lean_ctor_get(v___x_3559_, 0);
lean_dec(v_unused_3569_);
v___x_3561_ = v___x_3559_;
v_isShared_3562_ = v_isSharedCheck_3568_;
goto v_resetjp_3560_;
}
else
{
lean_dec(v___x_3559_);
v___x_3561_ = lean_box(0);
v_isShared_3562_ = v_isSharedCheck_3568_;
goto v_resetjp_3560_;
}
v_resetjp_3560_:
{
if (v___x_3540_ == 0)
{
lean_del_object(v___x_3561_);
lean_dec_ref(v_pfx_3531_);
goto v___jp_3534_;
}
else
{
lean_object* v___x_3563_; lean_object* v___x_3564_; lean_object* v___x_3566_; 
lean_dec(v_asyncMode_3533_);
lean_del_object(v___x_3518_);
lean_dec_ref(v_ext_3516_);
lean_dec(v_val_3515_);
lean_dec(v_decl_3514_);
lean_dec_ref(v_env_3513_);
v___x_3563_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__6));
v___x_3564_ = lean_string_append(v_pfx_3531_, v___x_3563_);
if (v_isShared_3562_ == 0)
{
lean_ctor_set_tag(v___x_3561_, 0);
lean_ctor_set(v___x_3561_, 0, v___x_3564_);
v___x_3566_ = v___x_3561_;
goto v_reusejp_3565_;
}
else
{
lean_object* v_reuseFailAlloc_3567_; 
v_reuseFailAlloc_3567_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3567_, 0, v___x_3564_);
v___x_3566_ = v_reuseFailAlloc_3567_;
goto v_reusejp_3565_;
}
v_reusejp_3565_:
{
return v___x_3566_;
}
}
}
}
}
v___jp_3534_:
{
lean_object* v___x_3536_; 
lean_inc(v_decl_3514_);
if (v_isShared_3519_ == 0)
{
lean_ctor_set(v___x_3518_, 1, v_val_3515_);
lean_ctor_set(v___x_3518_, 0, v_decl_3514_);
v___x_3536_ = v___x_3518_;
goto v_reusejp_3535_;
}
else
{
lean_object* v_reuseFailAlloc_3539_; 
v_reuseFailAlloc_3539_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3539_, 0, v_decl_3514_);
lean_ctor_set(v_reuseFailAlloc_3539_, 1, v_val_3515_);
v___x_3536_ = v_reuseFailAlloc_3539_;
goto v_reusejp_3535_;
}
v_reusejp_3535_:
{
lean_object* v___x_3537_; lean_object* v___x_3538_; 
v___x_3537_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_ext_3516_, v_env_3513_, v___x_3536_, v_asyncMode_3533_, v_decl_3514_);
lean_dec(v_asyncMode_3533_);
v___x_3538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3538_, 0, v___x_3537_);
return v___x_3538_;
}
}
}
else
{
lean_object* v___x_3571_; uint8_t v_isShared_3572_; uint8_t v_isSharedCheck_3578_; 
lean_del_object(v___x_3518_);
lean_dec_ref(v_ext_3516_);
lean_dec(v_val_3515_);
lean_dec(v_decl_3514_);
lean_dec_ref(v_env_3513_);
v_isSharedCheck_3578_ = !lean_is_exclusive(v___x_3532_);
if (v_isSharedCheck_3578_ == 0)
{
lean_object* v_unused_3579_; 
v_unused_3579_ = lean_ctor_get(v___x_3532_, 0);
lean_dec(v_unused_3579_);
v___x_3571_ = v___x_3532_;
v_isShared_3572_ = v_isSharedCheck_3578_;
goto v_resetjp_3570_;
}
else
{
lean_dec(v___x_3532_);
v___x_3571_ = lean_box(0);
v_isShared_3572_ = v_isSharedCheck_3578_;
goto v_resetjp_3570_;
}
v_resetjp_3570_:
{
lean_object* v___x_3573_; lean_object* v___x_3574_; lean_object* v___x_3576_; 
v___x_3573_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__7));
v___x_3574_ = lean_string_append(v_pfx_3531_, v___x_3573_);
if (v_isShared_3572_ == 0)
{
lean_ctor_set_tag(v___x_3571_, 0);
lean_ctor_set(v___x_3571_, 0, v___x_3574_);
v___x_3576_ = v___x_3571_;
goto v_reusejp_3575_;
}
else
{
lean_object* v_reuseFailAlloc_3577_; 
v_reuseFailAlloc_3577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3577_, 0, v___x_3574_);
v___x_3576_ = v_reuseFailAlloc_3577_;
goto v_reusejp_3575_;
}
v_reusejp_3575_:
{
return v___x_3576_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_EnumAttributes_setValue(lean_object* v_00_u03b1_3582_, lean_object* v_attrs_3583_, lean_object* v_env_3584_, lean_object* v_decl_3585_, lean_object* v_val_3586_){
_start:
{
lean_object* v___x_3587_; 
v___x_3587_ = l_Lean_EnumAttributes_setValue___redArg(v_attrs_3583_, v_env_3584_, v_decl_3585_, v_val_3586_);
return v___x_3587_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_Attributes_2990505691____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3589_; lean_object* v___x_3590_; lean_object* v___x_3591_; 
v___x_3589_ = lean_obj_once(&l_Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_, &l_Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2__once, _init_l_Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_);
v___x_3590_ = lean_st_mk_ref(v___x_3589_);
v___x_3591_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3591_, 0, v___x_3590_);
return v___x_3591_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_Attributes_2990505691____hygCtx___hyg_2____boxed(lean_object* v_a_3592_){
_start:
{
lean_object* v_res_3593_; 
v_res_3593_ = l_Lean_initFn_00___x40_Lean_Attributes_2990505691____hygCtx___hyg_2_();
return v_res_3593_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerAttributeImplBuilder(lean_object* v_builderId_3596_, lean_object* v_builder_3597_){
_start:
{
lean_object* v___x_3599_; lean_object* v___x_3600_; uint8_t v___x_3601_; 
v___x_3599_ = l_Lean_attributeImplBuilderTableRef;
v___x_3600_ = lean_st_ref_get(v___x_3599_);
v___x_3601_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(v___x_3600_, v_builderId_3596_);
lean_dec(v___x_3600_);
if (v___x_3601_ == 0)
{
lean_object* v___x_3602_; lean_object* v___x_3603_; lean_object* v___x_3604_; lean_object* v___x_3605_; 
v___x_3602_ = lean_st_ref_take(v___x_3599_);
v___x_3603_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1___redArg(v___x_3602_, v_builderId_3596_, v_builder_3597_);
v___x_3604_ = lean_st_ref_set(v___x_3599_, v___x_3603_);
v___x_3605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3605_, 0, v___x_3604_);
return v___x_3605_;
}
else
{
lean_object* v___x_3606_; lean_object* v___x_3607_; lean_object* v___x_3608_; lean_object* v___x_3609_; lean_object* v___x_3610_; lean_object* v___x_3611_; lean_object* v___x_3612_; 
lean_dec_ref(v_builder_3597_);
v___x_3606_ = ((lean_object*)(l_Lean_registerAttributeImplBuilder___closed__0));
v___x_3607_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_builderId_3596_, v___x_3601_);
v___x_3608_ = lean_string_append(v___x_3606_, v___x_3607_);
lean_dec_ref(v___x_3607_);
v___x_3609_ = ((lean_object*)(l_Lean_registerAttributeImplBuilder___closed__1));
v___x_3610_ = lean_string_append(v___x_3608_, v___x_3609_);
v___x_3611_ = lean_mk_io_user_error(v___x_3610_);
v___x_3612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3612_, 0, v___x_3611_);
return v___x_3612_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerAttributeImplBuilder___boxed(lean_object* v_builderId_3613_, lean_object* v_builder_3614_, lean_object* v_a_3615_){
_start:
{
lean_object* v_res_3616_; 
v_res_3616_ = l_Lean_registerAttributeImplBuilder(v_builderId_3613_, v_builder_3614_);
return v_res_3616_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___redArg(lean_object* v_e_3617_){
_start:
{
if (lean_obj_tag(v_e_3617_) == 0)
{
lean_object* v_a_3619_; lean_object* v___x_3621_; uint8_t v_isShared_3622_; uint8_t v_isSharedCheck_3627_; 
v_a_3619_ = lean_ctor_get(v_e_3617_, 0);
v_isSharedCheck_3627_ = !lean_is_exclusive(v_e_3617_);
if (v_isSharedCheck_3627_ == 0)
{
v___x_3621_ = v_e_3617_;
v_isShared_3622_ = v_isSharedCheck_3627_;
goto v_resetjp_3620_;
}
else
{
lean_inc(v_a_3619_);
lean_dec(v_e_3617_);
v___x_3621_ = lean_box(0);
v_isShared_3622_ = v_isSharedCheck_3627_;
goto v_resetjp_3620_;
}
v_resetjp_3620_:
{
lean_object* v___x_3623_; lean_object* v___x_3625_; 
v___x_3623_ = lean_mk_io_user_error(v_a_3619_);
if (v_isShared_3622_ == 0)
{
lean_ctor_set_tag(v___x_3621_, 1);
lean_ctor_set(v___x_3621_, 0, v___x_3623_);
v___x_3625_ = v___x_3621_;
goto v_reusejp_3624_;
}
else
{
lean_object* v_reuseFailAlloc_3626_; 
v_reuseFailAlloc_3626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3626_, 0, v___x_3623_);
v___x_3625_ = v_reuseFailAlloc_3626_;
goto v_reusejp_3624_;
}
v_reusejp_3624_:
{
return v___x_3625_;
}
}
}
else
{
lean_object* v_a_3628_; lean_object* v___x_3630_; uint8_t v_isShared_3631_; uint8_t v_isSharedCheck_3635_; 
v_a_3628_ = lean_ctor_get(v_e_3617_, 0);
v_isSharedCheck_3635_ = !lean_is_exclusive(v_e_3617_);
if (v_isSharedCheck_3635_ == 0)
{
v___x_3630_ = v_e_3617_;
v_isShared_3631_ = v_isSharedCheck_3635_;
goto v_resetjp_3629_;
}
else
{
lean_inc(v_a_3628_);
lean_dec(v_e_3617_);
v___x_3630_ = lean_box(0);
v_isShared_3631_ = v_isSharedCheck_3635_;
goto v_resetjp_3629_;
}
v_resetjp_3629_:
{
lean_object* v___x_3633_; 
if (v_isShared_3631_ == 0)
{
lean_ctor_set_tag(v___x_3630_, 0);
v___x_3633_ = v___x_3630_;
goto v_reusejp_3632_;
}
else
{
lean_object* v_reuseFailAlloc_3634_; 
v_reuseFailAlloc_3634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3634_, 0, v_a_3628_);
v___x_3633_ = v_reuseFailAlloc_3634_;
goto v_reusejp_3632_;
}
v_reusejp_3632_:
{
return v___x_3633_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___redArg___boxed(lean_object* v_e_3636_, lean_object* v_a_3637_){
_start:
{
lean_object* v_res_3638_; 
v_res_3638_ = l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___redArg(v_e_3636_);
return v_res_3638_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1(lean_object* v_00_u03b1_3639_, lean_object* v_e_3640_){
_start:
{
lean_object* v___x_3642_; 
v___x_3642_ = l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___redArg(v_e_3640_);
return v___x_3642_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___boxed(lean_object* v_00_u03b1_3643_, lean_object* v_e_3644_, lean_object* v_a_3645_){
_start:
{
lean_object* v_res_3646_; 
v_res_3646_ = l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1(v_00_u03b1_3643_, v_e_3644_);
return v_res_3646_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___redArg(lean_object* v_a_3647_, lean_object* v_x_3648_){
_start:
{
if (lean_obj_tag(v_x_3648_) == 0)
{
lean_object* v___x_3649_; 
v___x_3649_ = lean_box(0);
return v___x_3649_;
}
else
{
lean_object* v_key_3650_; lean_object* v_value_3651_; lean_object* v_tail_3652_; uint8_t v___x_3653_; 
v_key_3650_ = lean_ctor_get(v_x_3648_, 0);
v_value_3651_ = lean_ctor_get(v_x_3648_, 1);
v_tail_3652_ = lean_ctor_get(v_x_3648_, 2);
v___x_3653_ = lean_name_eq(v_key_3650_, v_a_3647_);
if (v___x_3653_ == 0)
{
v_x_3648_ = v_tail_3652_;
goto _start;
}
else
{
lean_object* v___x_3655_; 
lean_inc(v_value_3651_);
v___x_3655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3655_, 0, v_value_3651_);
return v___x_3655_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___redArg___boxed(lean_object* v_a_3656_, lean_object* v_x_3657_){
_start:
{
lean_object* v_res_3658_; 
v_res_3658_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___redArg(v_a_3656_, v_x_3657_);
lean_dec(v_x_3657_);
lean_dec(v_a_3656_);
return v_res_3658_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(lean_object* v_m_3659_, lean_object* v_a_3660_){
_start:
{
lean_object* v_buckets_3661_; lean_object* v___x_3662_; uint64_t v___y_3664_; 
v_buckets_3661_ = lean_ctor_get(v_m_3659_, 1);
v___x_3662_ = lean_array_get_size(v_buckets_3661_);
if (lean_obj_tag(v_a_3660_) == 0)
{
uint64_t v___x_3678_; 
v___x_3678_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg___closed__0);
v___y_3664_ = v___x_3678_;
goto v___jp_3663_;
}
else
{
uint64_t v_hash_3679_; 
v_hash_3679_ = lean_ctor_get_uint64(v_a_3660_, sizeof(void*)*2);
v___y_3664_ = v_hash_3679_;
goto v___jp_3663_;
}
v___jp_3663_:
{
uint64_t v___x_3665_; uint64_t v___x_3666_; uint64_t v_fold_3667_; uint64_t v___x_3668_; uint64_t v___x_3669_; uint64_t v___x_3670_; size_t v___x_3671_; size_t v___x_3672_; size_t v___x_3673_; size_t v___x_3674_; size_t v___x_3675_; lean_object* v___x_3676_; lean_object* v___x_3677_; 
v___x_3665_ = 32ULL;
v___x_3666_ = lean_uint64_shift_right(v___y_3664_, v___x_3665_);
v_fold_3667_ = lean_uint64_xor(v___y_3664_, v___x_3666_);
v___x_3668_ = 16ULL;
v___x_3669_ = lean_uint64_shift_right(v_fold_3667_, v___x_3668_);
v___x_3670_ = lean_uint64_xor(v_fold_3667_, v___x_3669_);
v___x_3671_ = lean_uint64_to_usize(v___x_3670_);
v___x_3672_ = lean_usize_of_nat(v___x_3662_);
v___x_3673_ = ((size_t)1ULL);
v___x_3674_ = lean_usize_sub(v___x_3672_, v___x_3673_);
v___x_3675_ = lean_usize_land(v___x_3671_, v___x_3674_);
v___x_3676_ = lean_array_uget_borrowed(v_buckets_3661_, v___x_3675_);
v___x_3677_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___redArg(v_a_3660_, v___x_3676_);
return v___x_3677_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg___boxed(lean_object* v_m_3680_, lean_object* v_a_3681_){
_start:
{
lean_object* v_res_3682_; 
v_res_3682_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(v_m_3680_, v_a_3681_);
lean_dec(v_a_3681_);
lean_dec_ref(v_m_3680_);
return v_res_3682_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAttributeImplOfEntry(lean_object* v_e_3684_){
_start:
{
lean_object* v___x_3686_; lean_object* v___x_3687_; lean_object* v_builderId_3688_; lean_object* v_ref_3689_; lean_object* v_args_3690_; lean_object* v___x_3691_; 
v___x_3686_ = l_Lean_attributeImplBuilderTableRef;
v___x_3687_ = lean_st_ref_get(v___x_3686_);
v_builderId_3688_ = lean_ctor_get(v_e_3684_, 0);
lean_inc(v_builderId_3688_);
v_ref_3689_ = lean_ctor_get(v_e_3684_, 1);
lean_inc(v_ref_3689_);
v_args_3690_ = lean_ctor_get(v_e_3684_, 2);
lean_inc(v_args_3690_);
lean_dec_ref(v_e_3684_);
v___x_3691_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(v___x_3687_, v_builderId_3688_);
lean_dec(v___x_3687_);
if (lean_obj_tag(v___x_3691_) == 0)
{
lean_object* v___x_3692_; uint8_t v___x_3693_; lean_object* v___x_3694_; lean_object* v___x_3695_; lean_object* v___x_3696_; lean_object* v___x_3697_; lean_object* v___x_3698_; lean_object* v___x_3699_; 
lean_dec(v_args_3690_);
lean_dec(v_ref_3689_);
v___x_3692_ = ((lean_object*)(l_Lean_mkAttributeImplOfEntry___closed__0));
v___x_3693_ = 1;
v___x_3694_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_builderId_3688_, v___x_3693_);
v___x_3695_ = lean_string_append(v___x_3692_, v___x_3694_);
lean_dec_ref(v___x_3694_);
v___x_3696_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__4));
v___x_3697_ = lean_string_append(v___x_3695_, v___x_3696_);
v___x_3698_ = lean_mk_io_user_error(v___x_3697_);
v___x_3699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3699_, 0, v___x_3698_);
return v___x_3699_;
}
else
{
lean_object* v_val_3700_; lean_object* v___x_3701_; lean_object* v___x_3702_; 
lean_dec(v_builderId_3688_);
v_val_3700_ = lean_ctor_get(v___x_3691_, 0);
lean_inc(v_val_3700_);
lean_dec_ref(v___x_3691_);
v___x_3701_ = lean_apply_2(v_val_3700_, v_ref_3689_, v_args_3690_);
v___x_3702_ = l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___redArg(v___x_3701_);
return v___x_3702_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkAttributeImplOfEntry___boxed(lean_object* v_e_3703_, lean_object* v_a_3704_){
_start:
{
lean_object* v_res_3705_; 
v_res_3705_ = l_Lean_mkAttributeImplOfEntry(v_e_3703_);
return v_res_3705_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0(lean_object* v_00_u03b2_3706_, lean_object* v_m_3707_, lean_object* v_a_3708_){
_start:
{
lean_object* v___x_3709_; 
v___x_3709_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(v_m_3707_, v_a_3708_);
return v___x_3709_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___boxed(lean_object* v_00_u03b2_3710_, lean_object* v_m_3711_, lean_object* v_a_3712_){
_start:
{
lean_object* v_res_3713_; 
v_res_3713_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0(v_00_u03b2_3710_, v_m_3711_, v_a_3712_);
lean_dec(v_a_3712_);
lean_dec_ref(v_m_3711_);
return v_res_3713_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0(lean_object* v_00_u03b2_3714_, lean_object* v_a_3715_, lean_object* v_x_3716_){
_start:
{
lean_object* v___x_3717_; 
v___x_3717_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___redArg(v_a_3715_, v_x_3716_);
return v___x_3717_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3718_, lean_object* v_a_3719_, lean_object* v_x_3720_){
_start:
{
lean_object* v_res_3721_; 
v_res_3721_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0(v_00_u03b2_3718_, v_a_3719_, v_x_3720_);
lean_dec(v_x_3720_);
lean_dec(v_a_3719_);
return v_res_3721_;
}
}
static lean_object* _init_l_Lean_instInhabitedAttributeExtensionState_default___closed__0(void){
_start:
{
lean_object* v___x_3722_; lean_object* v___x_3723_; lean_object* v___x_3724_; 
v___x_3722_ = lean_obj_once(&l_Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_, &l_Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2__once, _init_l_Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_);
v___x_3723_ = lean_box(0);
v___x_3724_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3724_, 0, v___x_3723_);
lean_ctor_set(v___x_3724_, 1, v___x_3722_);
return v___x_3724_;
}
}
static lean_object* _init_l_Lean_instInhabitedAttributeExtensionState_default(void){
_start:
{
lean_object* v___x_3725_; 
v___x_3725_ = lean_obj_once(&l_Lean_instInhabitedAttributeExtensionState_default___closed__0, &l_Lean_instInhabitedAttributeExtensionState_default___closed__0_once, _init_l_Lean_instInhabitedAttributeExtensionState_default___closed__0);
return v___x_3725_;
}
}
static lean_object* _init_l_Lean_instInhabitedAttributeExtensionState(void){
_start:
{
lean_object* v___x_3726_; 
v___x_3726_ = l_Lean_instInhabitedAttributeExtensionState_default;
return v___x_3726_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_AttributeExtension_mkInitial(){
_start:
{
lean_object* v___x_3728_; lean_object* v___x_3729_; lean_object* v___x_3730_; lean_object* v___x_3731_; lean_object* v___x_3732_; 
v___x_3728_ = l_Lean_attributeMapRef;
v___x_3729_ = lean_st_ref_get(v___x_3728_);
v___x_3730_ = lean_box(0);
v___x_3731_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3731_, 0, v___x_3730_);
lean_ctor_set(v___x_3731_, 1, v___x_3729_);
v___x_3732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3732_, 0, v___x_3731_);
return v___x_3732_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_AttributeExtension_mkInitial___boxed(lean_object* v_a_3733_){
_start:
{
lean_object* v_res_3734_; 
v_res_3734_ = l___private_Lean_Attributes_0__Lean_AttributeExtension_mkInitial();
return v_res_3734_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAttributeImplOfConstantUnsafe(lean_object* v_env_3740_, lean_object* v_opts_3741_, lean_object* v_declName_3742_){
_start:
{
uint8_t v___x_3745_; lean_object* v___x_3746_; 
v___x_3745_ = 0;
lean_inc(v_declName_3742_);
lean_inc_ref(v_env_3740_);
v___x_3746_ = l_Lean_Environment_find_x3f(v_env_3740_, v_declName_3742_, v___x_3745_);
if (lean_obj_tag(v___x_3746_) == 0)
{
lean_object* v___x_3747_; uint8_t v___x_3748_; lean_object* v___x_3749_; lean_object* v___x_3750_; lean_object* v___x_3751_; lean_object* v___x_3752_; lean_object* v___x_3753_; 
lean_dec_ref(v_env_3740_);
v___x_3747_ = ((lean_object*)(l_Lean_mkAttributeImplOfConstantUnsafe___closed__2));
v___x_3748_ = 1;
v___x_3749_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_declName_3742_, v___x_3748_);
v___x_3750_ = lean_string_append(v___x_3747_, v___x_3749_);
lean_dec_ref(v___x_3749_);
v___x_3751_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__4));
v___x_3752_ = lean_string_append(v___x_3750_, v___x_3751_);
v___x_3753_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3753_, 0, v___x_3752_);
return v___x_3753_;
}
else
{
lean_object* v_val_3754_; lean_object* v___x_3755_; 
v_val_3754_ = lean_ctor_get(v___x_3746_, 0);
lean_inc(v_val_3754_);
lean_dec_ref(v___x_3746_);
v___x_3755_ = l_Lean_ConstantInfo_type(v_val_3754_);
lean_dec(v_val_3754_);
if (lean_obj_tag(v___x_3755_) == 4)
{
lean_object* v_declName_3756_; 
v_declName_3756_ = lean_ctor_get(v___x_3755_, 0);
lean_inc(v_declName_3756_);
lean_dec_ref(v___x_3755_);
if (lean_obj_tag(v_declName_3756_) == 1)
{
lean_object* v_pre_3757_; 
v_pre_3757_ = lean_ctor_get(v_declName_3756_, 0);
lean_inc(v_pre_3757_);
if (lean_obj_tag(v_pre_3757_) == 1)
{
lean_object* v_pre_3758_; 
v_pre_3758_ = lean_ctor_get(v_pre_3757_, 0);
if (lean_obj_tag(v_pre_3758_) == 0)
{
lean_object* v_str_3759_; lean_object* v_str_3760_; lean_object* v___x_3761_; uint8_t v___x_3762_; 
v_str_3759_ = lean_ctor_get(v_declName_3756_, 1);
lean_inc_ref(v_str_3759_);
lean_dec_ref(v_declName_3756_);
v_str_3760_ = lean_ctor_get(v_pre_3757_, 1);
lean_inc_ref(v_str_3760_);
lean_dec_ref(v_pre_3757_);
v___x_3761_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__0));
v___x_3762_ = lean_string_dec_eq(v_str_3760_, v___x_3761_);
lean_dec_ref(v_str_3760_);
if (v___x_3762_ == 0)
{
lean_dec_ref(v_str_3759_);
lean_dec(v_declName_3742_);
lean_dec_ref(v_env_3740_);
goto v___jp_3743_;
}
else
{
lean_object* v___x_3763_; uint8_t v___x_3764_; 
v___x_3763_ = ((lean_object*)(l_Lean_mkAttributeImplOfConstantUnsafe___closed__3));
v___x_3764_ = lean_string_dec_eq(v_str_3759_, v___x_3763_);
lean_dec_ref(v_str_3759_);
if (v___x_3764_ == 0)
{
lean_dec(v_declName_3742_);
lean_dec_ref(v_env_3740_);
goto v___jp_3743_;
}
else
{
lean_object* v___x_3765_; 
v___x_3765_ = l_Lean_Environment_evalConst___redArg(v_env_3740_, v_opts_3741_, v_declName_3742_, v___x_3764_);
lean_dec(v_declName_3742_);
lean_dec_ref(v_env_3740_);
return v___x_3765_;
}
}
}
else
{
lean_dec_ref(v_pre_3757_);
lean_dec_ref(v_declName_3756_);
lean_dec(v_declName_3742_);
lean_dec_ref(v_env_3740_);
goto v___jp_3743_;
}
}
else
{
lean_dec_ref(v_declName_3756_);
lean_dec(v_pre_3757_);
lean_dec(v_declName_3742_);
lean_dec_ref(v_env_3740_);
goto v___jp_3743_;
}
}
else
{
lean_dec(v_declName_3756_);
lean_dec(v_declName_3742_);
lean_dec_ref(v_env_3740_);
goto v___jp_3743_;
}
}
else
{
lean_dec_ref(v___x_3755_);
lean_dec(v_declName_3742_);
lean_dec_ref(v_env_3740_);
goto v___jp_3743_;
}
}
v___jp_3743_:
{
lean_object* v___x_3744_; 
v___x_3744_ = ((lean_object*)(l_Lean_mkAttributeImplOfConstantUnsafe___closed__1));
return v___x_3744_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkAttributeImplOfConstantUnsafe___boxed(lean_object* v_env_3766_, lean_object* v_opts_3767_, lean_object* v_declName_3768_){
_start:
{
lean_object* v_res_3769_; 
v_res_3769_ = l_Lean_mkAttributeImplOfConstantUnsafe(v_env_3766_, v_opts_3767_, v_declName_3768_);
lean_dec_ref(v_opts_3767_);
return v_res_3769_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg(lean_object* v_as_3770_, size_t v_i_3771_, size_t v_stop_3772_, lean_object* v_b_3773_){
_start:
{
uint8_t v___x_3775_; 
v___x_3775_ = lean_usize_dec_eq(v_i_3771_, v_stop_3772_);
if (v___x_3775_ == 0)
{
lean_object* v___x_3776_; lean_object* v___x_3777_; 
v___x_3776_ = lean_array_uget_borrowed(v_as_3770_, v_i_3771_);
lean_inc(v___x_3776_);
v___x_3777_ = l_Lean_mkAttributeImplOfEntry(v___x_3776_);
if (lean_obj_tag(v___x_3777_) == 0)
{
lean_object* v_a_3778_; lean_object* v_toAttributeImplCore_3779_; lean_object* v_name_3780_; lean_object* v___x_3781_; size_t v___x_3782_; size_t v___x_3783_; 
v_a_3778_ = lean_ctor_get(v___x_3777_, 0);
lean_inc(v_a_3778_);
lean_dec_ref(v___x_3777_);
v_toAttributeImplCore_3779_ = lean_ctor_get(v_a_3778_, 0);
v_name_3780_ = lean_ctor_get(v_toAttributeImplCore_3779_, 1);
lean_inc(v_name_3780_);
v___x_3781_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1___redArg(v_b_3773_, v_name_3780_, v_a_3778_);
v___x_3782_ = ((size_t)1ULL);
v___x_3783_ = lean_usize_add(v_i_3771_, v___x_3782_);
v_i_3771_ = v___x_3783_;
v_b_3773_ = v___x_3781_;
goto _start;
}
else
{
lean_object* v_a_3785_; lean_object* v___x_3787_; uint8_t v_isShared_3788_; uint8_t v_isSharedCheck_3792_; 
lean_dec_ref(v_b_3773_);
v_a_3785_ = lean_ctor_get(v___x_3777_, 0);
v_isSharedCheck_3792_ = !lean_is_exclusive(v___x_3777_);
if (v_isSharedCheck_3792_ == 0)
{
v___x_3787_ = v___x_3777_;
v_isShared_3788_ = v_isSharedCheck_3792_;
goto v_resetjp_3786_;
}
else
{
lean_inc(v_a_3785_);
lean_dec(v___x_3777_);
v___x_3787_ = lean_box(0);
v_isShared_3788_ = v_isSharedCheck_3792_;
goto v_resetjp_3786_;
}
v_resetjp_3786_:
{
lean_object* v___x_3790_; 
if (v_isShared_3788_ == 0)
{
v___x_3790_ = v___x_3787_;
goto v_reusejp_3789_;
}
else
{
lean_object* v_reuseFailAlloc_3791_; 
v_reuseFailAlloc_3791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3791_, 0, v_a_3785_);
v___x_3790_ = v_reuseFailAlloc_3791_;
goto v_reusejp_3789_;
}
v_reusejp_3789_:
{
return v___x_3790_;
}
}
}
}
else
{
lean_object* v___x_3793_; 
v___x_3793_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3793_, 0, v_b_3773_);
return v___x_3793_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg___boxed(lean_object* v_as_3794_, lean_object* v_i_3795_, lean_object* v_stop_3796_, lean_object* v_b_3797_, lean_object* v___y_3798_){
_start:
{
size_t v_i_boxed_3799_; size_t v_stop_boxed_3800_; lean_object* v_res_3801_; 
v_i_boxed_3799_ = lean_unbox_usize(v_i_3795_);
lean_dec(v_i_3795_);
v_stop_boxed_3800_ = lean_unbox_usize(v_stop_3796_);
lean_dec(v_stop_3796_);
v_res_3801_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg(v_as_3794_, v_i_boxed_3799_, v_stop_boxed_3800_, v_b_3797_);
lean_dec_ref(v_as_3794_);
return v_res_3801_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__1(lean_object* v_as_3802_, size_t v_i_3803_, size_t v_stop_3804_, lean_object* v_b_3805_, lean_object* v___y_3806_){
_start:
{
lean_object* v_a_3809_; lean_object* v___y_3814_; uint8_t v___x_3816_; 
v___x_3816_ = lean_usize_dec_eq(v_i_3803_, v_stop_3804_);
if (v___x_3816_ == 0)
{
lean_object* v___x_3817_; lean_object* v___x_3818_; lean_object* v___x_3819_; uint8_t v___x_3820_; 
v___x_3817_ = lean_array_uget_borrowed(v_as_3802_, v_i_3803_);
v___x_3818_ = lean_unsigned_to_nat(0u);
v___x_3819_ = lean_array_get_size(v___x_3817_);
v___x_3820_ = lean_nat_dec_lt(v___x_3818_, v___x_3819_);
if (v___x_3820_ == 0)
{
v_a_3809_ = v_b_3805_;
goto v___jp_3808_;
}
else
{
uint8_t v___x_3821_; 
v___x_3821_ = lean_nat_dec_le(v___x_3819_, v___x_3819_);
if (v___x_3821_ == 0)
{
if (v___x_3820_ == 0)
{
v_a_3809_ = v_b_3805_;
goto v___jp_3808_;
}
else
{
size_t v___x_3822_; size_t v___x_3823_; lean_object* v___x_3824_; 
v___x_3822_ = ((size_t)0ULL);
v___x_3823_ = lean_usize_of_nat(v___x_3819_);
v___x_3824_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg(v___x_3817_, v___x_3822_, v___x_3823_, v_b_3805_);
v___y_3814_ = v___x_3824_;
goto v___jp_3813_;
}
}
else
{
size_t v___x_3825_; size_t v___x_3826_; lean_object* v___x_3827_; 
v___x_3825_ = ((size_t)0ULL);
v___x_3826_ = lean_usize_of_nat(v___x_3819_);
v___x_3827_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg(v___x_3817_, v___x_3825_, v___x_3826_, v_b_3805_);
v___y_3814_ = v___x_3827_;
goto v___jp_3813_;
}
}
}
else
{
lean_object* v___x_3828_; 
v___x_3828_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3828_, 0, v_b_3805_);
return v___x_3828_;
}
v___jp_3808_:
{
size_t v___x_3810_; size_t v___x_3811_; 
v___x_3810_ = ((size_t)1ULL);
v___x_3811_ = lean_usize_add(v_i_3803_, v___x_3810_);
v_i_3803_ = v___x_3811_;
v_b_3805_ = v_a_3809_;
goto _start;
}
v___jp_3813_:
{
if (lean_obj_tag(v___y_3814_) == 0)
{
lean_object* v_a_3815_; 
v_a_3815_ = lean_ctor_get(v___y_3814_, 0);
lean_inc(v_a_3815_);
lean_dec_ref(v___y_3814_);
v_a_3809_ = v_a_3815_;
goto v___jp_3808_;
}
else
{
return v___y_3814_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__1___boxed(lean_object* v_as_3829_, lean_object* v_i_3830_, lean_object* v_stop_3831_, lean_object* v_b_3832_, lean_object* v___y_3833_, lean_object* v___y_3834_){
_start:
{
size_t v_i_boxed_3835_; size_t v_stop_boxed_3836_; lean_object* v_res_3837_; 
v_i_boxed_3835_ = lean_unbox_usize(v_i_3830_);
lean_dec(v_i_3830_);
v_stop_boxed_3836_ = lean_unbox_usize(v_stop_3831_);
lean_dec(v_stop_3831_);
v_res_3837_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__1(v_as_3829_, v_i_boxed_3835_, v_stop_boxed_3836_, v_b_3832_, v___y_3833_);
lean_dec_ref(v___y_3833_);
lean_dec_ref(v_as_3829_);
return v_res_3837_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_AttributeExtension_addImported(lean_object* v_es_3838_, lean_object* v_a_3839_){
_start:
{
lean_object* v_a_3842_; lean_object* v___y_3847_; lean_object* v___x_3857_; lean_object* v___x_3858_; lean_object* v___x_3859_; lean_object* v___x_3860_; uint8_t v___x_3861_; 
v___x_3857_ = l_Lean_attributeMapRef;
v___x_3858_ = lean_st_ref_get(v___x_3857_);
v___x_3859_ = lean_unsigned_to_nat(0u);
v___x_3860_ = lean_array_get_size(v_es_3838_);
v___x_3861_ = lean_nat_dec_lt(v___x_3859_, v___x_3860_);
if (v___x_3861_ == 0)
{
v_a_3842_ = v___x_3858_;
goto v___jp_3841_;
}
else
{
uint8_t v___x_3862_; 
v___x_3862_ = lean_nat_dec_le(v___x_3860_, v___x_3860_);
if (v___x_3862_ == 0)
{
if (v___x_3861_ == 0)
{
v_a_3842_ = v___x_3858_;
goto v___jp_3841_;
}
else
{
size_t v___x_3863_; size_t v___x_3864_; lean_object* v___x_3865_; 
v___x_3863_ = ((size_t)0ULL);
v___x_3864_ = lean_usize_of_nat(v___x_3860_);
v___x_3865_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__1(v_es_3838_, v___x_3863_, v___x_3864_, v___x_3858_, v_a_3839_);
v___y_3847_ = v___x_3865_;
goto v___jp_3846_;
}
}
else
{
size_t v___x_3866_; size_t v___x_3867_; lean_object* v___x_3868_; 
v___x_3866_ = ((size_t)0ULL);
v___x_3867_ = lean_usize_of_nat(v___x_3860_);
v___x_3868_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__1(v_es_3838_, v___x_3866_, v___x_3867_, v___x_3858_, v_a_3839_);
v___y_3847_ = v___x_3868_;
goto v___jp_3846_;
}
}
v___jp_3841_:
{
lean_object* v___x_3843_; lean_object* v___x_3844_; lean_object* v___x_3845_; 
v___x_3843_ = lean_box(0);
v___x_3844_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3844_, 0, v___x_3843_);
lean_ctor_set(v___x_3844_, 1, v_a_3842_);
v___x_3845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3845_, 0, v___x_3844_);
return v___x_3845_;
}
v___jp_3846_:
{
if (lean_obj_tag(v___y_3847_) == 0)
{
lean_object* v_a_3848_; 
v_a_3848_ = lean_ctor_get(v___y_3847_, 0);
lean_inc(v_a_3848_);
lean_dec_ref(v___y_3847_);
v_a_3842_ = v_a_3848_;
goto v___jp_3841_;
}
else
{
lean_object* v_a_3849_; lean_object* v___x_3851_; uint8_t v_isShared_3852_; uint8_t v_isSharedCheck_3856_; 
v_a_3849_ = lean_ctor_get(v___y_3847_, 0);
v_isSharedCheck_3856_ = !lean_is_exclusive(v___y_3847_);
if (v_isSharedCheck_3856_ == 0)
{
v___x_3851_ = v___y_3847_;
v_isShared_3852_ = v_isSharedCheck_3856_;
goto v_resetjp_3850_;
}
else
{
lean_inc(v_a_3849_);
lean_dec(v___y_3847_);
v___x_3851_ = lean_box(0);
v_isShared_3852_ = v_isSharedCheck_3856_;
goto v_resetjp_3850_;
}
v_resetjp_3850_:
{
lean_object* v___x_3854_; 
if (v_isShared_3852_ == 0)
{
v___x_3854_ = v___x_3851_;
goto v_reusejp_3853_;
}
else
{
lean_object* v_reuseFailAlloc_3855_; 
v_reuseFailAlloc_3855_ = lean_alloc_ctor(1, 1, 0);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_AttributeExtension_addImported___boxed(lean_object* v_es_3869_, lean_object* v_a_3870_, lean_object* v_a_3871_){
_start:
{
lean_object* v_res_3872_; 
v_res_3872_ = l___private_Lean_Attributes_0__Lean_AttributeExtension_addImported(v_es_3869_, v_a_3870_);
lean_dec_ref(v_a_3870_);
lean_dec_ref(v_es_3869_);
return v_res_3872_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0(lean_object* v_as_3873_, size_t v_i_3874_, size_t v_stop_3875_, lean_object* v_b_3876_, lean_object* v___y_3877_){
_start:
{
lean_object* v___x_3879_; 
v___x_3879_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg(v_as_3873_, v_i_3874_, v_stop_3875_, v_b_3876_);
return v___x_3879_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___boxed(lean_object* v_as_3880_, lean_object* v_i_3881_, lean_object* v_stop_3882_, lean_object* v_b_3883_, lean_object* v___y_3884_, lean_object* v___y_3885_){
_start:
{
size_t v_i_boxed_3886_; size_t v_stop_boxed_3887_; lean_object* v_res_3888_; 
v_i_boxed_3886_ = lean_unbox_usize(v_i_3881_);
lean_dec(v_i_3881_);
v_stop_boxed_3887_ = lean_unbox_usize(v_stop_3882_);
lean_dec(v_stop_3882_);
v_res_3888_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0(v_as_3880_, v_i_boxed_3886_, v_stop_boxed_3887_, v_b_3883_, v___y_3884_);
lean_dec_ref(v___y_3884_);
lean_dec_ref(v_as_3880_);
return v_res_3888_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_addAttrEntry(lean_object* v_s_3889_, lean_object* v_e_3890_){
_start:
{
lean_object* v_snd_3891_; lean_object* v_toAttributeImplCore_3892_; lean_object* v_fst_3893_; lean_object* v___x_3895_; uint8_t v_isShared_3896_; uint8_t v_isSharedCheck_3911_; 
v_snd_3891_ = lean_ctor_get(v_e_3890_, 1);
lean_inc(v_snd_3891_);
v_toAttributeImplCore_3892_ = lean_ctor_get(v_snd_3891_, 0);
v_fst_3893_ = lean_ctor_get(v_e_3890_, 0);
v_isSharedCheck_3911_ = !lean_is_exclusive(v_e_3890_);
if (v_isSharedCheck_3911_ == 0)
{
lean_object* v_unused_3912_; 
v_unused_3912_ = lean_ctor_get(v_e_3890_, 1);
lean_dec(v_unused_3912_);
v___x_3895_ = v_e_3890_;
v_isShared_3896_ = v_isSharedCheck_3911_;
goto v_resetjp_3894_;
}
else
{
lean_inc(v_fst_3893_);
lean_dec(v_e_3890_);
v___x_3895_ = lean_box(0);
v_isShared_3896_ = v_isSharedCheck_3911_;
goto v_resetjp_3894_;
}
v_resetjp_3894_:
{
lean_object* v_newEntries_3897_; lean_object* v_map_3898_; lean_object* v___x_3900_; uint8_t v_isShared_3901_; uint8_t v_isSharedCheck_3910_; 
v_newEntries_3897_ = lean_ctor_get(v_s_3889_, 0);
v_map_3898_ = lean_ctor_get(v_s_3889_, 1);
v_isSharedCheck_3910_ = !lean_is_exclusive(v_s_3889_);
if (v_isSharedCheck_3910_ == 0)
{
v___x_3900_ = v_s_3889_;
v_isShared_3901_ = v_isSharedCheck_3910_;
goto v_resetjp_3899_;
}
else
{
lean_inc(v_map_3898_);
lean_inc(v_newEntries_3897_);
lean_dec(v_s_3889_);
v___x_3900_ = lean_box(0);
v_isShared_3901_ = v_isSharedCheck_3910_;
goto v_resetjp_3899_;
}
v_resetjp_3899_:
{
lean_object* v_name_3902_; lean_object* v___x_3904_; 
v_name_3902_ = lean_ctor_get(v_toAttributeImplCore_3892_, 1);
lean_inc(v_name_3902_);
if (v_isShared_3896_ == 0)
{
lean_ctor_set_tag(v___x_3895_, 1);
lean_ctor_set(v___x_3895_, 1, v_newEntries_3897_);
v___x_3904_ = v___x_3895_;
goto v_reusejp_3903_;
}
else
{
lean_object* v_reuseFailAlloc_3909_; 
v_reuseFailAlloc_3909_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3909_, 0, v_fst_3893_);
lean_ctor_set(v_reuseFailAlloc_3909_, 1, v_newEntries_3897_);
v___x_3904_ = v_reuseFailAlloc_3909_;
goto v_reusejp_3903_;
}
v_reusejp_3903_:
{
lean_object* v___x_3905_; lean_object* v___x_3907_; 
v___x_3905_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1___redArg(v_map_3898_, v_name_3902_, v_snd_3891_);
if (v_isShared_3901_ == 0)
{
lean_ctor_set(v___x_3900_, 1, v___x_3905_);
lean_ctor_set(v___x_3900_, 0, v___x_3904_);
v___x_3907_ = v___x_3900_;
goto v_reusejp_3906_;
}
else
{
lean_object* v_reuseFailAlloc_3908_; 
v_reuseFailAlloc_3908_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3908_, 0, v___x_3904_);
lean_ctor_set(v_reuseFailAlloc_3908_, 1, v___x_3905_);
v___x_3907_ = v_reuseFailAlloc_3908_;
goto v_reusejp_3906_;
}
v_reusejp_3906_:
{
return v___x_3907_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(lean_object* v_x_3913_, lean_object* v_s_3914_, uint8_t v_x_3915_){
_start:
{
lean_object* v_newEntries_3916_; lean_object* v___x_3917_; lean_object* v___x_3918_; 
v_newEntries_3916_ = lean_ctor_get(v_s_3914_, 0);
lean_inc(v_newEntries_3916_);
lean_dec_ref(v_s_3914_);
v___x_3917_ = l_List_reverse___redArg(v_newEntries_3916_);
v___x_3918_ = lean_array_mk(v___x_3917_);
return v___x_3918_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2____boxed(lean_object* v_x_3919_, lean_object* v_s_3920_, lean_object* v_x_3921_){
_start:
{
uint8_t v_x_90__boxed_3922_; lean_object* v_res_3923_; 
v_x_90__boxed_3922_ = lean_unbox(v_x_3921_);
v_res_3923_ = l_Lean_initFn___lam__0_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(v_x_3919_, v_s_3920_, v_x_90__boxed_3922_);
lean_dec_ref(v_x_3919_);
return v_res_3923_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__1_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(lean_object* v_s_3924_){
_start:
{
lean_object* v_newEntries_3925_; lean_object* v___x_3927_; uint8_t v_isShared_3928_; uint8_t v_isSharedCheck_3936_; 
v_newEntries_3925_ = lean_ctor_get(v_s_3924_, 0);
v_isSharedCheck_3936_ = !lean_is_exclusive(v_s_3924_);
if (v_isSharedCheck_3936_ == 0)
{
lean_object* v_unused_3937_; 
v_unused_3937_ = lean_ctor_get(v_s_3924_, 1);
lean_dec(v_unused_3937_);
v___x_3927_ = v_s_3924_;
v_isShared_3928_ = v_isSharedCheck_3936_;
goto v_resetjp_3926_;
}
else
{
lean_inc(v_newEntries_3925_);
lean_dec(v_s_3924_);
v___x_3927_ = lean_box(0);
v_isShared_3928_ = v_isSharedCheck_3936_;
goto v_resetjp_3926_;
}
v_resetjp_3926_:
{
lean_object* v___x_3929_; lean_object* v___x_3930_; lean_object* v___x_3931_; lean_object* v___x_3932_; lean_object* v___x_3934_; 
v___x_3929_ = ((lean_object*)(l_Lean_registerTagAttribute___lam__2___closed__4));
v___x_3930_ = l_List_lengthTR___redArg(v_newEntries_3925_);
lean_dec(v_newEntries_3925_);
v___x_3931_ = l_Nat_reprFast(v___x_3930_);
v___x_3932_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3932_, 0, v___x_3931_);
if (v_isShared_3928_ == 0)
{
lean_ctor_set_tag(v___x_3927_, 5);
lean_ctor_set(v___x_3927_, 1, v___x_3932_);
lean_ctor_set(v___x_3927_, 0, v___x_3929_);
v___x_3934_ = v___x_3927_;
goto v_reusejp_3933_;
}
else
{
lean_object* v_reuseFailAlloc_3935_; 
v_reuseFailAlloc_3935_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3935_, 0, v___x_3929_);
lean_ctor_set(v_reuseFailAlloc_3935_, 1, v___x_3932_);
v___x_3934_ = v_reuseFailAlloc_3935_;
goto v_reusejp_3933_;
}
v_reusejp_3933_:
{
return v___x_3934_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__2_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(lean_object* v_s_3938_){
_start:
{
lean_object* v_newEntries_3939_; lean_object* v___x_3940_; lean_object* v___x_3941_; 
v_newEntries_3939_ = lean_ctor_get(v_s_3938_, 0);
lean_inc(v_newEntries_3939_);
lean_dec_ref(v_s_3938_);
v___x_3940_ = l_List_reverse___redArg(v_newEntries_3939_);
v___x_3941_ = lean_array_mk(v___x_3940_);
return v___x_3941_;
}
}
static lean_object* _init_l_Lean_initFn___closed__7_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3951_; lean_object* v___x_3952_; lean_object* v___f_3953_; lean_object* v___f_3954_; lean_object* v___x_3955_; lean_object* v___x_3956_; lean_object* v___x_3957_; lean_object* v___x_3958_; lean_object* v___x_3959_; 
v___x_3951_ = lean_box(0);
v___x_3952_ = lean_box(2);
v___f_3953_ = ((lean_object*)(l_Lean_initFn___closed__1_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___f_3954_ = ((lean_object*)(l_Lean_initFn___closed__0_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___x_3955_ = ((lean_object*)(l_Lean_initFn___closed__6_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___x_3956_ = ((lean_object*)(l_Lean_initFn___closed__5_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___x_3957_ = lean_alloc_closure((void*)(l___private_Lean_Attributes_0__Lean_AttributeExtension_mkInitial___boxed), 1, 0);
v___x_3958_ = ((lean_object*)(l_Lean_initFn___closed__4_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___x_3959_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_3959_, 0, v___x_3958_);
lean_ctor_set(v___x_3959_, 1, v___x_3957_);
lean_ctor_set(v___x_3959_, 2, v___x_3956_);
lean_ctor_set(v___x_3959_, 3, v___x_3955_);
lean_ctor_set(v___x_3959_, 4, v___f_3954_);
lean_ctor_set(v___x_3959_, 5, v___f_3953_);
lean_ctor_set(v___x_3959_, 6, v___x_3952_);
lean_ctor_set(v___x_3959_, 7, v___x_3951_);
return v___x_3959_;
}
}
static lean_object* _init_l_Lean_initFn___closed__8_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_3960_; lean_object* v___x_3961_; lean_object* v___x_3962_; 
v___f_3960_ = ((lean_object*)(l_Lean_initFn___closed__2_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___x_3961_ = lean_obj_once(&l_Lean_initFn___closed__7_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_, &l_Lean_initFn___closed__7_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2__once, _init_l_Lean_initFn___closed__7_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_);
v___x_3962_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3962_, 0, v___x_3961_);
lean_ctor_set(v___x_3962_, 1, v___f_3960_);
return v___x_3962_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3964_; lean_object* v___x_3965_; 
v___x_3964_ = lean_obj_once(&l_Lean_initFn___closed__8_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_, &l_Lean_initFn___closed__8_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2__once, _init_l_Lean_initFn___closed__8_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_);
v___x_3965_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_3964_);
return v___x_3965_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2____boxed(lean_object* v_a_3966_){
_start:
{
lean_object* v_res_3967_; 
v_res_3967_ = l_Lean_initFn_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_();
return v_res_3967_;
}
}
LEAN_EXPORT lean_object* lean_is_attribute(lean_object* v_n_3968_){
_start:
{
lean_object* v___x_3970_; lean_object* v___x_3971_; uint8_t v___x_3972_; lean_object* v___x_3973_; lean_object* v___x_3974_; 
v___x_3970_ = l_Lean_attributeMapRef;
v___x_3971_ = lean_st_ref_get(v___x_3970_);
v___x_3972_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(v___x_3971_, v_n_3968_);
lean_dec(v_n_3968_);
lean_dec(v___x_3971_);
v___x_3973_ = lean_box(v___x_3972_);
v___x_3974_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3974_, 0, v___x_3973_);
return v___x_3974_;
}
}
LEAN_EXPORT lean_object* l_Lean_isBuiltinAttribute___boxed(lean_object* v_n_3975_, lean_object* v_a_3976_){
_start:
{
lean_object* v_res_3977_; 
v_res_3977_ = lean_is_attribute(v_n_3975_);
return v_res_3977_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_getBuiltinAttributeNames_spec__0(lean_object* v_x_3978_, lean_object* v_x_3979_){
_start:
{
if (lean_obj_tag(v_x_3979_) == 0)
{
return v_x_3978_;
}
else
{
lean_object* v_key_3980_; lean_object* v_tail_3981_; lean_object* v___x_3982_; 
v_key_3980_ = lean_ctor_get(v_x_3979_, 0);
v_tail_3981_ = lean_ctor_get(v_x_3979_, 2);
lean_inc(v_key_3980_);
v___x_3982_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3982_, 0, v_key_3980_);
lean_ctor_set(v___x_3982_, 1, v_x_3978_);
v_x_3978_ = v___x_3982_;
v_x_3979_ = v_tail_3981_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_getBuiltinAttributeNames_spec__0___boxed(lean_object* v_x_3984_, lean_object* v_x_3985_){
_start:
{
lean_object* v_res_3986_; 
v_res_3986_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_getBuiltinAttributeNames_spec__0(v_x_3984_, v_x_3985_);
lean_dec(v_x_3985_);
return v_res_3986_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1(lean_object* v_as_3987_, size_t v_i_3988_, size_t v_stop_3989_, lean_object* v_b_3990_){
_start:
{
uint8_t v___x_3991_; 
v___x_3991_ = lean_usize_dec_eq(v_i_3988_, v_stop_3989_);
if (v___x_3991_ == 0)
{
lean_object* v___x_3992_; lean_object* v___x_3993_; size_t v___x_3994_; size_t v___x_3995_; 
v___x_3992_ = lean_array_uget_borrowed(v_as_3987_, v_i_3988_);
v___x_3993_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_getBuiltinAttributeNames_spec__0(v_b_3990_, v___x_3992_);
v___x_3994_ = ((size_t)1ULL);
v___x_3995_ = lean_usize_add(v_i_3988_, v___x_3994_);
v_i_3988_ = v___x_3995_;
v_b_3990_ = v___x_3993_;
goto _start;
}
else
{
return v_b_3990_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1___boxed(lean_object* v_as_3997_, lean_object* v_i_3998_, lean_object* v_stop_3999_, lean_object* v_b_4000_){
_start:
{
size_t v_i_boxed_4001_; size_t v_stop_boxed_4002_; lean_object* v_res_4003_; 
v_i_boxed_4001_ = lean_unbox_usize(v_i_3998_);
lean_dec(v_i_3998_);
v_stop_boxed_4002_ = lean_unbox_usize(v_stop_3999_);
lean_dec(v_stop_3999_);
v_res_4003_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1(v_as_3997_, v_i_boxed_4001_, v_stop_boxed_4002_, v_b_4000_);
lean_dec_ref(v_as_3997_);
return v_res_4003_;
}
}
LEAN_EXPORT lean_object* l_Lean_getBuiltinAttributeNames(){
_start:
{
lean_object* v___x_4005_; lean_object* v___x_4006_; lean_object* v_buckets_4007_; lean_object* v___x_4008_; lean_object* v___x_4009_; lean_object* v___x_4010_; uint8_t v___x_4011_; 
v___x_4005_ = l_Lean_attributeMapRef;
v___x_4006_ = lean_st_ref_get(v___x_4005_);
v_buckets_4007_ = lean_ctor_get(v___x_4006_, 1);
lean_inc_ref(v_buckets_4007_);
lean_dec(v___x_4006_);
v___x_4008_ = lean_box(0);
v___x_4009_ = lean_unsigned_to_nat(0u);
v___x_4010_ = lean_array_get_size(v_buckets_4007_);
v___x_4011_ = lean_nat_dec_lt(v___x_4009_, v___x_4010_);
if (v___x_4011_ == 0)
{
lean_object* v___x_4012_; 
lean_dec_ref(v_buckets_4007_);
v___x_4012_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4012_, 0, v___x_4008_);
return v___x_4012_;
}
else
{
uint8_t v___x_4013_; 
v___x_4013_ = lean_nat_dec_le(v___x_4010_, v___x_4010_);
if (v___x_4013_ == 0)
{
if (v___x_4011_ == 0)
{
lean_object* v___x_4014_; 
lean_dec_ref(v_buckets_4007_);
v___x_4014_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4014_, 0, v___x_4008_);
return v___x_4014_;
}
else
{
size_t v___x_4015_; size_t v___x_4016_; lean_object* v___x_4017_; lean_object* v___x_4018_; 
v___x_4015_ = ((size_t)0ULL);
v___x_4016_ = lean_usize_of_nat(v___x_4010_);
v___x_4017_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1(v_buckets_4007_, v___x_4015_, v___x_4016_, v___x_4008_);
lean_dec_ref(v_buckets_4007_);
v___x_4018_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4018_, 0, v___x_4017_);
return v___x_4018_;
}
}
else
{
size_t v___x_4019_; size_t v___x_4020_; lean_object* v___x_4021_; lean_object* v___x_4022_; 
v___x_4019_ = ((size_t)0ULL);
v___x_4020_ = lean_usize_of_nat(v___x_4010_);
v___x_4021_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1(v_buckets_4007_, v___x_4019_, v___x_4020_, v___x_4008_);
lean_dec_ref(v_buckets_4007_);
v___x_4022_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4022_, 0, v___x_4021_);
return v___x_4022_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getBuiltinAttributeNames___boxed(lean_object* v_a_4023_){
_start:
{
lean_object* v_res_4024_; 
v_res_4024_ = l_Lean_getBuiltinAttributeNames();
return v_res_4024_;
}
}
LEAN_EXPORT lean_object* l_Lean_getBuiltinAttributeImpl(lean_object* v_attrName_4026_){
_start:
{
lean_object* v___x_4028_; lean_object* v___x_4029_; lean_object* v___x_4030_; 
v___x_4028_ = l_Lean_attributeMapRef;
v___x_4029_ = lean_st_ref_get(v___x_4028_);
v___x_4030_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(v___x_4029_, v_attrName_4026_);
lean_dec(v___x_4029_);
if (lean_obj_tag(v___x_4030_) == 0)
{
lean_object* v___x_4031_; uint8_t v___x_4032_; lean_object* v___x_4033_; lean_object* v___x_4034_; lean_object* v___x_4035_; lean_object* v___x_4036_; lean_object* v___x_4037_; lean_object* v___x_4038_; 
v___x_4031_ = ((lean_object*)(l_Lean_getBuiltinAttributeImpl___closed__0));
v___x_4032_ = 1;
v___x_4033_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_attrName_4026_, v___x_4032_);
v___x_4034_ = lean_string_append(v___x_4031_, v___x_4033_);
lean_dec_ref(v___x_4033_);
v___x_4035_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__4));
v___x_4036_ = lean_string_append(v___x_4034_, v___x_4035_);
v___x_4037_ = lean_mk_io_user_error(v___x_4036_);
v___x_4038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4038_, 0, v___x_4037_);
return v___x_4038_;
}
else
{
lean_object* v_val_4039_; lean_object* v___x_4041_; uint8_t v_isShared_4042_; uint8_t v_isSharedCheck_4046_; 
lean_dec(v_attrName_4026_);
v_val_4039_ = lean_ctor_get(v___x_4030_, 0);
v_isSharedCheck_4046_ = !lean_is_exclusive(v___x_4030_);
if (v_isSharedCheck_4046_ == 0)
{
v___x_4041_ = v___x_4030_;
v_isShared_4042_ = v_isSharedCheck_4046_;
goto v_resetjp_4040_;
}
else
{
lean_inc(v_val_4039_);
lean_dec(v___x_4030_);
v___x_4041_ = lean_box(0);
v_isShared_4042_ = v_isSharedCheck_4046_;
goto v_resetjp_4040_;
}
v_resetjp_4040_:
{
lean_object* v___x_4044_; 
if (v_isShared_4042_ == 0)
{
lean_ctor_set_tag(v___x_4041_, 0);
v___x_4044_ = v___x_4041_;
goto v_reusejp_4043_;
}
else
{
lean_object* v_reuseFailAlloc_4045_; 
v_reuseFailAlloc_4045_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4045_, 0, v_val_4039_);
v___x_4044_ = v_reuseFailAlloc_4045_;
goto v_reusejp_4043_;
}
v_reusejp_4043_:
{
return v___x_4044_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getBuiltinAttributeImpl___boxed(lean_object* v_attrName_4047_, lean_object* v_a_4048_){
_start:
{
lean_object* v_res_4049_; 
v_res_4049_ = l_Lean_getBuiltinAttributeImpl(v_attrName_4047_);
return v_res_4049_;
}
}
LEAN_EXPORT lean_object* lean_attribute_application_time(lean_object* v_n_4050_){
_start:
{
lean_object* v___x_4052_; 
v___x_4052_ = l_Lean_getBuiltinAttributeImpl(v_n_4050_);
if (lean_obj_tag(v___x_4052_) == 0)
{
lean_object* v_a_4053_; lean_object* v___x_4055_; uint8_t v_isShared_4056_; uint8_t v_isSharedCheck_4063_; 
v_a_4053_ = lean_ctor_get(v___x_4052_, 0);
v_isSharedCheck_4063_ = !lean_is_exclusive(v___x_4052_);
if (v_isSharedCheck_4063_ == 0)
{
v___x_4055_ = v___x_4052_;
v_isShared_4056_ = v_isSharedCheck_4063_;
goto v_resetjp_4054_;
}
else
{
lean_inc(v_a_4053_);
lean_dec(v___x_4052_);
v___x_4055_ = lean_box(0);
v_isShared_4056_ = v_isSharedCheck_4063_;
goto v_resetjp_4054_;
}
v_resetjp_4054_:
{
lean_object* v_toAttributeImplCore_4057_; uint8_t v_applicationTime_4058_; lean_object* v___x_4059_; lean_object* v___x_4061_; 
v_toAttributeImplCore_4057_ = lean_ctor_get(v_a_4053_, 0);
lean_inc_ref(v_toAttributeImplCore_4057_);
lean_dec(v_a_4053_);
v_applicationTime_4058_ = lean_ctor_get_uint8(v_toAttributeImplCore_4057_, sizeof(void*)*3);
lean_dec_ref(v_toAttributeImplCore_4057_);
v___x_4059_ = lean_box(v_applicationTime_4058_);
if (v_isShared_4056_ == 0)
{
lean_ctor_set(v___x_4055_, 0, v___x_4059_);
v___x_4061_ = v___x_4055_;
goto v_reusejp_4060_;
}
else
{
lean_object* v_reuseFailAlloc_4062_; 
v_reuseFailAlloc_4062_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4062_, 0, v___x_4059_);
v___x_4061_ = v_reuseFailAlloc_4062_;
goto v_reusejp_4060_;
}
v_reusejp_4060_:
{
return v___x_4061_;
}
}
}
else
{
lean_object* v_a_4064_; lean_object* v___x_4066_; uint8_t v_isShared_4067_; uint8_t v_isSharedCheck_4071_; 
v_a_4064_ = lean_ctor_get(v___x_4052_, 0);
v_isSharedCheck_4071_ = !lean_is_exclusive(v___x_4052_);
if (v_isSharedCheck_4071_ == 0)
{
v___x_4066_ = v___x_4052_;
v_isShared_4067_ = v_isSharedCheck_4071_;
goto v_resetjp_4065_;
}
else
{
lean_inc(v_a_4064_);
lean_dec(v___x_4052_);
v___x_4066_ = lean_box(0);
v_isShared_4067_ = v_isSharedCheck_4071_;
goto v_resetjp_4065_;
}
v_resetjp_4065_:
{
lean_object* v___x_4069_; 
if (v_isShared_4067_ == 0)
{
v___x_4069_ = v___x_4066_;
goto v_reusejp_4068_;
}
else
{
lean_object* v_reuseFailAlloc_4070_; 
v_reuseFailAlloc_4070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4070_, 0, v_a_4064_);
v___x_4069_ = v_reuseFailAlloc_4070_;
goto v_reusejp_4068_;
}
v_reusejp_4068_:
{
return v___x_4069_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getBuiltinAttributeApplicationTime___boxed(lean_object* v_n_4072_, lean_object* v_a_4073_){
_start:
{
lean_object* v_res_4074_; 
v_res_4074_ = lean_attribute_application_time(v_n_4072_);
return v_res_4074_;
}
}
LEAN_EXPORT uint8_t l_Lean_isAttribute(lean_object* v_env_4075_, lean_object* v_attrName_4076_){
_start:
{
lean_object* v___x_4077_; lean_object* v_toEnvExtension_4078_; lean_object* v_asyncMode_4079_; lean_object* v___x_4080_; lean_object* v___x_4081_; lean_object* v___x_4082_; lean_object* v_map_4083_; uint8_t v___x_4084_; 
v___x_4077_ = l_Lean_attributeExtension;
v_toEnvExtension_4078_ = lean_ctor_get(v___x_4077_, 0);
lean_inc_ref(v_toEnvExtension_4078_);
v_asyncMode_4079_ = lean_ctor_get(v_toEnvExtension_4078_, 2);
lean_inc(v_asyncMode_4079_);
lean_dec_ref(v_toEnvExtension_4078_);
v___x_4080_ = l_Lean_instInhabitedAttributeExtensionState_default;
v___x_4081_ = lean_box(0);
v___x_4082_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_4080_, v___x_4077_, v_env_4075_, v_asyncMode_4079_, v___x_4081_);
lean_dec(v_asyncMode_4079_);
v_map_4083_ = lean_ctor_get(v___x_4082_, 1);
lean_inc_ref(v_map_4083_);
lean_dec(v___x_4082_);
v___x_4084_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(v_map_4083_, v_attrName_4076_);
lean_dec_ref(v_map_4083_);
return v___x_4084_;
}
}
LEAN_EXPORT lean_object* l_Lean_isAttribute___boxed(lean_object* v_env_4085_, lean_object* v_attrName_4086_){
_start:
{
uint8_t v_res_4087_; lean_object* v_r_4088_; 
v_res_4087_ = l_Lean_isAttribute(v_env_4085_, v_attrName_4086_);
lean_dec(v_attrName_4086_);
v_r_4088_ = lean_box(v_res_4087_);
return v_r_4088_;
}
}
LEAN_EXPORT lean_object* l_Lean_getAttributeNames(lean_object* v_env_4089_){
_start:
{
lean_object* v___x_4090_; lean_object* v_toEnvExtension_4091_; lean_object* v_asyncMode_4092_; lean_object* v___x_4093_; lean_object* v___x_4094_; lean_object* v___x_4095_; lean_object* v_map_4096_; lean_object* v_buckets_4097_; lean_object* v___x_4098_; lean_object* v___x_4099_; lean_object* v___x_4100_; uint8_t v___x_4101_; 
v___x_4090_ = l_Lean_attributeExtension;
v_toEnvExtension_4091_ = lean_ctor_get(v___x_4090_, 0);
lean_inc_ref(v_toEnvExtension_4091_);
v_asyncMode_4092_ = lean_ctor_get(v_toEnvExtension_4091_, 2);
lean_inc(v_asyncMode_4092_);
lean_dec_ref(v_toEnvExtension_4091_);
v___x_4093_ = l_Lean_instInhabitedAttributeExtensionState_default;
v___x_4094_ = lean_box(0);
v___x_4095_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_4093_, v___x_4090_, v_env_4089_, v_asyncMode_4092_, v___x_4094_);
lean_dec(v_asyncMode_4092_);
v_map_4096_ = lean_ctor_get(v___x_4095_, 1);
lean_inc_ref(v_map_4096_);
lean_dec(v___x_4095_);
v_buckets_4097_ = lean_ctor_get(v_map_4096_, 1);
lean_inc_ref(v_buckets_4097_);
lean_dec_ref(v_map_4096_);
v___x_4098_ = lean_box(0);
v___x_4099_ = lean_unsigned_to_nat(0u);
v___x_4100_ = lean_array_get_size(v_buckets_4097_);
v___x_4101_ = lean_nat_dec_lt(v___x_4099_, v___x_4100_);
if (v___x_4101_ == 0)
{
lean_dec_ref(v_buckets_4097_);
return v___x_4098_;
}
else
{
uint8_t v___x_4102_; 
v___x_4102_ = lean_nat_dec_le(v___x_4100_, v___x_4100_);
if (v___x_4102_ == 0)
{
if (v___x_4101_ == 0)
{
lean_dec_ref(v_buckets_4097_);
return v___x_4098_;
}
else
{
size_t v___x_4103_; size_t v___x_4104_; lean_object* v___x_4105_; 
v___x_4103_ = ((size_t)0ULL);
v___x_4104_ = lean_usize_of_nat(v___x_4100_);
v___x_4105_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1(v_buckets_4097_, v___x_4103_, v___x_4104_, v___x_4098_);
lean_dec_ref(v_buckets_4097_);
return v___x_4105_;
}
}
else
{
size_t v___x_4106_; size_t v___x_4107_; lean_object* v___x_4108_; 
v___x_4106_ = ((size_t)0ULL);
v___x_4107_ = lean_usize_of_nat(v___x_4100_);
v___x_4108_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1(v_buckets_4097_, v___x_4106_, v___x_4107_, v___x_4098_);
lean_dec_ref(v_buckets_4097_);
return v___x_4108_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getAttributeImpl(lean_object* v_env_4109_, lean_object* v_attrName_4110_){
_start:
{
lean_object* v___x_4111_; lean_object* v_toEnvExtension_4112_; lean_object* v_asyncMode_4113_; lean_object* v___x_4114_; lean_object* v___x_4115_; lean_object* v___x_4116_; lean_object* v_map_4117_; lean_object* v___x_4118_; 
v___x_4111_ = l_Lean_attributeExtension;
v_toEnvExtension_4112_ = lean_ctor_get(v___x_4111_, 0);
lean_inc_ref(v_toEnvExtension_4112_);
v_asyncMode_4113_ = lean_ctor_get(v_toEnvExtension_4112_, 2);
lean_inc(v_asyncMode_4113_);
lean_dec_ref(v_toEnvExtension_4112_);
v___x_4114_ = l_Lean_instInhabitedAttributeExtensionState_default;
v___x_4115_ = lean_box(0);
v___x_4116_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_4114_, v___x_4111_, v_env_4109_, v_asyncMode_4113_, v___x_4115_);
lean_dec(v_asyncMode_4113_);
v_map_4117_ = lean_ctor_get(v___x_4116_, 1);
lean_inc_ref(v_map_4117_);
lean_dec(v___x_4116_);
v___x_4118_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(v_map_4117_, v_attrName_4110_);
lean_dec_ref(v_map_4117_);
if (lean_obj_tag(v___x_4118_) == 0)
{
lean_object* v___x_4119_; uint8_t v___x_4120_; lean_object* v___x_4121_; lean_object* v___x_4122_; lean_object* v___x_4123_; lean_object* v___x_4124_; lean_object* v___x_4125_; 
v___x_4119_ = ((lean_object*)(l_Lean_getBuiltinAttributeImpl___closed__0));
v___x_4120_ = 1;
v___x_4121_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_attrName_4110_, v___x_4120_);
v___x_4122_ = lean_string_append(v___x_4119_, v___x_4121_);
lean_dec_ref(v___x_4121_);
v___x_4123_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__4));
v___x_4124_ = lean_string_append(v___x_4122_, v___x_4123_);
v___x_4125_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4125_, 0, v___x_4124_);
return v___x_4125_;
}
else
{
lean_object* v_val_4126_; lean_object* v___x_4128_; uint8_t v_isShared_4129_; uint8_t v_isSharedCheck_4133_; 
lean_dec(v_attrName_4110_);
v_val_4126_ = lean_ctor_get(v___x_4118_, 0);
v_isSharedCheck_4133_ = !lean_is_exclusive(v___x_4118_);
if (v_isSharedCheck_4133_ == 0)
{
v___x_4128_ = v___x_4118_;
v_isShared_4129_ = v_isSharedCheck_4133_;
goto v_resetjp_4127_;
}
else
{
lean_inc(v_val_4126_);
lean_dec(v___x_4118_);
v___x_4128_ = lean_box(0);
v_isShared_4129_ = v_isSharedCheck_4133_;
goto v_resetjp_4127_;
}
v_resetjp_4127_:
{
lean_object* v___x_4131_; 
if (v_isShared_4129_ == 0)
{
v___x_4131_ = v___x_4128_;
goto v_reusejp_4130_;
}
else
{
lean_object* v_reuseFailAlloc_4132_; 
v_reuseFailAlloc_4132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4132_, 0, v_val_4126_);
v___x_4131_ = v_reuseFailAlloc_4132_;
goto v_reusejp_4130_;
}
v_reusejp_4130_:
{
return v___x_4131_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerAttributeOfBuilder(lean_object* v_env_4134_, lean_object* v_builderId_4135_, lean_object* v_ref_4136_, lean_object* v_args_4137_){
_start:
{
lean_object* v_entry_4139_; lean_object* v___x_4140_; 
v_entry_4139_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_entry_4139_, 0, v_builderId_4135_);
lean_ctor_set(v_entry_4139_, 1, v_ref_4136_);
lean_ctor_set(v_entry_4139_, 2, v_args_4137_);
lean_inc_ref(v_entry_4139_);
v___x_4140_ = l_Lean_mkAttributeImplOfEntry(v_entry_4139_);
if (lean_obj_tag(v___x_4140_) == 0)
{
lean_object* v_a_4141_; lean_object* v___x_4143_; uint8_t v_isShared_4144_; uint8_t v_isSharedCheck_4166_; 
v_a_4141_ = lean_ctor_get(v___x_4140_, 0);
v_isSharedCheck_4166_ = !lean_is_exclusive(v___x_4140_);
if (v_isSharedCheck_4166_ == 0)
{
v___x_4143_ = v___x_4140_;
v_isShared_4144_ = v_isSharedCheck_4166_;
goto v_resetjp_4142_;
}
else
{
lean_inc(v_a_4141_);
lean_dec(v___x_4140_);
v___x_4143_ = lean_box(0);
v_isShared_4144_ = v_isSharedCheck_4166_;
goto v_resetjp_4142_;
}
v_resetjp_4142_:
{
lean_object* v_toAttributeImplCore_4145_; lean_object* v_name_4146_; uint8_t v___x_4147_; 
v_toAttributeImplCore_4145_ = lean_ctor_get(v_a_4141_, 0);
v_name_4146_ = lean_ctor_get(v_toAttributeImplCore_4145_, 1);
lean_inc_ref(v_env_4134_);
v___x_4147_ = l_Lean_isAttribute(v_env_4134_, v_name_4146_);
if (v___x_4147_ == 0)
{
lean_object* v___x_4148_; lean_object* v_toEnvExtension_4149_; lean_object* v_asyncMode_4150_; lean_object* v___x_4151_; lean_object* v___x_4152_; lean_object* v___x_4153_; lean_object* v___x_4155_; 
v___x_4148_ = l_Lean_attributeExtension;
v_toEnvExtension_4149_ = lean_ctor_get(v___x_4148_, 0);
lean_inc_ref(v_toEnvExtension_4149_);
v_asyncMode_4150_ = lean_ctor_get(v_toEnvExtension_4149_, 2);
lean_inc(v_asyncMode_4150_);
lean_dec_ref(v_toEnvExtension_4149_);
v___x_4151_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4151_, 0, v_entry_4139_);
lean_ctor_set(v___x_4151_, 1, v_a_4141_);
v___x_4152_ = lean_box(0);
v___x_4153_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_4148_, v_env_4134_, v___x_4151_, v_asyncMode_4150_, v___x_4152_);
lean_dec(v_asyncMode_4150_);
if (v_isShared_4144_ == 0)
{
lean_ctor_set(v___x_4143_, 0, v___x_4153_);
v___x_4155_ = v___x_4143_;
goto v_reusejp_4154_;
}
else
{
lean_object* v_reuseFailAlloc_4156_; 
v_reuseFailAlloc_4156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4156_, 0, v___x_4153_);
v___x_4155_ = v_reuseFailAlloc_4156_;
goto v_reusejp_4154_;
}
v_reusejp_4154_:
{
return v___x_4155_;
}
}
else
{
lean_object* v___x_4157_; lean_object* v___x_4158_; lean_object* v___x_4159_; lean_object* v___x_4160_; lean_object* v___x_4161_; lean_object* v___x_4162_; lean_object* v___x_4164_; 
lean_inc(v_name_4146_);
lean_dec(v_a_4141_);
lean_dec_ref(v_entry_4139_);
lean_dec_ref(v_env_4134_);
v___x_4157_ = ((lean_object*)(l_Lean_registerBuiltinAttribute___closed__2));
v___x_4158_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_4146_, v___x_4147_);
v___x_4159_ = lean_string_append(v___x_4157_, v___x_4158_);
lean_dec_ref(v___x_4158_);
v___x_4160_ = ((lean_object*)(l_Lean_registerBuiltinAttribute___closed__3));
v___x_4161_ = lean_string_append(v___x_4159_, v___x_4160_);
v___x_4162_ = lean_mk_io_user_error(v___x_4161_);
if (v_isShared_4144_ == 0)
{
lean_ctor_set_tag(v___x_4143_, 1);
lean_ctor_set(v___x_4143_, 0, v___x_4162_);
v___x_4164_ = v___x_4143_;
goto v_reusejp_4163_;
}
else
{
lean_object* v_reuseFailAlloc_4165_; 
v_reuseFailAlloc_4165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4165_, 0, v___x_4162_);
v___x_4164_ = v_reuseFailAlloc_4165_;
goto v_reusejp_4163_;
}
v_reusejp_4163_:
{
return v___x_4164_;
}
}
}
}
else
{
lean_object* v_a_4167_; lean_object* v___x_4169_; uint8_t v_isShared_4170_; uint8_t v_isSharedCheck_4174_; 
lean_dec_ref(v_entry_4139_);
lean_dec_ref(v_env_4134_);
v_a_4167_ = lean_ctor_get(v___x_4140_, 0);
v_isSharedCheck_4174_ = !lean_is_exclusive(v___x_4140_);
if (v_isSharedCheck_4174_ == 0)
{
v___x_4169_ = v___x_4140_;
v_isShared_4170_ = v_isSharedCheck_4174_;
goto v_resetjp_4168_;
}
else
{
lean_inc(v_a_4167_);
lean_dec(v___x_4140_);
v___x_4169_ = lean_box(0);
v_isShared_4170_ = v_isSharedCheck_4174_;
goto v_resetjp_4168_;
}
v_resetjp_4168_:
{
lean_object* v___x_4172_; 
if (v_isShared_4170_ == 0)
{
v___x_4172_ = v___x_4169_;
goto v_reusejp_4171_;
}
else
{
lean_object* v_reuseFailAlloc_4173_; 
v_reuseFailAlloc_4173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4173_, 0, v_a_4167_);
v___x_4172_ = v_reuseFailAlloc_4173_;
goto v_reusejp_4171_;
}
v_reusejp_4171_:
{
return v___x_4172_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerAttributeOfBuilder___boxed(lean_object* v_env_4175_, lean_object* v_builderId_4176_, lean_object* v_ref_4177_, lean_object* v_args_4178_, lean_object* v_a_4179_){
_start:
{
lean_object* v_res_4180_; 
v_res_4180_ = l_Lean_registerAttributeOfBuilder(v_env_4175_, v_builderId_4176_, v_ref_4177_, v_args_4178_);
return v_res_4180_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg(lean_object* v_x_4181_, lean_object* v___y_4182_, lean_object* v___y_4183_){
_start:
{
if (lean_obj_tag(v_x_4181_) == 0)
{
lean_object* v_a_4185_; lean_object* v___x_4186_; lean_object* v___x_4187_; 
v_a_4185_ = lean_ctor_get(v_x_4181_, 0);
lean_inc(v_a_4185_);
lean_dec_ref(v_x_4181_);
v___x_4186_ = l_Lean_stringToMessageData(v_a_4185_);
v___x_4187_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0_spec__0___redArg(v___x_4186_, v___y_4182_, v___y_4183_);
return v___x_4187_;
}
else
{
lean_object* v_a_4188_; lean_object* v___x_4190_; uint8_t v_isShared_4191_; uint8_t v_isSharedCheck_4195_; 
v_a_4188_ = lean_ctor_get(v_x_4181_, 0);
v_isSharedCheck_4195_ = !lean_is_exclusive(v_x_4181_);
if (v_isSharedCheck_4195_ == 0)
{
v___x_4190_ = v_x_4181_;
v_isShared_4191_ = v_isSharedCheck_4195_;
goto v_resetjp_4189_;
}
else
{
lean_inc(v_a_4188_);
lean_dec(v_x_4181_);
v___x_4190_ = lean_box(0);
v_isShared_4191_ = v_isSharedCheck_4195_;
goto v_resetjp_4189_;
}
v_resetjp_4189_:
{
lean_object* v___x_4193_; 
if (v_isShared_4191_ == 0)
{
lean_ctor_set_tag(v___x_4190_, 0);
v___x_4193_ = v___x_4190_;
goto v_reusejp_4192_;
}
else
{
lean_object* v_reuseFailAlloc_4194_; 
v_reuseFailAlloc_4194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4194_, 0, v_a_4188_);
v___x_4193_ = v_reuseFailAlloc_4194_;
goto v_reusejp_4192_;
}
v_reusejp_4192_:
{
return v___x_4193_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg___boxed(lean_object* v_x_4196_, lean_object* v___y_4197_, lean_object* v___y_4198_, lean_object* v___y_4199_){
_start:
{
lean_object* v_res_4200_; 
v_res_4200_ = l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg(v_x_4196_, v___y_4197_, v___y_4198_);
lean_dec(v___y_4198_);
lean_dec_ref(v___y_4197_);
return v_res_4200_;
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_add(lean_object* v_declName_4201_, lean_object* v_attrName_4202_, lean_object* v_stx_4203_, uint8_t v_kind_4204_, lean_object* v_a_4205_, lean_object* v_a_4206_){
_start:
{
lean_object* v___x_4208_; lean_object* v_env_4209_; lean_object* v___x_4210_; lean_object* v___x_4211_; 
v___x_4208_ = lean_st_ref_get(v_a_4206_);
v_env_4209_ = lean_ctor_get(v___x_4208_, 0);
lean_inc_ref(v_env_4209_);
lean_dec(v___x_4208_);
v___x_4210_ = l_Lean_getAttributeImpl(v_env_4209_, v_attrName_4202_);
v___x_4211_ = l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg(v___x_4210_, v_a_4205_, v_a_4206_);
if (lean_obj_tag(v___x_4211_) == 0)
{
lean_object* v_a_4212_; lean_object* v_add_4213_; lean_object* v___x_4214_; lean_object* v___x_4215_; 
v_a_4212_ = lean_ctor_get(v___x_4211_, 0);
lean_inc(v_a_4212_);
lean_dec_ref(v___x_4211_);
v_add_4213_ = lean_ctor_get(v_a_4212_, 1);
lean_inc_ref(v_add_4213_);
lean_dec(v_a_4212_);
v___x_4214_ = lean_box(v_kind_4204_);
lean_inc(v_a_4206_);
lean_inc_ref(v_a_4205_);
v___x_4215_ = lean_apply_6(v_add_4213_, v_declName_4201_, v_stx_4203_, v___x_4214_, v_a_4205_, v_a_4206_, lean_box(0));
return v___x_4215_;
}
else
{
lean_object* v_a_4216_; lean_object* v___x_4218_; uint8_t v_isShared_4219_; uint8_t v_isSharedCheck_4223_; 
lean_dec(v_stx_4203_);
lean_dec(v_declName_4201_);
v_a_4216_ = lean_ctor_get(v___x_4211_, 0);
v_isSharedCheck_4223_ = !lean_is_exclusive(v___x_4211_);
if (v_isSharedCheck_4223_ == 0)
{
v___x_4218_ = v___x_4211_;
v_isShared_4219_ = v_isSharedCheck_4223_;
goto v_resetjp_4217_;
}
else
{
lean_inc(v_a_4216_);
lean_dec(v___x_4211_);
v___x_4218_ = lean_box(0);
v_isShared_4219_ = v_isSharedCheck_4223_;
goto v_resetjp_4217_;
}
v_resetjp_4217_:
{
lean_object* v___x_4221_; 
if (v_isShared_4219_ == 0)
{
v___x_4221_ = v___x_4218_;
goto v_reusejp_4220_;
}
else
{
lean_object* v_reuseFailAlloc_4222_; 
v_reuseFailAlloc_4222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4222_, 0, v_a_4216_);
v___x_4221_ = v_reuseFailAlloc_4222_;
goto v_reusejp_4220_;
}
v_reusejp_4220_:
{
return v___x_4221_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_add___boxed(lean_object* v_declName_4224_, lean_object* v_attrName_4225_, lean_object* v_stx_4226_, lean_object* v_kind_4227_, lean_object* v_a_4228_, lean_object* v_a_4229_, lean_object* v_a_4230_){
_start:
{
uint8_t v_kind_boxed_4231_; lean_object* v_res_4232_; 
v_kind_boxed_4231_ = lean_unbox(v_kind_4227_);
v_res_4232_ = l_Lean_Attribute_add(v_declName_4224_, v_attrName_4225_, v_stx_4226_, v_kind_boxed_4231_, v_a_4228_, v_a_4229_);
lean_dec(v_a_4229_);
lean_dec_ref(v_a_4228_);
return v_res_4232_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0(lean_object* v_00_u03b1_4233_, lean_object* v_x_4234_, lean_object* v___y_4235_, lean_object* v___y_4236_){
_start:
{
lean_object* v___x_4238_; 
v___x_4238_ = l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg(v_x_4234_, v___y_4235_, v___y_4236_);
return v___x_4238_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___boxed(lean_object* v_00_u03b1_4239_, lean_object* v_x_4240_, lean_object* v___y_4241_, lean_object* v___y_4242_, lean_object* v___y_4243_){
_start:
{
lean_object* v_res_4244_; 
v_res_4244_ = l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0(v_00_u03b1_4239_, v_x_4240_, v___y_4241_, v___y_4242_);
lean_dec(v___y_4242_);
lean_dec_ref(v___y_4241_);
return v_res_4244_;
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_erase(lean_object* v_declName_4245_, lean_object* v_attrName_4246_, lean_object* v_a_4247_, lean_object* v_a_4248_){
_start:
{
lean_object* v___x_4250_; lean_object* v_env_4251_; lean_object* v___x_4252_; lean_object* v___x_4253_; 
v___x_4250_ = lean_st_ref_get(v_a_4248_);
v_env_4251_ = lean_ctor_get(v___x_4250_, 0);
lean_inc_ref(v_env_4251_);
lean_dec(v___x_4250_);
v___x_4252_ = l_Lean_getAttributeImpl(v_env_4251_, v_attrName_4246_);
v___x_4253_ = l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg(v___x_4252_, v_a_4247_, v_a_4248_);
if (lean_obj_tag(v___x_4253_) == 0)
{
lean_object* v_a_4254_; lean_object* v_erase_4255_; lean_object* v___x_4256_; 
v_a_4254_ = lean_ctor_get(v___x_4253_, 0);
lean_inc(v_a_4254_);
lean_dec_ref(v___x_4253_);
v_erase_4255_ = lean_ctor_get(v_a_4254_, 2);
lean_inc_ref(v_erase_4255_);
lean_dec(v_a_4254_);
lean_inc(v_a_4248_);
lean_inc_ref(v_a_4247_);
v___x_4256_ = lean_apply_4(v_erase_4255_, v_declName_4245_, v_a_4247_, v_a_4248_, lean_box(0));
return v___x_4256_;
}
else
{
lean_object* v_a_4257_; lean_object* v___x_4259_; uint8_t v_isShared_4260_; uint8_t v_isSharedCheck_4264_; 
lean_dec(v_declName_4245_);
v_a_4257_ = lean_ctor_get(v___x_4253_, 0);
v_isSharedCheck_4264_ = !lean_is_exclusive(v___x_4253_);
if (v_isSharedCheck_4264_ == 0)
{
v___x_4259_ = v___x_4253_;
v_isShared_4260_ = v_isSharedCheck_4264_;
goto v_resetjp_4258_;
}
else
{
lean_inc(v_a_4257_);
lean_dec(v___x_4253_);
v___x_4259_ = lean_box(0);
v_isShared_4260_ = v_isSharedCheck_4264_;
goto v_resetjp_4258_;
}
v_resetjp_4258_:
{
lean_object* v___x_4262_; 
if (v_isShared_4260_ == 0)
{
v___x_4262_ = v___x_4259_;
goto v_reusejp_4261_;
}
else
{
lean_object* v_reuseFailAlloc_4263_; 
v_reuseFailAlloc_4263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4263_, 0, v_a_4257_);
v___x_4262_ = v_reuseFailAlloc_4263_;
goto v_reusejp_4261_;
}
v_reusejp_4261_:
{
return v___x_4262_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_erase___boxed(lean_object* v_declName_4265_, lean_object* v_attrName_4266_, lean_object* v_a_4267_, lean_object* v_a_4268_, lean_object* v_a_4269_){
_start:
{
lean_object* v_res_4270_; 
v_res_4270_ = l_Lean_Attribute_erase(v_declName_4265_, v_attrName_4266_, v_a_4267_, v_a_4268_);
lean_dec(v_a_4268_);
lean_dec_ref(v_a_4267_);
return v_res_4270_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_updateEnvAttributesImpl_spec__0(lean_object* v_x_4271_, lean_object* v_x_4272_){
_start:
{
if (lean_obj_tag(v_x_4272_) == 0)
{
return v_x_4271_;
}
else
{
lean_object* v_key_4273_; lean_object* v_value_4274_; lean_object* v_tail_4275_; lean_object* v_newEntries_4276_; lean_object* v_map_4277_; uint8_t v___x_4278_; 
v_key_4273_ = lean_ctor_get(v_x_4272_, 0);
lean_inc(v_key_4273_);
v_value_4274_ = lean_ctor_get(v_x_4272_, 1);
lean_inc(v_value_4274_);
v_tail_4275_ = lean_ctor_get(v_x_4272_, 2);
lean_inc(v_tail_4275_);
lean_dec_ref(v_x_4272_);
v_newEntries_4276_ = lean_ctor_get(v_x_4271_, 0);
v_map_4277_ = lean_ctor_get(v_x_4271_, 1);
v___x_4278_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(v_map_4277_, v_key_4273_);
if (v___x_4278_ == 0)
{
lean_object* v___x_4280_; uint8_t v_isShared_4281_; uint8_t v_isSharedCheck_4287_; 
lean_inc_ref(v_map_4277_);
lean_inc(v_newEntries_4276_);
v_isSharedCheck_4287_ = !lean_is_exclusive(v_x_4271_);
if (v_isSharedCheck_4287_ == 0)
{
lean_object* v_unused_4288_; lean_object* v_unused_4289_; 
v_unused_4288_ = lean_ctor_get(v_x_4271_, 1);
lean_dec(v_unused_4288_);
v_unused_4289_ = lean_ctor_get(v_x_4271_, 0);
lean_dec(v_unused_4289_);
v___x_4280_ = v_x_4271_;
v_isShared_4281_ = v_isSharedCheck_4287_;
goto v_resetjp_4279_;
}
else
{
lean_dec(v_x_4271_);
v___x_4280_ = lean_box(0);
v_isShared_4281_ = v_isSharedCheck_4287_;
goto v_resetjp_4279_;
}
v_resetjp_4279_:
{
lean_object* v___x_4282_; lean_object* v___x_4284_; 
v___x_4282_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1___redArg(v_map_4277_, v_key_4273_, v_value_4274_);
if (v_isShared_4281_ == 0)
{
lean_ctor_set(v___x_4280_, 1, v___x_4282_);
v___x_4284_ = v___x_4280_;
goto v_reusejp_4283_;
}
else
{
lean_object* v_reuseFailAlloc_4286_; 
v_reuseFailAlloc_4286_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4286_, 0, v_newEntries_4276_);
lean_ctor_set(v_reuseFailAlloc_4286_, 1, v___x_4282_);
v___x_4284_ = v_reuseFailAlloc_4286_;
goto v_reusejp_4283_;
}
v_reusejp_4283_:
{
v_x_4271_ = v___x_4284_;
v_x_4272_ = v_tail_4275_;
goto _start;
}
}
}
else
{
lean_dec(v_value_4274_);
lean_dec(v_key_4273_);
v_x_4272_ = v_tail_4275_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_updateEnvAttributesImpl_spec__1(lean_object* v_as_4291_, size_t v_i_4292_, size_t v_stop_4293_, lean_object* v_b_4294_){
_start:
{
uint8_t v___x_4295_; 
v___x_4295_ = lean_usize_dec_eq(v_i_4292_, v_stop_4293_);
if (v___x_4295_ == 0)
{
lean_object* v___x_4296_; lean_object* v___x_4297_; size_t v___x_4298_; size_t v___x_4299_; 
v___x_4296_ = lean_array_uget_borrowed(v_as_4291_, v_i_4292_);
lean_inc(v___x_4296_);
v___x_4297_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_updateEnvAttributesImpl_spec__0(v_b_4294_, v___x_4296_);
v___x_4298_ = ((size_t)1ULL);
v___x_4299_ = lean_usize_add(v_i_4292_, v___x_4298_);
v_i_4292_ = v___x_4299_;
v_b_4294_ = v___x_4297_;
goto _start;
}
else
{
return v_b_4294_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_updateEnvAttributesImpl_spec__1___boxed(lean_object* v_as_4301_, lean_object* v_i_4302_, lean_object* v_stop_4303_, lean_object* v_b_4304_){
_start:
{
size_t v_i_boxed_4305_; size_t v_stop_boxed_4306_; lean_object* v_res_4307_; 
v_i_boxed_4305_ = lean_unbox_usize(v_i_4302_);
lean_dec(v_i_4302_);
v_stop_boxed_4306_ = lean_unbox_usize(v_stop_4303_);
lean_dec(v_stop_4303_);
v_res_4307_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_updateEnvAttributesImpl_spec__1(v_as_4301_, v_i_boxed_4305_, v_stop_boxed_4306_, v_b_4304_);
lean_dec_ref(v_as_4301_);
return v_res_4307_;
}
}
LEAN_EXPORT lean_object* lean_update_env_attributes(lean_object* v_env_4308_){
_start:
{
lean_object* v___x_4310_; lean_object* v___x_4311_; lean_object* v___x_4312_; lean_object* v___y_4314_; lean_object* v_toEnvExtension_4317_; lean_object* v_asyncMode_4318_; lean_object* v_buckets_4319_; lean_object* v___x_4320_; lean_object* v___x_4321_; lean_object* v___x_4322_; lean_object* v___x_4323_; lean_object* v___x_4324_; uint8_t v___x_4325_; 
v___x_4310_ = l_Lean_attributeMapRef;
v___x_4311_ = lean_st_ref_get(v___x_4310_);
v___x_4312_ = l_Lean_attributeExtension;
v_toEnvExtension_4317_ = lean_ctor_get(v___x_4312_, 0);
lean_inc_ref(v_toEnvExtension_4317_);
v_asyncMode_4318_ = lean_ctor_get(v_toEnvExtension_4317_, 2);
lean_inc(v_asyncMode_4318_);
lean_dec_ref(v_toEnvExtension_4317_);
v_buckets_4319_ = lean_ctor_get(v___x_4311_, 1);
lean_inc_ref(v_buckets_4319_);
lean_dec(v___x_4311_);
v___x_4320_ = l_Lean_instInhabitedAttributeExtensionState_default;
v___x_4321_ = lean_box(0);
lean_inc_ref(v_env_4308_);
v___x_4322_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_4320_, v___x_4312_, v_env_4308_, v_asyncMode_4318_, v___x_4321_);
lean_dec(v_asyncMode_4318_);
v___x_4323_ = lean_unsigned_to_nat(0u);
v___x_4324_ = lean_array_get_size(v_buckets_4319_);
v___x_4325_ = lean_nat_dec_lt(v___x_4323_, v___x_4324_);
if (v___x_4325_ == 0)
{
lean_dec_ref(v_buckets_4319_);
v___y_4314_ = v___x_4322_;
goto v___jp_4313_;
}
else
{
uint8_t v___x_4326_; 
v___x_4326_ = lean_nat_dec_le(v___x_4324_, v___x_4324_);
if (v___x_4326_ == 0)
{
if (v___x_4325_ == 0)
{
lean_dec_ref(v_buckets_4319_);
v___y_4314_ = v___x_4322_;
goto v___jp_4313_;
}
else
{
size_t v___x_4327_; size_t v___x_4328_; lean_object* v___x_4329_; 
v___x_4327_ = ((size_t)0ULL);
v___x_4328_ = lean_usize_of_nat(v___x_4324_);
v___x_4329_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_updateEnvAttributesImpl_spec__1(v_buckets_4319_, v___x_4327_, v___x_4328_, v___x_4322_);
lean_dec_ref(v_buckets_4319_);
v___y_4314_ = v___x_4329_;
goto v___jp_4313_;
}
}
else
{
size_t v___x_4330_; size_t v___x_4331_; lean_object* v___x_4332_; 
v___x_4330_ = ((size_t)0ULL);
v___x_4331_ = lean_usize_of_nat(v___x_4324_);
v___x_4332_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_updateEnvAttributesImpl_spec__1(v_buckets_4319_, v___x_4330_, v___x_4331_, v___x_4322_);
lean_dec_ref(v_buckets_4319_);
v___y_4314_ = v___x_4332_;
goto v___jp_4313_;
}
}
v___jp_4313_:
{
lean_object* v___x_4315_; lean_object* v___x_4316_; 
v___x_4315_ = l_Lean_PersistentEnvExtension_setState___redArg(v___x_4312_, v_env_4308_, v___y_4314_);
v___x_4316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4316_, 0, v___x_4315_);
return v___x_4316_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_updateEnvAttributesImpl___boxed(lean_object* v_env_4333_, lean_object* v_a_4334_){
_start:
{
lean_object* v_res_4335_; 
v_res_4335_ = lean_update_env_attributes(v_env_4333_);
return v_res_4335_;
}
}
LEAN_EXPORT lean_object* lean_get_num_attributes(){
_start:
{
lean_object* v___x_4337_; lean_object* v___x_4338_; lean_object* v_size_4339_; lean_object* v___x_4340_; 
v___x_4337_ = l_Lean_attributeMapRef;
v___x_4338_ = lean_st_ref_get(v___x_4337_);
v_size_4339_ = lean_ctor_get(v___x_4338_, 0);
lean_inc(v_size_4339_);
lean_dec(v___x_4338_);
v___x_4340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4340_, 0, v_size_4339_);
return v___x_4340_;
}
}
LEAN_EXPORT lean_object* l_Lean_getNumBuiltinAttributesImpl___boxed(lean_object* v_a_4341_){
_start:
{
lean_object* v_res_4342_; 
v_res_4342_ = lean_get_num_attributes();
return v_res_4342_;
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
