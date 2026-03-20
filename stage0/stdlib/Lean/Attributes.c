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
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__4(lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___lam__4(lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___lam__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___lam__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_closure_object l_Lean_registerParametricAttribute___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_registerParametricAttribute___redArg___lam__4___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_registerParametricAttribute___redArg___closed__3_value)} };
static const lean_object* l_Lean_registerParametricAttribute___redArg___closed__4 = (const lean_object*)&l_Lean_registerParametricAttribute___redArg___closed__4_value;
static const lean_closure_object l_Lean_registerParametricAttribute___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_registerParametricAttribute___redArg___lam__5___boxed, .m_arity = 4, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_registerParametricAttribute___redArg___closed__3_value)} };
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
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_closure_object l_Lean_registerEnumAttributes___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_registerEnumAttributes___redArg___lam__5___boxed, .m_arity = 4, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))} };
static const lean_object* l_Lean_registerEnumAttributes___redArg___closed__5 = (const lean_object*)&l_Lean_registerEnumAttributes___redArg___closed__5_value;
static const lean_closure_object l_Lean_registerEnumAttributes___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_registerTagAttribute___lam__4___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))} };
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
lean_object* v_fileName_654_; lean_object* v_fileMap_655_; lean_object* v_options_656_; lean_object* v_currRecDepth_657_; lean_object* v_maxRecDepth_658_; lean_object* v_ref_659_; lean_object* v_currNamespace_660_; lean_object* v_openDecls_661_; lean_object* v_initHeartbeats_662_; lean_object* v_maxHeartbeats_663_; lean_object* v_quotContext_664_; lean_object* v_currMacroScope_665_; uint8_t v_diag_666_; lean_object* v_cancelTk_x3f_667_; uint8_t v_suppressElabErrors_668_; lean_object* v_inheritedTraceOptions_669_; lean_object* v___x_671_; uint8_t v_isShared_672_; uint8_t v_isSharedCheck_678_; 
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
v_isSharedCheck_678_ = !lean_is_exclusive(v___y_651_);
if (v_isSharedCheck_678_ == 0)
{
v___x_671_ = v___y_651_;
v_isShared_672_ = v_isSharedCheck_678_;
goto v_resetjp_670_;
}
else
{
lean_inc(v_inheritedTraceOptions_669_);
lean_inc(v_cancelTk_x3f_667_);
lean_inc(v_currMacroScope_665_);
lean_inc(v_quotContext_664_);
lean_inc(v_maxHeartbeats_663_);
lean_inc(v_initHeartbeats_662_);
lean_inc(v_openDecls_661_);
lean_inc(v_currNamespace_660_);
lean_inc(v_ref_659_);
lean_inc(v_maxRecDepth_658_);
lean_inc(v_currRecDepth_657_);
lean_inc(v_options_656_);
lean_inc(v_fileMap_655_);
lean_inc(v_fileName_654_);
lean_dec(v___y_651_);
v___x_671_ = lean_box(0);
v_isShared_672_ = v_isSharedCheck_678_;
goto v_resetjp_670_;
}
v_resetjp_670_:
{
lean_object* v_ref_673_; lean_object* v___x_675_; 
v_ref_673_ = l_Lean_replaceRef(v_ref_649_, v_ref_659_);
lean_dec(v_ref_659_);
if (v_isShared_672_ == 0)
{
lean_ctor_set(v___x_671_, 5, v_ref_673_);
v___x_675_ = v___x_671_;
goto v_reusejp_674_;
}
else
{
lean_object* v_reuseFailAlloc_677_; 
v_reuseFailAlloc_677_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_677_, 0, v_fileName_654_);
lean_ctor_set(v_reuseFailAlloc_677_, 1, v_fileMap_655_);
lean_ctor_set(v_reuseFailAlloc_677_, 2, v_options_656_);
lean_ctor_set(v_reuseFailAlloc_677_, 3, v_currRecDepth_657_);
lean_ctor_set(v_reuseFailAlloc_677_, 4, v_maxRecDepth_658_);
lean_ctor_set(v_reuseFailAlloc_677_, 5, v_ref_673_);
lean_ctor_set(v_reuseFailAlloc_677_, 6, v_currNamespace_660_);
lean_ctor_set(v_reuseFailAlloc_677_, 7, v_openDecls_661_);
lean_ctor_set(v_reuseFailAlloc_677_, 8, v_initHeartbeats_662_);
lean_ctor_set(v_reuseFailAlloc_677_, 9, v_maxHeartbeats_663_);
lean_ctor_set(v_reuseFailAlloc_677_, 10, v_quotContext_664_);
lean_ctor_set(v_reuseFailAlloc_677_, 11, v_currMacroScope_665_);
lean_ctor_set(v_reuseFailAlloc_677_, 12, v_cancelTk_x3f_667_);
lean_ctor_set(v_reuseFailAlloc_677_, 13, v_inheritedTraceOptions_669_);
lean_ctor_set_uint8(v_reuseFailAlloc_677_, sizeof(void*)*14, v_diag_666_);
lean_ctor_set_uint8(v_reuseFailAlloc_677_, sizeof(void*)*14 + 1, v_suppressElabErrors_668_);
v___x_675_ = v_reuseFailAlloc_677_;
goto v_reusejp_674_;
}
v_reusejp_674_:
{
lean_object* v___x_676_; 
v___x_676_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0_spec__0___redArg(v_msg_650_, v___x_675_, v___y_652_);
lean_dec_ref(v___x_675_);
return v___x_676_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg___boxed(lean_object* v_ref_679_, lean_object* v_msg_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_){
_start:
{
lean_object* v_res_684_; 
v_res_684_ = l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg(v_ref_679_, v_msg_680_, v___y_681_, v___y_682_);
lean_dec(v___y_682_);
lean_dec(v_ref_679_);
return v_res_684_;
}
}
static lean_object* _init_l_Lean_Attribute_Builtin_ensureNoArgs___closed__4(void){
_start:
{
lean_object* v___x_693_; lean_object* v___x_694_; 
v___x_693_ = ((lean_object*)(l_Lean_Attribute_Builtin_ensureNoArgs___closed__3));
v___x_694_ = l_Lean_stringToMessageData(v___x_693_);
return v___x_694_;
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_ensureNoArgs(lean_object* v_stx_701_, lean_object* v_a_702_, lean_object* v_a_703_){
_start:
{
lean_object* v___x_705_; uint8_t v___y_716_; lean_object* v___x_722_; uint8_t v___x_723_; 
lean_inc(v_stx_701_);
v___x_705_ = l_Lean_Syntax_getKind(v_stx_701_);
v___x_722_ = ((lean_object*)(l_Lean_Attribute_Builtin_ensureNoArgs___closed__6));
v___x_723_ = lean_name_eq(v___x_705_, v___x_722_);
if (v___x_723_ == 0)
{
v___y_716_ = v___x_723_;
goto v___jp_715_;
}
else
{
lean_object* v___x_724_; lean_object* v___x_725_; uint8_t v___x_726_; 
v___x_724_ = lean_unsigned_to_nat(1u);
v___x_725_ = l_Lean_Syntax_getArg(v_stx_701_, v___x_724_);
v___x_726_ = l_Lean_Syntax_isNone(v___x_725_);
lean_dec(v___x_725_);
v___y_716_ = v___x_726_;
goto v___jp_715_;
}
v___jp_706_:
{
lean_object* v___x_707_; uint8_t v___x_708_; 
v___x_707_ = ((lean_object*)(l_Lean_Attribute_Builtin_ensureNoArgs___closed__2));
v___x_708_ = lean_name_eq(v___x_705_, v___x_707_);
lean_dec(v___x_705_);
if (v___x_708_ == 0)
{
if (lean_obj_tag(v_stx_701_) == 0)
{
lean_object* v___x_709_; lean_object* v___x_710_; 
lean_dec_ref(v_a_702_);
v___x_709_ = lean_box(0);
v___x_710_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_710_, 0, v___x_709_);
return v___x_710_;
}
else
{
lean_object* v___x_711_; lean_object* v___x_712_; 
v___x_711_ = lean_obj_once(&l_Lean_Attribute_Builtin_ensureNoArgs___closed__4, &l_Lean_Attribute_Builtin_ensureNoArgs___closed__4_once, _init_l_Lean_Attribute_Builtin_ensureNoArgs___closed__4);
v___x_712_ = l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg(v_stx_701_, v___x_711_, v_a_702_, v_a_703_);
lean_dec(v_stx_701_);
return v___x_712_;
}
}
else
{
lean_object* v___x_713_; lean_object* v___x_714_; 
lean_dec_ref(v_a_702_);
lean_dec(v_stx_701_);
v___x_713_ = lean_box(0);
v___x_714_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_714_, 0, v___x_713_);
return v___x_714_;
}
}
v___jp_715_:
{
if (v___y_716_ == 0)
{
goto v___jp_706_;
}
else
{
lean_object* v___x_717_; lean_object* v___x_718_; uint8_t v___x_719_; 
v___x_717_ = lean_unsigned_to_nat(2u);
v___x_718_ = l_Lean_Syntax_getArg(v_stx_701_, v___x_717_);
v___x_719_ = l_Lean_Syntax_isNone(v___x_718_);
lean_dec(v___x_718_);
if (v___x_719_ == 0)
{
goto v___jp_706_;
}
else
{
lean_object* v___x_720_; lean_object* v___x_721_; 
lean_dec(v___x_705_);
lean_dec_ref(v_a_702_);
lean_dec(v_stx_701_);
v___x_720_ = lean_box(0);
v___x_721_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_721_, 0, v___x_720_);
return v___x_721_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_ensureNoArgs___boxed(lean_object* v_stx_727_, lean_object* v_a_728_, lean_object* v_a_729_, lean_object* v_a_730_){
_start:
{
lean_object* v_res_731_; 
v_res_731_ = l_Lean_Attribute_Builtin_ensureNoArgs(v_stx_727_, v_a_728_, v_a_729_);
lean_dec(v_a_729_);
return v_res_731_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0(lean_object* v_00_u03b1_732_, lean_object* v_ref_733_, lean_object* v_msg_734_, lean_object* v___y_735_, lean_object* v___y_736_){
_start:
{
lean_object* v___x_738_; 
v___x_738_ = l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg(v_ref_733_, v_msg_734_, v___y_735_, v___y_736_);
return v___x_738_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___boxed(lean_object* v_00_u03b1_739_, lean_object* v_ref_740_, lean_object* v_msg_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_){
_start:
{
lean_object* v_res_745_; 
v_res_745_ = l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0(v_00_u03b1_739_, v_ref_740_, v_msg_741_, v___y_742_, v___y_743_);
lean_dec(v___y_743_);
lean_dec(v_ref_740_);
return v_res_745_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0_spec__0(lean_object* v_00_u03b1_746_, lean_object* v_msg_747_, lean_object* v___y_748_, lean_object* v___y_749_){
_start:
{
lean_object* v___x_751_; 
v___x_751_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0_spec__0___redArg(v_msg_747_, v___y_748_, v___y_749_);
return v___x_751_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0_spec__0___boxed(lean_object* v_00_u03b1_752_, lean_object* v_msg_753_, lean_object* v___y_754_, lean_object* v___y_755_, lean_object* v___y_756_){
_start:
{
lean_object* v_res_757_; 
v_res_757_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0_spec__0(v_00_u03b1_752_, v_msg_753_, v___y_754_, v___y_755_);
lean_dec(v___y_755_);
lean_dec_ref(v___y_754_);
return v_res_757_;
}
}
static lean_object* _init_l_Lean_Attribute_Builtin_getIdent_x3f___closed__5(void){
_start:
{
lean_object* v___x_771_; lean_object* v___x_772_; 
v___x_771_ = ((lean_object*)(l_Lean_Attribute_Builtin_getIdent_x3f___closed__4));
v___x_772_ = l_Lean_stringToMessageData(v___x_771_);
return v___x_772_;
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getIdent_x3f(lean_object* v_stx_773_, lean_object* v_a_774_, lean_object* v_a_775_){
_start:
{
lean_object* v___x_785_; lean_object* v___x_786_; uint8_t v___x_787_; 
lean_inc(v_stx_773_);
v___x_785_ = l_Lean_Syntax_getKind(v_stx_773_);
v___x_786_ = ((lean_object*)(l_Lean_Attribute_Builtin_ensureNoArgs___closed__6));
v___x_787_ = lean_name_eq(v___x_785_, v___x_786_);
if (v___x_787_ == 0)
{
lean_object* v___x_788_; uint8_t v___x_789_; 
v___x_788_ = ((lean_object*)(l_Lean_Attribute_Builtin_getIdent_x3f___closed__1));
v___x_789_ = lean_name_eq(v___x_785_, v___x_788_);
if (v___x_789_ == 0)
{
lean_object* v___x_790_; uint8_t v___x_791_; 
v___x_790_ = ((lean_object*)(l_Lean_Attribute_Builtin_getIdent_x3f___closed__3));
v___x_791_ = lean_name_eq(v___x_785_, v___x_790_);
lean_dec(v___x_785_);
if (v___x_791_ == 0)
{
lean_object* v___x_792_; lean_object* v___x_793_; 
v___x_792_ = lean_obj_once(&l_Lean_Attribute_Builtin_getIdent_x3f___closed__5, &l_Lean_Attribute_Builtin_getIdent_x3f___closed__5_once, _init_l_Lean_Attribute_Builtin_getIdent_x3f___closed__5);
v___x_793_ = l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg(v_stx_773_, v___x_792_, v_a_774_, v_a_775_);
lean_dec(v_stx_773_);
return v___x_793_;
}
else
{
lean_dec_ref(v_a_774_);
goto v___jp_777_;
}
}
else
{
lean_dec(v___x_785_);
lean_dec_ref(v_a_774_);
goto v___jp_777_;
}
}
else
{
lean_object* v___x_794_; lean_object* v___x_795_; uint8_t v___x_796_; 
lean_dec(v___x_785_);
lean_dec_ref(v_a_774_);
v___x_794_ = lean_unsigned_to_nat(1u);
v___x_795_ = l_Lean_Syntax_getArg(v_stx_773_, v___x_794_);
lean_dec(v_stx_773_);
v___x_796_ = l_Lean_Syntax_isNone(v___x_795_);
if (v___x_796_ == 0)
{
if (v___x_787_ == 0)
{
lean_dec(v___x_795_);
goto v___jp_782_;
}
else
{
lean_object* v___x_797_; lean_object* v___x_798_; uint8_t v___x_799_; 
v___x_797_ = lean_unsigned_to_nat(0u);
v___x_798_ = l_Lean_Syntax_getArg(v___x_795_, v___x_797_);
lean_dec(v___x_795_);
v___x_799_ = l_Lean_Syntax_isIdent(v___x_798_);
if (v___x_799_ == 0)
{
lean_dec(v___x_798_);
goto v___jp_782_;
}
else
{
lean_object* v___x_800_; lean_object* v___x_801_; 
v___x_800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_800_, 0, v___x_798_);
v___x_801_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_801_, 0, v___x_800_);
return v___x_801_;
}
}
}
else
{
lean_dec(v___x_795_);
goto v___jp_782_;
}
}
v___jp_777_:
{
lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; 
v___x_778_ = lean_unsigned_to_nat(1u);
v___x_779_ = l_Lean_Syntax_getArg(v_stx_773_, v___x_778_);
lean_dec(v_stx_773_);
v___x_780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_780_, 0, v___x_779_);
v___x_781_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_781_, 0, v___x_780_);
return v___x_781_;
}
v___jp_782_:
{
lean_object* v___x_783_; lean_object* v___x_784_; 
v___x_783_ = lean_box(0);
v___x_784_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_784_, 0, v___x_783_);
return v___x_784_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getIdent_x3f___boxed(lean_object* v_stx_802_, lean_object* v_a_803_, lean_object* v_a_804_, lean_object* v_a_805_){
_start:
{
lean_object* v_res_806_; 
v_res_806_ = l_Lean_Attribute_Builtin_getIdent_x3f(v_stx_802_, v_a_803_, v_a_804_);
lean_dec(v_a_804_);
return v_res_806_;
}
}
static lean_object* _init_l_Lean_Attribute_Builtin_getIdent___closed__1(void){
_start:
{
lean_object* v___x_808_; lean_object* v___x_809_; 
v___x_808_ = ((lean_object*)(l_Lean_Attribute_Builtin_getIdent___closed__0));
v___x_809_ = l_Lean_stringToMessageData(v___x_808_);
return v___x_809_;
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getIdent(lean_object* v_stx_810_, lean_object* v_a_811_, lean_object* v_a_812_){
_start:
{
lean_object* v___x_814_; 
lean_inc_ref(v_a_811_);
lean_inc(v_stx_810_);
v___x_814_ = l_Lean_Attribute_Builtin_getIdent_x3f(v_stx_810_, v_a_811_, v_a_812_);
if (lean_obj_tag(v___x_814_) == 0)
{
lean_object* v_a_815_; lean_object* v___x_817_; uint8_t v_isShared_818_; uint8_t v_isSharedCheck_828_; 
v_a_815_ = lean_ctor_get(v___x_814_, 0);
v_isSharedCheck_828_ = !lean_is_exclusive(v___x_814_);
if (v_isSharedCheck_828_ == 0)
{
v___x_817_ = v___x_814_;
v_isShared_818_ = v_isSharedCheck_828_;
goto v_resetjp_816_;
}
else
{
lean_inc(v_a_815_);
lean_dec(v___x_814_);
v___x_817_ = lean_box(0);
v_isShared_818_ = v_isSharedCheck_828_;
goto v_resetjp_816_;
}
v_resetjp_816_:
{
if (lean_obj_tag(v_a_815_) == 0)
{
lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; 
lean_del_object(v___x_817_);
v___x_819_ = lean_obj_once(&l_Lean_Attribute_Builtin_getIdent___closed__1, &l_Lean_Attribute_Builtin_getIdent___closed__1_once, _init_l_Lean_Attribute_Builtin_getIdent___closed__1);
lean_inc(v_stx_810_);
v___x_820_ = l_Lean_MessageData_ofSyntax(v_stx_810_);
v___x_821_ = l_Lean_indentD(v___x_820_);
v___x_822_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_822_, 0, v___x_819_);
lean_ctor_set(v___x_822_, 1, v___x_821_);
v___x_823_ = l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg(v_stx_810_, v___x_822_, v_a_811_, v_a_812_);
lean_dec(v_stx_810_);
return v___x_823_;
}
else
{
lean_object* v_val_824_; lean_object* v___x_826_; 
lean_dec_ref(v_a_811_);
lean_dec(v_stx_810_);
v_val_824_ = lean_ctor_get(v_a_815_, 0);
lean_inc(v_val_824_);
lean_dec_ref(v_a_815_);
if (v_isShared_818_ == 0)
{
lean_ctor_set(v___x_817_, 0, v_val_824_);
v___x_826_ = v___x_817_;
goto v_reusejp_825_;
}
else
{
lean_object* v_reuseFailAlloc_827_; 
v_reuseFailAlloc_827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_827_, 0, v_val_824_);
v___x_826_ = v_reuseFailAlloc_827_;
goto v_reusejp_825_;
}
v_reusejp_825_:
{
return v___x_826_;
}
}
}
}
else
{
lean_object* v_a_829_; lean_object* v___x_831_; uint8_t v_isShared_832_; uint8_t v_isSharedCheck_836_; 
lean_dec_ref(v_a_811_);
lean_dec(v_stx_810_);
v_a_829_ = lean_ctor_get(v___x_814_, 0);
v_isSharedCheck_836_ = !lean_is_exclusive(v___x_814_);
if (v_isSharedCheck_836_ == 0)
{
v___x_831_ = v___x_814_;
v_isShared_832_ = v_isSharedCheck_836_;
goto v_resetjp_830_;
}
else
{
lean_inc(v_a_829_);
lean_dec(v___x_814_);
v___x_831_ = lean_box(0);
v_isShared_832_ = v_isSharedCheck_836_;
goto v_resetjp_830_;
}
v_resetjp_830_:
{
lean_object* v___x_834_; 
if (v_isShared_832_ == 0)
{
v___x_834_ = v___x_831_;
goto v_reusejp_833_;
}
else
{
lean_object* v_reuseFailAlloc_835_; 
v_reuseFailAlloc_835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_835_, 0, v_a_829_);
v___x_834_ = v_reuseFailAlloc_835_;
goto v_reusejp_833_;
}
v_reusejp_833_:
{
return v___x_834_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getIdent___boxed(lean_object* v_stx_837_, lean_object* v_a_838_, lean_object* v_a_839_, lean_object* v_a_840_){
_start:
{
lean_object* v_res_841_; 
v_res_841_ = l_Lean_Attribute_Builtin_getIdent(v_stx_837_, v_a_838_, v_a_839_);
lean_dec(v_a_839_);
return v_res_841_;
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getId_x3f(lean_object* v_stx_842_, lean_object* v_a_843_, lean_object* v_a_844_){
_start:
{
lean_object* v___x_846_; 
v___x_846_ = l_Lean_Attribute_Builtin_getIdent_x3f(v_stx_842_, v_a_843_, v_a_844_);
if (lean_obj_tag(v___x_846_) == 0)
{
lean_object* v_a_847_; lean_object* v___x_849_; uint8_t v_isShared_850_; uint8_t v_isSharedCheck_867_; 
v_a_847_ = lean_ctor_get(v___x_846_, 0);
v_isSharedCheck_867_ = !lean_is_exclusive(v___x_846_);
if (v_isSharedCheck_867_ == 0)
{
v___x_849_ = v___x_846_;
v_isShared_850_ = v_isSharedCheck_867_;
goto v_resetjp_848_;
}
else
{
lean_inc(v_a_847_);
lean_dec(v___x_846_);
v___x_849_ = lean_box(0);
v_isShared_850_ = v_isSharedCheck_867_;
goto v_resetjp_848_;
}
v_resetjp_848_:
{
if (lean_obj_tag(v_a_847_) == 0)
{
lean_object* v___x_851_; lean_object* v___x_853_; 
v___x_851_ = lean_box(0);
if (v_isShared_850_ == 0)
{
lean_ctor_set(v___x_849_, 0, v___x_851_);
v___x_853_ = v___x_849_;
goto v_reusejp_852_;
}
else
{
lean_object* v_reuseFailAlloc_854_; 
v_reuseFailAlloc_854_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_854_, 0, v___x_851_);
v___x_853_ = v_reuseFailAlloc_854_;
goto v_reusejp_852_;
}
v_reusejp_852_:
{
return v___x_853_;
}
}
else
{
lean_object* v_val_855_; lean_object* v___x_857_; uint8_t v_isShared_858_; uint8_t v_isSharedCheck_866_; 
v_val_855_ = lean_ctor_get(v_a_847_, 0);
v_isSharedCheck_866_ = !lean_is_exclusive(v_a_847_);
if (v_isSharedCheck_866_ == 0)
{
v___x_857_ = v_a_847_;
v_isShared_858_ = v_isSharedCheck_866_;
goto v_resetjp_856_;
}
else
{
lean_inc(v_val_855_);
lean_dec(v_a_847_);
v___x_857_ = lean_box(0);
v_isShared_858_ = v_isSharedCheck_866_;
goto v_resetjp_856_;
}
v_resetjp_856_:
{
lean_object* v___x_859_; lean_object* v___x_861_; 
v___x_859_ = l_Lean_Syntax_getId(v_val_855_);
lean_dec(v_val_855_);
if (v_isShared_858_ == 0)
{
lean_ctor_set(v___x_857_, 0, v___x_859_);
v___x_861_ = v___x_857_;
goto v_reusejp_860_;
}
else
{
lean_object* v_reuseFailAlloc_865_; 
v_reuseFailAlloc_865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_865_, 0, v___x_859_);
v___x_861_ = v_reuseFailAlloc_865_;
goto v_reusejp_860_;
}
v_reusejp_860_:
{
lean_object* v___x_863_; 
if (v_isShared_850_ == 0)
{
lean_ctor_set(v___x_849_, 0, v___x_861_);
v___x_863_ = v___x_849_;
goto v_reusejp_862_;
}
else
{
lean_object* v_reuseFailAlloc_864_; 
v_reuseFailAlloc_864_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_864_, 0, v___x_861_);
v___x_863_ = v_reuseFailAlloc_864_;
goto v_reusejp_862_;
}
v_reusejp_862_:
{
return v___x_863_;
}
}
}
}
}
}
else
{
lean_object* v_a_868_; lean_object* v___x_870_; uint8_t v_isShared_871_; uint8_t v_isSharedCheck_875_; 
v_a_868_ = lean_ctor_get(v___x_846_, 0);
v_isSharedCheck_875_ = !lean_is_exclusive(v___x_846_);
if (v_isSharedCheck_875_ == 0)
{
v___x_870_ = v___x_846_;
v_isShared_871_ = v_isSharedCheck_875_;
goto v_resetjp_869_;
}
else
{
lean_inc(v_a_868_);
lean_dec(v___x_846_);
v___x_870_ = lean_box(0);
v_isShared_871_ = v_isSharedCheck_875_;
goto v_resetjp_869_;
}
v_resetjp_869_:
{
lean_object* v___x_873_; 
if (v_isShared_871_ == 0)
{
v___x_873_ = v___x_870_;
goto v_reusejp_872_;
}
else
{
lean_object* v_reuseFailAlloc_874_; 
v_reuseFailAlloc_874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_874_, 0, v_a_868_);
v___x_873_ = v_reuseFailAlloc_874_;
goto v_reusejp_872_;
}
v_reusejp_872_:
{
return v___x_873_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getId_x3f___boxed(lean_object* v_stx_876_, lean_object* v_a_877_, lean_object* v_a_878_, lean_object* v_a_879_){
_start:
{
lean_object* v_res_880_; 
v_res_880_ = l_Lean_Attribute_Builtin_getId_x3f(v_stx_876_, v_a_877_, v_a_878_);
lean_dec(v_a_878_);
return v_res_880_;
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getId(lean_object* v_stx_881_, lean_object* v_a_882_, lean_object* v_a_883_){
_start:
{
lean_object* v___x_885_; 
v___x_885_ = l_Lean_Attribute_Builtin_getIdent(v_stx_881_, v_a_882_, v_a_883_);
if (lean_obj_tag(v___x_885_) == 0)
{
lean_object* v_a_886_; lean_object* v___x_888_; uint8_t v_isShared_889_; uint8_t v_isSharedCheck_894_; 
v_a_886_ = lean_ctor_get(v___x_885_, 0);
v_isSharedCheck_894_ = !lean_is_exclusive(v___x_885_);
if (v_isSharedCheck_894_ == 0)
{
v___x_888_ = v___x_885_;
v_isShared_889_ = v_isSharedCheck_894_;
goto v_resetjp_887_;
}
else
{
lean_inc(v_a_886_);
lean_dec(v___x_885_);
v___x_888_ = lean_box(0);
v_isShared_889_ = v_isSharedCheck_894_;
goto v_resetjp_887_;
}
v_resetjp_887_:
{
lean_object* v___x_890_; lean_object* v___x_892_; 
v___x_890_ = l_Lean_Syntax_getId(v_a_886_);
lean_dec(v_a_886_);
if (v_isShared_889_ == 0)
{
lean_ctor_set(v___x_888_, 0, v___x_890_);
v___x_892_ = v___x_888_;
goto v_reusejp_891_;
}
else
{
lean_object* v_reuseFailAlloc_893_; 
v_reuseFailAlloc_893_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_893_, 0, v___x_890_);
v___x_892_ = v_reuseFailAlloc_893_;
goto v_reusejp_891_;
}
v_reusejp_891_:
{
return v___x_892_;
}
}
}
else
{
lean_object* v_a_895_; lean_object* v___x_897_; uint8_t v_isShared_898_; uint8_t v_isSharedCheck_902_; 
v_a_895_ = lean_ctor_get(v___x_885_, 0);
v_isSharedCheck_902_ = !lean_is_exclusive(v___x_885_);
if (v_isSharedCheck_902_ == 0)
{
v___x_897_ = v___x_885_;
v_isShared_898_ = v_isSharedCheck_902_;
goto v_resetjp_896_;
}
else
{
lean_inc(v_a_895_);
lean_dec(v___x_885_);
v___x_897_ = lean_box(0);
v_isShared_898_ = v_isSharedCheck_902_;
goto v_resetjp_896_;
}
v_resetjp_896_:
{
lean_object* v___x_900_; 
if (v_isShared_898_ == 0)
{
v___x_900_ = v___x_897_;
goto v_reusejp_899_;
}
else
{
lean_object* v_reuseFailAlloc_901_; 
v_reuseFailAlloc_901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_901_, 0, v_a_895_);
v___x_900_ = v_reuseFailAlloc_901_;
goto v_reusejp_899_;
}
v_reusejp_899_:
{
return v___x_900_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getId___boxed(lean_object* v_stx_903_, lean_object* v_a_904_, lean_object* v_a_905_, lean_object* v_a_906_){
_start:
{
lean_object* v_res_907_; 
v_res_907_ = l_Lean_Attribute_Builtin_getId(v_stx_903_, v_a_904_, v_a_905_);
lean_dec(v_a_905_);
return v_res_907_;
}
}
static lean_object* _init_l_Lean_getAttrParamOptPrio___closed__1(void){
_start:
{
lean_object* v___x_909_; lean_object* v___x_910_; 
v___x_909_ = ((lean_object*)(l_Lean_getAttrParamOptPrio___closed__0));
v___x_910_ = l_Lean_stringToMessageData(v___x_909_);
return v___x_910_;
}
}
LEAN_EXPORT lean_object* l_Lean_getAttrParamOptPrio(lean_object* v_optPrioStx_911_, lean_object* v_a_912_, lean_object* v_a_913_){
_start:
{
uint8_t v___x_915_; 
v___x_915_ = l_Lean_Syntax_isNone(v_optPrioStx_911_);
if (v___x_915_ == 0)
{
lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; 
v___x_916_ = lean_unsigned_to_nat(0u);
v___x_917_ = l_Lean_Syntax_getArg(v_optPrioStx_911_, v___x_916_);
v___x_918_ = l_Lean_Syntax_isNatLit_x3f(v___x_917_);
lean_dec(v___x_917_);
if (lean_obj_tag(v___x_918_) == 0)
{
lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; 
v___x_919_ = lean_obj_once(&l_Lean_getAttrParamOptPrio___closed__1, &l_Lean_getAttrParamOptPrio___closed__1_once, _init_l_Lean_getAttrParamOptPrio___closed__1);
lean_inc(v_optPrioStx_911_);
v___x_920_ = l_Lean_MessageData_ofSyntax(v_optPrioStx_911_);
v___x_921_ = l_Lean_indentD(v___x_920_);
v___x_922_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_922_, 0, v___x_919_);
lean_ctor_set(v___x_922_, 1, v___x_921_);
v___x_923_ = l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg(v_optPrioStx_911_, v___x_922_, v_a_912_, v_a_913_);
lean_dec(v_optPrioStx_911_);
return v___x_923_;
}
else
{
lean_object* v_val_924_; lean_object* v___x_926_; uint8_t v_isShared_927_; uint8_t v_isSharedCheck_931_; 
lean_dec_ref(v_a_912_);
lean_dec(v_optPrioStx_911_);
v_val_924_ = lean_ctor_get(v___x_918_, 0);
v_isSharedCheck_931_ = !lean_is_exclusive(v___x_918_);
if (v_isSharedCheck_931_ == 0)
{
v___x_926_ = v___x_918_;
v_isShared_927_ = v_isSharedCheck_931_;
goto v_resetjp_925_;
}
else
{
lean_inc(v_val_924_);
lean_dec(v___x_918_);
v___x_926_ = lean_box(0);
v_isShared_927_ = v_isSharedCheck_931_;
goto v_resetjp_925_;
}
v_resetjp_925_:
{
lean_object* v___x_929_; 
if (v_isShared_927_ == 0)
{
lean_ctor_set_tag(v___x_926_, 0);
v___x_929_ = v___x_926_;
goto v_reusejp_928_;
}
else
{
lean_object* v_reuseFailAlloc_930_; 
v_reuseFailAlloc_930_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_930_, 0, v_val_924_);
v___x_929_ = v_reuseFailAlloc_930_;
goto v_reusejp_928_;
}
v_reusejp_928_:
{
return v___x_929_;
}
}
}
}
else
{
lean_object* v___x_932_; lean_object* v___x_933_; 
lean_dec_ref(v_a_912_);
lean_dec(v_optPrioStx_911_);
v___x_932_ = lean_unsigned_to_nat(1000u);
v___x_933_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_933_, 0, v___x_932_);
return v___x_933_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getAttrParamOptPrio___boxed(lean_object* v_optPrioStx_934_, lean_object* v_a_935_, lean_object* v_a_936_, lean_object* v_a_937_){
_start:
{
lean_object* v_res_938_; 
v_res_938_ = l_Lean_getAttrParamOptPrio(v_optPrioStx_934_, v_a_935_, v_a_936_);
lean_dec(v_a_936_);
return v_res_938_;
}
}
static lean_object* _init_l_Lean_Attribute_Builtin_getPrio___closed__1(void){
_start:
{
lean_object* v___x_940_; lean_object* v___x_941_; 
v___x_940_ = ((lean_object*)(l_Lean_Attribute_Builtin_getPrio___closed__0));
v___x_941_ = l_Lean_stringToMessageData(v___x_940_);
return v___x_941_;
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getPrio(lean_object* v_stx_942_, lean_object* v_a_943_, lean_object* v_a_944_){
_start:
{
lean_object* v___x_946_; lean_object* v___x_947_; uint8_t v___x_948_; 
lean_inc(v_stx_942_);
v___x_946_ = l_Lean_Syntax_getKind(v_stx_942_);
v___x_947_ = ((lean_object*)(l_Lean_Attribute_Builtin_ensureNoArgs___closed__6));
v___x_948_ = lean_name_eq(v___x_946_, v___x_947_);
lean_dec(v___x_946_);
if (v___x_948_ == 0)
{
lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; 
v___x_949_ = lean_obj_once(&l_Lean_Attribute_Builtin_getPrio___closed__1, &l_Lean_Attribute_Builtin_getPrio___closed__1_once, _init_l_Lean_Attribute_Builtin_getPrio___closed__1);
lean_inc(v_stx_942_);
v___x_950_ = l_Lean_MessageData_ofSyntax(v_stx_942_);
v___x_951_ = l_Lean_indentD(v___x_950_);
v___x_952_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_952_, 0, v___x_949_);
lean_ctor_set(v___x_952_, 1, v___x_951_);
v___x_953_ = l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg(v_stx_942_, v___x_952_, v_a_943_, v_a_944_);
lean_dec(v_stx_942_);
return v___x_953_;
}
else
{
lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; 
v___x_954_ = lean_unsigned_to_nat(1u);
v___x_955_ = l_Lean_Syntax_getArg(v_stx_942_, v___x_954_);
lean_dec(v_stx_942_);
v___x_956_ = l_Lean_getAttrParamOptPrio(v___x_955_, v_a_943_, v_a_944_);
return v___x_956_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getPrio___boxed(lean_object* v_stx_957_, lean_object* v_a_958_, lean_object* v_a_959_, lean_object* v_a_960_){
_start:
{
lean_object* v_res_961_; 
v_res_961_ = l_Lean_Attribute_Builtin_getPrio(v_stx_957_, v_a_958_, v_a_959_);
lean_dec(v_a_959_);
return v_res_961_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__1(void){
_start:
{
lean_object* v___x_963_; lean_object* v___x_964_; 
v___x_963_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__0));
v___x_964_ = l_Lean_stringToMessageData(v___x_963_);
return v___x_964_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__3(void){
_start:
{
lean_object* v___x_966_; lean_object* v___x_967_; 
v___x_966_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__2));
v___x_967_ = l_Lean_stringToMessageData(v___x_966_);
return v___x_967_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__5(void){
_start:
{
lean_object* v___x_969_; lean_object* v___x_970_; 
v___x_969_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__4));
v___x_970_ = l_Lean_stringToMessageData(v___x_969_);
return v___x_970_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___redArg(lean_object* v_inst_971_, lean_object* v_inst_972_, lean_object* v_name_973_, uint8_t v_kind_974_){
_start:
{
lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___y_981_; 
v___x_975_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__1, &l_Lean_throwAttrMustBeGlobal___redArg___closed__1_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__1);
v___x_976_ = l_Lean_MessageData_ofName(v_name_973_);
v___x_977_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_977_, 0, v___x_975_);
lean_ctor_set(v___x_977_, 1, v___x_976_);
v___x_978_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__3, &l_Lean_throwAttrMustBeGlobal___redArg___closed__3_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__3);
v___x_979_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_979_, 0, v___x_977_);
lean_ctor_set(v___x_979_, 1, v___x_978_);
switch(v_kind_974_)
{
case 0:
{
lean_object* v___x_988_; 
v___x_988_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__0));
v___y_981_ = v___x_988_;
goto v___jp_980_;
}
case 1:
{
lean_object* v___x_989_; 
v___x_989_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__1));
v___y_981_ = v___x_989_;
goto v___jp_980_;
}
default: 
{
lean_object* v___x_990_; 
v___x_990_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__2));
v___y_981_ = v___x_990_;
goto v___jp_980_;
}
}
v___jp_980_:
{
lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; 
v___x_982_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_982_, 0, v___y_981_);
v___x_983_ = l_Lean_MessageData_ofFormat(v___x_982_);
v___x_984_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_984_, 0, v___x_979_);
lean_ctor_set(v___x_984_, 1, v___x_983_);
v___x_985_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__5, &l_Lean_throwAttrMustBeGlobal___redArg___closed__5_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__5);
v___x_986_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_986_, 0, v___x_984_);
lean_ctor_set(v___x_986_, 1, v___x_985_);
v___x_987_ = l_Lean_throwError___redArg(v_inst_971_, v_inst_972_, v___x_986_);
return v___x_987_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___redArg___boxed(lean_object* v_inst_991_, lean_object* v_inst_992_, lean_object* v_name_993_, lean_object* v_kind_994_){
_start:
{
uint8_t v_kind_boxed_995_; lean_object* v_res_996_; 
v_kind_boxed_995_ = lean_unbox(v_kind_994_);
v_res_996_ = l_Lean_throwAttrMustBeGlobal___redArg(v_inst_991_, v_inst_992_, v_name_993_, v_kind_boxed_995_);
return v_res_996_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal(lean_object* v_m_997_, lean_object* v_inst_998_, lean_object* v_inst_999_, lean_object* v_00_u03b1_1000_, lean_object* v_name_1001_, uint8_t v_kind_1002_){
_start:
{
lean_object* v___x_1003_; 
v___x_1003_ = l_Lean_throwAttrMustBeGlobal___redArg(v_inst_998_, v_inst_999_, v_name_1001_, v_kind_1002_);
return v___x_1003_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___boxed(lean_object* v_m_1004_, lean_object* v_inst_1005_, lean_object* v_inst_1006_, lean_object* v_00_u03b1_1007_, lean_object* v_name_1008_, lean_object* v_kind_1009_){
_start:
{
uint8_t v_kind_boxed_1010_; lean_object* v_res_1011_; 
v_kind_boxed_1010_ = lean_unbox(v_kind_1009_);
v_res_1011_ = l_Lean_throwAttrMustBeGlobal(v_m_1004_, v_inst_1005_, v_inst_1006_, v_00_u03b1_1007_, v_name_1008_, v_kind_boxed_1010_);
return v_res_1011_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1(void){
_start:
{
lean_object* v___x_1013_; lean_object* v___x_1014_; 
v___x_1013_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___redArg___closed__0));
v___x_1014_ = l_Lean_stringToMessageData(v___x_1013_);
return v___x_1014_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__3(void){
_start:
{
lean_object* v___x_1016_; lean_object* v___x_1017_; 
v___x_1016_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___redArg___closed__2));
v___x_1017_ = l_Lean_stringToMessageData(v___x_1016_);
return v___x_1017_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__5(void){
_start:
{
lean_object* v___x_1019_; lean_object* v___x_1020_; 
v___x_1019_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___redArg___closed__4));
v___x_1020_ = l_Lean_stringToMessageData(v___x_1019_);
return v___x_1020_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___redArg(lean_object* v_inst_1021_, lean_object* v_inst_1022_, lean_object* v_attrName_1023_, lean_object* v_declName_1024_){
_start:
{
lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; uint8_t v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; 
v___x_1025_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1);
v___x_1026_ = l_Lean_MessageData_ofName(v_attrName_1023_);
v___x_1027_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1027_, 0, v___x_1025_);
lean_ctor_set(v___x_1027_, 1, v___x_1026_);
v___x_1028_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__3, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__3_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__3);
v___x_1029_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1029_, 0, v___x_1027_);
lean_ctor_set(v___x_1029_, 1, v___x_1028_);
v___x_1030_ = 0;
v___x_1031_ = l_Lean_MessageData_ofConstName(v_declName_1024_, v___x_1030_);
v___x_1032_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1032_, 0, v___x_1029_);
lean_ctor_set(v___x_1032_, 1, v___x_1031_);
v___x_1033_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__5, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__5_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__5);
v___x_1034_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1034_, 0, v___x_1032_);
lean_ctor_set(v___x_1034_, 1, v___x_1033_);
v___x_1035_ = l_Lean_throwError___redArg(v_inst_1021_, v_inst_1022_, v___x_1034_);
return v___x_1035_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule(lean_object* v_m_1036_, lean_object* v_inst_1037_, lean_object* v_inst_1038_, lean_object* v_00_u03b1_1039_, lean_object* v_attrName_1040_, lean_object* v_declName_1041_){
_start:
{
lean_object* v___x_1042_; 
v___x_1042_ = l_Lean_throwAttrDeclInImportedModule___redArg(v_inst_1037_, v_inst_1038_, v_attrName_1040_, v_declName_1041_);
return v___x_1042_;
}
}
static lean_object* _init_l_Lean_throwAttrNotInAsyncCtx___redArg___closed__1(void){
_start:
{
lean_object* v___x_1044_; lean_object* v___x_1045_; 
v___x_1044_ = ((lean_object*)(l_Lean_throwAttrNotInAsyncCtx___redArg___closed__0));
v___x_1045_ = l_Lean_stringToMessageData(v___x_1044_);
return v___x_1045_;
}
}
static lean_object* _init_l_Lean_throwAttrNotInAsyncCtx___redArg___closed__3(void){
_start:
{
lean_object* v___x_1047_; lean_object* v___x_1048_; 
v___x_1047_ = ((lean_object*)(l_Lean_throwAttrNotInAsyncCtx___redArg___closed__2));
v___x_1048_ = l_Lean_stringToMessageData(v___x_1047_);
return v___x_1048_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___redArg(lean_object* v_inst_1049_, lean_object* v_inst_1050_, lean_object* v_attrName_1051_, lean_object* v_declName_1052_, lean_object* v_asyncPrefix_x3f_1053_){
_start:
{
lean_object* v___y_1055_; 
if (lean_obj_tag(v_asyncPrefix_x3f_1053_) == 0)
{
lean_object* v___x_1068_; 
v___x_1068_ = l_Lean_MessageData_nil;
v___y_1055_ = v___x_1068_;
goto v___jp_1054_;
}
else
{
lean_object* v_val_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; 
v_val_1069_ = lean_ctor_get(v_asyncPrefix_x3f_1053_, 0);
lean_inc(v_val_1069_);
lean_dec_ref(v_asyncPrefix_x3f_1053_);
v___x_1070_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___redArg___closed__3, &l_Lean_throwAttrNotInAsyncCtx___redArg___closed__3_once, _init_l_Lean_throwAttrNotInAsyncCtx___redArg___closed__3);
v___x_1071_ = l_Lean_MessageData_ofName(v_val_1069_);
v___x_1072_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1072_, 0, v___x_1070_);
lean_ctor_set(v___x_1072_, 1, v___x_1071_);
v___x_1073_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__5, &l_Lean_throwAttrMustBeGlobal___redArg___closed__5_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__5);
v___x_1074_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1074_, 0, v___x_1072_);
lean_ctor_set(v___x_1074_, 1, v___x_1073_);
v___y_1055_ = v___x_1074_;
goto v___jp_1054_;
}
v___jp_1054_:
{
lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; uint8_t v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; 
v___x_1056_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1);
v___x_1057_ = l_Lean_MessageData_ofName(v_attrName_1051_);
v___x_1058_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1058_, 0, v___x_1056_);
lean_ctor_set(v___x_1058_, 1, v___x_1057_);
v___x_1059_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__3, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__3_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__3);
v___x_1060_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1060_, 0, v___x_1058_);
lean_ctor_set(v___x_1060_, 1, v___x_1059_);
v___x_1061_ = 0;
v___x_1062_ = l_Lean_MessageData_ofConstName(v_declName_1052_, v___x_1061_);
v___x_1063_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1063_, 0, v___x_1060_);
lean_ctor_set(v___x_1063_, 1, v___x_1062_);
v___x_1064_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___redArg___closed__1, &l_Lean_throwAttrNotInAsyncCtx___redArg___closed__1_once, _init_l_Lean_throwAttrNotInAsyncCtx___redArg___closed__1);
v___x_1065_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1065_, 0, v___x_1063_);
lean_ctor_set(v___x_1065_, 1, v___x_1064_);
v___x_1066_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1066_, 0, v___x_1065_);
lean_ctor_set(v___x_1066_, 1, v___y_1055_);
v___x_1067_ = l_Lean_throwError___redArg(v_inst_1049_, v_inst_1050_, v___x_1066_);
return v___x_1067_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx(lean_object* v_m_1075_, lean_object* v_inst_1076_, lean_object* v_inst_1077_, lean_object* v_00_u03b1_1078_, lean_object* v_attrName_1079_, lean_object* v_declName_1080_, lean_object* v_asyncPrefix_x3f_1081_){
_start:
{
lean_object* v___x_1082_; 
v___x_1082_ = l_Lean_throwAttrNotInAsyncCtx___redArg(v_inst_1076_, v_inst_1077_, v_attrName_1079_, v_declName_1080_, v_asyncPrefix_x3f_1081_);
return v___x_1082_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1(void){
_start:
{
lean_object* v___x_1084_; lean_object* v___x_1085_; 
v___x_1084_ = ((lean_object*)(l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__0));
v___x_1085_ = l_Lean_stringToMessageData(v___x_1084_);
return v___x_1085_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__3(void){
_start:
{
lean_object* v___x_1087_; lean_object* v___x_1088_; 
v___x_1087_ = ((lean_object*)(l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__2));
v___x_1088_ = l_Lean_stringToMessageData(v___x_1087_);
return v___x_1088_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__5(void){
_start:
{
lean_object* v___x_1090_; lean_object* v___x_1091_; 
v___x_1090_ = ((lean_object*)(l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__4));
v___x_1091_ = l_Lean_stringToMessageData(v___x_1090_);
return v___x_1091_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__7(void){
_start:
{
lean_object* v___x_1093_; lean_object* v___x_1094_; 
v___x_1093_ = ((lean_object*)(l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__6));
v___x_1094_ = l_Lean_stringToMessageData(v___x_1093_);
return v___x_1094_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclNotOfExpectedType___redArg(lean_object* v_inst_1095_, lean_object* v_inst_1096_, lean_object* v_attrName_1097_, lean_object* v_declName_1098_, lean_object* v_givenType_1099_, lean_object* v_expectedType_1100_){
_start:
{
lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; uint8_t v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; 
v___x_1101_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1);
v___x_1102_ = l_Lean_MessageData_ofName(v_attrName_1097_);
lean_inc_ref(v___x_1102_);
v___x_1103_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1103_, 0, v___x_1101_);
lean_ctor_set(v___x_1103_, 1, v___x_1102_);
v___x_1104_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1, &l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1);
v___x_1105_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1105_, 0, v___x_1103_);
lean_ctor_set(v___x_1105_, 1, v___x_1104_);
v___x_1106_ = 0;
v___x_1107_ = l_Lean_MessageData_ofConstName(v_declName_1098_, v___x_1106_);
v___x_1108_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1108_, 0, v___x_1105_);
lean_ctor_set(v___x_1108_, 1, v___x_1107_);
v___x_1109_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__3, &l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__3_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__3);
v___x_1110_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1110_, 0, v___x_1108_);
lean_ctor_set(v___x_1110_, 1, v___x_1109_);
v___x_1111_ = l_Lean_indentExpr(v_givenType_1099_);
v___x_1112_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1112_, 0, v___x_1110_);
lean_ctor_set(v___x_1112_, 1, v___x_1111_);
v___x_1113_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__5, &l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__5_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__5);
v___x_1114_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1114_, 0, v___x_1112_);
lean_ctor_set(v___x_1114_, 1, v___x_1113_);
v___x_1115_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1115_, 0, v___x_1114_);
lean_ctor_set(v___x_1115_, 1, v___x_1102_);
v___x_1116_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__7, &l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__7_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__7);
v___x_1117_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1117_, 0, v___x_1115_);
lean_ctor_set(v___x_1117_, 1, v___x_1116_);
v___x_1118_ = l_Lean_indentExpr(v_expectedType_1100_);
v___x_1119_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1119_, 0, v___x_1117_);
lean_ctor_set(v___x_1119_, 1, v___x_1118_);
v___x_1120_ = l_Lean_throwError___redArg(v_inst_1095_, v_inst_1096_, v___x_1119_);
return v___x_1120_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclNotOfExpectedType(lean_object* v_m_1121_, lean_object* v_inst_1122_, lean_object* v_inst_1123_, lean_object* v_00_u03b1_1124_, lean_object* v_attrName_1125_, lean_object* v_declName_1126_, lean_object* v_givenType_1127_, lean_object* v_expectedType_1128_){
_start:
{
lean_object* v___x_1129_; 
v___x_1129_ = l_Lean_throwAttrDeclNotOfExpectedType___redArg(v_inst_1122_, v_inst_1123_, v_attrName_1125_, v_declName_1126_, v_givenType_1127_, v_expectedType_1128_);
return v___x_1129_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1___redArg(lean_object* v_constName_1130_, uint8_t v_skipRealize_1131_, lean_object* v___y_1132_){
_start:
{
lean_object* v___x_1134_; lean_object* v_env_1135_; uint8_t v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; 
v___x_1134_ = lean_st_ref_get(v___y_1132_);
v_env_1135_ = lean_ctor_get(v___x_1134_, 0);
lean_inc_ref(v_env_1135_);
lean_dec(v___x_1134_);
v___x_1136_ = l_Lean_Environment_contains(v_env_1135_, v_constName_1130_, v_skipRealize_1131_);
v___x_1137_ = lean_box(v___x_1136_);
v___x_1138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1138_, 0, v___x_1137_);
return v___x_1138_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1___redArg___boxed(lean_object* v_constName_1139_, lean_object* v_skipRealize_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_){
_start:
{
uint8_t v_skipRealize_boxed_1143_; lean_object* v_res_1144_; 
v_skipRealize_boxed_1143_ = lean_unbox(v_skipRealize_1140_);
v_res_1144_ = l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1___redArg(v_constName_1139_, v_skipRealize_boxed_1143_, v___y_1141_);
lean_dec(v___y_1141_);
return v_res_1144_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1(lean_object* v_constName_1145_, uint8_t v_skipRealize_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_){
_start:
{
lean_object* v___x_1150_; 
v___x_1150_ = l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1___redArg(v_constName_1145_, v_skipRealize_1146_, v___y_1148_);
return v___x_1150_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1___boxed(lean_object* v_constName_1151_, lean_object* v_skipRealize_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_){
_start:
{
uint8_t v_skipRealize_boxed_1156_; lean_object* v_res_1157_; 
v_skipRealize_boxed_1156_ = lean_unbox(v_skipRealize_1152_);
v_res_1157_ = l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1(v_constName_1151_, v_skipRealize_boxed_1156_, v___y_1153_, v___y_1154_);
lean_dec(v___y_1154_);
lean_dec_ref(v___y_1153_);
return v_res_1157_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___lam__0(lean_object* v___y_1158_, uint8_t v_isExporting_1159_, lean_object* v___x_1160_, lean_object* v_a_x3f_1161_){
_start:
{
lean_object* v___x_1163_; lean_object* v_env_1164_; lean_object* v_nextMacroScope_1165_; lean_object* v_ngen_1166_; lean_object* v_auxDeclNGen_1167_; lean_object* v_traceState_1168_; lean_object* v_messages_1169_; lean_object* v_infoState_1170_; lean_object* v_snapshotTasks_1171_; lean_object* v___x_1173_; uint8_t v_isShared_1174_; uint8_t v_isSharedCheck_1182_; 
v___x_1163_ = lean_st_ref_take(v___y_1158_);
v_env_1164_ = lean_ctor_get(v___x_1163_, 0);
v_nextMacroScope_1165_ = lean_ctor_get(v___x_1163_, 1);
v_ngen_1166_ = lean_ctor_get(v___x_1163_, 2);
v_auxDeclNGen_1167_ = lean_ctor_get(v___x_1163_, 3);
v_traceState_1168_ = lean_ctor_get(v___x_1163_, 4);
v_messages_1169_ = lean_ctor_get(v___x_1163_, 6);
v_infoState_1170_ = lean_ctor_get(v___x_1163_, 7);
v_snapshotTasks_1171_ = lean_ctor_get(v___x_1163_, 8);
v_isSharedCheck_1182_ = !lean_is_exclusive(v___x_1163_);
if (v_isSharedCheck_1182_ == 0)
{
lean_object* v_unused_1183_; 
v_unused_1183_ = lean_ctor_get(v___x_1163_, 5);
lean_dec(v_unused_1183_);
v___x_1173_ = v___x_1163_;
v_isShared_1174_ = v_isSharedCheck_1182_;
goto v_resetjp_1172_;
}
else
{
lean_inc(v_snapshotTasks_1171_);
lean_inc(v_infoState_1170_);
lean_inc(v_messages_1169_);
lean_inc(v_traceState_1168_);
lean_inc(v_auxDeclNGen_1167_);
lean_inc(v_ngen_1166_);
lean_inc(v_nextMacroScope_1165_);
lean_inc(v_env_1164_);
lean_dec(v___x_1163_);
v___x_1173_ = lean_box(0);
v_isShared_1174_ = v_isSharedCheck_1182_;
goto v_resetjp_1172_;
}
v_resetjp_1172_:
{
lean_object* v___x_1175_; lean_object* v___x_1177_; 
v___x_1175_ = l_Lean_Environment_setExporting(v_env_1164_, v_isExporting_1159_);
if (v_isShared_1174_ == 0)
{
lean_ctor_set(v___x_1173_, 5, v___x_1160_);
lean_ctor_set(v___x_1173_, 0, v___x_1175_);
v___x_1177_ = v___x_1173_;
goto v_reusejp_1176_;
}
else
{
lean_object* v_reuseFailAlloc_1181_; 
v_reuseFailAlloc_1181_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1181_, 0, v___x_1175_);
lean_ctor_set(v_reuseFailAlloc_1181_, 1, v_nextMacroScope_1165_);
lean_ctor_set(v_reuseFailAlloc_1181_, 2, v_ngen_1166_);
lean_ctor_set(v_reuseFailAlloc_1181_, 3, v_auxDeclNGen_1167_);
lean_ctor_set(v_reuseFailAlloc_1181_, 4, v_traceState_1168_);
lean_ctor_set(v_reuseFailAlloc_1181_, 5, v___x_1160_);
lean_ctor_set(v_reuseFailAlloc_1181_, 6, v_messages_1169_);
lean_ctor_set(v_reuseFailAlloc_1181_, 7, v_infoState_1170_);
lean_ctor_set(v_reuseFailAlloc_1181_, 8, v_snapshotTasks_1171_);
v___x_1177_ = v_reuseFailAlloc_1181_;
goto v_reusejp_1176_;
}
v_reusejp_1176_:
{
lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; 
v___x_1178_ = lean_st_ref_set(v___y_1158_, v___x_1177_);
v___x_1179_ = lean_box(0);
v___x_1180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1180_, 0, v___x_1179_);
return v___x_1180_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___lam__0___boxed(lean_object* v___y_1184_, lean_object* v_isExporting_1185_, lean_object* v___x_1186_, lean_object* v_a_x3f_1187_, lean_object* v___y_1188_){
_start:
{
uint8_t v_isExporting_boxed_1189_; lean_object* v_res_1190_; 
v_isExporting_boxed_1189_ = lean_unbox(v_isExporting_1185_);
v_res_1190_ = l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___lam__0(v___y_1184_, v_isExporting_boxed_1189_, v___x_1186_, v_a_x3f_1187_);
lean_dec(v_a_x3f_1187_);
lean_dec(v___y_1184_);
return v_res_1190_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_1191_; 
v___x_1191_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1191_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_1192_; lean_object* v___x_1193_; 
v___x_1192_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__0, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__0);
v___x_1193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1193_, 0, v___x_1192_);
return v___x_1193_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_1194_; lean_object* v___x_1195_; 
v___x_1194_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1);
v___x_1195_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1195_, 0, v___x_1194_);
lean_ctor_set(v___x_1195_, 1, v___x_1194_);
return v___x_1195_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg(lean_object* v_x_1196_, uint8_t v_isExporting_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_){
_start:
{
lean_object* v___x_1201_; lean_object* v_env_1202_; uint8_t v_isExporting_1203_; lean_object* v___x_1204_; lean_object* v_env_1205_; lean_object* v_nextMacroScope_1206_; lean_object* v_ngen_1207_; lean_object* v_auxDeclNGen_1208_; lean_object* v_traceState_1209_; lean_object* v_messages_1210_; lean_object* v_infoState_1211_; lean_object* v_snapshotTasks_1212_; lean_object* v___x_1214_; uint8_t v_isShared_1215_; uint8_t v_isSharedCheck_1251_; 
v___x_1201_ = lean_st_ref_get(v___y_1199_);
v_env_1202_ = lean_ctor_get(v___x_1201_, 0);
lean_inc_ref(v_env_1202_);
lean_dec(v___x_1201_);
v_isExporting_1203_ = lean_ctor_get_uint8(v_env_1202_, sizeof(void*)*8);
lean_dec_ref(v_env_1202_);
v___x_1204_ = lean_st_ref_take(v___y_1199_);
v_env_1205_ = lean_ctor_get(v___x_1204_, 0);
v_nextMacroScope_1206_ = lean_ctor_get(v___x_1204_, 1);
v_ngen_1207_ = lean_ctor_get(v___x_1204_, 2);
v_auxDeclNGen_1208_ = lean_ctor_get(v___x_1204_, 3);
v_traceState_1209_ = lean_ctor_get(v___x_1204_, 4);
v_messages_1210_ = lean_ctor_get(v___x_1204_, 6);
v_infoState_1211_ = lean_ctor_get(v___x_1204_, 7);
v_snapshotTasks_1212_ = lean_ctor_get(v___x_1204_, 8);
v_isSharedCheck_1251_ = !lean_is_exclusive(v___x_1204_);
if (v_isSharedCheck_1251_ == 0)
{
lean_object* v_unused_1252_; 
v_unused_1252_ = lean_ctor_get(v___x_1204_, 5);
lean_dec(v_unused_1252_);
v___x_1214_ = v___x_1204_;
v_isShared_1215_ = v_isSharedCheck_1251_;
goto v_resetjp_1213_;
}
else
{
lean_inc(v_snapshotTasks_1212_);
lean_inc(v_infoState_1211_);
lean_inc(v_messages_1210_);
lean_inc(v_traceState_1209_);
lean_inc(v_auxDeclNGen_1208_);
lean_inc(v_ngen_1207_);
lean_inc(v_nextMacroScope_1206_);
lean_inc(v_env_1205_);
lean_dec(v___x_1204_);
v___x_1214_ = lean_box(0);
v_isShared_1215_ = v_isSharedCheck_1251_;
goto v_resetjp_1213_;
}
v_resetjp_1213_:
{
lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1219_; 
v___x_1216_ = l_Lean_Environment_setExporting(v_env_1205_, v_isExporting_1197_);
v___x_1217_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2);
if (v_isShared_1215_ == 0)
{
lean_ctor_set(v___x_1214_, 5, v___x_1217_);
lean_ctor_set(v___x_1214_, 0, v___x_1216_);
v___x_1219_ = v___x_1214_;
goto v_reusejp_1218_;
}
else
{
lean_object* v_reuseFailAlloc_1250_; 
v_reuseFailAlloc_1250_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1250_, 0, v___x_1216_);
lean_ctor_set(v_reuseFailAlloc_1250_, 1, v_nextMacroScope_1206_);
lean_ctor_set(v_reuseFailAlloc_1250_, 2, v_ngen_1207_);
lean_ctor_set(v_reuseFailAlloc_1250_, 3, v_auxDeclNGen_1208_);
lean_ctor_set(v_reuseFailAlloc_1250_, 4, v_traceState_1209_);
lean_ctor_set(v_reuseFailAlloc_1250_, 5, v___x_1217_);
lean_ctor_set(v_reuseFailAlloc_1250_, 6, v_messages_1210_);
lean_ctor_set(v_reuseFailAlloc_1250_, 7, v_infoState_1211_);
lean_ctor_set(v_reuseFailAlloc_1250_, 8, v_snapshotTasks_1212_);
v___x_1219_ = v_reuseFailAlloc_1250_;
goto v_reusejp_1218_;
}
v_reusejp_1218_:
{
lean_object* v___x_1220_; lean_object* v_r_1221_; 
v___x_1220_ = lean_st_ref_set(v___y_1199_, v___x_1219_);
lean_inc(v___y_1199_);
v_r_1221_ = lean_apply_3(v_x_1196_, v___y_1198_, v___y_1199_, lean_box(0));
if (lean_obj_tag(v_r_1221_) == 0)
{
lean_object* v_a_1222_; lean_object* v___x_1224_; uint8_t v_isShared_1225_; uint8_t v_isSharedCheck_1238_; 
v_a_1222_ = lean_ctor_get(v_r_1221_, 0);
v_isSharedCheck_1238_ = !lean_is_exclusive(v_r_1221_);
if (v_isSharedCheck_1238_ == 0)
{
v___x_1224_ = v_r_1221_;
v_isShared_1225_ = v_isSharedCheck_1238_;
goto v_resetjp_1223_;
}
else
{
lean_inc(v_a_1222_);
lean_dec(v_r_1221_);
v___x_1224_ = lean_box(0);
v_isShared_1225_ = v_isSharedCheck_1238_;
goto v_resetjp_1223_;
}
v_resetjp_1223_:
{
lean_object* v___x_1227_; 
lean_inc(v_a_1222_);
if (v_isShared_1225_ == 0)
{
lean_ctor_set_tag(v___x_1224_, 1);
v___x_1227_ = v___x_1224_;
goto v_reusejp_1226_;
}
else
{
lean_object* v_reuseFailAlloc_1237_; 
v_reuseFailAlloc_1237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1237_, 0, v_a_1222_);
v___x_1227_ = v_reuseFailAlloc_1237_;
goto v_reusejp_1226_;
}
v_reusejp_1226_:
{
lean_object* v___x_1228_; lean_object* v___x_1230_; uint8_t v_isShared_1231_; uint8_t v_isSharedCheck_1235_; 
v___x_1228_ = l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___lam__0(v___y_1199_, v_isExporting_1203_, v___x_1217_, v___x_1227_);
lean_dec_ref(v___x_1227_);
lean_dec(v___y_1199_);
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
lean_ctor_set(v___x_1230_, 0, v_a_1222_);
v___x_1233_ = v___x_1230_;
goto v_reusejp_1232_;
}
else
{
lean_object* v_reuseFailAlloc_1234_; 
v_reuseFailAlloc_1234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1234_, 0, v_a_1222_);
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
else
{
lean_object* v_a_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1243_; uint8_t v_isShared_1244_; uint8_t v_isSharedCheck_1248_; 
v_a_1239_ = lean_ctor_get(v_r_1221_, 0);
lean_inc(v_a_1239_);
lean_dec_ref(v_r_1221_);
v___x_1240_ = lean_box(0);
v___x_1241_ = l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___lam__0(v___y_1199_, v_isExporting_1203_, v___x_1217_, v___x_1240_);
lean_dec(v___y_1199_);
v_isSharedCheck_1248_ = !lean_is_exclusive(v___x_1241_);
if (v_isSharedCheck_1248_ == 0)
{
lean_object* v_unused_1249_; 
v_unused_1249_ = lean_ctor_get(v___x_1241_, 0);
lean_dec(v_unused_1249_);
v___x_1243_ = v___x_1241_;
v_isShared_1244_ = v_isSharedCheck_1248_;
goto v_resetjp_1242_;
}
else
{
lean_dec(v___x_1241_);
v___x_1243_ = lean_box(0);
v_isShared_1244_ = v_isSharedCheck_1248_;
goto v_resetjp_1242_;
}
v_resetjp_1242_:
{
lean_object* v___x_1246_; 
if (v_isShared_1244_ == 0)
{
lean_ctor_set_tag(v___x_1243_, 1);
lean_ctor_set(v___x_1243_, 0, v_a_1239_);
v___x_1246_ = v___x_1243_;
goto v_reusejp_1245_;
}
else
{
lean_object* v_reuseFailAlloc_1247_; 
v_reuseFailAlloc_1247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1247_, 0, v_a_1239_);
v___x_1246_ = v_reuseFailAlloc_1247_;
goto v_reusejp_1245_;
}
v_reusejp_1245_:
{
return v___x_1246_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___boxed(lean_object* v_x_1253_, lean_object* v_isExporting_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_){
_start:
{
uint8_t v_isExporting_boxed_1258_; lean_object* v_res_1259_; 
v_isExporting_boxed_1258_ = lean_unbox(v_isExporting_1254_);
v_res_1259_ = l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg(v_x_1253_, v_isExporting_boxed_1258_, v___y_1255_, v___y_1256_);
return v_res_1259_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2(lean_object* v_00_u03b1_1260_, lean_object* v_x_1261_, uint8_t v_isExporting_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_){
_start:
{
lean_object* v___x_1266_; 
v___x_1266_ = l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg(v_x_1261_, v_isExporting_1262_, v___y_1263_, v___y_1264_);
return v___x_1266_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___boxed(lean_object* v_00_u03b1_1267_, lean_object* v_x_1268_, lean_object* v_isExporting_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_){
_start:
{
uint8_t v_isExporting_boxed_1273_; lean_object* v_res_1274_; 
v_isExporting_boxed_1273_ = lean_unbox(v_isExporting_1269_);
v_res_1274_ = l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2(v_00_u03b1_1267_, v_x_1268_, v_isExporting_boxed_1273_, v___y_1270_, v___y_1271_);
return v_res_1274_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0_spec__3(lean_object* v_opts_1275_, lean_object* v_opt_1276_){
_start:
{
lean_object* v_name_1277_; lean_object* v_defValue_1278_; lean_object* v_map_1279_; lean_object* v___x_1280_; 
v_name_1277_ = lean_ctor_get(v_opt_1276_, 0);
v_defValue_1278_ = lean_ctor_get(v_opt_1276_, 1);
v_map_1279_ = lean_ctor_get(v_opts_1275_, 0);
v___x_1280_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1279_, v_name_1277_);
if (lean_obj_tag(v___x_1280_) == 0)
{
uint8_t v___x_1281_; 
v___x_1281_ = lean_unbox(v_defValue_1278_);
return v___x_1281_;
}
else
{
lean_object* v_val_1282_; 
v_val_1282_ = lean_ctor_get(v___x_1280_, 0);
lean_inc(v_val_1282_);
lean_dec_ref(v___x_1280_);
if (lean_obj_tag(v_val_1282_) == 1)
{
uint8_t v_v_1283_; 
v_v_1283_ = lean_ctor_get_uint8(v_val_1282_, 0);
lean_dec_ref(v_val_1282_);
return v_v_1283_;
}
else
{
uint8_t v___x_1284_; 
lean_dec(v_val_1282_);
v___x_1284_ = lean_unbox(v_defValue_1278_);
return v___x_1284_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0_spec__3___boxed(lean_object* v_opts_1285_, lean_object* v_opt_1286_){
_start:
{
uint8_t v_res_1287_; lean_object* v_r_1288_; 
v_res_1287_ = l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0_spec__3(v_opts_1285_, v_opt_1286_);
lean_dec_ref(v_opt_1286_);
lean_dec_ref(v_opts_1285_);
v_r_1288_ = lean_box(v_res_1287_);
return v_r_1288_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0(uint8_t v___y_1296_, uint8_t v_suppressElabErrors_1297_, lean_object* v_x_1298_){
_start:
{
if (lean_obj_tag(v_x_1298_) == 1)
{
lean_object* v_pre_1299_; 
v_pre_1299_ = lean_ctor_get(v_x_1298_, 0);
switch(lean_obj_tag(v_pre_1299_))
{
case 1:
{
lean_object* v_pre_1300_; 
v_pre_1300_ = lean_ctor_get(v_pre_1299_, 0);
switch(lean_obj_tag(v_pre_1300_))
{
case 0:
{
lean_object* v_str_1301_; lean_object* v_str_1302_; lean_object* v___x_1303_; uint8_t v___x_1304_; 
v_str_1301_ = lean_ctor_get(v_x_1298_, 1);
v_str_1302_ = lean_ctor_get(v_pre_1299_, 1);
v___x_1303_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__0));
v___x_1304_ = lean_string_dec_eq(v_str_1302_, v___x_1303_);
if (v___x_1304_ == 0)
{
lean_object* v___x_1305_; uint8_t v___x_1306_; 
v___x_1305_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__2));
v___x_1306_ = lean_string_dec_eq(v_str_1302_, v___x_1305_);
if (v___x_1306_ == 0)
{
return v___y_1296_;
}
else
{
lean_object* v___x_1307_; uint8_t v___x_1308_; 
v___x_1307_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__1));
v___x_1308_ = lean_string_dec_eq(v_str_1301_, v___x_1307_);
if (v___x_1308_ == 0)
{
return v___y_1296_;
}
else
{
return v_suppressElabErrors_1297_;
}
}
}
else
{
lean_object* v___x_1309_; uint8_t v___x_1310_; 
v___x_1309_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__2));
v___x_1310_ = lean_string_dec_eq(v_str_1301_, v___x_1309_);
if (v___x_1310_ == 0)
{
return v___y_1296_;
}
else
{
return v_suppressElabErrors_1297_;
}
}
}
case 1:
{
lean_object* v_pre_1311_; 
v_pre_1311_ = lean_ctor_get(v_pre_1300_, 0);
if (lean_obj_tag(v_pre_1311_) == 0)
{
lean_object* v_str_1312_; lean_object* v_str_1313_; lean_object* v_str_1314_; lean_object* v___x_1315_; uint8_t v___x_1316_; 
v_str_1312_ = lean_ctor_get(v_x_1298_, 1);
v_str_1313_ = lean_ctor_get(v_pre_1299_, 1);
v_str_1314_ = lean_ctor_get(v_pre_1300_, 1);
v___x_1315_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__3));
v___x_1316_ = lean_string_dec_eq(v_str_1314_, v___x_1315_);
if (v___x_1316_ == 0)
{
return v___y_1296_;
}
else
{
lean_object* v___x_1317_; uint8_t v___x_1318_; 
v___x_1317_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__4));
v___x_1318_ = lean_string_dec_eq(v_str_1313_, v___x_1317_);
if (v___x_1318_ == 0)
{
return v___y_1296_;
}
else
{
lean_object* v___x_1319_; uint8_t v___x_1320_; 
v___x_1319_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__5));
v___x_1320_ = lean_string_dec_eq(v_str_1312_, v___x_1319_);
if (v___x_1320_ == 0)
{
return v___y_1296_;
}
else
{
return v_suppressElabErrors_1297_;
}
}
}
}
else
{
return v___y_1296_;
}
}
default: 
{
return v___y_1296_;
}
}
}
case 0:
{
lean_object* v_str_1321_; lean_object* v___x_1322_; uint8_t v___x_1323_; 
v_str_1321_ = lean_ctor_get(v_x_1298_, 1);
v___x_1322_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__6));
v___x_1323_ = lean_string_dec_eq(v_str_1321_, v___x_1322_);
if (v___x_1323_ == 0)
{
return v___y_1296_;
}
else
{
return v_suppressElabErrors_1297_;
}
}
default: 
{
return v___y_1296_;
}
}
}
else
{
return v___y_1296_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___boxed(lean_object* v___y_1324_, lean_object* v_suppressElabErrors_1325_, lean_object* v_x_1326_){
_start:
{
uint8_t v___y_5440__boxed_1327_; uint8_t v_suppressElabErrors_boxed_1328_; uint8_t v_res_1329_; lean_object* v_r_1330_; 
v___y_5440__boxed_1327_ = lean_unbox(v___y_1324_);
v_suppressElabErrors_boxed_1328_ = lean_unbox(v_suppressElabErrors_1325_);
v_res_1329_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0(v___y_5440__boxed_1327_, v_suppressElabErrors_boxed_1328_, v_x_1326_);
lean_dec(v_x_1326_);
v_r_1330_ = lean_box(v_res_1329_);
return v_r_1330_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6(lean_object* v_ref_1331_, lean_object* v_msgData_1332_, uint8_t v_severity_1333_, uint8_t v_isSilent_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_){
_start:
{
lean_object* v___y_1339_; lean_object* v___y_1340_; lean_object* v___y_1341_; uint8_t v___y_1342_; lean_object* v___y_1343_; lean_object* v___y_1344_; uint8_t v___y_1345_; lean_object* v___y_1346_; lean_object* v___y_1347_; lean_object* v___y_1375_; lean_object* v___y_1376_; lean_object* v___y_1377_; uint8_t v___y_1378_; uint8_t v___y_1379_; lean_object* v___y_1380_; uint8_t v___y_1381_; lean_object* v___y_1382_; lean_object* v___y_1400_; lean_object* v___y_1401_; lean_object* v___y_1402_; uint8_t v___y_1403_; lean_object* v___y_1404_; uint8_t v___y_1405_; uint8_t v___y_1406_; lean_object* v___y_1407_; lean_object* v___y_1411_; lean_object* v___y_1412_; lean_object* v___y_1413_; uint8_t v___y_1414_; uint8_t v___y_1415_; lean_object* v___y_1416_; uint8_t v___y_1417_; uint8_t v___x_1422_; lean_object* v___y_1424_; lean_object* v___y_1425_; lean_object* v___y_1426_; uint8_t v___y_1427_; lean_object* v___y_1428_; uint8_t v___y_1429_; uint8_t v___y_1430_; uint8_t v___y_1432_; uint8_t v___x_1447_; 
v___x_1422_ = 2;
v___x_1447_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1333_, v___x_1422_);
if (v___x_1447_ == 0)
{
v___y_1432_ = v___x_1447_;
goto v___jp_1431_;
}
else
{
uint8_t v___x_1448_; 
lean_inc_ref(v_msgData_1332_);
v___x_1448_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_1332_);
v___y_1432_ = v___x_1448_;
goto v___jp_1431_;
}
v___jp_1338_:
{
lean_object* v___x_1348_; lean_object* v_currNamespace_1349_; lean_object* v_openDecls_1350_; lean_object* v_env_1351_; lean_object* v_nextMacroScope_1352_; lean_object* v_ngen_1353_; lean_object* v_auxDeclNGen_1354_; lean_object* v_traceState_1355_; lean_object* v_cache_1356_; lean_object* v_messages_1357_; lean_object* v_infoState_1358_; lean_object* v_snapshotTasks_1359_; lean_object* v___x_1361_; uint8_t v_isShared_1362_; uint8_t v_isSharedCheck_1373_; 
v___x_1348_ = lean_st_ref_take(v___y_1347_);
v_currNamespace_1349_ = lean_ctor_get(v___y_1346_, 6);
lean_inc(v_currNamespace_1349_);
v_openDecls_1350_ = lean_ctor_get(v___y_1346_, 7);
lean_inc(v_openDecls_1350_);
lean_dec_ref(v___y_1346_);
v_env_1351_ = lean_ctor_get(v___x_1348_, 0);
v_nextMacroScope_1352_ = lean_ctor_get(v___x_1348_, 1);
v_ngen_1353_ = lean_ctor_get(v___x_1348_, 2);
v_auxDeclNGen_1354_ = lean_ctor_get(v___x_1348_, 3);
v_traceState_1355_ = lean_ctor_get(v___x_1348_, 4);
v_cache_1356_ = lean_ctor_get(v___x_1348_, 5);
v_messages_1357_ = lean_ctor_get(v___x_1348_, 6);
v_infoState_1358_ = lean_ctor_get(v___x_1348_, 7);
v_snapshotTasks_1359_ = lean_ctor_get(v___x_1348_, 8);
v_isSharedCheck_1373_ = !lean_is_exclusive(v___x_1348_);
if (v_isSharedCheck_1373_ == 0)
{
v___x_1361_ = v___x_1348_;
v_isShared_1362_ = v_isSharedCheck_1373_;
goto v_resetjp_1360_;
}
else
{
lean_inc(v_snapshotTasks_1359_);
lean_inc(v_infoState_1358_);
lean_inc(v_messages_1357_);
lean_inc(v_cache_1356_);
lean_inc(v_traceState_1355_);
lean_inc(v_auxDeclNGen_1354_);
lean_inc(v_ngen_1353_);
lean_inc(v_nextMacroScope_1352_);
lean_inc(v_env_1351_);
lean_dec(v___x_1348_);
v___x_1361_ = lean_box(0);
v_isShared_1362_ = v_isSharedCheck_1373_;
goto v_resetjp_1360_;
}
v_resetjp_1360_:
{
lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1368_; 
v___x_1363_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1363_, 0, v_currNamespace_1349_);
lean_ctor_set(v___x_1363_, 1, v_openDecls_1350_);
v___x_1364_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1364_, 0, v___x_1363_);
lean_ctor_set(v___x_1364_, 1, v___y_1340_);
v___x_1365_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1365_, 0, v___y_1339_);
lean_ctor_set(v___x_1365_, 1, v___y_1344_);
lean_ctor_set(v___x_1365_, 2, v___y_1343_);
lean_ctor_set(v___x_1365_, 3, v___y_1341_);
lean_ctor_set(v___x_1365_, 4, v___x_1364_);
lean_ctor_set_uint8(v___x_1365_, sizeof(void*)*5, v___y_1342_);
lean_ctor_set_uint8(v___x_1365_, sizeof(void*)*5 + 1, v___y_1345_);
lean_ctor_set_uint8(v___x_1365_, sizeof(void*)*5 + 2, v_isSilent_1334_);
v___x_1366_ = l_Lean_MessageLog_add(v___x_1365_, v_messages_1357_);
if (v_isShared_1362_ == 0)
{
lean_ctor_set(v___x_1361_, 6, v___x_1366_);
v___x_1368_ = v___x_1361_;
goto v_reusejp_1367_;
}
else
{
lean_object* v_reuseFailAlloc_1372_; 
v_reuseFailAlloc_1372_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1372_, 0, v_env_1351_);
lean_ctor_set(v_reuseFailAlloc_1372_, 1, v_nextMacroScope_1352_);
lean_ctor_set(v_reuseFailAlloc_1372_, 2, v_ngen_1353_);
lean_ctor_set(v_reuseFailAlloc_1372_, 3, v_auxDeclNGen_1354_);
lean_ctor_set(v_reuseFailAlloc_1372_, 4, v_traceState_1355_);
lean_ctor_set(v_reuseFailAlloc_1372_, 5, v_cache_1356_);
lean_ctor_set(v_reuseFailAlloc_1372_, 6, v___x_1366_);
lean_ctor_set(v_reuseFailAlloc_1372_, 7, v_infoState_1358_);
lean_ctor_set(v_reuseFailAlloc_1372_, 8, v_snapshotTasks_1359_);
v___x_1368_ = v_reuseFailAlloc_1372_;
goto v_reusejp_1367_;
}
v_reusejp_1367_:
{
lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; 
v___x_1369_ = lean_st_ref_set(v___y_1347_, v___x_1368_);
v___x_1370_ = lean_box(0);
v___x_1371_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1371_, 0, v___x_1370_);
return v___x_1371_;
}
}
}
v___jp_1374_:
{
lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v_a_1385_; lean_object* v___x_1387_; uint8_t v_isShared_1388_; uint8_t v_isSharedCheck_1398_; 
v___x_1383_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_1332_);
v___x_1384_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0_spec__0_spec__1(v___x_1383_, v___y_1335_, v___y_1336_);
v_a_1385_ = lean_ctor_get(v___x_1384_, 0);
v_isSharedCheck_1398_ = !lean_is_exclusive(v___x_1384_);
if (v_isSharedCheck_1398_ == 0)
{
v___x_1387_ = v___x_1384_;
v_isShared_1388_ = v_isSharedCheck_1398_;
goto v_resetjp_1386_;
}
else
{
lean_inc(v_a_1385_);
lean_dec(v___x_1384_);
v___x_1387_ = lean_box(0);
v_isShared_1388_ = v_isSharedCheck_1398_;
goto v_resetjp_1386_;
}
v_resetjp_1386_:
{
lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; 
lean_inc_ref(v___y_1380_);
v___x_1389_ = l_Lean_FileMap_toPosition(v___y_1380_, v___y_1377_);
lean_dec(v___y_1377_);
v___x_1390_ = l_Lean_FileMap_toPosition(v___y_1380_, v___y_1382_);
lean_dec(v___y_1382_);
v___x_1391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1391_, 0, v___x_1390_);
v___x_1392_ = ((lean_object*)(l_Lean_instInhabitedAttributeImplCore_default___closed__0));
if (v___y_1378_ == 0)
{
lean_del_object(v___x_1387_);
lean_dec_ref(v___y_1375_);
v___y_1339_ = v___y_1376_;
v___y_1340_ = v_a_1385_;
v___y_1341_ = v___x_1392_;
v___y_1342_ = v___y_1379_;
v___y_1343_ = v___x_1391_;
v___y_1344_ = v___x_1389_;
v___y_1345_ = v___y_1381_;
v___y_1346_ = v___y_1335_;
v___y_1347_ = v___y_1336_;
goto v___jp_1338_;
}
else
{
uint8_t v___x_1393_; 
lean_inc(v_a_1385_);
v___x_1393_ = l_Lean_MessageData_hasTag(v___y_1375_, v_a_1385_);
if (v___x_1393_ == 0)
{
lean_object* v___x_1394_; lean_object* v___x_1396_; 
lean_dec_ref(v___x_1391_);
lean_dec_ref(v___x_1389_);
lean_dec(v_a_1385_);
lean_dec_ref(v___y_1376_);
lean_dec_ref(v___y_1335_);
v___x_1394_ = lean_box(0);
if (v_isShared_1388_ == 0)
{
lean_ctor_set(v___x_1387_, 0, v___x_1394_);
v___x_1396_ = v___x_1387_;
goto v_reusejp_1395_;
}
else
{
lean_object* v_reuseFailAlloc_1397_; 
v_reuseFailAlloc_1397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1397_, 0, v___x_1394_);
v___x_1396_ = v_reuseFailAlloc_1397_;
goto v_reusejp_1395_;
}
v_reusejp_1395_:
{
return v___x_1396_;
}
}
else
{
lean_del_object(v___x_1387_);
v___y_1339_ = v___y_1376_;
v___y_1340_ = v_a_1385_;
v___y_1341_ = v___x_1392_;
v___y_1342_ = v___y_1379_;
v___y_1343_ = v___x_1391_;
v___y_1344_ = v___x_1389_;
v___y_1345_ = v___y_1381_;
v___y_1346_ = v___y_1335_;
v___y_1347_ = v___y_1336_;
goto v___jp_1338_;
}
}
}
}
v___jp_1399_:
{
lean_object* v___x_1408_; 
v___x_1408_ = l_Lean_Syntax_getTailPos_x3f(v___y_1402_, v___y_1405_);
lean_dec(v___y_1402_);
if (lean_obj_tag(v___x_1408_) == 0)
{
lean_inc(v___y_1407_);
v___y_1375_ = v___y_1400_;
v___y_1376_ = v___y_1401_;
v___y_1377_ = v___y_1407_;
v___y_1378_ = v___y_1403_;
v___y_1379_ = v___y_1405_;
v___y_1380_ = v___y_1404_;
v___y_1381_ = v___y_1406_;
v___y_1382_ = v___y_1407_;
goto v___jp_1374_;
}
else
{
lean_object* v_val_1409_; 
v_val_1409_ = lean_ctor_get(v___x_1408_, 0);
lean_inc(v_val_1409_);
lean_dec_ref(v___x_1408_);
v___y_1375_ = v___y_1400_;
v___y_1376_ = v___y_1401_;
v___y_1377_ = v___y_1407_;
v___y_1378_ = v___y_1403_;
v___y_1379_ = v___y_1405_;
v___y_1380_ = v___y_1404_;
v___y_1381_ = v___y_1406_;
v___y_1382_ = v_val_1409_;
goto v___jp_1374_;
}
}
v___jp_1410_:
{
lean_object* v_ref_1418_; lean_object* v___x_1419_; 
v_ref_1418_ = l_Lean_replaceRef(v_ref_1331_, v___y_1413_);
lean_dec(v___y_1413_);
v___x_1419_ = l_Lean_Syntax_getPos_x3f(v_ref_1418_, v___y_1415_);
if (lean_obj_tag(v___x_1419_) == 0)
{
lean_object* v___x_1420_; 
v___x_1420_ = lean_unsigned_to_nat(0u);
v___y_1400_ = v___y_1411_;
v___y_1401_ = v___y_1412_;
v___y_1402_ = v_ref_1418_;
v___y_1403_ = v___y_1414_;
v___y_1404_ = v___y_1416_;
v___y_1405_ = v___y_1415_;
v___y_1406_ = v___y_1417_;
v___y_1407_ = v___x_1420_;
goto v___jp_1399_;
}
else
{
lean_object* v_val_1421_; 
v_val_1421_ = lean_ctor_get(v___x_1419_, 0);
lean_inc(v_val_1421_);
lean_dec_ref(v___x_1419_);
v___y_1400_ = v___y_1411_;
v___y_1401_ = v___y_1412_;
v___y_1402_ = v_ref_1418_;
v___y_1403_ = v___y_1414_;
v___y_1404_ = v___y_1416_;
v___y_1405_ = v___y_1415_;
v___y_1406_ = v___y_1417_;
v___y_1407_ = v_val_1421_;
goto v___jp_1399_;
}
}
v___jp_1423_:
{
if (v___y_1430_ == 0)
{
v___y_1411_ = v___y_1424_;
v___y_1412_ = v___y_1425_;
v___y_1413_ = v___y_1426_;
v___y_1414_ = v___y_1427_;
v___y_1415_ = v___y_1429_;
v___y_1416_ = v___y_1428_;
v___y_1417_ = v_severity_1333_;
goto v___jp_1410_;
}
else
{
v___y_1411_ = v___y_1424_;
v___y_1412_ = v___y_1425_;
v___y_1413_ = v___y_1426_;
v___y_1414_ = v___y_1427_;
v___y_1415_ = v___y_1429_;
v___y_1416_ = v___y_1428_;
v___y_1417_ = v___x_1422_;
goto v___jp_1410_;
}
}
v___jp_1431_:
{
if (v___y_1432_ == 0)
{
lean_object* v_fileName_1433_; lean_object* v_fileMap_1434_; lean_object* v_options_1435_; lean_object* v_ref_1436_; uint8_t v_suppressElabErrors_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___f_1440_; uint8_t v___x_1441_; uint8_t v___x_1442_; 
v_fileName_1433_ = lean_ctor_get(v___y_1335_, 0);
v_fileMap_1434_ = lean_ctor_get(v___y_1335_, 1);
v_options_1435_ = lean_ctor_get(v___y_1335_, 2);
v_ref_1436_ = lean_ctor_get(v___y_1335_, 5);
v_suppressElabErrors_1437_ = lean_ctor_get_uint8(v___y_1335_, sizeof(void*)*14 + 1);
v___x_1438_ = lean_box(v___y_1432_);
v___x_1439_ = lean_box(v_suppressElabErrors_1437_);
v___f_1440_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1440_, 0, v___x_1438_);
lean_closure_set(v___f_1440_, 1, v___x_1439_);
v___x_1441_ = 1;
v___x_1442_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1333_, v___x_1441_);
if (v___x_1442_ == 0)
{
lean_inc_ref(v_fileMap_1434_);
lean_inc(v_ref_1436_);
lean_inc_ref(v_fileName_1433_);
v___y_1424_ = v___f_1440_;
v___y_1425_ = v_fileName_1433_;
v___y_1426_ = v_ref_1436_;
v___y_1427_ = v_suppressElabErrors_1437_;
v___y_1428_ = v_fileMap_1434_;
v___y_1429_ = v___y_1432_;
v___y_1430_ = v___x_1442_;
goto v___jp_1423_;
}
else
{
lean_object* v___x_1443_; uint8_t v___x_1444_; 
v___x_1443_ = l_Lean_warningAsError;
v___x_1444_ = l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0_spec__3(v_options_1435_, v___x_1443_);
lean_inc_ref(v_fileMap_1434_);
lean_inc(v_ref_1436_);
lean_inc_ref(v_fileName_1433_);
v___y_1424_ = v___f_1440_;
v___y_1425_ = v_fileName_1433_;
v___y_1426_ = v_ref_1436_;
v___y_1427_ = v_suppressElabErrors_1437_;
v___y_1428_ = v_fileMap_1434_;
v___y_1429_ = v___y_1432_;
v___y_1430_ = v___x_1444_;
goto v___jp_1423_;
}
}
else
{
lean_object* v___x_1445_; lean_object* v___x_1446_; 
lean_dec_ref(v___y_1335_);
lean_dec_ref(v_msgData_1332_);
v___x_1445_ = lean_box(0);
v___x_1446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1446_, 0, v___x_1445_);
return v___x_1446_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___boxed(lean_object* v_ref_1449_, lean_object* v_msgData_1450_, lean_object* v_severity_1451_, lean_object* v_isSilent_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_){
_start:
{
uint8_t v_severity_boxed_1456_; uint8_t v_isSilent_boxed_1457_; lean_object* v_res_1458_; 
v_severity_boxed_1456_ = lean_unbox(v_severity_1451_);
v_isSilent_boxed_1457_ = lean_unbox(v_isSilent_1452_);
v_res_1458_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6(v_ref_1449_, v_msgData_1450_, v_severity_boxed_1456_, v_isSilent_boxed_1457_, v___y_1453_, v___y_1454_);
lean_dec(v___y_1454_);
lean_dec(v_ref_1449_);
return v_res_1458_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5(lean_object* v_msgData_1459_, uint8_t v_severity_1460_, uint8_t v_isSilent_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_){
_start:
{
lean_object* v_ref_1465_; lean_object* v___x_1466_; 
v_ref_1465_ = lean_ctor_get(v___y_1462_, 5);
lean_inc(v_ref_1465_);
v___x_1466_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6(v_ref_1465_, v_msgData_1459_, v_severity_1460_, v_isSilent_1461_, v___y_1462_, v___y_1463_);
lean_dec(v_ref_1465_);
return v___x_1466_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5___boxed(lean_object* v_msgData_1467_, lean_object* v_severity_1468_, lean_object* v_isSilent_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_){
_start:
{
uint8_t v_severity_boxed_1473_; uint8_t v_isSilent_boxed_1474_; lean_object* v_res_1475_; 
v_severity_boxed_1473_ = lean_unbox(v_severity_1468_);
v_isSilent_boxed_1474_ = lean_unbox(v_isSilent_1469_);
v_res_1475_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5(v_msgData_1467_, v_severity_boxed_1473_, v_isSilent_boxed_1474_, v___y_1470_, v___y_1471_);
lean_dec(v___y_1471_);
return v_res_1475_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1(lean_object* v_msgData_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_){
_start:
{
uint8_t v___x_1480_; uint8_t v___x_1481_; lean_object* v___x_1482_; 
v___x_1480_ = 1;
v___x_1481_ = 0;
v___x_1482_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5(v_msgData_1476_, v___x_1480_, v___x_1481_, v___y_1477_, v___y_1478_);
return v___x_1482_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1___boxed(lean_object* v_msgData_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_){
_start:
{
lean_object* v_res_1487_; 
v_res_1487_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1(v_msgData_1483_, v___y_1484_, v___y_1485_);
lean_dec(v___y_1485_);
return v_res_1487_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0___redArg(lean_object* v_opt_1488_, lean_object* v___y_1489_){
_start:
{
lean_object* v_options_1491_; uint8_t v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; 
v_options_1491_ = lean_ctor_get(v___y_1489_, 2);
v___x_1492_ = l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0_spec__3(v_options_1491_, v_opt_1488_);
v___x_1493_ = lean_box(v___x_1492_);
v___x_1494_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1494_, 0, v___x_1493_);
return v___x_1494_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0___redArg___boxed(lean_object* v_opt_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_){
_start:
{
lean_object* v_res_1498_; 
v_res_1498_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0___redArg(v_opt_1495_, v___y_1496_);
lean_dec_ref(v___y_1496_);
lean_dec_ref(v_opt_1495_);
return v_res_1498_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1500_; lean_object* v___x_1501_; 
v___x_1500_ = ((lean_object*)(l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__0));
v___x_1501_ = l_Lean_stringToMessageData(v___x_1500_);
return v___x_1501_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__3(void){
_start:
{
lean_object* v___x_1503_; lean_object* v___x_1504_; 
v___x_1503_ = ((lean_object*)(l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__2));
v___x_1504_ = l_Lean_stringToMessageData(v___x_1503_);
return v___x_1504_;
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0(lean_object* v_id_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_){
_start:
{
lean_object* v___x_1509_; lean_object* v_env_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v_a_1513_; lean_object* v___x_1515_; uint8_t v_isShared_1516_; uint8_t v_isSharedCheck_1532_; 
v___x_1509_ = lean_st_ref_get(v___y_1507_);
v_env_1510_ = lean_ctor_get(v___x_1509_, 0);
lean_inc_ref(v_env_1510_);
lean_dec(v___x_1509_);
v___x_1511_ = l_Lean_ResolveName_backward_privateInPublic_warn;
v___x_1512_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0___redArg(v___x_1511_, v___y_1506_);
v_a_1513_ = lean_ctor_get(v___x_1512_, 0);
v_isSharedCheck_1532_ = !lean_is_exclusive(v___x_1512_);
if (v_isSharedCheck_1532_ == 0)
{
v___x_1515_ = v___x_1512_;
v_isShared_1516_ = v_isSharedCheck_1532_;
goto v_resetjp_1514_;
}
else
{
lean_inc(v_a_1513_);
lean_dec(v___x_1512_);
v___x_1515_ = lean_box(0);
v_isShared_1516_ = v_isSharedCheck_1532_;
goto v_resetjp_1514_;
}
v_resetjp_1514_:
{
uint8_t v_isExporting_1522_; 
v_isExporting_1522_ = lean_ctor_get_uint8(v_env_1510_, sizeof(void*)*8);
lean_dec_ref(v_env_1510_);
if (v_isExporting_1522_ == 0)
{
lean_dec(v_a_1513_);
lean_dec_ref(v___y_1506_);
lean_dec(v_id_1505_);
goto v___jp_1517_;
}
else
{
uint8_t v___x_1523_; 
v___x_1523_ = l_Lean_isPrivateName(v_id_1505_);
if (v___x_1523_ == 0)
{
lean_dec(v_a_1513_);
lean_dec_ref(v___y_1506_);
lean_dec(v_id_1505_);
goto v___jp_1517_;
}
else
{
uint8_t v___x_1524_; 
v___x_1524_ = lean_unbox(v_a_1513_);
lean_dec(v_a_1513_);
if (v___x_1524_ == 0)
{
lean_dec_ref(v___y_1506_);
lean_dec(v_id_1505_);
goto v___jp_1517_;
}
else
{
lean_object* v___x_1525_; uint8_t v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; 
lean_del_object(v___x_1515_);
v___x_1525_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__1, &l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__1_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__1);
v___x_1526_ = 0;
v___x_1527_ = l_Lean_MessageData_ofConstName(v_id_1505_, v___x_1526_);
v___x_1528_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1528_, 0, v___x_1525_);
lean_ctor_set(v___x_1528_, 1, v___x_1527_);
v___x_1529_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__3, &l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__3_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__3);
v___x_1530_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1530_, 0, v___x_1528_);
lean_ctor_set(v___x_1530_, 1, v___x_1529_);
v___x_1531_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1(v___x_1530_, v___y_1506_, v___y_1507_);
return v___x_1531_;
}
}
}
v___jp_1517_:
{
lean_object* v___x_1518_; lean_object* v___x_1520_; 
v___x_1518_ = lean_box(0);
if (v_isShared_1516_ == 0)
{
lean_ctor_set(v___x_1515_, 0, v___x_1518_);
v___x_1520_ = v___x_1515_;
goto v_reusejp_1519_;
}
else
{
lean_object* v_reuseFailAlloc_1521_; 
v_reuseFailAlloc_1521_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1521_, 0, v___x_1518_);
v___x_1520_ = v_reuseFailAlloc_1521_;
goto v_reusejp_1519_;
}
v_reusejp_1519_:
{
return v___x_1520_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___boxed(lean_object* v_id_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_){
_start:
{
lean_object* v_res_1537_; 
v_res_1537_ = l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0(v_id_1533_, v___y_1534_, v___y_1535_);
lean_dec(v___y_1535_);
return v_res_1537_;
}
}
static lean_object* _init_l_Lean_ensureAttrDeclIsPublic___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1539_; lean_object* v___x_1540_; 
v___x_1539_ = ((lean_object*)(l_Lean_ensureAttrDeclIsPublic___lam__0___closed__0));
v___x_1540_ = l_Lean_stringToMessageData(v___x_1539_);
return v___x_1540_;
}
}
LEAN_EXPORT lean_object* l_Lean_ensureAttrDeclIsPublic___lam__0(lean_object* v_declName_1541_, uint8_t v_isModule_1542_, lean_object* v_attrName_1543_, lean_object* v___y_1544_, lean_object* v___y_1545_){
_start:
{
lean_object* v___x_1547_; 
lean_inc_ref(v___y_1544_);
lean_inc(v_declName_1541_);
v___x_1547_ = l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0(v_declName_1541_, v___y_1544_, v___y_1545_);
if (lean_obj_tag(v___x_1547_) == 0)
{
lean_object* v___x_1548_; lean_object* v_a_1549_; lean_object* v___x_1551_; uint8_t v_isShared_1552_; uint8_t v_isSharedCheck_1569_; 
lean_dec_ref(v___x_1547_);
lean_inc(v_declName_1541_);
v___x_1548_ = l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1___redArg(v_declName_1541_, v_isModule_1542_, v___y_1545_);
v_a_1549_ = lean_ctor_get(v___x_1548_, 0);
v_isSharedCheck_1569_ = !lean_is_exclusive(v___x_1548_);
if (v_isSharedCheck_1569_ == 0)
{
v___x_1551_ = v___x_1548_;
v_isShared_1552_ = v_isSharedCheck_1569_;
goto v_resetjp_1550_;
}
else
{
lean_inc(v_a_1549_);
lean_dec(v___x_1548_);
v___x_1551_ = lean_box(0);
v_isShared_1552_ = v_isSharedCheck_1569_;
goto v_resetjp_1550_;
}
v_resetjp_1550_:
{
uint8_t v___x_1553_; 
v___x_1553_ = lean_unbox(v_a_1549_);
if (v___x_1553_ == 0)
{
lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; uint8_t v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; 
lean_del_object(v___x_1551_);
v___x_1554_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1);
v___x_1555_ = l_Lean_MessageData_ofName(v_attrName_1543_);
v___x_1556_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1556_, 0, v___x_1554_);
lean_ctor_set(v___x_1556_, 1, v___x_1555_);
v___x_1557_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1, &l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1);
v___x_1558_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1558_, 0, v___x_1556_);
lean_ctor_set(v___x_1558_, 1, v___x_1557_);
v___x_1559_ = lean_unbox(v_a_1549_);
lean_dec(v_a_1549_);
v___x_1560_ = l_Lean_MessageData_ofConstName(v_declName_1541_, v___x_1559_);
v___x_1561_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1561_, 0, v___x_1558_);
lean_ctor_set(v___x_1561_, 1, v___x_1560_);
v___x_1562_ = lean_obj_once(&l_Lean_ensureAttrDeclIsPublic___lam__0___closed__1, &l_Lean_ensureAttrDeclIsPublic___lam__0___closed__1_once, _init_l_Lean_ensureAttrDeclIsPublic___lam__0___closed__1);
v___x_1563_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1563_, 0, v___x_1561_);
lean_ctor_set(v___x_1563_, 1, v___x_1562_);
v___x_1564_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0_spec__0___redArg(v___x_1563_, v___y_1544_, v___y_1545_);
lean_dec_ref(v___y_1544_);
return v___x_1564_;
}
else
{
lean_object* v___x_1565_; lean_object* v___x_1567_; 
lean_dec(v_a_1549_);
lean_dec_ref(v___y_1544_);
lean_dec(v_attrName_1543_);
lean_dec(v_declName_1541_);
v___x_1565_ = lean_box(0);
if (v_isShared_1552_ == 0)
{
lean_ctor_set(v___x_1551_, 0, v___x_1565_);
v___x_1567_ = v___x_1551_;
goto v_reusejp_1566_;
}
else
{
lean_object* v_reuseFailAlloc_1568_; 
v_reuseFailAlloc_1568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1568_, 0, v___x_1565_);
v___x_1567_ = v_reuseFailAlloc_1568_;
goto v_reusejp_1566_;
}
v_reusejp_1566_:
{
return v___x_1567_;
}
}
}
}
else
{
lean_dec_ref(v___y_1544_);
lean_dec(v_attrName_1543_);
lean_dec(v_declName_1541_);
return v___x_1547_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ensureAttrDeclIsPublic___lam__0___boxed(lean_object* v_declName_1570_, lean_object* v_isModule_1571_, lean_object* v_attrName_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_, lean_object* v___y_1575_){
_start:
{
uint8_t v_isModule_boxed_1576_; lean_object* v_res_1577_; 
v_isModule_boxed_1576_ = lean_unbox(v_isModule_1571_);
v_res_1577_ = l_Lean_ensureAttrDeclIsPublic___lam__0(v_declName_1570_, v_isModule_boxed_1576_, v_attrName_1572_, v___y_1573_, v___y_1574_);
lean_dec(v___y_1574_);
return v_res_1577_;
}
}
LEAN_EXPORT lean_object* l_Lean_ensureAttrDeclIsPublic(lean_object* v_attrName_1578_, lean_object* v_declName_1579_, uint8_t v_attrKind_1580_, lean_object* v_a_1581_, lean_object* v_a_1582_){
_start:
{
lean_object* v___x_1584_; lean_object* v_env_1588_; lean_object* v___x_1589_; uint8_t v_isModule_1590_; 
v___x_1584_ = lean_st_ref_get(v_a_1582_);
v_env_1588_ = lean_ctor_get(v___x_1584_, 0);
lean_inc_ref(v_env_1588_);
lean_dec(v___x_1584_);
v___x_1589_ = l_Lean_Environment_header(v_env_1588_);
lean_dec_ref(v_env_1588_);
v_isModule_1590_ = lean_ctor_get_uint8(v___x_1589_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_1589_);
if (v_isModule_1590_ == 0)
{
lean_dec(v_a_1582_);
lean_dec_ref(v_a_1581_);
lean_dec(v_declName_1579_);
lean_dec(v_attrName_1578_);
goto v___jp_1585_;
}
else
{
uint8_t v___x_1591_; uint8_t v___x_1592_; 
v___x_1591_ = 1;
v___x_1592_ = l_Lean_instBEqAttributeKind_beq(v_attrKind_1580_, v___x_1591_);
if (v___x_1592_ == 0)
{
lean_object* v___x_1593_; lean_object* v___f_1594_; lean_object* v___x_1595_; 
v___x_1593_ = lean_box(v_isModule_1590_);
v___f_1594_ = lean_alloc_closure((void*)(l_Lean_ensureAttrDeclIsPublic___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1594_, 0, v_declName_1579_);
lean_closure_set(v___f_1594_, 1, v___x_1593_);
lean_closure_set(v___f_1594_, 2, v_attrName_1578_);
v___x_1595_ = l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg(v___f_1594_, v_isModule_1590_, v_a_1581_, v_a_1582_);
return v___x_1595_;
}
else
{
lean_dec(v_a_1582_);
lean_dec_ref(v_a_1581_);
lean_dec(v_declName_1579_);
lean_dec(v_attrName_1578_);
goto v___jp_1585_;
}
}
v___jp_1585_:
{
lean_object* v___x_1586_; lean_object* v___x_1587_; 
v___x_1586_ = lean_box(0);
v___x_1587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1587_, 0, v___x_1586_);
return v___x_1587_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ensureAttrDeclIsPublic___boxed(lean_object* v_attrName_1596_, lean_object* v_declName_1597_, lean_object* v_attrKind_1598_, lean_object* v_a_1599_, lean_object* v_a_1600_, lean_object* v_a_1601_){
_start:
{
uint8_t v_attrKind_boxed_1602_; lean_object* v_res_1603_; 
v_attrKind_boxed_1602_ = lean_unbox(v_attrKind_1598_);
v_res_1603_ = l_Lean_ensureAttrDeclIsPublic(v_attrName_1596_, v_declName_1597_, v_attrKind_boxed_1602_, v_a_1599_, v_a_1600_);
return v_res_1603_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0(lean_object* v_opt_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_){
_start:
{
lean_object* v___x_1608_; 
v___x_1608_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0___redArg(v_opt_1604_, v___y_1605_);
return v___x_1608_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0___boxed(lean_object* v_opt_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_){
_start:
{
lean_object* v_res_1613_; 
v_res_1613_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0(v_opt_1609_, v___y_1610_, v___y_1611_);
lean_dec(v___y_1611_);
lean_dec_ref(v___y_1610_);
lean_dec_ref(v_opt_1609_);
return v_res_1613_;
}
}
static lean_object* _init_l_Lean_ensureAttrDeclIsMeta___closed__1(void){
_start:
{
lean_object* v___x_1615_; lean_object* v___x_1616_; 
v___x_1615_ = ((lean_object*)(l_Lean_ensureAttrDeclIsMeta___closed__0));
v___x_1616_ = l_Lean_stringToMessageData(v___x_1615_);
return v___x_1616_;
}
}
LEAN_EXPORT lean_object* l_Lean_ensureAttrDeclIsMeta(lean_object* v_attrName_1617_, lean_object* v_declName_1618_, uint8_t v_attrKind_1619_, lean_object* v_a_1620_, lean_object* v_a_1621_){
_start:
{
lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v_env_1625_; lean_object* v___x_1626_; uint8_t v_isModule_1627_; 
v___x_1623_ = lean_st_ref_get(v_a_1621_);
v___x_1624_ = lean_st_ref_get(v_a_1621_);
v_env_1625_ = lean_ctor_get(v___x_1623_, 0);
lean_inc_ref(v_env_1625_);
lean_dec(v___x_1623_);
v___x_1626_ = l_Lean_Environment_header(v_env_1625_);
lean_dec_ref(v_env_1625_);
v_isModule_1627_ = lean_ctor_get_uint8(v___x_1626_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_1626_);
if (v_isModule_1627_ == 0)
{
lean_object* v___x_1628_; 
lean_dec(v___x_1624_);
v___x_1628_ = l_Lean_ensureAttrDeclIsPublic(v_attrName_1617_, v_declName_1618_, v_attrKind_1619_, v_a_1620_, v_a_1621_);
return v___x_1628_;
}
else
{
lean_object* v_env_1629_; uint8_t v___x_1630_; 
v_env_1629_ = lean_ctor_get(v___x_1624_, 0);
lean_inc_ref(v_env_1629_);
lean_dec(v___x_1624_);
lean_inc(v_declName_1618_);
v___x_1630_ = l_Lean_isMarkedMeta(v_env_1629_, v_declName_1618_);
if (v___x_1630_ == 0)
{
lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; 
v___x_1631_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1);
v___x_1632_ = l_Lean_MessageData_ofName(v_attrName_1617_);
v___x_1633_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1633_, 0, v___x_1631_);
lean_ctor_set(v___x_1633_, 1, v___x_1632_);
v___x_1634_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1, &l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1);
v___x_1635_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1635_, 0, v___x_1633_);
lean_ctor_set(v___x_1635_, 1, v___x_1634_);
v___x_1636_ = l_Lean_MessageData_ofConstName(v_declName_1618_, v___x_1630_);
v___x_1637_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1637_, 0, v___x_1635_);
lean_ctor_set(v___x_1637_, 1, v___x_1636_);
v___x_1638_ = lean_obj_once(&l_Lean_ensureAttrDeclIsMeta___closed__1, &l_Lean_ensureAttrDeclIsMeta___closed__1_once, _init_l_Lean_ensureAttrDeclIsMeta___closed__1);
v___x_1639_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1639_, 0, v___x_1637_);
lean_ctor_set(v___x_1639_, 1, v___x_1638_);
v___x_1640_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0_spec__0___redArg(v___x_1639_, v_a_1620_, v_a_1621_);
lean_dec(v_a_1621_);
lean_dec_ref(v_a_1620_);
return v___x_1640_;
}
else
{
lean_object* v___x_1641_; 
v___x_1641_ = l_Lean_ensureAttrDeclIsPublic(v_attrName_1617_, v_declName_1618_, v_attrKind_1619_, v_a_1620_, v_a_1621_);
return v___x_1641_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ensureAttrDeclIsMeta___boxed(lean_object* v_attrName_1642_, lean_object* v_declName_1643_, lean_object* v_attrKind_1644_, lean_object* v_a_1645_, lean_object* v_a_1646_, lean_object* v_a_1647_){
_start:
{
uint8_t v_attrKind_boxed_1648_; lean_object* v_res_1649_; 
v_attrKind_boxed_1648_ = lean_unbox(v_attrKind_1644_);
v_res_1649_ = l_Lean_ensureAttrDeclIsMeta(v_attrName_1642_, v_declName_1643_, v_attrKind_boxed_1648_, v_a_1645_, v_a_1646_);
return v_res_1649_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__0(lean_object* v_x_1653_, lean_object* v___y_1654_){
_start:
{
lean_object* v___x_1656_; lean_object* v___x_1657_; 
v___x_1656_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___lam__0___closed__1));
v___x_1657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1657_, 0, v___x_1656_);
return v___x_1657_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__0___boxed(lean_object* v_x_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_){
_start:
{
lean_object* v_res_1661_; 
v_res_1661_ = l_Lean_instInhabitedTagAttribute_default___lam__0(v_x_1658_, v___y_1659_);
lean_dec_ref(v___y_1659_);
lean_dec_ref(v_x_1658_);
return v_res_1661_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__1(lean_object* v_s_1662_, lean_object* v_x_1663_){
_start:
{
lean_inc(v_s_1662_);
return v_s_1662_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__1___boxed(lean_object* v_s_1664_, lean_object* v_x_1665_){
_start:
{
lean_object* v_res_1666_; 
v_res_1666_ = l_Lean_instInhabitedTagAttribute_default___lam__1(v_s_1664_, v_x_1665_);
lean_dec(v_x_1665_);
lean_dec(v_s_1664_);
return v_res_1666_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__2(lean_object* v_x_1669_, lean_object* v_x_1670_, uint8_t v_x_1671_){
_start:
{
lean_object* v___x_1672_; 
v___x_1672_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___lam__2___closed__0));
return v___x_1672_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__2___boxed(lean_object* v_x_1673_, lean_object* v_x_1674_, lean_object* v_x_1675_){
_start:
{
uint8_t v_x_77__boxed_1676_; lean_object* v_res_1677_; 
v_x_77__boxed_1676_ = lean_unbox(v_x_1675_);
v_res_1677_ = l_Lean_instInhabitedTagAttribute_default___lam__2(v_x_1673_, v_x_1674_, v_x_77__boxed_1676_);
lean_dec(v_x_1674_);
lean_dec_ref(v_x_1673_);
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
v___x_1686_ = l_Lean_instInhabitedEnvExtension_default(lean_box(0));
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
lean_dec_ref(v_x_1706_);
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
lean_dec_ref(v_s_1739_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__2___redArg(lean_object* v_as_1749_, lean_object* v_lo_1750_, lean_object* v_hi_1751_){
_start:
{
uint8_t v___x_1752_; 
v___x_1752_ = lean_nat_dec_lt(v_lo_1750_, v_hi_1751_);
if (v___x_1752_ == 0)
{
lean_dec(v_lo_1750_);
return v_as_1749_;
}
else
{
lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v_fst_1755_; lean_object* v_snd_1756_; uint8_t v___x_1757_; 
v___x_1753_ = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__2___redArg___closed__0));
lean_inc(v_lo_1750_);
v___x_1754_ = l_Array_qpartition___redArg(v_as_1749_, v___x_1753_, v_lo_1750_, v_hi_1751_);
v_fst_1755_ = lean_ctor_get(v___x_1754_, 0);
lean_inc(v_fst_1755_);
v_snd_1756_ = lean_ctor_get(v___x_1754_, 1);
lean_inc(v_snd_1756_);
lean_dec_ref(v___x_1754_);
v___x_1757_ = lean_nat_dec_le(v_hi_1751_, v_fst_1755_);
if (v___x_1757_ == 0)
{
lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; 
v___x_1758_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__2___redArg(v_snd_1756_, v_lo_1750_, v_fst_1755_);
v___x_1759_ = lean_unsigned_to_nat(1u);
v___x_1760_ = lean_nat_add(v_fst_1755_, v___x_1759_);
lean_dec(v_fst_1755_);
v_as_1749_ = v___x_1758_;
v_lo_1750_ = v___x_1760_;
goto _start;
}
else
{
lean_dec(v_fst_1755_);
lean_dec(v_lo_1750_);
return v_snd_1756_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__2___redArg___boxed(lean_object* v_as_1762_, lean_object* v_lo_1763_, lean_object* v_hi_1764_){
_start:
{
lean_object* v_res_1765_; 
v_res_1765_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__2___redArg(v_as_1762_, v_lo_1763_, v_hi_1764_);
lean_dec(v_hi_1764_);
return v_res_1765_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerTagAttribute_spec__3(lean_object* v_env_1766_, lean_object* v_as_1767_, size_t v_i_1768_, size_t v_stop_1769_, lean_object* v_b_1770_){
_start:
{
lean_object* v___y_1772_; uint8_t v___x_1776_; 
v___x_1776_ = lean_usize_dec_eq(v_i_1768_, v_stop_1769_);
if (v___x_1776_ == 0)
{
lean_object* v___x_1777_; uint8_t v___x_1778_; 
v___x_1777_ = lean_array_uget_borrowed(v_as_1767_, v_i_1768_);
lean_inc(v___x_1777_);
lean_inc_ref(v_env_1766_);
v___x_1778_ = l_Lean_Environment_contains(v_env_1766_, v___x_1777_, v___x_1776_);
if (v___x_1778_ == 0)
{
v___y_1772_ = v_b_1770_;
goto v___jp_1771_;
}
else
{
lean_object* v___x_1779_; 
lean_inc(v___x_1777_);
v___x_1779_ = lean_array_push(v_b_1770_, v___x_1777_);
v___y_1772_ = v___x_1779_;
goto v___jp_1771_;
}
}
else
{
lean_dec_ref(v_env_1766_);
return v_b_1770_;
}
v___jp_1771_:
{
size_t v___x_1773_; size_t v___x_1774_; 
v___x_1773_ = ((size_t)1ULL);
v___x_1774_ = lean_usize_add(v_i_1768_, v___x_1773_);
v_i_1768_ = v___x_1774_;
v_b_1770_ = v___y_1772_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerTagAttribute_spec__3___boxed(lean_object* v_env_1780_, lean_object* v_as_1781_, lean_object* v_i_1782_, lean_object* v_stop_1783_, lean_object* v_b_1784_){
_start:
{
size_t v_i_boxed_1785_; size_t v_stop_boxed_1786_; lean_object* v_res_1787_; 
v_i_boxed_1785_ = lean_unbox_usize(v_i_1782_);
lean_dec(v_i_1782_);
v_stop_boxed_1786_ = lean_unbox_usize(v_stop_1783_);
lean_dec(v_stop_1783_);
v_res_1787_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerTagAttribute_spec__3(v_env_1780_, v_as_1781_, v_i_boxed_1785_, v_stop_boxed_1786_, v_b_1784_);
lean_dec_ref(v_as_1781_);
return v_res_1787_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerTagAttribute_spec__1_spec__1(lean_object* v_init_1788_, lean_object* v_x_1789_){
_start:
{
if (lean_obj_tag(v_x_1789_) == 0)
{
lean_object* v_k_1790_; lean_object* v_l_1791_; lean_object* v_r_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; 
v_k_1790_ = lean_ctor_get(v_x_1789_, 1);
lean_inc(v_k_1790_);
v_l_1791_ = lean_ctor_get(v_x_1789_, 3);
lean_inc(v_l_1791_);
v_r_1792_ = lean_ctor_get(v_x_1789_, 4);
lean_inc(v_r_1792_);
lean_dec_ref(v_x_1789_);
v___x_1793_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerTagAttribute_spec__1_spec__1(v_init_1788_, v_l_1791_);
v___x_1794_ = lean_array_push(v___x_1793_, v_k_1790_);
v_init_1788_ = v___x_1794_;
v_x_1789_ = v_r_1792_;
goto _start;
}
else
{
return v_init_1788_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__3(lean_object* v_env_1796_, lean_object* v_es_1797_, uint8_t v_x_1798_){
_start:
{
lean_object* v___y_1800_; lean_object* v___y_1801_; lean_object* v___y_1802_; lean_object* v___y_1803_; lean_object* v___x_1807_; lean_object* v___y_1809_; lean_object* v___x_1815_; lean_object* v_r_1816_; lean_object* v___x_1817_; uint8_t v___x_1818_; 
v___x_1807_ = lean_unsigned_to_nat(0u);
v___x_1815_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___lam__2___closed__0));
v_r_1816_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerTagAttribute_spec__1_spec__1(v___x_1815_, v_es_1797_);
v___x_1817_ = lean_array_get_size(v_r_1816_);
v___x_1818_ = lean_nat_dec_lt(v___x_1807_, v___x_1817_);
if (v___x_1818_ == 0)
{
lean_dec_ref(v_r_1816_);
lean_dec_ref(v_env_1796_);
v___y_1809_ = v___x_1815_;
goto v___jp_1808_;
}
else
{
uint8_t v___x_1819_; 
v___x_1819_ = lean_nat_dec_le(v___x_1817_, v___x_1817_);
if (v___x_1819_ == 0)
{
if (v___x_1818_ == 0)
{
lean_dec_ref(v_r_1816_);
lean_dec_ref(v_env_1796_);
v___y_1809_ = v___x_1815_;
goto v___jp_1808_;
}
else
{
size_t v___x_1820_; size_t v___x_1821_; lean_object* v___x_1822_; 
v___x_1820_ = ((size_t)0ULL);
v___x_1821_ = lean_usize_of_nat(v___x_1817_);
v___x_1822_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerTagAttribute_spec__3(v_env_1796_, v_r_1816_, v___x_1820_, v___x_1821_, v___x_1815_);
lean_dec_ref(v_r_1816_);
v___y_1809_ = v___x_1822_;
goto v___jp_1808_;
}
}
else
{
size_t v___x_1823_; size_t v___x_1824_; lean_object* v___x_1825_; 
v___x_1823_ = ((size_t)0ULL);
v___x_1824_ = lean_usize_of_nat(v___x_1817_);
v___x_1825_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerTagAttribute_spec__3(v_env_1796_, v_r_1816_, v___x_1823_, v___x_1824_, v___x_1815_);
lean_dec_ref(v_r_1816_);
v___y_1809_ = v___x_1825_;
goto v___jp_1808_;
}
}
v___jp_1799_:
{
uint8_t v___x_1804_; 
lean_dec(v___y_1801_);
v___x_1804_ = lean_nat_dec_le(v___y_1803_, v___y_1802_);
if (v___x_1804_ == 0)
{
lean_object* v___x_1805_; 
lean_dec(v___y_1802_);
lean_inc(v___y_1803_);
v___x_1805_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__2___redArg(v___y_1800_, v___y_1803_, v___y_1803_);
lean_dec(v___y_1803_);
return v___x_1805_;
}
else
{
lean_object* v___x_1806_; 
v___x_1806_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__2___redArg(v___y_1800_, v___y_1803_, v___y_1802_);
lean_dec(v___y_1802_);
return v___x_1806_;
}
}
v___jp_1808_:
{
lean_object* v___x_1810_; uint8_t v___x_1811_; 
v___x_1810_ = lean_array_get_size(v___y_1809_);
v___x_1811_ = lean_nat_dec_eq(v___x_1810_, v___x_1807_);
if (v___x_1811_ == 0)
{
lean_object* v___x_1812_; lean_object* v___x_1813_; uint8_t v___x_1814_; 
v___x_1812_ = lean_unsigned_to_nat(1u);
v___x_1813_ = lean_nat_sub(v___x_1810_, v___x_1812_);
v___x_1814_ = lean_nat_dec_le(v___x_1807_, v___x_1813_);
if (v___x_1814_ == 0)
{
lean_inc(v___x_1813_);
v___y_1800_ = v___y_1809_;
v___y_1801_ = v___x_1810_;
v___y_1802_ = v___x_1813_;
v___y_1803_ = v___x_1813_;
goto v___jp_1799_;
}
else
{
v___y_1800_ = v___y_1809_;
v___y_1801_ = v___x_1810_;
v___y_1802_ = v___x_1813_;
v___y_1803_ = v___x_1807_;
goto v___jp_1799_;
}
}
else
{
return v___y_1809_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__3___boxed(lean_object* v_env_1826_, lean_object* v_es_1827_, lean_object* v_x_1828_){
_start:
{
uint8_t v_x_2365__boxed_1829_; lean_object* v_res_1830_; 
v_x_2365__boxed_1829_ = lean_unbox(v_x_1828_);
v_res_1830_ = l_Lean_registerTagAttribute___lam__3(v_env_1826_, v_es_1827_, v_x_2365__boxed_1829_);
return v_res_1830_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__4(lean_object* v___x_1831_){
_start:
{
lean_object* v___x_1833_; 
v___x_1833_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1833_, 0, v___x_1831_);
return v___x_1833_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__4___boxed(lean_object* v___x_1834_, lean_object* v___y_1835_){
_start:
{
lean_object* v_res_1836_; 
v_res_1836_ = l_Lean_registerTagAttribute___lam__4(v___x_1834_);
return v_res_1836_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__5(lean_object* v___x_1837_, lean_object* v_x_1838_, lean_object* v_x_1839_){
_start:
{
lean_object* v___x_1841_; 
v___x_1841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1841_, 0, v___x_1837_);
return v___x_1841_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__5___boxed(lean_object* v___x_1842_, lean_object* v_x_1843_, lean_object* v_x_1844_, lean_object* v___y_1845_){
_start:
{
lean_object* v_res_1846_; 
v_res_1846_ = l_Lean_registerTagAttribute___lam__5(v___x_1842_, v_x_1843_, v_x_1844_);
lean_dec_ref(v_x_1844_);
lean_dec_ref(v_x_1843_);
return v_res_1846_;
}
}
static lean_object* _init_l_Lean_registerTagAttribute___lam__6___closed__1(void){
_start:
{
lean_object* v___x_1848_; lean_object* v___x_1849_; 
v___x_1848_ = ((lean_object*)(l_Lean_registerTagAttribute___lam__6___closed__0));
v___x_1849_ = l_Lean_stringToMessageData(v___x_1848_);
return v___x_1849_;
}
}
static lean_object* _init_l_Lean_registerTagAttribute___lam__6___closed__3(void){
_start:
{
lean_object* v___x_1851_; lean_object* v___x_1852_; 
v___x_1851_ = ((lean_object*)(l_Lean_registerTagAttribute___lam__6___closed__2));
v___x_1852_ = l_Lean_stringToMessageData(v___x_1851_);
return v___x_1852_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__6(lean_object* v_name_1853_, lean_object* v_decl_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_){
_start:
{
lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; 
v___x_1858_ = lean_obj_once(&l_Lean_registerTagAttribute___lam__6___closed__1, &l_Lean_registerTagAttribute___lam__6___closed__1_once, _init_l_Lean_registerTagAttribute___lam__6___closed__1);
v___x_1859_ = l_Lean_MessageData_ofName(v_name_1853_);
v___x_1860_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1860_, 0, v___x_1858_);
lean_ctor_set(v___x_1860_, 1, v___x_1859_);
v___x_1861_ = lean_obj_once(&l_Lean_registerTagAttribute___lam__6___closed__3, &l_Lean_registerTagAttribute___lam__6___closed__3_once, _init_l_Lean_registerTagAttribute___lam__6___closed__3);
v___x_1862_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1862_, 0, v___x_1860_);
lean_ctor_set(v___x_1862_, 1, v___x_1861_);
v___x_1863_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0_spec__0___redArg(v___x_1862_, v___y_1855_, v___y_1856_);
return v___x_1863_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__6___boxed(lean_object* v_name_1864_, lean_object* v_decl_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_){
_start:
{
lean_object* v_res_1869_; 
v_res_1869_ = l_Lean_registerTagAttribute___lam__6(v_name_1864_, v_decl_1865_, v___y_1866_, v___y_1867_);
lean_dec(v___y_1867_);
lean_dec_ref(v___y_1866_);
lean_dec(v_decl_1865_);
return v_res_1869_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg(lean_object* v_attrName_1870_, lean_object* v_declName_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_){
_start:
{
lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; uint8_t v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; 
v___x_1875_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1);
v___x_1876_ = l_Lean_MessageData_ofName(v_attrName_1870_);
v___x_1877_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1877_, 0, v___x_1875_);
lean_ctor_set(v___x_1877_, 1, v___x_1876_);
v___x_1878_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__3, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__3_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__3);
v___x_1879_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1879_, 0, v___x_1877_);
lean_ctor_set(v___x_1879_, 1, v___x_1878_);
v___x_1880_ = 0;
v___x_1881_ = l_Lean_MessageData_ofConstName(v_declName_1871_, v___x_1880_);
v___x_1882_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1882_, 0, v___x_1879_);
lean_ctor_set(v___x_1882_, 1, v___x_1881_);
v___x_1883_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__5, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__5_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__5);
v___x_1884_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1884_, 0, v___x_1882_);
lean_ctor_set(v___x_1884_, 1, v___x_1883_);
v___x_1885_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0_spec__0___redArg(v___x_1884_, v___y_1872_, v___y_1873_);
return v___x_1885_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg___boxed(lean_object* v_attrName_1886_, lean_object* v_declName_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_){
_start:
{
lean_object* v_res_1891_; 
v_res_1891_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg(v_attrName_1886_, v_declName_1887_, v___y_1888_, v___y_1889_);
lean_dec(v___y_1889_);
lean_dec_ref(v___y_1888_);
return v_res_1891_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___redArg(lean_object* v_attrName_1892_, lean_object* v_declName_1893_, lean_object* v_asyncPrefix_x3f_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_){
_start:
{
lean_object* v___y_1899_; 
if (lean_obj_tag(v_asyncPrefix_x3f_1894_) == 0)
{
lean_object* v___x_1912_; 
v___x_1912_ = l_Lean_MessageData_nil;
v___y_1899_ = v___x_1912_;
goto v___jp_1898_;
}
else
{
lean_object* v_val_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; 
v_val_1913_ = lean_ctor_get(v_asyncPrefix_x3f_1894_, 0);
lean_inc(v_val_1913_);
lean_dec_ref(v_asyncPrefix_x3f_1894_);
v___x_1914_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___redArg___closed__3, &l_Lean_throwAttrNotInAsyncCtx___redArg___closed__3_once, _init_l_Lean_throwAttrNotInAsyncCtx___redArg___closed__3);
v___x_1915_ = l_Lean_MessageData_ofName(v_val_1913_);
v___x_1916_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1916_, 0, v___x_1914_);
lean_ctor_set(v___x_1916_, 1, v___x_1915_);
v___x_1917_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__5, &l_Lean_throwAttrMustBeGlobal___redArg___closed__5_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__5);
v___x_1918_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1918_, 0, v___x_1916_);
lean_ctor_set(v___x_1918_, 1, v___x_1917_);
v___y_1899_ = v___x_1918_;
goto v___jp_1898_;
}
v___jp_1898_:
{
lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; uint8_t v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; 
v___x_1900_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1);
v___x_1901_ = l_Lean_MessageData_ofName(v_attrName_1892_);
v___x_1902_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1902_, 0, v___x_1900_);
lean_ctor_set(v___x_1902_, 1, v___x_1901_);
v___x_1903_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__3, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__3_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__3);
v___x_1904_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1904_, 0, v___x_1902_);
lean_ctor_set(v___x_1904_, 1, v___x_1903_);
v___x_1905_ = 0;
v___x_1906_ = l_Lean_MessageData_ofConstName(v_declName_1893_, v___x_1905_);
v___x_1907_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1907_, 0, v___x_1904_);
lean_ctor_set(v___x_1907_, 1, v___x_1906_);
v___x_1908_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___redArg___closed__1, &l_Lean_throwAttrNotInAsyncCtx___redArg___closed__1_once, _init_l_Lean_throwAttrNotInAsyncCtx___redArg___closed__1);
v___x_1909_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1909_, 0, v___x_1907_);
lean_ctor_set(v___x_1909_, 1, v___x_1908_);
v___x_1910_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1910_, 0, v___x_1909_);
lean_ctor_set(v___x_1910_, 1, v___y_1899_);
v___x_1911_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0_spec__0___redArg(v___x_1910_, v___y_1895_, v___y_1896_);
return v___x_1911_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___redArg___boxed(lean_object* v_attrName_1919_, lean_object* v_declName_1920_, lean_object* v_asyncPrefix_x3f_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_){
_start:
{
lean_object* v_res_1925_; 
v_res_1925_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___redArg(v_attrName_1919_, v_declName_1920_, v_asyncPrefix_x3f_1921_, v___y_1922_, v___y_1923_);
lean_dec(v___y_1923_);
lean_dec_ref(v___y_1922_);
return v_res_1925_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg(lean_object* v_name_1926_, uint8_t v_kind_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_){
_start:
{
lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___y_1937_; 
v___x_1931_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__1, &l_Lean_throwAttrMustBeGlobal___redArg___closed__1_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__1);
v___x_1932_ = l_Lean_MessageData_ofName(v_name_1926_);
v___x_1933_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1933_, 0, v___x_1931_);
lean_ctor_set(v___x_1933_, 1, v___x_1932_);
v___x_1934_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__3, &l_Lean_throwAttrMustBeGlobal___redArg___closed__3_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__3);
v___x_1935_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1935_, 0, v___x_1933_);
lean_ctor_set(v___x_1935_, 1, v___x_1934_);
switch(v_kind_1927_)
{
case 0:
{
lean_object* v___x_1944_; 
v___x_1944_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__0));
v___y_1937_ = v___x_1944_;
goto v___jp_1936_;
}
case 1:
{
lean_object* v___x_1945_; 
v___x_1945_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__1));
v___y_1937_ = v___x_1945_;
goto v___jp_1936_;
}
default: 
{
lean_object* v___x_1946_; 
v___x_1946_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__2));
v___y_1937_ = v___x_1946_;
goto v___jp_1936_;
}
}
v___jp_1936_:
{
lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; 
v___x_1938_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1938_, 0, v___y_1937_);
v___x_1939_ = l_Lean_MessageData_ofFormat(v___x_1938_);
v___x_1940_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1940_, 0, v___x_1935_);
lean_ctor_set(v___x_1940_, 1, v___x_1939_);
v___x_1941_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__5, &l_Lean_throwAttrMustBeGlobal___redArg___closed__5_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__5);
v___x_1942_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1942_, 0, v___x_1940_);
lean_ctor_set(v___x_1942_, 1, v___x_1941_);
v___x_1943_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0_spec__0___redArg(v___x_1942_, v___y_1928_, v___y_1929_);
return v___x_1943_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg___boxed(lean_object* v_name_1947_, lean_object* v_kind_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_){
_start:
{
uint8_t v_kind_boxed_1952_; lean_object* v_res_1953_; 
v_kind_boxed_1952_ = lean_unbox(v_kind_1948_);
v_res_1953_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg(v_name_1947_, v_kind_boxed_1952_, v___y_1949_, v___y_1950_);
lean_dec(v___y_1950_);
lean_dec_ref(v___y_1949_);
return v_res_1953_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__7(lean_object* v_validate_1954_, lean_object* v_a_1955_, lean_object* v_name_1956_, lean_object* v_decl_1957_, lean_object* v_stx_1958_, uint8_t v_kind_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_){
_start:
{
lean_object* v___y_1964_; lean_object* v___y_1965_; lean_object* v___y_1999_; lean_object* v___y_2000_; lean_object* v___y_2001_; lean_object* v___y_2008_; lean_object* v___y_2009_; lean_object* v___x_2014_; 
lean_inc_ref(v___y_1960_);
v___x_2014_ = l_Lean_Attribute_Builtin_ensureNoArgs(v_stx_1958_, v___y_1960_, v___y_1961_);
if (lean_obj_tag(v___x_2014_) == 0)
{
uint8_t v___x_2015_; uint8_t v___x_2016_; 
lean_dec_ref(v___x_2014_);
v___x_2015_ = 0;
v___x_2016_ = l_Lean_instBEqAttributeKind_beq(v_kind_1959_, v___x_2015_);
if (v___x_2016_ == 0)
{
lean_object* v___x_2017_; 
lean_dec(v_decl_1957_);
lean_dec_ref(v_a_1955_);
lean_dec_ref(v_validate_1954_);
v___x_2017_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg(v_name_1956_, v_kind_1959_, v___y_1960_, v___y_1961_);
lean_dec(v___y_1961_);
lean_dec_ref(v___y_1960_);
return v___x_2017_;
}
else
{
v___y_2008_ = v___y_1960_;
v___y_2009_ = v___y_1961_;
goto v___jp_2007_;
}
}
else
{
lean_dec(v___y_1961_);
lean_dec_ref(v___y_1960_);
lean_dec(v_decl_1957_);
lean_dec(v_name_1956_);
lean_dec_ref(v_a_1955_);
lean_dec_ref(v_validate_1954_);
return v___x_2014_;
}
v___jp_1963_:
{
lean_object* v___x_1966_; 
lean_inc(v___y_1965_);
lean_inc(v_decl_1957_);
v___x_1966_ = lean_apply_4(v_validate_1954_, v_decl_1957_, v___y_1964_, v___y_1965_, lean_box(0));
if (lean_obj_tag(v___x_1966_) == 0)
{
lean_object* v___x_1968_; uint8_t v_isShared_1969_; uint8_t v_isSharedCheck_1996_; 
v_isSharedCheck_1996_ = !lean_is_exclusive(v___x_1966_);
if (v_isSharedCheck_1996_ == 0)
{
lean_object* v_unused_1997_; 
v_unused_1997_ = lean_ctor_get(v___x_1966_, 0);
lean_dec(v_unused_1997_);
v___x_1968_ = v___x_1966_;
v_isShared_1969_ = v_isSharedCheck_1996_;
goto v_resetjp_1967_;
}
else
{
lean_dec(v___x_1966_);
v___x_1968_ = lean_box(0);
v_isShared_1969_ = v_isSharedCheck_1996_;
goto v_resetjp_1967_;
}
v_resetjp_1967_:
{
lean_object* v___x_1970_; lean_object* v_toEnvExtension_1971_; lean_object* v_env_1972_; lean_object* v_nextMacroScope_1973_; lean_object* v_ngen_1974_; lean_object* v_auxDeclNGen_1975_; lean_object* v_traceState_1976_; lean_object* v_messages_1977_; lean_object* v_infoState_1978_; lean_object* v_snapshotTasks_1979_; lean_object* v___x_1981_; uint8_t v_isShared_1982_; uint8_t v_isSharedCheck_1994_; 
v___x_1970_ = lean_st_ref_take(v___y_1965_);
v_toEnvExtension_1971_ = lean_ctor_get(v_a_1955_, 0);
v_env_1972_ = lean_ctor_get(v___x_1970_, 0);
v_nextMacroScope_1973_ = lean_ctor_get(v___x_1970_, 1);
v_ngen_1974_ = lean_ctor_get(v___x_1970_, 2);
v_auxDeclNGen_1975_ = lean_ctor_get(v___x_1970_, 3);
v_traceState_1976_ = lean_ctor_get(v___x_1970_, 4);
v_messages_1977_ = lean_ctor_get(v___x_1970_, 6);
v_infoState_1978_ = lean_ctor_get(v___x_1970_, 7);
v_snapshotTasks_1979_ = lean_ctor_get(v___x_1970_, 8);
v_isSharedCheck_1994_ = !lean_is_exclusive(v___x_1970_);
if (v_isSharedCheck_1994_ == 0)
{
lean_object* v_unused_1995_; 
v_unused_1995_ = lean_ctor_get(v___x_1970_, 5);
lean_dec(v_unused_1995_);
v___x_1981_ = v___x_1970_;
v_isShared_1982_ = v_isSharedCheck_1994_;
goto v_resetjp_1980_;
}
else
{
lean_inc(v_snapshotTasks_1979_);
lean_inc(v_infoState_1978_);
lean_inc(v_messages_1977_);
lean_inc(v_traceState_1976_);
lean_inc(v_auxDeclNGen_1975_);
lean_inc(v_ngen_1974_);
lean_inc(v_nextMacroScope_1973_);
lean_inc(v_env_1972_);
lean_dec(v___x_1970_);
v___x_1981_ = lean_box(0);
v_isShared_1982_ = v_isSharedCheck_1994_;
goto v_resetjp_1980_;
}
v_resetjp_1980_:
{
lean_object* v_asyncMode_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; lean_object* v___x_1987_; 
v_asyncMode_1983_ = lean_ctor_get(v_toEnvExtension_1971_, 2);
lean_inc(v_asyncMode_1983_);
lean_inc(v_decl_1957_);
v___x_1984_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_a_1955_, v_env_1972_, v_decl_1957_, v_asyncMode_1983_, v_decl_1957_);
lean_dec(v_asyncMode_1983_);
v___x_1985_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2);
if (v_isShared_1982_ == 0)
{
lean_ctor_set(v___x_1981_, 5, v___x_1985_);
lean_ctor_set(v___x_1981_, 0, v___x_1984_);
v___x_1987_ = v___x_1981_;
goto v_reusejp_1986_;
}
else
{
lean_object* v_reuseFailAlloc_1993_; 
v_reuseFailAlloc_1993_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1993_, 0, v___x_1984_);
lean_ctor_set(v_reuseFailAlloc_1993_, 1, v_nextMacroScope_1973_);
lean_ctor_set(v_reuseFailAlloc_1993_, 2, v_ngen_1974_);
lean_ctor_set(v_reuseFailAlloc_1993_, 3, v_auxDeclNGen_1975_);
lean_ctor_set(v_reuseFailAlloc_1993_, 4, v_traceState_1976_);
lean_ctor_set(v_reuseFailAlloc_1993_, 5, v___x_1985_);
lean_ctor_set(v_reuseFailAlloc_1993_, 6, v_messages_1977_);
lean_ctor_set(v_reuseFailAlloc_1993_, 7, v_infoState_1978_);
lean_ctor_set(v_reuseFailAlloc_1993_, 8, v_snapshotTasks_1979_);
v___x_1987_ = v_reuseFailAlloc_1993_;
goto v_reusejp_1986_;
}
v_reusejp_1986_:
{
lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1991_; 
v___x_1988_ = lean_st_ref_set(v___y_1965_, v___x_1987_);
lean_dec(v___y_1965_);
v___x_1989_ = lean_box(0);
if (v_isShared_1969_ == 0)
{
lean_ctor_set(v___x_1968_, 0, v___x_1989_);
v___x_1991_ = v___x_1968_;
goto v_reusejp_1990_;
}
else
{
lean_object* v_reuseFailAlloc_1992_; 
v_reuseFailAlloc_1992_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1992_, 0, v___x_1989_);
v___x_1991_ = v_reuseFailAlloc_1992_;
goto v_reusejp_1990_;
}
v_reusejp_1990_:
{
return v___x_1991_;
}
}
}
}
}
else
{
lean_dec(v___y_1965_);
lean_dec(v_decl_1957_);
lean_dec_ref(v_a_1955_);
return v___x_1966_;
}
}
v___jp_1998_:
{
lean_object* v_toEnvExtension_2002_; lean_object* v_asyncMode_2003_; uint8_t v___x_2004_; 
v_toEnvExtension_2002_ = lean_ctor_get(v_a_1955_, 0);
v_asyncMode_2003_ = lean_ctor_get(v_toEnvExtension_2002_, 2);
lean_inc(v_decl_1957_);
lean_inc_ref(v___y_1999_);
v___x_2004_ = l_Lean_EnvExtension_asyncMayModify___redArg(v___y_1999_, v_decl_1957_, v_asyncMode_2003_);
if (v___x_2004_ == 0)
{
lean_object* v___x_2005_; lean_object* v___x_2006_; 
lean_dec_ref(v_a_1955_);
lean_dec_ref(v_validate_1954_);
v___x_2005_ = l_Lean_Environment_asyncPrefix_x3f(v___y_1999_);
v___x_2006_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___redArg(v_name_1956_, v_decl_1957_, v___x_2005_, v___y_2000_, v___y_2001_);
lean_dec(v___y_2001_);
lean_dec_ref(v___y_2000_);
return v___x_2006_;
}
else
{
lean_dec_ref(v___y_1999_);
lean_dec(v_name_1956_);
v___y_1964_ = v___y_2000_;
v___y_1965_ = v___y_2001_;
goto v___jp_1963_;
}
}
v___jp_2007_:
{
lean_object* v___x_2010_; lean_object* v_env_2011_; lean_object* v___x_2012_; 
v___x_2010_ = lean_st_ref_get(v___y_2009_);
v_env_2011_ = lean_ctor_get(v___x_2010_, 0);
lean_inc_ref(v_env_2011_);
lean_dec(v___x_2010_);
v___x_2012_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2011_, v_decl_1957_);
if (lean_obj_tag(v___x_2012_) == 0)
{
v___y_1999_ = v_env_2011_;
v___y_2000_ = v___y_2008_;
v___y_2001_ = v___y_2009_;
goto v___jp_1998_;
}
else
{
lean_object* v___x_2013_; 
lean_dec_ref(v___x_2012_);
lean_dec_ref(v_env_2011_);
lean_dec_ref(v_a_1955_);
lean_dec_ref(v_validate_1954_);
v___x_2013_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg(v_name_1956_, v_decl_1957_, v___y_2008_, v___y_2009_);
lean_dec(v___y_2009_);
lean_dec_ref(v___y_2008_);
return v___x_2013_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__7___boxed(lean_object* v_validate_2018_, lean_object* v_a_2019_, lean_object* v_name_2020_, lean_object* v_decl_2021_, lean_object* v_stx_2022_, lean_object* v_kind_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_){
_start:
{
uint8_t v_kind_boxed_2027_; lean_object* v_res_2028_; 
v_kind_boxed_2027_ = lean_unbox(v_kind_2023_);
v_res_2028_ = l_Lean_registerTagAttribute___lam__7(v_validate_2018_, v_a_2019_, v_name_2020_, v_decl_2021_, v_stx_2022_, v_kind_boxed_2027_, v___y_2024_, v___y_2025_);
return v_res_2028_;
}
}
static lean_object* _init_l_Lean_registerTagAttribute___closed__5(void){
_start:
{
lean_object* v___x_2034_; lean_object* v___f_2035_; 
v___x_2034_ = l_Lean_NameSet_empty;
v___f_2035_ = lean_alloc_closure((void*)(l_Lean_registerTagAttribute___lam__4___boxed), 2, 1);
lean_closure_set(v___f_2035_, 0, v___x_2034_);
return v___f_2035_;
}
}
static lean_object* _init_l_Lean_registerTagAttribute___closed__6(void){
_start:
{
lean_object* v___x_2036_; lean_object* v___f_2037_; 
v___x_2036_ = l_Lean_NameSet_empty;
v___f_2037_ = lean_alloc_closure((void*)(l_Lean_registerTagAttribute___lam__5___boxed), 4, 1);
lean_closure_set(v___f_2037_, 0, v___x_2036_);
return v___f_2037_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute(lean_object* v_name_2040_, lean_object* v_descr_2041_, lean_object* v_validate_2042_, lean_object* v_ref_2043_, uint8_t v_applicationTime_2044_, lean_object* v_asyncMode_2045_){
_start:
{
lean_object* v___f_2047_; lean_object* v___f_2048_; lean_object* v___f_2049_; lean_object* v___f_2050_; lean_object* v___f_2051_; lean_object* v___f_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; 
v___f_2047_ = ((lean_object*)(l_Lean_registerTagAttribute___closed__0));
v___f_2048_ = ((lean_object*)(l_Lean_registerTagAttribute___closed__2));
v___f_2049_ = ((lean_object*)(l_Lean_registerTagAttribute___closed__3));
v___f_2050_ = ((lean_object*)(l_Lean_registerTagAttribute___closed__4));
v___f_2051_ = lean_obj_once(&l_Lean_registerTagAttribute___closed__5, &l_Lean_registerTagAttribute___closed__5_once, _init_l_Lean_registerTagAttribute___closed__5);
v___f_2052_ = lean_obj_once(&l_Lean_registerTagAttribute___closed__6, &l_Lean_registerTagAttribute___closed__6_once, _init_l_Lean_registerTagAttribute___closed__6);
v___x_2053_ = ((lean_object*)(l_Lean_registerTagAttribute___closed__7));
lean_inc(v_ref_2043_);
v___x_2054_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_2054_, 0, v_ref_2043_);
lean_ctor_set(v___x_2054_, 1, v___f_2051_);
lean_ctor_set(v___x_2054_, 2, v___f_2052_);
lean_ctor_set(v___x_2054_, 3, v___f_2050_);
lean_ctor_set(v___x_2054_, 4, v___f_2049_);
lean_ctor_set(v___x_2054_, 5, v___f_2048_);
lean_ctor_set(v___x_2054_, 6, v_asyncMode_2045_);
lean_ctor_set(v___x_2054_, 7, v___x_2053_);
v___x_2055_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2055_, 0, v___x_2054_);
lean_ctor_set(v___x_2055_, 1, v___f_2047_);
v___x_2056_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_2055_);
if (lean_obj_tag(v___x_2056_) == 0)
{
lean_object* v_a_2057_; lean_object* v___f_2058_; lean_object* v___f_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; 
v_a_2057_ = lean_ctor_get(v___x_2056_, 0);
lean_inc(v_a_2057_);
lean_dec_ref(v___x_2056_);
lean_inc(v_name_2040_);
v___f_2058_ = lean_alloc_closure((void*)(l_Lean_registerTagAttribute___lam__6___boxed), 5, 1);
lean_closure_set(v___f_2058_, 0, v_name_2040_);
lean_inc(v_name_2040_);
lean_inc(v_a_2057_);
v___f_2059_ = lean_alloc_closure((void*)(l_Lean_registerTagAttribute___lam__7___boxed), 9, 3);
lean_closure_set(v___f_2059_, 0, v_validate_2042_);
lean_closure_set(v___f_2059_, 1, v_a_2057_);
lean_closure_set(v___f_2059_, 2, v_name_2040_);
v___x_2060_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2060_, 0, v_ref_2043_);
lean_ctor_set(v___x_2060_, 1, v_name_2040_);
lean_ctor_set(v___x_2060_, 2, v_descr_2041_);
lean_ctor_set_uint8(v___x_2060_, sizeof(void*)*3, v_applicationTime_2044_);
v___x_2061_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2061_, 0, v___x_2060_);
lean_ctor_set(v___x_2061_, 1, v___f_2059_);
lean_ctor_set(v___x_2061_, 2, v___f_2058_);
lean_inc_ref(v___x_2061_);
v___x_2062_ = l_Lean_registerBuiltinAttribute(v___x_2061_);
if (lean_obj_tag(v___x_2062_) == 0)
{
lean_object* v___x_2064_; uint8_t v_isShared_2065_; uint8_t v_isSharedCheck_2070_; 
v_isSharedCheck_2070_ = !lean_is_exclusive(v___x_2062_);
if (v_isSharedCheck_2070_ == 0)
{
lean_object* v_unused_2071_; 
v_unused_2071_ = lean_ctor_get(v___x_2062_, 0);
lean_dec(v_unused_2071_);
v___x_2064_ = v___x_2062_;
v_isShared_2065_ = v_isSharedCheck_2070_;
goto v_resetjp_2063_;
}
else
{
lean_dec(v___x_2062_);
v___x_2064_ = lean_box(0);
v_isShared_2065_ = v_isSharedCheck_2070_;
goto v_resetjp_2063_;
}
v_resetjp_2063_:
{
lean_object* v___x_2066_; lean_object* v___x_2068_; 
v___x_2066_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2066_, 0, v___x_2061_);
lean_ctor_set(v___x_2066_, 1, v_a_2057_);
if (v_isShared_2065_ == 0)
{
lean_ctor_set(v___x_2064_, 0, v___x_2066_);
v___x_2068_ = v___x_2064_;
goto v_reusejp_2067_;
}
else
{
lean_object* v_reuseFailAlloc_2069_; 
v_reuseFailAlloc_2069_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2069_, 0, v___x_2066_);
v___x_2068_ = v_reuseFailAlloc_2069_;
goto v_reusejp_2067_;
}
v_reusejp_2067_:
{
return v___x_2068_;
}
}
}
else
{
lean_object* v_a_2072_; lean_object* v___x_2074_; uint8_t v_isShared_2075_; uint8_t v_isSharedCheck_2079_; 
lean_dec_ref(v___x_2061_);
lean_dec(v_a_2057_);
v_a_2072_ = lean_ctor_get(v___x_2062_, 0);
v_isSharedCheck_2079_ = !lean_is_exclusive(v___x_2062_);
if (v_isSharedCheck_2079_ == 0)
{
v___x_2074_ = v___x_2062_;
v_isShared_2075_ = v_isSharedCheck_2079_;
goto v_resetjp_2073_;
}
else
{
lean_inc(v_a_2072_);
lean_dec(v___x_2062_);
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
else
{
lean_object* v_a_2080_; lean_object* v___x_2082_; uint8_t v_isShared_2083_; uint8_t v_isSharedCheck_2087_; 
lean_dec(v_ref_2043_);
lean_dec_ref(v_validate_2042_);
lean_dec_ref(v_descr_2041_);
lean_dec(v_name_2040_);
v_a_2080_ = lean_ctor_get(v___x_2056_, 0);
v_isSharedCheck_2087_ = !lean_is_exclusive(v___x_2056_);
if (v_isSharedCheck_2087_ == 0)
{
v___x_2082_ = v___x_2056_;
v_isShared_2083_ = v_isSharedCheck_2087_;
goto v_resetjp_2081_;
}
else
{
lean_inc(v_a_2080_);
lean_dec(v___x_2056_);
v___x_2082_ = lean_box(0);
v_isShared_2083_ = v_isSharedCheck_2087_;
goto v_resetjp_2081_;
}
v_resetjp_2081_:
{
lean_object* v___x_2085_; 
if (v_isShared_2083_ == 0)
{
v___x_2085_ = v___x_2082_;
goto v_reusejp_2084_;
}
else
{
lean_object* v_reuseFailAlloc_2086_; 
v_reuseFailAlloc_2086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2086_, 0, v_a_2080_);
v___x_2085_ = v_reuseFailAlloc_2086_;
goto v_reusejp_2084_;
}
v_reusejp_2084_:
{
return v___x_2085_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___boxed(lean_object* v_name_2088_, lean_object* v_descr_2089_, lean_object* v_validate_2090_, lean_object* v_ref_2091_, lean_object* v_applicationTime_2092_, lean_object* v_asyncMode_2093_, lean_object* v_a_2094_){
_start:
{
uint8_t v_applicationTime_boxed_2095_; lean_object* v_res_2096_; 
v_applicationTime_boxed_2095_ = lean_unbox(v_applicationTime_2092_);
v_res_2096_ = l_Lean_registerTagAttribute(v_name_2088_, v_descr_2089_, v_validate_2090_, v_ref_2091_, v_applicationTime_boxed_2095_, v_asyncMode_2093_);
return v_res_2096_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerTagAttribute_spec__1(lean_object* v_init_2097_, lean_object* v_t_2098_){
_start:
{
lean_object* v___x_2099_; 
v___x_2099_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerTagAttribute_spec__1_spec__1(v_init_2097_, v_t_2098_);
return v___x_2099_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__2(lean_object* v_n_2100_, lean_object* v_as_2101_, lean_object* v_lo_2102_, lean_object* v_hi_2103_, lean_object* v_w_2104_, lean_object* v_hlo_2105_, lean_object* v_hhi_2106_){
_start:
{
lean_object* v___x_2107_; 
v___x_2107_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__2___redArg(v_as_2101_, v_lo_2102_, v_hi_2103_);
return v___x_2107_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__2___boxed(lean_object* v_n_2108_, lean_object* v_as_2109_, lean_object* v_lo_2110_, lean_object* v_hi_2111_, lean_object* v_w_2112_, lean_object* v_hlo_2113_, lean_object* v_hhi_2114_){
_start:
{
lean_object* v_res_2115_; 
v_res_2115_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__2(v_n_2108_, v_as_2109_, v_lo_2110_, v_hi_2111_, v_w_2112_, v_hlo_2113_, v_hhi_2114_);
lean_dec(v_hi_2111_);
lean_dec(v_n_2108_);
return v_res_2115_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4(lean_object* v_00_u03b1_2116_, lean_object* v_attrName_2117_, lean_object* v_declName_2118_, lean_object* v_asyncPrefix_x3f_2119_, lean_object* v___y_2120_, lean_object* v___y_2121_){
_start:
{
lean_object* v___x_2123_; 
v___x_2123_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___redArg(v_attrName_2117_, v_declName_2118_, v_asyncPrefix_x3f_2119_, v___y_2120_, v___y_2121_);
return v___x_2123_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___boxed(lean_object* v_00_u03b1_2124_, lean_object* v_attrName_2125_, lean_object* v_declName_2126_, lean_object* v_asyncPrefix_x3f_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_){
_start:
{
lean_object* v_res_2131_; 
v_res_2131_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4(v_00_u03b1_2124_, v_attrName_2125_, v_declName_2126_, v_asyncPrefix_x3f_2127_, v___y_2128_, v___y_2129_);
lean_dec(v___y_2129_);
lean_dec_ref(v___y_2128_);
return v_res_2131_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5(lean_object* v_00_u03b1_2132_, lean_object* v_attrName_2133_, lean_object* v_declName_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_){
_start:
{
lean_object* v___x_2138_; 
v___x_2138_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg(v_attrName_2133_, v_declName_2134_, v___y_2135_, v___y_2136_);
return v___x_2138_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___boxed(lean_object* v_00_u03b1_2139_, lean_object* v_attrName_2140_, lean_object* v_declName_2141_, lean_object* v___y_2142_, lean_object* v___y_2143_, lean_object* v___y_2144_){
_start:
{
lean_object* v_res_2145_; 
v_res_2145_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5(v_00_u03b1_2139_, v_attrName_2140_, v_declName_2141_, v___y_2142_, v___y_2143_);
lean_dec(v___y_2143_);
lean_dec_ref(v___y_2142_);
return v_res_2145_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6(lean_object* v_00_u03b1_2146_, lean_object* v_name_2147_, uint8_t v_kind_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_){
_start:
{
lean_object* v___x_2152_; 
v___x_2152_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg(v_name_2147_, v_kind_2148_, v___y_2149_, v___y_2150_);
return v___x_2152_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___boxed(lean_object* v_00_u03b1_2153_, lean_object* v_name_2154_, lean_object* v_kind_2155_, lean_object* v___y_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_){
_start:
{
uint8_t v_kind_boxed_2159_; lean_object* v_res_2160_; 
v_kind_boxed_2159_ = lean_unbox(v_kind_2155_);
v_res_2160_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6(v_00_u03b1_2153_, v_name_2154_, v_kind_boxed_2159_, v___y_2156_, v___y_2157_);
lean_dec(v___y_2157_);
lean_dec_ref(v___y_2156_);
return v_res_2160_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg___lam__0(lean_object* v_attr_2161_, lean_object* v_decl_2162_, lean_object* v_env_2163_){
_start:
{
lean_object* v_ext_2164_; lean_object* v_toEnvExtension_2165_; lean_object* v_asyncMode_2166_; lean_object* v___x_2167_; 
v_ext_2164_ = lean_ctor_get(v_attr_2161_, 1);
lean_inc_ref(v_ext_2164_);
lean_dec_ref(v_attr_2161_);
v_toEnvExtension_2165_ = lean_ctor_get(v_ext_2164_, 0);
v_asyncMode_2166_ = lean_ctor_get(v_toEnvExtension_2165_, 2);
lean_inc(v_asyncMode_2166_);
lean_inc(v_decl_2162_);
v___x_2167_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_ext_2164_, v_env_2163_, v_decl_2162_, v_asyncMode_2166_, v_decl_2162_);
lean_dec(v_asyncMode_2166_);
return v___x_2167_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg___lam__1(lean_object* v_modifyEnv_2168_, lean_object* v___f_2169_, lean_object* v_____r_2170_){
_start:
{
lean_object* v___x_2171_; 
v___x_2171_ = lean_apply_1(v_modifyEnv_2168_, v___f_2169_);
return v___x_2171_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg___lam__2(lean_object* v_attr_2172_, lean_object* v_env_2173_, lean_object* v_decl_2174_, lean_object* v_inst_2175_, lean_object* v_inst_2176_, lean_object* v_toBind_2177_, lean_object* v___f_2178_, lean_object* v_modifyEnv_2179_, lean_object* v___f_2180_, lean_object* v_____r_2181_){
_start:
{
lean_object* v_ext_2182_; lean_object* v_toEnvExtension_2183_; lean_object* v_attr_2184_; lean_object* v_asyncMode_2185_; uint8_t v___x_2186_; 
v_ext_2182_ = lean_ctor_get(v_attr_2172_, 1);
v_toEnvExtension_2183_ = lean_ctor_get(v_ext_2182_, 0);
lean_inc_ref(v_toEnvExtension_2183_);
v_attr_2184_ = lean_ctor_get(v_attr_2172_, 0);
lean_inc_ref(v_attr_2184_);
lean_dec_ref(v_attr_2172_);
v_asyncMode_2185_ = lean_ctor_get(v_toEnvExtension_2183_, 2);
lean_inc(v_asyncMode_2185_);
lean_dec_ref(v_toEnvExtension_2183_);
lean_inc(v_decl_2174_);
lean_inc_ref(v_env_2173_);
v___x_2186_ = l_Lean_EnvExtension_asyncMayModify___redArg(v_env_2173_, v_decl_2174_, v_asyncMode_2185_);
lean_dec(v_asyncMode_2185_);
if (v___x_2186_ == 0)
{
lean_object* v_toAttributeImplCore_2187_; lean_object* v_name_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; 
lean_dec_ref(v___f_2180_);
lean_dec(v_modifyEnv_2179_);
v_toAttributeImplCore_2187_ = lean_ctor_get(v_attr_2184_, 0);
lean_inc_ref(v_toAttributeImplCore_2187_);
lean_dec_ref(v_attr_2184_);
v_name_2188_ = lean_ctor_get(v_toAttributeImplCore_2187_, 1);
lean_inc(v_name_2188_);
lean_dec_ref(v_toAttributeImplCore_2187_);
v___x_2189_ = l_Lean_Environment_asyncPrefix_x3f(v_env_2173_);
v___x_2190_ = l_Lean_throwAttrNotInAsyncCtx___redArg(v_inst_2175_, v_inst_2176_, v_name_2188_, v_decl_2174_, v___x_2189_);
v___x_2191_ = lean_apply_4(v_toBind_2177_, lean_box(0), lean_box(0), v___x_2190_, v___f_2178_);
return v___x_2191_;
}
else
{
lean_object* v___x_2192_; 
lean_dec_ref(v_attr_2184_);
lean_dec(v___f_2178_);
lean_dec(v_toBind_2177_);
lean_dec_ref(v_inst_2176_);
lean_dec_ref(v_inst_2175_);
lean_dec(v_decl_2174_);
lean_dec_ref(v_env_2173_);
v___x_2192_ = lean_apply_1(v_modifyEnv_2179_, v___f_2180_);
return v___x_2192_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg___lam__3(lean_object* v___f_2193_, lean_object* v_____r_2194_){
_start:
{
lean_object* v___x_2195_; 
v___x_2195_ = lean_apply_1(v___f_2193_, v_____r_2194_);
return v___x_2195_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg___lam__4(lean_object* v_attr_2196_, lean_object* v_decl_2197_, lean_object* v_inst_2198_, lean_object* v_inst_2199_, lean_object* v_toBind_2200_, lean_object* v___f_2201_, lean_object* v_modifyEnv_2202_, lean_object* v___f_2203_, lean_object* v_env_2204_){
_start:
{
lean_object* v___f_2205_; lean_object* v___x_2206_; 
lean_inc_ref(v___f_2203_);
lean_inc(v_modifyEnv_2202_);
lean_inc(v___f_2201_);
lean_inc(v_toBind_2200_);
lean_inc_ref(v_inst_2199_);
lean_inc_ref(v_inst_2198_);
lean_inc(v_decl_2197_);
lean_inc_ref(v_env_2204_);
lean_inc_ref(v_attr_2196_);
v___f_2205_ = lean_alloc_closure((void*)(l_Lean_TagAttribute_setTag___redArg___lam__2), 10, 9);
lean_closure_set(v___f_2205_, 0, v_attr_2196_);
lean_closure_set(v___f_2205_, 1, v_env_2204_);
lean_closure_set(v___f_2205_, 2, v_decl_2197_);
lean_closure_set(v___f_2205_, 3, v_inst_2198_);
lean_closure_set(v___f_2205_, 4, v_inst_2199_);
lean_closure_set(v___f_2205_, 5, v_toBind_2200_);
lean_closure_set(v___f_2205_, 6, v___f_2201_);
lean_closure_set(v___f_2205_, 7, v_modifyEnv_2202_);
lean_closure_set(v___f_2205_, 8, v___f_2203_);
v___x_2206_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2204_, v_decl_2197_);
if (lean_obj_tag(v___x_2206_) == 0)
{
lean_object* v___x_2207_; lean_object* v___x_2208_; 
lean_dec_ref(v___f_2205_);
v___x_2207_ = lean_box(0);
v___x_2208_ = l_Lean_TagAttribute_setTag___redArg___lam__2(v_attr_2196_, v_env_2204_, v_decl_2197_, v_inst_2198_, v_inst_2199_, v_toBind_2200_, v___f_2201_, v_modifyEnv_2202_, v___f_2203_, v___x_2207_);
return v___x_2208_;
}
else
{
lean_object* v_attr_2209_; lean_object* v_toAttributeImplCore_2210_; lean_object* v_name_2211_; lean_object* v___f_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; 
lean_dec_ref(v___x_2206_);
lean_dec_ref(v_env_2204_);
lean_dec_ref(v___f_2203_);
lean_dec(v_modifyEnv_2202_);
lean_dec(v___f_2201_);
v_attr_2209_ = lean_ctor_get(v_attr_2196_, 0);
lean_inc_ref(v_attr_2209_);
lean_dec_ref(v_attr_2196_);
v_toAttributeImplCore_2210_ = lean_ctor_get(v_attr_2209_, 0);
lean_inc_ref(v_toAttributeImplCore_2210_);
lean_dec_ref(v_attr_2209_);
v_name_2211_ = lean_ctor_get(v_toAttributeImplCore_2210_, 1);
lean_inc(v_name_2211_);
lean_dec_ref(v_toAttributeImplCore_2210_);
v___f_2212_ = lean_alloc_closure((void*)(l_Lean_TagAttribute_setTag___redArg___lam__3), 2, 1);
lean_closure_set(v___f_2212_, 0, v___f_2205_);
v___x_2213_ = l_Lean_throwAttrDeclInImportedModule___redArg(v_inst_2198_, v_inst_2199_, v_name_2211_, v_decl_2197_);
v___x_2214_ = lean_apply_4(v_toBind_2200_, lean_box(0), lean_box(0), v___x_2213_, v___f_2212_);
return v___x_2214_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg(lean_object* v_inst_2215_, lean_object* v_inst_2216_, lean_object* v_inst_2217_, lean_object* v_attr_2218_, lean_object* v_decl_2219_){
_start:
{
lean_object* v_toBind_2220_; lean_object* v_getEnv_2221_; lean_object* v_modifyEnv_2222_; lean_object* v___f_2223_; lean_object* v___f_2224_; lean_object* v___f_2225_; lean_object* v___x_2226_; 
v_toBind_2220_ = lean_ctor_get(v_inst_2215_, 1);
lean_inc(v_toBind_2220_);
v_getEnv_2221_ = lean_ctor_get(v_inst_2217_, 0);
lean_inc(v_getEnv_2221_);
v_modifyEnv_2222_ = lean_ctor_get(v_inst_2217_, 1);
lean_inc(v_modifyEnv_2222_);
lean_dec_ref(v_inst_2217_);
lean_inc(v_decl_2219_);
lean_inc_ref(v_attr_2218_);
v___f_2223_ = lean_alloc_closure((void*)(l_Lean_TagAttribute_setTag___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2223_, 0, v_attr_2218_);
lean_closure_set(v___f_2223_, 1, v_decl_2219_);
lean_inc_ref(v___f_2223_);
lean_inc(v_modifyEnv_2222_);
v___f_2224_ = lean_alloc_closure((void*)(l_Lean_TagAttribute_setTag___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2224_, 0, v_modifyEnv_2222_);
lean_closure_set(v___f_2224_, 1, v___f_2223_);
lean_inc(v_toBind_2220_);
v___f_2225_ = lean_alloc_closure((void*)(l_Lean_TagAttribute_setTag___redArg___lam__4), 9, 8);
lean_closure_set(v___f_2225_, 0, v_attr_2218_);
lean_closure_set(v___f_2225_, 1, v_decl_2219_);
lean_closure_set(v___f_2225_, 2, v_inst_2215_);
lean_closure_set(v___f_2225_, 3, v_inst_2216_);
lean_closure_set(v___f_2225_, 4, v_toBind_2220_);
lean_closure_set(v___f_2225_, 5, v___f_2224_);
lean_closure_set(v___f_2225_, 6, v_modifyEnv_2222_);
lean_closure_set(v___f_2225_, 7, v___f_2223_);
v___x_2226_ = lean_apply_4(v_toBind_2220_, lean_box(0), lean_box(0), v_getEnv_2221_, v___f_2225_);
return v___x_2226_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag(lean_object* v_m_2227_, lean_object* v_inst_2228_, lean_object* v_inst_2229_, lean_object* v_inst_2230_, lean_object* v_attr_2231_, lean_object* v_decl_2232_){
_start:
{
lean_object* v___x_2233_; 
v___x_2233_ = l_Lean_TagAttribute_setTag___redArg(v_inst_2228_, v_inst_2229_, v_inst_2230_, v_attr_2231_, v_decl_2232_);
return v___x_2233_;
}
}
LEAN_EXPORT uint8_t l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___redArg(lean_object* v_as_2234_, lean_object* v_k_2235_, lean_object* v_x_2236_, lean_object* v_x_2237_){
_start:
{
lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v_m_2240_; lean_object* v_a_2241_; uint8_t v___x_2242_; 
v___x_2238_ = lean_nat_add(v_x_2236_, v_x_2237_);
v___x_2239_ = lean_unsigned_to_nat(1u);
v_m_2240_ = lean_nat_shiftr(v___x_2238_, v___x_2239_);
lean_dec(v___x_2238_);
v_a_2241_ = lean_array_fget_borrowed(v_as_2234_, v_m_2240_);
v___x_2242_ = l_Lean_Name_quickLt(v_a_2241_, v_k_2235_);
if (v___x_2242_ == 0)
{
uint8_t v___x_2243_; 
lean_dec(v_x_2237_);
v___x_2243_ = l_Lean_Name_quickLt(v_k_2235_, v_a_2241_);
if (v___x_2243_ == 0)
{
uint8_t v___x_2244_; 
lean_dec(v_m_2240_);
lean_dec(v_x_2236_);
v___x_2244_ = 1;
return v___x_2244_;
}
else
{
lean_object* v___x_2245_; uint8_t v___x_2246_; 
v___x_2245_ = lean_unsigned_to_nat(0u);
v___x_2246_ = lean_nat_dec_eq(v_m_2240_, v___x_2245_);
if (v___x_2246_ == 0)
{
lean_object* v___x_2247_; uint8_t v___x_2248_; 
v___x_2247_ = lean_nat_sub(v_m_2240_, v___x_2239_);
lean_dec(v_m_2240_);
v___x_2248_ = lean_nat_dec_lt(v___x_2247_, v_x_2236_);
if (v___x_2248_ == 0)
{
v_x_2237_ = v___x_2247_;
goto _start;
}
else
{
lean_dec(v___x_2247_);
lean_dec(v_x_2236_);
return v___x_2242_;
}
}
else
{
lean_dec(v_m_2240_);
lean_dec(v_x_2236_);
return v___x_2242_;
}
}
}
else
{
lean_object* v___x_2250_; uint8_t v___x_2251_; 
lean_dec(v_x_2236_);
v___x_2250_ = lean_nat_add(v_m_2240_, v___x_2239_);
lean_dec(v_m_2240_);
v___x_2251_ = lean_nat_dec_le(v___x_2250_, v_x_2237_);
if (v___x_2251_ == 0)
{
lean_dec(v___x_2250_);
lean_dec(v_x_2237_);
return v___x_2251_;
}
else
{
v_x_2236_ = v___x_2250_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___redArg___boxed(lean_object* v_as_2253_, lean_object* v_k_2254_, lean_object* v_x_2255_, lean_object* v_x_2256_){
_start:
{
uint8_t v_res_2257_; lean_object* v_r_2258_; 
v_res_2257_ = l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___redArg(v_as_2253_, v_k_2254_, v_x_2255_, v_x_2256_);
lean_dec(v_k_2254_);
lean_dec_ref(v_as_2253_);
v_r_2258_ = lean_box(v_res_2257_);
return v_r_2258_;
}
}
LEAN_EXPORT uint8_t l_Lean_TagAttribute_hasTag(lean_object* v_attr_2259_, lean_object* v_env_2260_, lean_object* v_decl_2261_){
_start:
{
lean_object* v___x_2262_; lean_object* v___x_2263_; 
v___x_2262_ = lean_box(1);
v___x_2263_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2260_, v_decl_2261_);
if (lean_obj_tag(v___x_2263_) == 0)
{
lean_object* v_ext_2264_; lean_object* v_toEnvExtension_2265_; lean_object* v_asyncMode_2266_; lean_object* v___x_2267_; uint8_t v___x_2268_; 
v_ext_2264_ = lean_ctor_get(v_attr_2259_, 1);
v_toEnvExtension_2265_ = lean_ctor_get(v_ext_2264_, 0);
v_asyncMode_2266_ = lean_ctor_get(v_toEnvExtension_2265_, 2);
lean_inc(v_decl_2261_);
v___x_2267_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2262_, v_ext_2264_, v_env_2260_, v_asyncMode_2266_, v_decl_2261_);
v___x_2268_ = l_Lean_NameSet_contains(v___x_2267_, v_decl_2261_);
lean_dec(v_decl_2261_);
lean_dec(v___x_2267_);
return v___x_2268_;
}
else
{
lean_object* v_val_2269_; lean_object* v_ext_2270_; uint8_t v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; uint8_t v___x_2275_; 
v_val_2269_ = lean_ctor_get(v___x_2263_, 0);
lean_inc(v_val_2269_);
lean_dec_ref(v___x_2263_);
v_ext_2270_ = lean_ctor_get(v_attr_2259_, 1);
v___x_2271_ = 0;
v___x_2272_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_2262_, v_ext_2270_, v_env_2260_, v_val_2269_, v___x_2271_);
lean_dec(v_val_2269_);
lean_dec_ref(v_env_2260_);
v___x_2273_ = lean_unsigned_to_nat(0u);
v___x_2274_ = lean_array_get_size(v___x_2272_);
v___x_2275_ = lean_nat_dec_lt(v___x_2273_, v___x_2274_);
if (v___x_2275_ == 0)
{
lean_dec_ref(v___x_2272_);
lean_dec(v_decl_2261_);
return v___x_2275_;
}
else
{
lean_object* v___x_2276_; lean_object* v___x_2277_; uint8_t v___x_2278_; 
v___x_2276_ = lean_unsigned_to_nat(1u);
v___x_2277_ = lean_nat_sub(v___x_2274_, v___x_2276_);
v___x_2278_ = lean_nat_dec_le(v___x_2273_, v___x_2277_);
if (v___x_2278_ == 0)
{
lean_dec(v___x_2277_);
lean_dec_ref(v___x_2272_);
lean_dec(v_decl_2261_);
return v___x_2278_;
}
else
{
uint8_t v___x_2279_; 
v___x_2279_ = l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___redArg(v___x_2272_, v_decl_2261_, v___x_2273_, v___x_2277_);
lean_dec(v_decl_2261_);
lean_dec_ref(v___x_2272_);
return v___x_2279_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_hasTag___boxed(lean_object* v_attr_2280_, lean_object* v_env_2281_, lean_object* v_decl_2282_){
_start:
{
uint8_t v_res_2283_; lean_object* v_r_2284_; 
v_res_2283_ = l_Lean_TagAttribute_hasTag(v_attr_2280_, v_env_2281_, v_decl_2282_);
lean_dec_ref(v_attr_2280_);
v_r_2284_ = lean_box(v_res_2283_);
return v_r_2284_;
}
}
LEAN_EXPORT uint8_t l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0(lean_object* v_as_2285_, lean_object* v_k_2286_, lean_object* v_x_2287_, lean_object* v_x_2288_, lean_object* v_x_2289_){
_start:
{
uint8_t v___x_2290_; 
v___x_2290_ = l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___redArg(v_as_2285_, v_k_2286_, v_x_2287_, v_x_2288_);
return v___x_2290_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___boxed(lean_object* v_as_2291_, lean_object* v_k_2292_, lean_object* v_x_2293_, lean_object* v_x_2294_, lean_object* v_x_2295_){
_start:
{
uint8_t v_res_2296_; lean_object* v_r_2297_; 
v_res_2296_ = l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0(v_as_2291_, v_k_2292_, v_x_2293_, v_x_2294_, v_x_2295_);
lean_dec(v_k_2292_);
lean_dec_ref(v_as_2291_);
v_r_2297_ = lean_box(v_res_2296_);
return v_r_2297_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__0(lean_object* v_x_2298_, lean_object* v___y_2299_){
_start:
{
lean_object* v___x_2301_; lean_object* v___x_2302_; 
v___x_2301_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___lam__0___closed__1));
v___x_2302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2302_, 0, v___x_2301_);
return v___x_2302_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__0___boxed(lean_object* v_x_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_){
_start:
{
lean_object* v_res_2306_; 
v_res_2306_ = l_Lean_instInhabitedParametricAttribute_default___lam__0(v_x_2303_, v___y_2304_);
lean_dec_ref(v___y_2304_);
lean_dec_ref(v_x_2303_);
return v_res_2306_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__1(lean_object* v_s_2307_, lean_object* v_x_2308_){
_start:
{
lean_inc_ref(v_s_2307_);
return v_s_2307_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__1___boxed(lean_object* v_s_2309_, lean_object* v_x_2310_){
_start:
{
lean_object* v_res_2311_; 
v_res_2311_ = l_Lean_instInhabitedParametricAttribute_default___lam__1(v_s_2309_, v_x_2310_);
lean_dec_ref(v_x_2310_);
lean_dec_ref(v_s_2309_);
return v_res_2311_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__2(lean_object* v_x_2314_, lean_object* v_x_2315_, uint8_t v_x_2316_){
_start:
{
lean_object* v___x_2317_; 
v___x_2317_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___lam__2___closed__0));
return v___x_2317_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__2___boxed(lean_object* v_x_2318_, lean_object* v_x_2319_, lean_object* v_x_2320_){
_start:
{
uint8_t v_x_80__boxed_2321_; lean_object* v_res_2322_; 
v_x_80__boxed_2321_ = lean_unbox(v_x_2320_);
v_res_2322_ = l_Lean_instInhabitedParametricAttribute_default___lam__2(v_x_2318_, v_x_2319_, v_x_80__boxed_2321_);
lean_dec_ref(v_x_2319_);
lean_dec_ref(v_x_2318_);
return v_res_2322_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__3(lean_object* v_x_2323_){
_start:
{
lean_object* v___x_2324_; 
v___x_2324_ = lean_box(0);
return v___x_2324_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__3___boxed(lean_object* v_x_2325_){
_start:
{
lean_object* v_res_2326_; 
v_res_2326_ = l_Lean_instInhabitedParametricAttribute_default___lam__3(v_x_2325_);
lean_dec_ref(v_x_2325_);
return v_res_2326_;
}
}
static lean_object* _init_l_Lean_instInhabitedParametricAttribute_default___closed__4(void){
_start:
{
lean_object* v___x_2331_; 
v___x_2331_ = l_Lean_instInhabitedEnvExtension_default(lean_box(0));
return v___x_2331_;
}
}
static lean_object* _init_l_Lean_instInhabitedParametricAttribute_default___closed__5(void){
_start:
{
lean_object* v___f_2332_; lean_object* v___f_2333_; lean_object* v___f_2334_; lean_object* v___f_2335_; lean_object* v___x_2336_; lean_object* v___x_2337_; lean_object* v___x_2338_; 
v___f_2332_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___closed__3));
v___f_2333_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___closed__2));
v___f_2334_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___closed__1));
v___f_2335_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___closed__0));
v___x_2336_ = lean_box(0);
v___x_2337_ = lean_obj_once(&l_Lean_instInhabitedParametricAttribute_default___closed__4, &l_Lean_instInhabitedParametricAttribute_default___closed__4_once, _init_l_Lean_instInhabitedParametricAttribute_default___closed__4);
v___x_2338_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2338_, 0, v___x_2337_);
lean_ctor_set(v___x_2338_, 1, v___x_2336_);
lean_ctor_set(v___x_2338_, 2, v___f_2335_);
lean_ctor_set(v___x_2338_, 3, v___f_2334_);
lean_ctor_set(v___x_2338_, 4, v___f_2333_);
lean_ctor_set(v___x_2338_, 5, v___f_2332_);
return v___x_2338_;
}
}
static lean_object* _init_l_Lean_instInhabitedParametricAttribute_default___closed__6(void){
_start:
{
uint8_t v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; 
v___x_2339_ = 0;
v___x_2340_ = lean_obj_once(&l_Lean_instInhabitedParametricAttribute_default___closed__5, &l_Lean_instInhabitedParametricAttribute_default___closed__5_once, _init_l_Lean_instInhabitedParametricAttribute_default___closed__5);
v___x_2341_ = ((lean_object*)(l_Lean_instInhabitedAttributeImpl_default));
v___x_2342_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2342_, 0, v___x_2341_);
lean_ctor_set(v___x_2342_, 1, v___x_2340_);
lean_ctor_set_uint8(v___x_2342_, sizeof(void*)*2, v___x_2339_);
return v___x_2342_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default(lean_object* v_a_2343_){
_start:
{
lean_object* v___x_2344_; 
v___x_2344_ = lean_obj_once(&l_Lean_instInhabitedParametricAttribute_default___closed__6, &l_Lean_instInhabitedParametricAttribute_default___closed__6_once, _init_l_Lean_instInhabitedParametricAttribute_default___closed__6);
return v___x_2344_;
}
}
static lean_object* _init_l_Lean_instInhabitedParametricAttribute___closed__0(void){
_start:
{
lean_object* v___x_2345_; 
v___x_2345_ = l_Lean_instInhabitedParametricAttribute_default(lean_box(0));
return v___x_2345_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute(lean_object* v_a_2346_){
_start:
{
lean_object* v___x_2347_; 
v___x_2347_ = lean_obj_once(&l_Lean_instInhabitedParametricAttribute___closed__0, &l_Lean_instInhabitedParametricAttribute___closed__0_once, _init_l_Lean_instInhabitedParametricAttribute___closed__0);
return v___x_2347_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_registerParametricAttribute_spec__4___redArg(lean_object* v_env_2348_, lean_object* v___y_2349_){
_start:
{
lean_object* v___x_2351_; lean_object* v_nextMacroScope_2352_; lean_object* v_ngen_2353_; lean_object* v_auxDeclNGen_2354_; lean_object* v_traceState_2355_; lean_object* v_messages_2356_; lean_object* v_infoState_2357_; lean_object* v_snapshotTasks_2358_; lean_object* v___x_2360_; uint8_t v_isShared_2361_; uint8_t v_isSharedCheck_2369_; 
v___x_2351_ = lean_st_ref_take(v___y_2349_);
v_nextMacroScope_2352_ = lean_ctor_get(v___x_2351_, 1);
v_ngen_2353_ = lean_ctor_get(v___x_2351_, 2);
v_auxDeclNGen_2354_ = lean_ctor_get(v___x_2351_, 3);
v_traceState_2355_ = lean_ctor_get(v___x_2351_, 4);
v_messages_2356_ = lean_ctor_get(v___x_2351_, 6);
v_infoState_2357_ = lean_ctor_get(v___x_2351_, 7);
v_snapshotTasks_2358_ = lean_ctor_get(v___x_2351_, 8);
v_isSharedCheck_2369_ = !lean_is_exclusive(v___x_2351_);
if (v_isSharedCheck_2369_ == 0)
{
lean_object* v_unused_2370_; lean_object* v_unused_2371_; 
v_unused_2370_ = lean_ctor_get(v___x_2351_, 5);
lean_dec(v_unused_2370_);
v_unused_2371_ = lean_ctor_get(v___x_2351_, 0);
lean_dec(v_unused_2371_);
v___x_2360_ = v___x_2351_;
v_isShared_2361_ = v_isSharedCheck_2369_;
goto v_resetjp_2359_;
}
else
{
lean_inc(v_snapshotTasks_2358_);
lean_inc(v_infoState_2357_);
lean_inc(v_messages_2356_);
lean_inc(v_traceState_2355_);
lean_inc(v_auxDeclNGen_2354_);
lean_inc(v_ngen_2353_);
lean_inc(v_nextMacroScope_2352_);
lean_dec(v___x_2351_);
v___x_2360_ = lean_box(0);
v_isShared_2361_ = v_isSharedCheck_2369_;
goto v_resetjp_2359_;
}
v_resetjp_2359_:
{
lean_object* v___x_2362_; lean_object* v___x_2364_; 
v___x_2362_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2);
if (v_isShared_2361_ == 0)
{
lean_ctor_set(v___x_2360_, 5, v___x_2362_);
lean_ctor_set(v___x_2360_, 0, v_env_2348_);
v___x_2364_ = v___x_2360_;
goto v_reusejp_2363_;
}
else
{
lean_object* v_reuseFailAlloc_2368_; 
v_reuseFailAlloc_2368_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2368_, 0, v_env_2348_);
lean_ctor_set(v_reuseFailAlloc_2368_, 1, v_nextMacroScope_2352_);
lean_ctor_set(v_reuseFailAlloc_2368_, 2, v_ngen_2353_);
lean_ctor_set(v_reuseFailAlloc_2368_, 3, v_auxDeclNGen_2354_);
lean_ctor_set(v_reuseFailAlloc_2368_, 4, v_traceState_2355_);
lean_ctor_set(v_reuseFailAlloc_2368_, 5, v___x_2362_);
lean_ctor_set(v_reuseFailAlloc_2368_, 6, v_messages_2356_);
lean_ctor_set(v_reuseFailAlloc_2368_, 7, v_infoState_2357_);
lean_ctor_set(v_reuseFailAlloc_2368_, 8, v_snapshotTasks_2358_);
v___x_2364_ = v_reuseFailAlloc_2368_;
goto v_reusejp_2363_;
}
v_reusejp_2363_:
{
lean_object* v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; 
v___x_2365_ = lean_st_ref_set(v___y_2349_, v___x_2364_);
v___x_2366_ = lean_box(0);
v___x_2367_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2367_, 0, v___x_2366_);
return v___x_2367_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_registerParametricAttribute_spec__4___redArg___boxed(lean_object* v_env_2372_, lean_object* v___y_2373_, lean_object* v___y_2374_){
_start:
{
lean_object* v_res_2375_; 
v_res_2375_ = l_Lean_setEnv___at___00Lean_registerParametricAttribute_spec__4___redArg(v_env_2372_, v___y_2373_);
lean_dec(v___y_2373_);
return v_res_2375_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_registerParametricAttribute_spec__4(lean_object* v_env_2376_, lean_object* v___y_2377_, lean_object* v___y_2378_){
_start:
{
lean_object* v___x_2380_; 
v___x_2380_ = l_Lean_setEnv___at___00Lean_registerParametricAttribute_spec__4___redArg(v_env_2376_, v___y_2378_);
return v___x_2380_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_registerParametricAttribute_spec__4___boxed(lean_object* v_env_2381_, lean_object* v___y_2382_, lean_object* v___y_2383_, lean_object* v___y_2384_){
_start:
{
lean_object* v_res_2385_; 
v_res_2385_ = l_Lean_setEnv___at___00Lean_registerParametricAttribute_spec__4(v_env_2381_, v___y_2382_, v___y_2383_);
lean_dec(v___y_2383_);
lean_dec_ref(v___y_2382_);
return v_res_2385_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___lam__0(lean_object* v_x_2386_, lean_object* v_p_2387_){
_start:
{
lean_object* v_fst_2388_; lean_object* v_snd_2389_; lean_object* v___x_2391_; uint8_t v_isShared_2392_; uint8_t v_isSharedCheck_2406_; 
v_fst_2388_ = lean_ctor_get(v_x_2386_, 0);
v_snd_2389_ = lean_ctor_get(v_x_2386_, 1);
v_isSharedCheck_2406_ = !lean_is_exclusive(v_x_2386_);
if (v_isSharedCheck_2406_ == 0)
{
v___x_2391_ = v_x_2386_;
v_isShared_2392_ = v_isSharedCheck_2406_;
goto v_resetjp_2390_;
}
else
{
lean_inc(v_snd_2389_);
lean_inc(v_fst_2388_);
lean_dec(v_x_2386_);
v___x_2391_ = lean_box(0);
v_isShared_2392_ = v_isSharedCheck_2406_;
goto v_resetjp_2390_;
}
v_resetjp_2390_:
{
lean_object* v_fst_2393_; lean_object* v_snd_2394_; lean_object* v___x_2396_; uint8_t v_isShared_2397_; uint8_t v_isSharedCheck_2405_; 
v_fst_2393_ = lean_ctor_get(v_p_2387_, 0);
v_snd_2394_ = lean_ctor_get(v_p_2387_, 1);
v_isSharedCheck_2405_ = !lean_is_exclusive(v_p_2387_);
if (v_isSharedCheck_2405_ == 0)
{
v___x_2396_ = v_p_2387_;
v_isShared_2397_ = v_isSharedCheck_2405_;
goto v_resetjp_2395_;
}
else
{
lean_inc(v_snd_2394_);
lean_inc(v_fst_2393_);
lean_dec(v_p_2387_);
v___x_2396_ = lean_box(0);
v_isShared_2397_ = v_isSharedCheck_2405_;
goto v_resetjp_2395_;
}
v_resetjp_2395_:
{
lean_object* v___x_2399_; 
lean_inc(v_fst_2393_);
if (v_isShared_2392_ == 0)
{
lean_ctor_set_tag(v___x_2391_, 1);
lean_ctor_set(v___x_2391_, 1, v_fst_2388_);
lean_ctor_set(v___x_2391_, 0, v_fst_2393_);
v___x_2399_ = v___x_2391_;
goto v_reusejp_2398_;
}
else
{
lean_object* v_reuseFailAlloc_2404_; 
v_reuseFailAlloc_2404_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2404_, 0, v_fst_2393_);
lean_ctor_set(v_reuseFailAlloc_2404_, 1, v_fst_2388_);
v___x_2399_ = v_reuseFailAlloc_2404_;
goto v_reusejp_2398_;
}
v_reusejp_2398_:
{
lean_object* v___x_2400_; lean_object* v___x_2402_; 
v___x_2400_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_2393_, v_snd_2394_, v_snd_2389_);
if (v_isShared_2397_ == 0)
{
lean_ctor_set(v___x_2396_, 1, v___x_2400_);
lean_ctor_set(v___x_2396_, 0, v___x_2399_);
v___x_2402_ = v___x_2396_;
goto v_reusejp_2401_;
}
else
{
lean_object* v_reuseFailAlloc_2403_; 
v_reuseFailAlloc_2403_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2403_, 0, v___x_2399_);
lean_ctor_set(v_reuseFailAlloc_2403_, 1, v___x_2400_);
v___x_2402_ = v_reuseFailAlloc_2403_;
goto v_reusejp_2401_;
}
v_reusejp_2401_:
{
return v___x_2402_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1_spec__1___redArg(lean_object* v_init_2407_, lean_object* v_x_2408_){
_start:
{
if (lean_obj_tag(v_x_2408_) == 0)
{
lean_object* v_k_2409_; lean_object* v_v_2410_; lean_object* v_l_2411_; lean_object* v_r_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; 
v_k_2409_ = lean_ctor_get(v_x_2408_, 1);
v_v_2410_ = lean_ctor_get(v_x_2408_, 2);
v_l_2411_ = lean_ctor_get(v_x_2408_, 3);
v_r_2412_ = lean_ctor_get(v_x_2408_, 4);
v___x_2413_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1_spec__1___redArg(v_init_2407_, v_l_2411_);
lean_inc(v_v_2410_);
lean_inc(v_k_2409_);
v___x_2414_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2414_, 0, v_k_2409_);
lean_ctor_set(v___x_2414_, 1, v_v_2410_);
v___x_2415_ = lean_array_push(v___x_2413_, v___x_2414_);
v_init_2407_ = v___x_2415_;
v_x_2408_ = v_r_2412_;
goto _start;
}
else
{
return v_init_2407_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1_spec__1___redArg___boxed(lean_object* v_init_2417_, lean_object* v_x_2418_){
_start:
{
lean_object* v_res_2419_; 
v_res_2419_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1_spec__1___redArg(v_init_2417_, v_x_2418_);
lean_dec(v_x_2418_);
return v_res_2419_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2___redArg___lam__0(lean_object* v_a_2420_, lean_object* v_b_2421_){
_start:
{
lean_object* v_fst_2422_; lean_object* v_fst_2423_; uint8_t v___x_2424_; 
v_fst_2422_ = lean_ctor_get(v_a_2420_, 0);
v_fst_2423_ = lean_ctor_get(v_b_2421_, 0);
v___x_2424_ = l_Lean_Name_quickLt(v_fst_2422_, v_fst_2423_);
return v___x_2424_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2___redArg___lam__0___boxed(lean_object* v_a_2425_, lean_object* v_b_2426_){
_start:
{
uint8_t v_res_2427_; lean_object* v_r_2428_; 
v_res_2427_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2___redArg___lam__0(v_a_2425_, v_b_2426_);
lean_dec_ref(v_b_2426_);
lean_dec_ref(v_a_2425_);
v_r_2428_ = lean_box(v_res_2427_);
return v_r_2428_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2___redArg(lean_object* v_as_2430_, lean_object* v_lo_2431_, lean_object* v_hi_2432_){
_start:
{
uint8_t v___x_2433_; 
v___x_2433_ = lean_nat_dec_lt(v_lo_2431_, v_hi_2432_);
if (v___x_2433_ == 0)
{
lean_dec(v_lo_2431_);
return v_as_2430_;
}
else
{
lean_object* v___f_2434_; lean_object* v___x_2435_; lean_object* v_fst_2436_; lean_object* v_snd_2437_; uint8_t v___x_2438_; 
v___f_2434_ = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2___redArg___closed__0));
lean_inc(v_lo_2431_);
v___x_2435_ = l_Array_qpartition___redArg(v_as_2430_, v___f_2434_, v_lo_2431_, v_hi_2432_);
v_fst_2436_ = lean_ctor_get(v___x_2435_, 0);
lean_inc(v_fst_2436_);
v_snd_2437_ = lean_ctor_get(v___x_2435_, 1);
lean_inc(v_snd_2437_);
lean_dec_ref(v___x_2435_);
v___x_2438_ = lean_nat_dec_le(v_hi_2432_, v_fst_2436_);
if (v___x_2438_ == 0)
{
lean_object* v___x_2439_; lean_object* v___x_2440_; lean_object* v___x_2441_; 
v___x_2439_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2___redArg(v_snd_2437_, v_lo_2431_, v_fst_2436_);
v___x_2440_ = lean_unsigned_to_nat(1u);
v___x_2441_ = lean_nat_add(v_fst_2436_, v___x_2440_);
lean_dec(v_fst_2436_);
v_as_2430_ = v___x_2439_;
v_lo_2431_ = v___x_2441_;
goto _start;
}
else
{
lean_dec(v_fst_2436_);
lean_dec(v_lo_2431_);
return v_snd_2437_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2___redArg___boxed(lean_object* v_as_2443_, lean_object* v_lo_2444_, lean_object* v_hi_2445_){
_start:
{
lean_object* v_res_2446_; 
v_res_2446_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2___redArg(v_as_2443_, v_lo_2444_, v_hi_2445_);
lean_dec(v_hi_2445_);
return v_res_2446_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3_spec__4___redArg(lean_object* v_snd_2447_, lean_object* v_as_2448_, size_t v_i_2449_, size_t v_stop_2450_, lean_object* v_b_2451_){
_start:
{
lean_object* v___y_2453_; uint8_t v___x_2457_; 
v___x_2457_ = lean_usize_dec_eq(v_i_2449_, v_stop_2450_);
if (v___x_2457_ == 0)
{
lean_object* v___x_2458_; lean_object* v___x_2459_; 
v___x_2458_ = lean_array_uget_borrowed(v_as_2448_, v_i_2449_);
v___x_2459_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_snd_2447_, v___x_2458_);
if (lean_obj_tag(v___x_2459_) == 0)
{
v___y_2453_ = v_b_2451_;
goto v___jp_2452_;
}
else
{
lean_object* v_val_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; 
v_val_2460_ = lean_ctor_get(v___x_2459_, 0);
lean_inc(v_val_2460_);
lean_dec_ref(v___x_2459_);
lean_inc(v___x_2458_);
v___x_2461_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2461_, 0, v___x_2458_);
lean_ctor_set(v___x_2461_, 1, v_val_2460_);
v___x_2462_ = lean_array_push(v_b_2451_, v___x_2461_);
v___y_2453_ = v___x_2462_;
goto v___jp_2452_;
}
}
else
{
return v_b_2451_;
}
v___jp_2452_:
{
size_t v___x_2454_; size_t v___x_2455_; 
v___x_2454_ = ((size_t)1ULL);
v___x_2455_ = lean_usize_add(v_i_2449_, v___x_2454_);
v_i_2449_ = v___x_2455_;
v_b_2451_ = v___y_2453_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3_spec__4___redArg___boxed(lean_object* v_snd_2463_, lean_object* v_as_2464_, lean_object* v_i_2465_, lean_object* v_stop_2466_, lean_object* v_b_2467_){
_start:
{
size_t v_i_boxed_2468_; size_t v_stop_boxed_2469_; lean_object* v_res_2470_; 
v_i_boxed_2468_ = lean_unbox_usize(v_i_2465_);
lean_dec(v_i_2465_);
v_stop_boxed_2469_ = lean_unbox_usize(v_stop_2466_);
lean_dec(v_stop_2466_);
v_res_2470_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3_spec__4___redArg(v_snd_2463_, v_as_2464_, v_i_boxed_2468_, v_stop_boxed_2469_, v_b_2467_);
lean_dec_ref(v_as_2464_);
lean_dec(v_snd_2463_);
return v_res_2470_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3___redArg(lean_object* v_snd_2471_, lean_object* v_as_2472_, lean_object* v_start_2473_, lean_object* v_stop_2474_){
_start:
{
lean_object* v___x_2475_; uint8_t v___x_2476_; 
v___x_2475_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___lam__2___closed__0));
v___x_2476_ = lean_nat_dec_lt(v_start_2473_, v_stop_2474_);
if (v___x_2476_ == 0)
{
return v___x_2475_;
}
else
{
lean_object* v___x_2477_; uint8_t v___x_2478_; 
v___x_2477_ = lean_array_get_size(v_as_2472_);
v___x_2478_ = lean_nat_dec_le(v_stop_2474_, v___x_2477_);
if (v___x_2478_ == 0)
{
uint8_t v___x_2479_; 
v___x_2479_ = lean_nat_dec_lt(v_start_2473_, v___x_2477_);
if (v___x_2479_ == 0)
{
return v___x_2475_;
}
else
{
size_t v___x_2480_; size_t v___x_2481_; lean_object* v___x_2482_; 
v___x_2480_ = lean_usize_of_nat(v_start_2473_);
v___x_2481_ = lean_usize_of_nat(v___x_2477_);
v___x_2482_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3_spec__4___redArg(v_snd_2471_, v_as_2472_, v___x_2480_, v___x_2481_, v___x_2475_);
return v___x_2482_;
}
}
else
{
size_t v___x_2483_; size_t v___x_2484_; lean_object* v___x_2485_; 
v___x_2483_ = lean_usize_of_nat(v_start_2473_);
v___x_2484_ = lean_usize_of_nat(v_stop_2474_);
v___x_2485_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3_spec__4___redArg(v_snd_2471_, v_as_2472_, v___x_2483_, v___x_2484_, v___x_2475_);
return v___x_2485_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3___redArg___boxed(lean_object* v_snd_2486_, lean_object* v_as_2487_, lean_object* v_start_2488_, lean_object* v_stop_2489_){
_start:
{
lean_object* v_res_2490_; 
v_res_2490_ = l_Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3___redArg(v_snd_2486_, v_as_2487_, v_start_2488_, v_stop_2489_);
lean_dec(v_stop_2489_);
lean_dec(v_start_2488_);
lean_dec_ref(v_as_2487_);
lean_dec(v_snd_2486_);
return v_res_2490_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttribute_spec__0___redArg(lean_object* v_impl_2491_, lean_object* v_env_2492_, lean_object* v_as_2493_, size_t v_i_2494_, size_t v_stop_2495_, lean_object* v_b_2496_){
_start:
{
lean_object* v___y_2498_; uint8_t v___x_2502_; 
v___x_2502_ = lean_usize_dec_eq(v_i_2494_, v_stop_2495_);
if (v___x_2502_ == 0)
{
lean_object* v___x_2503_; lean_object* v_fst_2504_; lean_object* v_snd_2505_; lean_object* v_filterExport_2506_; lean_object* v___x_2507_; uint8_t v___x_2508_; 
v___x_2503_ = lean_array_uget_borrowed(v_as_2493_, v_i_2494_);
v_fst_2504_ = lean_ctor_get(v___x_2503_, 0);
v_snd_2505_ = lean_ctor_get(v___x_2503_, 1);
v_filterExport_2506_ = lean_ctor_get(v_impl_2491_, 3);
lean_inc_ref(v_filterExport_2506_);
lean_inc(v_snd_2505_);
lean_inc(v_fst_2504_);
lean_inc_ref(v_env_2492_);
v___x_2507_ = lean_apply_3(v_filterExport_2506_, v_env_2492_, v_fst_2504_, v_snd_2505_);
v___x_2508_ = lean_unbox(v___x_2507_);
if (v___x_2508_ == 0)
{
v___y_2498_ = v_b_2496_;
goto v___jp_2497_;
}
else
{
lean_object* v___x_2509_; 
lean_inc(v___x_2503_);
v___x_2509_ = lean_array_push(v_b_2496_, v___x_2503_);
v___y_2498_ = v___x_2509_;
goto v___jp_2497_;
}
}
else
{
lean_dec_ref(v_env_2492_);
lean_dec_ref(v_impl_2491_);
return v_b_2496_;
}
v___jp_2497_:
{
size_t v___x_2499_; size_t v___x_2500_; 
v___x_2499_ = ((size_t)1ULL);
v___x_2500_ = lean_usize_add(v_i_2494_, v___x_2499_);
v_i_2494_ = v___x_2500_;
v_b_2496_ = v___y_2498_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttribute_spec__0___redArg___boxed(lean_object* v_impl_2510_, lean_object* v_env_2511_, lean_object* v_as_2512_, lean_object* v_i_2513_, lean_object* v_stop_2514_, lean_object* v_b_2515_){
_start:
{
size_t v_i_boxed_2516_; size_t v_stop_boxed_2517_; lean_object* v_res_2518_; 
v_i_boxed_2516_ = lean_unbox_usize(v_i_2513_);
lean_dec(v_i_2513_);
v_stop_boxed_2517_ = lean_unbox_usize(v_stop_2514_);
lean_dec(v_stop_2514_);
v_res_2518_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttribute_spec__0___redArg(v_impl_2510_, v_env_2511_, v_as_2512_, v_i_boxed_2516_, v_stop_boxed_2517_, v_b_2515_);
lean_dec_ref(v_as_2512_);
return v_res_2518_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___lam__1(lean_object* v_impl_2519_, uint8_t v_preserveOrder_2520_, lean_object* v_env_2521_, lean_object* v_x_2522_, uint8_t v_lvl_2523_){
_start:
{
lean_object* v___y_2525_; 
if (v_preserveOrder_2520_ == 0)
{
lean_object* v_snd_2539_; lean_object* v___x_2540_; lean_object* v___x_2541_; lean_object* v_r_2542_; lean_object* v___y_2544_; lean_object* v___y_2545_; lean_object* v___x_2547_; uint8_t v___x_2548_; 
v_snd_2539_ = lean_ctor_get(v_x_2522_, 1);
lean_inc(v_snd_2539_);
lean_dec_ref(v_x_2522_);
v___x_2540_ = lean_unsigned_to_nat(0u);
v___x_2541_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___lam__2___closed__0));
v_r_2542_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1_spec__1___redArg(v___x_2541_, v_snd_2539_);
lean_dec(v_snd_2539_);
v___x_2547_ = lean_array_get_size(v_r_2542_);
v___x_2548_ = lean_nat_dec_eq(v___x_2547_, v___x_2540_);
if (v___x_2548_ == 0)
{
lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v___y_2552_; uint8_t v___x_2554_; 
v___x_2549_ = lean_unsigned_to_nat(1u);
v___x_2550_ = lean_nat_sub(v___x_2547_, v___x_2549_);
v___x_2554_ = lean_nat_dec_le(v___x_2540_, v___x_2550_);
if (v___x_2554_ == 0)
{
lean_inc(v___x_2550_);
v___y_2552_ = v___x_2550_;
goto v___jp_2551_;
}
else
{
v___y_2552_ = v___x_2540_;
goto v___jp_2551_;
}
v___jp_2551_:
{
uint8_t v___x_2553_; 
v___x_2553_ = lean_nat_dec_le(v___y_2552_, v___x_2550_);
if (v___x_2553_ == 0)
{
lean_dec(v___x_2550_);
lean_inc(v___y_2552_);
v___y_2544_ = v___y_2552_;
v___y_2545_ = v___y_2552_;
goto v___jp_2543_;
}
else
{
v___y_2544_ = v___y_2552_;
v___y_2545_ = v___x_2550_;
goto v___jp_2543_;
}
}
}
else
{
v___y_2525_ = v_r_2542_;
goto v___jp_2524_;
}
v___jp_2543_:
{
lean_object* v___x_2546_; 
v___x_2546_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2___redArg(v_r_2542_, v___y_2544_, v___y_2545_);
lean_dec(v___y_2545_);
v___y_2525_ = v___x_2546_;
goto v___jp_2524_;
}
}
else
{
lean_object* v_fst_2555_; lean_object* v_snd_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; 
v_fst_2555_ = lean_ctor_get(v_x_2522_, 0);
lean_inc(v_fst_2555_);
v_snd_2556_ = lean_ctor_get(v_x_2522_, 1);
lean_inc(v_snd_2556_);
lean_dec_ref(v_x_2522_);
v___x_2557_ = lean_array_mk(v_fst_2555_);
v___x_2558_ = l_Array_reverse___redArg(v___x_2557_);
v___x_2559_ = lean_unsigned_to_nat(0u);
v___x_2560_ = lean_array_get_size(v___x_2558_);
v___x_2561_ = l_Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3___redArg(v_snd_2556_, v___x_2558_, v___x_2559_, v___x_2560_);
lean_dec_ref(v___x_2558_);
lean_dec(v_snd_2556_);
v___y_2525_ = v___x_2561_;
goto v___jp_2524_;
}
v___jp_2524_:
{
uint8_t v___x_2526_; uint8_t v___x_2527_; 
v___x_2526_ = 2;
v___x_2527_ = l_Lean_instDecidableEqOLeanLevel(v_lvl_2523_, v___x_2526_);
if (v___x_2527_ == 0)
{
lean_object* v___x_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; uint8_t v___x_2531_; 
v___x_2528_ = lean_unsigned_to_nat(0u);
v___x_2529_ = lean_array_get_size(v___y_2525_);
v___x_2530_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___lam__2___closed__0));
v___x_2531_ = lean_nat_dec_lt(v___x_2528_, v___x_2529_);
if (v___x_2531_ == 0)
{
lean_dec_ref(v___y_2525_);
lean_dec_ref(v_env_2521_);
lean_dec_ref(v_impl_2519_);
return v___x_2530_;
}
else
{
uint8_t v___x_2532_; 
v___x_2532_ = lean_nat_dec_le(v___x_2529_, v___x_2529_);
if (v___x_2532_ == 0)
{
if (v___x_2531_ == 0)
{
lean_dec_ref(v___y_2525_);
lean_dec_ref(v_env_2521_);
lean_dec_ref(v_impl_2519_);
return v___x_2530_;
}
else
{
size_t v___x_2533_; size_t v___x_2534_; lean_object* v___x_2535_; 
v___x_2533_ = ((size_t)0ULL);
v___x_2534_ = lean_usize_of_nat(v___x_2529_);
v___x_2535_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttribute_spec__0___redArg(v_impl_2519_, v_env_2521_, v___y_2525_, v___x_2533_, v___x_2534_, v___x_2530_);
lean_dec_ref(v___y_2525_);
return v___x_2535_;
}
}
else
{
size_t v___x_2536_; size_t v___x_2537_; lean_object* v___x_2538_; 
v___x_2536_ = ((size_t)0ULL);
v___x_2537_ = lean_usize_of_nat(v___x_2529_);
v___x_2538_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttribute_spec__0___redArg(v_impl_2519_, v_env_2521_, v___y_2525_, v___x_2536_, v___x_2537_, v___x_2530_);
lean_dec_ref(v___y_2525_);
return v___x_2538_;
}
}
}
else
{
lean_dec_ref(v_env_2521_);
lean_dec_ref(v_impl_2519_);
return v___y_2525_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___lam__1___boxed(lean_object* v_impl_2562_, lean_object* v_preserveOrder_2563_, lean_object* v_env_2564_, lean_object* v_x_2565_, lean_object* v_lvl_2566_){
_start:
{
uint8_t v_preserveOrder_boxed_2567_; uint8_t v_lvl_boxed_2568_; lean_object* v_res_2569_; 
v_preserveOrder_boxed_2567_ = lean_unbox(v_preserveOrder_2563_);
v_lvl_boxed_2568_ = lean_unbox(v_lvl_2566_);
v_res_2569_ = l_Lean_registerParametricAttribute___redArg___lam__1(v_impl_2562_, v_preserveOrder_boxed_2567_, v_env_2564_, v_x_2565_, v_lvl_boxed_2568_);
return v_res_2569_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___lam__2(lean_object* v_x_2579_){
_start:
{
lean_object* v_snd_2580_; lean_object* v___x_2582_; uint8_t v_isShared_2583_; uint8_t v_isSharedCheck_2594_; 
v_snd_2580_ = lean_ctor_get(v_x_2579_, 1);
v_isSharedCheck_2594_ = !lean_is_exclusive(v_x_2579_);
if (v_isSharedCheck_2594_ == 0)
{
lean_object* v_unused_2595_; 
v_unused_2595_ = lean_ctor_get(v_x_2579_, 0);
lean_dec(v_unused_2595_);
v___x_2582_ = v_x_2579_;
v_isShared_2583_ = v_isSharedCheck_2594_;
goto v_resetjp_2581_;
}
else
{
lean_inc(v_snd_2580_);
lean_dec(v_x_2579_);
v___x_2582_ = lean_box(0);
v_isShared_2583_ = v_isSharedCheck_2594_;
goto v_resetjp_2581_;
}
v_resetjp_2581_:
{
lean_object* v___x_2584_; lean_object* v___y_2586_; 
v___x_2584_ = ((lean_object*)(l_Lean_registerParametricAttribute___redArg___lam__2___closed__3));
if (lean_obj_tag(v_snd_2580_) == 0)
{
lean_object* v_size_2592_; 
v_size_2592_ = lean_ctor_get(v_snd_2580_, 0);
lean_inc(v_size_2592_);
lean_dec_ref(v_snd_2580_);
v___y_2586_ = v_size_2592_;
goto v___jp_2585_;
}
else
{
lean_object* v___x_2593_; 
v___x_2593_ = lean_unsigned_to_nat(0u);
v___y_2586_ = v___x_2593_;
goto v___jp_2585_;
}
v___jp_2585_:
{
lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2590_; 
v___x_2587_ = l_Nat_reprFast(v___y_2586_);
v___x_2588_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2588_, 0, v___x_2587_);
if (v_isShared_2583_ == 0)
{
lean_ctor_set_tag(v___x_2582_, 5);
lean_ctor_set(v___x_2582_, 1, v___x_2588_);
lean_ctor_set(v___x_2582_, 0, v___x_2584_);
v___x_2590_ = v___x_2582_;
goto v_reusejp_2589_;
}
else
{
lean_object* v_reuseFailAlloc_2591_; 
v_reuseFailAlloc_2591_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2591_, 0, v___x_2584_);
lean_ctor_set(v_reuseFailAlloc_2591_, 1, v___x_2588_);
v___x_2590_ = v_reuseFailAlloc_2591_;
goto v_reusejp_2589_;
}
v_reusejp_2589_:
{
return v___x_2590_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___lam__3(lean_object* v_x_2596_){
_start:
{
lean_object* v___x_2597_; 
v___x_2597_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___lam__2___closed__0));
return v___x_2597_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___lam__3___boxed(lean_object* v_x_2598_){
_start:
{
lean_object* v_res_2599_; 
v_res_2599_ = l_Lean_registerParametricAttribute___redArg___lam__3(v_x_2598_);
lean_dec_ref(v_x_2598_);
return v_res_2599_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___lam__4(lean_object* v___x_2600_){
_start:
{
lean_object* v___x_2602_; 
v___x_2602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2602_, 0, v___x_2600_);
return v___x_2602_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___lam__4___boxed(lean_object* v___x_2603_, lean_object* v___y_2604_){
_start:
{
lean_object* v_res_2605_; 
v_res_2605_ = l_Lean_registerParametricAttribute___redArg___lam__4(v___x_2603_);
return v_res_2605_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___lam__5(lean_object* v___x_2606_, lean_object* v_x_2607_, lean_object* v___y_2608_){
_start:
{
lean_object* v___x_2610_; 
v___x_2610_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2610_, 0, v___x_2606_);
return v___x_2610_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___lam__5___boxed(lean_object* v___x_2611_, lean_object* v_x_2612_, lean_object* v___y_2613_, lean_object* v___y_2614_){
_start:
{
lean_object* v_res_2615_; 
v_res_2615_ = l_Lean_registerParametricAttribute___redArg___lam__5(v___x_2611_, v_x_2612_, v___y_2613_);
lean_dec_ref(v___y_2613_);
lean_dec_ref(v_x_2612_);
return v_res_2615_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___lam__7(lean_object* v_getParam_2616_, lean_object* v_a_2617_, lean_object* v_afterSet_2618_, lean_object* v_name_2619_, lean_object* v_decl_2620_, lean_object* v_stx_2621_, uint8_t v_kind_2622_, lean_object* v___y_2623_, lean_object* v___y_2624_){
_start:
{
lean_object* v___y_2627_; lean_object* v___y_2628_; lean_object* v___y_2629_; lean_object* v___y_2630_; uint8_t v___y_2631_; lean_object* v___y_2634_; lean_object* v___y_2635_; lean_object* v___y_2636_; uint8_t v___x_2679_; uint8_t v___x_2680_; 
v___x_2679_ = 0;
v___x_2680_ = l_Lean_instBEqAttributeKind_beq(v_kind_2622_, v___x_2679_);
if (v___x_2680_ == 0)
{
lean_object* v___x_2681_; 
lean_dec(v_stx_2621_);
lean_dec(v_decl_2620_);
lean_dec_ref(v_afterSet_2618_);
lean_dec_ref(v_a_2617_);
lean_dec_ref(v_getParam_2616_);
v___x_2681_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg(v_name_2619_, v_kind_2622_, v___y_2623_, v___y_2624_);
lean_dec(v___y_2624_);
lean_dec_ref(v___y_2623_);
return v___x_2681_;
}
else
{
goto v___jp_2674_;
}
v___jp_2626_:
{
lean_dec_ref(v___y_2630_);
if (v___y_2631_ == 0)
{
lean_object* v___x_2632_; 
lean_dec_ref(v___y_2629_);
v___x_2632_ = l_Lean_setEnv___at___00Lean_registerParametricAttribute_spec__4___redArg(v___y_2628_, v___y_2627_);
lean_dec(v___y_2627_);
return v___x_2632_;
}
else
{
lean_dec_ref(v___y_2628_);
lean_dec(v___y_2627_);
return v___y_2629_;
}
}
v___jp_2633_:
{
lean_object* v___x_2637_; 
lean_inc(v___y_2636_);
lean_inc_ref(v___y_2635_);
lean_inc(v_decl_2620_);
v___x_2637_ = lean_apply_5(v_getParam_2616_, v_decl_2620_, v_stx_2621_, v___y_2635_, v___y_2636_, lean_box(0));
if (lean_obj_tag(v___x_2637_) == 0)
{
lean_object* v_a_2638_; lean_object* v___x_2639_; lean_object* v_toEnvExtension_2640_; lean_object* v_env_2641_; lean_object* v_nextMacroScope_2642_; lean_object* v_ngen_2643_; lean_object* v_auxDeclNGen_2644_; lean_object* v_traceState_2645_; lean_object* v_messages_2646_; lean_object* v_infoState_2647_; lean_object* v_snapshotTasks_2648_; lean_object* v___x_2650_; uint8_t v_isShared_2651_; uint8_t v_isSharedCheck_2664_; 
v_a_2638_ = lean_ctor_get(v___x_2637_, 0);
lean_inc(v_a_2638_);
lean_dec_ref(v___x_2637_);
v___x_2639_ = lean_st_ref_take(v___y_2636_);
v_toEnvExtension_2640_ = lean_ctor_get(v_a_2617_, 0);
v_env_2641_ = lean_ctor_get(v___x_2639_, 0);
v_nextMacroScope_2642_ = lean_ctor_get(v___x_2639_, 1);
v_ngen_2643_ = lean_ctor_get(v___x_2639_, 2);
v_auxDeclNGen_2644_ = lean_ctor_get(v___x_2639_, 3);
v_traceState_2645_ = lean_ctor_get(v___x_2639_, 4);
v_messages_2646_ = lean_ctor_get(v___x_2639_, 6);
v_infoState_2647_ = lean_ctor_get(v___x_2639_, 7);
v_snapshotTasks_2648_ = lean_ctor_get(v___x_2639_, 8);
v_isSharedCheck_2664_ = !lean_is_exclusive(v___x_2639_);
if (v_isSharedCheck_2664_ == 0)
{
lean_object* v_unused_2665_; 
v_unused_2665_ = lean_ctor_get(v___x_2639_, 5);
lean_dec(v_unused_2665_);
v___x_2650_ = v___x_2639_;
v_isShared_2651_ = v_isSharedCheck_2664_;
goto v_resetjp_2649_;
}
else
{
lean_inc(v_snapshotTasks_2648_);
lean_inc(v_infoState_2647_);
lean_inc(v_messages_2646_);
lean_inc(v_traceState_2645_);
lean_inc(v_auxDeclNGen_2644_);
lean_inc(v_ngen_2643_);
lean_inc(v_nextMacroScope_2642_);
lean_inc(v_env_2641_);
lean_dec(v___x_2639_);
v___x_2650_ = lean_box(0);
v_isShared_2651_ = v_isSharedCheck_2664_;
goto v_resetjp_2649_;
}
v_resetjp_2649_:
{
lean_object* v_asyncMode_2652_; lean_object* v___x_2653_; lean_object* v___x_2654_; lean_object* v___x_2655_; lean_object* v___x_2657_; 
v_asyncMode_2652_ = lean_ctor_get(v_toEnvExtension_2640_, 2);
lean_inc(v_asyncMode_2652_);
lean_inc(v_a_2638_);
lean_inc(v_decl_2620_);
v___x_2653_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2653_, 0, v_decl_2620_);
lean_ctor_set(v___x_2653_, 1, v_a_2638_);
lean_inc(v_decl_2620_);
v___x_2654_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_a_2617_, v_env_2641_, v___x_2653_, v_asyncMode_2652_, v_decl_2620_);
lean_dec(v_asyncMode_2652_);
v___x_2655_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2);
if (v_isShared_2651_ == 0)
{
lean_ctor_set(v___x_2650_, 5, v___x_2655_);
lean_ctor_set(v___x_2650_, 0, v___x_2654_);
v___x_2657_ = v___x_2650_;
goto v_reusejp_2656_;
}
else
{
lean_object* v_reuseFailAlloc_2663_; 
v_reuseFailAlloc_2663_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2663_, 0, v___x_2654_);
lean_ctor_set(v_reuseFailAlloc_2663_, 1, v_nextMacroScope_2642_);
lean_ctor_set(v_reuseFailAlloc_2663_, 2, v_ngen_2643_);
lean_ctor_set(v_reuseFailAlloc_2663_, 3, v_auxDeclNGen_2644_);
lean_ctor_set(v_reuseFailAlloc_2663_, 4, v_traceState_2645_);
lean_ctor_set(v_reuseFailAlloc_2663_, 5, v___x_2655_);
lean_ctor_set(v_reuseFailAlloc_2663_, 6, v_messages_2646_);
lean_ctor_set(v_reuseFailAlloc_2663_, 7, v_infoState_2647_);
lean_ctor_set(v_reuseFailAlloc_2663_, 8, v_snapshotTasks_2648_);
v___x_2657_ = v_reuseFailAlloc_2663_;
goto v_reusejp_2656_;
}
v_reusejp_2656_:
{
lean_object* v___x_2658_; lean_object* v___x_2659_; 
v___x_2658_ = lean_st_ref_set(v___y_2636_, v___x_2657_);
lean_inc(v___y_2636_);
lean_inc_ref(v___y_2635_);
v___x_2659_ = lean_apply_5(v_afterSet_2618_, v_decl_2620_, v_a_2638_, v___y_2635_, v___y_2636_, lean_box(0));
if (lean_obj_tag(v___x_2659_) == 0)
{
lean_dec(v___y_2636_);
lean_dec_ref(v___y_2635_);
lean_dec_ref(v___y_2634_);
return v___x_2659_;
}
else
{
lean_object* v_a_2660_; uint8_t v___x_2661_; 
v_a_2660_ = lean_ctor_get(v___x_2659_, 0);
lean_inc(v_a_2660_);
v___x_2661_ = l_Lean_Exception_isInterrupt(v_a_2660_);
if (v___x_2661_ == 0)
{
uint8_t v___x_2662_; 
v___x_2662_ = l_Lean_Exception_isRuntime(v_a_2660_);
v___y_2627_ = v___y_2636_;
v___y_2628_ = v___y_2634_;
v___y_2629_ = v___x_2659_;
v___y_2630_ = v___y_2635_;
v___y_2631_ = v___x_2662_;
goto v___jp_2626_;
}
else
{
lean_dec(v_a_2660_);
v___y_2627_ = v___y_2636_;
v___y_2628_ = v___y_2634_;
v___y_2629_ = v___x_2659_;
v___y_2630_ = v___y_2635_;
v___y_2631_ = v___x_2661_;
goto v___jp_2626_;
}
}
}
}
}
else
{
lean_object* v_a_2666_; lean_object* v___x_2668_; uint8_t v_isShared_2669_; uint8_t v_isSharedCheck_2673_; 
lean_dec(v___y_2636_);
lean_dec_ref(v___y_2635_);
lean_dec_ref(v___y_2634_);
lean_dec(v_decl_2620_);
lean_dec_ref(v_afterSet_2618_);
lean_dec_ref(v_a_2617_);
v_a_2666_ = lean_ctor_get(v___x_2637_, 0);
v_isSharedCheck_2673_ = !lean_is_exclusive(v___x_2637_);
if (v_isSharedCheck_2673_ == 0)
{
v___x_2668_ = v___x_2637_;
v_isShared_2669_ = v_isSharedCheck_2673_;
goto v_resetjp_2667_;
}
else
{
lean_inc(v_a_2666_);
lean_dec(v___x_2637_);
v___x_2668_ = lean_box(0);
v_isShared_2669_ = v_isSharedCheck_2673_;
goto v_resetjp_2667_;
}
v_resetjp_2667_:
{
lean_object* v___x_2671_; 
if (v_isShared_2669_ == 0)
{
v___x_2671_ = v___x_2668_;
goto v_reusejp_2670_;
}
else
{
lean_object* v_reuseFailAlloc_2672_; 
v_reuseFailAlloc_2672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2672_, 0, v_a_2666_);
v___x_2671_ = v_reuseFailAlloc_2672_;
goto v_reusejp_2670_;
}
v_reusejp_2670_:
{
return v___x_2671_;
}
}
}
}
v___jp_2674_:
{
lean_object* v___x_2675_; lean_object* v_env_2676_; lean_object* v___x_2677_; 
v___x_2675_ = lean_st_ref_get(v___y_2624_);
v_env_2676_ = lean_ctor_get(v___x_2675_, 0);
lean_inc_ref(v_env_2676_);
lean_dec(v___x_2675_);
v___x_2677_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2676_, v_decl_2620_);
if (lean_obj_tag(v___x_2677_) == 0)
{
lean_dec(v_name_2619_);
v___y_2634_ = v_env_2676_;
v___y_2635_ = v___y_2623_;
v___y_2636_ = v___y_2624_;
goto v___jp_2633_;
}
else
{
lean_object* v___x_2678_; 
lean_dec_ref(v___x_2677_);
lean_dec_ref(v_env_2676_);
lean_dec(v_stx_2621_);
lean_dec_ref(v_afterSet_2618_);
lean_dec_ref(v_a_2617_);
lean_dec_ref(v_getParam_2616_);
v___x_2678_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg(v_name_2619_, v_decl_2620_, v___y_2623_, v___y_2624_);
lean_dec(v___y_2624_);
lean_dec_ref(v___y_2623_);
return v___x_2678_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___lam__7___boxed(lean_object* v_getParam_2682_, lean_object* v_a_2683_, lean_object* v_afterSet_2684_, lean_object* v_name_2685_, lean_object* v_decl_2686_, lean_object* v_stx_2687_, lean_object* v_kind_2688_, lean_object* v___y_2689_, lean_object* v___y_2690_, lean_object* v___y_2691_){
_start:
{
uint8_t v_kind_boxed_2692_; lean_object* v_res_2693_; 
v_kind_boxed_2692_ = lean_unbox(v_kind_2688_);
v_res_2693_ = l_Lean_registerParametricAttribute___redArg___lam__7(v_getParam_2682_, v_a_2683_, v_afterSet_2684_, v_name_2685_, v_decl_2686_, v_stx_2687_, v_kind_boxed_2692_, v___y_2689_, v___y_2690_);
return v_res_2693_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg(lean_object* v_impl_2704_){
_start:
{
lean_object* v_toAttributeImplCore_2706_; lean_object* v_getParam_2707_; lean_object* v_afterSet_2708_; uint8_t v_preserveOrder_2709_; lean_object* v_ref_2710_; lean_object* v_name_2711_; lean_object* v___f_2712_; lean_object* v___x_2713_; lean_object* v___f_2714_; lean_object* v___f_2715_; lean_object* v___f_2716_; lean_object* v___f_2717_; lean_object* v___f_2718_; lean_object* v___x_2719_; lean_object* v___x_2720_; lean_object* v___x_2721_; lean_object* v___x_2722_; lean_object* v___x_2723_; 
v_toAttributeImplCore_2706_ = lean_ctor_get(v_impl_2704_, 0);
lean_inc_ref(v_toAttributeImplCore_2706_);
v_getParam_2707_ = lean_ctor_get(v_impl_2704_, 1);
lean_inc_ref(v_getParam_2707_);
v_afterSet_2708_ = lean_ctor_get(v_impl_2704_, 2);
lean_inc_ref(v_afterSet_2708_);
v_preserveOrder_2709_ = lean_ctor_get_uint8(v_impl_2704_, sizeof(void*)*4);
v_ref_2710_ = lean_ctor_get(v_toAttributeImplCore_2706_, 0);
v_name_2711_ = lean_ctor_get(v_toAttributeImplCore_2706_, 1);
v___f_2712_ = ((lean_object*)(l_Lean_registerParametricAttribute___redArg___closed__0));
v___x_2713_ = lean_box(v_preserveOrder_2709_);
v___f_2714_ = lean_alloc_closure((void*)(l_Lean_registerParametricAttribute___redArg___lam__1___boxed), 5, 2);
lean_closure_set(v___f_2714_, 0, v_impl_2704_);
lean_closure_set(v___f_2714_, 1, v___x_2713_);
v___f_2715_ = ((lean_object*)(l_Lean_registerParametricAttribute___redArg___closed__1));
v___f_2716_ = ((lean_object*)(l_Lean_registerParametricAttribute___redArg___closed__2));
v___f_2717_ = ((lean_object*)(l_Lean_registerParametricAttribute___redArg___closed__4));
v___f_2718_ = ((lean_object*)(l_Lean_registerParametricAttribute___redArg___closed__5));
v___x_2719_ = lean_box(2);
v___x_2720_ = lean_box(0);
lean_inc(v_ref_2710_);
v___x_2721_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_2721_, 0, v_ref_2710_);
lean_ctor_set(v___x_2721_, 1, v___f_2717_);
lean_ctor_set(v___x_2721_, 2, v___f_2718_);
lean_ctor_set(v___x_2721_, 3, v___f_2712_);
lean_ctor_set(v___x_2721_, 4, v___f_2714_);
lean_ctor_set(v___x_2721_, 5, v___f_2715_);
lean_ctor_set(v___x_2721_, 6, v___x_2719_);
lean_ctor_set(v___x_2721_, 7, v___x_2720_);
v___x_2722_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2722_, 0, v___x_2721_);
lean_ctor_set(v___x_2722_, 1, v___f_2716_);
v___x_2723_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_2722_);
if (lean_obj_tag(v___x_2723_) == 0)
{
lean_object* v_a_2724_; lean_object* v___f_2725_; lean_object* v___f_2726_; lean_object* v___x_2727_; lean_object* v___x_2728_; 
v_a_2724_ = lean_ctor_get(v___x_2723_, 0);
lean_inc(v_a_2724_);
lean_dec_ref(v___x_2723_);
lean_inc(v_name_2711_);
v___f_2725_ = lean_alloc_closure((void*)(l_Lean_registerTagAttribute___lam__6___boxed), 5, 1);
lean_closure_set(v___f_2725_, 0, v_name_2711_);
lean_inc(v_name_2711_);
lean_inc(v_a_2724_);
v___f_2726_ = lean_alloc_closure((void*)(l_Lean_registerParametricAttribute___redArg___lam__7___boxed), 10, 4);
lean_closure_set(v___f_2726_, 0, v_getParam_2707_);
lean_closure_set(v___f_2726_, 1, v_a_2724_);
lean_closure_set(v___f_2726_, 2, v_afterSet_2708_);
lean_closure_set(v___f_2726_, 3, v_name_2711_);
v___x_2727_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2727_, 0, v_toAttributeImplCore_2706_);
lean_ctor_set(v___x_2727_, 1, v___f_2726_);
lean_ctor_set(v___x_2727_, 2, v___f_2725_);
lean_inc_ref(v___x_2727_);
v___x_2728_ = l_Lean_registerBuiltinAttribute(v___x_2727_);
if (lean_obj_tag(v___x_2728_) == 0)
{
lean_object* v___x_2730_; uint8_t v_isShared_2731_; uint8_t v_isSharedCheck_2736_; 
v_isSharedCheck_2736_ = !lean_is_exclusive(v___x_2728_);
if (v_isSharedCheck_2736_ == 0)
{
lean_object* v_unused_2737_; 
v_unused_2737_ = lean_ctor_get(v___x_2728_, 0);
lean_dec(v_unused_2737_);
v___x_2730_ = v___x_2728_;
v_isShared_2731_ = v_isSharedCheck_2736_;
goto v_resetjp_2729_;
}
else
{
lean_dec(v___x_2728_);
v___x_2730_ = lean_box(0);
v_isShared_2731_ = v_isSharedCheck_2736_;
goto v_resetjp_2729_;
}
v_resetjp_2729_:
{
lean_object* v___x_2732_; lean_object* v___x_2734_; 
v___x_2732_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2732_, 0, v___x_2727_);
lean_ctor_set(v___x_2732_, 1, v_a_2724_);
lean_ctor_set_uint8(v___x_2732_, sizeof(void*)*2, v_preserveOrder_2709_);
if (v_isShared_2731_ == 0)
{
lean_ctor_set(v___x_2730_, 0, v___x_2732_);
v___x_2734_ = v___x_2730_;
goto v_reusejp_2733_;
}
else
{
lean_object* v_reuseFailAlloc_2735_; 
v_reuseFailAlloc_2735_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2735_, 0, v___x_2732_);
v___x_2734_ = v_reuseFailAlloc_2735_;
goto v_reusejp_2733_;
}
v_reusejp_2733_:
{
return v___x_2734_;
}
}
}
else
{
lean_object* v_a_2738_; lean_object* v___x_2740_; uint8_t v_isShared_2741_; uint8_t v_isSharedCheck_2745_; 
lean_dec_ref(v___x_2727_);
lean_dec(v_a_2724_);
v_a_2738_ = lean_ctor_get(v___x_2728_, 0);
v_isSharedCheck_2745_ = !lean_is_exclusive(v___x_2728_);
if (v_isSharedCheck_2745_ == 0)
{
v___x_2740_ = v___x_2728_;
v_isShared_2741_ = v_isSharedCheck_2745_;
goto v_resetjp_2739_;
}
else
{
lean_inc(v_a_2738_);
lean_dec(v___x_2728_);
v___x_2740_ = lean_box(0);
v_isShared_2741_ = v_isSharedCheck_2745_;
goto v_resetjp_2739_;
}
v_resetjp_2739_:
{
lean_object* v___x_2743_; 
if (v_isShared_2741_ == 0)
{
v___x_2743_ = v___x_2740_;
goto v_reusejp_2742_;
}
else
{
lean_object* v_reuseFailAlloc_2744_; 
v_reuseFailAlloc_2744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2744_, 0, v_a_2738_);
v___x_2743_ = v_reuseFailAlloc_2744_;
goto v_reusejp_2742_;
}
v_reusejp_2742_:
{
return v___x_2743_;
}
}
}
}
else
{
lean_object* v_a_2746_; lean_object* v___x_2748_; uint8_t v_isShared_2749_; uint8_t v_isSharedCheck_2753_; 
lean_dec_ref(v_afterSet_2708_);
lean_dec_ref(v_getParam_2707_);
lean_dec_ref(v_toAttributeImplCore_2706_);
v_a_2746_ = lean_ctor_get(v___x_2723_, 0);
v_isSharedCheck_2753_ = !lean_is_exclusive(v___x_2723_);
if (v_isSharedCheck_2753_ == 0)
{
v___x_2748_ = v___x_2723_;
v_isShared_2749_ = v_isSharedCheck_2753_;
goto v_resetjp_2747_;
}
else
{
lean_inc(v_a_2746_);
lean_dec(v___x_2723_);
v___x_2748_ = lean_box(0);
v_isShared_2749_ = v_isSharedCheck_2753_;
goto v_resetjp_2747_;
}
v_resetjp_2747_:
{
lean_object* v___x_2751_; 
if (v_isShared_2749_ == 0)
{
v___x_2751_ = v___x_2748_;
goto v_reusejp_2750_;
}
else
{
lean_object* v_reuseFailAlloc_2752_; 
v_reuseFailAlloc_2752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2752_, 0, v_a_2746_);
v___x_2751_ = v_reuseFailAlloc_2752_;
goto v_reusejp_2750_;
}
v_reusejp_2750_:
{
return v___x_2751_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___boxed(lean_object* v_impl_2754_, lean_object* v_a_2755_){
_start:
{
lean_object* v_res_2756_; 
v_res_2756_ = l_Lean_registerParametricAttribute___redArg(v_impl_2754_);
return v_res_2756_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute(lean_object* v_00_u03b1_2757_, lean_object* v_impl_2758_){
_start:
{
lean_object* v___x_2760_; 
v___x_2760_ = l_Lean_registerParametricAttribute___redArg(v_impl_2758_);
return v___x_2760_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___boxed(lean_object* v_00_u03b1_2761_, lean_object* v_impl_2762_, lean_object* v_a_2763_){
_start:
{
lean_object* v_res_2764_; 
v_res_2764_ = l_Lean_registerParametricAttribute(v_00_u03b1_2761_, v_impl_2762_);
return v_res_2764_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttribute_spec__0(lean_object* v_00_u03b1_2765_, lean_object* v_impl_2766_, lean_object* v_env_2767_, lean_object* v_as_2768_, size_t v_i_2769_, size_t v_stop_2770_, lean_object* v_b_2771_){
_start:
{
lean_object* v___x_2772_; 
v___x_2772_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttribute_spec__0___redArg(v_impl_2766_, v_env_2767_, v_as_2768_, v_i_2769_, v_stop_2770_, v_b_2771_);
return v___x_2772_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttribute_spec__0___boxed(lean_object* v_00_u03b1_2773_, lean_object* v_impl_2774_, lean_object* v_env_2775_, lean_object* v_as_2776_, lean_object* v_i_2777_, lean_object* v_stop_2778_, lean_object* v_b_2779_){
_start:
{
size_t v_i_boxed_2780_; size_t v_stop_boxed_2781_; lean_object* v_res_2782_; 
v_i_boxed_2780_ = lean_unbox_usize(v_i_2777_);
lean_dec(v_i_2777_);
v_stop_boxed_2781_ = lean_unbox_usize(v_stop_2778_);
lean_dec(v_stop_2778_);
v_res_2782_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttribute_spec__0(v_00_u03b1_2773_, v_impl_2774_, v_env_2775_, v_as_2776_, v_i_boxed_2780_, v_stop_boxed_2781_, v_b_2779_);
lean_dec_ref(v_as_2776_);
return v_res_2782_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1___redArg(lean_object* v_init_2783_, lean_object* v_t_2784_){
_start:
{
lean_object* v___x_2785_; 
v___x_2785_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1_spec__1___redArg(v_init_2783_, v_t_2784_);
return v___x_2785_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1___redArg___boxed(lean_object* v_init_2786_, lean_object* v_t_2787_){
_start:
{
lean_object* v_res_2788_; 
v_res_2788_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1___redArg(v_init_2786_, v_t_2787_);
lean_dec(v_t_2787_);
return v_res_2788_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1(lean_object* v_00_u03b1_2789_, lean_object* v_init_2790_, lean_object* v_t_2791_){
_start:
{
lean_object* v___x_2792_; 
v___x_2792_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1_spec__1___redArg(v_init_2790_, v_t_2791_);
return v___x_2792_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1___boxed(lean_object* v_00_u03b1_2793_, lean_object* v_init_2794_, lean_object* v_t_2795_){
_start:
{
lean_object* v_res_2796_; 
v_res_2796_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1(v_00_u03b1_2793_, v_init_2794_, v_t_2795_);
lean_dec(v_t_2795_);
return v_res_2796_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2(lean_object* v_00_u03b1_2797_, lean_object* v_n_2798_, lean_object* v_as_2799_, lean_object* v_lo_2800_, lean_object* v_hi_2801_, lean_object* v_w_2802_, lean_object* v_hlo_2803_, lean_object* v_hhi_2804_){
_start:
{
lean_object* v___x_2805_; 
v___x_2805_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2___redArg(v_as_2799_, v_lo_2800_, v_hi_2801_);
return v___x_2805_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2___boxed(lean_object* v_00_u03b1_2806_, lean_object* v_n_2807_, lean_object* v_as_2808_, lean_object* v_lo_2809_, lean_object* v_hi_2810_, lean_object* v_w_2811_, lean_object* v_hlo_2812_, lean_object* v_hhi_2813_){
_start:
{
lean_object* v_res_2814_; 
v_res_2814_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2(v_00_u03b1_2806_, v_n_2807_, v_as_2808_, v_lo_2809_, v_hi_2810_, v_w_2811_, v_hlo_2812_, v_hhi_2813_);
lean_dec(v_hi_2810_);
lean_dec(v_n_2807_);
return v_res_2814_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3(lean_object* v_00_u03b1_2815_, lean_object* v_snd_2816_, lean_object* v_as_2817_, lean_object* v_start_2818_, lean_object* v_stop_2819_){
_start:
{
lean_object* v___x_2820_; 
v___x_2820_ = l_Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3___redArg(v_snd_2816_, v_as_2817_, v_start_2818_, v_stop_2819_);
return v___x_2820_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3___boxed(lean_object* v_00_u03b1_2821_, lean_object* v_snd_2822_, lean_object* v_as_2823_, lean_object* v_start_2824_, lean_object* v_stop_2825_){
_start:
{
lean_object* v_res_2826_; 
v_res_2826_ = l_Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3(v_00_u03b1_2821_, v_snd_2822_, v_as_2823_, v_start_2824_, v_stop_2825_);
lean_dec(v_stop_2825_);
lean_dec(v_start_2824_);
lean_dec_ref(v_as_2823_);
lean_dec(v_snd_2822_);
return v_res_2826_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1_spec__1(lean_object* v_00_u03b1_2827_, lean_object* v_init_2828_, lean_object* v_x_2829_){
_start:
{
lean_object* v___x_2830_; 
v___x_2830_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1_spec__1___redArg(v_init_2828_, v_x_2829_);
return v___x_2830_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1_spec__1___boxed(lean_object* v_00_u03b1_2831_, lean_object* v_init_2832_, lean_object* v_x_2833_){
_start:
{
lean_object* v_res_2834_; 
v_res_2834_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1_spec__1(v_00_u03b1_2831_, v_init_2832_, v_x_2833_);
lean_dec(v_x_2833_);
return v_res_2834_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3_spec__4(lean_object* v_00_u03b1_2835_, lean_object* v_snd_2836_, lean_object* v_as_2837_, size_t v_i_2838_, size_t v_stop_2839_, lean_object* v_b_2840_){
_start:
{
lean_object* v___x_2841_; 
v___x_2841_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3_spec__4___redArg(v_snd_2836_, v_as_2837_, v_i_2838_, v_stop_2839_, v_b_2840_);
return v___x_2841_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3_spec__4___boxed(lean_object* v_00_u03b1_2842_, lean_object* v_snd_2843_, lean_object* v_as_2844_, lean_object* v_i_2845_, lean_object* v_stop_2846_, lean_object* v_b_2847_){
_start:
{
size_t v_i_boxed_2848_; size_t v_stop_boxed_2849_; lean_object* v_res_2850_; 
v_i_boxed_2848_ = lean_unbox_usize(v_i_2845_);
lean_dec(v_i_2845_);
v_stop_boxed_2849_ = lean_unbox_usize(v_stop_2846_);
lean_dec(v_stop_2846_);
v_res_2850_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3_spec__4(v_00_u03b1_2842_, v_snd_2843_, v_as_2844_, v_i_boxed_2848_, v_stop_boxed_2849_, v_b_2847_);
lean_dec_ref(v_as_2844_);
lean_dec(v_snd_2843_);
return v_res_2850_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParam_x3f___redArg___lam__1(lean_object* v_decl_2851_, lean_object* v___x_2852_, lean_object* v___x_2853_, lean_object* v_a_2854_, lean_object* v_x_2855_, lean_object* v___y_2856_){
_start:
{
lean_object* v_fst_2857_; uint8_t v___x_2858_; 
v_fst_2857_ = lean_ctor_get(v_a_2854_, 0);
v___x_2858_ = lean_name_eq(v_fst_2857_, v_decl_2851_);
if (v___x_2858_ == 0)
{
lean_object* v___x_2859_; 
lean_dec_ref(v_a_2854_);
v___x_2859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2859_, 0, v___x_2852_);
return v___x_2859_;
}
else
{
lean_object* v___x_2860_; lean_object* v___x_2861_; lean_object* v___x_2862_; lean_object* v___x_2863_; 
lean_dec_ref(v___x_2852_);
v___x_2860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2860_, 0, v_a_2854_);
v___x_2861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2861_, 0, v___x_2860_);
v___x_2862_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2862_, 0, v___x_2861_);
lean_ctor_set(v___x_2862_, 1, v___x_2853_);
v___x_2863_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2863_, 0, v___x_2862_);
return v___x_2863_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParam_x3f___redArg___lam__1___boxed(lean_object* v_decl_2864_, lean_object* v___x_2865_, lean_object* v___x_2866_, lean_object* v_a_2867_, lean_object* v_x_2868_, lean_object* v___y_2869_){
_start:
{
lean_object* v_res_2870_; 
v_res_2870_ = l_Lean_ParametricAttribute_getParam_x3f___redArg___lam__1(v_decl_2864_, v___x_2865_, v___x_2866_, v_a_2867_, v_x_2868_, v___y_2869_);
lean_dec_ref(v___y_2869_);
lean_dec(v_decl_2864_);
return v_res_2870_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParam_x3f___redArg(lean_object* v_inst_2897_, lean_object* v_attr_2898_, lean_object* v_env_2899_, lean_object* v_decl_2900_){
_start:
{
lean_object* v___y_2902_; lean_object* v___x_2913_; lean_object* v___x_2914_; 
v___x_2913_ = ((lean_object*)(l_Lean_ParametricAttribute_getParam_x3f___redArg___closed__0));
v___x_2914_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2899_, v_decl_2900_);
if (lean_obj_tag(v___x_2914_) == 0)
{
lean_object* v_ext_2915_; lean_object* v_toEnvExtension_2916_; lean_object* v_asyncMode_2917_; lean_object* v___x_2918_; lean_object* v___x_2919_; lean_object* v_snd_2920_; lean_object* v___x_2921_; 
lean_dec(v_inst_2897_);
v_ext_2915_ = lean_ctor_get(v_attr_2898_, 1);
v_toEnvExtension_2916_ = lean_ctor_get(v_ext_2915_, 0);
v_asyncMode_2917_ = lean_ctor_get(v_toEnvExtension_2916_, 2);
v___x_2918_ = lean_box(0);
v___x_2919_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2913_, v_ext_2915_, v_env_2899_, v_asyncMode_2917_, v___x_2918_);
v_snd_2920_ = lean_ctor_get(v___x_2919_, 1);
lean_inc(v_snd_2920_);
lean_dec(v___x_2919_);
v___x_2921_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_snd_2920_, v_decl_2900_);
lean_dec(v_decl_2900_);
lean_dec(v_snd_2920_);
return v___x_2921_;
}
else
{
uint8_t v_preserveOrder_2922_; 
v_preserveOrder_2922_ = lean_ctor_get_uint8(v_attr_2898_, sizeof(void*)*2);
if (v_preserveOrder_2922_ == 0)
{
lean_object* v_val_2923_; lean_object* v_ext_2924_; uint8_t v___x_2925_; lean_object* v___x_2926_; lean_object* v___x_2927_; lean_object* v___x_2928_; uint8_t v___x_2929_; 
v_val_2923_ = lean_ctor_get(v___x_2914_, 0);
lean_inc(v_val_2923_);
lean_dec_ref(v___x_2914_);
v_ext_2924_ = lean_ctor_get(v_attr_2898_, 1);
v___x_2925_ = 0;
v___x_2926_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_2913_, v_ext_2924_, v_env_2899_, v_val_2923_, v___x_2925_);
lean_dec(v_val_2923_);
lean_dec_ref(v_env_2899_);
v___x_2927_ = lean_unsigned_to_nat(0u);
v___x_2928_ = lean_array_get_size(v___x_2926_);
v___x_2929_ = lean_nat_dec_lt(v___x_2927_, v___x_2928_);
if (v___x_2929_ == 0)
{
lean_object* v___x_2930_; 
lean_dec_ref(v___x_2926_);
lean_dec(v_decl_2900_);
lean_dec(v_inst_2897_);
v___x_2930_ = lean_box(0);
return v___x_2930_;
}
else
{
lean_object* v___x_2931_; lean_object* v___x_2932_; uint8_t v___x_2933_; 
v___x_2931_ = lean_unsigned_to_nat(1u);
v___x_2932_ = lean_nat_sub(v___x_2928_, v___x_2931_);
v___x_2933_ = lean_nat_dec_le(v___x_2927_, v___x_2932_);
if (v___x_2933_ == 0)
{
lean_object* v___x_2934_; 
lean_dec(v___x_2932_);
lean_dec_ref(v___x_2926_);
lean_dec(v_decl_2900_);
lean_dec(v_inst_2897_);
v___x_2934_ = lean_box(0);
return v___x_2934_;
}
else
{
lean_object* v___f_2935_; lean_object* v___x_2936_; lean_object* v___x_2937_; lean_object* v___x_2938_; 
v___f_2935_ = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2___redArg___closed__0));
v___x_2936_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2936_, 0, v_decl_2900_);
lean_ctor_set(v___x_2936_, 1, v_inst_2897_);
v___x_2937_ = ((lean_object*)(l_Lean_ParametricAttribute_getParam_x3f___redArg___closed__1));
v___x_2938_ = l_Array_binSearchAux___redArg(v___f_2935_, v___x_2937_, v___x_2926_, v___x_2936_, v___x_2927_, v___x_2932_);
lean_dec_ref(v___x_2926_);
v___y_2902_ = v___x_2938_;
goto v___jp_2901_;
}
}
}
else
{
lean_object* v_val_2939_; lean_object* v_ext_2940_; uint8_t v___x_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; lean_object* v___x_2944_; lean_object* v___x_2945_; lean_object* v___x_2946_; lean_object* v___f_2947_; size_t v_sz_2948_; size_t v___x_2949_; lean_object* v___x_2950_; lean_object* v_fst_2951_; 
lean_dec(v_inst_2897_);
v_val_2939_ = lean_ctor_get(v___x_2914_, 0);
lean_inc(v_val_2939_);
lean_dec_ref(v___x_2914_);
v_ext_2940_ = lean_ctor_get(v_attr_2898_, 1);
v___x_2941_ = 0;
v___x_2942_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_2913_, v_ext_2940_, v_env_2899_, v_val_2939_, v___x_2941_);
lean_dec(v_val_2939_);
lean_dec_ref(v_env_2899_);
v___x_2943_ = ((lean_object*)(l_Lean_ParametricAttribute_getParam_x3f___redArg___closed__11));
v___x_2944_ = lean_box(0);
v___x_2945_ = lean_box(0);
v___x_2946_ = ((lean_object*)(l_Lean_ParametricAttribute_getParam_x3f___redArg___closed__12));
v___f_2947_ = lean_alloc_closure((void*)(l_Lean_ParametricAttribute_getParam_x3f___redArg___lam__1___boxed), 6, 3);
lean_closure_set(v___f_2947_, 0, v_decl_2900_);
lean_closure_set(v___f_2947_, 1, v___x_2946_);
lean_closure_set(v___f_2947_, 2, v___x_2945_);
v_sz_2948_ = lean_array_size(v___x_2942_);
v___x_2949_ = ((size_t)0ULL);
v___x_2950_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_2943_, v___x_2942_, v___f_2947_, v_sz_2948_, v___x_2949_, v___x_2946_);
v_fst_2951_ = lean_ctor_get(v___x_2950_, 0);
lean_inc(v_fst_2951_);
lean_dec(v___x_2950_);
if (lean_obj_tag(v_fst_2951_) == 0)
{
return v___x_2944_;
}
else
{
lean_object* v_val_2952_; 
v_val_2952_ = lean_ctor_get(v_fst_2951_, 0);
lean_inc(v_val_2952_);
lean_dec_ref(v_fst_2951_);
v___y_2902_ = v_val_2952_;
goto v___jp_2901_;
}
}
}
v___jp_2901_:
{
if (lean_obj_tag(v___y_2902_) == 0)
{
lean_object* v___x_2903_; 
v___x_2903_ = lean_box(0);
return v___x_2903_;
}
else
{
lean_object* v_val_2904_; lean_object* v___x_2906_; uint8_t v_isShared_2907_; uint8_t v_isSharedCheck_2912_; 
v_val_2904_ = lean_ctor_get(v___y_2902_, 0);
v_isSharedCheck_2912_ = !lean_is_exclusive(v___y_2902_);
if (v_isSharedCheck_2912_ == 0)
{
v___x_2906_ = v___y_2902_;
v_isShared_2907_ = v_isSharedCheck_2912_;
goto v_resetjp_2905_;
}
else
{
lean_inc(v_val_2904_);
lean_dec(v___y_2902_);
v___x_2906_ = lean_box(0);
v_isShared_2907_ = v_isSharedCheck_2912_;
goto v_resetjp_2905_;
}
v_resetjp_2905_:
{
lean_object* v_snd_2908_; lean_object* v___x_2910_; 
v_snd_2908_ = lean_ctor_get(v_val_2904_, 1);
lean_inc(v_snd_2908_);
lean_dec(v_val_2904_);
if (v_isShared_2907_ == 0)
{
lean_ctor_set(v___x_2906_, 0, v_snd_2908_);
v___x_2910_ = v___x_2906_;
goto v_reusejp_2909_;
}
else
{
lean_object* v_reuseFailAlloc_2911_; 
v_reuseFailAlloc_2911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2911_, 0, v_snd_2908_);
v___x_2910_ = v_reuseFailAlloc_2911_;
goto v_reusejp_2909_;
}
v_reusejp_2909_:
{
return v___x_2910_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParam_x3f___redArg___boxed(lean_object* v_inst_2953_, lean_object* v_attr_2954_, lean_object* v_env_2955_, lean_object* v_decl_2956_){
_start:
{
lean_object* v_res_2957_; 
v_res_2957_ = l_Lean_ParametricAttribute_getParam_x3f___redArg(v_inst_2953_, v_attr_2954_, v_env_2955_, v_decl_2956_);
lean_dec_ref(v_attr_2954_);
return v_res_2957_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParam_x3f(lean_object* v_00_u03b1_2958_, lean_object* v_inst_2959_, lean_object* v_attr_2960_, lean_object* v_env_2961_, lean_object* v_decl_2962_){
_start:
{
lean_object* v___x_2963_; 
v___x_2963_ = l_Lean_ParametricAttribute_getParam_x3f___redArg(v_inst_2959_, v_attr_2960_, v_env_2961_, v_decl_2962_);
return v___x_2963_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParam_x3f___boxed(lean_object* v_00_u03b1_2964_, lean_object* v_inst_2965_, lean_object* v_attr_2966_, lean_object* v_env_2967_, lean_object* v_decl_2968_){
_start:
{
lean_object* v_res_2969_; 
v_res_2969_ = l_Lean_ParametricAttribute_getParam_x3f(v_00_u03b1_2964_, v_inst_2965_, v_attr_2966_, v_env_2967_, v_decl_2968_);
lean_dec_ref(v_attr_2966_);
return v_res_2969_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_setParam___redArg(lean_object* v_attr_2974_, lean_object* v_env_2975_, lean_object* v_decl_2976_, lean_object* v_param_2977_){
_start:
{
lean_object* v___x_2978_; 
v___x_2978_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2975_, v_decl_2976_);
if (lean_obj_tag(v___x_2978_) == 0)
{
lean_object* v_ext_2979_; lean_object* v_toEnvExtension_2980_; lean_object* v_attr_2981_; lean_object* v_asyncMode_2982_; lean_object* v___x_2983_; lean_object* v___x_2984_; lean_object* v___x_2985_; lean_object* v_snd_2986_; lean_object* v___x_2988_; uint8_t v_isShared_2989_; uint8_t v_isSharedCheck_3016_; 
v_ext_2979_ = lean_ctor_get(v_attr_2974_, 1);
lean_inc_ref(v_ext_2979_);
v_toEnvExtension_2980_ = lean_ctor_get(v_ext_2979_, 0);
v_attr_2981_ = lean_ctor_get(v_attr_2974_, 0);
lean_inc_ref(v_attr_2981_);
lean_dec_ref(v_attr_2974_);
v_asyncMode_2982_ = lean_ctor_get(v_toEnvExtension_2980_, 2);
lean_inc(v_asyncMode_2982_);
v___x_2983_ = ((lean_object*)(l_Lean_ParametricAttribute_getParam_x3f___redArg___closed__0));
v___x_2984_ = lean_box(0);
lean_inc_ref(v_env_2975_);
v___x_2985_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2983_, v_ext_2979_, v_env_2975_, v_asyncMode_2982_, v___x_2984_);
v_snd_2986_ = lean_ctor_get(v___x_2985_, 1);
v_isSharedCheck_3016_ = !lean_is_exclusive(v___x_2985_);
if (v_isSharedCheck_3016_ == 0)
{
lean_object* v_unused_3017_; 
v_unused_3017_ = lean_ctor_get(v___x_2985_, 0);
lean_dec(v_unused_3017_);
v___x_2988_ = v___x_2985_;
v_isShared_2989_ = v_isSharedCheck_3016_;
goto v_resetjp_2987_;
}
else
{
lean_inc(v_snd_2986_);
lean_dec(v___x_2985_);
v___x_2988_ = lean_box(0);
v_isShared_2989_ = v_isSharedCheck_3016_;
goto v_resetjp_2987_;
}
v_resetjp_2987_:
{
lean_object* v___x_2990_; 
v___x_2990_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_snd_2986_, v_decl_2976_);
lean_dec(v_snd_2986_);
if (lean_obj_tag(v___x_2990_) == 0)
{
lean_object* v___x_2992_; 
lean_dec_ref(v_attr_2981_);
if (v_isShared_2989_ == 0)
{
lean_ctor_set(v___x_2988_, 1, v_param_2977_);
lean_ctor_set(v___x_2988_, 0, v_decl_2976_);
v___x_2992_ = v___x_2988_;
goto v_reusejp_2991_;
}
else
{
lean_object* v_reuseFailAlloc_2995_; 
v_reuseFailAlloc_2995_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2995_, 0, v_decl_2976_);
lean_ctor_set(v_reuseFailAlloc_2995_, 1, v_param_2977_);
v___x_2992_ = v_reuseFailAlloc_2995_;
goto v_reusejp_2991_;
}
v_reusejp_2991_:
{
lean_object* v___x_2993_; lean_object* v___x_2994_; 
v___x_2993_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_ext_2979_, v_env_2975_, v___x_2992_, v_asyncMode_2982_, v___x_2984_);
lean_dec(v_asyncMode_2982_);
v___x_2994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2994_, 0, v___x_2993_);
return v___x_2994_;
}
}
else
{
lean_object* v___x_2997_; uint8_t v_isShared_2998_; uint8_t v_isSharedCheck_3014_; 
lean_del_object(v___x_2988_);
lean_dec(v_asyncMode_2982_);
lean_dec_ref(v_ext_2979_);
lean_dec(v_param_2977_);
lean_dec_ref(v_env_2975_);
v_isSharedCheck_3014_ = !lean_is_exclusive(v___x_2990_);
if (v_isSharedCheck_3014_ == 0)
{
lean_object* v_unused_3015_; 
v_unused_3015_ = lean_ctor_get(v___x_2990_, 0);
lean_dec(v_unused_3015_);
v___x_2997_ = v___x_2990_;
v_isShared_2998_ = v_isSharedCheck_3014_;
goto v_resetjp_2996_;
}
else
{
lean_dec(v___x_2990_);
v___x_2997_ = lean_box(0);
v_isShared_2998_ = v_isSharedCheck_3014_;
goto v_resetjp_2996_;
}
v_resetjp_2996_:
{
lean_object* v_toAttributeImplCore_2999_; lean_object* v_name_3000_; uint8_t v___x_3001_; lean_object* v___x_3002_; lean_object* v___x_3003_; lean_object* v___x_3004_; lean_object* v___x_3005_; lean_object* v___x_3006_; lean_object* v___x_3007_; lean_object* v___x_3008_; lean_object* v___x_3009_; lean_object* v___x_3010_; lean_object* v___x_3012_; 
v_toAttributeImplCore_2999_ = lean_ctor_get(v_attr_2981_, 0);
lean_inc_ref(v_toAttributeImplCore_2999_);
lean_dec_ref(v_attr_2981_);
v_name_3000_ = lean_ctor_get(v_toAttributeImplCore_2999_, 1);
lean_inc(v_name_3000_);
lean_dec_ref(v_toAttributeImplCore_2999_);
v___x_3001_ = 1;
v___x_3002_ = ((lean_object*)(l_Lean_ParametricAttribute_setParam___redArg___closed__0));
v___x_3003_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_3000_, v___x_3001_);
v___x_3004_ = lean_string_append(v___x_3002_, v___x_3003_);
lean_dec_ref(v___x_3003_);
v___x_3005_ = ((lean_object*)(l_Lean_ParametricAttribute_setParam___redArg___closed__1));
v___x_3006_ = lean_string_append(v___x_3004_, v___x_3005_);
v___x_3007_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_decl_2976_, v___x_3001_);
v___x_3008_ = lean_string_append(v___x_3006_, v___x_3007_);
lean_dec_ref(v___x_3007_);
v___x_3009_ = ((lean_object*)(l_Lean_ParametricAttribute_setParam___redArg___closed__2));
v___x_3010_ = lean_string_append(v___x_3008_, v___x_3009_);
if (v_isShared_2998_ == 0)
{
lean_ctor_set_tag(v___x_2997_, 0);
lean_ctor_set(v___x_2997_, 0, v___x_3010_);
v___x_3012_ = v___x_2997_;
goto v_reusejp_3011_;
}
else
{
lean_object* v_reuseFailAlloc_3013_; 
v_reuseFailAlloc_3013_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3013_, 0, v___x_3010_);
v___x_3012_ = v_reuseFailAlloc_3013_;
goto v_reusejp_3011_;
}
v_reusejp_3011_:
{
return v___x_3012_;
}
}
}
}
}
else
{
lean_object* v___x_3019_; uint8_t v_isShared_3020_; uint8_t v_isSharedCheck_3037_; 
lean_dec(v_param_2977_);
lean_dec_ref(v_env_2975_);
v_isSharedCheck_3037_ = !lean_is_exclusive(v___x_2978_);
if (v_isSharedCheck_3037_ == 0)
{
lean_object* v_unused_3038_; 
v_unused_3038_ = lean_ctor_get(v___x_2978_, 0);
lean_dec(v_unused_3038_);
v___x_3019_ = v___x_2978_;
v_isShared_3020_ = v_isSharedCheck_3037_;
goto v_resetjp_3018_;
}
else
{
lean_dec(v___x_2978_);
v___x_3019_ = lean_box(0);
v_isShared_3020_ = v_isSharedCheck_3037_;
goto v_resetjp_3018_;
}
v_resetjp_3018_:
{
lean_object* v_attr_3021_; lean_object* v_toAttributeImplCore_3022_; lean_object* v_name_3023_; uint8_t v___x_3024_; lean_object* v___x_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; lean_object* v___x_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; lean_object* v___x_3031_; lean_object* v___x_3032_; lean_object* v___x_3033_; lean_object* v___x_3035_; 
v_attr_3021_ = lean_ctor_get(v_attr_2974_, 0);
lean_inc_ref(v_attr_3021_);
lean_dec_ref(v_attr_2974_);
v_toAttributeImplCore_3022_ = lean_ctor_get(v_attr_3021_, 0);
lean_inc_ref(v_toAttributeImplCore_3022_);
lean_dec_ref(v_attr_3021_);
v_name_3023_ = lean_ctor_get(v_toAttributeImplCore_3022_, 1);
lean_inc(v_name_3023_);
lean_dec_ref(v_toAttributeImplCore_3022_);
v___x_3024_ = 1;
v___x_3025_ = ((lean_object*)(l_Lean_ParametricAttribute_setParam___redArg___closed__0));
v___x_3026_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_3023_, v___x_3024_);
v___x_3027_ = lean_string_append(v___x_3025_, v___x_3026_);
lean_dec_ref(v___x_3026_);
v___x_3028_ = ((lean_object*)(l_Lean_ParametricAttribute_setParam___redArg___closed__1));
v___x_3029_ = lean_string_append(v___x_3027_, v___x_3028_);
v___x_3030_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_decl_2976_, v___x_3024_);
v___x_3031_ = lean_string_append(v___x_3029_, v___x_3030_);
lean_dec_ref(v___x_3030_);
v___x_3032_ = ((lean_object*)(l_Lean_ParametricAttribute_setParam___redArg___closed__3));
v___x_3033_ = lean_string_append(v___x_3031_, v___x_3032_);
if (v_isShared_3020_ == 0)
{
lean_ctor_set_tag(v___x_3019_, 0);
lean_ctor_set(v___x_3019_, 0, v___x_3033_);
v___x_3035_ = v___x_3019_;
goto v_reusejp_3034_;
}
else
{
lean_object* v_reuseFailAlloc_3036_; 
v_reuseFailAlloc_3036_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3036_, 0, v___x_3033_);
v___x_3035_ = v_reuseFailAlloc_3036_;
goto v_reusejp_3034_;
}
v_reusejp_3034_:
{
return v___x_3035_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_setParam(lean_object* v_00_u03b1_3039_, lean_object* v_attr_3040_, lean_object* v_env_3041_, lean_object* v_decl_3042_, lean_object* v_param_3043_){
_start:
{
lean_object* v___x_3044_; 
v___x_3044_ = l_Lean_ParametricAttribute_setParam___redArg(v_attr_3040_, v_env_3041_, v_decl_3042_, v_param_3043_);
return v___x_3044_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___lam__0(lean_object* v_x_3045_, lean_object* v___y_3046_){
_start:
{
lean_object* v___x_3048_; lean_object* v___x_3049_; 
v___x_3048_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___lam__0___closed__1));
v___x_3049_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3049_, 0, v___x_3048_);
return v___x_3049_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___lam__0___boxed(lean_object* v_x_3050_, lean_object* v___y_3051_, lean_object* v___y_3052_){
_start:
{
lean_object* v_res_3053_; 
v_res_3053_ = l_Lean_instInhabitedEnumAttributes_default___lam__0(v_x_3050_, v___y_3051_);
lean_dec_ref(v___y_3051_);
lean_dec_ref(v_x_3050_);
return v_res_3053_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___lam__1(lean_object* v_s_3054_, lean_object* v_x_3055_){
_start:
{
lean_inc(v_s_3054_);
return v_s_3054_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___lam__1___boxed(lean_object* v_s_3056_, lean_object* v_x_3057_){
_start:
{
lean_object* v_res_3058_; 
v_res_3058_ = l_Lean_instInhabitedEnumAttributes_default___lam__1(v_s_3056_, v_x_3057_);
lean_dec_ref(v_x_3057_);
lean_dec(v_s_3056_);
return v_res_3058_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___lam__2(lean_object* v_x_3059_, lean_object* v_x_3060_, uint8_t v_x_3061_){
_start:
{
lean_object* v___x_3062_; 
v___x_3062_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___lam__2___closed__0));
return v___x_3062_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___lam__2___boxed(lean_object* v_x_3063_, lean_object* v_x_3064_, lean_object* v_x_3065_){
_start:
{
uint8_t v_x_72__boxed_3066_; lean_object* v_res_3067_; 
v_x_72__boxed_3066_ = lean_unbox(v_x_3065_);
v_res_3067_ = l_Lean_instInhabitedEnumAttributes_default___lam__2(v_x_3063_, v_x_3064_, v_x_72__boxed_3066_);
lean_dec(v_x_3064_);
lean_dec_ref(v_x_3063_);
return v_res_3067_;
}
}
static lean_object* _init_l_Lean_instInhabitedEnumAttributes_default___closed__3(void){
_start:
{
lean_object* v___x_3071_; 
v___x_3071_ = l_Lean_instInhabitedEnvExtension_default(lean_box(0));
return v___x_3071_;
}
}
static lean_object* _init_l_Lean_instInhabitedEnumAttributes_default___closed__4(void){
_start:
{
lean_object* v___f_3072_; lean_object* v___f_3073_; lean_object* v___f_3074_; lean_object* v___f_3075_; lean_object* v___x_3076_; lean_object* v___x_3077_; lean_object* v___x_3078_; 
v___f_3072_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___closed__3));
v___f_3073_ = ((lean_object*)(l_Lean_instInhabitedEnumAttributes_default___closed__2));
v___f_3074_ = ((lean_object*)(l_Lean_instInhabitedEnumAttributes_default___closed__1));
v___f_3075_ = ((lean_object*)(l_Lean_instInhabitedEnumAttributes_default___closed__0));
v___x_3076_ = lean_box(0);
v___x_3077_ = lean_obj_once(&l_Lean_instInhabitedEnumAttributes_default___closed__3, &l_Lean_instInhabitedEnumAttributes_default___closed__3_once, _init_l_Lean_instInhabitedEnumAttributes_default___closed__3);
v___x_3078_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3078_, 0, v___x_3077_);
lean_ctor_set(v___x_3078_, 1, v___x_3076_);
lean_ctor_set(v___x_3078_, 2, v___f_3075_);
lean_ctor_set(v___x_3078_, 3, v___f_3074_);
lean_ctor_set(v___x_3078_, 4, v___f_3073_);
lean_ctor_set(v___x_3078_, 5, v___f_3072_);
return v___x_3078_;
}
}
static lean_object* _init_l_Lean_instInhabitedEnumAttributes_default___closed__5(void){
_start:
{
lean_object* v___x_3079_; lean_object* v___x_3080_; lean_object* v___x_3081_; 
v___x_3079_ = lean_obj_once(&l_Lean_instInhabitedEnumAttributes_default___closed__4, &l_Lean_instInhabitedEnumAttributes_default___closed__4_once, _init_l_Lean_instInhabitedEnumAttributes_default___closed__4);
v___x_3080_ = lean_box(0);
v___x_3081_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3081_, 0, v___x_3080_);
lean_ctor_set(v___x_3081_, 1, v___x_3079_);
return v___x_3081_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default(lean_object* v_a_3082_){
_start:
{
lean_object* v___x_3083_; 
v___x_3083_ = lean_obj_once(&l_Lean_instInhabitedEnumAttributes_default___closed__5, &l_Lean_instInhabitedEnumAttributes_default___closed__5_once, _init_l_Lean_instInhabitedEnumAttributes_default___closed__5);
return v___x_3083_;
}
}
static lean_object* _init_l_Lean_instInhabitedEnumAttributes___closed__0(void){
_start:
{
lean_object* v___x_3084_; 
v___x_3084_ = l_Lean_instInhabitedEnumAttributes_default(lean_box(0));
return v___x_3084_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes(lean_object* v_a_3085_){
_start:
{
lean_object* v___x_3086_; 
v___x_3086_ = lean_obj_once(&l_Lean_instInhabitedEnumAttributes___closed__0, &l_Lean_instInhabitedEnumAttributes___closed__0_once, _init_l_Lean_instInhabitedEnumAttributes___closed__0);
return v___x_3086_;
}
}
static lean_object* _init_l_Lean_registerEnumAttributes___auto__1(void){
_start:
{
lean_object* v___x_3087_; 
v___x_3087_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__28, &l_Lean_AttributeImplCore_ref___autoParam___closed__28_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__28);
return v___x_3087_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__0(lean_object* v_x_3088_){
_start:
{
lean_object* v___x_3089_; 
v___x_3089_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___lam__2___closed__0));
return v___x_3089_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__0___boxed(lean_object* v_x_3090_){
_start:
{
lean_object* v_res_3091_; 
v_res_3091_ = l_Lean_registerEnumAttributes___redArg___lam__0(v_x_3090_);
lean_dec(v_x_3090_);
return v_res_3091_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___redArg(lean_object* v_newState_3092_, lean_object* v_x_3093_, lean_object* v_x_3094_){
_start:
{
if (lean_obj_tag(v_x_3094_) == 0)
{
return v_x_3093_;
}
else
{
lean_object* v_head_3095_; lean_object* v_tail_3096_; lean_object* v___x_3097_; 
v_head_3095_ = lean_ctor_get(v_x_3094_, 0);
lean_inc(v_head_3095_);
v_tail_3096_ = lean_ctor_get(v_x_3094_, 1);
lean_inc(v_tail_3096_);
lean_dec_ref(v_x_3094_);
v___x_3097_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_newState_3092_, v_head_3095_);
if (lean_obj_tag(v___x_3097_) == 1)
{
lean_object* v_val_3098_; lean_object* v___x_3099_; 
v_val_3098_ = lean_ctor_get(v___x_3097_, 0);
lean_inc(v_val_3098_);
lean_dec_ref(v___x_3097_);
v___x_3099_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_head_3095_, v_val_3098_, v_x_3093_);
v_x_3093_ = v___x_3099_;
v_x_3094_ = v_tail_3096_;
goto _start;
}
else
{
lean_dec(v___x_3097_);
lean_dec(v_head_3095_);
v_x_3094_ = v_tail_3096_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___redArg___boxed(lean_object* v_newState_3102_, lean_object* v_x_3103_, lean_object* v_x_3104_){
_start:
{
lean_object* v_res_3105_; 
v_res_3105_ = l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___redArg(v_newState_3102_, v_x_3103_, v_x_3104_);
lean_dec(v_newState_3102_);
return v_res_3105_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__1(lean_object* v_x_3106_, lean_object* v_newState_3107_, lean_object* v_consts_3108_, lean_object* v_st_3109_){
_start:
{
lean_object* v___x_3110_; 
v___x_3110_ = l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___redArg(v_newState_3107_, v_st_3109_, v_consts_3108_);
return v___x_3110_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__1___boxed(lean_object* v_x_3111_, lean_object* v_newState_3112_, lean_object* v_consts_3113_, lean_object* v_st_3114_){
_start:
{
lean_object* v_res_3115_; 
v_res_3115_ = l_Lean_registerEnumAttributes___redArg___lam__1(v_x_3111_, v_newState_3112_, v_consts_3113_, v_st_3114_);
lean_dec(v_newState_3112_);
lean_dec(v_x_3111_);
return v_res_3115_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__2(lean_object* v_s_3125_){
_start:
{
lean_object* v___x_3126_; lean_object* v___y_3128_; 
v___x_3126_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___lam__2___closed__3));
if (lean_obj_tag(v_s_3125_) == 0)
{
lean_object* v_size_3132_; 
v_size_3132_ = lean_ctor_get(v_s_3125_, 0);
lean_inc(v_size_3132_);
lean_dec_ref(v_s_3125_);
v___y_3128_ = v_size_3132_;
goto v___jp_3127_;
}
else
{
lean_object* v___x_3133_; 
v___x_3133_ = lean_unsigned_to_nat(0u);
v___y_3128_ = v___x_3133_;
goto v___jp_3127_;
}
v___jp_3127_:
{
lean_object* v___x_3129_; lean_object* v___x_3130_; lean_object* v___x_3131_; 
v___x_3129_ = l_Nat_reprFast(v___y_3128_);
v___x_3130_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3130_, 0, v___x_3129_);
v___x_3131_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3131_, 0, v___x_3126_);
lean_ctor_set(v___x_3131_, 1, v___x_3130_);
return v___x_3131_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg(lean_object* v_env_3134_, lean_object* v_as_3135_, size_t v_i_3136_, size_t v_stop_3137_, lean_object* v_b_3138_){
_start:
{
lean_object* v___y_3140_; uint8_t v___x_3144_; 
v___x_3144_ = lean_usize_dec_eq(v_i_3136_, v_stop_3137_);
if (v___x_3144_ == 0)
{
lean_object* v___x_3145_; lean_object* v_fst_3146_; uint8_t v___x_3147_; 
v___x_3145_ = lean_array_uget_borrowed(v_as_3135_, v_i_3136_);
v_fst_3146_ = lean_ctor_get(v___x_3145_, 0);
lean_inc(v_fst_3146_);
lean_inc_ref(v_env_3134_);
v___x_3147_ = l_Lean_Environment_contains(v_env_3134_, v_fst_3146_, v___x_3144_);
if (v___x_3147_ == 0)
{
v___y_3140_ = v_b_3138_;
goto v___jp_3139_;
}
else
{
lean_object* v___x_3148_; 
lean_inc(v___x_3145_);
v___x_3148_ = lean_array_push(v_b_3138_, v___x_3145_);
v___y_3140_ = v___x_3148_;
goto v___jp_3139_;
}
}
else
{
lean_dec_ref(v_env_3134_);
return v_b_3138_;
}
v___jp_3139_:
{
size_t v___x_3141_; size_t v___x_3142_; 
v___x_3141_ = ((size_t)1ULL);
v___x_3142_ = lean_usize_add(v_i_3136_, v___x_3141_);
v_i_3136_ = v___x_3142_;
v_b_3138_ = v___y_3140_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg___boxed(lean_object* v_env_3149_, lean_object* v_as_3150_, lean_object* v_i_3151_, lean_object* v_stop_3152_, lean_object* v_b_3153_){
_start:
{
size_t v_i_boxed_3154_; size_t v_stop_boxed_3155_; lean_object* v_res_3156_; 
v_i_boxed_3154_ = lean_unbox_usize(v_i_3151_);
lean_dec(v_i_3151_);
v_stop_boxed_3155_ = lean_unbox_usize(v_stop_3152_);
lean_dec(v_stop_3152_);
v_res_3156_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg(v_env_3149_, v_as_3150_, v_i_boxed_3154_, v_stop_boxed_3155_, v_b_3153_);
lean_dec_ref(v_as_3150_);
return v_res_3156_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__3(lean_object* v_env_3157_, lean_object* v_m_3158_, uint8_t v_x_3159_){
_start:
{
lean_object* v___y_3161_; lean_object* v___y_3162_; lean_object* v___y_3163_; lean_object* v___x_3167_; lean_object* v___y_3169_; lean_object* v___x_3175_; lean_object* v_r_3176_; lean_object* v___x_3177_; uint8_t v___x_3178_; 
v___x_3167_ = lean_unsigned_to_nat(0u);
v___x_3175_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___lam__2___closed__0));
v_r_3176_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1_spec__1___redArg(v___x_3175_, v_m_3158_);
v___x_3177_ = lean_array_get_size(v_r_3176_);
v___x_3178_ = lean_nat_dec_lt(v___x_3167_, v___x_3177_);
if (v___x_3178_ == 0)
{
lean_dec_ref(v_r_3176_);
lean_dec_ref(v_env_3157_);
v___y_3169_ = v___x_3175_;
goto v___jp_3168_;
}
else
{
uint8_t v___x_3179_; 
v___x_3179_ = lean_nat_dec_le(v___x_3177_, v___x_3177_);
if (v___x_3179_ == 0)
{
if (v___x_3178_ == 0)
{
lean_dec_ref(v_r_3176_);
lean_dec_ref(v_env_3157_);
v___y_3169_ = v___x_3175_;
goto v___jp_3168_;
}
else
{
size_t v___x_3180_; size_t v___x_3181_; lean_object* v___x_3182_; 
v___x_3180_ = ((size_t)0ULL);
v___x_3181_ = lean_usize_of_nat(v___x_3177_);
v___x_3182_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg(v_env_3157_, v_r_3176_, v___x_3180_, v___x_3181_, v___x_3175_);
lean_dec_ref(v_r_3176_);
v___y_3169_ = v___x_3182_;
goto v___jp_3168_;
}
}
else
{
size_t v___x_3183_; size_t v___x_3184_; lean_object* v___x_3185_; 
v___x_3183_ = ((size_t)0ULL);
v___x_3184_ = lean_usize_of_nat(v___x_3177_);
v___x_3185_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg(v_env_3157_, v_r_3176_, v___x_3183_, v___x_3184_, v___x_3175_);
lean_dec_ref(v_r_3176_);
v___y_3169_ = v___x_3185_;
goto v___jp_3168_;
}
}
v___jp_3160_:
{
uint8_t v___x_3164_; 
v___x_3164_ = lean_nat_dec_le(v___y_3163_, v___y_3162_);
if (v___x_3164_ == 0)
{
lean_object* v___x_3165_; 
lean_dec(v___y_3162_);
lean_inc(v___y_3163_);
v___x_3165_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2___redArg(v___y_3161_, v___y_3163_, v___y_3163_);
lean_dec(v___y_3163_);
return v___x_3165_;
}
else
{
lean_object* v___x_3166_; 
v___x_3166_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2___redArg(v___y_3161_, v___y_3163_, v___y_3162_);
lean_dec(v___y_3162_);
return v___x_3166_;
}
}
v___jp_3168_:
{
lean_object* v___x_3170_; uint8_t v___x_3171_; 
v___x_3170_ = lean_array_get_size(v___y_3169_);
v___x_3171_ = lean_nat_dec_eq(v___x_3170_, v___x_3167_);
if (v___x_3171_ == 0)
{
lean_object* v___x_3172_; lean_object* v___x_3173_; uint8_t v___x_3174_; 
v___x_3172_ = lean_unsigned_to_nat(1u);
v___x_3173_ = lean_nat_sub(v___x_3170_, v___x_3172_);
v___x_3174_ = lean_nat_dec_le(v___x_3167_, v___x_3173_);
if (v___x_3174_ == 0)
{
lean_inc(v___x_3173_);
v___y_3161_ = v___y_3169_;
v___y_3162_ = v___x_3173_;
v___y_3163_ = v___x_3173_;
goto v___jp_3160_;
}
else
{
v___y_3161_ = v___y_3169_;
v___y_3162_ = v___x_3173_;
v___y_3163_ = v___x_3167_;
goto v___jp_3160_;
}
}
else
{
return v___y_3169_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__3___boxed(lean_object* v_env_3186_, lean_object* v_m_3187_, lean_object* v_x_3188_){
_start:
{
uint8_t v_x_2358__boxed_3189_; lean_object* v_res_3190_; 
v_x_2358__boxed_3189_ = lean_unbox(v_x_3188_);
v_res_3190_ = l_Lean_registerEnumAttributes___redArg___lam__3(v_env_3186_, v_m_3187_, v_x_2358__boxed_3189_);
lean_dec(v_m_3187_);
return v_res_3190_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__4(lean_object* v_s_3191_, lean_object* v_p_3192_){
_start:
{
lean_object* v_fst_3193_; lean_object* v_snd_3194_; lean_object* v___x_3195_; 
v_fst_3193_ = lean_ctor_get(v_p_3192_, 0);
lean_inc(v_fst_3193_);
v_snd_3194_ = lean_ctor_get(v_p_3192_, 1);
lean_inc(v_snd_3194_);
lean_dec_ref(v_p_3192_);
v___x_3195_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_3193_, v_snd_3194_, v_s_3191_);
return v___x_3195_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__5(lean_object* v___x_3196_, lean_object* v_x_3197_, lean_object* v_x_3198_){
_start:
{
lean_object* v___x_3200_; 
v___x_3200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3200_, 0, v___x_3196_);
return v___x_3200_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__5___boxed(lean_object* v___x_3201_, lean_object* v_x_3202_, lean_object* v_x_3203_, lean_object* v___y_3204_){
_start:
{
lean_object* v_res_3205_; 
v_res_3205_ = l_Lean_registerEnumAttributes___redArg___lam__5(v___x_3201_, v_x_3202_, v_x_3203_);
lean_dec_ref(v_x_3203_);
lean_dec_ref(v_x_3202_);
return v_res_3205_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_registerEnumAttributes_spec__3(lean_object* v_as_3206_){
_start:
{
if (lean_obj_tag(v_as_3206_) == 0)
{
lean_object* v___x_3208_; lean_object* v___x_3209_; 
v___x_3208_ = lean_box(0);
v___x_3209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3209_, 0, v___x_3208_);
return v___x_3209_;
}
else
{
lean_object* v_head_3210_; lean_object* v_tail_3211_; lean_object* v___x_3212_; 
v_head_3210_ = lean_ctor_get(v_as_3206_, 0);
lean_inc(v_head_3210_);
v_tail_3211_ = lean_ctor_get(v_as_3206_, 1);
lean_inc(v_tail_3211_);
lean_dec_ref(v_as_3206_);
v___x_3212_ = l_Lean_registerBuiltinAttribute(v_head_3210_);
if (lean_obj_tag(v___x_3212_) == 0)
{
lean_dec_ref(v___x_3212_);
v_as_3206_ = v_tail_3211_;
goto _start;
}
else
{
lean_dec(v_tail_3211_);
return v___x_3212_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_registerEnumAttributes_spec__3___boxed(lean_object* v_as_3214_, lean_object* v___y_3215_){
_start:
{
lean_object* v_res_3216_; 
v_res_3216_ = l_List_forM___at___00Lean_registerEnumAttributes_spec__3(v_as_3214_);
return v_res_3216_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__1(lean_object* v_validate_3217_, lean_object* v_snd_3218_, lean_object* v_a_3219_, lean_object* v_fst_3220_, lean_object* v_decl_3221_, lean_object* v_stx_3222_, uint8_t v_kind_3223_, lean_object* v___y_3224_, lean_object* v___y_3225_){
_start:
{
lean_object* v___y_3228_; lean_object* v___y_3229_; lean_object* v___y_3264_; lean_object* v___y_3265_; lean_object* v___x_3270_; 
lean_inc_ref(v___y_3224_);
v___x_3270_ = l_Lean_Attribute_Builtin_ensureNoArgs(v_stx_3222_, v___y_3224_, v___y_3225_);
if (lean_obj_tag(v___x_3270_) == 0)
{
uint8_t v___x_3271_; uint8_t v___x_3272_; 
lean_dec_ref(v___x_3270_);
v___x_3271_ = 0;
v___x_3272_ = l_Lean_instBEqAttributeKind_beq(v_kind_3223_, v___x_3271_);
if (v___x_3272_ == 0)
{
lean_object* v___x_3273_; 
lean_dec(v_decl_3221_);
lean_dec_ref(v_a_3219_);
lean_dec(v_snd_3218_);
lean_dec_ref(v_validate_3217_);
v___x_3273_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg(v_fst_3220_, v_kind_3223_, v___y_3224_, v___y_3225_);
lean_dec(v___y_3225_);
lean_dec_ref(v___y_3224_);
return v___x_3273_;
}
else
{
v___y_3264_ = v___y_3224_;
v___y_3265_ = v___y_3225_;
goto v___jp_3263_;
}
}
else
{
lean_dec(v___y_3225_);
lean_dec_ref(v___y_3224_);
lean_dec(v_decl_3221_);
lean_dec(v_fst_3220_);
lean_dec_ref(v_a_3219_);
lean_dec(v_snd_3218_);
lean_dec_ref(v_validate_3217_);
return v___x_3270_;
}
v___jp_3227_:
{
lean_object* v___x_3230_; 
lean_inc(v___y_3229_);
lean_inc(v_snd_3218_);
lean_inc(v_decl_3221_);
v___x_3230_ = lean_apply_5(v_validate_3217_, v_decl_3221_, v_snd_3218_, v___y_3228_, v___y_3229_, lean_box(0));
if (lean_obj_tag(v___x_3230_) == 0)
{
lean_object* v___x_3232_; uint8_t v_isShared_3233_; uint8_t v_isSharedCheck_3261_; 
v_isSharedCheck_3261_ = !lean_is_exclusive(v___x_3230_);
if (v_isSharedCheck_3261_ == 0)
{
lean_object* v_unused_3262_; 
v_unused_3262_ = lean_ctor_get(v___x_3230_, 0);
lean_dec(v_unused_3262_);
v___x_3232_ = v___x_3230_;
v_isShared_3233_ = v_isSharedCheck_3261_;
goto v_resetjp_3231_;
}
else
{
lean_dec(v___x_3230_);
v___x_3232_ = lean_box(0);
v_isShared_3233_ = v_isSharedCheck_3261_;
goto v_resetjp_3231_;
}
v_resetjp_3231_:
{
lean_object* v___x_3234_; lean_object* v_toEnvExtension_3235_; lean_object* v_env_3236_; lean_object* v_nextMacroScope_3237_; lean_object* v_ngen_3238_; lean_object* v_auxDeclNGen_3239_; lean_object* v_traceState_3240_; lean_object* v_messages_3241_; lean_object* v_infoState_3242_; lean_object* v_snapshotTasks_3243_; lean_object* v___x_3245_; uint8_t v_isShared_3246_; uint8_t v_isSharedCheck_3259_; 
v___x_3234_ = lean_st_ref_take(v___y_3229_);
v_toEnvExtension_3235_ = lean_ctor_get(v_a_3219_, 0);
v_env_3236_ = lean_ctor_get(v___x_3234_, 0);
v_nextMacroScope_3237_ = lean_ctor_get(v___x_3234_, 1);
v_ngen_3238_ = lean_ctor_get(v___x_3234_, 2);
v_auxDeclNGen_3239_ = lean_ctor_get(v___x_3234_, 3);
v_traceState_3240_ = lean_ctor_get(v___x_3234_, 4);
v_messages_3241_ = lean_ctor_get(v___x_3234_, 6);
v_infoState_3242_ = lean_ctor_get(v___x_3234_, 7);
v_snapshotTasks_3243_ = lean_ctor_get(v___x_3234_, 8);
v_isSharedCheck_3259_ = !lean_is_exclusive(v___x_3234_);
if (v_isSharedCheck_3259_ == 0)
{
lean_object* v_unused_3260_; 
v_unused_3260_ = lean_ctor_get(v___x_3234_, 5);
lean_dec(v_unused_3260_);
v___x_3245_ = v___x_3234_;
v_isShared_3246_ = v_isSharedCheck_3259_;
goto v_resetjp_3244_;
}
else
{
lean_inc(v_snapshotTasks_3243_);
lean_inc(v_infoState_3242_);
lean_inc(v_messages_3241_);
lean_inc(v_traceState_3240_);
lean_inc(v_auxDeclNGen_3239_);
lean_inc(v_ngen_3238_);
lean_inc(v_nextMacroScope_3237_);
lean_inc(v_env_3236_);
lean_dec(v___x_3234_);
v___x_3245_ = lean_box(0);
v_isShared_3246_ = v_isSharedCheck_3259_;
goto v_resetjp_3244_;
}
v_resetjp_3244_:
{
lean_object* v_asyncMode_3247_; lean_object* v___x_3248_; lean_object* v___x_3249_; lean_object* v___x_3250_; lean_object* v___x_3252_; 
v_asyncMode_3247_ = lean_ctor_get(v_toEnvExtension_3235_, 2);
lean_inc(v_asyncMode_3247_);
lean_inc(v_decl_3221_);
v___x_3248_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3248_, 0, v_decl_3221_);
lean_ctor_set(v___x_3248_, 1, v_snd_3218_);
v___x_3249_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_a_3219_, v_env_3236_, v___x_3248_, v_asyncMode_3247_, v_decl_3221_);
lean_dec(v_asyncMode_3247_);
v___x_3250_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2);
if (v_isShared_3246_ == 0)
{
lean_ctor_set(v___x_3245_, 5, v___x_3250_);
lean_ctor_set(v___x_3245_, 0, v___x_3249_);
v___x_3252_ = v___x_3245_;
goto v_reusejp_3251_;
}
else
{
lean_object* v_reuseFailAlloc_3258_; 
v_reuseFailAlloc_3258_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3258_, 0, v___x_3249_);
lean_ctor_set(v_reuseFailAlloc_3258_, 1, v_nextMacroScope_3237_);
lean_ctor_set(v_reuseFailAlloc_3258_, 2, v_ngen_3238_);
lean_ctor_set(v_reuseFailAlloc_3258_, 3, v_auxDeclNGen_3239_);
lean_ctor_set(v_reuseFailAlloc_3258_, 4, v_traceState_3240_);
lean_ctor_set(v_reuseFailAlloc_3258_, 5, v___x_3250_);
lean_ctor_set(v_reuseFailAlloc_3258_, 6, v_messages_3241_);
lean_ctor_set(v_reuseFailAlloc_3258_, 7, v_infoState_3242_);
lean_ctor_set(v_reuseFailAlloc_3258_, 8, v_snapshotTasks_3243_);
v___x_3252_ = v_reuseFailAlloc_3258_;
goto v_reusejp_3251_;
}
v_reusejp_3251_:
{
lean_object* v___x_3253_; lean_object* v___x_3254_; lean_object* v___x_3256_; 
v___x_3253_ = lean_st_ref_set(v___y_3229_, v___x_3252_);
lean_dec(v___y_3229_);
v___x_3254_ = lean_box(0);
if (v_isShared_3233_ == 0)
{
lean_ctor_set(v___x_3232_, 0, v___x_3254_);
v___x_3256_ = v___x_3232_;
goto v_reusejp_3255_;
}
else
{
lean_object* v_reuseFailAlloc_3257_; 
v_reuseFailAlloc_3257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3257_, 0, v___x_3254_);
v___x_3256_ = v_reuseFailAlloc_3257_;
goto v_reusejp_3255_;
}
v_reusejp_3255_:
{
return v___x_3256_;
}
}
}
}
}
else
{
lean_dec(v___y_3229_);
lean_dec(v_decl_3221_);
lean_dec_ref(v_a_3219_);
lean_dec(v_snd_3218_);
return v___x_3230_;
}
}
v___jp_3263_:
{
lean_object* v___x_3266_; lean_object* v_env_3267_; lean_object* v___x_3268_; 
v___x_3266_ = lean_st_ref_get(v___y_3265_);
v_env_3267_ = lean_ctor_get(v___x_3266_, 0);
lean_inc_ref(v_env_3267_);
lean_dec(v___x_3266_);
v___x_3268_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3267_, v_decl_3221_);
lean_dec_ref(v_env_3267_);
if (lean_obj_tag(v___x_3268_) == 0)
{
lean_dec(v_fst_3220_);
v___y_3228_ = v___y_3264_;
v___y_3229_ = v___y_3265_;
goto v___jp_3227_;
}
else
{
lean_object* v___x_3269_; 
lean_dec_ref(v___x_3268_);
lean_dec_ref(v_a_3219_);
lean_dec(v_snd_3218_);
lean_dec_ref(v_validate_3217_);
v___x_3269_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg(v_fst_3220_, v_decl_3221_, v___y_3264_, v___y_3265_);
lean_dec(v___y_3265_);
lean_dec_ref(v___y_3264_);
return v___x_3269_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__1___boxed(lean_object* v_validate_3274_, lean_object* v_snd_3275_, lean_object* v_a_3276_, lean_object* v_fst_3277_, lean_object* v_decl_3278_, lean_object* v_stx_3279_, lean_object* v_kind_3280_, lean_object* v___y_3281_, lean_object* v___y_3282_, lean_object* v___y_3283_){
_start:
{
uint8_t v_kind_boxed_3284_; lean_object* v_res_3285_; 
v_kind_boxed_3284_ = lean_unbox(v_kind_3280_);
v_res_3285_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__1(v_validate_3274_, v_snd_3275_, v_a_3276_, v_fst_3277_, v_decl_3278_, v_stx_3279_, v_kind_boxed_3284_, v___y_3281_, v___y_3282_);
return v_res_3285_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__0(lean_object* v_fst_3286_, lean_object* v_decl_3287_, lean_object* v___y_3288_, lean_object* v___y_3289_){
_start:
{
lean_object* v___x_3291_; lean_object* v___x_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; 
v___x_3291_ = lean_obj_once(&l_Lean_registerTagAttribute___lam__6___closed__1, &l_Lean_registerTagAttribute___lam__6___closed__1_once, _init_l_Lean_registerTagAttribute___lam__6___closed__1);
v___x_3292_ = l_Lean_MessageData_ofName(v_fst_3286_);
v___x_3293_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3293_, 0, v___x_3291_);
lean_ctor_set(v___x_3293_, 1, v___x_3292_);
v___x_3294_ = lean_obj_once(&l_Lean_registerTagAttribute___lam__6___closed__3, &l_Lean_registerTagAttribute___lam__6___closed__3_once, _init_l_Lean_registerTagAttribute___lam__6___closed__3);
v___x_3295_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3295_, 0, v___x_3293_);
lean_ctor_set(v___x_3295_, 1, v___x_3294_);
v___x_3296_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0_spec__0___redArg(v___x_3295_, v___y_3288_, v___y_3289_);
return v___x_3296_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__0___boxed(lean_object* v_fst_3297_, lean_object* v_decl_3298_, lean_object* v___y_3299_, lean_object* v___y_3300_, lean_object* v___y_3301_){
_start:
{
lean_object* v_res_3302_; 
v_res_3302_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__0(v_fst_3297_, v_decl_3298_, v___y_3299_, v___y_3300_);
lean_dec(v___y_3300_);
lean_dec_ref(v___y_3299_);
lean_dec(v_decl_3298_);
return v_res_3302_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg(lean_object* v_validate_3303_, lean_object* v_a_3304_, lean_object* v_ref_3305_, uint8_t v_applicationTime_3306_, lean_object* v_a_3307_, lean_object* v_a_3308_){
_start:
{
if (lean_obj_tag(v_a_3307_) == 0)
{
lean_object* v___x_3309_; 
lean_dec(v_ref_3305_);
lean_dec_ref(v_a_3304_);
lean_dec_ref(v_validate_3303_);
v___x_3309_ = l_List_reverse___redArg(v_a_3308_);
return v___x_3309_;
}
else
{
lean_object* v_head_3310_; lean_object* v_snd_3311_; lean_object* v_tail_3312_; lean_object* v___x_3314_; uint8_t v_isShared_3315_; uint8_t v_isSharedCheck_3327_; 
v_head_3310_ = lean_ctor_get(v_a_3307_, 0);
lean_inc(v_head_3310_);
v_snd_3311_ = lean_ctor_get(v_head_3310_, 1);
lean_inc(v_snd_3311_);
v_tail_3312_ = lean_ctor_get(v_a_3307_, 1);
v_isSharedCheck_3327_ = !lean_is_exclusive(v_a_3307_);
if (v_isSharedCheck_3327_ == 0)
{
lean_object* v_unused_3328_; 
v_unused_3328_ = lean_ctor_get(v_a_3307_, 0);
lean_dec(v_unused_3328_);
v___x_3314_ = v_a_3307_;
v_isShared_3315_ = v_isSharedCheck_3327_;
goto v_resetjp_3313_;
}
else
{
lean_inc(v_tail_3312_);
lean_dec(v_a_3307_);
v___x_3314_ = lean_box(0);
v_isShared_3315_ = v_isSharedCheck_3327_;
goto v_resetjp_3313_;
}
v_resetjp_3313_:
{
lean_object* v_fst_3316_; lean_object* v_fst_3317_; lean_object* v_snd_3318_; lean_object* v___f_3319_; lean_object* v___f_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; lean_object* v___x_3324_; 
v_fst_3316_ = lean_ctor_get(v_head_3310_, 0);
lean_inc(v_fst_3316_);
lean_dec(v_head_3310_);
v_fst_3317_ = lean_ctor_get(v_snd_3311_, 0);
lean_inc(v_fst_3317_);
v_snd_3318_ = lean_ctor_get(v_snd_3311_, 1);
lean_inc(v_snd_3318_);
lean_dec(v_snd_3311_);
lean_inc(v_fst_3316_);
v___f_3319_ = lean_alloc_closure((void*)(l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__0___boxed), 5, 1);
lean_closure_set(v___f_3319_, 0, v_fst_3316_);
lean_inc(v_fst_3316_);
lean_inc_ref(v_a_3304_);
lean_inc_ref(v_validate_3303_);
v___f_3320_ = lean_alloc_closure((void*)(l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__1___boxed), 10, 4);
lean_closure_set(v___f_3320_, 0, v_validate_3303_);
lean_closure_set(v___f_3320_, 1, v_snd_3318_);
lean_closure_set(v___f_3320_, 2, v_a_3304_);
lean_closure_set(v___f_3320_, 3, v_fst_3316_);
lean_inc(v_ref_3305_);
v___x_3321_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_3321_, 0, v_ref_3305_);
lean_ctor_set(v___x_3321_, 1, v_fst_3316_);
lean_ctor_set(v___x_3321_, 2, v_fst_3317_);
lean_ctor_set_uint8(v___x_3321_, sizeof(void*)*3, v_applicationTime_3306_);
v___x_3322_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3322_, 0, v___x_3321_);
lean_ctor_set(v___x_3322_, 1, v___f_3320_);
lean_ctor_set(v___x_3322_, 2, v___f_3319_);
if (v_isShared_3315_ == 0)
{
lean_ctor_set(v___x_3314_, 1, v_a_3308_);
lean_ctor_set(v___x_3314_, 0, v___x_3322_);
v___x_3324_ = v___x_3314_;
goto v_reusejp_3323_;
}
else
{
lean_object* v_reuseFailAlloc_3326_; 
v_reuseFailAlloc_3326_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3326_, 0, v___x_3322_);
lean_ctor_set(v_reuseFailAlloc_3326_, 1, v_a_3308_);
v___x_3324_ = v_reuseFailAlloc_3326_;
goto v_reusejp_3323_;
}
v_reusejp_3323_:
{
v_a_3307_ = v_tail_3312_;
v_a_3308_ = v___x_3324_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___boxed(lean_object* v_validate_3329_, lean_object* v_a_3330_, lean_object* v_ref_3331_, lean_object* v_applicationTime_3332_, lean_object* v_a_3333_, lean_object* v_a_3334_){
_start:
{
uint8_t v_applicationTime_boxed_3335_; lean_object* v_res_3336_; 
v_applicationTime_boxed_3335_ = lean_unbox(v_applicationTime_3332_);
v_res_3336_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg(v_validate_3329_, v_a_3330_, v_ref_3331_, v_applicationTime_boxed_3335_, v_a_3333_, v_a_3334_);
return v_res_3336_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg(lean_object* v_attrDescrs_3350_, lean_object* v_validate_3351_, uint8_t v_applicationTime_3352_, lean_object* v_ref_3353_){
_start:
{
lean_object* v___f_3355_; lean_object* v___f_3356_; lean_object* v___f_3357_; lean_object* v___f_3358_; lean_object* v___f_3359_; lean_object* v___f_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; lean_object* v___x_3365_; 
v___f_3355_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__0));
v___f_3356_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__2));
v___f_3357_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__3));
v___f_3358_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__4));
v___f_3359_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__5));
v___f_3360_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__6));
v___x_3361_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__7));
v___x_3362_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__8));
lean_inc(v_ref_3353_);
v___x_3363_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_3363_, 0, v_ref_3353_);
lean_ctor_set(v___x_3363_, 1, v___f_3360_);
lean_ctor_set(v___x_3363_, 2, v___f_3359_);
lean_ctor_set(v___x_3363_, 3, v___f_3358_);
lean_ctor_set(v___x_3363_, 4, v___f_3357_);
lean_ctor_set(v___x_3363_, 5, v___f_3356_);
lean_ctor_set(v___x_3363_, 6, v___x_3361_);
lean_ctor_set(v___x_3363_, 7, v___x_3362_);
v___x_3364_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3364_, 0, v___x_3363_);
lean_ctor_set(v___x_3364_, 1, v___f_3355_);
v___x_3365_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_3364_);
if (lean_obj_tag(v___x_3365_) == 0)
{
lean_object* v_a_3366_; lean_object* v___x_3367_; lean_object* v___x_3368_; lean_object* v___x_3369_; 
v_a_3366_ = lean_ctor_get(v___x_3365_, 0);
lean_inc(v_a_3366_);
lean_dec_ref(v___x_3365_);
v___x_3367_ = lean_box(0);
lean_inc(v_a_3366_);
v___x_3368_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg(v_validate_3351_, v_a_3366_, v_ref_3353_, v_applicationTime_3352_, v_attrDescrs_3350_, v___x_3367_);
lean_inc(v___x_3368_);
v___x_3369_ = l_List_forM___at___00Lean_registerEnumAttributes_spec__3(v___x_3368_);
if (lean_obj_tag(v___x_3369_) == 0)
{
lean_object* v___x_3371_; uint8_t v_isShared_3372_; uint8_t v_isSharedCheck_3377_; 
v_isSharedCheck_3377_ = !lean_is_exclusive(v___x_3369_);
if (v_isSharedCheck_3377_ == 0)
{
lean_object* v_unused_3378_; 
v_unused_3378_ = lean_ctor_get(v___x_3369_, 0);
lean_dec(v_unused_3378_);
v___x_3371_ = v___x_3369_;
v_isShared_3372_ = v_isSharedCheck_3377_;
goto v_resetjp_3370_;
}
else
{
lean_dec(v___x_3369_);
v___x_3371_ = lean_box(0);
v_isShared_3372_ = v_isSharedCheck_3377_;
goto v_resetjp_3370_;
}
v_resetjp_3370_:
{
lean_object* v___x_3373_; lean_object* v___x_3375_; 
v___x_3373_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3373_, 0, v___x_3368_);
lean_ctor_set(v___x_3373_, 1, v_a_3366_);
if (v_isShared_3372_ == 0)
{
lean_ctor_set(v___x_3371_, 0, v___x_3373_);
v___x_3375_ = v___x_3371_;
goto v_reusejp_3374_;
}
else
{
lean_object* v_reuseFailAlloc_3376_; 
v_reuseFailAlloc_3376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3376_, 0, v___x_3373_);
v___x_3375_ = v_reuseFailAlloc_3376_;
goto v_reusejp_3374_;
}
v_reusejp_3374_:
{
return v___x_3375_;
}
}
}
else
{
lean_object* v_a_3379_; lean_object* v___x_3381_; uint8_t v_isShared_3382_; uint8_t v_isSharedCheck_3386_; 
lean_dec(v___x_3368_);
lean_dec(v_a_3366_);
v_a_3379_ = lean_ctor_get(v___x_3369_, 0);
v_isSharedCheck_3386_ = !lean_is_exclusive(v___x_3369_);
if (v_isSharedCheck_3386_ == 0)
{
v___x_3381_ = v___x_3369_;
v_isShared_3382_ = v_isSharedCheck_3386_;
goto v_resetjp_3380_;
}
else
{
lean_inc(v_a_3379_);
lean_dec(v___x_3369_);
v___x_3381_ = lean_box(0);
v_isShared_3382_ = v_isSharedCheck_3386_;
goto v_resetjp_3380_;
}
v_resetjp_3380_:
{
lean_object* v___x_3384_; 
if (v_isShared_3382_ == 0)
{
v___x_3384_ = v___x_3381_;
goto v_reusejp_3383_;
}
else
{
lean_object* v_reuseFailAlloc_3385_; 
v_reuseFailAlloc_3385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3385_, 0, v_a_3379_);
v___x_3384_ = v_reuseFailAlloc_3385_;
goto v_reusejp_3383_;
}
v_reusejp_3383_:
{
return v___x_3384_;
}
}
}
}
else
{
lean_object* v_a_3387_; lean_object* v___x_3389_; uint8_t v_isShared_3390_; uint8_t v_isSharedCheck_3394_; 
lean_dec(v_ref_3353_);
lean_dec_ref(v_validate_3351_);
lean_dec(v_attrDescrs_3350_);
v_a_3387_ = lean_ctor_get(v___x_3365_, 0);
v_isSharedCheck_3394_ = !lean_is_exclusive(v___x_3365_);
if (v_isSharedCheck_3394_ == 0)
{
v___x_3389_ = v___x_3365_;
v_isShared_3390_ = v_isSharedCheck_3394_;
goto v_resetjp_3388_;
}
else
{
lean_inc(v_a_3387_);
lean_dec(v___x_3365_);
v___x_3389_ = lean_box(0);
v_isShared_3390_ = v_isSharedCheck_3394_;
goto v_resetjp_3388_;
}
v_resetjp_3388_:
{
lean_object* v___x_3392_; 
if (v_isShared_3390_ == 0)
{
v___x_3392_ = v___x_3389_;
goto v_reusejp_3391_;
}
else
{
lean_object* v_reuseFailAlloc_3393_; 
v_reuseFailAlloc_3393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3393_, 0, v_a_3387_);
v___x_3392_ = v_reuseFailAlloc_3393_;
goto v_reusejp_3391_;
}
v_reusejp_3391_:
{
return v___x_3392_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___boxed(lean_object* v_attrDescrs_3395_, lean_object* v_validate_3396_, lean_object* v_applicationTime_3397_, lean_object* v_ref_3398_, lean_object* v_a_3399_){
_start:
{
uint8_t v_applicationTime_boxed_3400_; lean_object* v_res_3401_; 
v_applicationTime_boxed_3400_ = lean_unbox(v_applicationTime_3397_);
v_res_3401_ = l_Lean_registerEnumAttributes___redArg(v_attrDescrs_3395_, v_validate_3396_, v_applicationTime_boxed_3400_, v_ref_3398_);
return v_res_3401_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes(lean_object* v_00_u03b1_3402_, lean_object* v_attrDescrs_3403_, lean_object* v_validate_3404_, uint8_t v_applicationTime_3405_, lean_object* v_ref_3406_){
_start:
{
lean_object* v___x_3408_; 
v___x_3408_ = l_Lean_registerEnumAttributes___redArg(v_attrDescrs_3403_, v_validate_3404_, v_applicationTime_3405_, v_ref_3406_);
return v___x_3408_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___boxed(lean_object* v_00_u03b1_3409_, lean_object* v_attrDescrs_3410_, lean_object* v_validate_3411_, lean_object* v_applicationTime_3412_, lean_object* v_ref_3413_, lean_object* v_a_3414_){
_start:
{
uint8_t v_applicationTime_boxed_3415_; lean_object* v_res_3416_; 
v_applicationTime_boxed_3415_ = lean_unbox(v_applicationTime_3412_);
v_res_3416_ = l_Lean_registerEnumAttributes(v_00_u03b1_3409_, v_attrDescrs_3410_, v_validate_3411_, v_applicationTime_boxed_3415_, v_ref_3413_);
return v_res_3416_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0(lean_object* v_00_u03b1_3417_, lean_object* v_env_3418_, lean_object* v_as_3419_, size_t v_i_3420_, size_t v_stop_3421_, lean_object* v_b_3422_){
_start:
{
lean_object* v___x_3423_; 
v___x_3423_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg(v_env_3418_, v_as_3419_, v_i_3420_, v_stop_3421_, v_b_3422_);
return v___x_3423_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___boxed(lean_object* v_00_u03b1_3424_, lean_object* v_env_3425_, lean_object* v_as_3426_, lean_object* v_i_3427_, lean_object* v_stop_3428_, lean_object* v_b_3429_){
_start:
{
size_t v_i_boxed_3430_; size_t v_stop_boxed_3431_; lean_object* v_res_3432_; 
v_i_boxed_3430_ = lean_unbox_usize(v_i_3427_);
lean_dec(v_i_3427_);
v_stop_boxed_3431_ = lean_unbox_usize(v_stop_3428_);
lean_dec(v_stop_3428_);
v_res_3432_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0(v_00_u03b1_3424_, v_env_3425_, v_as_3426_, v_i_boxed_3430_, v_stop_boxed_3431_, v_b_3429_);
lean_dec_ref(v_as_3426_);
return v_res_3432_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerEnumAttributes_spec__1(lean_object* v_00_u03b1_3433_, lean_object* v_newState_3434_, lean_object* v_x_3435_, lean_object* v_x_3436_){
_start:
{
lean_object* v___x_3437_; 
v___x_3437_ = l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___redArg(v_newState_3434_, v_x_3435_, v_x_3436_);
return v___x_3437_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___boxed(lean_object* v_00_u03b1_3438_, lean_object* v_newState_3439_, lean_object* v_x_3440_, lean_object* v_x_3441_){
_start:
{
lean_object* v_res_3442_; 
v_res_3442_ = l_List_foldl___at___00Lean_registerEnumAttributes_spec__1(v_00_u03b1_3438_, v_newState_3439_, v_x_3440_, v_x_3441_);
lean_dec(v_newState_3439_);
return v_res_3442_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2(lean_object* v_00_u03b1_3443_, lean_object* v_validate_3444_, lean_object* v_a_3445_, lean_object* v_ref_3446_, uint8_t v_applicationTime_3447_, lean_object* v_a_3448_, lean_object* v_a_3449_){
_start:
{
lean_object* v___x_3450_; 
v___x_3450_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg(v_validate_3444_, v_a_3445_, v_ref_3446_, v_applicationTime_3447_, v_a_3448_, v_a_3449_);
return v___x_3450_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___boxed(lean_object* v_00_u03b1_3451_, lean_object* v_validate_3452_, lean_object* v_a_3453_, lean_object* v_ref_3454_, lean_object* v_applicationTime_3455_, lean_object* v_a_3456_, lean_object* v_a_3457_){
_start:
{
uint8_t v_applicationTime_boxed_3458_; lean_object* v_res_3459_; 
v_applicationTime_boxed_3458_ = lean_unbox(v_applicationTime_3455_);
v_res_3459_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2(v_00_u03b1_3451_, v_validate_3452_, v_a_3453_, v_ref_3454_, v_applicationTime_boxed_3458_, v_a_3456_, v_a_3457_);
return v_res_3459_;
}
}
LEAN_EXPORT lean_object* l_Lean_EnumAttributes_getValue___redArg(lean_object* v_inst_3460_, lean_object* v_attr_3461_, lean_object* v_env_3462_, lean_object* v_decl_3463_){
_start:
{
lean_object* v___x_3464_; lean_object* v___x_3465_; 
v___x_3464_ = lean_box(1);
v___x_3465_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3462_, v_decl_3463_);
if (lean_obj_tag(v___x_3465_) == 0)
{
lean_object* v_ext_3466_; lean_object* v_toEnvExtension_3467_; lean_object* v_asyncMode_3468_; lean_object* v___x_3469_; lean_object* v___x_3470_; 
lean_dec(v_inst_3460_);
v_ext_3466_ = lean_ctor_get(v_attr_3461_, 1);
lean_inc_ref(v_ext_3466_);
lean_dec_ref(v_attr_3461_);
v_toEnvExtension_3467_ = lean_ctor_get(v_ext_3466_, 0);
v_asyncMode_3468_ = lean_ctor_get(v_toEnvExtension_3467_, 2);
lean_inc(v_asyncMode_3468_);
lean_inc(v_decl_3463_);
v___x_3469_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3464_, v_ext_3466_, v_env_3462_, v_asyncMode_3468_, v_decl_3463_);
lean_dec(v_asyncMode_3468_);
lean_dec_ref(v_ext_3466_);
v___x_3470_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_3469_, v_decl_3463_);
lean_dec(v_decl_3463_);
lean_dec(v___x_3469_);
return v___x_3470_;
}
else
{
lean_object* v_val_3471_; lean_object* v_ext_3472_; lean_object* v___x_3474_; uint8_t v_isShared_3475_; uint8_t v_isSharedCheck_3502_; 
v_val_3471_ = lean_ctor_get(v___x_3465_, 0);
lean_inc(v_val_3471_);
lean_dec_ref(v___x_3465_);
v_ext_3472_ = lean_ctor_get(v_attr_3461_, 1);
v_isSharedCheck_3502_ = !lean_is_exclusive(v_attr_3461_);
if (v_isSharedCheck_3502_ == 0)
{
lean_object* v_unused_3503_; 
v_unused_3503_ = lean_ctor_get(v_attr_3461_, 0);
lean_dec(v_unused_3503_);
v___x_3474_ = v_attr_3461_;
v_isShared_3475_ = v_isSharedCheck_3502_;
goto v_resetjp_3473_;
}
else
{
lean_inc(v_ext_3472_);
lean_dec(v_attr_3461_);
v___x_3474_ = lean_box(0);
v_isShared_3475_ = v_isSharedCheck_3502_;
goto v_resetjp_3473_;
}
v_resetjp_3473_:
{
uint8_t v___x_3476_; lean_object* v___x_3477_; lean_object* v___x_3478_; lean_object* v___x_3479_; uint8_t v___x_3480_; 
v___x_3476_ = 0;
v___x_3477_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_3464_, v_ext_3472_, v_env_3462_, v_val_3471_, v___x_3476_);
lean_dec(v_val_3471_);
lean_dec_ref(v_env_3462_);
lean_dec_ref(v_ext_3472_);
v___x_3478_ = lean_unsigned_to_nat(0u);
v___x_3479_ = lean_array_get_size(v___x_3477_);
v___x_3480_ = lean_nat_dec_lt(v___x_3478_, v___x_3479_);
if (v___x_3480_ == 0)
{
lean_object* v___x_3481_; 
lean_dec_ref(v___x_3477_);
lean_del_object(v___x_3474_);
lean_dec(v_decl_3463_);
lean_dec(v_inst_3460_);
v___x_3481_ = lean_box(0);
return v___x_3481_;
}
else
{
lean_object* v___x_3482_; lean_object* v___x_3483_; uint8_t v___x_3484_; 
v___x_3482_ = lean_unsigned_to_nat(1u);
v___x_3483_ = lean_nat_sub(v___x_3479_, v___x_3482_);
v___x_3484_ = lean_nat_dec_le(v___x_3478_, v___x_3483_);
if (v___x_3484_ == 0)
{
lean_object* v___x_3485_; 
lean_dec(v___x_3483_);
lean_dec_ref(v___x_3477_);
lean_del_object(v___x_3474_);
lean_dec(v_decl_3463_);
lean_dec(v_inst_3460_);
v___x_3485_ = lean_box(0);
return v___x_3485_;
}
else
{
lean_object* v___f_3486_; lean_object* v___x_3488_; 
v___f_3486_ = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2___redArg___closed__0));
if (v_isShared_3475_ == 0)
{
lean_ctor_set(v___x_3474_, 1, v_inst_3460_);
lean_ctor_set(v___x_3474_, 0, v_decl_3463_);
v___x_3488_ = v___x_3474_;
goto v_reusejp_3487_;
}
else
{
lean_object* v_reuseFailAlloc_3501_; 
v_reuseFailAlloc_3501_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3501_, 0, v_decl_3463_);
lean_ctor_set(v_reuseFailAlloc_3501_, 1, v_inst_3460_);
v___x_3488_ = v_reuseFailAlloc_3501_;
goto v_reusejp_3487_;
}
v_reusejp_3487_:
{
lean_object* v___x_3489_; lean_object* v___x_3490_; 
v___x_3489_ = ((lean_object*)(l_Lean_ParametricAttribute_getParam_x3f___redArg___closed__1));
v___x_3490_ = l_Array_binSearchAux___redArg(v___f_3486_, v___x_3489_, v___x_3477_, v___x_3488_, v___x_3478_, v___x_3483_);
lean_dec_ref(v___x_3477_);
if (lean_obj_tag(v___x_3490_) == 0)
{
lean_object* v___x_3491_; 
v___x_3491_ = lean_box(0);
return v___x_3491_;
}
else
{
lean_object* v_val_3492_; lean_object* v___x_3494_; uint8_t v_isShared_3495_; uint8_t v_isSharedCheck_3500_; 
v_val_3492_ = lean_ctor_get(v___x_3490_, 0);
v_isSharedCheck_3500_ = !lean_is_exclusive(v___x_3490_);
if (v_isSharedCheck_3500_ == 0)
{
v___x_3494_ = v___x_3490_;
v_isShared_3495_ = v_isSharedCheck_3500_;
goto v_resetjp_3493_;
}
else
{
lean_inc(v_val_3492_);
lean_dec(v___x_3490_);
v___x_3494_ = lean_box(0);
v_isShared_3495_ = v_isSharedCheck_3500_;
goto v_resetjp_3493_;
}
v_resetjp_3493_:
{
lean_object* v_snd_3496_; lean_object* v___x_3498_; 
v_snd_3496_ = lean_ctor_get(v_val_3492_, 1);
lean_inc(v_snd_3496_);
lean_dec(v_val_3492_);
if (v_isShared_3495_ == 0)
{
lean_ctor_set(v___x_3494_, 0, v_snd_3496_);
v___x_3498_ = v___x_3494_;
goto v_reusejp_3497_;
}
else
{
lean_object* v_reuseFailAlloc_3499_; 
v_reuseFailAlloc_3499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3499_, 0, v_snd_3496_);
v___x_3498_ = v_reuseFailAlloc_3499_;
goto v_reusejp_3497_;
}
v_reusejp_3497_:
{
return v___x_3498_;
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
LEAN_EXPORT lean_object* l_Lean_EnumAttributes_getValue(lean_object* v_00_u03b1_3504_, lean_object* v_inst_3505_, lean_object* v_attr_3506_, lean_object* v_env_3507_, lean_object* v_decl_3508_){
_start:
{
lean_object* v___x_3509_; 
v___x_3509_ = l_Lean_EnumAttributes_getValue___redArg(v_inst_3505_, v_attr_3506_, v_env_3507_, v_decl_3508_);
return v___x_3509_;
}
}
LEAN_EXPORT lean_object* l_Lean_EnumAttributes_setValue___redArg(lean_object* v_attrs_3518_, lean_object* v_env_3519_, lean_object* v_decl_3520_, lean_object* v_val_3521_){
_start:
{
lean_object* v_ext_3522_; lean_object* v___x_3524_; uint8_t v_isShared_3525_; uint8_t v_isSharedCheck_3586_; 
v_ext_3522_ = lean_ctor_get(v_attrs_3518_, 1);
v_isSharedCheck_3586_ = !lean_is_exclusive(v_attrs_3518_);
if (v_isSharedCheck_3586_ == 0)
{
lean_object* v_unused_3587_; 
v_unused_3587_ = lean_ctor_get(v_attrs_3518_, 0);
lean_dec(v_unused_3587_);
v___x_3524_ = v_attrs_3518_;
v_isShared_3525_ = v_isSharedCheck_3586_;
goto v_resetjp_3523_;
}
else
{
lean_inc(v_ext_3522_);
lean_dec(v_attrs_3518_);
v___x_3524_ = lean_box(0);
v_isShared_3525_ = v_isSharedCheck_3586_;
goto v_resetjp_3523_;
}
v_resetjp_3523_:
{
lean_object* v_toEnvExtension_3526_; lean_object* v_name_3527_; lean_object* v___x_3528_; uint8_t v___x_3529_; lean_object* v___x_3530_; lean_object* v___x_3531_; lean_object* v___x_3532_; lean_object* v___x_3533_; lean_object* v___x_3534_; lean_object* v___x_3535_; lean_object* v___x_3536_; lean_object* v_pfx_3537_; lean_object* v___x_3538_; 
v_toEnvExtension_3526_ = lean_ctor_get(v_ext_3522_, 0);
v_name_3527_ = lean_ctor_get(v_ext_3522_, 1);
v___x_3528_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__0));
v___x_3529_ = 1;
lean_inc(v_name_3527_);
v___x_3530_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_3527_, v___x_3529_);
v___x_3531_ = lean_string_append(v___x_3528_, v___x_3530_);
lean_dec_ref(v___x_3530_);
v___x_3532_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__1));
v___x_3533_ = lean_string_append(v___x_3531_, v___x_3532_);
lean_inc(v_decl_3520_);
v___x_3534_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_decl_3520_, v___x_3529_);
v___x_3535_ = lean_string_append(v___x_3533_, v___x_3534_);
lean_dec_ref(v___x_3534_);
v___x_3536_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__4));
v_pfx_3537_ = lean_string_append(v___x_3535_, v___x_3536_);
v___x_3538_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3519_, v_decl_3520_);
if (lean_obj_tag(v___x_3538_) == 0)
{
lean_object* v_asyncMode_3539_; uint8_t v___x_3546_; 
v_asyncMode_3539_ = lean_ctor_get(v_toEnvExtension_3526_, 2);
lean_inc(v_asyncMode_3539_);
lean_inc(v_decl_3520_);
lean_inc_ref(v_env_3519_);
v___x_3546_ = l_Lean_EnvExtension_asyncMayModify___redArg(v_env_3519_, v_decl_3520_, v_asyncMode_3539_);
if (v___x_3546_ == 0)
{
lean_object* v___x_3547_; lean_object* v___x_3548_; lean_object* v___y_3550_; lean_object* v___x_3554_; 
lean_dec(v_asyncMode_3539_);
lean_del_object(v___x_3524_);
lean_dec_ref(v_ext_3522_);
lean_dec(v_val_3521_);
lean_dec(v_decl_3520_);
v___x_3547_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__2));
v___x_3548_ = lean_string_append(v_pfx_3537_, v___x_3547_);
v___x_3554_ = l_Lean_Environment_asyncPrefix_x3f(v_env_3519_);
if (lean_obj_tag(v___x_3554_) == 0)
{
lean_object* v___x_3555_; 
v___x_3555_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__3));
v___y_3550_ = v___x_3555_;
goto v___jp_3549_;
}
else
{
lean_object* v_val_3556_; lean_object* v___x_3557_; lean_object* v___x_3558_; lean_object* v___x_3559_; lean_object* v___x_3560_; lean_object* v___x_3561_; lean_object* v___x_3562_; 
v_val_3556_ = lean_ctor_get(v___x_3554_, 0);
lean_inc(v_val_3556_);
lean_dec_ref(v___x_3554_);
v___x_3557_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__4));
v___x_3558_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_val_3556_, v___x_3529_);
v___x_3559_ = l_addParenHeuristic(v___x_3558_);
v___x_3560_ = lean_string_append(v___x_3557_, v___x_3559_);
lean_dec_ref(v___x_3559_);
v___x_3561_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__5));
v___x_3562_ = lean_string_append(v___x_3560_, v___x_3561_);
v___y_3550_ = v___x_3562_;
goto v___jp_3549_;
}
v___jp_3549_:
{
lean_object* v___x_3551_; lean_object* v___x_3552_; lean_object* v___x_3553_; 
v___x_3551_ = lean_string_append(v___x_3548_, v___y_3550_);
lean_dec_ref(v___y_3550_);
v___x_3552_ = lean_string_append(v___x_3551_, v___x_3536_);
v___x_3553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3553_, 0, v___x_3552_);
return v___x_3553_;
}
}
else
{
lean_object* v___x_3563_; lean_object* v___x_3564_; lean_object* v___x_3565_; 
v___x_3563_ = lean_box(1);
lean_inc(v_decl_3520_);
lean_inc_ref(v_env_3519_);
v___x_3564_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3563_, v_ext_3522_, v_env_3519_, v_asyncMode_3539_, v_decl_3520_);
v___x_3565_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_3564_, v_decl_3520_);
lean_dec(v___x_3564_);
if (lean_obj_tag(v___x_3565_) == 0)
{
lean_dec_ref(v_pfx_3537_);
goto v___jp_3540_;
}
else
{
lean_object* v___x_3567_; uint8_t v_isShared_3568_; uint8_t v_isSharedCheck_3574_; 
v_isSharedCheck_3574_ = !lean_is_exclusive(v___x_3565_);
if (v_isSharedCheck_3574_ == 0)
{
lean_object* v_unused_3575_; 
v_unused_3575_ = lean_ctor_get(v___x_3565_, 0);
lean_dec(v_unused_3575_);
v___x_3567_ = v___x_3565_;
v_isShared_3568_ = v_isSharedCheck_3574_;
goto v_resetjp_3566_;
}
else
{
lean_dec(v___x_3565_);
v___x_3567_ = lean_box(0);
v_isShared_3568_ = v_isSharedCheck_3574_;
goto v_resetjp_3566_;
}
v_resetjp_3566_:
{
if (v___x_3546_ == 0)
{
lean_del_object(v___x_3567_);
lean_dec_ref(v_pfx_3537_);
goto v___jp_3540_;
}
else
{
lean_object* v___x_3569_; lean_object* v___x_3570_; lean_object* v___x_3572_; 
lean_dec(v_asyncMode_3539_);
lean_del_object(v___x_3524_);
lean_dec_ref(v_ext_3522_);
lean_dec(v_val_3521_);
lean_dec(v_decl_3520_);
lean_dec_ref(v_env_3519_);
v___x_3569_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__6));
v___x_3570_ = lean_string_append(v_pfx_3537_, v___x_3569_);
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
v___jp_3540_:
{
lean_object* v___x_3542_; 
lean_inc(v_decl_3520_);
if (v_isShared_3525_ == 0)
{
lean_ctor_set(v___x_3524_, 1, v_val_3521_);
lean_ctor_set(v___x_3524_, 0, v_decl_3520_);
v___x_3542_ = v___x_3524_;
goto v_reusejp_3541_;
}
else
{
lean_object* v_reuseFailAlloc_3545_; 
v_reuseFailAlloc_3545_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3545_, 0, v_decl_3520_);
lean_ctor_set(v_reuseFailAlloc_3545_, 1, v_val_3521_);
v___x_3542_ = v_reuseFailAlloc_3545_;
goto v_reusejp_3541_;
}
v_reusejp_3541_:
{
lean_object* v___x_3543_; lean_object* v___x_3544_; 
v___x_3543_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_ext_3522_, v_env_3519_, v___x_3542_, v_asyncMode_3539_, v_decl_3520_);
lean_dec(v_asyncMode_3539_);
v___x_3544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3544_, 0, v___x_3543_);
return v___x_3544_;
}
}
}
else
{
lean_object* v___x_3577_; uint8_t v_isShared_3578_; uint8_t v_isSharedCheck_3584_; 
lean_del_object(v___x_3524_);
lean_dec_ref(v_ext_3522_);
lean_dec(v_val_3521_);
lean_dec(v_decl_3520_);
lean_dec_ref(v_env_3519_);
v_isSharedCheck_3584_ = !lean_is_exclusive(v___x_3538_);
if (v_isSharedCheck_3584_ == 0)
{
lean_object* v_unused_3585_; 
v_unused_3585_ = lean_ctor_get(v___x_3538_, 0);
lean_dec(v_unused_3585_);
v___x_3577_ = v___x_3538_;
v_isShared_3578_ = v_isSharedCheck_3584_;
goto v_resetjp_3576_;
}
else
{
lean_dec(v___x_3538_);
v___x_3577_ = lean_box(0);
v_isShared_3578_ = v_isSharedCheck_3584_;
goto v_resetjp_3576_;
}
v_resetjp_3576_:
{
lean_object* v___x_3579_; lean_object* v___x_3580_; lean_object* v___x_3582_; 
v___x_3579_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__7));
v___x_3580_ = lean_string_append(v_pfx_3537_, v___x_3579_);
if (v_isShared_3578_ == 0)
{
lean_ctor_set_tag(v___x_3577_, 0);
lean_ctor_set(v___x_3577_, 0, v___x_3580_);
v___x_3582_ = v___x_3577_;
goto v_reusejp_3581_;
}
else
{
lean_object* v_reuseFailAlloc_3583_; 
v_reuseFailAlloc_3583_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3583_, 0, v___x_3580_);
v___x_3582_ = v_reuseFailAlloc_3583_;
goto v_reusejp_3581_;
}
v_reusejp_3581_:
{
return v___x_3582_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_EnumAttributes_setValue(lean_object* v_00_u03b1_3588_, lean_object* v_attrs_3589_, lean_object* v_env_3590_, lean_object* v_decl_3591_, lean_object* v_val_3592_){
_start:
{
lean_object* v___x_3593_; 
v___x_3593_ = l_Lean_EnumAttributes_setValue___redArg(v_attrs_3589_, v_env_3590_, v_decl_3591_, v_val_3592_);
return v___x_3593_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_Attributes_2990505691____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3595_; lean_object* v___x_3596_; lean_object* v___x_3597_; 
v___x_3595_ = lean_obj_once(&l_Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_, &l_Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2__once, _init_l_Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_);
v___x_3596_ = lean_st_mk_ref(v___x_3595_);
v___x_3597_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3597_, 0, v___x_3596_);
return v___x_3597_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_Attributes_2990505691____hygCtx___hyg_2____boxed(lean_object* v_a_3598_){
_start:
{
lean_object* v_res_3599_; 
v_res_3599_ = l_Lean_initFn_00___x40_Lean_Attributes_2990505691____hygCtx___hyg_2_();
return v_res_3599_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerAttributeImplBuilder(lean_object* v_builderId_3602_, lean_object* v_builder_3603_){
_start:
{
lean_object* v___x_3605_; lean_object* v___x_3606_; uint8_t v___x_3607_; 
v___x_3605_ = l_Lean_attributeImplBuilderTableRef;
v___x_3606_ = lean_st_ref_get(v___x_3605_);
v___x_3607_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(v___x_3606_, v_builderId_3602_);
lean_dec(v___x_3606_);
if (v___x_3607_ == 0)
{
lean_object* v___x_3608_; lean_object* v___x_3609_; lean_object* v___x_3610_; lean_object* v___x_3611_; 
v___x_3608_ = lean_st_ref_take(v___x_3605_);
v___x_3609_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1___redArg(v___x_3608_, v_builderId_3602_, v_builder_3603_);
v___x_3610_ = lean_st_ref_set(v___x_3605_, v___x_3609_);
v___x_3611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3611_, 0, v___x_3610_);
return v___x_3611_;
}
else
{
lean_object* v___x_3612_; lean_object* v___x_3613_; lean_object* v___x_3614_; lean_object* v___x_3615_; lean_object* v___x_3616_; lean_object* v___x_3617_; lean_object* v___x_3618_; 
lean_dec_ref(v_builder_3603_);
v___x_3612_ = ((lean_object*)(l_Lean_registerAttributeImplBuilder___closed__0));
v___x_3613_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_builderId_3602_, v___x_3607_);
v___x_3614_ = lean_string_append(v___x_3612_, v___x_3613_);
lean_dec_ref(v___x_3613_);
v___x_3615_ = ((lean_object*)(l_Lean_registerAttributeImplBuilder___closed__1));
v___x_3616_ = lean_string_append(v___x_3614_, v___x_3615_);
v___x_3617_ = lean_mk_io_user_error(v___x_3616_);
v___x_3618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3618_, 0, v___x_3617_);
return v___x_3618_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerAttributeImplBuilder___boxed(lean_object* v_builderId_3619_, lean_object* v_builder_3620_, lean_object* v_a_3621_){
_start:
{
lean_object* v_res_3622_; 
v_res_3622_ = l_Lean_registerAttributeImplBuilder(v_builderId_3619_, v_builder_3620_);
return v_res_3622_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___redArg(lean_object* v_e_3623_){
_start:
{
if (lean_obj_tag(v_e_3623_) == 0)
{
lean_object* v_a_3625_; lean_object* v___x_3627_; uint8_t v_isShared_3628_; uint8_t v_isSharedCheck_3633_; 
v_a_3625_ = lean_ctor_get(v_e_3623_, 0);
v_isSharedCheck_3633_ = !lean_is_exclusive(v_e_3623_);
if (v_isSharedCheck_3633_ == 0)
{
v___x_3627_ = v_e_3623_;
v_isShared_3628_ = v_isSharedCheck_3633_;
goto v_resetjp_3626_;
}
else
{
lean_inc(v_a_3625_);
lean_dec(v_e_3623_);
v___x_3627_ = lean_box(0);
v_isShared_3628_ = v_isSharedCheck_3633_;
goto v_resetjp_3626_;
}
v_resetjp_3626_:
{
lean_object* v___x_3629_; lean_object* v___x_3631_; 
v___x_3629_ = lean_mk_io_user_error(v_a_3625_);
if (v_isShared_3628_ == 0)
{
lean_ctor_set_tag(v___x_3627_, 1);
lean_ctor_set(v___x_3627_, 0, v___x_3629_);
v___x_3631_ = v___x_3627_;
goto v_reusejp_3630_;
}
else
{
lean_object* v_reuseFailAlloc_3632_; 
v_reuseFailAlloc_3632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3632_, 0, v___x_3629_);
v___x_3631_ = v_reuseFailAlloc_3632_;
goto v_reusejp_3630_;
}
v_reusejp_3630_:
{
return v___x_3631_;
}
}
}
else
{
lean_object* v_a_3634_; lean_object* v___x_3636_; uint8_t v_isShared_3637_; uint8_t v_isSharedCheck_3641_; 
v_a_3634_ = lean_ctor_get(v_e_3623_, 0);
v_isSharedCheck_3641_ = !lean_is_exclusive(v_e_3623_);
if (v_isSharedCheck_3641_ == 0)
{
v___x_3636_ = v_e_3623_;
v_isShared_3637_ = v_isSharedCheck_3641_;
goto v_resetjp_3635_;
}
else
{
lean_inc(v_a_3634_);
lean_dec(v_e_3623_);
v___x_3636_ = lean_box(0);
v_isShared_3637_ = v_isSharedCheck_3641_;
goto v_resetjp_3635_;
}
v_resetjp_3635_:
{
lean_object* v___x_3639_; 
if (v_isShared_3637_ == 0)
{
lean_ctor_set_tag(v___x_3636_, 0);
v___x_3639_ = v___x_3636_;
goto v_reusejp_3638_;
}
else
{
lean_object* v_reuseFailAlloc_3640_; 
v_reuseFailAlloc_3640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3640_, 0, v_a_3634_);
v___x_3639_ = v_reuseFailAlloc_3640_;
goto v_reusejp_3638_;
}
v_reusejp_3638_:
{
return v___x_3639_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___redArg___boxed(lean_object* v_e_3642_, lean_object* v_a_3643_){
_start:
{
lean_object* v_res_3644_; 
v_res_3644_ = l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___redArg(v_e_3642_);
return v_res_3644_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1(lean_object* v_00_u03b1_3645_, lean_object* v_e_3646_){
_start:
{
lean_object* v___x_3648_; 
v___x_3648_ = l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___redArg(v_e_3646_);
return v___x_3648_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___boxed(lean_object* v_00_u03b1_3649_, lean_object* v_e_3650_, lean_object* v_a_3651_){
_start:
{
lean_object* v_res_3652_; 
v_res_3652_ = l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1(v_00_u03b1_3649_, v_e_3650_);
return v_res_3652_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___redArg(lean_object* v_a_3653_, lean_object* v_x_3654_){
_start:
{
if (lean_obj_tag(v_x_3654_) == 0)
{
lean_object* v___x_3655_; 
v___x_3655_ = lean_box(0);
return v___x_3655_;
}
else
{
lean_object* v_key_3656_; lean_object* v_value_3657_; lean_object* v_tail_3658_; uint8_t v___x_3659_; 
v_key_3656_ = lean_ctor_get(v_x_3654_, 0);
v_value_3657_ = lean_ctor_get(v_x_3654_, 1);
v_tail_3658_ = lean_ctor_get(v_x_3654_, 2);
v___x_3659_ = lean_name_eq(v_key_3656_, v_a_3653_);
if (v___x_3659_ == 0)
{
v_x_3654_ = v_tail_3658_;
goto _start;
}
else
{
lean_object* v___x_3661_; 
lean_inc(v_value_3657_);
v___x_3661_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3661_, 0, v_value_3657_);
return v___x_3661_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___redArg___boxed(lean_object* v_a_3662_, lean_object* v_x_3663_){
_start:
{
lean_object* v_res_3664_; 
v_res_3664_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___redArg(v_a_3662_, v_x_3663_);
lean_dec(v_x_3663_);
lean_dec(v_a_3662_);
return v_res_3664_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(lean_object* v_m_3665_, lean_object* v_a_3666_){
_start:
{
lean_object* v_buckets_3667_; lean_object* v___x_3668_; uint64_t v___y_3670_; 
v_buckets_3667_ = lean_ctor_get(v_m_3665_, 1);
v___x_3668_ = lean_array_get_size(v_buckets_3667_);
if (lean_obj_tag(v_a_3666_) == 0)
{
uint64_t v___x_3684_; 
v___x_3684_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg___closed__0);
v___y_3670_ = v___x_3684_;
goto v___jp_3669_;
}
else
{
uint64_t v_hash_3685_; 
v_hash_3685_ = lean_ctor_get_uint64(v_a_3666_, sizeof(void*)*2);
v___y_3670_ = v_hash_3685_;
goto v___jp_3669_;
}
v___jp_3669_:
{
uint64_t v___x_3671_; uint64_t v___x_3672_; uint64_t v_fold_3673_; uint64_t v___x_3674_; uint64_t v___x_3675_; uint64_t v___x_3676_; size_t v___x_3677_; size_t v___x_3678_; size_t v___x_3679_; size_t v___x_3680_; size_t v___x_3681_; lean_object* v___x_3682_; lean_object* v___x_3683_; 
v___x_3671_ = 32ULL;
v___x_3672_ = lean_uint64_shift_right(v___y_3670_, v___x_3671_);
v_fold_3673_ = lean_uint64_xor(v___y_3670_, v___x_3672_);
v___x_3674_ = 16ULL;
v___x_3675_ = lean_uint64_shift_right(v_fold_3673_, v___x_3674_);
v___x_3676_ = lean_uint64_xor(v_fold_3673_, v___x_3675_);
v___x_3677_ = lean_uint64_to_usize(v___x_3676_);
v___x_3678_ = lean_usize_of_nat(v___x_3668_);
v___x_3679_ = ((size_t)1ULL);
v___x_3680_ = lean_usize_sub(v___x_3678_, v___x_3679_);
v___x_3681_ = lean_usize_land(v___x_3677_, v___x_3680_);
v___x_3682_ = lean_array_uget_borrowed(v_buckets_3667_, v___x_3681_);
v___x_3683_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___redArg(v_a_3666_, v___x_3682_);
return v___x_3683_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg___boxed(lean_object* v_m_3686_, lean_object* v_a_3687_){
_start:
{
lean_object* v_res_3688_; 
v_res_3688_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(v_m_3686_, v_a_3687_);
lean_dec(v_a_3687_);
lean_dec_ref(v_m_3686_);
return v_res_3688_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAttributeImplOfEntry(lean_object* v_e_3690_){
_start:
{
lean_object* v___x_3692_; lean_object* v___x_3693_; lean_object* v_builderId_3694_; lean_object* v_ref_3695_; lean_object* v_args_3696_; lean_object* v___x_3697_; 
v___x_3692_ = l_Lean_attributeImplBuilderTableRef;
v___x_3693_ = lean_st_ref_get(v___x_3692_);
v_builderId_3694_ = lean_ctor_get(v_e_3690_, 0);
lean_inc(v_builderId_3694_);
v_ref_3695_ = lean_ctor_get(v_e_3690_, 1);
lean_inc(v_ref_3695_);
v_args_3696_ = lean_ctor_get(v_e_3690_, 2);
lean_inc(v_args_3696_);
lean_dec_ref(v_e_3690_);
v___x_3697_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(v___x_3693_, v_builderId_3694_);
lean_dec(v___x_3693_);
if (lean_obj_tag(v___x_3697_) == 0)
{
lean_object* v___x_3698_; uint8_t v___x_3699_; lean_object* v___x_3700_; lean_object* v___x_3701_; lean_object* v___x_3702_; lean_object* v___x_3703_; lean_object* v___x_3704_; lean_object* v___x_3705_; 
lean_dec(v_args_3696_);
lean_dec(v_ref_3695_);
v___x_3698_ = ((lean_object*)(l_Lean_mkAttributeImplOfEntry___closed__0));
v___x_3699_ = 1;
v___x_3700_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_builderId_3694_, v___x_3699_);
v___x_3701_ = lean_string_append(v___x_3698_, v___x_3700_);
lean_dec_ref(v___x_3700_);
v___x_3702_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__4));
v___x_3703_ = lean_string_append(v___x_3701_, v___x_3702_);
v___x_3704_ = lean_mk_io_user_error(v___x_3703_);
v___x_3705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3705_, 0, v___x_3704_);
return v___x_3705_;
}
else
{
lean_object* v_val_3706_; lean_object* v___x_3707_; lean_object* v___x_3708_; 
lean_dec(v_builderId_3694_);
v_val_3706_ = lean_ctor_get(v___x_3697_, 0);
lean_inc(v_val_3706_);
lean_dec_ref(v___x_3697_);
v___x_3707_ = lean_apply_2(v_val_3706_, v_ref_3695_, v_args_3696_);
v___x_3708_ = l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___redArg(v___x_3707_);
return v___x_3708_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkAttributeImplOfEntry___boxed(lean_object* v_e_3709_, lean_object* v_a_3710_){
_start:
{
lean_object* v_res_3711_; 
v_res_3711_ = l_Lean_mkAttributeImplOfEntry(v_e_3709_);
return v_res_3711_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0(lean_object* v_00_u03b2_3712_, lean_object* v_m_3713_, lean_object* v_a_3714_){
_start:
{
lean_object* v___x_3715_; 
v___x_3715_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(v_m_3713_, v_a_3714_);
return v___x_3715_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___boxed(lean_object* v_00_u03b2_3716_, lean_object* v_m_3717_, lean_object* v_a_3718_){
_start:
{
lean_object* v_res_3719_; 
v_res_3719_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0(v_00_u03b2_3716_, v_m_3717_, v_a_3718_);
lean_dec(v_a_3718_);
lean_dec_ref(v_m_3717_);
return v_res_3719_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0(lean_object* v_00_u03b2_3720_, lean_object* v_a_3721_, lean_object* v_x_3722_){
_start:
{
lean_object* v___x_3723_; 
v___x_3723_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___redArg(v_a_3721_, v_x_3722_);
return v___x_3723_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3724_, lean_object* v_a_3725_, lean_object* v_x_3726_){
_start:
{
lean_object* v_res_3727_; 
v_res_3727_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0(v_00_u03b2_3724_, v_a_3725_, v_x_3726_);
lean_dec(v_x_3726_);
lean_dec(v_a_3725_);
return v_res_3727_;
}
}
static lean_object* _init_l_Lean_instInhabitedAttributeExtensionState_default___closed__0(void){
_start:
{
lean_object* v___x_3728_; lean_object* v___x_3729_; lean_object* v___x_3730_; 
v___x_3728_ = lean_obj_once(&l_Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_, &l_Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2__once, _init_l_Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_);
v___x_3729_ = lean_box(0);
v___x_3730_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3730_, 0, v___x_3729_);
lean_ctor_set(v___x_3730_, 1, v___x_3728_);
return v___x_3730_;
}
}
static lean_object* _init_l_Lean_instInhabitedAttributeExtensionState_default(void){
_start:
{
lean_object* v___x_3731_; 
v___x_3731_ = lean_obj_once(&l_Lean_instInhabitedAttributeExtensionState_default___closed__0, &l_Lean_instInhabitedAttributeExtensionState_default___closed__0_once, _init_l_Lean_instInhabitedAttributeExtensionState_default___closed__0);
return v___x_3731_;
}
}
static lean_object* _init_l_Lean_instInhabitedAttributeExtensionState(void){
_start:
{
lean_object* v___x_3732_; 
v___x_3732_ = l_Lean_instInhabitedAttributeExtensionState_default;
return v___x_3732_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_AttributeExtension_mkInitial(){
_start:
{
lean_object* v___x_3734_; lean_object* v___x_3735_; lean_object* v___x_3736_; lean_object* v___x_3737_; lean_object* v___x_3738_; 
v___x_3734_ = l_Lean_attributeMapRef;
v___x_3735_ = lean_st_ref_get(v___x_3734_);
v___x_3736_ = lean_box(0);
v___x_3737_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3737_, 0, v___x_3736_);
lean_ctor_set(v___x_3737_, 1, v___x_3735_);
v___x_3738_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3738_, 0, v___x_3737_);
return v___x_3738_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_AttributeExtension_mkInitial___boxed(lean_object* v_a_3739_){
_start:
{
lean_object* v_res_3740_; 
v_res_3740_ = l___private_Lean_Attributes_0__Lean_AttributeExtension_mkInitial();
return v_res_3740_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAttributeImplOfConstantUnsafe(lean_object* v_env_3746_, lean_object* v_opts_3747_, lean_object* v_declName_3748_){
_start:
{
uint8_t v___x_3751_; lean_object* v___x_3752_; 
v___x_3751_ = 0;
lean_inc(v_declName_3748_);
lean_inc_ref(v_env_3746_);
v___x_3752_ = l_Lean_Environment_find_x3f(v_env_3746_, v_declName_3748_, v___x_3751_);
if (lean_obj_tag(v___x_3752_) == 0)
{
lean_object* v___x_3753_; uint8_t v___x_3754_; lean_object* v___x_3755_; lean_object* v___x_3756_; lean_object* v___x_3757_; lean_object* v___x_3758_; lean_object* v___x_3759_; 
lean_dec_ref(v_env_3746_);
v___x_3753_ = ((lean_object*)(l_Lean_mkAttributeImplOfConstantUnsafe___closed__2));
v___x_3754_ = 1;
v___x_3755_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_declName_3748_, v___x_3754_);
v___x_3756_ = lean_string_append(v___x_3753_, v___x_3755_);
lean_dec_ref(v___x_3755_);
v___x_3757_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__4));
v___x_3758_ = lean_string_append(v___x_3756_, v___x_3757_);
v___x_3759_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3759_, 0, v___x_3758_);
return v___x_3759_;
}
else
{
lean_object* v_val_3760_; lean_object* v___x_3761_; 
v_val_3760_ = lean_ctor_get(v___x_3752_, 0);
lean_inc(v_val_3760_);
lean_dec_ref(v___x_3752_);
v___x_3761_ = l_Lean_ConstantInfo_type(v_val_3760_);
lean_dec(v_val_3760_);
if (lean_obj_tag(v___x_3761_) == 4)
{
lean_object* v_declName_3762_; 
v_declName_3762_ = lean_ctor_get(v___x_3761_, 0);
lean_inc(v_declName_3762_);
lean_dec_ref(v___x_3761_);
if (lean_obj_tag(v_declName_3762_) == 1)
{
lean_object* v_pre_3763_; 
v_pre_3763_ = lean_ctor_get(v_declName_3762_, 0);
lean_inc(v_pre_3763_);
if (lean_obj_tag(v_pre_3763_) == 1)
{
lean_object* v_pre_3764_; 
v_pre_3764_ = lean_ctor_get(v_pre_3763_, 0);
if (lean_obj_tag(v_pre_3764_) == 0)
{
lean_object* v_str_3765_; lean_object* v_str_3766_; lean_object* v___x_3767_; uint8_t v___x_3768_; 
v_str_3765_ = lean_ctor_get(v_declName_3762_, 1);
lean_inc_ref(v_str_3765_);
lean_dec_ref(v_declName_3762_);
v_str_3766_ = lean_ctor_get(v_pre_3763_, 1);
lean_inc_ref(v_str_3766_);
lean_dec_ref(v_pre_3763_);
v___x_3767_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__0));
v___x_3768_ = lean_string_dec_eq(v_str_3766_, v___x_3767_);
lean_dec_ref(v_str_3766_);
if (v___x_3768_ == 0)
{
lean_dec_ref(v_str_3765_);
lean_dec(v_declName_3748_);
lean_dec_ref(v_env_3746_);
goto v___jp_3749_;
}
else
{
lean_object* v___x_3769_; uint8_t v___x_3770_; 
v___x_3769_ = ((lean_object*)(l_Lean_mkAttributeImplOfConstantUnsafe___closed__3));
v___x_3770_ = lean_string_dec_eq(v_str_3765_, v___x_3769_);
lean_dec_ref(v_str_3765_);
if (v___x_3770_ == 0)
{
lean_dec(v_declName_3748_);
lean_dec_ref(v_env_3746_);
goto v___jp_3749_;
}
else
{
lean_object* v___x_3771_; 
v___x_3771_ = l_Lean_Environment_evalConst___redArg(v_env_3746_, v_opts_3747_, v_declName_3748_, v___x_3770_);
return v___x_3771_;
}
}
}
else
{
lean_dec_ref(v_pre_3763_);
lean_dec_ref(v_declName_3762_);
lean_dec(v_declName_3748_);
lean_dec_ref(v_env_3746_);
goto v___jp_3749_;
}
}
else
{
lean_dec(v_pre_3763_);
lean_dec_ref(v_declName_3762_);
lean_dec(v_declName_3748_);
lean_dec_ref(v_env_3746_);
goto v___jp_3749_;
}
}
else
{
lean_dec(v_declName_3762_);
lean_dec(v_declName_3748_);
lean_dec_ref(v_env_3746_);
goto v___jp_3749_;
}
}
else
{
lean_dec_ref(v___x_3761_);
lean_dec(v_declName_3748_);
lean_dec_ref(v_env_3746_);
goto v___jp_3749_;
}
}
v___jp_3749_:
{
lean_object* v___x_3750_; 
v___x_3750_ = ((lean_object*)(l_Lean_mkAttributeImplOfConstantUnsafe___closed__1));
return v___x_3750_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkAttributeImplOfConstantUnsafe___boxed(lean_object* v_env_3772_, lean_object* v_opts_3773_, lean_object* v_declName_3774_){
_start:
{
lean_object* v_res_3775_; 
v_res_3775_ = l_Lean_mkAttributeImplOfConstantUnsafe(v_env_3772_, v_opts_3773_, v_declName_3774_);
lean_dec_ref(v_opts_3773_);
return v_res_3775_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg(lean_object* v_as_3776_, size_t v_i_3777_, size_t v_stop_3778_, lean_object* v_b_3779_){
_start:
{
uint8_t v___x_3781_; 
v___x_3781_ = lean_usize_dec_eq(v_i_3777_, v_stop_3778_);
if (v___x_3781_ == 0)
{
lean_object* v___x_3782_; lean_object* v___x_3783_; 
v___x_3782_ = lean_array_uget_borrowed(v_as_3776_, v_i_3777_);
lean_inc(v___x_3782_);
v___x_3783_ = l_Lean_mkAttributeImplOfEntry(v___x_3782_);
if (lean_obj_tag(v___x_3783_) == 0)
{
lean_object* v_a_3784_; lean_object* v_toAttributeImplCore_3785_; lean_object* v_name_3786_; lean_object* v___x_3787_; size_t v___x_3788_; size_t v___x_3789_; 
v_a_3784_ = lean_ctor_get(v___x_3783_, 0);
lean_inc(v_a_3784_);
lean_dec_ref(v___x_3783_);
v_toAttributeImplCore_3785_ = lean_ctor_get(v_a_3784_, 0);
v_name_3786_ = lean_ctor_get(v_toAttributeImplCore_3785_, 1);
lean_inc(v_name_3786_);
v___x_3787_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1___redArg(v_b_3779_, v_name_3786_, v_a_3784_);
v___x_3788_ = ((size_t)1ULL);
v___x_3789_ = lean_usize_add(v_i_3777_, v___x_3788_);
v_i_3777_ = v___x_3789_;
v_b_3779_ = v___x_3787_;
goto _start;
}
else
{
lean_object* v_a_3791_; lean_object* v___x_3793_; uint8_t v_isShared_3794_; uint8_t v_isSharedCheck_3798_; 
lean_dec_ref(v_b_3779_);
v_a_3791_ = lean_ctor_get(v___x_3783_, 0);
v_isSharedCheck_3798_ = !lean_is_exclusive(v___x_3783_);
if (v_isSharedCheck_3798_ == 0)
{
v___x_3793_ = v___x_3783_;
v_isShared_3794_ = v_isSharedCheck_3798_;
goto v_resetjp_3792_;
}
else
{
lean_inc(v_a_3791_);
lean_dec(v___x_3783_);
v___x_3793_ = lean_box(0);
v_isShared_3794_ = v_isSharedCheck_3798_;
goto v_resetjp_3792_;
}
v_resetjp_3792_:
{
lean_object* v___x_3796_; 
if (v_isShared_3794_ == 0)
{
v___x_3796_ = v___x_3793_;
goto v_reusejp_3795_;
}
else
{
lean_object* v_reuseFailAlloc_3797_; 
v_reuseFailAlloc_3797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3797_, 0, v_a_3791_);
v___x_3796_ = v_reuseFailAlloc_3797_;
goto v_reusejp_3795_;
}
v_reusejp_3795_:
{
return v___x_3796_;
}
}
}
}
else
{
lean_object* v___x_3799_; 
v___x_3799_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3799_, 0, v_b_3779_);
return v___x_3799_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg___boxed(lean_object* v_as_3800_, lean_object* v_i_3801_, lean_object* v_stop_3802_, lean_object* v_b_3803_, lean_object* v___y_3804_){
_start:
{
size_t v_i_boxed_3805_; size_t v_stop_boxed_3806_; lean_object* v_res_3807_; 
v_i_boxed_3805_ = lean_unbox_usize(v_i_3801_);
lean_dec(v_i_3801_);
v_stop_boxed_3806_ = lean_unbox_usize(v_stop_3802_);
lean_dec(v_stop_3802_);
v_res_3807_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg(v_as_3800_, v_i_boxed_3805_, v_stop_boxed_3806_, v_b_3803_);
lean_dec_ref(v_as_3800_);
return v_res_3807_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__1(lean_object* v_as_3808_, size_t v_i_3809_, size_t v_stop_3810_, lean_object* v_b_3811_, lean_object* v___y_3812_){
_start:
{
lean_object* v_a_3815_; lean_object* v___y_3820_; uint8_t v___x_3822_; 
v___x_3822_ = lean_usize_dec_eq(v_i_3809_, v_stop_3810_);
if (v___x_3822_ == 0)
{
lean_object* v___x_3823_; lean_object* v___x_3824_; lean_object* v___x_3825_; uint8_t v___x_3826_; 
v___x_3823_ = lean_array_uget_borrowed(v_as_3808_, v_i_3809_);
v___x_3824_ = lean_unsigned_to_nat(0u);
v___x_3825_ = lean_array_get_size(v___x_3823_);
v___x_3826_ = lean_nat_dec_lt(v___x_3824_, v___x_3825_);
if (v___x_3826_ == 0)
{
v_a_3815_ = v_b_3811_;
goto v___jp_3814_;
}
else
{
uint8_t v___x_3827_; 
v___x_3827_ = lean_nat_dec_le(v___x_3825_, v___x_3825_);
if (v___x_3827_ == 0)
{
if (v___x_3826_ == 0)
{
v_a_3815_ = v_b_3811_;
goto v___jp_3814_;
}
else
{
size_t v___x_3828_; size_t v___x_3829_; lean_object* v___x_3830_; 
v___x_3828_ = ((size_t)0ULL);
v___x_3829_ = lean_usize_of_nat(v___x_3825_);
v___x_3830_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg(v___x_3823_, v___x_3828_, v___x_3829_, v_b_3811_);
v___y_3820_ = v___x_3830_;
goto v___jp_3819_;
}
}
else
{
size_t v___x_3831_; size_t v___x_3832_; lean_object* v___x_3833_; 
v___x_3831_ = ((size_t)0ULL);
v___x_3832_ = lean_usize_of_nat(v___x_3825_);
v___x_3833_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg(v___x_3823_, v___x_3831_, v___x_3832_, v_b_3811_);
v___y_3820_ = v___x_3833_;
goto v___jp_3819_;
}
}
}
else
{
lean_object* v___x_3834_; 
v___x_3834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3834_, 0, v_b_3811_);
return v___x_3834_;
}
v___jp_3814_:
{
size_t v___x_3816_; size_t v___x_3817_; 
v___x_3816_ = ((size_t)1ULL);
v___x_3817_ = lean_usize_add(v_i_3809_, v___x_3816_);
v_i_3809_ = v___x_3817_;
v_b_3811_ = v_a_3815_;
goto _start;
}
v___jp_3819_:
{
if (lean_obj_tag(v___y_3820_) == 0)
{
lean_object* v_a_3821_; 
v_a_3821_ = lean_ctor_get(v___y_3820_, 0);
lean_inc(v_a_3821_);
lean_dec_ref(v___y_3820_);
v_a_3815_ = v_a_3821_;
goto v___jp_3814_;
}
else
{
return v___y_3820_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__1___boxed(lean_object* v_as_3835_, lean_object* v_i_3836_, lean_object* v_stop_3837_, lean_object* v_b_3838_, lean_object* v___y_3839_, lean_object* v___y_3840_){
_start:
{
size_t v_i_boxed_3841_; size_t v_stop_boxed_3842_; lean_object* v_res_3843_; 
v_i_boxed_3841_ = lean_unbox_usize(v_i_3836_);
lean_dec(v_i_3836_);
v_stop_boxed_3842_ = lean_unbox_usize(v_stop_3837_);
lean_dec(v_stop_3837_);
v_res_3843_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__1(v_as_3835_, v_i_boxed_3841_, v_stop_boxed_3842_, v_b_3838_, v___y_3839_);
lean_dec_ref(v___y_3839_);
lean_dec_ref(v_as_3835_);
return v_res_3843_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_AttributeExtension_addImported(lean_object* v_es_3844_, lean_object* v_a_3845_){
_start:
{
lean_object* v_a_3848_; lean_object* v___y_3853_; lean_object* v___x_3863_; lean_object* v___x_3864_; lean_object* v___x_3865_; lean_object* v___x_3866_; uint8_t v___x_3867_; 
v___x_3863_ = l_Lean_attributeMapRef;
v___x_3864_ = lean_st_ref_get(v___x_3863_);
v___x_3865_ = lean_unsigned_to_nat(0u);
v___x_3866_ = lean_array_get_size(v_es_3844_);
v___x_3867_ = lean_nat_dec_lt(v___x_3865_, v___x_3866_);
if (v___x_3867_ == 0)
{
v_a_3848_ = v___x_3864_;
goto v___jp_3847_;
}
else
{
uint8_t v___x_3868_; 
v___x_3868_ = lean_nat_dec_le(v___x_3866_, v___x_3866_);
if (v___x_3868_ == 0)
{
if (v___x_3867_ == 0)
{
v_a_3848_ = v___x_3864_;
goto v___jp_3847_;
}
else
{
size_t v___x_3869_; size_t v___x_3870_; lean_object* v___x_3871_; 
v___x_3869_ = ((size_t)0ULL);
v___x_3870_ = lean_usize_of_nat(v___x_3866_);
v___x_3871_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__1(v_es_3844_, v___x_3869_, v___x_3870_, v___x_3864_, v_a_3845_);
v___y_3853_ = v___x_3871_;
goto v___jp_3852_;
}
}
else
{
size_t v___x_3872_; size_t v___x_3873_; lean_object* v___x_3874_; 
v___x_3872_ = ((size_t)0ULL);
v___x_3873_ = lean_usize_of_nat(v___x_3866_);
v___x_3874_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__1(v_es_3844_, v___x_3872_, v___x_3873_, v___x_3864_, v_a_3845_);
v___y_3853_ = v___x_3874_;
goto v___jp_3852_;
}
}
v___jp_3847_:
{
lean_object* v___x_3849_; lean_object* v___x_3850_; lean_object* v___x_3851_; 
v___x_3849_ = lean_box(0);
v___x_3850_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3850_, 0, v___x_3849_);
lean_ctor_set(v___x_3850_, 1, v_a_3848_);
v___x_3851_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3851_, 0, v___x_3850_);
return v___x_3851_;
}
v___jp_3852_:
{
if (lean_obj_tag(v___y_3853_) == 0)
{
lean_object* v_a_3854_; 
v_a_3854_ = lean_ctor_get(v___y_3853_, 0);
lean_inc(v_a_3854_);
lean_dec_ref(v___y_3853_);
v_a_3848_ = v_a_3854_;
goto v___jp_3847_;
}
else
{
lean_object* v_a_3855_; lean_object* v___x_3857_; uint8_t v_isShared_3858_; uint8_t v_isSharedCheck_3862_; 
v_a_3855_ = lean_ctor_get(v___y_3853_, 0);
v_isSharedCheck_3862_ = !lean_is_exclusive(v___y_3853_);
if (v_isSharedCheck_3862_ == 0)
{
v___x_3857_ = v___y_3853_;
v_isShared_3858_ = v_isSharedCheck_3862_;
goto v_resetjp_3856_;
}
else
{
lean_inc(v_a_3855_);
lean_dec(v___y_3853_);
v___x_3857_ = lean_box(0);
v_isShared_3858_ = v_isSharedCheck_3862_;
goto v_resetjp_3856_;
}
v_resetjp_3856_:
{
lean_object* v___x_3860_; 
if (v_isShared_3858_ == 0)
{
v___x_3860_ = v___x_3857_;
goto v_reusejp_3859_;
}
else
{
lean_object* v_reuseFailAlloc_3861_; 
v_reuseFailAlloc_3861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3861_, 0, v_a_3855_);
v___x_3860_ = v_reuseFailAlloc_3861_;
goto v_reusejp_3859_;
}
v_reusejp_3859_:
{
return v___x_3860_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_AttributeExtension_addImported___boxed(lean_object* v_es_3875_, lean_object* v_a_3876_, lean_object* v_a_3877_){
_start:
{
lean_object* v_res_3878_; 
v_res_3878_ = l___private_Lean_Attributes_0__Lean_AttributeExtension_addImported(v_es_3875_, v_a_3876_);
lean_dec_ref(v_a_3876_);
lean_dec_ref(v_es_3875_);
return v_res_3878_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0(lean_object* v_as_3879_, size_t v_i_3880_, size_t v_stop_3881_, lean_object* v_b_3882_, lean_object* v___y_3883_){
_start:
{
lean_object* v___x_3885_; 
v___x_3885_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg(v_as_3879_, v_i_3880_, v_stop_3881_, v_b_3882_);
return v___x_3885_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___boxed(lean_object* v_as_3886_, lean_object* v_i_3887_, lean_object* v_stop_3888_, lean_object* v_b_3889_, lean_object* v___y_3890_, lean_object* v___y_3891_){
_start:
{
size_t v_i_boxed_3892_; size_t v_stop_boxed_3893_; lean_object* v_res_3894_; 
v_i_boxed_3892_ = lean_unbox_usize(v_i_3887_);
lean_dec(v_i_3887_);
v_stop_boxed_3893_ = lean_unbox_usize(v_stop_3888_);
lean_dec(v_stop_3888_);
v_res_3894_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0(v_as_3886_, v_i_boxed_3892_, v_stop_boxed_3893_, v_b_3889_, v___y_3890_);
lean_dec_ref(v___y_3890_);
lean_dec_ref(v_as_3886_);
return v_res_3894_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_addAttrEntry(lean_object* v_s_3895_, lean_object* v_e_3896_){
_start:
{
lean_object* v_snd_3897_; lean_object* v_toAttributeImplCore_3898_; lean_object* v_fst_3899_; lean_object* v___x_3901_; uint8_t v_isShared_3902_; uint8_t v_isSharedCheck_3917_; 
v_snd_3897_ = lean_ctor_get(v_e_3896_, 1);
lean_inc(v_snd_3897_);
v_toAttributeImplCore_3898_ = lean_ctor_get(v_snd_3897_, 0);
v_fst_3899_ = lean_ctor_get(v_e_3896_, 0);
v_isSharedCheck_3917_ = !lean_is_exclusive(v_e_3896_);
if (v_isSharedCheck_3917_ == 0)
{
lean_object* v_unused_3918_; 
v_unused_3918_ = lean_ctor_get(v_e_3896_, 1);
lean_dec(v_unused_3918_);
v___x_3901_ = v_e_3896_;
v_isShared_3902_ = v_isSharedCheck_3917_;
goto v_resetjp_3900_;
}
else
{
lean_inc(v_fst_3899_);
lean_dec(v_e_3896_);
v___x_3901_ = lean_box(0);
v_isShared_3902_ = v_isSharedCheck_3917_;
goto v_resetjp_3900_;
}
v_resetjp_3900_:
{
lean_object* v_newEntries_3903_; lean_object* v_map_3904_; lean_object* v___x_3906_; uint8_t v_isShared_3907_; uint8_t v_isSharedCheck_3916_; 
v_newEntries_3903_ = lean_ctor_get(v_s_3895_, 0);
v_map_3904_ = lean_ctor_get(v_s_3895_, 1);
v_isSharedCheck_3916_ = !lean_is_exclusive(v_s_3895_);
if (v_isSharedCheck_3916_ == 0)
{
v___x_3906_ = v_s_3895_;
v_isShared_3907_ = v_isSharedCheck_3916_;
goto v_resetjp_3905_;
}
else
{
lean_inc(v_map_3904_);
lean_inc(v_newEntries_3903_);
lean_dec(v_s_3895_);
v___x_3906_ = lean_box(0);
v_isShared_3907_ = v_isSharedCheck_3916_;
goto v_resetjp_3905_;
}
v_resetjp_3905_:
{
lean_object* v_name_3908_; lean_object* v___x_3910_; 
v_name_3908_ = lean_ctor_get(v_toAttributeImplCore_3898_, 1);
lean_inc(v_name_3908_);
if (v_isShared_3902_ == 0)
{
lean_ctor_set_tag(v___x_3901_, 1);
lean_ctor_set(v___x_3901_, 1, v_newEntries_3903_);
v___x_3910_ = v___x_3901_;
goto v_reusejp_3909_;
}
else
{
lean_object* v_reuseFailAlloc_3915_; 
v_reuseFailAlloc_3915_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3915_, 0, v_fst_3899_);
lean_ctor_set(v_reuseFailAlloc_3915_, 1, v_newEntries_3903_);
v___x_3910_ = v_reuseFailAlloc_3915_;
goto v_reusejp_3909_;
}
v_reusejp_3909_:
{
lean_object* v___x_3911_; lean_object* v___x_3913_; 
v___x_3911_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1___redArg(v_map_3904_, v_name_3908_, v_snd_3897_);
if (v_isShared_3907_ == 0)
{
lean_ctor_set(v___x_3906_, 1, v___x_3911_);
lean_ctor_set(v___x_3906_, 0, v___x_3910_);
v___x_3913_ = v___x_3906_;
goto v_reusejp_3912_;
}
else
{
lean_object* v_reuseFailAlloc_3914_; 
v_reuseFailAlloc_3914_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3914_, 0, v___x_3910_);
lean_ctor_set(v_reuseFailAlloc_3914_, 1, v___x_3911_);
v___x_3913_ = v_reuseFailAlloc_3914_;
goto v_reusejp_3912_;
}
v_reusejp_3912_:
{
return v___x_3913_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(lean_object* v_x_3919_, lean_object* v_s_3920_, uint8_t v_x_3921_){
_start:
{
lean_object* v_newEntries_3922_; lean_object* v___x_3923_; lean_object* v___x_3924_; 
v_newEntries_3922_ = lean_ctor_get(v_s_3920_, 0);
lean_inc(v_newEntries_3922_);
lean_dec_ref(v_s_3920_);
v___x_3923_ = l_List_reverse___redArg(v_newEntries_3922_);
v___x_3924_ = lean_array_mk(v___x_3923_);
return v___x_3924_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2____boxed(lean_object* v_x_3925_, lean_object* v_s_3926_, lean_object* v_x_3927_){
_start:
{
uint8_t v_x_90__boxed_3928_; lean_object* v_res_3929_; 
v_x_90__boxed_3928_ = lean_unbox(v_x_3927_);
v_res_3929_ = l_Lean_initFn___lam__0_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(v_x_3925_, v_s_3926_, v_x_90__boxed_3928_);
lean_dec_ref(v_x_3925_);
return v_res_3929_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__1_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(lean_object* v_s_3930_){
_start:
{
lean_object* v_newEntries_3931_; lean_object* v___x_3933_; uint8_t v_isShared_3934_; uint8_t v_isSharedCheck_3942_; 
v_newEntries_3931_ = lean_ctor_get(v_s_3930_, 0);
v_isSharedCheck_3942_ = !lean_is_exclusive(v_s_3930_);
if (v_isSharedCheck_3942_ == 0)
{
lean_object* v_unused_3943_; 
v_unused_3943_ = lean_ctor_get(v_s_3930_, 1);
lean_dec(v_unused_3943_);
v___x_3933_ = v_s_3930_;
v_isShared_3934_ = v_isSharedCheck_3942_;
goto v_resetjp_3932_;
}
else
{
lean_inc(v_newEntries_3931_);
lean_dec(v_s_3930_);
v___x_3933_ = lean_box(0);
v_isShared_3934_ = v_isSharedCheck_3942_;
goto v_resetjp_3932_;
}
v_resetjp_3932_:
{
lean_object* v___x_3935_; lean_object* v___x_3936_; lean_object* v___x_3937_; lean_object* v___x_3938_; lean_object* v___x_3940_; 
v___x_3935_ = ((lean_object*)(l_Lean_registerTagAttribute___lam__2___closed__4));
v___x_3936_ = l_List_lengthTR___redArg(v_newEntries_3931_);
lean_dec(v_newEntries_3931_);
v___x_3937_ = l_Nat_reprFast(v___x_3936_);
v___x_3938_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3938_, 0, v___x_3937_);
if (v_isShared_3934_ == 0)
{
lean_ctor_set_tag(v___x_3933_, 5);
lean_ctor_set(v___x_3933_, 1, v___x_3938_);
lean_ctor_set(v___x_3933_, 0, v___x_3935_);
v___x_3940_ = v___x_3933_;
goto v_reusejp_3939_;
}
else
{
lean_object* v_reuseFailAlloc_3941_; 
v_reuseFailAlloc_3941_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3941_, 0, v___x_3935_);
lean_ctor_set(v_reuseFailAlloc_3941_, 1, v___x_3938_);
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
LEAN_EXPORT lean_object* l_Lean_initFn___lam__2_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(lean_object* v_s_3944_){
_start:
{
lean_object* v_newEntries_3945_; lean_object* v___x_3946_; lean_object* v___x_3947_; 
v_newEntries_3945_ = lean_ctor_get(v_s_3944_, 0);
lean_inc(v_newEntries_3945_);
lean_dec_ref(v_s_3944_);
v___x_3946_ = l_List_reverse___redArg(v_newEntries_3945_);
v___x_3947_ = lean_array_mk(v___x_3946_);
return v___x_3947_;
}
}
static lean_object* _init_l_Lean_initFn___closed__7_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3957_; lean_object* v___x_3958_; lean_object* v___f_3959_; lean_object* v___f_3960_; lean_object* v___x_3961_; lean_object* v___x_3962_; lean_object* v___x_3963_; lean_object* v___x_3964_; lean_object* v___x_3965_; 
v___x_3957_ = lean_box(0);
v___x_3958_ = lean_box(2);
v___f_3959_ = ((lean_object*)(l_Lean_initFn___closed__1_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___f_3960_ = ((lean_object*)(l_Lean_initFn___closed__0_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___x_3961_ = ((lean_object*)(l_Lean_initFn___closed__6_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___x_3962_ = ((lean_object*)(l_Lean_initFn___closed__5_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___x_3963_ = lean_alloc_closure((void*)(l___private_Lean_Attributes_0__Lean_AttributeExtension_mkInitial___boxed), 1, 0);
v___x_3964_ = ((lean_object*)(l_Lean_initFn___closed__4_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___x_3965_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_3965_, 0, v___x_3964_);
lean_ctor_set(v___x_3965_, 1, v___x_3963_);
lean_ctor_set(v___x_3965_, 2, v___x_3962_);
lean_ctor_set(v___x_3965_, 3, v___x_3961_);
lean_ctor_set(v___x_3965_, 4, v___f_3960_);
lean_ctor_set(v___x_3965_, 5, v___f_3959_);
lean_ctor_set(v___x_3965_, 6, v___x_3958_);
lean_ctor_set(v___x_3965_, 7, v___x_3957_);
return v___x_3965_;
}
}
static lean_object* _init_l_Lean_initFn___closed__8_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_3966_; lean_object* v___x_3967_; lean_object* v___x_3968_; 
v___f_3966_ = ((lean_object*)(l_Lean_initFn___closed__2_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___x_3967_ = lean_obj_once(&l_Lean_initFn___closed__7_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_, &l_Lean_initFn___closed__7_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2__once, _init_l_Lean_initFn___closed__7_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_);
v___x_3968_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3968_, 0, v___x_3967_);
lean_ctor_set(v___x_3968_, 1, v___f_3966_);
return v___x_3968_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3970_; lean_object* v___x_3971_; 
v___x_3970_ = lean_obj_once(&l_Lean_initFn___closed__8_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_, &l_Lean_initFn___closed__8_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2__once, _init_l_Lean_initFn___closed__8_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_);
v___x_3971_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_3970_);
return v___x_3971_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2____boxed(lean_object* v_a_3972_){
_start:
{
lean_object* v_res_3973_; 
v_res_3973_ = l_Lean_initFn_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_();
return v_res_3973_;
}
}
LEAN_EXPORT lean_object* lean_is_attribute(lean_object* v_n_3974_){
_start:
{
lean_object* v___x_3976_; lean_object* v___x_3977_; uint8_t v___x_3978_; lean_object* v___x_3979_; lean_object* v___x_3980_; 
v___x_3976_ = l_Lean_attributeMapRef;
v___x_3977_ = lean_st_ref_get(v___x_3976_);
v___x_3978_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(v___x_3977_, v_n_3974_);
lean_dec(v_n_3974_);
lean_dec(v___x_3977_);
v___x_3979_ = lean_box(v___x_3978_);
v___x_3980_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3980_, 0, v___x_3979_);
return v___x_3980_;
}
}
LEAN_EXPORT lean_object* l_Lean_isBuiltinAttribute___boxed(lean_object* v_n_3981_, lean_object* v_a_3982_){
_start:
{
lean_object* v_res_3983_; 
v_res_3983_ = lean_is_attribute(v_n_3981_);
return v_res_3983_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_getBuiltinAttributeNames_spec__0(lean_object* v_x_3984_, lean_object* v_x_3985_){
_start:
{
if (lean_obj_tag(v_x_3985_) == 0)
{
return v_x_3984_;
}
else
{
lean_object* v_key_3986_; lean_object* v_tail_3987_; lean_object* v___x_3988_; 
v_key_3986_ = lean_ctor_get(v_x_3985_, 0);
v_tail_3987_ = lean_ctor_get(v_x_3985_, 2);
lean_inc(v_key_3986_);
v___x_3988_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3988_, 0, v_key_3986_);
lean_ctor_set(v___x_3988_, 1, v_x_3984_);
v_x_3984_ = v___x_3988_;
v_x_3985_ = v_tail_3987_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_getBuiltinAttributeNames_spec__0___boxed(lean_object* v_x_3990_, lean_object* v_x_3991_){
_start:
{
lean_object* v_res_3992_; 
v_res_3992_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_getBuiltinAttributeNames_spec__0(v_x_3990_, v_x_3991_);
lean_dec(v_x_3991_);
return v_res_3992_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1(lean_object* v_as_3993_, size_t v_i_3994_, size_t v_stop_3995_, lean_object* v_b_3996_){
_start:
{
uint8_t v___x_3997_; 
v___x_3997_ = lean_usize_dec_eq(v_i_3994_, v_stop_3995_);
if (v___x_3997_ == 0)
{
lean_object* v___x_3998_; lean_object* v___x_3999_; size_t v___x_4000_; size_t v___x_4001_; 
v___x_3998_ = lean_array_uget_borrowed(v_as_3993_, v_i_3994_);
v___x_3999_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_getBuiltinAttributeNames_spec__0(v_b_3996_, v___x_3998_);
v___x_4000_ = ((size_t)1ULL);
v___x_4001_ = lean_usize_add(v_i_3994_, v___x_4000_);
v_i_3994_ = v___x_4001_;
v_b_3996_ = v___x_3999_;
goto _start;
}
else
{
return v_b_3996_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1___boxed(lean_object* v_as_4003_, lean_object* v_i_4004_, lean_object* v_stop_4005_, lean_object* v_b_4006_){
_start:
{
size_t v_i_boxed_4007_; size_t v_stop_boxed_4008_; lean_object* v_res_4009_; 
v_i_boxed_4007_ = lean_unbox_usize(v_i_4004_);
lean_dec(v_i_4004_);
v_stop_boxed_4008_ = lean_unbox_usize(v_stop_4005_);
lean_dec(v_stop_4005_);
v_res_4009_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1(v_as_4003_, v_i_boxed_4007_, v_stop_boxed_4008_, v_b_4006_);
lean_dec_ref(v_as_4003_);
return v_res_4009_;
}
}
LEAN_EXPORT lean_object* l_Lean_getBuiltinAttributeNames(){
_start:
{
lean_object* v___x_4011_; lean_object* v___x_4012_; lean_object* v_buckets_4013_; lean_object* v___x_4014_; lean_object* v___x_4015_; lean_object* v___x_4016_; uint8_t v___x_4017_; 
v___x_4011_ = l_Lean_attributeMapRef;
v___x_4012_ = lean_st_ref_get(v___x_4011_);
v_buckets_4013_ = lean_ctor_get(v___x_4012_, 1);
lean_inc_ref(v_buckets_4013_);
lean_dec(v___x_4012_);
v___x_4014_ = lean_box(0);
v___x_4015_ = lean_unsigned_to_nat(0u);
v___x_4016_ = lean_array_get_size(v_buckets_4013_);
v___x_4017_ = lean_nat_dec_lt(v___x_4015_, v___x_4016_);
if (v___x_4017_ == 0)
{
lean_object* v___x_4018_; 
lean_dec_ref(v_buckets_4013_);
v___x_4018_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4018_, 0, v___x_4014_);
return v___x_4018_;
}
else
{
uint8_t v___x_4019_; 
v___x_4019_ = lean_nat_dec_le(v___x_4016_, v___x_4016_);
if (v___x_4019_ == 0)
{
if (v___x_4017_ == 0)
{
lean_object* v___x_4020_; 
lean_dec_ref(v_buckets_4013_);
v___x_4020_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4020_, 0, v___x_4014_);
return v___x_4020_;
}
else
{
size_t v___x_4021_; size_t v___x_4022_; lean_object* v___x_4023_; lean_object* v___x_4024_; 
v___x_4021_ = ((size_t)0ULL);
v___x_4022_ = lean_usize_of_nat(v___x_4016_);
v___x_4023_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1(v_buckets_4013_, v___x_4021_, v___x_4022_, v___x_4014_);
lean_dec_ref(v_buckets_4013_);
v___x_4024_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4024_, 0, v___x_4023_);
return v___x_4024_;
}
}
else
{
size_t v___x_4025_; size_t v___x_4026_; lean_object* v___x_4027_; lean_object* v___x_4028_; 
v___x_4025_ = ((size_t)0ULL);
v___x_4026_ = lean_usize_of_nat(v___x_4016_);
v___x_4027_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1(v_buckets_4013_, v___x_4025_, v___x_4026_, v___x_4014_);
lean_dec_ref(v_buckets_4013_);
v___x_4028_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4028_, 0, v___x_4027_);
return v___x_4028_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getBuiltinAttributeNames___boxed(lean_object* v_a_4029_){
_start:
{
lean_object* v_res_4030_; 
v_res_4030_ = l_Lean_getBuiltinAttributeNames();
return v_res_4030_;
}
}
LEAN_EXPORT lean_object* l_Lean_getBuiltinAttributeImpl(lean_object* v_attrName_4032_){
_start:
{
lean_object* v___x_4034_; lean_object* v___x_4035_; lean_object* v___x_4036_; 
v___x_4034_ = l_Lean_attributeMapRef;
v___x_4035_ = lean_st_ref_get(v___x_4034_);
v___x_4036_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(v___x_4035_, v_attrName_4032_);
lean_dec(v___x_4035_);
if (lean_obj_tag(v___x_4036_) == 0)
{
lean_object* v___x_4037_; uint8_t v___x_4038_; lean_object* v___x_4039_; lean_object* v___x_4040_; lean_object* v___x_4041_; lean_object* v___x_4042_; lean_object* v___x_4043_; lean_object* v___x_4044_; 
v___x_4037_ = ((lean_object*)(l_Lean_getBuiltinAttributeImpl___closed__0));
v___x_4038_ = 1;
v___x_4039_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_attrName_4032_, v___x_4038_);
v___x_4040_ = lean_string_append(v___x_4037_, v___x_4039_);
lean_dec_ref(v___x_4039_);
v___x_4041_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__4));
v___x_4042_ = lean_string_append(v___x_4040_, v___x_4041_);
v___x_4043_ = lean_mk_io_user_error(v___x_4042_);
v___x_4044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4044_, 0, v___x_4043_);
return v___x_4044_;
}
else
{
lean_object* v_val_4045_; lean_object* v___x_4047_; uint8_t v_isShared_4048_; uint8_t v_isSharedCheck_4052_; 
lean_dec(v_attrName_4032_);
v_val_4045_ = lean_ctor_get(v___x_4036_, 0);
v_isSharedCheck_4052_ = !lean_is_exclusive(v___x_4036_);
if (v_isSharedCheck_4052_ == 0)
{
v___x_4047_ = v___x_4036_;
v_isShared_4048_ = v_isSharedCheck_4052_;
goto v_resetjp_4046_;
}
else
{
lean_inc(v_val_4045_);
lean_dec(v___x_4036_);
v___x_4047_ = lean_box(0);
v_isShared_4048_ = v_isSharedCheck_4052_;
goto v_resetjp_4046_;
}
v_resetjp_4046_:
{
lean_object* v___x_4050_; 
if (v_isShared_4048_ == 0)
{
lean_ctor_set_tag(v___x_4047_, 0);
v___x_4050_ = v___x_4047_;
goto v_reusejp_4049_;
}
else
{
lean_object* v_reuseFailAlloc_4051_; 
v_reuseFailAlloc_4051_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4051_, 0, v_val_4045_);
v___x_4050_ = v_reuseFailAlloc_4051_;
goto v_reusejp_4049_;
}
v_reusejp_4049_:
{
return v___x_4050_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getBuiltinAttributeImpl___boxed(lean_object* v_attrName_4053_, lean_object* v_a_4054_){
_start:
{
lean_object* v_res_4055_; 
v_res_4055_ = l_Lean_getBuiltinAttributeImpl(v_attrName_4053_);
return v_res_4055_;
}
}
LEAN_EXPORT lean_object* lean_attribute_application_time(lean_object* v_n_4056_){
_start:
{
lean_object* v___x_4058_; 
v___x_4058_ = l_Lean_getBuiltinAttributeImpl(v_n_4056_);
if (lean_obj_tag(v___x_4058_) == 0)
{
lean_object* v_a_4059_; lean_object* v___x_4061_; uint8_t v_isShared_4062_; uint8_t v_isSharedCheck_4069_; 
v_a_4059_ = lean_ctor_get(v___x_4058_, 0);
v_isSharedCheck_4069_ = !lean_is_exclusive(v___x_4058_);
if (v_isSharedCheck_4069_ == 0)
{
v___x_4061_ = v___x_4058_;
v_isShared_4062_ = v_isSharedCheck_4069_;
goto v_resetjp_4060_;
}
else
{
lean_inc(v_a_4059_);
lean_dec(v___x_4058_);
v___x_4061_ = lean_box(0);
v_isShared_4062_ = v_isSharedCheck_4069_;
goto v_resetjp_4060_;
}
v_resetjp_4060_:
{
lean_object* v_toAttributeImplCore_4063_; uint8_t v_applicationTime_4064_; lean_object* v___x_4065_; lean_object* v___x_4067_; 
v_toAttributeImplCore_4063_ = lean_ctor_get(v_a_4059_, 0);
lean_inc_ref(v_toAttributeImplCore_4063_);
lean_dec(v_a_4059_);
v_applicationTime_4064_ = lean_ctor_get_uint8(v_toAttributeImplCore_4063_, sizeof(void*)*3);
lean_dec_ref(v_toAttributeImplCore_4063_);
v___x_4065_ = lean_box(v_applicationTime_4064_);
if (v_isShared_4062_ == 0)
{
lean_ctor_set(v___x_4061_, 0, v___x_4065_);
v___x_4067_ = v___x_4061_;
goto v_reusejp_4066_;
}
else
{
lean_object* v_reuseFailAlloc_4068_; 
v_reuseFailAlloc_4068_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4068_, 0, v___x_4065_);
v___x_4067_ = v_reuseFailAlloc_4068_;
goto v_reusejp_4066_;
}
v_reusejp_4066_:
{
return v___x_4067_;
}
}
}
else
{
lean_object* v_a_4070_; lean_object* v___x_4072_; uint8_t v_isShared_4073_; uint8_t v_isSharedCheck_4077_; 
v_a_4070_ = lean_ctor_get(v___x_4058_, 0);
v_isSharedCheck_4077_ = !lean_is_exclusive(v___x_4058_);
if (v_isSharedCheck_4077_ == 0)
{
v___x_4072_ = v___x_4058_;
v_isShared_4073_ = v_isSharedCheck_4077_;
goto v_resetjp_4071_;
}
else
{
lean_inc(v_a_4070_);
lean_dec(v___x_4058_);
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
}
LEAN_EXPORT lean_object* l_Lean_getBuiltinAttributeApplicationTime___boxed(lean_object* v_n_4078_, lean_object* v_a_4079_){
_start:
{
lean_object* v_res_4080_; 
v_res_4080_ = lean_attribute_application_time(v_n_4078_);
return v_res_4080_;
}
}
LEAN_EXPORT uint8_t l_Lean_isAttribute(lean_object* v_env_4081_, lean_object* v_attrName_4082_){
_start:
{
lean_object* v___x_4083_; lean_object* v_toEnvExtension_4084_; lean_object* v_asyncMode_4085_; lean_object* v___x_4086_; lean_object* v___x_4087_; lean_object* v___x_4088_; lean_object* v_map_4089_; uint8_t v___x_4090_; 
v___x_4083_ = l_Lean_attributeExtension;
v_toEnvExtension_4084_ = lean_ctor_get(v___x_4083_, 0);
lean_inc_ref(v_toEnvExtension_4084_);
v_asyncMode_4085_ = lean_ctor_get(v_toEnvExtension_4084_, 2);
lean_inc(v_asyncMode_4085_);
lean_dec_ref(v_toEnvExtension_4084_);
v___x_4086_ = l_Lean_instInhabitedAttributeExtensionState_default;
v___x_4087_ = lean_box(0);
v___x_4088_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_4086_, v___x_4083_, v_env_4081_, v_asyncMode_4085_, v___x_4087_);
lean_dec(v_asyncMode_4085_);
v_map_4089_ = lean_ctor_get(v___x_4088_, 1);
lean_inc_ref(v_map_4089_);
lean_dec(v___x_4088_);
v___x_4090_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(v_map_4089_, v_attrName_4082_);
lean_dec_ref(v_map_4089_);
return v___x_4090_;
}
}
LEAN_EXPORT lean_object* l_Lean_isAttribute___boxed(lean_object* v_env_4091_, lean_object* v_attrName_4092_){
_start:
{
uint8_t v_res_4093_; lean_object* v_r_4094_; 
v_res_4093_ = l_Lean_isAttribute(v_env_4091_, v_attrName_4092_);
lean_dec(v_attrName_4092_);
v_r_4094_ = lean_box(v_res_4093_);
return v_r_4094_;
}
}
LEAN_EXPORT lean_object* l_Lean_getAttributeNames(lean_object* v_env_4095_){
_start:
{
lean_object* v___x_4096_; lean_object* v_toEnvExtension_4097_; lean_object* v_asyncMode_4098_; lean_object* v___x_4099_; lean_object* v___x_4100_; lean_object* v___x_4101_; lean_object* v_map_4102_; lean_object* v_buckets_4103_; lean_object* v___x_4104_; lean_object* v___x_4105_; lean_object* v___x_4106_; uint8_t v___x_4107_; 
v___x_4096_ = l_Lean_attributeExtension;
v_toEnvExtension_4097_ = lean_ctor_get(v___x_4096_, 0);
lean_inc_ref(v_toEnvExtension_4097_);
v_asyncMode_4098_ = lean_ctor_get(v_toEnvExtension_4097_, 2);
lean_inc(v_asyncMode_4098_);
lean_dec_ref(v_toEnvExtension_4097_);
v___x_4099_ = l_Lean_instInhabitedAttributeExtensionState_default;
v___x_4100_ = lean_box(0);
v___x_4101_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_4099_, v___x_4096_, v_env_4095_, v_asyncMode_4098_, v___x_4100_);
lean_dec(v_asyncMode_4098_);
v_map_4102_ = lean_ctor_get(v___x_4101_, 1);
lean_inc_ref(v_map_4102_);
lean_dec(v___x_4101_);
v_buckets_4103_ = lean_ctor_get(v_map_4102_, 1);
lean_inc_ref(v_buckets_4103_);
lean_dec_ref(v_map_4102_);
v___x_4104_ = lean_box(0);
v___x_4105_ = lean_unsigned_to_nat(0u);
v___x_4106_ = lean_array_get_size(v_buckets_4103_);
v___x_4107_ = lean_nat_dec_lt(v___x_4105_, v___x_4106_);
if (v___x_4107_ == 0)
{
lean_dec_ref(v_buckets_4103_);
return v___x_4104_;
}
else
{
uint8_t v___x_4108_; 
v___x_4108_ = lean_nat_dec_le(v___x_4106_, v___x_4106_);
if (v___x_4108_ == 0)
{
if (v___x_4107_ == 0)
{
lean_dec_ref(v_buckets_4103_);
return v___x_4104_;
}
else
{
size_t v___x_4109_; size_t v___x_4110_; lean_object* v___x_4111_; 
v___x_4109_ = ((size_t)0ULL);
v___x_4110_ = lean_usize_of_nat(v___x_4106_);
v___x_4111_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1(v_buckets_4103_, v___x_4109_, v___x_4110_, v___x_4104_);
lean_dec_ref(v_buckets_4103_);
return v___x_4111_;
}
}
else
{
size_t v___x_4112_; size_t v___x_4113_; lean_object* v___x_4114_; 
v___x_4112_ = ((size_t)0ULL);
v___x_4113_ = lean_usize_of_nat(v___x_4106_);
v___x_4114_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1(v_buckets_4103_, v___x_4112_, v___x_4113_, v___x_4104_);
lean_dec_ref(v_buckets_4103_);
return v___x_4114_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getAttributeImpl(lean_object* v_env_4115_, lean_object* v_attrName_4116_){
_start:
{
lean_object* v___x_4117_; lean_object* v_toEnvExtension_4118_; lean_object* v_asyncMode_4119_; lean_object* v___x_4120_; lean_object* v___x_4121_; lean_object* v___x_4122_; lean_object* v_map_4123_; lean_object* v___x_4124_; 
v___x_4117_ = l_Lean_attributeExtension;
v_toEnvExtension_4118_ = lean_ctor_get(v___x_4117_, 0);
lean_inc_ref(v_toEnvExtension_4118_);
v_asyncMode_4119_ = lean_ctor_get(v_toEnvExtension_4118_, 2);
lean_inc(v_asyncMode_4119_);
lean_dec_ref(v_toEnvExtension_4118_);
v___x_4120_ = l_Lean_instInhabitedAttributeExtensionState_default;
v___x_4121_ = lean_box(0);
v___x_4122_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_4120_, v___x_4117_, v_env_4115_, v_asyncMode_4119_, v___x_4121_);
lean_dec(v_asyncMode_4119_);
v_map_4123_ = lean_ctor_get(v___x_4122_, 1);
lean_inc_ref(v_map_4123_);
lean_dec(v___x_4122_);
v___x_4124_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(v_map_4123_, v_attrName_4116_);
lean_dec_ref(v_map_4123_);
if (lean_obj_tag(v___x_4124_) == 0)
{
lean_object* v___x_4125_; uint8_t v___x_4126_; lean_object* v___x_4127_; lean_object* v___x_4128_; lean_object* v___x_4129_; lean_object* v___x_4130_; lean_object* v___x_4131_; 
v___x_4125_ = ((lean_object*)(l_Lean_getBuiltinAttributeImpl___closed__0));
v___x_4126_ = 1;
v___x_4127_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_attrName_4116_, v___x_4126_);
v___x_4128_ = lean_string_append(v___x_4125_, v___x_4127_);
lean_dec_ref(v___x_4127_);
v___x_4129_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__4));
v___x_4130_ = lean_string_append(v___x_4128_, v___x_4129_);
v___x_4131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4131_, 0, v___x_4130_);
return v___x_4131_;
}
else
{
lean_object* v_val_4132_; lean_object* v___x_4134_; uint8_t v_isShared_4135_; uint8_t v_isSharedCheck_4139_; 
lean_dec(v_attrName_4116_);
v_val_4132_ = lean_ctor_get(v___x_4124_, 0);
v_isSharedCheck_4139_ = !lean_is_exclusive(v___x_4124_);
if (v_isSharedCheck_4139_ == 0)
{
v___x_4134_ = v___x_4124_;
v_isShared_4135_ = v_isSharedCheck_4139_;
goto v_resetjp_4133_;
}
else
{
lean_inc(v_val_4132_);
lean_dec(v___x_4124_);
v___x_4134_ = lean_box(0);
v_isShared_4135_ = v_isSharedCheck_4139_;
goto v_resetjp_4133_;
}
v_resetjp_4133_:
{
lean_object* v___x_4137_; 
if (v_isShared_4135_ == 0)
{
v___x_4137_ = v___x_4134_;
goto v_reusejp_4136_;
}
else
{
lean_object* v_reuseFailAlloc_4138_; 
v_reuseFailAlloc_4138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4138_, 0, v_val_4132_);
v___x_4137_ = v_reuseFailAlloc_4138_;
goto v_reusejp_4136_;
}
v_reusejp_4136_:
{
return v___x_4137_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerAttributeOfBuilder(lean_object* v_env_4140_, lean_object* v_builderId_4141_, lean_object* v_ref_4142_, lean_object* v_args_4143_){
_start:
{
lean_object* v_entry_4145_; lean_object* v___x_4146_; 
v_entry_4145_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_entry_4145_, 0, v_builderId_4141_);
lean_ctor_set(v_entry_4145_, 1, v_ref_4142_);
lean_ctor_set(v_entry_4145_, 2, v_args_4143_);
lean_inc_ref(v_entry_4145_);
v___x_4146_ = l_Lean_mkAttributeImplOfEntry(v_entry_4145_);
if (lean_obj_tag(v___x_4146_) == 0)
{
lean_object* v_a_4147_; lean_object* v___x_4149_; uint8_t v_isShared_4150_; uint8_t v_isSharedCheck_4172_; 
v_a_4147_ = lean_ctor_get(v___x_4146_, 0);
v_isSharedCheck_4172_ = !lean_is_exclusive(v___x_4146_);
if (v_isSharedCheck_4172_ == 0)
{
v___x_4149_ = v___x_4146_;
v_isShared_4150_ = v_isSharedCheck_4172_;
goto v_resetjp_4148_;
}
else
{
lean_inc(v_a_4147_);
lean_dec(v___x_4146_);
v___x_4149_ = lean_box(0);
v_isShared_4150_ = v_isSharedCheck_4172_;
goto v_resetjp_4148_;
}
v_resetjp_4148_:
{
lean_object* v_toAttributeImplCore_4151_; lean_object* v_name_4152_; uint8_t v___x_4153_; 
v_toAttributeImplCore_4151_ = lean_ctor_get(v_a_4147_, 0);
v_name_4152_ = lean_ctor_get(v_toAttributeImplCore_4151_, 1);
lean_inc_ref(v_env_4140_);
v___x_4153_ = l_Lean_isAttribute(v_env_4140_, v_name_4152_);
if (v___x_4153_ == 0)
{
lean_object* v___x_4154_; lean_object* v_toEnvExtension_4155_; lean_object* v_asyncMode_4156_; lean_object* v___x_4157_; lean_object* v___x_4158_; lean_object* v___x_4159_; lean_object* v___x_4161_; 
v___x_4154_ = l_Lean_attributeExtension;
v_toEnvExtension_4155_ = lean_ctor_get(v___x_4154_, 0);
lean_inc_ref(v_toEnvExtension_4155_);
v_asyncMode_4156_ = lean_ctor_get(v_toEnvExtension_4155_, 2);
lean_inc(v_asyncMode_4156_);
lean_dec_ref(v_toEnvExtension_4155_);
v___x_4157_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4157_, 0, v_entry_4145_);
lean_ctor_set(v___x_4157_, 1, v_a_4147_);
v___x_4158_ = lean_box(0);
v___x_4159_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_4154_, v_env_4140_, v___x_4157_, v_asyncMode_4156_, v___x_4158_);
lean_dec(v_asyncMode_4156_);
if (v_isShared_4150_ == 0)
{
lean_ctor_set(v___x_4149_, 0, v___x_4159_);
v___x_4161_ = v___x_4149_;
goto v_reusejp_4160_;
}
else
{
lean_object* v_reuseFailAlloc_4162_; 
v_reuseFailAlloc_4162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4162_, 0, v___x_4159_);
v___x_4161_ = v_reuseFailAlloc_4162_;
goto v_reusejp_4160_;
}
v_reusejp_4160_:
{
return v___x_4161_;
}
}
else
{
lean_object* v___x_4163_; lean_object* v___x_4164_; lean_object* v___x_4165_; lean_object* v___x_4166_; lean_object* v___x_4167_; lean_object* v___x_4168_; lean_object* v___x_4170_; 
lean_inc(v_name_4152_);
lean_dec(v_a_4147_);
lean_dec_ref(v_entry_4145_);
lean_dec_ref(v_env_4140_);
v___x_4163_ = ((lean_object*)(l_Lean_registerBuiltinAttribute___closed__2));
v___x_4164_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_4152_, v___x_4153_);
v___x_4165_ = lean_string_append(v___x_4163_, v___x_4164_);
lean_dec_ref(v___x_4164_);
v___x_4166_ = ((lean_object*)(l_Lean_registerBuiltinAttribute___closed__3));
v___x_4167_ = lean_string_append(v___x_4165_, v___x_4166_);
v___x_4168_ = lean_mk_io_user_error(v___x_4167_);
if (v_isShared_4150_ == 0)
{
lean_ctor_set_tag(v___x_4149_, 1);
lean_ctor_set(v___x_4149_, 0, v___x_4168_);
v___x_4170_ = v___x_4149_;
goto v_reusejp_4169_;
}
else
{
lean_object* v_reuseFailAlloc_4171_; 
v_reuseFailAlloc_4171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4171_, 0, v___x_4168_);
v___x_4170_ = v_reuseFailAlloc_4171_;
goto v_reusejp_4169_;
}
v_reusejp_4169_:
{
return v___x_4170_;
}
}
}
}
else
{
lean_object* v_a_4173_; lean_object* v___x_4175_; uint8_t v_isShared_4176_; uint8_t v_isSharedCheck_4180_; 
lean_dec_ref(v_entry_4145_);
lean_dec_ref(v_env_4140_);
v_a_4173_ = lean_ctor_get(v___x_4146_, 0);
v_isSharedCheck_4180_ = !lean_is_exclusive(v___x_4146_);
if (v_isSharedCheck_4180_ == 0)
{
v___x_4175_ = v___x_4146_;
v_isShared_4176_ = v_isSharedCheck_4180_;
goto v_resetjp_4174_;
}
else
{
lean_inc(v_a_4173_);
lean_dec(v___x_4146_);
v___x_4175_ = lean_box(0);
v_isShared_4176_ = v_isSharedCheck_4180_;
goto v_resetjp_4174_;
}
v_resetjp_4174_:
{
lean_object* v___x_4178_; 
if (v_isShared_4176_ == 0)
{
v___x_4178_ = v___x_4175_;
goto v_reusejp_4177_;
}
else
{
lean_object* v_reuseFailAlloc_4179_; 
v_reuseFailAlloc_4179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4179_, 0, v_a_4173_);
v___x_4178_ = v_reuseFailAlloc_4179_;
goto v_reusejp_4177_;
}
v_reusejp_4177_:
{
return v___x_4178_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerAttributeOfBuilder___boxed(lean_object* v_env_4181_, lean_object* v_builderId_4182_, lean_object* v_ref_4183_, lean_object* v_args_4184_, lean_object* v_a_4185_){
_start:
{
lean_object* v_res_4186_; 
v_res_4186_ = l_Lean_registerAttributeOfBuilder(v_env_4181_, v_builderId_4182_, v_ref_4183_, v_args_4184_);
return v_res_4186_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg(lean_object* v_x_4187_, lean_object* v___y_4188_, lean_object* v___y_4189_){
_start:
{
if (lean_obj_tag(v_x_4187_) == 0)
{
lean_object* v_a_4191_; lean_object* v___x_4192_; lean_object* v___x_4193_; 
v_a_4191_ = lean_ctor_get(v_x_4187_, 0);
lean_inc(v_a_4191_);
lean_dec_ref(v_x_4187_);
v___x_4192_ = l_Lean_stringToMessageData(v_a_4191_);
v___x_4193_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0_spec__0___redArg(v___x_4192_, v___y_4188_, v___y_4189_);
return v___x_4193_;
}
else
{
lean_object* v_a_4194_; lean_object* v___x_4196_; uint8_t v_isShared_4197_; uint8_t v_isSharedCheck_4201_; 
v_a_4194_ = lean_ctor_get(v_x_4187_, 0);
v_isSharedCheck_4201_ = !lean_is_exclusive(v_x_4187_);
if (v_isSharedCheck_4201_ == 0)
{
v___x_4196_ = v_x_4187_;
v_isShared_4197_ = v_isSharedCheck_4201_;
goto v_resetjp_4195_;
}
else
{
lean_inc(v_a_4194_);
lean_dec(v_x_4187_);
v___x_4196_ = lean_box(0);
v_isShared_4197_ = v_isSharedCheck_4201_;
goto v_resetjp_4195_;
}
v_resetjp_4195_:
{
lean_object* v___x_4199_; 
if (v_isShared_4197_ == 0)
{
lean_ctor_set_tag(v___x_4196_, 0);
v___x_4199_ = v___x_4196_;
goto v_reusejp_4198_;
}
else
{
lean_object* v_reuseFailAlloc_4200_; 
v_reuseFailAlloc_4200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4200_, 0, v_a_4194_);
v___x_4199_ = v_reuseFailAlloc_4200_;
goto v_reusejp_4198_;
}
v_reusejp_4198_:
{
return v___x_4199_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg___boxed(lean_object* v_x_4202_, lean_object* v___y_4203_, lean_object* v___y_4204_, lean_object* v___y_4205_){
_start:
{
lean_object* v_res_4206_; 
v_res_4206_ = l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg(v_x_4202_, v___y_4203_, v___y_4204_);
lean_dec(v___y_4204_);
lean_dec_ref(v___y_4203_);
return v_res_4206_;
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_add(lean_object* v_declName_4207_, lean_object* v_attrName_4208_, lean_object* v_stx_4209_, uint8_t v_kind_4210_, lean_object* v_a_4211_, lean_object* v_a_4212_){
_start:
{
lean_object* v___x_4214_; lean_object* v_env_4215_; lean_object* v___x_4216_; lean_object* v___x_4217_; 
v___x_4214_ = lean_st_ref_get(v_a_4212_);
v_env_4215_ = lean_ctor_get(v___x_4214_, 0);
lean_inc_ref(v_env_4215_);
lean_dec(v___x_4214_);
v___x_4216_ = l_Lean_getAttributeImpl(v_env_4215_, v_attrName_4208_);
v___x_4217_ = l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg(v___x_4216_, v_a_4211_, v_a_4212_);
if (lean_obj_tag(v___x_4217_) == 0)
{
lean_object* v_a_4218_; lean_object* v_add_4219_; lean_object* v___x_4220_; lean_object* v___x_4221_; 
v_a_4218_ = lean_ctor_get(v___x_4217_, 0);
lean_inc(v_a_4218_);
lean_dec_ref(v___x_4217_);
v_add_4219_ = lean_ctor_get(v_a_4218_, 1);
lean_inc_ref(v_add_4219_);
lean_dec(v_a_4218_);
v___x_4220_ = lean_box(v_kind_4210_);
v___x_4221_ = lean_apply_6(v_add_4219_, v_declName_4207_, v_stx_4209_, v___x_4220_, v_a_4211_, v_a_4212_, lean_box(0));
return v___x_4221_;
}
else
{
lean_object* v_a_4222_; lean_object* v___x_4224_; uint8_t v_isShared_4225_; uint8_t v_isSharedCheck_4229_; 
lean_dec(v_a_4212_);
lean_dec_ref(v_a_4211_);
lean_dec(v_stx_4209_);
lean_dec(v_declName_4207_);
v_a_4222_ = lean_ctor_get(v___x_4217_, 0);
v_isSharedCheck_4229_ = !lean_is_exclusive(v___x_4217_);
if (v_isSharedCheck_4229_ == 0)
{
v___x_4224_ = v___x_4217_;
v_isShared_4225_ = v_isSharedCheck_4229_;
goto v_resetjp_4223_;
}
else
{
lean_inc(v_a_4222_);
lean_dec(v___x_4217_);
v___x_4224_ = lean_box(0);
v_isShared_4225_ = v_isSharedCheck_4229_;
goto v_resetjp_4223_;
}
v_resetjp_4223_:
{
lean_object* v___x_4227_; 
if (v_isShared_4225_ == 0)
{
v___x_4227_ = v___x_4224_;
goto v_reusejp_4226_;
}
else
{
lean_object* v_reuseFailAlloc_4228_; 
v_reuseFailAlloc_4228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4228_, 0, v_a_4222_);
v___x_4227_ = v_reuseFailAlloc_4228_;
goto v_reusejp_4226_;
}
v_reusejp_4226_:
{
return v___x_4227_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_add___boxed(lean_object* v_declName_4230_, lean_object* v_attrName_4231_, lean_object* v_stx_4232_, lean_object* v_kind_4233_, lean_object* v_a_4234_, lean_object* v_a_4235_, lean_object* v_a_4236_){
_start:
{
uint8_t v_kind_boxed_4237_; lean_object* v_res_4238_; 
v_kind_boxed_4237_ = lean_unbox(v_kind_4233_);
v_res_4238_ = l_Lean_Attribute_add(v_declName_4230_, v_attrName_4231_, v_stx_4232_, v_kind_boxed_4237_, v_a_4234_, v_a_4235_);
return v_res_4238_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0(lean_object* v_00_u03b1_4239_, lean_object* v_x_4240_, lean_object* v___y_4241_, lean_object* v___y_4242_){
_start:
{
lean_object* v___x_4244_; 
v___x_4244_ = l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg(v_x_4240_, v___y_4241_, v___y_4242_);
return v___x_4244_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___boxed(lean_object* v_00_u03b1_4245_, lean_object* v_x_4246_, lean_object* v___y_4247_, lean_object* v___y_4248_, lean_object* v___y_4249_){
_start:
{
lean_object* v_res_4250_; 
v_res_4250_ = l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0(v_00_u03b1_4245_, v_x_4246_, v___y_4247_, v___y_4248_);
lean_dec(v___y_4248_);
lean_dec_ref(v___y_4247_);
return v_res_4250_;
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_erase(lean_object* v_declName_4251_, lean_object* v_attrName_4252_, lean_object* v_a_4253_, lean_object* v_a_4254_){
_start:
{
lean_object* v___x_4256_; lean_object* v_env_4257_; lean_object* v___x_4258_; lean_object* v___x_4259_; 
v___x_4256_ = lean_st_ref_get(v_a_4254_);
v_env_4257_ = lean_ctor_get(v___x_4256_, 0);
lean_inc_ref(v_env_4257_);
lean_dec(v___x_4256_);
v___x_4258_ = l_Lean_getAttributeImpl(v_env_4257_, v_attrName_4252_);
v___x_4259_ = l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg(v___x_4258_, v_a_4253_, v_a_4254_);
if (lean_obj_tag(v___x_4259_) == 0)
{
lean_object* v_a_4260_; lean_object* v_erase_4261_; lean_object* v___x_4262_; 
v_a_4260_ = lean_ctor_get(v___x_4259_, 0);
lean_inc(v_a_4260_);
lean_dec_ref(v___x_4259_);
v_erase_4261_ = lean_ctor_get(v_a_4260_, 2);
lean_inc_ref(v_erase_4261_);
lean_dec(v_a_4260_);
v___x_4262_ = lean_apply_4(v_erase_4261_, v_declName_4251_, v_a_4253_, v_a_4254_, lean_box(0));
return v___x_4262_;
}
else
{
lean_object* v_a_4263_; lean_object* v___x_4265_; uint8_t v_isShared_4266_; uint8_t v_isSharedCheck_4270_; 
lean_dec(v_a_4254_);
lean_dec_ref(v_a_4253_);
lean_dec(v_declName_4251_);
v_a_4263_ = lean_ctor_get(v___x_4259_, 0);
v_isSharedCheck_4270_ = !lean_is_exclusive(v___x_4259_);
if (v_isSharedCheck_4270_ == 0)
{
v___x_4265_ = v___x_4259_;
v_isShared_4266_ = v_isSharedCheck_4270_;
goto v_resetjp_4264_;
}
else
{
lean_inc(v_a_4263_);
lean_dec(v___x_4259_);
v___x_4265_ = lean_box(0);
v_isShared_4266_ = v_isSharedCheck_4270_;
goto v_resetjp_4264_;
}
v_resetjp_4264_:
{
lean_object* v___x_4268_; 
if (v_isShared_4266_ == 0)
{
v___x_4268_ = v___x_4265_;
goto v_reusejp_4267_;
}
else
{
lean_object* v_reuseFailAlloc_4269_; 
v_reuseFailAlloc_4269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4269_, 0, v_a_4263_);
v___x_4268_ = v_reuseFailAlloc_4269_;
goto v_reusejp_4267_;
}
v_reusejp_4267_:
{
return v___x_4268_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_erase___boxed(lean_object* v_declName_4271_, lean_object* v_attrName_4272_, lean_object* v_a_4273_, lean_object* v_a_4274_, lean_object* v_a_4275_){
_start:
{
lean_object* v_res_4276_; 
v_res_4276_ = l_Lean_Attribute_erase(v_declName_4271_, v_attrName_4272_, v_a_4273_, v_a_4274_);
return v_res_4276_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_updateEnvAttributesImpl_spec__0(lean_object* v_x_4277_, lean_object* v_x_4278_){
_start:
{
if (lean_obj_tag(v_x_4278_) == 0)
{
return v_x_4277_;
}
else
{
lean_object* v_key_4279_; lean_object* v_value_4280_; lean_object* v_tail_4281_; lean_object* v_newEntries_4282_; lean_object* v_map_4283_; uint8_t v___x_4284_; 
v_key_4279_ = lean_ctor_get(v_x_4278_, 0);
lean_inc(v_key_4279_);
v_value_4280_ = lean_ctor_get(v_x_4278_, 1);
lean_inc(v_value_4280_);
v_tail_4281_ = lean_ctor_get(v_x_4278_, 2);
lean_inc(v_tail_4281_);
lean_dec_ref(v_x_4278_);
v_newEntries_4282_ = lean_ctor_get(v_x_4277_, 0);
v_map_4283_ = lean_ctor_get(v_x_4277_, 1);
v___x_4284_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(v_map_4283_, v_key_4279_);
if (v___x_4284_ == 0)
{
lean_object* v___x_4286_; uint8_t v_isShared_4287_; uint8_t v_isSharedCheck_4293_; 
lean_inc_ref(v_map_4283_);
lean_inc(v_newEntries_4282_);
v_isSharedCheck_4293_ = !lean_is_exclusive(v_x_4277_);
if (v_isSharedCheck_4293_ == 0)
{
lean_object* v_unused_4294_; lean_object* v_unused_4295_; 
v_unused_4294_ = lean_ctor_get(v_x_4277_, 1);
lean_dec(v_unused_4294_);
v_unused_4295_ = lean_ctor_get(v_x_4277_, 0);
lean_dec(v_unused_4295_);
v___x_4286_ = v_x_4277_;
v_isShared_4287_ = v_isSharedCheck_4293_;
goto v_resetjp_4285_;
}
else
{
lean_dec(v_x_4277_);
v___x_4286_ = lean_box(0);
v_isShared_4287_ = v_isSharedCheck_4293_;
goto v_resetjp_4285_;
}
v_resetjp_4285_:
{
lean_object* v___x_4288_; lean_object* v___x_4290_; 
v___x_4288_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1___redArg(v_map_4283_, v_key_4279_, v_value_4280_);
if (v_isShared_4287_ == 0)
{
lean_ctor_set(v___x_4286_, 1, v___x_4288_);
v___x_4290_ = v___x_4286_;
goto v_reusejp_4289_;
}
else
{
lean_object* v_reuseFailAlloc_4292_; 
v_reuseFailAlloc_4292_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4292_, 0, v_newEntries_4282_);
lean_ctor_set(v_reuseFailAlloc_4292_, 1, v___x_4288_);
v___x_4290_ = v_reuseFailAlloc_4292_;
goto v_reusejp_4289_;
}
v_reusejp_4289_:
{
v_x_4277_ = v___x_4290_;
v_x_4278_ = v_tail_4281_;
goto _start;
}
}
}
else
{
lean_dec(v_value_4280_);
lean_dec(v_key_4279_);
v_x_4278_ = v_tail_4281_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_updateEnvAttributesImpl_spec__1(lean_object* v_as_4297_, size_t v_i_4298_, size_t v_stop_4299_, lean_object* v_b_4300_){
_start:
{
uint8_t v___x_4301_; 
v___x_4301_ = lean_usize_dec_eq(v_i_4298_, v_stop_4299_);
if (v___x_4301_ == 0)
{
lean_object* v___x_4302_; lean_object* v___x_4303_; size_t v___x_4304_; size_t v___x_4305_; 
v___x_4302_ = lean_array_uget_borrowed(v_as_4297_, v_i_4298_);
lean_inc(v___x_4302_);
v___x_4303_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_updateEnvAttributesImpl_spec__0(v_b_4300_, v___x_4302_);
v___x_4304_ = ((size_t)1ULL);
v___x_4305_ = lean_usize_add(v_i_4298_, v___x_4304_);
v_i_4298_ = v___x_4305_;
v_b_4300_ = v___x_4303_;
goto _start;
}
else
{
return v_b_4300_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_updateEnvAttributesImpl_spec__1___boxed(lean_object* v_as_4307_, lean_object* v_i_4308_, lean_object* v_stop_4309_, lean_object* v_b_4310_){
_start:
{
size_t v_i_boxed_4311_; size_t v_stop_boxed_4312_; lean_object* v_res_4313_; 
v_i_boxed_4311_ = lean_unbox_usize(v_i_4308_);
lean_dec(v_i_4308_);
v_stop_boxed_4312_ = lean_unbox_usize(v_stop_4309_);
lean_dec(v_stop_4309_);
v_res_4313_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_updateEnvAttributesImpl_spec__1(v_as_4307_, v_i_boxed_4311_, v_stop_boxed_4312_, v_b_4310_);
lean_dec_ref(v_as_4307_);
return v_res_4313_;
}
}
LEAN_EXPORT lean_object* lean_update_env_attributes(lean_object* v_env_4314_){
_start:
{
lean_object* v___x_4316_; lean_object* v___x_4317_; lean_object* v___x_4318_; lean_object* v___y_4320_; lean_object* v_toEnvExtension_4323_; lean_object* v_asyncMode_4324_; lean_object* v_buckets_4325_; lean_object* v___x_4326_; lean_object* v___x_4327_; lean_object* v___x_4328_; lean_object* v___x_4329_; lean_object* v___x_4330_; uint8_t v___x_4331_; 
v___x_4316_ = l_Lean_attributeMapRef;
v___x_4317_ = lean_st_ref_get(v___x_4316_);
v___x_4318_ = l_Lean_attributeExtension;
v_toEnvExtension_4323_ = lean_ctor_get(v___x_4318_, 0);
lean_inc_ref(v_toEnvExtension_4323_);
v_asyncMode_4324_ = lean_ctor_get(v_toEnvExtension_4323_, 2);
lean_inc(v_asyncMode_4324_);
lean_dec_ref(v_toEnvExtension_4323_);
v_buckets_4325_ = lean_ctor_get(v___x_4317_, 1);
lean_inc_ref(v_buckets_4325_);
lean_dec(v___x_4317_);
v___x_4326_ = l_Lean_instInhabitedAttributeExtensionState_default;
v___x_4327_ = lean_box(0);
lean_inc_ref(v_env_4314_);
v___x_4328_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_4326_, v___x_4318_, v_env_4314_, v_asyncMode_4324_, v___x_4327_);
lean_dec(v_asyncMode_4324_);
v___x_4329_ = lean_unsigned_to_nat(0u);
v___x_4330_ = lean_array_get_size(v_buckets_4325_);
v___x_4331_ = lean_nat_dec_lt(v___x_4329_, v___x_4330_);
if (v___x_4331_ == 0)
{
lean_dec_ref(v_buckets_4325_);
v___y_4320_ = v___x_4328_;
goto v___jp_4319_;
}
else
{
uint8_t v___x_4332_; 
v___x_4332_ = lean_nat_dec_le(v___x_4330_, v___x_4330_);
if (v___x_4332_ == 0)
{
if (v___x_4331_ == 0)
{
lean_dec_ref(v_buckets_4325_);
v___y_4320_ = v___x_4328_;
goto v___jp_4319_;
}
else
{
size_t v___x_4333_; size_t v___x_4334_; lean_object* v___x_4335_; 
v___x_4333_ = ((size_t)0ULL);
v___x_4334_ = lean_usize_of_nat(v___x_4330_);
v___x_4335_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_updateEnvAttributesImpl_spec__1(v_buckets_4325_, v___x_4333_, v___x_4334_, v___x_4328_);
lean_dec_ref(v_buckets_4325_);
v___y_4320_ = v___x_4335_;
goto v___jp_4319_;
}
}
else
{
size_t v___x_4336_; size_t v___x_4337_; lean_object* v___x_4338_; 
v___x_4336_ = ((size_t)0ULL);
v___x_4337_ = lean_usize_of_nat(v___x_4330_);
v___x_4338_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_updateEnvAttributesImpl_spec__1(v_buckets_4325_, v___x_4336_, v___x_4337_, v___x_4328_);
lean_dec_ref(v_buckets_4325_);
v___y_4320_ = v___x_4338_;
goto v___jp_4319_;
}
}
v___jp_4319_:
{
lean_object* v___x_4321_; lean_object* v___x_4322_; 
v___x_4321_ = l_Lean_PersistentEnvExtension_setState___redArg(v___x_4318_, v_env_4314_, v___y_4320_);
v___x_4322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4322_, 0, v___x_4321_);
return v___x_4322_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_updateEnvAttributesImpl___boxed(lean_object* v_env_4339_, lean_object* v_a_4340_){
_start:
{
lean_object* v_res_4341_; 
v_res_4341_ = lean_update_env_attributes(v_env_4339_);
return v_res_4341_;
}
}
LEAN_EXPORT lean_object* lean_get_num_attributes(){
_start:
{
lean_object* v___x_4343_; lean_object* v___x_4344_; lean_object* v_size_4345_; lean_object* v___x_4346_; 
v___x_4343_ = l_Lean_attributeMapRef;
v___x_4344_ = lean_st_ref_get(v___x_4343_);
v_size_4345_ = lean_ctor_get(v___x_4344_, 0);
lean_inc(v_size_4345_);
lean_dec(v___x_4344_);
v___x_4346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4346_, 0, v_size_4345_);
return v___x_4346_;
}
}
LEAN_EXPORT lean_object* l_Lean_getNumBuiltinAttributesImpl___boxed(lean_object* v_a_4347_){
_start:
{
lean_object* v_res_4348_; 
v_res_4348_ = lean_get_num_attributes();
return v_res_4348_;
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
