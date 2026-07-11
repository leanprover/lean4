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
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t l_Lean_Name_quickLt(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
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
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
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
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
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
uint8_t lean_bool_not(uint8_t);
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
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instInhabitedEnvExtension_default(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
extern lean_object* l_Lean_ResolveName_backward_privateInPublic_warn;
uint8_t l_Lean_isPrivateName(lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_Lean_Syntax_isNatLit_x3f(lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isMarkedMeta(lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Array_reverse___redArg(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerTagAttribute_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerTagAttribute_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerTagAttribute_spec__1_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__5(lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__5___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3_spec__5___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3_spec__5(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParam_x3f___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParam_x3f___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_ParametricAttribute_getParam_x3f___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_ParametricAttribute_getParam_x3f___redArg___closed__0 = (const lean_object*)&l_Lean_ParametricAttribute_getParam_x3f___redArg___closed__0_value;
static const lean_closure_object l_Lean_ParametricAttribute_getParam_x3f___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_ParametricAttribute_getParam_x3f___redArg___closed__1 = (const lean_object*)&l_Lean_ParametricAttribute_getParam_x3f___redArg___closed__1_value;
static const lean_closure_object l_Lean_ParametricAttribute_getParam_x3f___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_id___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_ParametricAttribute_getParam_x3f___redArg___closed__2 = (const lean_object*)&l_Lean_ParametricAttribute_getParam_x3f___redArg___closed__2_value;
static const lean_closure_object l_Lean_ParametricAttribute_getParam_x3f___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_ParametricAttribute_getParam_x3f___redArg___closed__3 = (const lean_object*)&l_Lean_ParametricAttribute_getParam_x3f___redArg___closed__3_value;
static const lean_closure_object l_Lean_ParametricAttribute_getParam_x3f___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_ParametricAttribute_getParam_x3f___redArg___closed__4 = (const lean_object*)&l_Lean_ParametricAttribute_getParam_x3f___redArg___closed__4_value;
static const lean_closure_object l_Lean_ParametricAttribute_getParam_x3f___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_ParametricAttribute_getParam_x3f___redArg___closed__5 = (const lean_object*)&l_Lean_ParametricAttribute_getParam_x3f___redArg___closed__5_value;
static const lean_closure_object l_Lean_ParametricAttribute_getParam_x3f___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_ParametricAttribute_getParam_x3f___redArg___closed__6 = (const lean_object*)&l_Lean_ParametricAttribute_getParam_x3f___redArg___closed__6_value;
static const lean_closure_object l_Lean_ParametricAttribute_getParam_x3f___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_ParametricAttribute_getParam_x3f___redArg___closed__7 = (const lean_object*)&l_Lean_ParametricAttribute_getParam_x3f___redArg___closed__7_value;
static const lean_closure_object l_Lean_ParametricAttribute_getParam_x3f___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_ParametricAttribute_getParam_x3f___redArg___closed__8 = (const lean_object*)&l_Lean_ParametricAttribute_getParam_x3f___redArg___closed__8_value;
static const lean_closure_object l_Lean_ParametricAttribute_getParam_x3f___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_ParametricAttribute_getParam_x3f___redArg___closed__9 = (const lean_object*)&l_Lean_ParametricAttribute_getParam_x3f___redArg___closed__9_value;
static const lean_ctor_object l_Lean_ParametricAttribute_getParam_x3f___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_ParametricAttribute_getParam_x3f___redArg___closed__3_value),((lean_object*)&l_Lean_ParametricAttribute_getParam_x3f___redArg___closed__4_value)}};
static const lean_object* l_Lean_ParametricAttribute_getParam_x3f___redArg___closed__10 = (const lean_object*)&l_Lean_ParametricAttribute_getParam_x3f___redArg___closed__10_value;
static const lean_ctor_object l_Lean_ParametricAttribute_getParam_x3f___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_ParametricAttribute_getParam_x3f___redArg___closed__10_value),((lean_object*)&l_Lean_ParametricAttribute_getParam_x3f___redArg___closed__5_value),((lean_object*)&l_Lean_ParametricAttribute_getParam_x3f___redArg___closed__6_value),((lean_object*)&l_Lean_ParametricAttribute_getParam_x3f___redArg___closed__7_value),((lean_object*)&l_Lean_ParametricAttribute_getParam_x3f___redArg___closed__8_value)}};
static const lean_object* l_Lean_ParametricAttribute_getParam_x3f___redArg___closed__11 = (const lean_object*)&l_Lean_ParametricAttribute_getParam_x3f___redArg___closed__11_value;
static const lean_ctor_object l_Lean_ParametricAttribute_getParam_x3f___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_ParametricAttribute_getParam_x3f___redArg___closed__11_value),((lean_object*)&l_Lean_ParametricAttribute_getParam_x3f___redArg___closed__9_value)}};
static const lean_object* l_Lean_ParametricAttribute_getParam_x3f___redArg___closed__12 = (const lean_object*)&l_Lean_ParametricAttribute_getParam_x3f___redArg___closed__12_value;
static const lean_ctor_object l_Lean_ParametricAttribute_getParam_x3f___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_ParametricAttribute_getParam_x3f___redArg___closed__13 = (const lean_object*)&l_Lean_ParametricAttribute_getParam_x3f___redArg___closed__13_value;
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
uint8_t v___y_994__boxed_322_; lean_object* v_res_323_; 
v___y_994__boxed_322_ = lean_unbox(v___y_318_);
v_res_323_ = l_Lean_instInhabitedAttributeImpl_default___lam__0(v_x_316_, v___y_317_, v___y_994__boxed_322_, v___y_319_, v___y_320_);
lean_dec(v___y_320_);
lean_dec_ref(v___y_319_);
lean_dec(v___y_317_);
lean_dec(v_x_316_);
return v_res_323_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_324_; 
v___x_324_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_324_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_325_; lean_object* v___x_326_; 
v___x_325_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__0);
v___x_326_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_326_, 0, v___x_325_);
return v___x_326_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; 
v___x_327_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__1);
v___x_328_ = lean_unsigned_to_nat(0u);
v___x_329_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_329_, 0, v___x_328_);
lean_ctor_set(v___x_329_, 1, v___x_328_);
lean_ctor_set(v___x_329_, 2, v___x_328_);
lean_ctor_set(v___x_329_, 3, v___x_328_);
lean_ctor_set(v___x_329_, 4, v___x_327_);
lean_ctor_set(v___x_329_, 5, v___x_327_);
lean_ctor_set(v___x_329_, 6, v___x_327_);
lean_ctor_set(v___x_329_, 7, v___x_327_);
lean_ctor_set(v___x_329_, 8, v___x_327_);
lean_ctor_set(v___x_329_, 9, v___x_327_);
return v___x_329_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; 
v___x_330_ = lean_unsigned_to_nat(32u);
v___x_331_ = lean_mk_empty_array_with_capacity(v___x_330_);
v___x_332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_332_, 0, v___x_331_);
return v___x_332_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__4(void){
_start:
{
size_t v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; 
v___x_333_ = ((size_t)5ULL);
v___x_334_ = lean_unsigned_to_nat(0u);
v___x_335_ = lean_unsigned_to_nat(32u);
v___x_336_ = lean_mk_empty_array_with_capacity(v___x_335_);
v___x_337_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__3);
v___x_338_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_338_, 0, v___x_337_);
lean_ctor_set(v___x_338_, 1, v___x_336_);
lean_ctor_set(v___x_338_, 2, v___x_334_);
lean_ctor_set(v___x_338_, 3, v___x_334_);
lean_ctor_set_usize(v___x_338_, 4, v___x_333_);
return v___x_338_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; 
v___x_339_ = lean_box(1);
v___x_340_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__4);
v___x_341_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__1);
v___x_342_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_342_, 0, v___x_341_);
lean_ctor_set(v___x_342_, 1, v___x_340_);
lean_ctor_set(v___x_342_, 2, v___x_339_);
return v___x_342_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0(lean_object* v_msgData_343_, lean_object* v___y_344_, lean_object* v___y_345_){
_start:
{
lean_object* v___x_347_; lean_object* v_env_348_; lean_object* v_options_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; 
v___x_347_ = lean_st_ref_get(v___y_345_);
v_env_348_ = lean_ctor_get(v___x_347_, 0);
lean_inc_ref(v_env_348_);
lean_dec(v___x_347_);
v_options_349_ = lean_ctor_get(v___y_344_, 2);
v___x_350_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__2);
v___x_351_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__5);
lean_inc_ref(v_options_349_);
v___x_352_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_352_, 0, v_env_348_);
lean_ctor_set(v___x_352_, 1, v___x_350_);
lean_ctor_set(v___x_352_, 2, v___x_351_);
lean_ctor_set(v___x_352_, 3, v_options_349_);
v___x_353_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_353_, 0, v___x_352_);
lean_ctor_set(v___x_353_, 1, v_msgData_343_);
v___x_354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_354_, 0, v___x_353_);
return v___x_354_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___boxed(lean_object* v_msgData_355_, lean_object* v___y_356_, lean_object* v___y_357_, lean_object* v___y_358_){
_start:
{
lean_object* v_res_359_; 
v_res_359_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0(v_msgData_355_, v___y_356_, v___y_357_);
lean_dec(v___y_357_);
lean_dec_ref(v___y_356_);
return v_res_359_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(lean_object* v_msg_360_, lean_object* v___y_361_, lean_object* v___y_362_){
_start:
{
lean_object* v_ref_364_; lean_object* v___x_365_; lean_object* v_a_366_; lean_object* v___x_368_; uint8_t v_isShared_369_; uint8_t v_isSharedCheck_374_; 
v_ref_364_ = lean_ctor_get(v___y_361_, 5);
v___x_365_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0(v_msg_360_, v___y_361_, v___y_362_);
v_a_366_ = lean_ctor_get(v___x_365_, 0);
v_isSharedCheck_374_ = !lean_is_exclusive(v___x_365_);
if (v_isSharedCheck_374_ == 0)
{
v___x_368_ = v___x_365_;
v_isShared_369_ = v_isSharedCheck_374_;
goto v_resetjp_367_;
}
else
{
lean_inc(v_a_366_);
lean_dec(v___x_365_);
v___x_368_ = lean_box(0);
v_isShared_369_ = v_isSharedCheck_374_;
goto v_resetjp_367_;
}
v_resetjp_367_:
{
lean_object* v___x_370_; lean_object* v___x_372_; 
lean_inc(v_ref_364_);
v___x_370_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_370_, 0, v_ref_364_);
lean_ctor_set(v___x_370_, 1, v_a_366_);
if (v_isShared_369_ == 0)
{
lean_ctor_set_tag(v___x_368_, 1);
lean_ctor_set(v___x_368_, 0, v___x_370_);
v___x_372_ = v___x_368_;
goto v_reusejp_371_;
}
else
{
lean_object* v_reuseFailAlloc_373_; 
v_reuseFailAlloc_373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_373_, 0, v___x_370_);
v___x_372_ = v_reuseFailAlloc_373_;
goto v_reusejp_371_;
}
v_reusejp_371_:
{
return v___x_372_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg___boxed(lean_object* v_msg_375_, lean_object* v___y_376_, lean_object* v___y_377_, lean_object* v___y_378_){
_start:
{
lean_object* v_res_379_; 
v_res_379_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v_msg_375_, v___y_376_, v___y_377_);
lean_dec(v___y_377_);
lean_dec_ref(v___y_376_);
return v_res_379_;
}
}
static lean_object* _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1(void){
_start:
{
lean_object* v___x_381_; lean_object* v___x_382_; 
v___x_381_ = ((lean_object*)(l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__0));
v___x_382_ = l_Lean_stringToMessageData(v___x_381_);
return v___x_382_;
}
}
static lean_object* _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3(void){
_start:
{
lean_object* v___x_384_; lean_object* v___x_385_; 
v___x_384_ = ((lean_object*)(l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__2));
v___x_385_ = l_Lean_stringToMessageData(v___x_384_);
return v___x_385_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedAttributeImpl_default___lam__1(lean_object* v___x_386_, lean_object* v_decl_387_, lean_object* v___y_388_, lean_object* v___y_389_){
_start:
{
lean_object* v_name_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; 
v_name_391_ = lean_ctor_get(v___x_386_, 1);
lean_inc(v_name_391_);
lean_dec_ref(v___x_386_);
v___x_392_ = lean_obj_once(&l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1, &l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1_once, _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1);
v___x_393_ = l_Lean_MessageData_ofName(v_name_391_);
v___x_394_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_394_, 0, v___x_392_);
lean_ctor_set(v___x_394_, 1, v___x_393_);
v___x_395_ = lean_obj_once(&l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3, &l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3_once, _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3);
v___x_396_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_396_, 0, v___x_394_);
lean_ctor_set(v___x_396_, 1, v___x_395_);
v___x_397_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_396_, v___y_388_, v___y_389_);
return v___x_397_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedAttributeImpl_default___lam__1___boxed(lean_object* v___x_398_, lean_object* v_decl_399_, lean_object* v___y_400_, lean_object* v___y_401_, lean_object* v___y_402_){
_start:
{
lean_object* v_res_403_; 
v_res_403_ = l_Lean_instInhabitedAttributeImpl_default___lam__1(v___x_398_, v_decl_399_, v___y_400_, v___y_401_);
lean_dec(v___y_401_);
lean_dec_ref(v___y_400_);
lean_dec(v_decl_399_);
return v_res_403_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0(lean_object* v_00_u03b1_412_, lean_object* v_msg_413_, lean_object* v___y_414_, lean_object* v___y_415_){
_start:
{
lean_object* v___x_417_; 
v___x_417_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v_msg_413_, v___y_414_, v___y_415_);
return v___x_417_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___boxed(lean_object* v_00_u03b1_418_, lean_object* v_msg_419_, lean_object* v___y_420_, lean_object* v___y_421_, lean_object* v___y_422_){
_start:
{
lean_object* v_res_423_; 
v_res_423_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0(v_00_u03b1_418_, v_msg_419_, v___y_420_, v___y_421_);
lean_dec(v___y_421_);
lean_dec_ref(v___y_420_);
return v_res_423_;
}
}
static lean_object* _init_l___private_Lean_Attributes_0__Lean_initFn___closed__0_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; 
v___x_425_ = lean_box(0);
v___x_426_ = lean_unsigned_to_nat(16u);
v___x_427_ = lean_mk_array(v___x_426_, v___x_425_);
return v___x_427_;
}
}
static lean_object* _init_l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; 
v___x_428_ = lean_obj_once(&l___private_Lean_Attributes_0__Lean_initFn___closed__0_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_, &l___private_Lean_Attributes_0__Lean_initFn___closed__0_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2__once, _init_l___private_Lean_Attributes_0__Lean_initFn___closed__0_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_);
v___x_429_ = lean_unsigned_to_nat(0u);
v___x_430_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_430_, 0, v___x_429_);
lean_ctor_set(v___x_430_, 1, v___x_428_);
return v___x_430_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; 
v___x_432_ = lean_obj_once(&l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_, &l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2__once, _init_l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_);
v___x_433_ = lean_st_mk_ref(v___x_432_);
v___x_434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_434_, 0, v___x_433_);
return v___x_434_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2____boxed(lean_object* v_a_435_){
_start:
{
lean_object* v_res_436_; 
v_res_436_ = l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_();
return v_res_436_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0_spec__0___redArg(lean_object* v_a_437_, lean_object* v_x_438_){
_start:
{
if (lean_obj_tag(v_x_438_) == 0)
{
uint8_t v___x_439_; 
v___x_439_ = 0;
return v___x_439_;
}
else
{
lean_object* v_key_440_; lean_object* v_tail_441_; uint8_t v___x_442_; 
v_key_440_ = lean_ctor_get(v_x_438_, 0);
v_tail_441_ = lean_ctor_get(v_x_438_, 2);
v___x_442_ = lean_name_eq(v_key_440_, v_a_437_);
if (v___x_442_ == 0)
{
v_x_438_ = v_tail_441_;
goto _start;
}
else
{
return v___x_442_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0_spec__0___redArg___boxed(lean_object* v_a_444_, lean_object* v_x_445_){
_start:
{
uint8_t v_res_446_; lean_object* v_r_447_; 
v_res_446_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0_spec__0___redArg(v_a_444_, v_x_445_);
lean_dec(v_x_445_);
lean_dec(v_a_444_);
v_r_447_ = lean_box(v_res_446_);
return v_r_447_;
}
}
static uint64_t _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_448_; uint64_t v___x_449_; 
v___x_448_ = lean_unsigned_to_nat(1723u);
v___x_449_ = lean_uint64_of_nat(v___x_448_);
return v___x_449_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(lean_object* v_m_450_, lean_object* v_a_451_){
_start:
{
lean_object* v_buckets_452_; lean_object* v___x_453_; uint64_t v___y_455_; 
v_buckets_452_ = lean_ctor_get(v_m_450_, 1);
v___x_453_ = lean_array_get_size(v_buckets_452_);
if (lean_obj_tag(v_a_451_) == 0)
{
uint64_t v___x_469_; 
v___x_469_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg___closed__0);
v___y_455_ = v___x_469_;
goto v___jp_454_;
}
else
{
uint64_t v_hash_470_; 
v_hash_470_ = lean_ctor_get_uint64(v_a_451_, sizeof(void*)*2);
v___y_455_ = v_hash_470_;
goto v___jp_454_;
}
v___jp_454_:
{
uint64_t v___x_456_; uint64_t v___x_457_; uint64_t v_fold_458_; uint64_t v___x_459_; uint64_t v___x_460_; uint64_t v___x_461_; size_t v___x_462_; size_t v___x_463_; size_t v___x_464_; size_t v___x_465_; size_t v___x_466_; lean_object* v___x_467_; uint8_t v___x_468_; 
v___x_456_ = 32ULL;
v___x_457_ = lean_uint64_shift_right(v___y_455_, v___x_456_);
v_fold_458_ = lean_uint64_xor(v___y_455_, v___x_457_);
v___x_459_ = 16ULL;
v___x_460_ = lean_uint64_shift_right(v_fold_458_, v___x_459_);
v___x_461_ = lean_uint64_xor(v_fold_458_, v___x_460_);
v___x_462_ = lean_uint64_to_usize(v___x_461_);
v___x_463_ = lean_usize_of_nat(v___x_453_);
v___x_464_ = ((size_t)1ULL);
v___x_465_ = lean_usize_sub(v___x_463_, v___x_464_);
v___x_466_ = lean_usize_land(v___x_462_, v___x_465_);
v___x_467_ = lean_array_uget_borrowed(v_buckets_452_, v___x_466_);
v___x_468_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0_spec__0___redArg(v_a_451_, v___x_467_);
return v___x_468_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg___boxed(lean_object* v_m_471_, lean_object* v_a_472_){
_start:
{
uint8_t v_res_473_; lean_object* v_r_474_; 
v_res_473_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(v_m_471_, v_a_472_);
lean_dec(v_a_472_);
lean_dec_ref(v_m_471_);
v_r_474_ = lean_box(v_res_473_);
return v_r_474_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__3___redArg(lean_object* v_a_475_, lean_object* v_b_476_, lean_object* v_x_477_){
_start:
{
if (lean_obj_tag(v_x_477_) == 0)
{
lean_dec(v_b_476_);
lean_dec(v_a_475_);
return v_x_477_;
}
else
{
lean_object* v_key_478_; lean_object* v_value_479_; lean_object* v_tail_480_; lean_object* v___x_482_; uint8_t v_isShared_483_; uint8_t v_isSharedCheck_492_; 
v_key_478_ = lean_ctor_get(v_x_477_, 0);
v_value_479_ = lean_ctor_get(v_x_477_, 1);
v_tail_480_ = lean_ctor_get(v_x_477_, 2);
v_isSharedCheck_492_ = !lean_is_exclusive(v_x_477_);
if (v_isSharedCheck_492_ == 0)
{
v___x_482_ = v_x_477_;
v_isShared_483_ = v_isSharedCheck_492_;
goto v_resetjp_481_;
}
else
{
lean_inc(v_tail_480_);
lean_inc(v_value_479_);
lean_inc(v_key_478_);
lean_dec(v_x_477_);
v___x_482_ = lean_box(0);
v_isShared_483_ = v_isSharedCheck_492_;
goto v_resetjp_481_;
}
v_resetjp_481_:
{
uint8_t v___x_484_; 
v___x_484_ = lean_name_eq(v_key_478_, v_a_475_);
if (v___x_484_ == 0)
{
lean_object* v___x_485_; lean_object* v___x_487_; 
v___x_485_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__3___redArg(v_a_475_, v_b_476_, v_tail_480_);
if (v_isShared_483_ == 0)
{
lean_ctor_set(v___x_482_, 2, v___x_485_);
v___x_487_ = v___x_482_;
goto v_reusejp_486_;
}
else
{
lean_object* v_reuseFailAlloc_488_; 
v_reuseFailAlloc_488_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_488_, 0, v_key_478_);
lean_ctor_set(v_reuseFailAlloc_488_, 1, v_value_479_);
lean_ctor_set(v_reuseFailAlloc_488_, 2, v___x_485_);
v___x_487_ = v_reuseFailAlloc_488_;
goto v_reusejp_486_;
}
v_reusejp_486_:
{
return v___x_487_;
}
}
else
{
lean_object* v___x_490_; 
lean_dec(v_value_479_);
lean_dec(v_key_478_);
if (v_isShared_483_ == 0)
{
lean_ctor_set(v___x_482_, 1, v_b_476_);
lean_ctor_set(v___x_482_, 0, v_a_475_);
v___x_490_ = v___x_482_;
goto v_reusejp_489_;
}
else
{
lean_object* v_reuseFailAlloc_491_; 
v_reuseFailAlloc_491_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_491_, 0, v_a_475_);
lean_ctor_set(v_reuseFailAlloc_491_, 1, v_b_476_);
lean_ctor_set(v_reuseFailAlloc_491_, 2, v_tail_480_);
v___x_490_ = v_reuseFailAlloc_491_;
goto v_reusejp_489_;
}
v_reusejp_489_:
{
return v___x_490_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2_spec__3_spec__4___redArg(lean_object* v_x_493_, lean_object* v_x_494_){
_start:
{
if (lean_obj_tag(v_x_494_) == 0)
{
return v_x_493_;
}
else
{
lean_object* v_key_495_; lean_object* v_value_496_; lean_object* v_tail_497_; lean_object* v___x_499_; uint8_t v_isShared_500_; uint8_t v_isSharedCheck_523_; 
v_key_495_ = lean_ctor_get(v_x_494_, 0);
v_value_496_ = lean_ctor_get(v_x_494_, 1);
v_tail_497_ = lean_ctor_get(v_x_494_, 2);
v_isSharedCheck_523_ = !lean_is_exclusive(v_x_494_);
if (v_isSharedCheck_523_ == 0)
{
v___x_499_ = v_x_494_;
v_isShared_500_ = v_isSharedCheck_523_;
goto v_resetjp_498_;
}
else
{
lean_inc(v_tail_497_);
lean_inc(v_value_496_);
lean_inc(v_key_495_);
lean_dec(v_x_494_);
v___x_499_ = lean_box(0);
v_isShared_500_ = v_isSharedCheck_523_;
goto v_resetjp_498_;
}
v_resetjp_498_:
{
lean_object* v___x_501_; uint64_t v___y_503_; 
v___x_501_ = lean_array_get_size(v_x_493_);
if (lean_obj_tag(v_key_495_) == 0)
{
uint64_t v___x_521_; 
v___x_521_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg___closed__0);
v___y_503_ = v___x_521_;
goto v___jp_502_;
}
else
{
uint64_t v_hash_522_; 
v_hash_522_ = lean_ctor_get_uint64(v_key_495_, sizeof(void*)*2);
v___y_503_ = v_hash_522_;
goto v___jp_502_;
}
v___jp_502_:
{
uint64_t v___x_504_; uint64_t v___x_505_; uint64_t v_fold_506_; uint64_t v___x_507_; uint64_t v___x_508_; uint64_t v___x_509_; size_t v___x_510_; size_t v___x_511_; size_t v___x_512_; size_t v___x_513_; size_t v___x_514_; lean_object* v___x_515_; lean_object* v___x_517_; 
v___x_504_ = 32ULL;
v___x_505_ = lean_uint64_shift_right(v___y_503_, v___x_504_);
v_fold_506_ = lean_uint64_xor(v___y_503_, v___x_505_);
v___x_507_ = 16ULL;
v___x_508_ = lean_uint64_shift_right(v_fold_506_, v___x_507_);
v___x_509_ = lean_uint64_xor(v_fold_506_, v___x_508_);
v___x_510_ = lean_uint64_to_usize(v___x_509_);
v___x_511_ = lean_usize_of_nat(v___x_501_);
v___x_512_ = ((size_t)1ULL);
v___x_513_ = lean_usize_sub(v___x_511_, v___x_512_);
v___x_514_ = lean_usize_land(v___x_510_, v___x_513_);
v___x_515_ = lean_array_uget_borrowed(v_x_493_, v___x_514_);
lean_inc(v___x_515_);
if (v_isShared_500_ == 0)
{
lean_ctor_set(v___x_499_, 2, v___x_515_);
v___x_517_ = v___x_499_;
goto v_reusejp_516_;
}
else
{
lean_object* v_reuseFailAlloc_520_; 
v_reuseFailAlloc_520_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_520_, 0, v_key_495_);
lean_ctor_set(v_reuseFailAlloc_520_, 1, v_value_496_);
lean_ctor_set(v_reuseFailAlloc_520_, 2, v___x_515_);
v___x_517_ = v_reuseFailAlloc_520_;
goto v_reusejp_516_;
}
v_reusejp_516_:
{
lean_object* v___x_518_; 
v___x_518_ = lean_array_uset(v_x_493_, v___x_514_, v___x_517_);
v_x_493_ = v___x_518_;
v_x_494_ = v_tail_497_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2_spec__3___redArg(lean_object* v_i_524_, lean_object* v_source_525_, lean_object* v_target_526_){
_start:
{
lean_object* v___x_527_; uint8_t v___x_528_; 
v___x_527_ = lean_array_get_size(v_source_525_);
v___x_528_ = lean_nat_dec_lt(v_i_524_, v___x_527_);
if (v___x_528_ == 0)
{
lean_dec_ref(v_source_525_);
lean_dec(v_i_524_);
return v_target_526_;
}
else
{
lean_object* v_es_529_; lean_object* v___x_530_; lean_object* v_source_531_; lean_object* v_target_532_; lean_object* v___x_533_; lean_object* v___x_534_; 
v_es_529_ = lean_array_fget(v_source_525_, v_i_524_);
v___x_530_ = lean_box(0);
v_source_531_ = lean_array_fset(v_source_525_, v_i_524_, v___x_530_);
v_target_532_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2_spec__3_spec__4___redArg(v_target_526_, v_es_529_);
v___x_533_ = lean_unsigned_to_nat(1u);
v___x_534_ = lean_nat_add(v_i_524_, v___x_533_);
lean_dec(v_i_524_);
v_i_524_ = v___x_534_;
v_source_525_ = v_source_531_;
v_target_526_ = v_target_532_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2___redArg(lean_object* v_data_536_){
_start:
{
lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v_nbuckets_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; 
v___x_537_ = lean_array_get_size(v_data_536_);
v___x_538_ = lean_unsigned_to_nat(2u);
v_nbuckets_539_ = lean_nat_mul(v___x_537_, v___x_538_);
v___x_540_ = lean_unsigned_to_nat(0u);
v___x_541_ = lean_box(0);
v___x_542_ = lean_mk_array(v_nbuckets_539_, v___x_541_);
v___x_543_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2_spec__3___redArg(v___x_540_, v_data_536_, v___x_542_);
return v___x_543_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1___redArg(lean_object* v_m_544_, lean_object* v_a_545_, lean_object* v_b_546_){
_start:
{
lean_object* v_size_547_; lean_object* v_buckets_548_; lean_object* v___x_550_; uint8_t v_isShared_551_; uint8_t v_isSharedCheck_594_; 
v_size_547_ = lean_ctor_get(v_m_544_, 0);
v_buckets_548_ = lean_ctor_get(v_m_544_, 1);
v_isSharedCheck_594_ = !lean_is_exclusive(v_m_544_);
if (v_isSharedCheck_594_ == 0)
{
v___x_550_ = v_m_544_;
v_isShared_551_ = v_isSharedCheck_594_;
goto v_resetjp_549_;
}
else
{
lean_inc(v_buckets_548_);
lean_inc(v_size_547_);
lean_dec(v_m_544_);
v___x_550_ = lean_box(0);
v_isShared_551_ = v_isSharedCheck_594_;
goto v_resetjp_549_;
}
v_resetjp_549_:
{
lean_object* v___x_552_; uint64_t v___y_554_; 
v___x_552_ = lean_array_get_size(v_buckets_548_);
if (lean_obj_tag(v_a_545_) == 0)
{
uint64_t v___x_592_; 
v___x_592_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg___closed__0);
v___y_554_ = v___x_592_;
goto v___jp_553_;
}
else
{
uint64_t v_hash_593_; 
v_hash_593_ = lean_ctor_get_uint64(v_a_545_, sizeof(void*)*2);
v___y_554_ = v_hash_593_;
goto v___jp_553_;
}
v___jp_553_:
{
uint64_t v___x_555_; uint64_t v___x_556_; uint64_t v_fold_557_; uint64_t v___x_558_; uint64_t v___x_559_; uint64_t v___x_560_; size_t v___x_561_; size_t v___x_562_; size_t v___x_563_; size_t v___x_564_; size_t v___x_565_; lean_object* v_bkt_566_; uint8_t v___x_567_; 
v___x_555_ = 32ULL;
v___x_556_ = lean_uint64_shift_right(v___y_554_, v___x_555_);
v_fold_557_ = lean_uint64_xor(v___y_554_, v___x_556_);
v___x_558_ = 16ULL;
v___x_559_ = lean_uint64_shift_right(v_fold_557_, v___x_558_);
v___x_560_ = lean_uint64_xor(v_fold_557_, v___x_559_);
v___x_561_ = lean_uint64_to_usize(v___x_560_);
v___x_562_ = lean_usize_of_nat(v___x_552_);
v___x_563_ = ((size_t)1ULL);
v___x_564_ = lean_usize_sub(v___x_562_, v___x_563_);
v___x_565_ = lean_usize_land(v___x_561_, v___x_564_);
v_bkt_566_ = lean_array_uget_borrowed(v_buckets_548_, v___x_565_);
v___x_567_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0_spec__0___redArg(v_a_545_, v_bkt_566_);
if (v___x_567_ == 0)
{
lean_object* v___x_568_; lean_object* v_size_x27_569_; lean_object* v___x_570_; lean_object* v_buckets_x27_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; uint8_t v___x_577_; 
v___x_568_ = lean_unsigned_to_nat(1u);
v_size_x27_569_ = lean_nat_add(v_size_547_, v___x_568_);
lean_dec(v_size_547_);
lean_inc(v_bkt_566_);
v___x_570_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_570_, 0, v_a_545_);
lean_ctor_set(v___x_570_, 1, v_b_546_);
lean_ctor_set(v___x_570_, 2, v_bkt_566_);
v_buckets_x27_571_ = lean_array_uset(v_buckets_548_, v___x_565_, v___x_570_);
v___x_572_ = lean_unsigned_to_nat(4u);
v___x_573_ = lean_nat_mul(v_size_x27_569_, v___x_572_);
v___x_574_ = lean_unsigned_to_nat(3u);
v___x_575_ = lean_nat_div(v___x_573_, v___x_574_);
lean_dec(v___x_573_);
v___x_576_ = lean_array_get_size(v_buckets_x27_571_);
v___x_577_ = lean_nat_dec_le(v___x_575_, v___x_576_);
lean_dec(v___x_575_);
if (v___x_577_ == 0)
{
lean_object* v_val_578_; lean_object* v___x_580_; 
v_val_578_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2___redArg(v_buckets_x27_571_);
if (v_isShared_551_ == 0)
{
lean_ctor_set(v___x_550_, 1, v_val_578_);
lean_ctor_set(v___x_550_, 0, v_size_x27_569_);
v___x_580_ = v___x_550_;
goto v_reusejp_579_;
}
else
{
lean_object* v_reuseFailAlloc_581_; 
v_reuseFailAlloc_581_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_581_, 0, v_size_x27_569_);
lean_ctor_set(v_reuseFailAlloc_581_, 1, v_val_578_);
v___x_580_ = v_reuseFailAlloc_581_;
goto v_reusejp_579_;
}
v_reusejp_579_:
{
return v___x_580_;
}
}
else
{
lean_object* v___x_583_; 
if (v_isShared_551_ == 0)
{
lean_ctor_set(v___x_550_, 1, v_buckets_x27_571_);
lean_ctor_set(v___x_550_, 0, v_size_x27_569_);
v___x_583_ = v___x_550_;
goto v_reusejp_582_;
}
else
{
lean_object* v_reuseFailAlloc_584_; 
v_reuseFailAlloc_584_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_584_, 0, v_size_x27_569_);
lean_ctor_set(v_reuseFailAlloc_584_, 1, v_buckets_x27_571_);
v___x_583_ = v_reuseFailAlloc_584_;
goto v_reusejp_582_;
}
v_reusejp_582_:
{
return v___x_583_;
}
}
}
else
{
lean_object* v___x_585_; lean_object* v_buckets_x27_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_590_; 
lean_inc(v_bkt_566_);
v___x_585_ = lean_box(0);
v_buckets_x27_586_ = lean_array_uset(v_buckets_548_, v___x_565_, v___x_585_);
v___x_587_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__3___redArg(v_a_545_, v_b_546_, v_bkt_566_);
v___x_588_ = lean_array_uset(v_buckets_x27_586_, v___x_565_, v___x_587_);
if (v_isShared_551_ == 0)
{
lean_ctor_set(v___x_550_, 1, v___x_588_);
v___x_590_ = v___x_550_;
goto v_reusejp_589_;
}
else
{
lean_object* v_reuseFailAlloc_591_; 
v_reuseFailAlloc_591_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_591_, 0, v_size_547_);
lean_ctor_set(v_reuseFailAlloc_591_, 1, v___x_588_);
v___x_590_ = v_reuseFailAlloc_591_;
goto v_reusejp_589_;
}
v_reusejp_589_:
{
return v___x_590_;
}
}
}
}
}
}
static lean_object* _init_l_Lean_registerBuiltinAttribute___closed__1(void){
_start:
{
lean_object* v___x_596_; lean_object* v___x_597_; 
v___x_596_ = ((lean_object*)(l_Lean_registerBuiltinAttribute___closed__0));
v___x_597_ = lean_mk_io_user_error(v___x_596_);
return v___x_597_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerBuiltinAttribute(lean_object* v_attr_600_){
_start:
{
lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v_toAttributeImplCore_604_; lean_object* v_name_605_; uint8_t v___x_606_; 
v___x_602_ = l_Lean_attributeMapRef;
v___x_603_ = lean_st_ref_get(v___x_602_);
v_toAttributeImplCore_604_ = lean_ctor_get(v_attr_600_, 0);
v_name_605_ = lean_ctor_get(v_toAttributeImplCore_604_, 1);
lean_inc(v_name_605_);
v___x_606_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(v___x_603_, v_name_605_);
lean_dec(v___x_603_);
if (v___x_606_ == 0)
{
lean_object* v___x_607_; 
v___x_607_ = l_Lean_initializing();
if (lean_obj_tag(v___x_607_) == 0)
{
lean_object* v_a_608_; lean_object* v___x_610_; uint8_t v_isShared_611_; uint8_t v_isSharedCheck_623_; 
v_a_608_ = lean_ctor_get(v___x_607_, 0);
v_isSharedCheck_623_ = !lean_is_exclusive(v___x_607_);
if (v_isSharedCheck_623_ == 0)
{
v___x_610_ = v___x_607_;
v_isShared_611_ = v_isSharedCheck_623_;
goto v_resetjp_609_;
}
else
{
lean_inc(v_a_608_);
lean_dec(v___x_607_);
v___x_610_ = lean_box(0);
v_isShared_611_ = v_isSharedCheck_623_;
goto v_resetjp_609_;
}
v_resetjp_609_:
{
uint8_t v___x_612_; 
v___x_612_ = lean_unbox(v_a_608_);
lean_dec(v_a_608_);
if (v___x_612_ == 0)
{
lean_object* v___x_613_; lean_object* v___x_615_; 
lean_dec(v_name_605_);
lean_dec_ref(v_attr_600_);
v___x_613_ = lean_obj_once(&l_Lean_registerBuiltinAttribute___closed__1, &l_Lean_registerBuiltinAttribute___closed__1_once, _init_l_Lean_registerBuiltinAttribute___closed__1);
if (v_isShared_611_ == 0)
{
lean_ctor_set_tag(v___x_610_, 1);
lean_ctor_set(v___x_610_, 0, v___x_613_);
v___x_615_ = v___x_610_;
goto v_reusejp_614_;
}
else
{
lean_object* v_reuseFailAlloc_616_; 
v_reuseFailAlloc_616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_616_, 0, v___x_613_);
v___x_615_ = v_reuseFailAlloc_616_;
goto v_reusejp_614_;
}
v_reusejp_614_:
{
return v___x_615_;
}
}
else
{
lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_621_; 
v___x_617_ = lean_st_ref_take(v___x_602_);
v___x_618_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1___redArg(v___x_617_, v_name_605_, v_attr_600_);
v___x_619_ = lean_st_ref_set(v___x_602_, v___x_618_);
if (v_isShared_611_ == 0)
{
lean_ctor_set(v___x_610_, 0, v___x_619_);
v___x_621_ = v___x_610_;
goto v_reusejp_620_;
}
else
{
lean_object* v_reuseFailAlloc_622_; 
v_reuseFailAlloc_622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_622_, 0, v___x_619_);
v___x_621_ = v_reuseFailAlloc_622_;
goto v_reusejp_620_;
}
v_reusejp_620_:
{
return v___x_621_;
}
}
}
}
else
{
lean_object* v_a_624_; lean_object* v___x_626_; uint8_t v_isShared_627_; uint8_t v_isSharedCheck_631_; 
lean_dec(v_name_605_);
lean_dec_ref(v_attr_600_);
v_a_624_ = lean_ctor_get(v___x_607_, 0);
v_isSharedCheck_631_ = !lean_is_exclusive(v___x_607_);
if (v_isSharedCheck_631_ == 0)
{
v___x_626_ = v___x_607_;
v_isShared_627_ = v_isSharedCheck_631_;
goto v_resetjp_625_;
}
else
{
lean_inc(v_a_624_);
lean_dec(v___x_607_);
v___x_626_ = lean_box(0);
v_isShared_627_ = v_isSharedCheck_631_;
goto v_resetjp_625_;
}
v_resetjp_625_:
{
lean_object* v___x_629_; 
if (v_isShared_627_ == 0)
{
v___x_629_ = v___x_626_;
goto v_reusejp_628_;
}
else
{
lean_object* v_reuseFailAlloc_630_; 
v_reuseFailAlloc_630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_630_, 0, v_a_624_);
v___x_629_ = v_reuseFailAlloc_630_;
goto v_reusejp_628_;
}
v_reusejp_628_:
{
return v___x_629_;
}
}
}
}
else
{
lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; 
lean_dec_ref(v_attr_600_);
v___x_632_ = ((lean_object*)(l_Lean_registerBuiltinAttribute___closed__2));
v___x_633_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_605_, v___x_606_);
v___x_634_ = lean_string_append(v___x_632_, v___x_633_);
lean_dec_ref(v___x_633_);
v___x_635_ = ((lean_object*)(l_Lean_registerBuiltinAttribute___closed__3));
v___x_636_ = lean_string_append(v___x_634_, v___x_635_);
v___x_637_ = lean_mk_io_user_error(v___x_636_);
v___x_638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_638_, 0, v___x_637_);
return v___x_638_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerBuiltinAttribute___boxed(lean_object* v_attr_639_, lean_object* v_a_640_){
_start:
{
lean_object* v_res_641_; 
v_res_641_ = l_Lean_registerBuiltinAttribute(v_attr_639_);
return v_res_641_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0(lean_object* v_00_u03b2_642_, lean_object* v_m_643_, lean_object* v_a_644_){
_start:
{
uint8_t v___x_645_; 
v___x_645_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(v_m_643_, v_a_644_);
return v___x_645_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___boxed(lean_object* v_00_u03b2_646_, lean_object* v_m_647_, lean_object* v_a_648_){
_start:
{
uint8_t v_res_649_; lean_object* v_r_650_; 
v_res_649_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0(v_00_u03b2_646_, v_m_647_, v_a_648_);
lean_dec(v_a_648_);
lean_dec_ref(v_m_647_);
v_r_650_ = lean_box(v_res_649_);
return v_r_650_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1(lean_object* v_00_u03b2_651_, lean_object* v_m_652_, lean_object* v_a_653_, lean_object* v_b_654_){
_start:
{
lean_object* v___x_655_; 
v___x_655_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1___redArg(v_m_652_, v_a_653_, v_b_654_);
return v___x_655_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0_spec__0(lean_object* v_00_u03b2_656_, lean_object* v_a_657_, lean_object* v_x_658_){
_start:
{
uint8_t v___x_659_; 
v___x_659_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0_spec__0___redArg(v_a_657_, v_x_658_);
return v___x_659_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0_spec__0___boxed(lean_object* v_00_u03b2_660_, lean_object* v_a_661_, lean_object* v_x_662_){
_start:
{
uint8_t v_res_663_; lean_object* v_r_664_; 
v_res_663_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0_spec__0(v_00_u03b2_660_, v_a_661_, v_x_662_);
lean_dec(v_x_662_);
lean_dec(v_a_661_);
v_r_664_ = lean_box(v_res_663_);
return v_r_664_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2(lean_object* v_00_u03b2_665_, lean_object* v_data_666_){
_start:
{
lean_object* v___x_667_; 
v___x_667_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2___redArg(v_data_666_);
return v___x_667_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__3(lean_object* v_00_u03b2_668_, lean_object* v_a_669_, lean_object* v_b_670_, lean_object* v_x_671_){
_start:
{
lean_object* v___x_672_; 
v___x_672_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__3___redArg(v_a_669_, v_b_670_, v_x_671_);
return v___x_672_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_673_, lean_object* v_i_674_, lean_object* v_source_675_, lean_object* v_target_676_){
_start:
{
lean_object* v___x_677_; 
v___x_677_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2_spec__3___redArg(v_i_674_, v_source_675_, v_target_676_);
return v___x_677_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_678_, lean_object* v_x_679_, lean_object* v_x_680_){
_start:
{
lean_object* v___x_681_; 
v___x_681_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2_spec__3_spec__4___redArg(v_x_679_, v_x_680_);
return v___x_681_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg(lean_object* v_ref_682_, lean_object* v_msg_683_, lean_object* v___y_684_, lean_object* v___y_685_){
_start:
{
lean_object* v_fileName_687_; lean_object* v_fileMap_688_; lean_object* v_options_689_; lean_object* v_currRecDepth_690_; lean_object* v_maxRecDepth_691_; lean_object* v_ref_692_; lean_object* v_currNamespace_693_; lean_object* v_openDecls_694_; lean_object* v_initHeartbeats_695_; lean_object* v_maxHeartbeats_696_; lean_object* v_quotContext_697_; lean_object* v_currMacroScope_698_; uint8_t v_diag_699_; lean_object* v_cancelTk_x3f_700_; uint8_t v_suppressElabErrors_701_; lean_object* v_inheritedTraceOptions_702_; lean_object* v_ref_703_; lean_object* v___x_704_; lean_object* v___x_705_; 
v_fileName_687_ = lean_ctor_get(v___y_684_, 0);
v_fileMap_688_ = lean_ctor_get(v___y_684_, 1);
v_options_689_ = lean_ctor_get(v___y_684_, 2);
v_currRecDepth_690_ = lean_ctor_get(v___y_684_, 3);
v_maxRecDepth_691_ = lean_ctor_get(v___y_684_, 4);
v_ref_692_ = lean_ctor_get(v___y_684_, 5);
v_currNamespace_693_ = lean_ctor_get(v___y_684_, 6);
v_openDecls_694_ = lean_ctor_get(v___y_684_, 7);
v_initHeartbeats_695_ = lean_ctor_get(v___y_684_, 8);
v_maxHeartbeats_696_ = lean_ctor_get(v___y_684_, 9);
v_quotContext_697_ = lean_ctor_get(v___y_684_, 10);
v_currMacroScope_698_ = lean_ctor_get(v___y_684_, 11);
v_diag_699_ = lean_ctor_get_uint8(v___y_684_, sizeof(void*)*14);
v_cancelTk_x3f_700_ = lean_ctor_get(v___y_684_, 12);
v_suppressElabErrors_701_ = lean_ctor_get_uint8(v___y_684_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_702_ = lean_ctor_get(v___y_684_, 13);
v_ref_703_ = l_Lean_replaceRef(v_ref_682_, v_ref_692_);
lean_inc_ref(v_inheritedTraceOptions_702_);
lean_inc(v_cancelTk_x3f_700_);
lean_inc(v_currMacroScope_698_);
lean_inc(v_quotContext_697_);
lean_inc(v_maxHeartbeats_696_);
lean_inc(v_initHeartbeats_695_);
lean_inc(v_openDecls_694_);
lean_inc(v_currNamespace_693_);
lean_inc(v_maxRecDepth_691_);
lean_inc(v_currRecDepth_690_);
lean_inc_ref(v_options_689_);
lean_inc_ref(v_fileMap_688_);
lean_inc_ref(v_fileName_687_);
v___x_704_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_704_, 0, v_fileName_687_);
lean_ctor_set(v___x_704_, 1, v_fileMap_688_);
lean_ctor_set(v___x_704_, 2, v_options_689_);
lean_ctor_set(v___x_704_, 3, v_currRecDepth_690_);
lean_ctor_set(v___x_704_, 4, v_maxRecDepth_691_);
lean_ctor_set(v___x_704_, 5, v_ref_703_);
lean_ctor_set(v___x_704_, 6, v_currNamespace_693_);
lean_ctor_set(v___x_704_, 7, v_openDecls_694_);
lean_ctor_set(v___x_704_, 8, v_initHeartbeats_695_);
lean_ctor_set(v___x_704_, 9, v_maxHeartbeats_696_);
lean_ctor_set(v___x_704_, 10, v_quotContext_697_);
lean_ctor_set(v___x_704_, 11, v_currMacroScope_698_);
lean_ctor_set(v___x_704_, 12, v_cancelTk_x3f_700_);
lean_ctor_set(v___x_704_, 13, v_inheritedTraceOptions_702_);
lean_ctor_set_uint8(v___x_704_, sizeof(void*)*14, v_diag_699_);
lean_ctor_set_uint8(v___x_704_, sizeof(void*)*14 + 1, v_suppressElabErrors_701_);
v___x_705_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v_msg_683_, v___x_704_, v___y_685_);
lean_dec_ref_known(v___x_704_, 14);
return v___x_705_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg___boxed(lean_object* v_ref_706_, lean_object* v_msg_707_, lean_object* v___y_708_, lean_object* v___y_709_, lean_object* v___y_710_){
_start:
{
lean_object* v_res_711_; 
v_res_711_ = l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg(v_ref_706_, v_msg_707_, v___y_708_, v___y_709_);
lean_dec(v___y_709_);
lean_dec_ref(v___y_708_);
lean_dec(v_ref_706_);
return v_res_711_;
}
}
static lean_object* _init_l_Lean_Attribute_Builtin_ensureNoArgs___closed__4(void){
_start:
{
lean_object* v___x_720_; lean_object* v___x_721_; 
v___x_720_ = ((lean_object*)(l_Lean_Attribute_Builtin_ensureNoArgs___closed__3));
v___x_721_ = l_Lean_stringToMessageData(v___x_720_);
return v___x_721_;
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_ensureNoArgs(lean_object* v_stx_728_, lean_object* v_a_729_, lean_object* v_a_730_){
_start:
{
lean_object* v___x_732_; uint8_t v___y_743_; lean_object* v___x_749_; uint8_t v___x_750_; 
lean_inc(v_stx_728_);
v___x_732_ = l_Lean_Syntax_getKind(v_stx_728_);
v___x_749_ = ((lean_object*)(l_Lean_Attribute_Builtin_ensureNoArgs___closed__6));
v___x_750_ = lean_name_eq(v___x_732_, v___x_749_);
if (v___x_750_ == 0)
{
v___y_743_ = v___x_750_;
goto v___jp_742_;
}
else
{
lean_object* v___x_751_; lean_object* v___x_752_; uint8_t v___x_753_; 
v___x_751_ = lean_unsigned_to_nat(1u);
v___x_752_ = l_Lean_Syntax_getArg(v_stx_728_, v___x_751_);
v___x_753_ = l_Lean_Syntax_isNone(v___x_752_);
lean_dec(v___x_752_);
v___y_743_ = v___x_753_;
goto v___jp_742_;
}
v___jp_733_:
{
lean_object* v___x_734_; uint8_t v___x_735_; 
v___x_734_ = ((lean_object*)(l_Lean_Attribute_Builtin_ensureNoArgs___closed__2));
v___x_735_ = lean_name_eq(v___x_732_, v___x_734_);
lean_dec(v___x_732_);
if (v___x_735_ == 0)
{
if (lean_obj_tag(v_stx_728_) == 0)
{
lean_object* v___x_736_; lean_object* v___x_737_; 
v___x_736_ = lean_box(0);
v___x_737_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_737_, 0, v___x_736_);
return v___x_737_;
}
else
{
lean_object* v___x_738_; lean_object* v___x_739_; 
v___x_738_ = lean_obj_once(&l_Lean_Attribute_Builtin_ensureNoArgs___closed__4, &l_Lean_Attribute_Builtin_ensureNoArgs___closed__4_once, _init_l_Lean_Attribute_Builtin_ensureNoArgs___closed__4);
v___x_739_ = l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg(v_stx_728_, v___x_738_, v_a_729_, v_a_730_);
lean_dec(v_stx_728_);
return v___x_739_;
}
}
else
{
lean_object* v___x_740_; lean_object* v___x_741_; 
lean_dec(v_stx_728_);
v___x_740_ = lean_box(0);
v___x_741_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_741_, 0, v___x_740_);
return v___x_741_;
}
}
v___jp_742_:
{
if (v___y_743_ == 0)
{
goto v___jp_733_;
}
else
{
lean_object* v___x_744_; lean_object* v___x_745_; uint8_t v___x_746_; 
v___x_744_ = lean_unsigned_to_nat(2u);
v___x_745_ = l_Lean_Syntax_getArg(v_stx_728_, v___x_744_);
v___x_746_ = l_Lean_Syntax_isNone(v___x_745_);
lean_dec(v___x_745_);
if (v___x_746_ == 0)
{
goto v___jp_733_;
}
else
{
lean_object* v___x_747_; lean_object* v___x_748_; 
lean_dec(v___x_732_);
lean_dec(v_stx_728_);
v___x_747_ = lean_box(0);
v___x_748_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_748_, 0, v___x_747_);
return v___x_748_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_ensureNoArgs___boxed(lean_object* v_stx_754_, lean_object* v_a_755_, lean_object* v_a_756_, lean_object* v_a_757_){
_start:
{
lean_object* v_res_758_; 
v_res_758_ = l_Lean_Attribute_Builtin_ensureNoArgs(v_stx_754_, v_a_755_, v_a_756_);
lean_dec(v_a_756_);
lean_dec_ref(v_a_755_);
return v_res_758_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0(lean_object* v_00_u03b1_759_, lean_object* v_ref_760_, lean_object* v_msg_761_, lean_object* v___y_762_, lean_object* v___y_763_){
_start:
{
lean_object* v___x_765_; 
v___x_765_ = l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg(v_ref_760_, v_msg_761_, v___y_762_, v___y_763_);
return v___x_765_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___boxed(lean_object* v_00_u03b1_766_, lean_object* v_ref_767_, lean_object* v_msg_768_, lean_object* v___y_769_, lean_object* v___y_770_, lean_object* v___y_771_){
_start:
{
lean_object* v_res_772_; 
v_res_772_ = l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0(v_00_u03b1_766_, v_ref_767_, v_msg_768_, v___y_769_, v___y_770_);
lean_dec(v___y_770_);
lean_dec_ref(v___y_769_);
lean_dec(v_ref_767_);
return v_res_772_;
}
}
static lean_object* _init_l_Lean_Attribute_Builtin_getIdent_x3f___closed__5(void){
_start:
{
lean_object* v___x_786_; lean_object* v___x_787_; 
v___x_786_ = ((lean_object*)(l_Lean_Attribute_Builtin_getIdent_x3f___closed__4));
v___x_787_ = l_Lean_stringToMessageData(v___x_786_);
return v___x_787_;
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getIdent_x3f(lean_object* v_stx_788_, lean_object* v_a_789_, lean_object* v_a_790_){
_start:
{
lean_object* v___x_797_; lean_object* v___x_798_; uint8_t v___x_799_; 
lean_inc(v_stx_788_);
v___x_797_ = l_Lean_Syntax_getKind(v_stx_788_);
v___x_798_ = ((lean_object*)(l_Lean_Attribute_Builtin_ensureNoArgs___closed__6));
v___x_799_ = lean_name_eq(v___x_797_, v___x_798_);
if (v___x_799_ == 0)
{
lean_object* v___x_800_; uint8_t v___x_801_; 
v___x_800_ = ((lean_object*)(l_Lean_Attribute_Builtin_getIdent_x3f___closed__1));
v___x_801_ = lean_name_eq(v___x_797_, v___x_800_);
if (v___x_801_ == 0)
{
lean_object* v___x_802_; uint8_t v___x_803_; 
v___x_802_ = ((lean_object*)(l_Lean_Attribute_Builtin_getIdent_x3f___closed__3));
v___x_803_ = lean_name_eq(v___x_797_, v___x_802_);
lean_dec(v___x_797_);
if (v___x_803_ == 0)
{
lean_object* v___x_804_; lean_object* v___x_805_; 
v___x_804_ = lean_obj_once(&l_Lean_Attribute_Builtin_getIdent_x3f___closed__5, &l_Lean_Attribute_Builtin_getIdent_x3f___closed__5_once, _init_l_Lean_Attribute_Builtin_getIdent_x3f___closed__5);
v___x_805_ = l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg(v_stx_788_, v___x_804_, v_a_789_, v_a_790_);
lean_dec(v_stx_788_);
return v___x_805_;
}
else
{
goto v___jp_792_;
}
}
else
{
lean_dec(v___x_797_);
goto v___jp_792_;
}
}
else
{
lean_object* v___x_806_; lean_object* v___x_807_; uint8_t v___y_809_; uint8_t v___x_816_; uint8_t v___x_817_; 
lean_dec(v___x_797_);
v___x_806_ = lean_unsigned_to_nat(1u);
v___x_807_ = l_Lean_Syntax_getArg(v_stx_788_, v___x_806_);
lean_dec(v_stx_788_);
v___x_816_ = l_Lean_Syntax_isNone(v___x_807_);
v___x_817_ = lean_bool_not(v___x_816_);
if (v___x_817_ == 0)
{
v___y_809_ = v___x_817_;
goto v___jp_808_;
}
else
{
lean_object* v___x_818_; lean_object* v___x_819_; uint8_t v___x_820_; 
v___x_818_ = lean_unsigned_to_nat(0u);
v___x_819_ = l_Lean_Syntax_getArg(v___x_807_, v___x_818_);
v___x_820_ = l_Lean_Syntax_isIdent(v___x_819_);
lean_dec(v___x_819_);
v___y_809_ = v___x_820_;
goto v___jp_808_;
}
v___jp_808_:
{
if (v___y_809_ == 0)
{
lean_object* v___x_810_; lean_object* v___x_811_; 
lean_dec(v___x_807_);
v___x_810_ = lean_box(0);
v___x_811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_811_, 0, v___x_810_);
return v___x_811_;
}
else
{
lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; 
v___x_812_ = lean_unsigned_to_nat(0u);
v___x_813_ = l_Lean_Syntax_getArg(v___x_807_, v___x_812_);
lean_dec(v___x_807_);
v___x_814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_814_, 0, v___x_813_);
v___x_815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_815_, 0, v___x_814_);
return v___x_815_;
}
}
}
v___jp_792_:
{
lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; 
v___x_793_ = lean_unsigned_to_nat(1u);
v___x_794_ = l_Lean_Syntax_getArg(v_stx_788_, v___x_793_);
lean_dec(v_stx_788_);
v___x_795_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_795_, 0, v___x_794_);
v___x_796_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_796_, 0, v___x_795_);
return v___x_796_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getIdent_x3f___boxed(lean_object* v_stx_821_, lean_object* v_a_822_, lean_object* v_a_823_, lean_object* v_a_824_){
_start:
{
lean_object* v_res_825_; 
v_res_825_ = l_Lean_Attribute_Builtin_getIdent_x3f(v_stx_821_, v_a_822_, v_a_823_);
lean_dec(v_a_823_);
lean_dec_ref(v_a_822_);
return v_res_825_;
}
}
static lean_object* _init_l_Lean_Attribute_Builtin_getIdent___closed__1(void){
_start:
{
lean_object* v___x_827_; lean_object* v___x_828_; 
v___x_827_ = ((lean_object*)(l_Lean_Attribute_Builtin_getIdent___closed__0));
v___x_828_ = l_Lean_stringToMessageData(v___x_827_);
return v___x_828_;
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getIdent(lean_object* v_stx_829_, lean_object* v_a_830_, lean_object* v_a_831_){
_start:
{
lean_object* v___x_833_; 
lean_inc(v_stx_829_);
v___x_833_ = l_Lean_Attribute_Builtin_getIdent_x3f(v_stx_829_, v_a_830_, v_a_831_);
if (lean_obj_tag(v___x_833_) == 0)
{
lean_object* v_a_834_; lean_object* v___x_836_; uint8_t v_isShared_837_; uint8_t v_isSharedCheck_847_; 
v_a_834_ = lean_ctor_get(v___x_833_, 0);
v_isSharedCheck_847_ = !lean_is_exclusive(v___x_833_);
if (v_isSharedCheck_847_ == 0)
{
v___x_836_ = v___x_833_;
v_isShared_837_ = v_isSharedCheck_847_;
goto v_resetjp_835_;
}
else
{
lean_inc(v_a_834_);
lean_dec(v___x_833_);
v___x_836_ = lean_box(0);
v_isShared_837_ = v_isSharedCheck_847_;
goto v_resetjp_835_;
}
v_resetjp_835_:
{
if (lean_obj_tag(v_a_834_) == 0)
{
lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; 
lean_del_object(v___x_836_);
v___x_838_ = lean_obj_once(&l_Lean_Attribute_Builtin_getIdent___closed__1, &l_Lean_Attribute_Builtin_getIdent___closed__1_once, _init_l_Lean_Attribute_Builtin_getIdent___closed__1);
lean_inc(v_stx_829_);
v___x_839_ = l_Lean_MessageData_ofSyntax(v_stx_829_);
v___x_840_ = l_Lean_indentD(v___x_839_);
v___x_841_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_841_, 0, v___x_838_);
lean_ctor_set(v___x_841_, 1, v___x_840_);
v___x_842_ = l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg(v_stx_829_, v___x_841_, v_a_830_, v_a_831_);
lean_dec(v_stx_829_);
return v___x_842_;
}
else
{
lean_object* v_val_843_; lean_object* v___x_845_; 
lean_dec(v_stx_829_);
v_val_843_ = lean_ctor_get(v_a_834_, 0);
lean_inc(v_val_843_);
lean_dec_ref_known(v_a_834_, 1);
if (v_isShared_837_ == 0)
{
lean_ctor_set(v___x_836_, 0, v_val_843_);
v___x_845_ = v___x_836_;
goto v_reusejp_844_;
}
else
{
lean_object* v_reuseFailAlloc_846_; 
v_reuseFailAlloc_846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_846_, 0, v_val_843_);
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
else
{
lean_object* v_a_848_; lean_object* v___x_850_; uint8_t v_isShared_851_; uint8_t v_isSharedCheck_855_; 
lean_dec(v_stx_829_);
v_a_848_ = lean_ctor_get(v___x_833_, 0);
v_isSharedCheck_855_ = !lean_is_exclusive(v___x_833_);
if (v_isSharedCheck_855_ == 0)
{
v___x_850_ = v___x_833_;
v_isShared_851_ = v_isSharedCheck_855_;
goto v_resetjp_849_;
}
else
{
lean_inc(v_a_848_);
lean_dec(v___x_833_);
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
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getIdent___boxed(lean_object* v_stx_856_, lean_object* v_a_857_, lean_object* v_a_858_, lean_object* v_a_859_){
_start:
{
lean_object* v_res_860_; 
v_res_860_ = l_Lean_Attribute_Builtin_getIdent(v_stx_856_, v_a_857_, v_a_858_);
lean_dec(v_a_858_);
lean_dec_ref(v_a_857_);
return v_res_860_;
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getId_x3f(lean_object* v_stx_861_, lean_object* v_a_862_, lean_object* v_a_863_){
_start:
{
lean_object* v___x_865_; 
v___x_865_ = l_Lean_Attribute_Builtin_getIdent_x3f(v_stx_861_, v_a_862_, v_a_863_);
if (lean_obj_tag(v___x_865_) == 0)
{
lean_object* v_a_866_; lean_object* v___x_868_; uint8_t v_isShared_869_; uint8_t v_isSharedCheck_886_; 
v_a_866_ = lean_ctor_get(v___x_865_, 0);
v_isSharedCheck_886_ = !lean_is_exclusive(v___x_865_);
if (v_isSharedCheck_886_ == 0)
{
v___x_868_ = v___x_865_;
v_isShared_869_ = v_isSharedCheck_886_;
goto v_resetjp_867_;
}
else
{
lean_inc(v_a_866_);
lean_dec(v___x_865_);
v___x_868_ = lean_box(0);
v_isShared_869_ = v_isSharedCheck_886_;
goto v_resetjp_867_;
}
v_resetjp_867_:
{
if (lean_obj_tag(v_a_866_) == 0)
{
lean_object* v___x_870_; lean_object* v___x_872_; 
v___x_870_ = lean_box(0);
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
else
{
lean_object* v_val_874_; lean_object* v___x_876_; uint8_t v_isShared_877_; uint8_t v_isSharedCheck_885_; 
v_val_874_ = lean_ctor_get(v_a_866_, 0);
v_isSharedCheck_885_ = !lean_is_exclusive(v_a_866_);
if (v_isSharedCheck_885_ == 0)
{
v___x_876_ = v_a_866_;
v_isShared_877_ = v_isSharedCheck_885_;
goto v_resetjp_875_;
}
else
{
lean_inc(v_val_874_);
lean_dec(v_a_866_);
v___x_876_ = lean_box(0);
v_isShared_877_ = v_isSharedCheck_885_;
goto v_resetjp_875_;
}
v_resetjp_875_:
{
lean_object* v___x_878_; lean_object* v___x_880_; 
v___x_878_ = l_Lean_Syntax_getId(v_val_874_);
lean_dec(v_val_874_);
if (v_isShared_877_ == 0)
{
lean_ctor_set(v___x_876_, 0, v___x_878_);
v___x_880_ = v___x_876_;
goto v_reusejp_879_;
}
else
{
lean_object* v_reuseFailAlloc_884_; 
v_reuseFailAlloc_884_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_884_, 0, v___x_878_);
v___x_880_ = v_reuseFailAlloc_884_;
goto v_reusejp_879_;
}
v_reusejp_879_:
{
lean_object* v___x_882_; 
if (v_isShared_869_ == 0)
{
lean_ctor_set(v___x_868_, 0, v___x_880_);
v___x_882_ = v___x_868_;
goto v_reusejp_881_;
}
else
{
lean_object* v_reuseFailAlloc_883_; 
v_reuseFailAlloc_883_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_883_, 0, v___x_880_);
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
}
else
{
lean_object* v_a_887_; lean_object* v___x_889_; uint8_t v_isShared_890_; uint8_t v_isSharedCheck_894_; 
v_a_887_ = lean_ctor_get(v___x_865_, 0);
v_isSharedCheck_894_ = !lean_is_exclusive(v___x_865_);
if (v_isSharedCheck_894_ == 0)
{
v___x_889_ = v___x_865_;
v_isShared_890_ = v_isSharedCheck_894_;
goto v_resetjp_888_;
}
else
{
lean_inc(v_a_887_);
lean_dec(v___x_865_);
v___x_889_ = lean_box(0);
v_isShared_890_ = v_isSharedCheck_894_;
goto v_resetjp_888_;
}
v_resetjp_888_:
{
lean_object* v___x_892_; 
if (v_isShared_890_ == 0)
{
v___x_892_ = v___x_889_;
goto v_reusejp_891_;
}
else
{
lean_object* v_reuseFailAlloc_893_; 
v_reuseFailAlloc_893_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_893_, 0, v_a_887_);
v___x_892_ = v_reuseFailAlloc_893_;
goto v_reusejp_891_;
}
v_reusejp_891_:
{
return v___x_892_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getId_x3f___boxed(lean_object* v_stx_895_, lean_object* v_a_896_, lean_object* v_a_897_, lean_object* v_a_898_){
_start:
{
lean_object* v_res_899_; 
v_res_899_ = l_Lean_Attribute_Builtin_getId_x3f(v_stx_895_, v_a_896_, v_a_897_);
lean_dec(v_a_897_);
lean_dec_ref(v_a_896_);
return v_res_899_;
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getId(lean_object* v_stx_900_, lean_object* v_a_901_, lean_object* v_a_902_){
_start:
{
lean_object* v___x_904_; 
v___x_904_ = l_Lean_Attribute_Builtin_getIdent(v_stx_900_, v_a_901_, v_a_902_);
if (lean_obj_tag(v___x_904_) == 0)
{
lean_object* v_a_905_; lean_object* v___x_907_; uint8_t v_isShared_908_; uint8_t v_isSharedCheck_913_; 
v_a_905_ = lean_ctor_get(v___x_904_, 0);
v_isSharedCheck_913_ = !lean_is_exclusive(v___x_904_);
if (v_isSharedCheck_913_ == 0)
{
v___x_907_ = v___x_904_;
v_isShared_908_ = v_isSharedCheck_913_;
goto v_resetjp_906_;
}
else
{
lean_inc(v_a_905_);
lean_dec(v___x_904_);
v___x_907_ = lean_box(0);
v_isShared_908_ = v_isSharedCheck_913_;
goto v_resetjp_906_;
}
v_resetjp_906_:
{
lean_object* v___x_909_; lean_object* v___x_911_; 
v___x_909_ = l_Lean_Syntax_getId(v_a_905_);
lean_dec(v_a_905_);
if (v_isShared_908_ == 0)
{
lean_ctor_set(v___x_907_, 0, v___x_909_);
v___x_911_ = v___x_907_;
goto v_reusejp_910_;
}
else
{
lean_object* v_reuseFailAlloc_912_; 
v_reuseFailAlloc_912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_912_, 0, v___x_909_);
v___x_911_ = v_reuseFailAlloc_912_;
goto v_reusejp_910_;
}
v_reusejp_910_:
{
return v___x_911_;
}
}
}
else
{
lean_object* v_a_914_; lean_object* v___x_916_; uint8_t v_isShared_917_; uint8_t v_isSharedCheck_921_; 
v_a_914_ = lean_ctor_get(v___x_904_, 0);
v_isSharedCheck_921_ = !lean_is_exclusive(v___x_904_);
if (v_isSharedCheck_921_ == 0)
{
v___x_916_ = v___x_904_;
v_isShared_917_ = v_isSharedCheck_921_;
goto v_resetjp_915_;
}
else
{
lean_inc(v_a_914_);
lean_dec(v___x_904_);
v___x_916_ = lean_box(0);
v_isShared_917_ = v_isSharedCheck_921_;
goto v_resetjp_915_;
}
v_resetjp_915_:
{
lean_object* v___x_919_; 
if (v_isShared_917_ == 0)
{
v___x_919_ = v___x_916_;
goto v_reusejp_918_;
}
else
{
lean_object* v_reuseFailAlloc_920_; 
v_reuseFailAlloc_920_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_920_, 0, v_a_914_);
v___x_919_ = v_reuseFailAlloc_920_;
goto v_reusejp_918_;
}
v_reusejp_918_:
{
return v___x_919_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getId___boxed(lean_object* v_stx_922_, lean_object* v_a_923_, lean_object* v_a_924_, lean_object* v_a_925_){
_start:
{
lean_object* v_res_926_; 
v_res_926_ = l_Lean_Attribute_Builtin_getId(v_stx_922_, v_a_923_, v_a_924_);
lean_dec(v_a_924_);
lean_dec_ref(v_a_923_);
return v_res_926_;
}
}
static lean_object* _init_l_Lean_getAttrParamOptPrio___closed__1(void){
_start:
{
lean_object* v___x_928_; lean_object* v___x_929_; 
v___x_928_ = ((lean_object*)(l_Lean_getAttrParamOptPrio___closed__0));
v___x_929_ = l_Lean_stringToMessageData(v___x_928_);
return v___x_929_;
}
}
LEAN_EXPORT lean_object* l_Lean_getAttrParamOptPrio(lean_object* v_optPrioStx_930_, lean_object* v_a_931_, lean_object* v_a_932_){
_start:
{
uint8_t v___x_934_; 
v___x_934_ = l_Lean_Syntax_isNone(v_optPrioStx_930_);
if (v___x_934_ == 0)
{
lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; 
v___x_935_ = lean_unsigned_to_nat(0u);
v___x_936_ = l_Lean_Syntax_getArg(v_optPrioStx_930_, v___x_935_);
v___x_937_ = l_Lean_Syntax_isNatLit_x3f(v___x_936_);
lean_dec(v___x_936_);
if (lean_obj_tag(v___x_937_) == 0)
{
lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; 
v___x_938_ = lean_obj_once(&l_Lean_getAttrParamOptPrio___closed__1, &l_Lean_getAttrParamOptPrio___closed__1_once, _init_l_Lean_getAttrParamOptPrio___closed__1);
lean_inc(v_optPrioStx_930_);
v___x_939_ = l_Lean_MessageData_ofSyntax(v_optPrioStx_930_);
v___x_940_ = l_Lean_indentD(v___x_939_);
v___x_941_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_941_, 0, v___x_938_);
lean_ctor_set(v___x_941_, 1, v___x_940_);
v___x_942_ = l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg(v_optPrioStx_930_, v___x_941_, v_a_931_, v_a_932_);
lean_dec(v_optPrioStx_930_);
return v___x_942_;
}
else
{
lean_object* v_val_943_; lean_object* v___x_945_; uint8_t v_isShared_946_; uint8_t v_isSharedCheck_950_; 
lean_dec(v_optPrioStx_930_);
v_val_943_ = lean_ctor_get(v___x_937_, 0);
v_isSharedCheck_950_ = !lean_is_exclusive(v___x_937_);
if (v_isSharedCheck_950_ == 0)
{
v___x_945_ = v___x_937_;
v_isShared_946_ = v_isSharedCheck_950_;
goto v_resetjp_944_;
}
else
{
lean_inc(v_val_943_);
lean_dec(v___x_937_);
v___x_945_ = lean_box(0);
v_isShared_946_ = v_isSharedCheck_950_;
goto v_resetjp_944_;
}
v_resetjp_944_:
{
lean_object* v___x_948_; 
if (v_isShared_946_ == 0)
{
lean_ctor_set_tag(v___x_945_, 0);
v___x_948_ = v___x_945_;
goto v_reusejp_947_;
}
else
{
lean_object* v_reuseFailAlloc_949_; 
v_reuseFailAlloc_949_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_949_, 0, v_val_943_);
v___x_948_ = v_reuseFailAlloc_949_;
goto v_reusejp_947_;
}
v_reusejp_947_:
{
return v___x_948_;
}
}
}
}
else
{
lean_object* v___x_951_; lean_object* v___x_952_; 
lean_dec(v_optPrioStx_930_);
v___x_951_ = lean_unsigned_to_nat(1000u);
v___x_952_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_952_, 0, v___x_951_);
return v___x_952_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getAttrParamOptPrio___boxed(lean_object* v_optPrioStx_953_, lean_object* v_a_954_, lean_object* v_a_955_, lean_object* v_a_956_){
_start:
{
lean_object* v_res_957_; 
v_res_957_ = l_Lean_getAttrParamOptPrio(v_optPrioStx_953_, v_a_954_, v_a_955_);
lean_dec(v_a_955_);
lean_dec_ref(v_a_954_);
return v_res_957_;
}
}
static lean_object* _init_l_Lean_Attribute_Builtin_getPrio___closed__1(void){
_start:
{
lean_object* v___x_959_; lean_object* v___x_960_; 
v___x_959_ = ((lean_object*)(l_Lean_Attribute_Builtin_getPrio___closed__0));
v___x_960_ = l_Lean_stringToMessageData(v___x_959_);
return v___x_960_;
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getPrio(lean_object* v_stx_961_, lean_object* v_a_962_, lean_object* v_a_963_){
_start:
{
lean_object* v___x_965_; lean_object* v___x_966_; uint8_t v___x_967_; 
lean_inc(v_stx_961_);
v___x_965_ = l_Lean_Syntax_getKind(v_stx_961_);
v___x_966_ = ((lean_object*)(l_Lean_Attribute_Builtin_ensureNoArgs___closed__6));
v___x_967_ = lean_name_eq(v___x_965_, v___x_966_);
lean_dec(v___x_965_);
if (v___x_967_ == 0)
{
lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; 
v___x_968_ = lean_obj_once(&l_Lean_Attribute_Builtin_getPrio___closed__1, &l_Lean_Attribute_Builtin_getPrio___closed__1_once, _init_l_Lean_Attribute_Builtin_getPrio___closed__1);
lean_inc(v_stx_961_);
v___x_969_ = l_Lean_MessageData_ofSyntax(v_stx_961_);
v___x_970_ = l_Lean_indentD(v___x_969_);
v___x_971_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_971_, 0, v___x_968_);
lean_ctor_set(v___x_971_, 1, v___x_970_);
v___x_972_ = l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg(v_stx_961_, v___x_971_, v_a_962_, v_a_963_);
lean_dec(v_stx_961_);
return v___x_972_;
}
else
{
lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; 
v___x_973_ = lean_unsigned_to_nat(1u);
v___x_974_ = l_Lean_Syntax_getArg(v_stx_961_, v___x_973_);
lean_dec(v_stx_961_);
v___x_975_ = l_Lean_getAttrParamOptPrio(v___x_974_, v_a_962_, v_a_963_);
return v___x_975_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getPrio___boxed(lean_object* v_stx_976_, lean_object* v_a_977_, lean_object* v_a_978_, lean_object* v_a_979_){
_start:
{
lean_object* v_res_980_; 
v_res_980_ = l_Lean_Attribute_Builtin_getPrio(v_stx_976_, v_a_977_, v_a_978_);
lean_dec(v_a_978_);
lean_dec_ref(v_a_977_);
return v_res_980_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__1(void){
_start:
{
lean_object* v___x_982_; lean_object* v___x_983_; 
v___x_982_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__0));
v___x_983_ = l_Lean_stringToMessageData(v___x_982_);
return v___x_983_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__3(void){
_start:
{
lean_object* v___x_985_; lean_object* v___x_986_; 
v___x_985_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__2));
v___x_986_ = l_Lean_stringToMessageData(v___x_985_);
return v___x_986_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__5(void){
_start:
{
lean_object* v___x_988_; lean_object* v___x_989_; 
v___x_988_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__4));
v___x_989_ = l_Lean_stringToMessageData(v___x_988_);
return v___x_989_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___redArg(lean_object* v_inst_990_, lean_object* v_inst_991_, lean_object* v_name_992_, uint8_t v_kind_993_){
_start:
{
lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___y_1000_; 
v___x_994_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__1, &l_Lean_throwAttrMustBeGlobal___redArg___closed__1_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__1);
v___x_995_ = l_Lean_MessageData_ofName(v_name_992_);
v___x_996_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_996_, 0, v___x_994_);
lean_ctor_set(v___x_996_, 1, v___x_995_);
v___x_997_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__3, &l_Lean_throwAttrMustBeGlobal___redArg___closed__3_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__3);
v___x_998_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_998_, 0, v___x_996_);
lean_ctor_set(v___x_998_, 1, v___x_997_);
switch(v_kind_993_)
{
case 0:
{
lean_object* v___x_1007_; 
v___x_1007_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__0));
v___y_1000_ = v___x_1007_;
goto v___jp_999_;
}
case 1:
{
lean_object* v___x_1008_; 
v___x_1008_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__1));
v___y_1000_ = v___x_1008_;
goto v___jp_999_;
}
default: 
{
lean_object* v___x_1009_; 
v___x_1009_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__2));
v___y_1000_ = v___x_1009_;
goto v___jp_999_;
}
}
v___jp_999_:
{
lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; 
lean_inc_ref(v___y_1000_);
v___x_1001_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1001_, 0, v___y_1000_);
v___x_1002_ = l_Lean_MessageData_ofFormat(v___x_1001_);
v___x_1003_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1003_, 0, v___x_998_);
lean_ctor_set(v___x_1003_, 1, v___x_1002_);
v___x_1004_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__5, &l_Lean_throwAttrMustBeGlobal___redArg___closed__5_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__5);
v___x_1005_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1005_, 0, v___x_1003_);
lean_ctor_set(v___x_1005_, 1, v___x_1004_);
v___x_1006_ = l_Lean_throwError___redArg(v_inst_990_, v_inst_991_, v___x_1005_);
return v___x_1006_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___redArg___boxed(lean_object* v_inst_1010_, lean_object* v_inst_1011_, lean_object* v_name_1012_, lean_object* v_kind_1013_){
_start:
{
uint8_t v_kind_boxed_1014_; lean_object* v_res_1015_; 
v_kind_boxed_1014_ = lean_unbox(v_kind_1013_);
v_res_1015_ = l_Lean_throwAttrMustBeGlobal___redArg(v_inst_1010_, v_inst_1011_, v_name_1012_, v_kind_boxed_1014_);
return v_res_1015_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal(lean_object* v_m_1016_, lean_object* v_inst_1017_, lean_object* v_inst_1018_, lean_object* v_00_u03b1_1019_, lean_object* v_name_1020_, uint8_t v_kind_1021_){
_start:
{
lean_object* v___x_1022_; 
v___x_1022_ = l_Lean_throwAttrMustBeGlobal___redArg(v_inst_1017_, v_inst_1018_, v_name_1020_, v_kind_1021_);
return v___x_1022_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___boxed(lean_object* v_m_1023_, lean_object* v_inst_1024_, lean_object* v_inst_1025_, lean_object* v_00_u03b1_1026_, lean_object* v_name_1027_, lean_object* v_kind_1028_){
_start:
{
uint8_t v_kind_boxed_1029_; lean_object* v_res_1030_; 
v_kind_boxed_1029_ = lean_unbox(v_kind_1028_);
v_res_1030_ = l_Lean_throwAttrMustBeGlobal(v_m_1023_, v_inst_1024_, v_inst_1025_, v_00_u03b1_1026_, v_name_1027_, v_kind_boxed_1029_);
return v_res_1030_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1(void){
_start:
{
lean_object* v___x_1032_; lean_object* v___x_1033_; 
v___x_1032_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___redArg___closed__0));
v___x_1033_ = l_Lean_stringToMessageData(v___x_1032_);
return v___x_1033_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__3(void){
_start:
{
lean_object* v___x_1035_; lean_object* v___x_1036_; 
v___x_1035_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___redArg___closed__2));
v___x_1036_ = l_Lean_stringToMessageData(v___x_1035_);
return v___x_1036_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__5(void){
_start:
{
lean_object* v___x_1038_; lean_object* v___x_1039_; 
v___x_1038_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___redArg___closed__4));
v___x_1039_ = l_Lean_stringToMessageData(v___x_1038_);
return v___x_1039_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___redArg(lean_object* v_inst_1040_, lean_object* v_inst_1041_, lean_object* v_attrName_1042_, lean_object* v_declName_1043_){
_start:
{
lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; uint8_t v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; 
v___x_1044_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1);
v___x_1045_ = l_Lean_MessageData_ofName(v_attrName_1042_);
v___x_1046_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1046_, 0, v___x_1044_);
lean_ctor_set(v___x_1046_, 1, v___x_1045_);
v___x_1047_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__3, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__3_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__3);
v___x_1048_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1048_, 0, v___x_1046_);
lean_ctor_set(v___x_1048_, 1, v___x_1047_);
v___x_1049_ = 0;
v___x_1050_ = l_Lean_MessageData_ofConstName(v_declName_1043_, v___x_1049_);
v___x_1051_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1051_, 0, v___x_1048_);
lean_ctor_set(v___x_1051_, 1, v___x_1050_);
v___x_1052_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__5, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__5_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__5);
v___x_1053_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1053_, 0, v___x_1051_);
lean_ctor_set(v___x_1053_, 1, v___x_1052_);
v___x_1054_ = l_Lean_throwError___redArg(v_inst_1040_, v_inst_1041_, v___x_1053_);
return v___x_1054_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule(lean_object* v_m_1055_, lean_object* v_inst_1056_, lean_object* v_inst_1057_, lean_object* v_00_u03b1_1058_, lean_object* v_attrName_1059_, lean_object* v_declName_1060_){
_start:
{
lean_object* v___x_1061_; 
v___x_1061_ = l_Lean_throwAttrDeclInImportedModule___redArg(v_inst_1056_, v_inst_1057_, v_attrName_1059_, v_declName_1060_);
return v___x_1061_;
}
}
static lean_object* _init_l_Lean_throwAttrNotInAsyncCtx___redArg___closed__1(void){
_start:
{
lean_object* v___x_1063_; lean_object* v___x_1064_; 
v___x_1063_ = ((lean_object*)(l_Lean_throwAttrNotInAsyncCtx___redArg___closed__0));
v___x_1064_ = l_Lean_stringToMessageData(v___x_1063_);
return v___x_1064_;
}
}
static lean_object* _init_l_Lean_throwAttrNotInAsyncCtx___redArg___closed__3(void){
_start:
{
lean_object* v___x_1066_; lean_object* v___x_1067_; 
v___x_1066_ = ((lean_object*)(l_Lean_throwAttrNotInAsyncCtx___redArg___closed__2));
v___x_1067_ = l_Lean_stringToMessageData(v___x_1066_);
return v___x_1067_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___redArg(lean_object* v_inst_1068_, lean_object* v_inst_1069_, lean_object* v_attrName_1070_, lean_object* v_declName_1071_, lean_object* v_asyncPrefix_x3f_1072_){
_start:
{
lean_object* v___y_1074_; 
if (lean_obj_tag(v_asyncPrefix_x3f_1072_) == 0)
{
lean_object* v___x_1087_; 
v___x_1087_ = l_Lean_MessageData_nil;
v___y_1074_ = v___x_1087_;
goto v___jp_1073_;
}
else
{
lean_object* v_val_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; 
v_val_1088_ = lean_ctor_get(v_asyncPrefix_x3f_1072_, 0);
lean_inc(v_val_1088_);
lean_dec_ref_known(v_asyncPrefix_x3f_1072_, 1);
v___x_1089_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___redArg___closed__3, &l_Lean_throwAttrNotInAsyncCtx___redArg___closed__3_once, _init_l_Lean_throwAttrNotInAsyncCtx___redArg___closed__3);
v___x_1090_ = l_Lean_MessageData_ofName(v_val_1088_);
v___x_1091_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1091_, 0, v___x_1089_);
lean_ctor_set(v___x_1091_, 1, v___x_1090_);
v___x_1092_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__5, &l_Lean_throwAttrMustBeGlobal___redArg___closed__5_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__5);
v___x_1093_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1093_, 0, v___x_1091_);
lean_ctor_set(v___x_1093_, 1, v___x_1092_);
v___y_1074_ = v___x_1093_;
goto v___jp_1073_;
}
v___jp_1073_:
{
lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; uint8_t v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; 
v___x_1075_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1);
v___x_1076_ = l_Lean_MessageData_ofName(v_attrName_1070_);
v___x_1077_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1077_, 0, v___x_1075_);
lean_ctor_set(v___x_1077_, 1, v___x_1076_);
v___x_1078_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__3, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__3_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__3);
v___x_1079_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1079_, 0, v___x_1077_);
lean_ctor_set(v___x_1079_, 1, v___x_1078_);
v___x_1080_ = 0;
v___x_1081_ = l_Lean_MessageData_ofConstName(v_declName_1071_, v___x_1080_);
v___x_1082_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1082_, 0, v___x_1079_);
lean_ctor_set(v___x_1082_, 1, v___x_1081_);
v___x_1083_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___redArg___closed__1, &l_Lean_throwAttrNotInAsyncCtx___redArg___closed__1_once, _init_l_Lean_throwAttrNotInAsyncCtx___redArg___closed__1);
v___x_1084_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1084_, 0, v___x_1082_);
lean_ctor_set(v___x_1084_, 1, v___x_1083_);
v___x_1085_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1085_, 0, v___x_1084_);
lean_ctor_set(v___x_1085_, 1, v___y_1074_);
v___x_1086_ = l_Lean_throwError___redArg(v_inst_1068_, v_inst_1069_, v___x_1085_);
return v___x_1086_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx(lean_object* v_m_1094_, lean_object* v_inst_1095_, lean_object* v_inst_1096_, lean_object* v_00_u03b1_1097_, lean_object* v_attrName_1098_, lean_object* v_declName_1099_, lean_object* v_asyncPrefix_x3f_1100_){
_start:
{
lean_object* v___x_1101_; 
v___x_1101_ = l_Lean_throwAttrNotInAsyncCtx___redArg(v_inst_1095_, v_inst_1096_, v_attrName_1098_, v_declName_1099_, v_asyncPrefix_x3f_1100_);
return v___x_1101_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1(void){
_start:
{
lean_object* v___x_1103_; lean_object* v___x_1104_; 
v___x_1103_ = ((lean_object*)(l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__0));
v___x_1104_ = l_Lean_stringToMessageData(v___x_1103_);
return v___x_1104_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__3(void){
_start:
{
lean_object* v___x_1106_; lean_object* v___x_1107_; 
v___x_1106_ = ((lean_object*)(l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__2));
v___x_1107_ = l_Lean_stringToMessageData(v___x_1106_);
return v___x_1107_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__5(void){
_start:
{
lean_object* v___x_1109_; lean_object* v___x_1110_; 
v___x_1109_ = ((lean_object*)(l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__4));
v___x_1110_ = l_Lean_stringToMessageData(v___x_1109_);
return v___x_1110_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__7(void){
_start:
{
lean_object* v___x_1112_; lean_object* v___x_1113_; 
v___x_1112_ = ((lean_object*)(l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__6));
v___x_1113_ = l_Lean_stringToMessageData(v___x_1112_);
return v___x_1113_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclNotOfExpectedType___redArg(lean_object* v_inst_1114_, lean_object* v_inst_1115_, lean_object* v_attrName_1116_, lean_object* v_declName_1117_, lean_object* v_givenType_1118_, lean_object* v_expectedType_1119_){
_start:
{
lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; uint8_t v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; 
v___x_1120_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1);
v___x_1121_ = l_Lean_MessageData_ofName(v_attrName_1116_);
lean_inc_ref(v___x_1121_);
v___x_1122_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1122_, 0, v___x_1120_);
lean_ctor_set(v___x_1122_, 1, v___x_1121_);
v___x_1123_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1, &l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1);
v___x_1124_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1124_, 0, v___x_1122_);
lean_ctor_set(v___x_1124_, 1, v___x_1123_);
v___x_1125_ = 0;
v___x_1126_ = l_Lean_MessageData_ofConstName(v_declName_1117_, v___x_1125_);
v___x_1127_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1127_, 0, v___x_1124_);
lean_ctor_set(v___x_1127_, 1, v___x_1126_);
v___x_1128_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__3, &l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__3_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__3);
v___x_1129_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1129_, 0, v___x_1127_);
lean_ctor_set(v___x_1129_, 1, v___x_1128_);
v___x_1130_ = l_Lean_indentExpr(v_givenType_1118_);
v___x_1131_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1131_, 0, v___x_1129_);
lean_ctor_set(v___x_1131_, 1, v___x_1130_);
v___x_1132_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__5, &l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__5_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__5);
v___x_1133_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1133_, 0, v___x_1131_);
lean_ctor_set(v___x_1133_, 1, v___x_1132_);
v___x_1134_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1134_, 0, v___x_1133_);
lean_ctor_set(v___x_1134_, 1, v___x_1121_);
v___x_1135_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__7, &l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__7_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__7);
v___x_1136_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1136_, 0, v___x_1134_);
lean_ctor_set(v___x_1136_, 1, v___x_1135_);
v___x_1137_ = l_Lean_indentExpr(v_expectedType_1119_);
v___x_1138_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1138_, 0, v___x_1136_);
lean_ctor_set(v___x_1138_, 1, v___x_1137_);
v___x_1139_ = l_Lean_throwError___redArg(v_inst_1114_, v_inst_1115_, v___x_1138_);
return v___x_1139_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclNotOfExpectedType(lean_object* v_m_1140_, lean_object* v_inst_1141_, lean_object* v_inst_1142_, lean_object* v_00_u03b1_1143_, lean_object* v_attrName_1144_, lean_object* v_declName_1145_, lean_object* v_givenType_1146_, lean_object* v_expectedType_1147_){
_start:
{
lean_object* v___x_1148_; 
v___x_1148_ = l_Lean_throwAttrDeclNotOfExpectedType___redArg(v_inst_1141_, v_inst_1142_, v_attrName_1144_, v_declName_1145_, v_givenType_1146_, v_expectedType_1147_);
return v___x_1148_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1___redArg(lean_object* v_constName_1149_, uint8_t v_skipRealize_1150_, lean_object* v___y_1151_){
_start:
{
lean_object* v___x_1153_; lean_object* v_env_1154_; uint8_t v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; 
v___x_1153_ = lean_st_ref_get(v___y_1151_);
v_env_1154_ = lean_ctor_get(v___x_1153_, 0);
lean_inc_ref(v_env_1154_);
lean_dec(v___x_1153_);
v___x_1155_ = l_Lean_Environment_contains(v_env_1154_, v_constName_1149_, v_skipRealize_1150_);
v___x_1156_ = lean_box(v___x_1155_);
v___x_1157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1157_, 0, v___x_1156_);
return v___x_1157_;
}
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
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1(lean_object* v_constName_1164_, uint8_t v_skipRealize_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_){
_start:
{
lean_object* v___x_1169_; 
v___x_1169_ = l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1___redArg(v_constName_1164_, v_skipRealize_1165_, v___y_1167_);
return v___x_1169_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1___boxed(lean_object* v_constName_1170_, lean_object* v_skipRealize_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_){
_start:
{
uint8_t v_skipRealize_boxed_1175_; lean_object* v_res_1176_; 
v_skipRealize_boxed_1175_ = lean_unbox(v_skipRealize_1171_);
v_res_1176_ = l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1(v_constName_1170_, v_skipRealize_boxed_1175_, v___y_1172_, v___y_1173_);
lean_dec(v___y_1173_);
lean_dec_ref(v___y_1172_);
return v_res_1176_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___lam__0(lean_object* v___y_1177_, uint8_t v_isExporting_1178_, lean_object* v___x_1179_, lean_object* v_a_x3f_1180_){
_start:
{
lean_object* v___x_1182_; lean_object* v_env_1183_; lean_object* v_nextMacroScope_1184_; lean_object* v_ngen_1185_; lean_object* v_auxDeclNGen_1186_; lean_object* v_traceState_1187_; lean_object* v_messages_1188_; lean_object* v_infoState_1189_; lean_object* v_snapshotTasks_1190_; lean_object* v___x_1192_; uint8_t v_isShared_1193_; uint8_t v_isSharedCheck_1201_; 
v___x_1182_ = lean_st_ref_take(v___y_1177_);
v_env_1183_ = lean_ctor_get(v___x_1182_, 0);
v_nextMacroScope_1184_ = lean_ctor_get(v___x_1182_, 1);
v_ngen_1185_ = lean_ctor_get(v___x_1182_, 2);
v_auxDeclNGen_1186_ = lean_ctor_get(v___x_1182_, 3);
v_traceState_1187_ = lean_ctor_get(v___x_1182_, 4);
v_messages_1188_ = lean_ctor_get(v___x_1182_, 6);
v_infoState_1189_ = lean_ctor_get(v___x_1182_, 7);
v_snapshotTasks_1190_ = lean_ctor_get(v___x_1182_, 8);
v_isSharedCheck_1201_ = !lean_is_exclusive(v___x_1182_);
if (v_isSharedCheck_1201_ == 0)
{
lean_object* v_unused_1202_; 
v_unused_1202_ = lean_ctor_get(v___x_1182_, 5);
lean_dec(v_unused_1202_);
v___x_1192_ = v___x_1182_;
v_isShared_1193_ = v_isSharedCheck_1201_;
goto v_resetjp_1191_;
}
else
{
lean_inc(v_snapshotTasks_1190_);
lean_inc(v_infoState_1189_);
lean_inc(v_messages_1188_);
lean_inc(v_traceState_1187_);
lean_inc(v_auxDeclNGen_1186_);
lean_inc(v_ngen_1185_);
lean_inc(v_nextMacroScope_1184_);
lean_inc(v_env_1183_);
lean_dec(v___x_1182_);
v___x_1192_ = lean_box(0);
v_isShared_1193_ = v_isSharedCheck_1201_;
goto v_resetjp_1191_;
}
v_resetjp_1191_:
{
lean_object* v___x_1194_; lean_object* v___x_1196_; 
v___x_1194_ = l_Lean_Environment_setExporting(v_env_1183_, v_isExporting_1178_);
if (v_isShared_1193_ == 0)
{
lean_ctor_set(v___x_1192_, 5, v___x_1179_);
lean_ctor_set(v___x_1192_, 0, v___x_1194_);
v___x_1196_ = v___x_1192_;
goto v_reusejp_1195_;
}
else
{
lean_object* v_reuseFailAlloc_1200_; 
v_reuseFailAlloc_1200_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1200_, 0, v___x_1194_);
lean_ctor_set(v_reuseFailAlloc_1200_, 1, v_nextMacroScope_1184_);
lean_ctor_set(v_reuseFailAlloc_1200_, 2, v_ngen_1185_);
lean_ctor_set(v_reuseFailAlloc_1200_, 3, v_auxDeclNGen_1186_);
lean_ctor_set(v_reuseFailAlloc_1200_, 4, v_traceState_1187_);
lean_ctor_set(v_reuseFailAlloc_1200_, 5, v___x_1179_);
lean_ctor_set(v_reuseFailAlloc_1200_, 6, v_messages_1188_);
lean_ctor_set(v_reuseFailAlloc_1200_, 7, v_infoState_1189_);
lean_ctor_set(v_reuseFailAlloc_1200_, 8, v_snapshotTasks_1190_);
v___x_1196_ = v_reuseFailAlloc_1200_;
goto v_reusejp_1195_;
}
v_reusejp_1195_:
{
lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; 
v___x_1197_ = lean_st_ref_set(v___y_1177_, v___x_1196_);
v___x_1198_ = lean_box(0);
v___x_1199_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1199_, 0, v___x_1198_);
return v___x_1199_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___lam__0___boxed(lean_object* v___y_1203_, lean_object* v_isExporting_1204_, lean_object* v___x_1205_, lean_object* v_a_x3f_1206_, lean_object* v___y_1207_){
_start:
{
uint8_t v_isExporting_boxed_1208_; lean_object* v_res_1209_; 
v_isExporting_boxed_1208_ = lean_unbox(v_isExporting_1204_);
v_res_1209_ = l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___lam__0(v___y_1203_, v_isExporting_boxed_1208_, v___x_1205_, v_a_x3f_1206_);
lean_dec(v_a_x3f_1206_);
lean_dec(v___y_1203_);
return v_res_1209_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_1210_; 
v___x_1210_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1210_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_1211_; lean_object* v___x_1212_; 
v___x_1211_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__0, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__0);
v___x_1212_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1212_, 0, v___x_1211_);
return v___x_1212_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_1213_; lean_object* v___x_1214_; 
v___x_1213_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1);
v___x_1214_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1214_, 0, v___x_1213_);
lean_ctor_set(v___x_1214_, 1, v___x_1213_);
return v___x_1214_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg(lean_object* v_x_1215_, uint8_t v_isExporting_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_){
_start:
{
lean_object* v___x_1220_; lean_object* v_env_1221_; uint8_t v_isExporting_1222_; uint8_t v___y_1274_; lean_object* v___x_1276_; uint8_t v_isModule_1277_; uint8_t v___x_1278_; 
v___x_1220_ = lean_st_ref_get(v___y_1218_);
v_env_1221_ = lean_ctor_get(v___x_1220_, 0);
lean_inc_ref(v_env_1221_);
lean_dec(v___x_1220_);
v_isExporting_1222_ = lean_ctor_get_uint8(v_env_1221_, sizeof(void*)*8);
v___x_1276_ = l_Lean_Environment_header(v_env_1221_);
lean_dec_ref(v_env_1221_);
v_isModule_1277_ = lean_ctor_get_uint8(v___x_1276_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_1276_);
v___x_1278_ = lean_bool_not(v_isModule_1277_);
if (v___x_1278_ == 0)
{
if (v_isExporting_1222_ == 0)
{
if (v_isExporting_1216_ == 0)
{
lean_object* v___x_1279_; 
lean_inc(v___y_1218_);
lean_inc_ref(v___y_1217_);
v___x_1279_ = lean_apply_3(v_x_1215_, v___y_1217_, v___y_1218_, lean_box(0));
return v___x_1279_;
}
else
{
goto v___jp_1223_;
}
}
else
{
v___y_1274_ = v_isExporting_1216_;
goto v___jp_1273_;
}
}
else
{
v___y_1274_ = v___x_1278_;
goto v___jp_1273_;
}
v___jp_1223_:
{
lean_object* v___x_1224_; lean_object* v_env_1225_; lean_object* v_nextMacroScope_1226_; lean_object* v_ngen_1227_; lean_object* v_auxDeclNGen_1228_; lean_object* v_traceState_1229_; lean_object* v_messages_1230_; lean_object* v_infoState_1231_; lean_object* v_snapshotTasks_1232_; lean_object* v___x_1234_; uint8_t v_isShared_1235_; uint8_t v_isSharedCheck_1271_; 
v___x_1224_ = lean_st_ref_take(v___y_1218_);
v_env_1225_ = lean_ctor_get(v___x_1224_, 0);
v_nextMacroScope_1226_ = lean_ctor_get(v___x_1224_, 1);
v_ngen_1227_ = lean_ctor_get(v___x_1224_, 2);
v_auxDeclNGen_1228_ = lean_ctor_get(v___x_1224_, 3);
v_traceState_1229_ = lean_ctor_get(v___x_1224_, 4);
v_messages_1230_ = lean_ctor_get(v___x_1224_, 6);
v_infoState_1231_ = lean_ctor_get(v___x_1224_, 7);
v_snapshotTasks_1232_ = lean_ctor_get(v___x_1224_, 8);
v_isSharedCheck_1271_ = !lean_is_exclusive(v___x_1224_);
if (v_isSharedCheck_1271_ == 0)
{
lean_object* v_unused_1272_; 
v_unused_1272_ = lean_ctor_get(v___x_1224_, 5);
lean_dec(v_unused_1272_);
v___x_1234_ = v___x_1224_;
v_isShared_1235_ = v_isSharedCheck_1271_;
goto v_resetjp_1233_;
}
else
{
lean_inc(v_snapshotTasks_1232_);
lean_inc(v_infoState_1231_);
lean_inc(v_messages_1230_);
lean_inc(v_traceState_1229_);
lean_inc(v_auxDeclNGen_1228_);
lean_inc(v_ngen_1227_);
lean_inc(v_nextMacroScope_1226_);
lean_inc(v_env_1225_);
lean_dec(v___x_1224_);
v___x_1234_ = lean_box(0);
v_isShared_1235_ = v_isSharedCheck_1271_;
goto v_resetjp_1233_;
}
v_resetjp_1233_:
{
lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1239_; 
v___x_1236_ = l_Lean_Environment_setExporting(v_env_1225_, v_isExporting_1216_);
v___x_1237_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2);
if (v_isShared_1235_ == 0)
{
lean_ctor_set(v___x_1234_, 5, v___x_1237_);
lean_ctor_set(v___x_1234_, 0, v___x_1236_);
v___x_1239_ = v___x_1234_;
goto v_reusejp_1238_;
}
else
{
lean_object* v_reuseFailAlloc_1270_; 
v_reuseFailAlloc_1270_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1270_, 0, v___x_1236_);
lean_ctor_set(v_reuseFailAlloc_1270_, 1, v_nextMacroScope_1226_);
lean_ctor_set(v_reuseFailAlloc_1270_, 2, v_ngen_1227_);
lean_ctor_set(v_reuseFailAlloc_1270_, 3, v_auxDeclNGen_1228_);
lean_ctor_set(v_reuseFailAlloc_1270_, 4, v_traceState_1229_);
lean_ctor_set(v_reuseFailAlloc_1270_, 5, v___x_1237_);
lean_ctor_set(v_reuseFailAlloc_1270_, 6, v_messages_1230_);
lean_ctor_set(v_reuseFailAlloc_1270_, 7, v_infoState_1231_);
lean_ctor_set(v_reuseFailAlloc_1270_, 8, v_snapshotTasks_1232_);
v___x_1239_ = v_reuseFailAlloc_1270_;
goto v_reusejp_1238_;
}
v_reusejp_1238_:
{
lean_object* v___x_1240_; lean_object* v_r_1241_; 
v___x_1240_ = lean_st_ref_set(v___y_1218_, v___x_1239_);
lean_inc(v___y_1218_);
lean_inc_ref(v___y_1217_);
v_r_1241_ = lean_apply_3(v_x_1215_, v___y_1217_, v___y_1218_, lean_box(0));
if (lean_obj_tag(v_r_1241_) == 0)
{
lean_object* v_a_1242_; lean_object* v___x_1244_; uint8_t v_isShared_1245_; uint8_t v_isSharedCheck_1258_; 
v_a_1242_ = lean_ctor_get(v_r_1241_, 0);
v_isSharedCheck_1258_ = !lean_is_exclusive(v_r_1241_);
if (v_isSharedCheck_1258_ == 0)
{
v___x_1244_ = v_r_1241_;
v_isShared_1245_ = v_isSharedCheck_1258_;
goto v_resetjp_1243_;
}
else
{
lean_inc(v_a_1242_);
lean_dec(v_r_1241_);
v___x_1244_ = lean_box(0);
v_isShared_1245_ = v_isSharedCheck_1258_;
goto v_resetjp_1243_;
}
v_resetjp_1243_:
{
lean_object* v___x_1247_; 
lean_inc(v_a_1242_);
if (v_isShared_1245_ == 0)
{
lean_ctor_set_tag(v___x_1244_, 1);
v___x_1247_ = v___x_1244_;
goto v_reusejp_1246_;
}
else
{
lean_object* v_reuseFailAlloc_1257_; 
v_reuseFailAlloc_1257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1257_, 0, v_a_1242_);
v___x_1247_ = v_reuseFailAlloc_1257_;
goto v_reusejp_1246_;
}
v_reusejp_1246_:
{
lean_object* v___x_1248_; lean_object* v___x_1250_; uint8_t v_isShared_1251_; uint8_t v_isSharedCheck_1255_; 
v___x_1248_ = l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___lam__0(v___y_1218_, v_isExporting_1222_, v___x_1237_, v___x_1247_);
lean_dec_ref(v___x_1247_);
v_isSharedCheck_1255_ = !lean_is_exclusive(v___x_1248_);
if (v_isSharedCheck_1255_ == 0)
{
lean_object* v_unused_1256_; 
v_unused_1256_ = lean_ctor_get(v___x_1248_, 0);
lean_dec(v_unused_1256_);
v___x_1250_ = v___x_1248_;
v_isShared_1251_ = v_isSharedCheck_1255_;
goto v_resetjp_1249_;
}
else
{
lean_dec(v___x_1248_);
v___x_1250_ = lean_box(0);
v_isShared_1251_ = v_isSharedCheck_1255_;
goto v_resetjp_1249_;
}
v_resetjp_1249_:
{
lean_object* v___x_1253_; 
if (v_isShared_1251_ == 0)
{
lean_ctor_set(v___x_1250_, 0, v_a_1242_);
v___x_1253_ = v___x_1250_;
goto v_reusejp_1252_;
}
else
{
lean_object* v_reuseFailAlloc_1254_; 
v_reuseFailAlloc_1254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1254_, 0, v_a_1242_);
v___x_1253_ = v_reuseFailAlloc_1254_;
goto v_reusejp_1252_;
}
v_reusejp_1252_:
{
return v___x_1253_;
}
}
}
}
}
else
{
lean_object* v_a_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1263_; uint8_t v_isShared_1264_; uint8_t v_isSharedCheck_1268_; 
v_a_1259_ = lean_ctor_get(v_r_1241_, 0);
lean_inc(v_a_1259_);
lean_dec_ref_known(v_r_1241_, 1);
v___x_1260_ = lean_box(0);
v___x_1261_ = l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___lam__0(v___y_1218_, v_isExporting_1222_, v___x_1237_, v___x_1260_);
v_isSharedCheck_1268_ = !lean_is_exclusive(v___x_1261_);
if (v_isSharedCheck_1268_ == 0)
{
lean_object* v_unused_1269_; 
v_unused_1269_ = lean_ctor_get(v___x_1261_, 0);
lean_dec(v_unused_1269_);
v___x_1263_ = v___x_1261_;
v_isShared_1264_ = v_isSharedCheck_1268_;
goto v_resetjp_1262_;
}
else
{
lean_dec(v___x_1261_);
v___x_1263_ = lean_box(0);
v_isShared_1264_ = v_isSharedCheck_1268_;
goto v_resetjp_1262_;
}
v_resetjp_1262_:
{
lean_object* v___x_1266_; 
if (v_isShared_1264_ == 0)
{
lean_ctor_set_tag(v___x_1263_, 1);
lean_ctor_set(v___x_1263_, 0, v_a_1259_);
v___x_1266_ = v___x_1263_;
goto v_reusejp_1265_;
}
else
{
lean_object* v_reuseFailAlloc_1267_; 
v_reuseFailAlloc_1267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1267_, 0, v_a_1259_);
v___x_1266_ = v_reuseFailAlloc_1267_;
goto v_reusejp_1265_;
}
v_reusejp_1265_:
{
return v___x_1266_;
}
}
}
}
}
}
v___jp_1273_:
{
if (v___y_1274_ == 0)
{
goto v___jp_1223_;
}
else
{
lean_object* v___x_1275_; 
lean_inc(v___y_1218_);
lean_inc_ref(v___y_1217_);
v___x_1275_ = lean_apply_3(v_x_1215_, v___y_1217_, v___y_1218_, lean_box(0));
return v___x_1275_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___boxed(lean_object* v_x_1280_, lean_object* v_isExporting_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_){
_start:
{
uint8_t v_isExporting_boxed_1285_; lean_object* v_res_1286_; 
v_isExporting_boxed_1285_ = lean_unbox(v_isExporting_1281_);
v_res_1286_ = l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg(v_x_1280_, v_isExporting_boxed_1285_, v___y_1282_, v___y_1283_);
lean_dec(v___y_1283_);
lean_dec_ref(v___y_1282_);
return v_res_1286_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2(lean_object* v_00_u03b1_1287_, lean_object* v_x_1288_, uint8_t v_isExporting_1289_, lean_object* v___y_1290_, lean_object* v___y_1291_){
_start:
{
lean_object* v___x_1293_; 
v___x_1293_ = l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg(v_x_1288_, v_isExporting_1289_, v___y_1290_, v___y_1291_);
return v___x_1293_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___boxed(lean_object* v_00_u03b1_1294_, lean_object* v_x_1295_, lean_object* v_isExporting_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_){
_start:
{
uint8_t v_isExporting_boxed_1300_; lean_object* v_res_1301_; 
v_isExporting_boxed_1300_ = lean_unbox(v_isExporting_1296_);
v_res_1301_ = l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2(v_00_u03b1_1294_, v_x_1295_, v_isExporting_boxed_1300_, v___y_1297_, v___y_1298_);
lean_dec(v___y_1298_);
lean_dec_ref(v___y_1297_);
return v_res_1301_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0_spec__3(lean_object* v_opts_1302_, lean_object* v_opt_1303_){
_start:
{
lean_object* v_name_1304_; lean_object* v_defValue_1305_; lean_object* v_map_1306_; lean_object* v___x_1307_; 
v_name_1304_ = lean_ctor_get(v_opt_1303_, 0);
v_defValue_1305_ = lean_ctor_get(v_opt_1303_, 1);
v_map_1306_ = lean_ctor_get(v_opts_1302_, 0);
v___x_1307_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1306_, v_name_1304_);
if (lean_obj_tag(v___x_1307_) == 0)
{
uint8_t v___x_1308_; 
v___x_1308_ = lean_unbox(v_defValue_1305_);
return v___x_1308_;
}
else
{
lean_object* v_val_1309_; 
v_val_1309_ = lean_ctor_get(v___x_1307_, 0);
lean_inc(v_val_1309_);
lean_dec_ref_known(v___x_1307_, 1);
if (lean_obj_tag(v_val_1309_) == 1)
{
uint8_t v_v_1310_; 
v_v_1310_ = lean_ctor_get_uint8(v_val_1309_, 0);
lean_dec_ref_known(v_val_1309_, 0);
return v_v_1310_;
}
else
{
uint8_t v___x_1311_; 
lean_dec(v_val_1309_);
v___x_1311_ = lean_unbox(v_defValue_1305_);
return v___x_1311_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0_spec__3___boxed(lean_object* v_opts_1312_, lean_object* v_opt_1313_){
_start:
{
uint8_t v_res_1314_; lean_object* v_r_1315_; 
v_res_1314_ = l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0_spec__3(v_opts_1312_, v_opt_1313_);
lean_dec_ref(v_opt_1313_);
lean_dec_ref(v_opts_1312_);
v_r_1315_ = lean_box(v_res_1314_);
return v_r_1315_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0(uint8_t v___y_1323_, uint8_t v_suppressElabErrors_1324_, lean_object* v_x_1325_){
_start:
{
if (lean_obj_tag(v_x_1325_) == 1)
{
lean_object* v_pre_1326_; 
v_pre_1326_ = lean_ctor_get(v_x_1325_, 0);
switch(lean_obj_tag(v_pre_1326_))
{
case 1:
{
lean_object* v_pre_1327_; 
v_pre_1327_ = lean_ctor_get(v_pre_1326_, 0);
switch(lean_obj_tag(v_pre_1327_))
{
case 0:
{
lean_object* v_str_1328_; lean_object* v_str_1329_; lean_object* v___x_1330_; uint8_t v___x_1331_; 
v_str_1328_ = lean_ctor_get(v_x_1325_, 1);
v_str_1329_ = lean_ctor_get(v_pre_1326_, 1);
v___x_1330_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__0));
v___x_1331_ = lean_string_dec_eq(v_str_1329_, v___x_1330_);
if (v___x_1331_ == 0)
{
lean_object* v___x_1332_; uint8_t v___x_1333_; 
v___x_1332_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__2));
v___x_1333_ = lean_string_dec_eq(v_str_1329_, v___x_1332_);
if (v___x_1333_ == 0)
{
return v___y_1323_;
}
else
{
lean_object* v___x_1334_; uint8_t v___x_1335_; 
v___x_1334_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__1));
v___x_1335_ = lean_string_dec_eq(v_str_1328_, v___x_1334_);
if (v___x_1335_ == 0)
{
return v___y_1323_;
}
else
{
return v_suppressElabErrors_1324_;
}
}
}
else
{
lean_object* v___x_1336_; uint8_t v___x_1337_; 
v___x_1336_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__2));
v___x_1337_ = lean_string_dec_eq(v_str_1328_, v___x_1336_);
if (v___x_1337_ == 0)
{
return v___y_1323_;
}
else
{
return v_suppressElabErrors_1324_;
}
}
}
case 1:
{
lean_object* v_pre_1338_; 
v_pre_1338_ = lean_ctor_get(v_pre_1327_, 0);
if (lean_obj_tag(v_pre_1338_) == 0)
{
lean_object* v_str_1339_; lean_object* v_str_1340_; lean_object* v_str_1341_; lean_object* v___x_1342_; uint8_t v___x_1343_; 
v_str_1339_ = lean_ctor_get(v_x_1325_, 1);
v_str_1340_ = lean_ctor_get(v_pre_1326_, 1);
v_str_1341_ = lean_ctor_get(v_pre_1327_, 1);
v___x_1342_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__3));
v___x_1343_ = lean_string_dec_eq(v_str_1341_, v___x_1342_);
if (v___x_1343_ == 0)
{
return v___y_1323_;
}
else
{
lean_object* v___x_1344_; uint8_t v___x_1345_; 
v___x_1344_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__4));
v___x_1345_ = lean_string_dec_eq(v_str_1340_, v___x_1344_);
if (v___x_1345_ == 0)
{
return v___y_1323_;
}
else
{
lean_object* v___x_1346_; uint8_t v___x_1347_; 
v___x_1346_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__5));
v___x_1347_ = lean_string_dec_eq(v_str_1339_, v___x_1346_);
if (v___x_1347_ == 0)
{
return v___y_1323_;
}
else
{
return v_suppressElabErrors_1324_;
}
}
}
}
else
{
return v___y_1323_;
}
}
default: 
{
return v___y_1323_;
}
}
}
case 0:
{
lean_object* v_str_1348_; lean_object* v___x_1349_; uint8_t v___x_1350_; 
v_str_1348_ = lean_ctor_get(v_x_1325_, 1);
v___x_1349_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__6));
v___x_1350_ = lean_string_dec_eq(v_str_1348_, v___x_1349_);
if (v___x_1350_ == 0)
{
return v___y_1323_;
}
else
{
return v_suppressElabErrors_1324_;
}
}
default: 
{
return v___y_1323_;
}
}
}
else
{
return v___y_1323_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___boxed(lean_object* v___y_1351_, lean_object* v_suppressElabErrors_1352_, lean_object* v_x_1353_){
_start:
{
uint8_t v___y_4892__boxed_1354_; uint8_t v_suppressElabErrors_boxed_1355_; uint8_t v_res_1356_; lean_object* v_r_1357_; 
v___y_4892__boxed_1354_ = lean_unbox(v___y_1351_);
v_suppressElabErrors_boxed_1355_ = lean_unbox(v_suppressElabErrors_1352_);
v_res_1356_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0(v___y_4892__boxed_1354_, v_suppressElabErrors_boxed_1355_, v_x_1353_);
lean_dec(v_x_1353_);
v_r_1357_ = lean_box(v_res_1356_);
return v_r_1357_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6(lean_object* v_ref_1358_, lean_object* v_msgData_1359_, uint8_t v_severity_1360_, uint8_t v_isSilent_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_){
_start:
{
lean_object* v___y_1366_; lean_object* v___y_1367_; lean_object* v___y_1368_; uint8_t v___y_1369_; uint8_t v___y_1370_; lean_object* v___y_1371_; lean_object* v___y_1372_; lean_object* v___y_1373_; lean_object* v___y_1374_; lean_object* v___y_1402_; lean_object* v___y_1403_; lean_object* v___y_1404_; uint8_t v___y_1405_; uint8_t v___y_1406_; lean_object* v___y_1407_; uint8_t v___y_1408_; lean_object* v___y_1409_; lean_object* v___y_1427_; lean_object* v___y_1428_; lean_object* v___y_1429_; uint8_t v___y_1430_; uint8_t v___y_1431_; uint8_t v___y_1432_; lean_object* v___y_1433_; lean_object* v___y_1434_; lean_object* v___y_1438_; lean_object* v___y_1439_; lean_object* v___y_1440_; uint8_t v___y_1441_; uint8_t v___y_1442_; lean_object* v___y_1443_; uint8_t v___y_1444_; uint8_t v___x_1449_; lean_object* v___y_1451_; lean_object* v___y_1452_; lean_object* v___y_1453_; uint8_t v___y_1454_; lean_object* v___y_1455_; uint8_t v___y_1456_; uint8_t v___y_1457_; uint8_t v___y_1459_; uint8_t v___x_1474_; 
v___x_1449_ = 2;
v___x_1474_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1360_, v___x_1449_);
if (v___x_1474_ == 0)
{
v___y_1459_ = v___x_1474_;
goto v___jp_1458_;
}
else
{
uint8_t v___x_1475_; 
lean_inc_ref(v_msgData_1359_);
v___x_1475_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_1359_);
v___y_1459_ = v___x_1475_;
goto v___jp_1458_;
}
v___jp_1365_:
{
lean_object* v___x_1375_; lean_object* v_currNamespace_1376_; lean_object* v_openDecls_1377_; lean_object* v_env_1378_; lean_object* v_nextMacroScope_1379_; lean_object* v_ngen_1380_; lean_object* v_auxDeclNGen_1381_; lean_object* v_traceState_1382_; lean_object* v_cache_1383_; lean_object* v_messages_1384_; lean_object* v_infoState_1385_; lean_object* v_snapshotTasks_1386_; lean_object* v___x_1388_; uint8_t v_isShared_1389_; uint8_t v_isSharedCheck_1400_; 
v___x_1375_ = lean_st_ref_take(v___y_1374_);
v_currNamespace_1376_ = lean_ctor_get(v___y_1373_, 6);
v_openDecls_1377_ = lean_ctor_get(v___y_1373_, 7);
v_env_1378_ = lean_ctor_get(v___x_1375_, 0);
v_nextMacroScope_1379_ = lean_ctor_get(v___x_1375_, 1);
v_ngen_1380_ = lean_ctor_get(v___x_1375_, 2);
v_auxDeclNGen_1381_ = lean_ctor_get(v___x_1375_, 3);
v_traceState_1382_ = lean_ctor_get(v___x_1375_, 4);
v_cache_1383_ = lean_ctor_get(v___x_1375_, 5);
v_messages_1384_ = lean_ctor_get(v___x_1375_, 6);
v_infoState_1385_ = lean_ctor_get(v___x_1375_, 7);
v_snapshotTasks_1386_ = lean_ctor_get(v___x_1375_, 8);
v_isSharedCheck_1400_ = !lean_is_exclusive(v___x_1375_);
if (v_isSharedCheck_1400_ == 0)
{
v___x_1388_ = v___x_1375_;
v_isShared_1389_ = v_isSharedCheck_1400_;
goto v_resetjp_1387_;
}
else
{
lean_inc(v_snapshotTasks_1386_);
lean_inc(v_infoState_1385_);
lean_inc(v_messages_1384_);
lean_inc(v_cache_1383_);
lean_inc(v_traceState_1382_);
lean_inc(v_auxDeclNGen_1381_);
lean_inc(v_ngen_1380_);
lean_inc(v_nextMacroScope_1379_);
lean_inc(v_env_1378_);
lean_dec(v___x_1375_);
v___x_1388_ = lean_box(0);
v_isShared_1389_ = v_isSharedCheck_1400_;
goto v_resetjp_1387_;
}
v_resetjp_1387_:
{
lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1395_; 
lean_inc(v_openDecls_1377_);
lean_inc(v_currNamespace_1376_);
v___x_1390_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1390_, 0, v_currNamespace_1376_);
lean_ctor_set(v___x_1390_, 1, v_openDecls_1377_);
v___x_1391_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1391_, 0, v___x_1390_);
lean_ctor_set(v___x_1391_, 1, v___y_1367_);
lean_inc_ref(v___y_1372_);
lean_inc_ref(v___y_1371_);
v___x_1392_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1392_, 0, v___y_1371_);
lean_ctor_set(v___x_1392_, 1, v___y_1368_);
lean_ctor_set(v___x_1392_, 2, v___y_1366_);
lean_ctor_set(v___x_1392_, 3, v___y_1372_);
lean_ctor_set(v___x_1392_, 4, v___x_1391_);
lean_ctor_set_uint8(v___x_1392_, sizeof(void*)*5, v___y_1369_);
lean_ctor_set_uint8(v___x_1392_, sizeof(void*)*5 + 1, v___y_1370_);
lean_ctor_set_uint8(v___x_1392_, sizeof(void*)*5 + 2, v_isSilent_1361_);
v___x_1393_ = l_Lean_MessageLog_add(v___x_1392_, v_messages_1384_);
if (v_isShared_1389_ == 0)
{
lean_ctor_set(v___x_1388_, 6, v___x_1393_);
v___x_1395_ = v___x_1388_;
goto v_reusejp_1394_;
}
else
{
lean_object* v_reuseFailAlloc_1399_; 
v_reuseFailAlloc_1399_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1399_, 0, v_env_1378_);
lean_ctor_set(v_reuseFailAlloc_1399_, 1, v_nextMacroScope_1379_);
lean_ctor_set(v_reuseFailAlloc_1399_, 2, v_ngen_1380_);
lean_ctor_set(v_reuseFailAlloc_1399_, 3, v_auxDeclNGen_1381_);
lean_ctor_set(v_reuseFailAlloc_1399_, 4, v_traceState_1382_);
lean_ctor_set(v_reuseFailAlloc_1399_, 5, v_cache_1383_);
lean_ctor_set(v_reuseFailAlloc_1399_, 6, v___x_1393_);
lean_ctor_set(v_reuseFailAlloc_1399_, 7, v_infoState_1385_);
lean_ctor_set(v_reuseFailAlloc_1399_, 8, v_snapshotTasks_1386_);
v___x_1395_ = v_reuseFailAlloc_1399_;
goto v_reusejp_1394_;
}
v_reusejp_1394_:
{
lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; 
v___x_1396_ = lean_st_ref_set(v___y_1374_, v___x_1395_);
v___x_1397_ = lean_box(0);
v___x_1398_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1398_, 0, v___x_1397_);
return v___x_1398_;
}
}
}
v___jp_1401_:
{
lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v_a_1412_; lean_object* v___x_1414_; uint8_t v_isShared_1415_; uint8_t v_isSharedCheck_1425_; 
v___x_1410_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_1359_);
v___x_1411_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0(v___x_1410_, v___y_1362_, v___y_1363_);
v_a_1412_ = lean_ctor_get(v___x_1411_, 0);
v_isSharedCheck_1425_ = !lean_is_exclusive(v___x_1411_);
if (v_isSharedCheck_1425_ == 0)
{
v___x_1414_ = v___x_1411_;
v_isShared_1415_ = v_isSharedCheck_1425_;
goto v_resetjp_1413_;
}
else
{
lean_inc(v_a_1412_);
lean_dec(v___x_1411_);
v___x_1414_ = lean_box(0);
v_isShared_1415_ = v_isSharedCheck_1425_;
goto v_resetjp_1413_;
}
v_resetjp_1413_:
{
lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; 
lean_inc_ref_n(v___y_1404_, 2);
v___x_1416_ = l_Lean_FileMap_toPosition(v___y_1404_, v___y_1403_);
lean_dec(v___y_1403_);
v___x_1417_ = l_Lean_FileMap_toPosition(v___y_1404_, v___y_1409_);
lean_dec(v___y_1409_);
v___x_1418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1418_, 0, v___x_1417_);
v___x_1419_ = ((lean_object*)(l_Lean_instInhabitedAttributeImplCore_default___closed__3));
if (v___y_1405_ == 0)
{
lean_del_object(v___x_1414_);
lean_dec_ref(v___y_1402_);
v___y_1366_ = v___x_1418_;
v___y_1367_ = v_a_1412_;
v___y_1368_ = v___x_1416_;
v___y_1369_ = v___y_1406_;
v___y_1370_ = v___y_1408_;
v___y_1371_ = v___y_1407_;
v___y_1372_ = v___x_1419_;
v___y_1373_ = v___y_1362_;
v___y_1374_ = v___y_1363_;
goto v___jp_1365_;
}
else
{
uint8_t v___x_1420_; 
lean_inc(v_a_1412_);
v___x_1420_ = l_Lean_MessageData_hasTag(v___y_1402_, v_a_1412_);
if (v___x_1420_ == 0)
{
lean_object* v___x_1421_; lean_object* v___x_1423_; 
lean_dec_ref_known(v___x_1418_, 1);
lean_dec_ref(v___x_1416_);
lean_dec(v_a_1412_);
v___x_1421_ = lean_box(0);
if (v_isShared_1415_ == 0)
{
lean_ctor_set(v___x_1414_, 0, v___x_1421_);
v___x_1423_ = v___x_1414_;
goto v_reusejp_1422_;
}
else
{
lean_object* v_reuseFailAlloc_1424_; 
v_reuseFailAlloc_1424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1424_, 0, v___x_1421_);
v___x_1423_ = v_reuseFailAlloc_1424_;
goto v_reusejp_1422_;
}
v_reusejp_1422_:
{
return v___x_1423_;
}
}
else
{
lean_del_object(v___x_1414_);
v___y_1366_ = v___x_1418_;
v___y_1367_ = v_a_1412_;
v___y_1368_ = v___x_1416_;
v___y_1369_ = v___y_1406_;
v___y_1370_ = v___y_1408_;
v___y_1371_ = v___y_1407_;
v___y_1372_ = v___x_1419_;
v___y_1373_ = v___y_1362_;
v___y_1374_ = v___y_1363_;
goto v___jp_1365_;
}
}
}
}
v___jp_1426_:
{
lean_object* v___x_1435_; 
v___x_1435_ = l_Lean_Syntax_getTailPos_x3f(v___y_1429_, v___y_1431_);
lean_dec(v___y_1429_);
if (lean_obj_tag(v___x_1435_) == 0)
{
lean_inc(v___y_1434_);
v___y_1402_ = v___y_1427_;
v___y_1403_ = v___y_1434_;
v___y_1404_ = v___y_1428_;
v___y_1405_ = v___y_1430_;
v___y_1406_ = v___y_1431_;
v___y_1407_ = v___y_1433_;
v___y_1408_ = v___y_1432_;
v___y_1409_ = v___y_1434_;
goto v___jp_1401_;
}
else
{
lean_object* v_val_1436_; 
v_val_1436_ = lean_ctor_get(v___x_1435_, 0);
lean_inc(v_val_1436_);
lean_dec_ref_known(v___x_1435_, 1);
v___y_1402_ = v___y_1427_;
v___y_1403_ = v___y_1434_;
v___y_1404_ = v___y_1428_;
v___y_1405_ = v___y_1430_;
v___y_1406_ = v___y_1431_;
v___y_1407_ = v___y_1433_;
v___y_1408_ = v___y_1432_;
v___y_1409_ = v_val_1436_;
goto v___jp_1401_;
}
}
v___jp_1437_:
{
lean_object* v_ref_1445_; lean_object* v___x_1446_; 
v_ref_1445_ = l_Lean_replaceRef(v_ref_1358_, v___y_1440_);
v___x_1446_ = l_Lean_Syntax_getPos_x3f(v_ref_1445_, v___y_1442_);
if (lean_obj_tag(v___x_1446_) == 0)
{
lean_object* v___x_1447_; 
v___x_1447_ = lean_unsigned_to_nat(0u);
v___y_1427_ = v___y_1438_;
v___y_1428_ = v___y_1439_;
v___y_1429_ = v_ref_1445_;
v___y_1430_ = v___y_1441_;
v___y_1431_ = v___y_1442_;
v___y_1432_ = v___y_1444_;
v___y_1433_ = v___y_1443_;
v___y_1434_ = v___x_1447_;
goto v___jp_1426_;
}
else
{
lean_object* v_val_1448_; 
v_val_1448_ = lean_ctor_get(v___x_1446_, 0);
lean_inc(v_val_1448_);
lean_dec_ref_known(v___x_1446_, 1);
v___y_1427_ = v___y_1438_;
v___y_1428_ = v___y_1439_;
v___y_1429_ = v_ref_1445_;
v___y_1430_ = v___y_1441_;
v___y_1431_ = v___y_1442_;
v___y_1432_ = v___y_1444_;
v___y_1433_ = v___y_1443_;
v___y_1434_ = v_val_1448_;
goto v___jp_1426_;
}
}
v___jp_1450_:
{
if (v___y_1457_ == 0)
{
v___y_1438_ = v___y_1451_;
v___y_1439_ = v___y_1453_;
v___y_1440_ = v___y_1452_;
v___y_1441_ = v___y_1454_;
v___y_1442_ = v___y_1456_;
v___y_1443_ = v___y_1455_;
v___y_1444_ = v_severity_1360_;
goto v___jp_1437_;
}
else
{
v___y_1438_ = v___y_1451_;
v___y_1439_ = v___y_1453_;
v___y_1440_ = v___y_1452_;
v___y_1441_ = v___y_1454_;
v___y_1442_ = v___y_1456_;
v___y_1443_ = v___y_1455_;
v___y_1444_ = v___x_1449_;
goto v___jp_1437_;
}
}
v___jp_1458_:
{
if (v___y_1459_ == 0)
{
lean_object* v_fileName_1460_; lean_object* v_fileMap_1461_; lean_object* v_options_1462_; lean_object* v_ref_1463_; uint8_t v_suppressElabErrors_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___f_1467_; uint8_t v___x_1468_; uint8_t v___x_1469_; 
v_fileName_1460_ = lean_ctor_get(v___y_1362_, 0);
v_fileMap_1461_ = lean_ctor_get(v___y_1362_, 1);
v_options_1462_ = lean_ctor_get(v___y_1362_, 2);
v_ref_1463_ = lean_ctor_get(v___y_1362_, 5);
v_suppressElabErrors_1464_ = lean_ctor_get_uint8(v___y_1362_, sizeof(void*)*14 + 1);
v___x_1465_ = lean_box(v___y_1459_);
v___x_1466_ = lean_box(v_suppressElabErrors_1464_);
v___f_1467_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1467_, 0, v___x_1465_);
lean_closure_set(v___f_1467_, 1, v___x_1466_);
v___x_1468_ = 1;
v___x_1469_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1360_, v___x_1468_);
if (v___x_1469_ == 0)
{
v___y_1451_ = v___f_1467_;
v___y_1452_ = v_ref_1463_;
v___y_1453_ = v_fileMap_1461_;
v___y_1454_ = v_suppressElabErrors_1464_;
v___y_1455_ = v_fileName_1460_;
v___y_1456_ = v___y_1459_;
v___y_1457_ = v___x_1469_;
goto v___jp_1450_;
}
else
{
lean_object* v___x_1470_; uint8_t v___x_1471_; 
v___x_1470_ = l_Lean_warningAsError;
v___x_1471_ = l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0_spec__3(v_options_1462_, v___x_1470_);
v___y_1451_ = v___f_1467_;
v___y_1452_ = v_ref_1463_;
v___y_1453_ = v_fileMap_1461_;
v___y_1454_ = v_suppressElabErrors_1464_;
v___y_1455_ = v_fileName_1460_;
v___y_1456_ = v___y_1459_;
v___y_1457_ = v___x_1471_;
goto v___jp_1450_;
}
}
else
{
lean_object* v___x_1472_; lean_object* v___x_1473_; 
lean_dec_ref(v_msgData_1359_);
v___x_1472_ = lean_box(0);
v___x_1473_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1473_, 0, v___x_1472_);
return v___x_1473_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___boxed(lean_object* v_ref_1476_, lean_object* v_msgData_1477_, lean_object* v_severity_1478_, lean_object* v_isSilent_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_){
_start:
{
uint8_t v_severity_boxed_1483_; uint8_t v_isSilent_boxed_1484_; lean_object* v_res_1485_; 
v_severity_boxed_1483_ = lean_unbox(v_severity_1478_);
v_isSilent_boxed_1484_ = lean_unbox(v_isSilent_1479_);
v_res_1485_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6(v_ref_1476_, v_msgData_1477_, v_severity_boxed_1483_, v_isSilent_boxed_1484_, v___y_1480_, v___y_1481_);
lean_dec(v___y_1481_);
lean_dec_ref(v___y_1480_);
lean_dec(v_ref_1476_);
return v_res_1485_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5(lean_object* v_msgData_1486_, uint8_t v_severity_1487_, uint8_t v_isSilent_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_){
_start:
{
lean_object* v_ref_1492_; lean_object* v___x_1493_; 
v_ref_1492_ = lean_ctor_get(v___y_1489_, 5);
v___x_1493_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6(v_ref_1492_, v_msgData_1486_, v_severity_1487_, v_isSilent_1488_, v___y_1489_, v___y_1490_);
return v___x_1493_;
}
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
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1(lean_object* v_msgData_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_){
_start:
{
uint8_t v___x_1507_; uint8_t v___x_1508_; lean_object* v___x_1509_; 
v___x_1507_ = 1;
v___x_1508_ = 0;
v___x_1509_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5(v_msgData_1503_, v___x_1507_, v___x_1508_, v___y_1504_, v___y_1505_);
return v___x_1509_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1___boxed(lean_object* v_msgData_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_){
_start:
{
lean_object* v_res_1514_; 
v_res_1514_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1(v_msgData_1510_, v___y_1511_, v___y_1512_);
lean_dec(v___y_1512_);
lean_dec_ref(v___y_1511_);
return v_res_1514_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0___redArg(lean_object* v_opt_1515_, lean_object* v___y_1516_){
_start:
{
lean_object* v_options_1518_; uint8_t v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; 
v_options_1518_ = lean_ctor_get(v___y_1516_, 2);
v___x_1519_ = l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0_spec__3(v_options_1518_, v_opt_1515_);
v___x_1520_ = lean_box(v___x_1519_);
v___x_1521_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1521_, 0, v___x_1520_);
return v___x_1521_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0___redArg___boxed(lean_object* v_opt_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_){
_start:
{
lean_object* v_res_1525_; 
v_res_1525_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0___redArg(v_opt_1522_, v___y_1523_);
lean_dec_ref(v___y_1523_);
lean_dec_ref(v_opt_1522_);
return v_res_1525_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1527_; lean_object* v___x_1528_; 
v___x_1527_ = ((lean_object*)(l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__0));
v___x_1528_ = l_Lean_stringToMessageData(v___x_1527_);
return v___x_1528_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__3(void){
_start:
{
lean_object* v___x_1530_; lean_object* v___x_1531_; 
v___x_1530_ = ((lean_object*)(l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__2));
v___x_1531_ = l_Lean_stringToMessageData(v___x_1530_);
return v___x_1531_;
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0(lean_object* v_id_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_){
_start:
{
lean_object* v___x_1536_; lean_object* v_env_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v_a_1540_; lean_object* v___x_1542_; uint8_t v_isShared_1543_; uint8_t v_isSharedCheck_1559_; 
v___x_1536_ = lean_st_ref_get(v___y_1534_);
v_env_1537_ = lean_ctor_get(v___x_1536_, 0);
lean_inc_ref(v_env_1537_);
lean_dec(v___x_1536_);
v___x_1538_ = l_Lean_ResolveName_backward_privateInPublic_warn;
v___x_1539_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0___redArg(v___x_1538_, v___y_1533_);
v_a_1540_ = lean_ctor_get(v___x_1539_, 0);
v_isSharedCheck_1559_ = !lean_is_exclusive(v___x_1539_);
if (v_isSharedCheck_1559_ == 0)
{
v___x_1542_ = v___x_1539_;
v_isShared_1543_ = v_isSharedCheck_1559_;
goto v_resetjp_1541_;
}
else
{
lean_inc(v_a_1540_);
lean_dec(v___x_1539_);
v___x_1542_ = lean_box(0);
v_isShared_1543_ = v_isSharedCheck_1559_;
goto v_resetjp_1541_;
}
v_resetjp_1541_:
{
uint8_t v_isExporting_1549_; 
v_isExporting_1549_ = lean_ctor_get_uint8(v_env_1537_, sizeof(void*)*8);
lean_dec_ref(v_env_1537_);
if (v_isExporting_1549_ == 0)
{
lean_dec(v_a_1540_);
lean_dec(v_id_1532_);
goto v___jp_1544_;
}
else
{
uint8_t v___x_1550_; 
v___x_1550_ = l_Lean_isPrivateName(v_id_1532_);
if (v___x_1550_ == 0)
{
lean_dec(v_a_1540_);
lean_dec(v_id_1532_);
goto v___jp_1544_;
}
else
{
uint8_t v___x_1551_; 
v___x_1551_ = lean_unbox(v_a_1540_);
lean_dec(v_a_1540_);
if (v___x_1551_ == 0)
{
lean_dec(v_id_1532_);
goto v___jp_1544_;
}
else
{
lean_object* v___x_1552_; uint8_t v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; 
lean_del_object(v___x_1542_);
v___x_1552_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__1, &l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__1_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__1);
v___x_1553_ = 0;
v___x_1554_ = l_Lean_MessageData_ofConstName(v_id_1532_, v___x_1553_);
v___x_1555_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1555_, 0, v___x_1552_);
lean_ctor_set(v___x_1555_, 1, v___x_1554_);
v___x_1556_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__3, &l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__3_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__3);
v___x_1557_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1557_, 0, v___x_1555_);
lean_ctor_set(v___x_1557_, 1, v___x_1556_);
v___x_1558_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1(v___x_1557_, v___y_1533_, v___y_1534_);
return v___x_1558_;
}
}
}
v___jp_1544_:
{
lean_object* v___x_1545_; lean_object* v___x_1547_; 
v___x_1545_ = lean_box(0);
if (v_isShared_1543_ == 0)
{
lean_ctor_set(v___x_1542_, 0, v___x_1545_);
v___x_1547_ = v___x_1542_;
goto v_reusejp_1546_;
}
else
{
lean_object* v_reuseFailAlloc_1548_; 
v_reuseFailAlloc_1548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1548_, 0, v___x_1545_);
v___x_1547_ = v_reuseFailAlloc_1548_;
goto v_reusejp_1546_;
}
v_reusejp_1546_:
{
return v___x_1547_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___boxed(lean_object* v_id_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_){
_start:
{
lean_object* v_res_1564_; 
v_res_1564_ = l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0(v_id_1560_, v___y_1561_, v___y_1562_);
lean_dec(v___y_1562_);
lean_dec_ref(v___y_1561_);
return v_res_1564_;
}
}
static lean_object* _init_l_Lean_ensureAttrDeclIsPublic___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1566_; lean_object* v___x_1567_; 
v___x_1566_ = ((lean_object*)(l_Lean_ensureAttrDeclIsPublic___lam__0___closed__0));
v___x_1567_ = l_Lean_stringToMessageData(v___x_1566_);
return v___x_1567_;
}
}
LEAN_EXPORT lean_object* l_Lean_ensureAttrDeclIsPublic___lam__0(lean_object* v_declName_1568_, uint8_t v_isModule_1569_, lean_object* v_attrName_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_){
_start:
{
lean_object* v___x_1574_; 
lean_inc(v_declName_1568_);
v___x_1574_ = l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0(v_declName_1568_, v___y_1571_, v___y_1572_);
if (lean_obj_tag(v___x_1574_) == 0)
{
lean_object* v___x_1575_; lean_object* v_a_1576_; lean_object* v___x_1578_; uint8_t v_isShared_1579_; uint8_t v_isSharedCheck_1597_; 
lean_dec_ref_known(v___x_1574_, 1);
lean_inc(v_declName_1568_);
v___x_1575_ = l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1___redArg(v_declName_1568_, v_isModule_1569_, v___y_1572_);
v_a_1576_ = lean_ctor_get(v___x_1575_, 0);
v_isSharedCheck_1597_ = !lean_is_exclusive(v___x_1575_);
if (v_isSharedCheck_1597_ == 0)
{
v___x_1578_ = v___x_1575_;
v_isShared_1579_ = v_isSharedCheck_1597_;
goto v_resetjp_1577_;
}
else
{
lean_inc(v_a_1576_);
lean_dec(v___x_1575_);
v___x_1578_ = lean_box(0);
v_isShared_1579_ = v_isSharedCheck_1597_;
goto v_resetjp_1577_;
}
v_resetjp_1577_:
{
uint8_t v___x_1580_; uint8_t v___x_1581_; 
v___x_1580_ = lean_unbox(v_a_1576_);
lean_dec(v_a_1576_);
v___x_1581_ = lean_bool_not(v___x_1580_);
if (v___x_1581_ == 0)
{
lean_object* v___x_1582_; lean_object* v___x_1584_; 
lean_dec(v_attrName_1570_);
lean_dec(v_declName_1568_);
v___x_1582_ = lean_box(0);
if (v_isShared_1579_ == 0)
{
lean_ctor_set(v___x_1578_, 0, v___x_1582_);
v___x_1584_ = v___x_1578_;
goto v_reusejp_1583_;
}
else
{
lean_object* v_reuseFailAlloc_1585_; 
v_reuseFailAlloc_1585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1585_, 0, v___x_1582_);
v___x_1584_ = v_reuseFailAlloc_1585_;
goto v_reusejp_1583_;
}
v_reusejp_1583_:
{
return v___x_1584_;
}
}
else
{
lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; uint8_t v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; 
lean_del_object(v___x_1578_);
v___x_1586_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1);
v___x_1587_ = l_Lean_MessageData_ofName(v_attrName_1570_);
v___x_1588_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1588_, 0, v___x_1586_);
lean_ctor_set(v___x_1588_, 1, v___x_1587_);
v___x_1589_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1, &l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1);
v___x_1590_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1590_, 0, v___x_1588_);
lean_ctor_set(v___x_1590_, 1, v___x_1589_);
v___x_1591_ = 0;
v___x_1592_ = l_Lean_MessageData_ofConstName(v_declName_1568_, v___x_1591_);
v___x_1593_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1593_, 0, v___x_1590_);
lean_ctor_set(v___x_1593_, 1, v___x_1592_);
v___x_1594_ = lean_obj_once(&l_Lean_ensureAttrDeclIsPublic___lam__0___closed__1, &l_Lean_ensureAttrDeclIsPublic___lam__0___closed__1_once, _init_l_Lean_ensureAttrDeclIsPublic___lam__0___closed__1);
v___x_1595_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1595_, 0, v___x_1593_);
lean_ctor_set(v___x_1595_, 1, v___x_1594_);
v___x_1596_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_1595_, v___y_1571_, v___y_1572_);
return v___x_1596_;
}
}
}
else
{
lean_dec(v_attrName_1570_);
lean_dec(v_declName_1568_);
return v___x_1574_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ensureAttrDeclIsPublic___lam__0___boxed(lean_object* v_declName_1598_, lean_object* v_isModule_1599_, lean_object* v_attrName_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_){
_start:
{
uint8_t v_isModule_boxed_1604_; lean_object* v_res_1605_; 
v_isModule_boxed_1604_ = lean_unbox(v_isModule_1599_);
v_res_1605_ = l_Lean_ensureAttrDeclIsPublic___lam__0(v_declName_1598_, v_isModule_boxed_1604_, v_attrName_1600_, v___y_1601_, v___y_1602_);
lean_dec(v___y_1602_);
lean_dec_ref(v___y_1601_);
return v_res_1605_;
}
}
LEAN_EXPORT lean_object* l_Lean_ensureAttrDeclIsPublic(lean_object* v_attrName_1606_, lean_object* v_declName_1607_, uint8_t v_attrKind_1608_, lean_object* v_a_1609_, lean_object* v_a_1610_){
_start:
{
lean_object* v___x_1612_; lean_object* v_env_1616_; lean_object* v___x_1617_; uint8_t v_isModule_1618_; 
v___x_1612_ = lean_st_ref_get(v_a_1610_);
v_env_1616_ = lean_ctor_get(v___x_1612_, 0);
lean_inc_ref(v_env_1616_);
lean_dec(v___x_1612_);
v___x_1617_ = l_Lean_Environment_header(v_env_1616_);
lean_dec_ref(v_env_1616_);
v_isModule_1618_ = lean_ctor_get_uint8(v___x_1617_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_1617_);
if (v_isModule_1618_ == 0)
{
lean_dec(v_declName_1607_);
lean_dec(v_attrName_1606_);
goto v___jp_1613_;
}
else
{
uint8_t v___x_1619_; uint8_t v___x_1620_; uint8_t v___x_1621_; 
v___x_1619_ = 1;
v___x_1620_ = l_Lean_instBEqAttributeKind_beq(v_attrKind_1608_, v___x_1619_);
v___x_1621_ = lean_bool_not(v___x_1620_);
if (v___x_1621_ == 0)
{
lean_dec(v_declName_1607_);
lean_dec(v_attrName_1606_);
goto v___jp_1613_;
}
else
{
lean_object* v___x_1622_; lean_object* v___f_1623_; lean_object* v___x_1624_; 
v___x_1622_ = lean_box(v_isModule_1618_);
v___f_1623_ = lean_alloc_closure((void*)(l_Lean_ensureAttrDeclIsPublic___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1623_, 0, v_declName_1607_);
lean_closure_set(v___f_1623_, 1, v___x_1622_);
lean_closure_set(v___f_1623_, 2, v_attrName_1606_);
v___x_1624_ = l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg(v___f_1623_, v_isModule_1618_, v_a_1609_, v_a_1610_);
return v___x_1624_;
}
}
v___jp_1613_:
{
lean_object* v___x_1614_; lean_object* v___x_1615_; 
v___x_1614_ = lean_box(0);
v___x_1615_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1615_, 0, v___x_1614_);
return v___x_1615_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ensureAttrDeclIsPublic___boxed(lean_object* v_attrName_1625_, lean_object* v_declName_1626_, lean_object* v_attrKind_1627_, lean_object* v_a_1628_, lean_object* v_a_1629_, lean_object* v_a_1630_){
_start:
{
uint8_t v_attrKind_boxed_1631_; lean_object* v_res_1632_; 
v_attrKind_boxed_1631_ = lean_unbox(v_attrKind_1627_);
v_res_1632_ = l_Lean_ensureAttrDeclIsPublic(v_attrName_1625_, v_declName_1626_, v_attrKind_boxed_1631_, v_a_1628_, v_a_1629_);
lean_dec(v_a_1629_);
lean_dec_ref(v_a_1628_);
return v_res_1632_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0(lean_object* v_opt_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_){
_start:
{
lean_object* v___x_1637_; 
v___x_1637_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0___redArg(v_opt_1633_, v___y_1634_);
return v___x_1637_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0___boxed(lean_object* v_opt_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_){
_start:
{
lean_object* v_res_1642_; 
v_res_1642_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0(v_opt_1638_, v___y_1639_, v___y_1640_);
lean_dec(v___y_1640_);
lean_dec_ref(v___y_1639_);
lean_dec_ref(v_opt_1638_);
return v_res_1642_;
}
}
static lean_object* _init_l_Lean_ensureAttrDeclIsMeta___closed__1(void){
_start:
{
lean_object* v___x_1644_; lean_object* v___x_1645_; 
v___x_1644_ = ((lean_object*)(l_Lean_ensureAttrDeclIsMeta___closed__0));
v___x_1645_ = l_Lean_stringToMessageData(v___x_1644_);
return v___x_1645_;
}
}
LEAN_EXPORT lean_object* l_Lean_ensureAttrDeclIsMeta(lean_object* v_attrName_1646_, lean_object* v_declName_1647_, uint8_t v_attrKind_1648_, lean_object* v_a_1649_, lean_object* v_a_1650_){
_start:
{
lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v_env_1654_; lean_object* v___x_1655_; uint8_t v_isModule_1656_; 
v___x_1652_ = lean_st_ref_get(v_a_1650_);
v___x_1653_ = lean_st_ref_get(v_a_1650_);
v_env_1654_ = lean_ctor_get(v___x_1652_, 0);
lean_inc_ref(v_env_1654_);
lean_dec(v___x_1652_);
v___x_1655_ = l_Lean_Environment_header(v_env_1654_);
lean_dec_ref(v_env_1654_);
v_isModule_1656_ = lean_ctor_get_uint8(v___x_1655_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_1655_);
if (v_isModule_1656_ == 0)
{
lean_object* v___x_1657_; 
lean_dec(v___x_1653_);
v___x_1657_ = l_Lean_ensureAttrDeclIsPublic(v_attrName_1646_, v_declName_1647_, v_attrKind_1648_, v_a_1649_, v_a_1650_);
return v___x_1657_;
}
else
{
lean_object* v_env_1658_; uint8_t v___x_1659_; uint8_t v___x_1660_; 
v_env_1658_ = lean_ctor_get(v___x_1653_, 0);
lean_inc_ref(v_env_1658_);
lean_dec(v___x_1653_);
lean_inc(v_declName_1647_);
v___x_1659_ = l_Lean_isMarkedMeta(v_env_1658_, v_declName_1647_);
v___x_1660_ = lean_bool_not(v___x_1659_);
if (v___x_1660_ == 0)
{
lean_object* v___x_1661_; 
v___x_1661_ = l_Lean_ensureAttrDeclIsPublic(v_attrName_1646_, v_declName_1647_, v_attrKind_1648_, v_a_1649_, v_a_1650_);
return v___x_1661_;
}
else
{
lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; uint8_t v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; 
v___x_1662_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1);
v___x_1663_ = l_Lean_MessageData_ofName(v_attrName_1646_);
v___x_1664_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1664_, 0, v___x_1662_);
lean_ctor_set(v___x_1664_, 1, v___x_1663_);
v___x_1665_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1, &l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1);
v___x_1666_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1666_, 0, v___x_1664_);
lean_ctor_set(v___x_1666_, 1, v___x_1665_);
v___x_1667_ = 0;
v___x_1668_ = l_Lean_MessageData_ofConstName(v_declName_1647_, v___x_1667_);
v___x_1669_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1669_, 0, v___x_1666_);
lean_ctor_set(v___x_1669_, 1, v___x_1668_);
v___x_1670_ = lean_obj_once(&l_Lean_ensureAttrDeclIsMeta___closed__1, &l_Lean_ensureAttrDeclIsMeta___closed__1_once, _init_l_Lean_ensureAttrDeclIsMeta___closed__1);
v___x_1671_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1671_, 0, v___x_1669_);
lean_ctor_set(v___x_1671_, 1, v___x_1670_);
v___x_1672_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_1671_, v_a_1649_, v_a_1650_);
return v___x_1672_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ensureAttrDeclIsMeta___boxed(lean_object* v_attrName_1673_, lean_object* v_declName_1674_, lean_object* v_attrKind_1675_, lean_object* v_a_1676_, lean_object* v_a_1677_, lean_object* v_a_1678_){
_start:
{
uint8_t v_attrKind_boxed_1679_; lean_object* v_res_1680_; 
v_attrKind_boxed_1679_ = lean_unbox(v_attrKind_1675_);
v_res_1680_ = l_Lean_ensureAttrDeclIsMeta(v_attrName_1673_, v_declName_1674_, v_attrKind_boxed_1679_, v_a_1676_, v_a_1677_);
lean_dec(v_a_1677_);
lean_dec_ref(v_a_1676_);
return v_res_1680_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__0(lean_object* v_x_1684_, lean_object* v___y_1685_){
_start:
{
lean_object* v___x_1687_; lean_object* v___x_1688_; 
v___x_1687_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___lam__0___closed__1));
v___x_1688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1688_, 0, v___x_1687_);
return v___x_1688_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__0___boxed(lean_object* v_x_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_){
_start:
{
lean_object* v_res_1692_; 
v_res_1692_ = l_Lean_instInhabitedTagAttribute_default___lam__0(v_x_1689_, v___y_1690_);
lean_dec_ref(v___y_1690_);
lean_dec_ref(v_x_1689_);
return v_res_1692_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__1(lean_object* v_s_1693_, lean_object* v_x_1694_){
_start:
{
lean_inc(v_s_1693_);
return v_s_1693_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__1___boxed(lean_object* v_s_1695_, lean_object* v_x_1696_){
_start:
{
lean_object* v_res_1697_; 
v_res_1697_ = l_Lean_instInhabitedTagAttribute_default___lam__1(v_s_1695_, v_x_1696_);
lean_dec(v_x_1696_);
lean_dec(v_s_1695_);
return v_res_1697_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__2(lean_object* v_x_1702_, lean_object* v_x_1703_){
_start:
{
lean_object* v___x_1704_; 
v___x_1704_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___lam__2___closed__1));
return v___x_1704_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__2___boxed(lean_object* v_x_1705_, lean_object* v_x_1706_){
_start:
{
lean_object* v_res_1707_; 
v_res_1707_ = l_Lean_instInhabitedTagAttribute_default___lam__2(v_x_1705_, v_x_1706_);
lean_dec(v_x_1706_);
lean_dec_ref(v_x_1705_);
return v_res_1707_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__3(lean_object* v_x_1708_){
_start:
{
lean_object* v___x_1709_; 
v___x_1709_ = lean_box(0);
return v___x_1709_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__3___boxed(lean_object* v_x_1710_){
_start:
{
lean_object* v_res_1711_; 
v_res_1711_ = l_Lean_instInhabitedTagAttribute_default___lam__3(v_x_1710_);
lean_dec(v_x_1710_);
return v_res_1711_;
}
}
static lean_object* _init_l_Lean_instInhabitedTagAttribute_default___closed__4(void){
_start:
{
lean_object* v___x_1716_; 
v___x_1716_ = l_Lean_instInhabitedEnvExtension_default(lean_box(0));
return v___x_1716_;
}
}
static lean_object* _init_l_Lean_instInhabitedTagAttribute_default___closed__5(void){
_start:
{
lean_object* v___f_1717_; lean_object* v___f_1718_; lean_object* v___f_1719_; lean_object* v___f_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; 
v___f_1717_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___closed__3));
v___f_1718_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___closed__2));
v___f_1719_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___closed__1));
v___f_1720_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___closed__0));
v___x_1721_ = lean_box(0);
v___x_1722_ = lean_obj_once(&l_Lean_instInhabitedTagAttribute_default___closed__4, &l_Lean_instInhabitedTagAttribute_default___closed__4_once, _init_l_Lean_instInhabitedTagAttribute_default___closed__4);
v___x_1723_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1723_, 0, v___x_1722_);
lean_ctor_set(v___x_1723_, 1, v___x_1721_);
lean_ctor_set(v___x_1723_, 2, v___f_1720_);
lean_ctor_set(v___x_1723_, 3, v___f_1719_);
lean_ctor_set(v___x_1723_, 4, v___f_1718_);
lean_ctor_set(v___x_1723_, 5, v___f_1717_);
return v___x_1723_;
}
}
static lean_object* _init_l_Lean_instInhabitedTagAttribute_default___closed__6(void){
_start:
{
lean_object* v___x_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; 
v___x_1724_ = lean_obj_once(&l_Lean_instInhabitedTagAttribute_default___closed__5, &l_Lean_instInhabitedTagAttribute_default___closed__5_once, _init_l_Lean_instInhabitedTagAttribute_default___closed__5);
v___x_1725_ = ((lean_object*)(l_Lean_instInhabitedAttributeImpl_default));
v___x_1726_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1726_, 0, v___x_1725_);
lean_ctor_set(v___x_1726_, 1, v___x_1724_);
return v___x_1726_;
}
}
static lean_object* _init_l_Lean_instInhabitedTagAttribute_default(void){
_start:
{
lean_object* v___x_1727_; 
v___x_1727_ = lean_obj_once(&l_Lean_instInhabitedTagAttribute_default___closed__6, &l_Lean_instInhabitedTagAttribute_default___closed__6_once, _init_l_Lean_instInhabitedTagAttribute_default___closed__6);
return v___x_1727_;
}
}
static lean_object* _init_l_Lean_instInhabitedTagAttribute(void){
_start:
{
lean_object* v___x_1728_; 
v___x_1728_ = l_Lean_instInhabitedTagAttribute_default;
return v___x_1728_;
}
}
static lean_object* _init_l_Lean_registerTagAttribute___auto__1(void){
_start:
{
lean_object* v___x_1729_; 
v___x_1729_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__28, &l_Lean_AttributeImplCore_ref___autoParam___closed__28_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__28);
return v___x_1729_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__0(lean_object* v_x_1730_){
_start:
{
lean_object* v___x_1731_; 
v___x_1731_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___lam__2___closed__0));
return v___x_1731_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__0___boxed(lean_object* v_x_1732_){
_start:
{
lean_object* v_res_1733_; 
v_res_1733_ = l_Lean_registerTagAttribute___lam__0(v_x_1732_);
lean_dec(v_x_1732_);
return v_res_1733_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerTagAttribute_spec__0(lean_object* v_newState_1734_, lean_object* v_x_1735_, lean_object* v_x_1736_){
_start:
{
if (lean_obj_tag(v_x_1736_) == 0)
{
return v_x_1735_;
}
else
{
lean_object* v_head_1737_; lean_object* v_tail_1738_; uint8_t v___x_1739_; 
v_head_1737_ = lean_ctor_get(v_x_1736_, 0);
lean_inc(v_head_1737_);
v_tail_1738_ = lean_ctor_get(v_x_1736_, 1);
lean_inc(v_tail_1738_);
lean_dec_ref_known(v_x_1736_, 2);
v___x_1739_ = l_Lean_NameSet_contains(v_newState_1734_, v_head_1737_);
if (v___x_1739_ == 0)
{
lean_dec(v_head_1737_);
v_x_1736_ = v_tail_1738_;
goto _start;
}
else
{
lean_object* v___x_1741_; 
v___x_1741_ = l_Lean_NameSet_insert(v_x_1735_, v_head_1737_);
v_x_1735_ = v___x_1741_;
v_x_1736_ = v_tail_1738_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerTagAttribute_spec__0___boxed(lean_object* v_newState_1743_, lean_object* v_x_1744_, lean_object* v_x_1745_){
_start:
{
lean_object* v_res_1746_; 
v_res_1746_ = l_List_foldl___at___00Lean_registerTagAttribute_spec__0(v_newState_1743_, v_x_1744_, v_x_1745_);
lean_dec(v_newState_1743_);
return v_res_1746_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__1(lean_object* v_x_1747_, lean_object* v_newState_1748_, lean_object* v_newConsts_1749_, lean_object* v_s_1750_){
_start:
{
lean_object* v___x_1751_; 
v___x_1751_ = l_List_foldl___at___00Lean_registerTagAttribute_spec__0(v_newState_1748_, v_s_1750_, v_newConsts_1749_);
return v___x_1751_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__1___boxed(lean_object* v_x_1752_, lean_object* v_newState_1753_, lean_object* v_newConsts_1754_, lean_object* v_s_1755_){
_start:
{
lean_object* v_res_1756_; 
v_res_1756_ = l_Lean_registerTagAttribute___lam__1(v_x_1752_, v_newState_1753_, v_newConsts_1754_, v_s_1755_);
lean_dec(v_newState_1753_);
lean_dec(v_x_1752_);
return v_res_1756_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__2(lean_object* v_s_1769_){
_start:
{
lean_object* v___x_1770_; lean_object* v___y_1772_; 
v___x_1770_ = ((lean_object*)(l_Lean_registerTagAttribute___lam__2___closed__5));
if (lean_obj_tag(v_s_1769_) == 0)
{
lean_object* v_size_1776_; 
v_size_1776_ = lean_ctor_get(v_s_1769_, 0);
lean_inc(v_size_1776_);
lean_dec_ref_known(v_s_1769_, 5);
v___y_1772_ = v_size_1776_;
goto v___jp_1771_;
}
else
{
lean_object* v___x_1777_; 
v___x_1777_ = lean_unsigned_to_nat(0u);
v___y_1772_ = v___x_1777_;
goto v___jp_1771_;
}
v___jp_1771_:
{
lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; 
v___x_1773_ = l_Nat_reprFast(v___y_1772_);
v___x_1774_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1774_, 0, v___x_1773_);
v___x_1775_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1775_, 0, v___x_1770_);
lean_ctor_set(v___x_1775_, 1, v___x_1774_);
return v___x_1775_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4___redArg(lean_object* v_hi_1778_, lean_object* v_pivot_1779_, lean_object* v_as_1780_, lean_object* v_i_1781_, lean_object* v_k_1782_){
_start:
{
uint8_t v___x_1783_; 
v___x_1783_ = lean_nat_dec_lt(v_k_1782_, v_hi_1778_);
if (v___x_1783_ == 0)
{
lean_object* v___x_1784_; lean_object* v___x_1785_; 
lean_dec(v_k_1782_);
v___x_1784_ = lean_array_fswap(v_as_1780_, v_i_1781_, v_hi_1778_);
v___x_1785_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1785_, 0, v_i_1781_);
lean_ctor_set(v___x_1785_, 1, v___x_1784_);
return v___x_1785_;
}
else
{
lean_object* v___x_1786_; uint8_t v___x_1787_; 
v___x_1786_ = lean_array_fget_borrowed(v_as_1780_, v_k_1782_);
v___x_1787_ = l_Lean_Name_quickLt(v___x_1786_, v_pivot_1779_);
if (v___x_1787_ == 0)
{
lean_object* v___x_1788_; lean_object* v___x_1789_; 
v___x_1788_ = lean_unsigned_to_nat(1u);
v___x_1789_ = lean_nat_add(v_k_1782_, v___x_1788_);
lean_dec(v_k_1782_);
v_k_1782_ = v___x_1789_;
goto _start;
}
else
{
lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; 
v___x_1791_ = lean_array_fswap(v_as_1780_, v_i_1781_, v_k_1782_);
v___x_1792_ = lean_unsigned_to_nat(1u);
v___x_1793_ = lean_nat_add(v_i_1781_, v___x_1792_);
lean_dec(v_i_1781_);
v___x_1794_ = lean_nat_add(v_k_1782_, v___x_1792_);
lean_dec(v_k_1782_);
v_as_1780_ = v___x_1791_;
v_i_1781_ = v___x_1793_;
v_k_1782_ = v___x_1794_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4___redArg___boxed(lean_object* v_hi_1796_, lean_object* v_pivot_1797_, lean_object* v_as_1798_, lean_object* v_i_1799_, lean_object* v_k_1800_){
_start:
{
lean_object* v_res_1801_; 
v_res_1801_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4___redArg(v_hi_1796_, v_pivot_1797_, v_as_1798_, v_i_1799_, v_k_1800_);
lean_dec(v_pivot_1797_);
lean_dec(v_hi_1796_);
return v_res_1801_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___redArg(lean_object* v_n_1802_, lean_object* v_as_1803_, lean_object* v_lo_1804_, lean_object* v_hi_1805_){
_start:
{
lean_object* v___y_1807_; uint8_t v___x_1817_; 
v___x_1817_ = lean_nat_dec_lt(v_lo_1804_, v_hi_1805_);
if (v___x_1817_ == 0)
{
lean_dec(v_lo_1804_);
return v_as_1803_;
}
else
{
lean_object* v___x_1818_; lean_object* v___x_1819_; lean_object* v_mid_1820_; lean_object* v___y_1822_; lean_object* v___y_1828_; lean_object* v___x_1833_; lean_object* v___x_1834_; uint8_t v___x_1835_; 
v___x_1818_ = lean_nat_add(v_lo_1804_, v_hi_1805_);
v___x_1819_ = lean_unsigned_to_nat(1u);
v_mid_1820_ = lean_nat_shiftr(v___x_1818_, v___x_1819_);
lean_dec(v___x_1818_);
v___x_1833_ = lean_array_fget_borrowed(v_as_1803_, v_mid_1820_);
v___x_1834_ = lean_array_fget_borrowed(v_as_1803_, v_lo_1804_);
v___x_1835_ = l_Lean_Name_quickLt(v___x_1833_, v___x_1834_);
if (v___x_1835_ == 0)
{
v___y_1828_ = v_as_1803_;
goto v___jp_1827_;
}
else
{
lean_object* v___x_1836_; 
v___x_1836_ = lean_array_fswap(v_as_1803_, v_lo_1804_, v_mid_1820_);
v___y_1828_ = v___x_1836_;
goto v___jp_1827_;
}
v___jp_1821_:
{
lean_object* v___x_1823_; lean_object* v___x_1824_; uint8_t v___x_1825_; 
v___x_1823_ = lean_array_fget_borrowed(v___y_1822_, v_mid_1820_);
v___x_1824_ = lean_array_fget_borrowed(v___y_1822_, v_hi_1805_);
v___x_1825_ = l_Lean_Name_quickLt(v___x_1823_, v___x_1824_);
if (v___x_1825_ == 0)
{
lean_dec(v_mid_1820_);
v___y_1807_ = v___y_1822_;
goto v___jp_1806_;
}
else
{
lean_object* v___x_1826_; 
v___x_1826_ = lean_array_fswap(v___y_1822_, v_mid_1820_, v_hi_1805_);
lean_dec(v_mid_1820_);
v___y_1807_ = v___x_1826_;
goto v___jp_1806_;
}
}
v___jp_1827_:
{
lean_object* v___x_1829_; lean_object* v___x_1830_; uint8_t v___x_1831_; 
v___x_1829_ = lean_array_fget_borrowed(v___y_1828_, v_hi_1805_);
v___x_1830_ = lean_array_fget_borrowed(v___y_1828_, v_lo_1804_);
v___x_1831_ = l_Lean_Name_quickLt(v___x_1829_, v___x_1830_);
if (v___x_1831_ == 0)
{
v___y_1822_ = v___y_1828_;
goto v___jp_1821_;
}
else
{
lean_object* v___x_1832_; 
v___x_1832_ = lean_array_fswap(v___y_1828_, v_lo_1804_, v_hi_1805_);
v___y_1822_ = v___x_1832_;
goto v___jp_1821_;
}
}
}
v___jp_1806_:
{
lean_object* v_pivot_1808_; lean_object* v___x_1809_; lean_object* v_fst_1810_; lean_object* v_snd_1811_; uint8_t v___x_1812_; 
v_pivot_1808_ = lean_array_fget(v___y_1807_, v_hi_1805_);
lean_inc_n(v_lo_1804_, 2);
v___x_1809_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4___redArg(v_hi_1805_, v_pivot_1808_, v___y_1807_, v_lo_1804_, v_lo_1804_);
lean_dec(v_pivot_1808_);
v_fst_1810_ = lean_ctor_get(v___x_1809_, 0);
lean_inc(v_fst_1810_);
v_snd_1811_ = lean_ctor_get(v___x_1809_, 1);
lean_inc(v_snd_1811_);
lean_dec_ref(v___x_1809_);
v___x_1812_ = lean_nat_dec_le(v_hi_1805_, v_fst_1810_);
if (v___x_1812_ == 0)
{
lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; 
v___x_1813_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___redArg(v_n_1802_, v_snd_1811_, v_lo_1804_, v_fst_1810_);
v___x_1814_ = lean_unsigned_to_nat(1u);
v___x_1815_ = lean_nat_add(v_fst_1810_, v___x_1814_);
lean_dec(v_fst_1810_);
v_as_1803_ = v___x_1813_;
v_lo_1804_ = v___x_1815_;
goto _start;
}
else
{
lean_dec(v_fst_1810_);
lean_dec(v_lo_1804_);
return v_snd_1811_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___redArg___boxed(lean_object* v_n_1837_, lean_object* v_as_1838_, lean_object* v_lo_1839_, lean_object* v_hi_1840_){
_start:
{
lean_object* v_res_1841_; 
v_res_1841_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___redArg(v_n_1837_, v_as_1838_, v_lo_1839_, v_hi_1840_);
lean_dec(v_hi_1840_);
lean_dec(v_n_1837_);
return v_res_1841_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerTagAttribute_spec__2(lean_object* v_env_1842_, lean_object* v_as_1843_, size_t v_i_1844_, size_t v_stop_1845_, lean_object* v_b_1846_){
_start:
{
lean_object* v___y_1848_; uint8_t v___x_1852_; 
v___x_1852_ = lean_usize_dec_eq(v_i_1844_, v_stop_1845_);
if (v___x_1852_ == 0)
{
lean_object* v___x_1853_; uint8_t v___x_1854_; lean_object* v___x_1855_; uint8_t v___x_1856_; 
v___x_1853_ = lean_array_uget_borrowed(v_as_1843_, v_i_1844_);
v___x_1854_ = 1;
lean_inc_ref(v_env_1842_);
v___x_1855_ = l_Lean_Environment_setExporting(v_env_1842_, v___x_1854_);
lean_inc(v___x_1853_);
v___x_1856_ = l_Lean_Environment_contains(v___x_1855_, v___x_1853_, v___x_1852_);
if (v___x_1856_ == 0)
{
v___y_1848_ = v_b_1846_;
goto v___jp_1847_;
}
else
{
lean_object* v___x_1857_; 
lean_inc(v___x_1853_);
v___x_1857_ = lean_array_push(v_b_1846_, v___x_1853_);
v___y_1848_ = v___x_1857_;
goto v___jp_1847_;
}
}
else
{
lean_dec_ref(v_env_1842_);
return v_b_1846_;
}
v___jp_1847_:
{
size_t v___x_1849_; size_t v___x_1850_; 
v___x_1849_ = ((size_t)1ULL);
v___x_1850_ = lean_usize_add(v_i_1844_, v___x_1849_);
v_i_1844_ = v___x_1850_;
v_b_1846_ = v___y_1848_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerTagAttribute_spec__2___boxed(lean_object* v_env_1858_, lean_object* v_as_1859_, lean_object* v_i_1860_, lean_object* v_stop_1861_, lean_object* v_b_1862_){
_start:
{
size_t v_i_boxed_1863_; size_t v_stop_boxed_1864_; lean_object* v_res_1865_; 
v_i_boxed_1863_ = lean_unbox_usize(v_i_1860_);
lean_dec(v_i_1860_);
v_stop_boxed_1864_ = lean_unbox_usize(v_stop_1861_);
lean_dec(v_stop_1861_);
v_res_1865_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerTagAttribute_spec__2(v_env_1858_, v_as_1859_, v_i_boxed_1863_, v_stop_boxed_1864_, v_b_1862_);
lean_dec_ref(v_as_1859_);
return v_res_1865_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerTagAttribute_spec__1_spec__1(lean_object* v_init_1866_, lean_object* v_x_1867_){
_start:
{
if (lean_obj_tag(v_x_1867_) == 0)
{
lean_object* v_k_1868_; lean_object* v_l_1869_; lean_object* v_r_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; 
v_k_1868_ = lean_ctor_get(v_x_1867_, 1);
lean_inc(v_k_1868_);
v_l_1869_ = lean_ctor_get(v_x_1867_, 3);
lean_inc(v_l_1869_);
v_r_1870_ = lean_ctor_get(v_x_1867_, 4);
lean_inc(v_r_1870_);
lean_dec_ref_known(v_x_1867_, 5);
v___x_1871_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerTagAttribute_spec__1_spec__1(v_init_1866_, v_l_1869_);
v___x_1872_ = lean_array_push(v___x_1871_, v_k_1868_);
v_init_1866_ = v___x_1872_;
v_x_1867_ = v_r_1870_;
goto _start;
}
else
{
return v_init_1866_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__3(lean_object* v_env_1874_, lean_object* v_es_1875_){
_start:
{
lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___y_1879_; lean_object* v___x_1893_; lean_object* v___x_1894_; lean_object* v___y_1896_; lean_object* v___y_1897_; uint8_t v___x_1899_; 
v___x_1876_ = lean_unsigned_to_nat(0u);
v___x_1877_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___lam__2___closed__0));
v___x_1893_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerTagAttribute_spec__1_spec__1(v___x_1877_, v_es_1875_);
v___x_1894_ = lean_array_get_size(v___x_1893_);
v___x_1899_ = lean_nat_dec_eq(v___x_1894_, v___x_1876_);
if (v___x_1899_ == 0)
{
lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___y_1903_; uint8_t v___x_1905_; 
v___x_1900_ = lean_unsigned_to_nat(1u);
v___x_1901_ = lean_nat_sub(v___x_1894_, v___x_1900_);
v___x_1905_ = lean_nat_dec_le(v___x_1876_, v___x_1901_);
if (v___x_1905_ == 0)
{
lean_inc(v___x_1901_);
v___y_1903_ = v___x_1901_;
goto v___jp_1902_;
}
else
{
v___y_1903_ = v___x_1876_;
goto v___jp_1902_;
}
v___jp_1902_:
{
uint8_t v___x_1904_; 
v___x_1904_ = lean_nat_dec_le(v___y_1903_, v___x_1901_);
if (v___x_1904_ == 0)
{
lean_dec(v___x_1901_);
lean_inc(v___y_1903_);
v___y_1896_ = v___y_1903_;
v___y_1897_ = v___y_1903_;
goto v___jp_1895_;
}
else
{
v___y_1896_ = v___y_1903_;
v___y_1897_ = v___x_1901_;
goto v___jp_1895_;
}
}
}
else
{
v___y_1879_ = v___x_1893_;
goto v___jp_1878_;
}
v___jp_1878_:
{
lean_object* v___x_1880_; uint8_t v___x_1881_; 
v___x_1880_ = lean_array_get_size(v___y_1879_);
v___x_1881_ = lean_nat_dec_lt(v___x_1876_, v___x_1880_);
if (v___x_1881_ == 0)
{
lean_object* v___x_1882_; 
lean_dec_ref(v_env_1874_);
v___x_1882_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1882_, 0, v___x_1877_);
lean_ctor_set(v___x_1882_, 1, v___x_1877_);
lean_ctor_set(v___x_1882_, 2, v___y_1879_);
return v___x_1882_;
}
else
{
uint8_t v___x_1883_; 
v___x_1883_ = lean_nat_dec_le(v___x_1880_, v___x_1880_);
if (v___x_1883_ == 0)
{
if (v___x_1881_ == 0)
{
lean_object* v___x_1884_; 
lean_dec_ref(v_env_1874_);
v___x_1884_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1884_, 0, v___x_1877_);
lean_ctor_set(v___x_1884_, 1, v___x_1877_);
lean_ctor_set(v___x_1884_, 2, v___y_1879_);
return v___x_1884_;
}
else
{
size_t v___x_1885_; size_t v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; 
v___x_1885_ = ((size_t)0ULL);
v___x_1886_ = lean_usize_of_nat(v___x_1880_);
v___x_1887_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerTagAttribute_spec__2(v_env_1874_, v___y_1879_, v___x_1885_, v___x_1886_, v___x_1877_);
lean_inc_ref(v___x_1887_);
v___x_1888_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1888_, 0, v___x_1887_);
lean_ctor_set(v___x_1888_, 1, v___x_1887_);
lean_ctor_set(v___x_1888_, 2, v___y_1879_);
return v___x_1888_;
}
}
else
{
size_t v___x_1889_; size_t v___x_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; 
v___x_1889_ = ((size_t)0ULL);
v___x_1890_ = lean_usize_of_nat(v___x_1880_);
v___x_1891_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerTagAttribute_spec__2(v_env_1874_, v___y_1879_, v___x_1889_, v___x_1890_, v___x_1877_);
lean_inc_ref(v___x_1891_);
v___x_1892_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1892_, 0, v___x_1891_);
lean_ctor_set(v___x_1892_, 1, v___x_1891_);
lean_ctor_set(v___x_1892_, 2, v___y_1879_);
return v___x_1892_;
}
}
}
v___jp_1895_:
{
lean_object* v___x_1898_; 
v___x_1898_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___redArg(v___x_1894_, v___x_1893_, v___y_1896_, v___y_1897_);
lean_dec(v___y_1897_);
v___y_1879_ = v___x_1898_;
goto v___jp_1878_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__4(lean_object* v___x_1906_, lean_object* v_x_1907_, lean_object* v_x_1908_){
_start:
{
lean_object* v___x_1910_; 
v___x_1910_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1910_, 0, v___x_1906_);
return v___x_1910_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__4___boxed(lean_object* v___x_1911_, lean_object* v_x_1912_, lean_object* v_x_1913_, lean_object* v___y_1914_){
_start:
{
lean_object* v_res_1915_; 
v_res_1915_ = l_Lean_registerTagAttribute___lam__4(v___x_1911_, v_x_1912_, v_x_1913_);
lean_dec_ref(v_x_1913_);
lean_dec_ref(v_x_1912_);
return v_res_1915_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__5(lean_object* v___x_1916_){
_start:
{
lean_object* v___x_1918_; 
v___x_1918_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1918_, 0, v___x_1916_);
return v___x_1918_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__5___boxed(lean_object* v___x_1919_, lean_object* v___y_1920_){
_start:
{
lean_object* v_res_1921_; 
v_res_1921_ = l_Lean_registerTagAttribute___lam__5(v___x_1919_);
return v_res_1921_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__6(lean_object* v_name_1922_, lean_object* v_decl_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_){
_start:
{
lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; 
v___x_1927_ = lean_obj_once(&l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1, &l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1_once, _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1);
v___x_1928_ = l_Lean_MessageData_ofName(v_name_1922_);
v___x_1929_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1929_, 0, v___x_1927_);
lean_ctor_set(v___x_1929_, 1, v___x_1928_);
v___x_1930_ = lean_obj_once(&l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3, &l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3_once, _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3);
v___x_1931_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1931_, 0, v___x_1929_);
lean_ctor_set(v___x_1931_, 1, v___x_1930_);
v___x_1932_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_1931_, v___y_1924_, v___y_1925_);
return v___x_1932_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__6___boxed(lean_object* v_name_1933_, lean_object* v_decl_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_){
_start:
{
lean_object* v_res_1938_; 
v_res_1938_ = l_Lean_registerTagAttribute___lam__6(v_name_1933_, v_decl_1934_, v___y_1935_, v___y_1936_);
lean_dec(v___y_1936_);
lean_dec_ref(v___y_1935_);
lean_dec(v_decl_1934_);
return v_res_1938_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg(lean_object* v_attrName_1939_, lean_object* v_declName_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_){
_start:
{
lean_object* v___x_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; uint8_t v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; 
v___x_1944_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1);
v___x_1945_ = l_Lean_MessageData_ofName(v_attrName_1939_);
v___x_1946_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1946_, 0, v___x_1944_);
lean_ctor_set(v___x_1946_, 1, v___x_1945_);
v___x_1947_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__3, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__3_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__3);
v___x_1948_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1948_, 0, v___x_1946_);
lean_ctor_set(v___x_1948_, 1, v___x_1947_);
v___x_1949_ = 0;
v___x_1950_ = l_Lean_MessageData_ofConstName(v_declName_1940_, v___x_1949_);
v___x_1951_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1951_, 0, v___x_1948_);
lean_ctor_set(v___x_1951_, 1, v___x_1950_);
v___x_1952_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__5, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__5_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__5);
v___x_1953_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1953_, 0, v___x_1951_);
lean_ctor_set(v___x_1953_, 1, v___x_1952_);
v___x_1954_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_1953_, v___y_1941_, v___y_1942_);
return v___x_1954_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg___boxed(lean_object* v_attrName_1955_, lean_object* v_declName_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_){
_start:
{
lean_object* v_res_1960_; 
v_res_1960_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg(v_attrName_1955_, v_declName_1956_, v___y_1957_, v___y_1958_);
lean_dec(v___y_1958_);
lean_dec_ref(v___y_1957_);
return v_res_1960_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___redArg(lean_object* v_attrName_1961_, lean_object* v_declName_1962_, lean_object* v_asyncPrefix_x3f_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_){
_start:
{
lean_object* v___y_1968_; 
if (lean_obj_tag(v_asyncPrefix_x3f_1963_) == 0)
{
lean_object* v___x_1981_; 
v___x_1981_ = l_Lean_MessageData_nil;
v___y_1968_ = v___x_1981_;
goto v___jp_1967_;
}
else
{
lean_object* v_val_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; 
v_val_1982_ = lean_ctor_get(v_asyncPrefix_x3f_1963_, 0);
lean_inc(v_val_1982_);
lean_dec_ref_known(v_asyncPrefix_x3f_1963_, 1);
v___x_1983_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___redArg___closed__3, &l_Lean_throwAttrNotInAsyncCtx___redArg___closed__3_once, _init_l_Lean_throwAttrNotInAsyncCtx___redArg___closed__3);
v___x_1984_ = l_Lean_MessageData_ofName(v_val_1982_);
v___x_1985_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1985_, 0, v___x_1983_);
lean_ctor_set(v___x_1985_, 1, v___x_1984_);
v___x_1986_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__5, &l_Lean_throwAttrMustBeGlobal___redArg___closed__5_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__5);
v___x_1987_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1987_, 0, v___x_1985_);
lean_ctor_set(v___x_1987_, 1, v___x_1986_);
v___y_1968_ = v___x_1987_;
goto v___jp_1967_;
}
v___jp_1967_:
{
lean_object* v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; lean_object* v___x_1972_; lean_object* v___x_1973_; uint8_t v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; 
v___x_1969_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1);
v___x_1970_ = l_Lean_MessageData_ofName(v_attrName_1961_);
v___x_1971_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1971_, 0, v___x_1969_);
lean_ctor_set(v___x_1971_, 1, v___x_1970_);
v___x_1972_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__3, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__3_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__3);
v___x_1973_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1973_, 0, v___x_1971_);
lean_ctor_set(v___x_1973_, 1, v___x_1972_);
v___x_1974_ = 0;
v___x_1975_ = l_Lean_MessageData_ofConstName(v_declName_1962_, v___x_1974_);
v___x_1976_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1976_, 0, v___x_1973_);
lean_ctor_set(v___x_1976_, 1, v___x_1975_);
v___x_1977_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___redArg___closed__1, &l_Lean_throwAttrNotInAsyncCtx___redArg___closed__1_once, _init_l_Lean_throwAttrNotInAsyncCtx___redArg___closed__1);
v___x_1978_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1978_, 0, v___x_1976_);
lean_ctor_set(v___x_1978_, 1, v___x_1977_);
v___x_1979_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1979_, 0, v___x_1978_);
lean_ctor_set(v___x_1979_, 1, v___y_1968_);
v___x_1980_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_1979_, v___y_1964_, v___y_1965_);
return v___x_1980_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___redArg___boxed(lean_object* v_attrName_1988_, lean_object* v_declName_1989_, lean_object* v_asyncPrefix_x3f_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_){
_start:
{
lean_object* v_res_1994_; 
v_res_1994_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___redArg(v_attrName_1988_, v_declName_1989_, v_asyncPrefix_x3f_1990_, v___y_1991_, v___y_1992_);
lean_dec(v___y_1992_);
lean_dec_ref(v___y_1991_);
return v_res_1994_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg(lean_object* v_name_1995_, uint8_t v_kind_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_){
_start:
{
lean_object* v___x_2000_; lean_object* v___x_2001_; lean_object* v___x_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; lean_object* v___y_2006_; 
v___x_2000_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__1, &l_Lean_throwAttrMustBeGlobal___redArg___closed__1_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__1);
v___x_2001_ = l_Lean_MessageData_ofName(v_name_1995_);
v___x_2002_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2002_, 0, v___x_2000_);
lean_ctor_set(v___x_2002_, 1, v___x_2001_);
v___x_2003_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__3, &l_Lean_throwAttrMustBeGlobal___redArg___closed__3_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__3);
v___x_2004_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2004_, 0, v___x_2002_);
lean_ctor_set(v___x_2004_, 1, v___x_2003_);
switch(v_kind_1996_)
{
case 0:
{
lean_object* v___x_2013_; 
v___x_2013_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__0));
v___y_2006_ = v___x_2013_;
goto v___jp_2005_;
}
case 1:
{
lean_object* v___x_2014_; 
v___x_2014_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__1));
v___y_2006_ = v___x_2014_;
goto v___jp_2005_;
}
default: 
{
lean_object* v___x_2015_; 
v___x_2015_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__2));
v___y_2006_ = v___x_2015_;
goto v___jp_2005_;
}
}
v___jp_2005_:
{
lean_object* v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; 
lean_inc_ref(v___y_2006_);
v___x_2007_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2007_, 0, v___y_2006_);
v___x_2008_ = l_Lean_MessageData_ofFormat(v___x_2007_);
v___x_2009_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2009_, 0, v___x_2004_);
lean_ctor_set(v___x_2009_, 1, v___x_2008_);
v___x_2010_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__5, &l_Lean_throwAttrMustBeGlobal___redArg___closed__5_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__5);
v___x_2011_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2011_, 0, v___x_2009_);
lean_ctor_set(v___x_2011_, 1, v___x_2010_);
v___x_2012_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_2011_, v___y_1997_, v___y_1998_);
return v___x_2012_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg___boxed(lean_object* v_name_2016_, lean_object* v_kind_2017_, lean_object* v___y_2018_, lean_object* v___y_2019_, lean_object* v___y_2020_){
_start:
{
uint8_t v_kind_boxed_2021_; lean_object* v_res_2022_; 
v_kind_boxed_2021_ = lean_unbox(v_kind_2017_);
v_res_2022_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg(v_name_2016_, v_kind_boxed_2021_, v___y_2018_, v___y_2019_);
lean_dec(v___y_2019_);
lean_dec_ref(v___y_2018_);
return v_res_2022_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__7(lean_object* v_validate_2023_, lean_object* v_a_2024_, lean_object* v_name_2025_, lean_object* v_decl_2026_, lean_object* v_stx_2027_, uint8_t v_kind_2028_, lean_object* v___y_2029_, lean_object* v___y_2030_){
_start:
{
lean_object* v___y_2033_; lean_object* v___y_2034_; lean_object* v___y_2068_; lean_object* v___y_2069_; lean_object* v___y_2070_; lean_object* v___y_2077_; lean_object* v___y_2078_; lean_object* v___x_2083_; 
v___x_2083_ = l_Lean_Attribute_Builtin_ensureNoArgs(v_stx_2027_, v___y_2029_, v___y_2030_);
if (lean_obj_tag(v___x_2083_) == 0)
{
uint8_t v___x_2084_; uint8_t v___x_2085_; 
lean_dec_ref_known(v___x_2083_, 1);
v___x_2084_ = 0;
v___x_2085_ = l_Lean_instBEqAttributeKind_beq(v_kind_2028_, v___x_2084_);
if (v___x_2085_ == 0)
{
lean_object* v___x_2086_; 
lean_dec(v_decl_2026_);
lean_dec_ref(v_a_2024_);
lean_dec_ref(v_validate_2023_);
v___x_2086_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg(v_name_2025_, v_kind_2028_, v___y_2029_, v___y_2030_);
return v___x_2086_;
}
else
{
v___y_2077_ = v___y_2029_;
v___y_2078_ = v___y_2030_;
goto v___jp_2076_;
}
}
else
{
lean_dec(v_decl_2026_);
lean_dec(v_name_2025_);
lean_dec_ref(v_a_2024_);
lean_dec_ref(v_validate_2023_);
return v___x_2083_;
}
v___jp_2032_:
{
lean_object* v___x_2035_; 
lean_inc(v___y_2034_);
lean_inc_ref(v___y_2033_);
lean_inc(v_decl_2026_);
v___x_2035_ = lean_apply_4(v_validate_2023_, v_decl_2026_, v___y_2033_, v___y_2034_, lean_box(0));
if (lean_obj_tag(v___x_2035_) == 0)
{
lean_object* v___x_2037_; uint8_t v_isShared_2038_; uint8_t v_isSharedCheck_2065_; 
v_isSharedCheck_2065_ = !lean_is_exclusive(v___x_2035_);
if (v_isSharedCheck_2065_ == 0)
{
lean_object* v_unused_2066_; 
v_unused_2066_ = lean_ctor_get(v___x_2035_, 0);
lean_dec(v_unused_2066_);
v___x_2037_ = v___x_2035_;
v_isShared_2038_ = v_isSharedCheck_2065_;
goto v_resetjp_2036_;
}
else
{
lean_dec(v___x_2035_);
v___x_2037_ = lean_box(0);
v_isShared_2038_ = v_isSharedCheck_2065_;
goto v_resetjp_2036_;
}
v_resetjp_2036_:
{
lean_object* v___x_2039_; lean_object* v_toEnvExtension_2040_; lean_object* v_env_2041_; lean_object* v_nextMacroScope_2042_; lean_object* v_ngen_2043_; lean_object* v_auxDeclNGen_2044_; lean_object* v_traceState_2045_; lean_object* v_messages_2046_; lean_object* v_infoState_2047_; lean_object* v_snapshotTasks_2048_; lean_object* v___x_2050_; uint8_t v_isShared_2051_; uint8_t v_isSharedCheck_2063_; 
v___x_2039_ = lean_st_ref_take(v___y_2034_);
v_toEnvExtension_2040_ = lean_ctor_get(v_a_2024_, 0);
v_env_2041_ = lean_ctor_get(v___x_2039_, 0);
v_nextMacroScope_2042_ = lean_ctor_get(v___x_2039_, 1);
v_ngen_2043_ = lean_ctor_get(v___x_2039_, 2);
v_auxDeclNGen_2044_ = lean_ctor_get(v___x_2039_, 3);
v_traceState_2045_ = lean_ctor_get(v___x_2039_, 4);
v_messages_2046_ = lean_ctor_get(v___x_2039_, 6);
v_infoState_2047_ = lean_ctor_get(v___x_2039_, 7);
v_snapshotTasks_2048_ = lean_ctor_get(v___x_2039_, 8);
v_isSharedCheck_2063_ = !lean_is_exclusive(v___x_2039_);
if (v_isSharedCheck_2063_ == 0)
{
lean_object* v_unused_2064_; 
v_unused_2064_ = lean_ctor_get(v___x_2039_, 5);
lean_dec(v_unused_2064_);
v___x_2050_ = v___x_2039_;
v_isShared_2051_ = v_isSharedCheck_2063_;
goto v_resetjp_2049_;
}
else
{
lean_inc(v_snapshotTasks_2048_);
lean_inc(v_infoState_2047_);
lean_inc(v_messages_2046_);
lean_inc(v_traceState_2045_);
lean_inc(v_auxDeclNGen_2044_);
lean_inc(v_ngen_2043_);
lean_inc(v_nextMacroScope_2042_);
lean_inc(v_env_2041_);
lean_dec(v___x_2039_);
v___x_2050_ = lean_box(0);
v_isShared_2051_ = v_isSharedCheck_2063_;
goto v_resetjp_2049_;
}
v_resetjp_2049_:
{
lean_object* v_asyncMode_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2056_; 
v_asyncMode_2052_ = lean_ctor_get(v_toEnvExtension_2040_, 2);
lean_inc(v_asyncMode_2052_);
lean_inc(v_decl_2026_);
v___x_2053_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_a_2024_, v_env_2041_, v_decl_2026_, v_asyncMode_2052_, v_decl_2026_);
lean_dec(v_asyncMode_2052_);
v___x_2054_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2);
if (v_isShared_2051_ == 0)
{
lean_ctor_set(v___x_2050_, 5, v___x_2054_);
lean_ctor_set(v___x_2050_, 0, v___x_2053_);
v___x_2056_ = v___x_2050_;
goto v_reusejp_2055_;
}
else
{
lean_object* v_reuseFailAlloc_2062_; 
v_reuseFailAlloc_2062_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2062_, 0, v___x_2053_);
lean_ctor_set(v_reuseFailAlloc_2062_, 1, v_nextMacroScope_2042_);
lean_ctor_set(v_reuseFailAlloc_2062_, 2, v_ngen_2043_);
lean_ctor_set(v_reuseFailAlloc_2062_, 3, v_auxDeclNGen_2044_);
lean_ctor_set(v_reuseFailAlloc_2062_, 4, v_traceState_2045_);
lean_ctor_set(v_reuseFailAlloc_2062_, 5, v___x_2054_);
lean_ctor_set(v_reuseFailAlloc_2062_, 6, v_messages_2046_);
lean_ctor_set(v_reuseFailAlloc_2062_, 7, v_infoState_2047_);
lean_ctor_set(v_reuseFailAlloc_2062_, 8, v_snapshotTasks_2048_);
v___x_2056_ = v_reuseFailAlloc_2062_;
goto v_reusejp_2055_;
}
v_reusejp_2055_:
{
lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2060_; 
v___x_2057_ = lean_st_ref_set(v___y_2034_, v___x_2056_);
v___x_2058_ = lean_box(0);
if (v_isShared_2038_ == 0)
{
lean_ctor_set(v___x_2037_, 0, v___x_2058_);
v___x_2060_ = v___x_2037_;
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
}
}
else
{
lean_dec(v_decl_2026_);
lean_dec_ref(v_a_2024_);
return v___x_2035_;
}
}
v___jp_2067_:
{
lean_object* v_toEnvExtension_2071_; lean_object* v_asyncMode_2072_; uint8_t v___x_2073_; 
v_toEnvExtension_2071_ = lean_ctor_get(v_a_2024_, 0);
v_asyncMode_2072_ = lean_ctor_get(v_toEnvExtension_2071_, 2);
lean_inc(v_decl_2026_);
lean_inc_ref(v___y_2068_);
v___x_2073_ = l_Lean_EnvExtension_asyncMayModify___redArg(v___y_2068_, v_decl_2026_, v_asyncMode_2072_);
if (v___x_2073_ == 0)
{
lean_object* v___x_2074_; lean_object* v___x_2075_; 
lean_dec_ref(v_a_2024_);
lean_dec_ref(v_validate_2023_);
v___x_2074_ = l_Lean_Environment_asyncPrefix_x3f(v___y_2068_);
v___x_2075_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___redArg(v_name_2025_, v_decl_2026_, v___x_2074_, v___y_2069_, v___y_2070_);
return v___x_2075_;
}
else
{
lean_dec_ref(v___y_2068_);
lean_dec(v_name_2025_);
v___y_2033_ = v___y_2069_;
v___y_2034_ = v___y_2070_;
goto v___jp_2032_;
}
}
v___jp_2076_:
{
lean_object* v___x_2079_; lean_object* v_env_2080_; lean_object* v___x_2081_; 
v___x_2079_ = lean_st_ref_get(v___y_2078_);
v_env_2080_ = lean_ctor_get(v___x_2079_, 0);
lean_inc_ref(v_env_2080_);
lean_dec(v___x_2079_);
v___x_2081_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2080_, v_decl_2026_);
if (lean_obj_tag(v___x_2081_) == 0)
{
v___y_2068_ = v_env_2080_;
v___y_2069_ = v___y_2077_;
v___y_2070_ = v___y_2078_;
goto v___jp_2067_;
}
else
{
lean_object* v___x_2082_; 
lean_dec_ref_known(v___x_2081_, 1);
lean_dec_ref(v_env_2080_);
lean_dec_ref(v_a_2024_);
lean_dec_ref(v_validate_2023_);
v___x_2082_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg(v_name_2025_, v_decl_2026_, v___y_2077_, v___y_2078_);
return v___x_2082_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__7___boxed(lean_object* v_validate_2087_, lean_object* v_a_2088_, lean_object* v_name_2089_, lean_object* v_decl_2090_, lean_object* v_stx_2091_, lean_object* v_kind_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_){
_start:
{
uint8_t v_kind_boxed_2096_; lean_object* v_res_2097_; 
v_kind_boxed_2096_ = lean_unbox(v_kind_2092_);
v_res_2097_ = l_Lean_registerTagAttribute___lam__7(v_validate_2087_, v_a_2088_, v_name_2089_, v_decl_2090_, v_stx_2091_, v_kind_boxed_2096_, v___y_2093_, v___y_2094_);
lean_dec(v___y_2094_);
lean_dec_ref(v___y_2093_);
return v_res_2097_;
}
}
static lean_object* _init_l_Lean_registerTagAttribute___closed__5(void){
_start:
{
lean_object* v___x_2103_; lean_object* v___f_2104_; 
v___x_2103_ = l_Lean_NameSet_empty;
v___f_2104_ = lean_alloc_closure((void*)(l_Lean_registerTagAttribute___lam__4___boxed), 4, 1);
lean_closure_set(v___f_2104_, 0, v___x_2103_);
return v___f_2104_;
}
}
static lean_object* _init_l_Lean_registerTagAttribute___closed__6(void){
_start:
{
lean_object* v___x_2105_; lean_object* v___f_2106_; 
v___x_2105_ = l_Lean_NameSet_empty;
v___f_2106_ = lean_alloc_closure((void*)(l_Lean_registerTagAttribute___lam__5___boxed), 2, 1);
lean_closure_set(v___f_2106_, 0, v___x_2105_);
return v___f_2106_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute(lean_object* v_name_2109_, lean_object* v_descr_2110_, lean_object* v_validate_2111_, lean_object* v_ref_2112_, uint8_t v_applicationTime_2113_, lean_object* v_asyncMode_2114_){
_start:
{
lean_object* v___f_2116_; lean_object* v___f_2117_; lean_object* v___f_2118_; lean_object* v___f_2119_; lean_object* v___f_2120_; lean_object* v___f_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; 
v___f_2116_ = ((lean_object*)(l_Lean_registerTagAttribute___closed__0));
v___f_2117_ = ((lean_object*)(l_Lean_registerTagAttribute___closed__2));
v___f_2118_ = ((lean_object*)(l_Lean_registerTagAttribute___closed__3));
v___f_2119_ = ((lean_object*)(l_Lean_registerTagAttribute___closed__4));
v___f_2120_ = lean_obj_once(&l_Lean_registerTagAttribute___closed__5, &l_Lean_registerTagAttribute___closed__5_once, _init_l_Lean_registerTagAttribute___closed__5);
v___f_2121_ = lean_obj_once(&l_Lean_registerTagAttribute___closed__6, &l_Lean_registerTagAttribute___closed__6_once, _init_l_Lean_registerTagAttribute___closed__6);
v___x_2122_ = ((lean_object*)(l_Lean_registerTagAttribute___closed__7));
lean_inc(v_ref_2112_);
v___x_2123_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_2123_, 0, v_ref_2112_);
lean_ctor_set(v___x_2123_, 1, v___f_2121_);
lean_ctor_set(v___x_2123_, 2, v___f_2120_);
lean_ctor_set(v___x_2123_, 3, v___f_2119_);
lean_ctor_set(v___x_2123_, 4, v___f_2118_);
lean_ctor_set(v___x_2123_, 5, v___f_2117_);
lean_ctor_set(v___x_2123_, 6, v_asyncMode_2114_);
lean_ctor_set(v___x_2123_, 7, v___x_2122_);
v___x_2124_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2124_, 0, v___x_2123_);
lean_ctor_set(v___x_2124_, 1, v___f_2116_);
v___x_2125_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_2124_);
if (lean_obj_tag(v___x_2125_) == 0)
{
lean_object* v_a_2126_; lean_object* v___f_2127_; lean_object* v___f_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; 
v_a_2126_ = lean_ctor_get(v___x_2125_, 0);
lean_inc_n(v_a_2126_, 2);
lean_dec_ref_known(v___x_2125_, 1);
lean_inc_n(v_name_2109_, 2);
v___f_2127_ = lean_alloc_closure((void*)(l_Lean_registerTagAttribute___lam__6___boxed), 5, 1);
lean_closure_set(v___f_2127_, 0, v_name_2109_);
v___f_2128_ = lean_alloc_closure((void*)(l_Lean_registerTagAttribute___lam__7___boxed), 9, 3);
lean_closure_set(v___f_2128_, 0, v_validate_2111_);
lean_closure_set(v___f_2128_, 1, v_a_2126_);
lean_closure_set(v___f_2128_, 2, v_name_2109_);
v___x_2129_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2129_, 0, v_ref_2112_);
lean_ctor_set(v___x_2129_, 1, v_name_2109_);
lean_ctor_set(v___x_2129_, 2, v_descr_2110_);
lean_ctor_set_uint8(v___x_2129_, sizeof(void*)*3, v_applicationTime_2113_);
v___x_2130_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2130_, 0, v___x_2129_);
lean_ctor_set(v___x_2130_, 1, v___f_2128_);
lean_ctor_set(v___x_2130_, 2, v___f_2127_);
lean_inc_ref(v___x_2130_);
v___x_2131_ = l_Lean_registerBuiltinAttribute(v___x_2130_);
if (lean_obj_tag(v___x_2131_) == 0)
{
lean_object* v___x_2133_; uint8_t v_isShared_2134_; uint8_t v_isSharedCheck_2139_; 
v_isSharedCheck_2139_ = !lean_is_exclusive(v___x_2131_);
if (v_isSharedCheck_2139_ == 0)
{
lean_object* v_unused_2140_; 
v_unused_2140_ = lean_ctor_get(v___x_2131_, 0);
lean_dec(v_unused_2140_);
v___x_2133_ = v___x_2131_;
v_isShared_2134_ = v_isSharedCheck_2139_;
goto v_resetjp_2132_;
}
else
{
lean_dec(v___x_2131_);
v___x_2133_ = lean_box(0);
v_isShared_2134_ = v_isSharedCheck_2139_;
goto v_resetjp_2132_;
}
v_resetjp_2132_:
{
lean_object* v___x_2135_; lean_object* v___x_2137_; 
v___x_2135_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2135_, 0, v___x_2130_);
lean_ctor_set(v___x_2135_, 1, v_a_2126_);
if (v_isShared_2134_ == 0)
{
lean_ctor_set(v___x_2133_, 0, v___x_2135_);
v___x_2137_ = v___x_2133_;
goto v_reusejp_2136_;
}
else
{
lean_object* v_reuseFailAlloc_2138_; 
v_reuseFailAlloc_2138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2138_, 0, v___x_2135_);
v___x_2137_ = v_reuseFailAlloc_2138_;
goto v_reusejp_2136_;
}
v_reusejp_2136_:
{
return v___x_2137_;
}
}
}
else
{
lean_object* v_a_2141_; lean_object* v___x_2143_; uint8_t v_isShared_2144_; uint8_t v_isSharedCheck_2148_; 
lean_dec_ref_known(v___x_2130_, 3);
lean_dec(v_a_2126_);
v_a_2141_ = lean_ctor_get(v___x_2131_, 0);
v_isSharedCheck_2148_ = !lean_is_exclusive(v___x_2131_);
if (v_isSharedCheck_2148_ == 0)
{
v___x_2143_ = v___x_2131_;
v_isShared_2144_ = v_isSharedCheck_2148_;
goto v_resetjp_2142_;
}
else
{
lean_inc(v_a_2141_);
lean_dec(v___x_2131_);
v___x_2143_ = lean_box(0);
v_isShared_2144_ = v_isSharedCheck_2148_;
goto v_resetjp_2142_;
}
v_resetjp_2142_:
{
lean_object* v___x_2146_; 
if (v_isShared_2144_ == 0)
{
v___x_2146_ = v___x_2143_;
goto v_reusejp_2145_;
}
else
{
lean_object* v_reuseFailAlloc_2147_; 
v_reuseFailAlloc_2147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2147_, 0, v_a_2141_);
v___x_2146_ = v_reuseFailAlloc_2147_;
goto v_reusejp_2145_;
}
v_reusejp_2145_:
{
return v___x_2146_;
}
}
}
}
else
{
lean_object* v_a_2149_; lean_object* v___x_2151_; uint8_t v_isShared_2152_; uint8_t v_isSharedCheck_2156_; 
lean_dec(v_ref_2112_);
lean_dec_ref(v_validate_2111_);
lean_dec_ref(v_descr_2110_);
lean_dec(v_name_2109_);
v_a_2149_ = lean_ctor_get(v___x_2125_, 0);
v_isSharedCheck_2156_ = !lean_is_exclusive(v___x_2125_);
if (v_isSharedCheck_2156_ == 0)
{
v___x_2151_ = v___x_2125_;
v_isShared_2152_ = v_isSharedCheck_2156_;
goto v_resetjp_2150_;
}
else
{
lean_inc(v_a_2149_);
lean_dec(v___x_2125_);
v___x_2151_ = lean_box(0);
v_isShared_2152_ = v_isSharedCheck_2156_;
goto v_resetjp_2150_;
}
v_resetjp_2150_:
{
lean_object* v___x_2154_; 
if (v_isShared_2152_ == 0)
{
v___x_2154_ = v___x_2151_;
goto v_reusejp_2153_;
}
else
{
lean_object* v_reuseFailAlloc_2155_; 
v_reuseFailAlloc_2155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2155_, 0, v_a_2149_);
v___x_2154_ = v_reuseFailAlloc_2155_;
goto v_reusejp_2153_;
}
v_reusejp_2153_:
{
return v___x_2154_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___boxed(lean_object* v_name_2157_, lean_object* v_descr_2158_, lean_object* v_validate_2159_, lean_object* v_ref_2160_, lean_object* v_applicationTime_2161_, lean_object* v_asyncMode_2162_, lean_object* v_a_2163_){
_start:
{
uint8_t v_applicationTime_boxed_2164_; lean_object* v_res_2165_; 
v_applicationTime_boxed_2164_ = lean_unbox(v_applicationTime_2161_);
v_res_2165_ = l_Lean_registerTagAttribute(v_name_2157_, v_descr_2158_, v_validate_2159_, v_ref_2160_, v_applicationTime_boxed_2164_, v_asyncMode_2162_);
return v_res_2165_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerTagAttribute_spec__1(lean_object* v_init_2166_, lean_object* v_t_2167_){
_start:
{
lean_object* v___x_2168_; 
v___x_2168_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerTagAttribute_spec__1_spec__1(v_init_2166_, v_t_2167_);
return v___x_2168_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3(lean_object* v_n_2169_, lean_object* v_as_2170_, lean_object* v_lo_2171_, lean_object* v_hi_2172_, lean_object* v_w_2173_, lean_object* v_hlo_2174_, lean_object* v_hhi_2175_){
_start:
{
lean_object* v___x_2176_; 
v___x_2176_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___redArg(v_n_2169_, v_as_2170_, v_lo_2171_, v_hi_2172_);
return v___x_2176_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___boxed(lean_object* v_n_2177_, lean_object* v_as_2178_, lean_object* v_lo_2179_, lean_object* v_hi_2180_, lean_object* v_w_2181_, lean_object* v_hlo_2182_, lean_object* v_hhi_2183_){
_start:
{
lean_object* v_res_2184_; 
v_res_2184_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3(v_n_2177_, v_as_2178_, v_lo_2179_, v_hi_2180_, v_w_2181_, v_hlo_2182_, v_hhi_2183_);
lean_dec(v_hi_2180_);
lean_dec(v_n_2177_);
return v_res_2184_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4(lean_object* v_00_u03b1_2185_, lean_object* v_attrName_2186_, lean_object* v_declName_2187_, lean_object* v_asyncPrefix_x3f_2188_, lean_object* v___y_2189_, lean_object* v___y_2190_){
_start:
{
lean_object* v___x_2192_; 
v___x_2192_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___redArg(v_attrName_2186_, v_declName_2187_, v_asyncPrefix_x3f_2188_, v___y_2189_, v___y_2190_);
return v___x_2192_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___boxed(lean_object* v_00_u03b1_2193_, lean_object* v_attrName_2194_, lean_object* v_declName_2195_, lean_object* v_asyncPrefix_x3f_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_){
_start:
{
lean_object* v_res_2200_; 
v_res_2200_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4(v_00_u03b1_2193_, v_attrName_2194_, v_declName_2195_, v_asyncPrefix_x3f_2196_, v___y_2197_, v___y_2198_);
lean_dec(v___y_2198_);
lean_dec_ref(v___y_2197_);
return v_res_2200_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5(lean_object* v_00_u03b1_2201_, lean_object* v_attrName_2202_, lean_object* v_declName_2203_, lean_object* v___y_2204_, lean_object* v___y_2205_){
_start:
{
lean_object* v___x_2207_; 
v___x_2207_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg(v_attrName_2202_, v_declName_2203_, v___y_2204_, v___y_2205_);
return v___x_2207_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___boxed(lean_object* v_00_u03b1_2208_, lean_object* v_attrName_2209_, lean_object* v_declName_2210_, lean_object* v___y_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_){
_start:
{
lean_object* v_res_2214_; 
v_res_2214_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5(v_00_u03b1_2208_, v_attrName_2209_, v_declName_2210_, v___y_2211_, v___y_2212_);
lean_dec(v___y_2212_);
lean_dec_ref(v___y_2211_);
return v_res_2214_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6(lean_object* v_00_u03b1_2215_, lean_object* v_name_2216_, uint8_t v_kind_2217_, lean_object* v___y_2218_, lean_object* v___y_2219_){
_start:
{
lean_object* v___x_2221_; 
v___x_2221_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg(v_name_2216_, v_kind_2217_, v___y_2218_, v___y_2219_);
return v___x_2221_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___boxed(lean_object* v_00_u03b1_2222_, lean_object* v_name_2223_, lean_object* v_kind_2224_, lean_object* v___y_2225_, lean_object* v___y_2226_, lean_object* v___y_2227_){
_start:
{
uint8_t v_kind_boxed_2228_; lean_object* v_res_2229_; 
v_kind_boxed_2228_ = lean_unbox(v_kind_2224_);
v_res_2229_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6(v_00_u03b1_2222_, v_name_2223_, v_kind_boxed_2228_, v___y_2225_, v___y_2226_);
lean_dec(v___y_2226_);
lean_dec_ref(v___y_2225_);
return v_res_2229_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4(lean_object* v_n_2230_, lean_object* v_lo_2231_, lean_object* v_hi_2232_, lean_object* v_hhi_2233_, lean_object* v_pivot_2234_, lean_object* v_as_2235_, lean_object* v_i_2236_, lean_object* v_k_2237_, lean_object* v_ilo_2238_, lean_object* v_ik_2239_, lean_object* v_w_2240_){
_start:
{
lean_object* v___x_2241_; 
v___x_2241_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4___redArg(v_hi_2232_, v_pivot_2234_, v_as_2235_, v_i_2236_, v_k_2237_);
return v___x_2241_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4___boxed(lean_object* v_n_2242_, lean_object* v_lo_2243_, lean_object* v_hi_2244_, lean_object* v_hhi_2245_, lean_object* v_pivot_2246_, lean_object* v_as_2247_, lean_object* v_i_2248_, lean_object* v_k_2249_, lean_object* v_ilo_2250_, lean_object* v_ik_2251_, lean_object* v_w_2252_){
_start:
{
lean_object* v_res_2253_; 
v_res_2253_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4(v_n_2242_, v_lo_2243_, v_hi_2244_, v_hhi_2245_, v_pivot_2246_, v_as_2247_, v_i_2248_, v_k_2249_, v_ilo_2250_, v_ik_2251_, v_w_2252_);
lean_dec(v_pivot_2246_);
lean_dec(v_hi_2244_);
lean_dec(v_lo_2243_);
lean_dec(v_n_2242_);
return v_res_2253_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg___lam__0(lean_object* v_attr_2254_, lean_object* v_decl_2255_, lean_object* v_env_2256_){
_start:
{
lean_object* v_ext_2257_; lean_object* v_toEnvExtension_2258_; lean_object* v_asyncMode_2259_; lean_object* v___x_2260_; 
v_ext_2257_ = lean_ctor_get(v_attr_2254_, 1);
lean_inc_ref(v_ext_2257_);
lean_dec_ref(v_attr_2254_);
v_toEnvExtension_2258_ = lean_ctor_get(v_ext_2257_, 0);
v_asyncMode_2259_ = lean_ctor_get(v_toEnvExtension_2258_, 2);
lean_inc(v_asyncMode_2259_);
lean_inc(v_decl_2255_);
v___x_2260_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_ext_2257_, v_env_2256_, v_decl_2255_, v_asyncMode_2259_, v_decl_2255_);
lean_dec(v_asyncMode_2259_);
return v___x_2260_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg___lam__1(lean_object* v_modifyEnv_2261_, lean_object* v___f_2262_, lean_object* v_____r_2263_){
_start:
{
lean_object* v___x_2264_; 
v___x_2264_ = lean_apply_1(v_modifyEnv_2261_, v___f_2262_);
return v___x_2264_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg___lam__2(lean_object* v_attr_2265_, lean_object* v_env_2266_, lean_object* v_decl_2267_, lean_object* v_inst_2268_, lean_object* v_inst_2269_, lean_object* v_toBind_2270_, lean_object* v___f_2271_, lean_object* v_modifyEnv_2272_, lean_object* v___f_2273_, lean_object* v_____r_2274_){
_start:
{
lean_object* v_ext_2275_; lean_object* v_toEnvExtension_2276_; lean_object* v_attr_2277_; lean_object* v_asyncMode_2278_; uint8_t v___x_2279_; 
v_ext_2275_ = lean_ctor_get(v_attr_2265_, 1);
v_toEnvExtension_2276_ = lean_ctor_get(v_ext_2275_, 0);
lean_inc_ref(v_toEnvExtension_2276_);
v_attr_2277_ = lean_ctor_get(v_attr_2265_, 0);
lean_inc_ref(v_attr_2277_);
lean_dec_ref(v_attr_2265_);
v_asyncMode_2278_ = lean_ctor_get(v_toEnvExtension_2276_, 2);
lean_inc(v_asyncMode_2278_);
lean_dec_ref(v_toEnvExtension_2276_);
lean_inc(v_decl_2267_);
lean_inc_ref(v_env_2266_);
v___x_2279_ = l_Lean_EnvExtension_asyncMayModify___redArg(v_env_2266_, v_decl_2267_, v_asyncMode_2278_);
lean_dec(v_asyncMode_2278_);
if (v___x_2279_ == 0)
{
lean_object* v_toAttributeImplCore_2280_; lean_object* v_name_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; 
lean_dec_ref(v___f_2273_);
lean_dec(v_modifyEnv_2272_);
v_toAttributeImplCore_2280_ = lean_ctor_get(v_attr_2277_, 0);
lean_inc_ref(v_toAttributeImplCore_2280_);
lean_dec_ref(v_attr_2277_);
v_name_2281_ = lean_ctor_get(v_toAttributeImplCore_2280_, 1);
lean_inc(v_name_2281_);
lean_dec_ref(v_toAttributeImplCore_2280_);
v___x_2282_ = l_Lean_Environment_asyncPrefix_x3f(v_env_2266_);
v___x_2283_ = l_Lean_throwAttrNotInAsyncCtx___redArg(v_inst_2268_, v_inst_2269_, v_name_2281_, v_decl_2267_, v___x_2282_);
v___x_2284_ = lean_apply_4(v_toBind_2270_, lean_box(0), lean_box(0), v___x_2283_, v___f_2271_);
return v___x_2284_;
}
else
{
lean_object* v___x_2285_; 
lean_dec_ref(v_attr_2277_);
lean_dec(v___f_2271_);
lean_dec(v_toBind_2270_);
lean_dec_ref(v_inst_2269_);
lean_dec_ref(v_inst_2268_);
lean_dec(v_decl_2267_);
lean_dec_ref(v_env_2266_);
v___x_2285_ = lean_apply_1(v_modifyEnv_2272_, v___f_2273_);
return v___x_2285_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg___lam__3(lean_object* v___f_2286_, lean_object* v_____r_2287_){
_start:
{
lean_object* v___x_2288_; 
v___x_2288_ = lean_apply_1(v___f_2286_, v_____r_2287_);
return v___x_2288_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg___lam__4(lean_object* v_attr_2289_, lean_object* v_decl_2290_, lean_object* v_inst_2291_, lean_object* v_inst_2292_, lean_object* v_toBind_2293_, lean_object* v___f_2294_, lean_object* v_modifyEnv_2295_, lean_object* v___f_2296_, lean_object* v_env_2297_){
_start:
{
lean_object* v___f_2298_; lean_object* v___x_2299_; 
lean_inc_ref(v___f_2296_);
lean_inc(v_modifyEnv_2295_);
lean_inc(v___f_2294_);
lean_inc(v_toBind_2293_);
lean_inc_ref(v_inst_2292_);
lean_inc_ref(v_inst_2291_);
lean_inc(v_decl_2290_);
lean_inc_ref(v_env_2297_);
lean_inc_ref(v_attr_2289_);
v___f_2298_ = lean_alloc_closure((void*)(l_Lean_TagAttribute_setTag___redArg___lam__2), 10, 9);
lean_closure_set(v___f_2298_, 0, v_attr_2289_);
lean_closure_set(v___f_2298_, 1, v_env_2297_);
lean_closure_set(v___f_2298_, 2, v_decl_2290_);
lean_closure_set(v___f_2298_, 3, v_inst_2291_);
lean_closure_set(v___f_2298_, 4, v_inst_2292_);
lean_closure_set(v___f_2298_, 5, v_toBind_2293_);
lean_closure_set(v___f_2298_, 6, v___f_2294_);
lean_closure_set(v___f_2298_, 7, v_modifyEnv_2295_);
lean_closure_set(v___f_2298_, 8, v___f_2296_);
v___x_2299_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2297_, v_decl_2290_);
if (lean_obj_tag(v___x_2299_) == 0)
{
lean_object* v___x_2300_; lean_object* v___x_2301_; 
lean_dec_ref(v___f_2298_);
v___x_2300_ = lean_box(0);
v___x_2301_ = l_Lean_TagAttribute_setTag___redArg___lam__2(v_attr_2289_, v_env_2297_, v_decl_2290_, v_inst_2291_, v_inst_2292_, v_toBind_2293_, v___f_2294_, v_modifyEnv_2295_, v___f_2296_, v___x_2300_);
return v___x_2301_;
}
else
{
lean_object* v_attr_2302_; lean_object* v_toAttributeImplCore_2303_; lean_object* v_name_2304_; lean_object* v___f_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; 
lean_dec_ref_known(v___x_2299_, 1);
lean_dec_ref(v_env_2297_);
lean_dec_ref(v___f_2296_);
lean_dec(v_modifyEnv_2295_);
lean_dec(v___f_2294_);
v_attr_2302_ = lean_ctor_get(v_attr_2289_, 0);
lean_inc_ref(v_attr_2302_);
lean_dec_ref(v_attr_2289_);
v_toAttributeImplCore_2303_ = lean_ctor_get(v_attr_2302_, 0);
lean_inc_ref(v_toAttributeImplCore_2303_);
lean_dec_ref(v_attr_2302_);
v_name_2304_ = lean_ctor_get(v_toAttributeImplCore_2303_, 1);
lean_inc(v_name_2304_);
lean_dec_ref(v_toAttributeImplCore_2303_);
v___f_2305_ = lean_alloc_closure((void*)(l_Lean_TagAttribute_setTag___redArg___lam__3), 2, 1);
lean_closure_set(v___f_2305_, 0, v___f_2298_);
v___x_2306_ = l_Lean_throwAttrDeclInImportedModule___redArg(v_inst_2291_, v_inst_2292_, v_name_2304_, v_decl_2290_);
v___x_2307_ = lean_apply_4(v_toBind_2293_, lean_box(0), lean_box(0), v___x_2306_, v___f_2305_);
return v___x_2307_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg(lean_object* v_inst_2308_, lean_object* v_inst_2309_, lean_object* v_inst_2310_, lean_object* v_attr_2311_, lean_object* v_decl_2312_){
_start:
{
lean_object* v_toBind_2313_; lean_object* v_getEnv_2314_; lean_object* v_modifyEnv_2315_; lean_object* v___f_2316_; lean_object* v___f_2317_; lean_object* v___f_2318_; lean_object* v___x_2319_; 
v_toBind_2313_ = lean_ctor_get(v_inst_2308_, 1);
lean_inc_n(v_toBind_2313_, 2);
v_getEnv_2314_ = lean_ctor_get(v_inst_2310_, 0);
lean_inc(v_getEnv_2314_);
v_modifyEnv_2315_ = lean_ctor_get(v_inst_2310_, 1);
lean_inc_n(v_modifyEnv_2315_, 2);
lean_dec_ref(v_inst_2310_);
lean_inc(v_decl_2312_);
lean_inc_ref(v_attr_2311_);
v___f_2316_ = lean_alloc_closure((void*)(l_Lean_TagAttribute_setTag___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2316_, 0, v_attr_2311_);
lean_closure_set(v___f_2316_, 1, v_decl_2312_);
lean_inc_ref(v___f_2316_);
v___f_2317_ = lean_alloc_closure((void*)(l_Lean_TagAttribute_setTag___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2317_, 0, v_modifyEnv_2315_);
lean_closure_set(v___f_2317_, 1, v___f_2316_);
v___f_2318_ = lean_alloc_closure((void*)(l_Lean_TagAttribute_setTag___redArg___lam__4), 9, 8);
lean_closure_set(v___f_2318_, 0, v_attr_2311_);
lean_closure_set(v___f_2318_, 1, v_decl_2312_);
lean_closure_set(v___f_2318_, 2, v_inst_2308_);
lean_closure_set(v___f_2318_, 3, v_inst_2309_);
lean_closure_set(v___f_2318_, 4, v_toBind_2313_);
lean_closure_set(v___f_2318_, 5, v___f_2317_);
lean_closure_set(v___f_2318_, 6, v_modifyEnv_2315_);
lean_closure_set(v___f_2318_, 7, v___f_2316_);
v___x_2319_ = lean_apply_4(v_toBind_2313_, lean_box(0), lean_box(0), v_getEnv_2314_, v___f_2318_);
return v___x_2319_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag(lean_object* v_m_2320_, lean_object* v_inst_2321_, lean_object* v_inst_2322_, lean_object* v_inst_2323_, lean_object* v_attr_2324_, lean_object* v_decl_2325_){
_start:
{
lean_object* v___x_2326_; 
v___x_2326_ = l_Lean_TagAttribute_setTag___redArg(v_inst_2321_, v_inst_2322_, v_inst_2323_, v_attr_2324_, v_decl_2325_);
return v___x_2326_;
}
}
LEAN_EXPORT uint8_t l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___redArg(lean_object* v_as_2327_, lean_object* v_k_2328_, lean_object* v_x_2329_, lean_object* v_x_2330_){
_start:
{
lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v_m_2333_; lean_object* v_a_2334_; uint8_t v___x_2335_; 
v___x_2331_ = lean_nat_add(v_x_2329_, v_x_2330_);
v___x_2332_ = lean_unsigned_to_nat(1u);
v_m_2333_ = lean_nat_shiftr(v___x_2331_, v___x_2332_);
lean_dec(v___x_2331_);
v_a_2334_ = lean_array_fget_borrowed(v_as_2327_, v_m_2333_);
v___x_2335_ = l_Lean_Name_quickLt(v_a_2334_, v_k_2328_);
if (v___x_2335_ == 0)
{
uint8_t v___x_2336_; 
lean_dec(v_x_2330_);
v___x_2336_ = l_Lean_Name_quickLt(v_k_2328_, v_a_2334_);
if (v___x_2336_ == 0)
{
uint8_t v___x_2337_; 
lean_dec(v_m_2333_);
lean_dec(v_x_2329_);
v___x_2337_ = 1;
return v___x_2337_;
}
else
{
lean_object* v___x_2338_; uint8_t v___x_2339_; 
v___x_2338_ = lean_unsigned_to_nat(0u);
v___x_2339_ = lean_nat_dec_eq(v_m_2333_, v___x_2338_);
if (v___x_2339_ == 0)
{
lean_object* v___x_2340_; uint8_t v___x_2341_; 
v___x_2340_ = lean_nat_sub(v_m_2333_, v___x_2332_);
lean_dec(v_m_2333_);
v___x_2341_ = lean_nat_dec_lt(v___x_2340_, v_x_2329_);
if (v___x_2341_ == 0)
{
v_x_2330_ = v___x_2340_;
goto _start;
}
else
{
lean_dec(v___x_2340_);
lean_dec(v_x_2329_);
return v___x_2335_;
}
}
else
{
lean_dec(v_m_2333_);
lean_dec(v_x_2329_);
return v___x_2335_;
}
}
}
else
{
lean_object* v___x_2343_; uint8_t v___x_2344_; 
lean_dec(v_x_2329_);
v___x_2343_ = lean_nat_add(v_m_2333_, v___x_2332_);
lean_dec(v_m_2333_);
v___x_2344_ = lean_nat_dec_le(v___x_2343_, v_x_2330_);
if (v___x_2344_ == 0)
{
lean_dec(v___x_2343_);
lean_dec(v_x_2330_);
return v___x_2344_;
}
else
{
v_x_2329_ = v___x_2343_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___redArg___boxed(lean_object* v_as_2346_, lean_object* v_k_2347_, lean_object* v_x_2348_, lean_object* v_x_2349_){
_start:
{
uint8_t v_res_2350_; lean_object* v_r_2351_; 
v_res_2350_ = l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___redArg(v_as_2346_, v_k_2347_, v_x_2348_, v_x_2349_);
lean_dec(v_k_2347_);
lean_dec_ref(v_as_2346_);
v_r_2351_ = lean_box(v_res_2350_);
return v_r_2351_;
}
}
LEAN_EXPORT uint8_t l_Lean_TagAttribute_hasTag(lean_object* v_attr_2352_, lean_object* v_env_2353_, lean_object* v_decl_2354_){
_start:
{
lean_object* v___x_2355_; lean_object* v___x_2356_; 
v___x_2355_ = lean_box(1);
v___x_2356_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2353_, v_decl_2354_);
if (lean_obj_tag(v___x_2356_) == 0)
{
lean_object* v_ext_2357_; lean_object* v_toEnvExtension_2358_; lean_object* v_asyncMode_2359_; lean_object* v___x_2360_; uint8_t v___x_2361_; 
v_ext_2357_ = lean_ctor_get(v_attr_2352_, 1);
v_toEnvExtension_2358_ = lean_ctor_get(v_ext_2357_, 0);
v_asyncMode_2359_ = lean_ctor_get(v_toEnvExtension_2358_, 2);
lean_inc(v_decl_2354_);
v___x_2360_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2355_, v_ext_2357_, v_env_2353_, v_asyncMode_2359_, v_decl_2354_);
v___x_2361_ = l_Lean_NameSet_contains(v___x_2360_, v_decl_2354_);
lean_dec(v_decl_2354_);
lean_dec(v___x_2360_);
return v___x_2361_;
}
else
{
lean_object* v_val_2362_; lean_object* v_ext_2363_; uint8_t v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; uint8_t v___x_2368_; 
v_val_2362_ = lean_ctor_get(v___x_2356_, 0);
lean_inc(v_val_2362_);
lean_dec_ref_known(v___x_2356_, 1);
v_ext_2363_ = lean_ctor_get(v_attr_2352_, 1);
v___x_2364_ = 0;
v___x_2365_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_2355_, v_ext_2363_, v_env_2353_, v_val_2362_, v___x_2364_);
lean_dec(v_val_2362_);
lean_dec_ref(v_env_2353_);
v___x_2366_ = lean_unsigned_to_nat(0u);
v___x_2367_ = lean_array_get_size(v___x_2365_);
v___x_2368_ = lean_nat_dec_lt(v___x_2366_, v___x_2367_);
if (v___x_2368_ == 0)
{
lean_dec_ref(v___x_2365_);
lean_dec(v_decl_2354_);
return v___x_2368_;
}
else
{
lean_object* v___x_2369_; lean_object* v___x_2370_; uint8_t v___x_2371_; 
v___x_2369_ = lean_unsigned_to_nat(1u);
v___x_2370_ = lean_nat_sub(v___x_2367_, v___x_2369_);
v___x_2371_ = lean_nat_dec_le(v___x_2366_, v___x_2370_);
if (v___x_2371_ == 0)
{
lean_dec(v___x_2370_);
lean_dec_ref(v___x_2365_);
lean_dec(v_decl_2354_);
return v___x_2371_;
}
else
{
uint8_t v___x_2372_; 
v___x_2372_ = l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___redArg(v___x_2365_, v_decl_2354_, v___x_2366_, v___x_2370_);
lean_dec(v_decl_2354_);
lean_dec_ref(v___x_2365_);
return v___x_2372_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_hasTag___boxed(lean_object* v_attr_2373_, lean_object* v_env_2374_, lean_object* v_decl_2375_){
_start:
{
uint8_t v_res_2376_; lean_object* v_r_2377_; 
v_res_2376_ = l_Lean_TagAttribute_hasTag(v_attr_2373_, v_env_2374_, v_decl_2375_);
lean_dec_ref(v_attr_2373_);
v_r_2377_ = lean_box(v_res_2376_);
return v_r_2377_;
}
}
LEAN_EXPORT uint8_t l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0(lean_object* v_as_2378_, lean_object* v_k_2379_, lean_object* v_x_2380_, lean_object* v_x_2381_, lean_object* v_x_2382_){
_start:
{
uint8_t v___x_2383_; 
v___x_2383_ = l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___redArg(v_as_2378_, v_k_2379_, v_x_2380_, v_x_2381_);
return v___x_2383_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___boxed(lean_object* v_as_2384_, lean_object* v_k_2385_, lean_object* v_x_2386_, lean_object* v_x_2387_, lean_object* v_x_2388_){
_start:
{
uint8_t v_res_2389_; lean_object* v_r_2390_; 
v_res_2389_ = l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0(v_as_2384_, v_k_2385_, v_x_2386_, v_x_2387_, v_x_2388_);
lean_dec(v_k_2385_);
lean_dec_ref(v_as_2384_);
v_r_2390_ = lean_box(v_res_2389_);
return v_r_2390_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__0(lean_object* v_x_2391_, lean_object* v___y_2392_){
_start:
{
lean_object* v___x_2394_; lean_object* v___x_2395_; 
v___x_2394_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___lam__0___closed__1));
v___x_2395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2395_, 0, v___x_2394_);
return v___x_2395_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__0___boxed(lean_object* v_x_2396_, lean_object* v___y_2397_, lean_object* v___y_2398_){
_start:
{
lean_object* v_res_2399_; 
v_res_2399_ = l_Lean_instInhabitedParametricAttribute_default___lam__0(v_x_2396_, v___y_2397_);
lean_dec_ref(v___y_2397_);
lean_dec_ref(v_x_2396_);
return v_res_2399_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__1(lean_object* v_s_2400_, lean_object* v_x_2401_){
_start:
{
lean_inc_ref(v_s_2400_);
return v_s_2400_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__1___boxed(lean_object* v_s_2402_, lean_object* v_x_2403_){
_start:
{
lean_object* v_res_2404_; 
v_res_2404_ = l_Lean_instInhabitedParametricAttribute_default___lam__1(v_s_2402_, v_x_2403_);
lean_dec_ref(v_x_2403_);
lean_dec_ref(v_s_2402_);
return v_res_2404_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__2(lean_object* v_x_2409_, lean_object* v_x_2410_){
_start:
{
lean_object* v___x_2411_; 
v___x_2411_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___lam__2___closed__1));
return v___x_2411_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__2___boxed(lean_object* v_x_2412_, lean_object* v_x_2413_){
_start:
{
lean_object* v_res_2414_; 
v_res_2414_ = l_Lean_instInhabitedParametricAttribute_default___lam__2(v_x_2412_, v_x_2413_);
lean_dec_ref(v_x_2413_);
lean_dec_ref(v_x_2412_);
return v_res_2414_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__3(lean_object* v_x_2415_){
_start:
{
lean_object* v___x_2416_; 
v___x_2416_ = lean_box(0);
return v___x_2416_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__3___boxed(lean_object* v_x_2417_){
_start:
{
lean_object* v_res_2418_; 
v_res_2418_ = l_Lean_instInhabitedParametricAttribute_default___lam__3(v_x_2417_);
lean_dec_ref(v_x_2417_);
return v_res_2418_;
}
}
static lean_object* _init_l_Lean_instInhabitedParametricAttribute_default___closed__4(void){
_start:
{
lean_object* v___x_2423_; 
v___x_2423_ = l_Lean_instInhabitedEnvExtension_default(lean_box(0));
return v___x_2423_;
}
}
static lean_object* _init_l_Lean_instInhabitedParametricAttribute_default___closed__5(void){
_start:
{
lean_object* v___f_2424_; lean_object* v___f_2425_; lean_object* v___f_2426_; lean_object* v___f_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; lean_object* v___x_2430_; 
v___f_2424_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___closed__3));
v___f_2425_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___closed__2));
v___f_2426_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___closed__1));
v___f_2427_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___closed__0));
v___x_2428_ = lean_box(0);
v___x_2429_ = lean_obj_once(&l_Lean_instInhabitedParametricAttribute_default___closed__4, &l_Lean_instInhabitedParametricAttribute_default___closed__4_once, _init_l_Lean_instInhabitedParametricAttribute_default___closed__4);
v___x_2430_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2430_, 0, v___x_2429_);
lean_ctor_set(v___x_2430_, 1, v___x_2428_);
lean_ctor_set(v___x_2430_, 2, v___f_2427_);
lean_ctor_set(v___x_2430_, 3, v___f_2426_);
lean_ctor_set(v___x_2430_, 4, v___f_2425_);
lean_ctor_set(v___x_2430_, 5, v___f_2424_);
return v___x_2430_;
}
}
static lean_object* _init_l_Lean_instInhabitedParametricAttribute_default___closed__6(void){
_start:
{
uint8_t v___x_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; 
v___x_2431_ = 0;
v___x_2432_ = lean_obj_once(&l_Lean_instInhabitedParametricAttribute_default___closed__5, &l_Lean_instInhabitedParametricAttribute_default___closed__5_once, _init_l_Lean_instInhabitedParametricAttribute_default___closed__5);
v___x_2433_ = ((lean_object*)(l_Lean_instInhabitedAttributeImpl_default));
v___x_2434_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2434_, 0, v___x_2433_);
lean_ctor_set(v___x_2434_, 1, v___x_2432_);
lean_ctor_set_uint8(v___x_2434_, sizeof(void*)*2, v___x_2431_);
return v___x_2434_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default(lean_object* v_00_u03b1_2435_){
_start:
{
lean_object* v___x_2436_; 
v___x_2436_ = lean_obj_once(&l_Lean_instInhabitedParametricAttribute_default___closed__6, &l_Lean_instInhabitedParametricAttribute_default___closed__6_once, _init_l_Lean_instInhabitedParametricAttribute_default___closed__6);
return v___x_2436_;
}
}
static lean_object* _init_l_Lean_instInhabitedParametricAttribute___closed__0(void){
_start:
{
lean_object* v___x_2437_; 
v___x_2437_ = l_Lean_instInhabitedParametricAttribute_default(lean_box(0));
return v___x_2437_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute(lean_object* v_a_2438_){
_start:
{
lean_object* v___x_2439_; 
v___x_2439_ = lean_obj_once(&l_Lean_instInhabitedParametricAttribute___closed__0, &l_Lean_instInhabitedParametricAttribute___closed__0_once, _init_l_Lean_instInhabitedParametricAttribute___closed__0);
return v___x_2439_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_registerParametricAttribute_spec__4___redArg(lean_object* v_env_2440_, lean_object* v___y_2441_){
_start:
{
lean_object* v___x_2443_; lean_object* v_nextMacroScope_2444_; lean_object* v_ngen_2445_; lean_object* v_auxDeclNGen_2446_; lean_object* v_traceState_2447_; lean_object* v_messages_2448_; lean_object* v_infoState_2449_; lean_object* v_snapshotTasks_2450_; lean_object* v___x_2452_; uint8_t v_isShared_2453_; uint8_t v_isSharedCheck_2461_; 
v___x_2443_ = lean_st_ref_take(v___y_2441_);
v_nextMacroScope_2444_ = lean_ctor_get(v___x_2443_, 1);
v_ngen_2445_ = lean_ctor_get(v___x_2443_, 2);
v_auxDeclNGen_2446_ = lean_ctor_get(v___x_2443_, 3);
v_traceState_2447_ = lean_ctor_get(v___x_2443_, 4);
v_messages_2448_ = lean_ctor_get(v___x_2443_, 6);
v_infoState_2449_ = lean_ctor_get(v___x_2443_, 7);
v_snapshotTasks_2450_ = lean_ctor_get(v___x_2443_, 8);
v_isSharedCheck_2461_ = !lean_is_exclusive(v___x_2443_);
if (v_isSharedCheck_2461_ == 0)
{
lean_object* v_unused_2462_; lean_object* v_unused_2463_; 
v_unused_2462_ = lean_ctor_get(v___x_2443_, 5);
lean_dec(v_unused_2462_);
v_unused_2463_ = lean_ctor_get(v___x_2443_, 0);
lean_dec(v_unused_2463_);
v___x_2452_ = v___x_2443_;
v_isShared_2453_ = v_isSharedCheck_2461_;
goto v_resetjp_2451_;
}
else
{
lean_inc(v_snapshotTasks_2450_);
lean_inc(v_infoState_2449_);
lean_inc(v_messages_2448_);
lean_inc(v_traceState_2447_);
lean_inc(v_auxDeclNGen_2446_);
lean_inc(v_ngen_2445_);
lean_inc(v_nextMacroScope_2444_);
lean_dec(v___x_2443_);
v___x_2452_ = lean_box(0);
v_isShared_2453_ = v_isSharedCheck_2461_;
goto v_resetjp_2451_;
}
v_resetjp_2451_:
{
lean_object* v___x_2454_; lean_object* v___x_2456_; 
v___x_2454_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2);
if (v_isShared_2453_ == 0)
{
lean_ctor_set(v___x_2452_, 5, v___x_2454_);
lean_ctor_set(v___x_2452_, 0, v_env_2440_);
v___x_2456_ = v___x_2452_;
goto v_reusejp_2455_;
}
else
{
lean_object* v_reuseFailAlloc_2460_; 
v_reuseFailAlloc_2460_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2460_, 0, v_env_2440_);
lean_ctor_set(v_reuseFailAlloc_2460_, 1, v_nextMacroScope_2444_);
lean_ctor_set(v_reuseFailAlloc_2460_, 2, v_ngen_2445_);
lean_ctor_set(v_reuseFailAlloc_2460_, 3, v_auxDeclNGen_2446_);
lean_ctor_set(v_reuseFailAlloc_2460_, 4, v_traceState_2447_);
lean_ctor_set(v_reuseFailAlloc_2460_, 5, v___x_2454_);
lean_ctor_set(v_reuseFailAlloc_2460_, 6, v_messages_2448_);
lean_ctor_set(v_reuseFailAlloc_2460_, 7, v_infoState_2449_);
lean_ctor_set(v_reuseFailAlloc_2460_, 8, v_snapshotTasks_2450_);
v___x_2456_ = v_reuseFailAlloc_2460_;
goto v_reusejp_2455_;
}
v_reusejp_2455_:
{
lean_object* v___x_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; 
v___x_2457_ = lean_st_ref_set(v___y_2441_, v___x_2456_);
v___x_2458_ = lean_box(0);
v___x_2459_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2459_, 0, v___x_2458_);
return v___x_2459_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_registerParametricAttribute_spec__4___redArg___boxed(lean_object* v_env_2464_, lean_object* v___y_2465_, lean_object* v___y_2466_){
_start:
{
lean_object* v_res_2467_; 
v_res_2467_ = l_Lean_setEnv___at___00Lean_registerParametricAttribute_spec__4___redArg(v_env_2464_, v___y_2465_);
lean_dec(v___y_2465_);
return v_res_2467_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_registerParametricAttribute_spec__4(lean_object* v_env_2468_, lean_object* v___y_2469_, lean_object* v___y_2470_){
_start:
{
lean_object* v___x_2472_; 
v___x_2472_ = l_Lean_setEnv___at___00Lean_registerParametricAttribute_spec__4___redArg(v_env_2468_, v___y_2470_);
return v___x_2472_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_registerParametricAttribute_spec__4___boxed(lean_object* v_env_2473_, lean_object* v___y_2474_, lean_object* v___y_2475_, lean_object* v___y_2476_){
_start:
{
lean_object* v_res_2477_; 
v_res_2477_ = l_Lean_setEnv___at___00Lean_registerParametricAttribute_spec__4(v_env_2473_, v___y_2474_, v___y_2475_);
lean_dec(v___y_2475_);
lean_dec_ref(v___y_2474_);
return v_res_2477_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___lam__0(lean_object* v_x_2478_, lean_object* v_p_2479_){
_start:
{
lean_object* v_fst_2480_; lean_object* v_snd_2481_; lean_object* v___x_2483_; uint8_t v_isShared_2484_; uint8_t v_isSharedCheck_2498_; 
v_fst_2480_ = lean_ctor_get(v_x_2478_, 0);
v_snd_2481_ = lean_ctor_get(v_x_2478_, 1);
v_isSharedCheck_2498_ = !lean_is_exclusive(v_x_2478_);
if (v_isSharedCheck_2498_ == 0)
{
v___x_2483_ = v_x_2478_;
v_isShared_2484_ = v_isSharedCheck_2498_;
goto v_resetjp_2482_;
}
else
{
lean_inc(v_snd_2481_);
lean_inc(v_fst_2480_);
lean_dec(v_x_2478_);
v___x_2483_ = lean_box(0);
v_isShared_2484_ = v_isSharedCheck_2498_;
goto v_resetjp_2482_;
}
v_resetjp_2482_:
{
lean_object* v_fst_2485_; lean_object* v_snd_2486_; lean_object* v___x_2488_; uint8_t v_isShared_2489_; uint8_t v_isSharedCheck_2497_; 
v_fst_2485_ = lean_ctor_get(v_p_2479_, 0);
v_snd_2486_ = lean_ctor_get(v_p_2479_, 1);
v_isSharedCheck_2497_ = !lean_is_exclusive(v_p_2479_);
if (v_isSharedCheck_2497_ == 0)
{
v___x_2488_ = v_p_2479_;
v_isShared_2489_ = v_isSharedCheck_2497_;
goto v_resetjp_2487_;
}
else
{
lean_inc(v_snd_2486_);
lean_inc(v_fst_2485_);
lean_dec(v_p_2479_);
v___x_2488_ = lean_box(0);
v_isShared_2489_ = v_isSharedCheck_2497_;
goto v_resetjp_2487_;
}
v_resetjp_2487_:
{
lean_object* v___x_2491_; 
lean_inc(v_fst_2485_);
if (v_isShared_2484_ == 0)
{
lean_ctor_set_tag(v___x_2483_, 1);
lean_ctor_set(v___x_2483_, 1, v_fst_2480_);
lean_ctor_set(v___x_2483_, 0, v_fst_2485_);
v___x_2491_ = v___x_2483_;
goto v_reusejp_2490_;
}
else
{
lean_object* v_reuseFailAlloc_2496_; 
v_reuseFailAlloc_2496_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2496_, 0, v_fst_2485_);
lean_ctor_set(v_reuseFailAlloc_2496_, 1, v_fst_2480_);
v___x_2491_ = v_reuseFailAlloc_2496_;
goto v_reusejp_2490_;
}
v_reusejp_2490_:
{
lean_object* v___x_2492_; lean_object* v___x_2494_; 
v___x_2492_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_2485_, v_snd_2486_, v_snd_2481_);
if (v_isShared_2489_ == 0)
{
lean_ctor_set(v___x_2488_, 1, v___x_2492_);
lean_ctor_set(v___x_2488_, 0, v___x_2491_);
v___x_2494_ = v___x_2488_;
goto v_reusejp_2493_;
}
else
{
lean_object* v_reuseFailAlloc_2495_; 
v_reuseFailAlloc_2495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2495_, 0, v___x_2491_);
lean_ctor_set(v_reuseFailAlloc_2495_, 1, v___x_2492_);
v___x_2494_ = v_reuseFailAlloc_2495_;
goto v_reusejp_2493_;
}
v_reusejp_2493_:
{
return v___x_2494_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1_spec__1___redArg(lean_object* v_init_2499_, lean_object* v_x_2500_){
_start:
{
if (lean_obj_tag(v_x_2500_) == 0)
{
lean_object* v_k_2501_; lean_object* v_v_2502_; lean_object* v_l_2503_; lean_object* v_r_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; 
v_k_2501_ = lean_ctor_get(v_x_2500_, 1);
v_v_2502_ = lean_ctor_get(v_x_2500_, 2);
v_l_2503_ = lean_ctor_get(v_x_2500_, 3);
v_r_2504_ = lean_ctor_get(v_x_2500_, 4);
v___x_2505_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1_spec__1___redArg(v_init_2499_, v_l_2503_);
lean_inc(v_v_2502_);
lean_inc(v_k_2501_);
v___x_2506_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2506_, 0, v_k_2501_);
lean_ctor_set(v___x_2506_, 1, v_v_2502_);
v___x_2507_ = lean_array_push(v___x_2505_, v___x_2506_);
v_init_2499_ = v___x_2507_;
v_x_2500_ = v_r_2504_;
goto _start;
}
else
{
return v_init_2499_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1_spec__1___redArg___boxed(lean_object* v_init_2509_, lean_object* v_x_2510_){
_start:
{
lean_object* v_res_2511_; 
v_res_2511_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1_spec__1___redArg(v_init_2509_, v_x_2510_);
lean_dec(v_x_2510_);
return v_res_2511_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2_spec__3___redArg(lean_object* v_hi_2512_, lean_object* v_pivot_2513_, lean_object* v_as_2514_, lean_object* v_i_2515_, lean_object* v_k_2516_){
_start:
{
uint8_t v___x_2517_; 
v___x_2517_ = lean_nat_dec_lt(v_k_2516_, v_hi_2512_);
if (v___x_2517_ == 0)
{
lean_object* v___x_2518_; lean_object* v___x_2519_; 
lean_dec(v_k_2516_);
v___x_2518_ = lean_array_fswap(v_as_2514_, v_i_2515_, v_hi_2512_);
v___x_2519_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2519_, 0, v_i_2515_);
lean_ctor_set(v___x_2519_, 1, v___x_2518_);
return v___x_2519_;
}
else
{
lean_object* v___x_2520_; lean_object* v_fst_2521_; lean_object* v_fst_2522_; uint8_t v___x_2523_; 
v___x_2520_ = lean_array_fget_borrowed(v_as_2514_, v_k_2516_);
v_fst_2521_ = lean_ctor_get(v___x_2520_, 0);
v_fst_2522_ = lean_ctor_get(v_pivot_2513_, 0);
v___x_2523_ = l_Lean_Name_quickLt(v_fst_2521_, v_fst_2522_);
if (v___x_2523_ == 0)
{
lean_object* v___x_2524_; lean_object* v___x_2525_; 
v___x_2524_ = lean_unsigned_to_nat(1u);
v___x_2525_ = lean_nat_add(v_k_2516_, v___x_2524_);
lean_dec(v_k_2516_);
v_k_2516_ = v___x_2525_;
goto _start;
}
else
{
lean_object* v___x_2527_; lean_object* v___x_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; 
v___x_2527_ = lean_array_fswap(v_as_2514_, v_i_2515_, v_k_2516_);
v___x_2528_ = lean_unsigned_to_nat(1u);
v___x_2529_ = lean_nat_add(v_i_2515_, v___x_2528_);
lean_dec(v_i_2515_);
v___x_2530_ = lean_nat_add(v_k_2516_, v___x_2528_);
lean_dec(v_k_2516_);
v_as_2514_ = v___x_2527_;
v_i_2515_ = v___x_2529_;
v_k_2516_ = v___x_2530_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2_spec__3___redArg___boxed(lean_object* v_hi_2532_, lean_object* v_pivot_2533_, lean_object* v_as_2534_, lean_object* v_i_2535_, lean_object* v_k_2536_){
_start:
{
lean_object* v_res_2537_; 
v_res_2537_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2_spec__3___redArg(v_hi_2532_, v_pivot_2533_, v_as_2534_, v_i_2535_, v_k_2536_);
lean_dec_ref(v_pivot_2533_);
lean_dec(v_hi_2532_);
return v_res_2537_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2___redArg___lam__0(lean_object* v_a_2538_, lean_object* v_b_2539_){
_start:
{
lean_object* v_fst_2540_; lean_object* v_fst_2541_; uint8_t v___x_2542_; 
v_fst_2540_ = lean_ctor_get(v_a_2538_, 0);
v_fst_2541_ = lean_ctor_get(v_b_2539_, 0);
v___x_2542_ = l_Lean_Name_quickLt(v_fst_2540_, v_fst_2541_);
return v___x_2542_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2___redArg___lam__0___boxed(lean_object* v_a_2543_, lean_object* v_b_2544_){
_start:
{
uint8_t v_res_2545_; lean_object* v_r_2546_; 
v_res_2545_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2___redArg___lam__0(v_a_2543_, v_b_2544_);
lean_dec_ref(v_b_2544_);
lean_dec_ref(v_a_2543_);
v_r_2546_ = lean_box(v_res_2545_);
return v_r_2546_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2___redArg(lean_object* v_n_2547_, lean_object* v_as_2548_, lean_object* v_lo_2549_, lean_object* v_hi_2550_){
_start:
{
lean_object* v___y_2552_; uint8_t v___x_2562_; 
v___x_2562_ = lean_nat_dec_lt(v_lo_2549_, v_hi_2550_);
if (v___x_2562_ == 0)
{
lean_dec(v_lo_2549_);
return v_as_2548_;
}
else
{
lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v_mid_2565_; lean_object* v___y_2567_; lean_object* v___y_2573_; lean_object* v___x_2578_; lean_object* v___x_2579_; uint8_t v___x_2580_; 
v___x_2563_ = lean_nat_add(v_lo_2549_, v_hi_2550_);
v___x_2564_ = lean_unsigned_to_nat(1u);
v_mid_2565_ = lean_nat_shiftr(v___x_2563_, v___x_2564_);
lean_dec(v___x_2563_);
v___x_2578_ = lean_array_fget_borrowed(v_as_2548_, v_mid_2565_);
v___x_2579_ = lean_array_fget_borrowed(v_as_2548_, v_lo_2549_);
v___x_2580_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2___redArg___lam__0(v___x_2578_, v___x_2579_);
if (v___x_2580_ == 0)
{
v___y_2573_ = v_as_2548_;
goto v___jp_2572_;
}
else
{
lean_object* v___x_2581_; 
v___x_2581_ = lean_array_fswap(v_as_2548_, v_lo_2549_, v_mid_2565_);
v___y_2573_ = v___x_2581_;
goto v___jp_2572_;
}
v___jp_2566_:
{
lean_object* v___x_2568_; lean_object* v___x_2569_; uint8_t v___x_2570_; 
v___x_2568_ = lean_array_fget_borrowed(v___y_2567_, v_mid_2565_);
v___x_2569_ = lean_array_fget_borrowed(v___y_2567_, v_hi_2550_);
v___x_2570_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2___redArg___lam__0(v___x_2568_, v___x_2569_);
if (v___x_2570_ == 0)
{
lean_dec(v_mid_2565_);
v___y_2552_ = v___y_2567_;
goto v___jp_2551_;
}
else
{
lean_object* v___x_2571_; 
v___x_2571_ = lean_array_fswap(v___y_2567_, v_mid_2565_, v_hi_2550_);
lean_dec(v_mid_2565_);
v___y_2552_ = v___x_2571_;
goto v___jp_2551_;
}
}
v___jp_2572_:
{
lean_object* v___x_2574_; lean_object* v___x_2575_; uint8_t v___x_2576_; 
v___x_2574_ = lean_array_fget_borrowed(v___y_2573_, v_hi_2550_);
v___x_2575_ = lean_array_fget_borrowed(v___y_2573_, v_lo_2549_);
v___x_2576_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2___redArg___lam__0(v___x_2574_, v___x_2575_);
if (v___x_2576_ == 0)
{
v___y_2567_ = v___y_2573_;
goto v___jp_2566_;
}
else
{
lean_object* v___x_2577_; 
v___x_2577_ = lean_array_fswap(v___y_2573_, v_lo_2549_, v_hi_2550_);
v___y_2567_ = v___x_2577_;
goto v___jp_2566_;
}
}
}
v___jp_2551_:
{
lean_object* v_pivot_2553_; lean_object* v___x_2554_; lean_object* v_fst_2555_; lean_object* v_snd_2556_; uint8_t v___x_2557_; 
v_pivot_2553_ = lean_array_fget(v___y_2552_, v_hi_2550_);
lean_inc_n(v_lo_2549_, 2);
v___x_2554_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2_spec__3___redArg(v_hi_2550_, v_pivot_2553_, v___y_2552_, v_lo_2549_, v_lo_2549_);
lean_dec(v_pivot_2553_);
v_fst_2555_ = lean_ctor_get(v___x_2554_, 0);
lean_inc(v_fst_2555_);
v_snd_2556_ = lean_ctor_get(v___x_2554_, 1);
lean_inc(v_snd_2556_);
lean_dec_ref(v___x_2554_);
v___x_2557_ = lean_nat_dec_le(v_hi_2550_, v_fst_2555_);
if (v___x_2557_ == 0)
{
lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; 
v___x_2558_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2___redArg(v_n_2547_, v_snd_2556_, v_lo_2549_, v_fst_2555_);
v___x_2559_ = lean_unsigned_to_nat(1u);
v___x_2560_ = lean_nat_add(v_fst_2555_, v___x_2559_);
lean_dec(v_fst_2555_);
v_as_2548_ = v___x_2558_;
v_lo_2549_ = v___x_2560_;
goto _start;
}
else
{
lean_dec(v_fst_2555_);
lean_dec(v_lo_2549_);
return v_snd_2556_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2___redArg___boxed(lean_object* v_n_2582_, lean_object* v_as_2583_, lean_object* v_lo_2584_, lean_object* v_hi_2585_){
_start:
{
lean_object* v_res_2586_; 
v_res_2586_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2___redArg(v_n_2582_, v_as_2583_, v_lo_2584_, v_hi_2585_);
lean_dec(v_hi_2585_);
lean_dec(v_n_2582_);
return v_res_2586_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3_spec__5___redArg(lean_object* v_snd_2587_, lean_object* v_as_2588_, size_t v_i_2589_, size_t v_stop_2590_, lean_object* v_b_2591_){
_start:
{
lean_object* v___y_2593_; uint8_t v___x_2597_; 
v___x_2597_ = lean_usize_dec_eq(v_i_2589_, v_stop_2590_);
if (v___x_2597_ == 0)
{
lean_object* v___x_2598_; lean_object* v___x_2599_; 
v___x_2598_ = lean_array_uget_borrowed(v_as_2588_, v_i_2589_);
v___x_2599_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_snd_2587_, v___x_2598_);
if (lean_obj_tag(v___x_2599_) == 0)
{
v___y_2593_ = v_b_2591_;
goto v___jp_2592_;
}
else
{
lean_object* v_val_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; 
v_val_2600_ = lean_ctor_get(v___x_2599_, 0);
lean_inc(v_val_2600_);
lean_dec_ref_known(v___x_2599_, 1);
lean_inc(v___x_2598_);
v___x_2601_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2601_, 0, v___x_2598_);
lean_ctor_set(v___x_2601_, 1, v_val_2600_);
v___x_2602_ = lean_array_push(v_b_2591_, v___x_2601_);
v___y_2593_ = v___x_2602_;
goto v___jp_2592_;
}
}
else
{
return v_b_2591_;
}
v___jp_2592_:
{
size_t v___x_2594_; size_t v___x_2595_; 
v___x_2594_ = ((size_t)1ULL);
v___x_2595_ = lean_usize_add(v_i_2589_, v___x_2594_);
v_i_2589_ = v___x_2595_;
v_b_2591_ = v___y_2593_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3_spec__5___redArg___boxed(lean_object* v_snd_2603_, lean_object* v_as_2604_, lean_object* v_i_2605_, lean_object* v_stop_2606_, lean_object* v_b_2607_){
_start:
{
size_t v_i_boxed_2608_; size_t v_stop_boxed_2609_; lean_object* v_res_2610_; 
v_i_boxed_2608_ = lean_unbox_usize(v_i_2605_);
lean_dec(v_i_2605_);
v_stop_boxed_2609_ = lean_unbox_usize(v_stop_2606_);
lean_dec(v_stop_2606_);
v_res_2610_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3_spec__5___redArg(v_snd_2603_, v_as_2604_, v_i_boxed_2608_, v_stop_boxed_2609_, v_b_2607_);
lean_dec_ref(v_as_2604_);
lean_dec(v_snd_2603_);
return v_res_2610_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3___redArg(lean_object* v_snd_2611_, lean_object* v_as_2612_, lean_object* v_start_2613_, lean_object* v_stop_2614_){
_start:
{
lean_object* v___x_2615_; uint8_t v___x_2616_; 
v___x_2615_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___lam__2___closed__0));
v___x_2616_ = lean_nat_dec_lt(v_start_2613_, v_stop_2614_);
if (v___x_2616_ == 0)
{
return v___x_2615_;
}
else
{
lean_object* v___x_2617_; uint8_t v___x_2618_; 
v___x_2617_ = lean_array_get_size(v_as_2612_);
v___x_2618_ = lean_nat_dec_le(v_stop_2614_, v___x_2617_);
if (v___x_2618_ == 0)
{
uint8_t v___x_2619_; 
v___x_2619_ = lean_nat_dec_lt(v_start_2613_, v___x_2617_);
if (v___x_2619_ == 0)
{
return v___x_2615_;
}
else
{
size_t v___x_2620_; size_t v___x_2621_; lean_object* v___x_2622_; 
v___x_2620_ = lean_usize_of_nat(v_start_2613_);
v___x_2621_ = lean_usize_of_nat(v___x_2617_);
v___x_2622_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3_spec__5___redArg(v_snd_2611_, v_as_2612_, v___x_2620_, v___x_2621_, v___x_2615_);
return v___x_2622_;
}
}
else
{
size_t v___x_2623_; size_t v___x_2624_; lean_object* v___x_2625_; 
v___x_2623_ = lean_usize_of_nat(v_start_2613_);
v___x_2624_ = lean_usize_of_nat(v_stop_2614_);
v___x_2625_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3_spec__5___redArg(v_snd_2611_, v_as_2612_, v___x_2623_, v___x_2624_, v___x_2615_);
return v___x_2625_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3___redArg___boxed(lean_object* v_snd_2626_, lean_object* v_as_2627_, lean_object* v_start_2628_, lean_object* v_stop_2629_){
_start:
{
lean_object* v_res_2630_; 
v_res_2630_ = l_Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3___redArg(v_snd_2626_, v_as_2627_, v_start_2628_, v_stop_2629_);
lean_dec(v_stop_2629_);
lean_dec(v_start_2628_);
lean_dec_ref(v_as_2627_);
lean_dec(v_snd_2626_);
return v_res_2630_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttribute_spec__0___redArg(lean_object* v_impl_2631_, lean_object* v_env_2632_, lean_object* v_as_2633_, size_t v_i_2634_, size_t v_stop_2635_, lean_object* v_b_2636_){
_start:
{
lean_object* v___y_2638_; uint8_t v___x_2642_; 
v___x_2642_ = lean_usize_dec_eq(v_i_2634_, v_stop_2635_);
if (v___x_2642_ == 0)
{
lean_object* v___x_2643_; lean_object* v_fst_2644_; lean_object* v_snd_2645_; lean_object* v_filterExport_2646_; lean_object* v___x_2647_; uint8_t v___x_2648_; 
v___x_2643_ = lean_array_uget_borrowed(v_as_2633_, v_i_2634_);
v_fst_2644_ = lean_ctor_get(v___x_2643_, 0);
v_snd_2645_ = lean_ctor_get(v___x_2643_, 1);
v_filterExport_2646_ = lean_ctor_get(v_impl_2631_, 3);
lean_inc_ref(v_filterExport_2646_);
lean_inc(v_snd_2645_);
lean_inc(v_fst_2644_);
lean_inc_ref(v_env_2632_);
v___x_2647_ = lean_apply_3(v_filterExport_2646_, v_env_2632_, v_fst_2644_, v_snd_2645_);
v___x_2648_ = lean_unbox(v___x_2647_);
if (v___x_2648_ == 0)
{
v___y_2638_ = v_b_2636_;
goto v___jp_2637_;
}
else
{
lean_object* v___x_2649_; 
lean_inc(v___x_2643_);
v___x_2649_ = lean_array_push(v_b_2636_, v___x_2643_);
v___y_2638_ = v___x_2649_;
goto v___jp_2637_;
}
}
else
{
lean_dec_ref(v_env_2632_);
lean_dec_ref(v_impl_2631_);
return v_b_2636_;
}
v___jp_2637_:
{
size_t v___x_2639_; size_t v___x_2640_; 
v___x_2639_ = ((size_t)1ULL);
v___x_2640_ = lean_usize_add(v_i_2634_, v___x_2639_);
v_i_2634_ = v___x_2640_;
v_b_2636_ = v___y_2638_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttribute_spec__0___redArg___boxed(lean_object* v_impl_2650_, lean_object* v_env_2651_, lean_object* v_as_2652_, lean_object* v_i_2653_, lean_object* v_stop_2654_, lean_object* v_b_2655_){
_start:
{
size_t v_i_boxed_2656_; size_t v_stop_boxed_2657_; lean_object* v_res_2658_; 
v_i_boxed_2656_ = lean_unbox_usize(v_i_2653_);
lean_dec(v_i_2653_);
v_stop_boxed_2657_ = lean_unbox_usize(v_stop_2654_);
lean_dec(v_stop_2654_);
v_res_2658_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttribute_spec__0___redArg(v_impl_2650_, v_env_2651_, v_as_2652_, v_i_boxed_2656_, v_stop_boxed_2657_, v_b_2655_);
lean_dec_ref(v_as_2652_);
return v_res_2658_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___lam__1(lean_object* v_impl_2659_, uint8_t v_preserveOrder_2660_, lean_object* v_env_2661_, lean_object* v_x_2662_){
_start:
{
lean_object* v___y_2664_; 
if (v_preserveOrder_2660_ == 0)
{
lean_object* v_snd_2680_; lean_object* v___x_2681_; lean_object* v___x_2682_; lean_object* v_r_2683_; lean_object* v___x_2684_; lean_object* v___y_2686_; lean_object* v___y_2687_; uint8_t v___x_2689_; 
v_snd_2680_ = lean_ctor_get(v_x_2662_, 1);
lean_inc(v_snd_2680_);
lean_dec_ref(v_x_2662_);
v___x_2681_ = lean_unsigned_to_nat(0u);
v___x_2682_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___lam__2___closed__0));
v_r_2683_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1_spec__1___redArg(v___x_2682_, v_snd_2680_);
lean_dec(v_snd_2680_);
v___x_2684_ = lean_array_get_size(v_r_2683_);
v___x_2689_ = lean_nat_dec_eq(v___x_2684_, v___x_2681_);
if (v___x_2689_ == 0)
{
lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v___y_2693_; uint8_t v___x_2695_; 
v___x_2690_ = lean_unsigned_to_nat(1u);
v___x_2691_ = lean_nat_sub(v___x_2684_, v___x_2690_);
v___x_2695_ = lean_nat_dec_le(v___x_2681_, v___x_2691_);
if (v___x_2695_ == 0)
{
lean_inc(v___x_2691_);
v___y_2693_ = v___x_2691_;
goto v___jp_2692_;
}
else
{
v___y_2693_ = v___x_2681_;
goto v___jp_2692_;
}
v___jp_2692_:
{
uint8_t v___x_2694_; 
v___x_2694_ = lean_nat_dec_le(v___y_2693_, v___x_2691_);
if (v___x_2694_ == 0)
{
lean_dec(v___x_2691_);
lean_inc(v___y_2693_);
v___y_2686_ = v___y_2693_;
v___y_2687_ = v___y_2693_;
goto v___jp_2685_;
}
else
{
v___y_2686_ = v___y_2693_;
v___y_2687_ = v___x_2691_;
goto v___jp_2685_;
}
}
}
else
{
v___y_2664_ = v_r_2683_;
goto v___jp_2663_;
}
v___jp_2685_:
{
lean_object* v___x_2688_; 
v___x_2688_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2___redArg(v___x_2684_, v_r_2683_, v___y_2686_, v___y_2687_);
lean_dec(v___y_2687_);
v___y_2664_ = v___x_2688_;
goto v___jp_2663_;
}
}
else
{
lean_object* v_fst_2696_; lean_object* v_snd_2697_; lean_object* v___x_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; 
v_fst_2696_ = lean_ctor_get(v_x_2662_, 0);
lean_inc(v_fst_2696_);
v_snd_2697_ = lean_ctor_get(v_x_2662_, 1);
lean_inc(v_snd_2697_);
lean_dec_ref(v_x_2662_);
v___x_2698_ = lean_array_mk(v_fst_2696_);
v___x_2699_ = l_Array_reverse___redArg(v___x_2698_);
v___x_2700_ = lean_unsigned_to_nat(0u);
v___x_2701_ = lean_array_get_size(v___x_2699_);
v___x_2702_ = l_Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3___redArg(v_snd_2697_, v___x_2699_, v___x_2700_, v___x_2701_);
lean_dec_ref(v___x_2699_);
lean_dec(v_snd_2697_);
v___y_2664_ = v___x_2702_;
goto v___jp_2663_;
}
v___jp_2663_:
{
lean_object* v___x_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; uint8_t v___x_2668_; 
v___x_2665_ = lean_unsigned_to_nat(0u);
v___x_2666_ = lean_array_get_size(v___y_2664_);
v___x_2667_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___lam__2___closed__0));
v___x_2668_ = lean_nat_dec_lt(v___x_2665_, v___x_2666_);
if (v___x_2668_ == 0)
{
lean_object* v___x_2669_; 
lean_dec_ref(v_env_2661_);
lean_dec_ref(v_impl_2659_);
v___x_2669_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2669_, 0, v___x_2667_);
lean_ctor_set(v___x_2669_, 1, v___x_2667_);
lean_ctor_set(v___x_2669_, 2, v___y_2664_);
return v___x_2669_;
}
else
{
uint8_t v___x_2670_; 
v___x_2670_ = lean_nat_dec_le(v___x_2666_, v___x_2666_);
if (v___x_2670_ == 0)
{
if (v___x_2668_ == 0)
{
lean_object* v___x_2671_; 
lean_dec_ref(v_env_2661_);
lean_dec_ref(v_impl_2659_);
v___x_2671_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2671_, 0, v___x_2667_);
lean_ctor_set(v___x_2671_, 1, v___x_2667_);
lean_ctor_set(v___x_2671_, 2, v___y_2664_);
return v___x_2671_;
}
else
{
size_t v___x_2672_; size_t v___x_2673_; lean_object* v___x_2674_; lean_object* v___x_2675_; 
v___x_2672_ = ((size_t)0ULL);
v___x_2673_ = lean_usize_of_nat(v___x_2666_);
v___x_2674_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttribute_spec__0___redArg(v_impl_2659_, v_env_2661_, v___y_2664_, v___x_2672_, v___x_2673_, v___x_2667_);
lean_inc_ref(v___x_2674_);
v___x_2675_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2675_, 0, v___x_2674_);
lean_ctor_set(v___x_2675_, 1, v___x_2674_);
lean_ctor_set(v___x_2675_, 2, v___y_2664_);
return v___x_2675_;
}
}
else
{
size_t v___x_2676_; size_t v___x_2677_; lean_object* v___x_2678_; lean_object* v___x_2679_; 
v___x_2676_ = ((size_t)0ULL);
v___x_2677_ = lean_usize_of_nat(v___x_2666_);
v___x_2678_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttribute_spec__0___redArg(v_impl_2659_, v_env_2661_, v___y_2664_, v___x_2676_, v___x_2677_, v___x_2667_);
lean_inc_ref(v___x_2678_);
v___x_2679_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2679_, 0, v___x_2678_);
lean_ctor_set(v___x_2679_, 1, v___x_2678_);
lean_ctor_set(v___x_2679_, 2, v___y_2664_);
return v___x_2679_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___lam__1___boxed(lean_object* v_impl_2703_, lean_object* v_preserveOrder_2704_, lean_object* v_env_2705_, lean_object* v_x_2706_){
_start:
{
uint8_t v_preserveOrder_boxed_2707_; lean_object* v_res_2708_; 
v_preserveOrder_boxed_2707_ = lean_unbox(v_preserveOrder_2704_);
v_res_2708_ = l_Lean_registerParametricAttribute___redArg___lam__1(v_impl_2703_, v_preserveOrder_boxed_2707_, v_env_2705_, v_x_2706_);
return v_res_2708_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___lam__2(lean_object* v_x_2718_){
_start:
{
lean_object* v_snd_2719_; lean_object* v___x_2721_; uint8_t v_isShared_2722_; uint8_t v_isSharedCheck_2733_; 
v_snd_2719_ = lean_ctor_get(v_x_2718_, 1);
v_isSharedCheck_2733_ = !lean_is_exclusive(v_x_2718_);
if (v_isSharedCheck_2733_ == 0)
{
lean_object* v_unused_2734_; 
v_unused_2734_ = lean_ctor_get(v_x_2718_, 0);
lean_dec(v_unused_2734_);
v___x_2721_ = v_x_2718_;
v_isShared_2722_ = v_isSharedCheck_2733_;
goto v_resetjp_2720_;
}
else
{
lean_inc(v_snd_2719_);
lean_dec(v_x_2718_);
v___x_2721_ = lean_box(0);
v_isShared_2722_ = v_isSharedCheck_2733_;
goto v_resetjp_2720_;
}
v_resetjp_2720_:
{
lean_object* v___x_2723_; lean_object* v___y_2725_; 
v___x_2723_ = ((lean_object*)(l_Lean_registerParametricAttribute___redArg___lam__2___closed__3));
if (lean_obj_tag(v_snd_2719_) == 0)
{
lean_object* v_size_2731_; 
v_size_2731_ = lean_ctor_get(v_snd_2719_, 0);
lean_inc(v_size_2731_);
lean_dec_ref_known(v_snd_2719_, 5);
v___y_2725_ = v_size_2731_;
goto v___jp_2724_;
}
else
{
lean_object* v___x_2732_; 
v___x_2732_ = lean_unsigned_to_nat(0u);
v___y_2725_ = v___x_2732_;
goto v___jp_2724_;
}
v___jp_2724_:
{
lean_object* v___x_2726_; lean_object* v___x_2727_; lean_object* v___x_2729_; 
v___x_2726_ = l_Nat_reprFast(v___y_2725_);
v___x_2727_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2727_, 0, v___x_2726_);
if (v_isShared_2722_ == 0)
{
lean_ctor_set_tag(v___x_2721_, 5);
lean_ctor_set(v___x_2721_, 1, v___x_2727_);
lean_ctor_set(v___x_2721_, 0, v___x_2723_);
v___x_2729_ = v___x_2721_;
goto v_reusejp_2728_;
}
else
{
lean_object* v_reuseFailAlloc_2730_; 
v_reuseFailAlloc_2730_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2730_, 0, v___x_2723_);
lean_ctor_set(v_reuseFailAlloc_2730_, 1, v___x_2727_);
v___x_2729_ = v_reuseFailAlloc_2730_;
goto v_reusejp_2728_;
}
v_reusejp_2728_:
{
return v___x_2729_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___lam__3(lean_object* v_x_2735_){
_start:
{
lean_object* v___x_2736_; 
v___x_2736_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___lam__2___closed__0));
return v___x_2736_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___lam__3___boxed(lean_object* v_x_2737_){
_start:
{
lean_object* v_res_2738_; 
v_res_2738_ = l_Lean_registerParametricAttribute___redArg___lam__3(v_x_2737_);
lean_dec_ref(v_x_2737_);
return v_res_2738_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___lam__4(lean_object* v___x_2739_, lean_object* v_x_2740_, lean_object* v___y_2741_){
_start:
{
lean_object* v___x_2743_; 
v___x_2743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2743_, 0, v___x_2739_);
return v___x_2743_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___lam__4___boxed(lean_object* v___x_2744_, lean_object* v_x_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_){
_start:
{
lean_object* v_res_2748_; 
v_res_2748_ = l_Lean_registerParametricAttribute___redArg___lam__4(v___x_2744_, v_x_2745_, v___y_2746_);
lean_dec_ref(v___y_2746_);
lean_dec_ref(v_x_2745_);
return v_res_2748_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___lam__5(lean_object* v___x_2749_){
_start:
{
lean_object* v___x_2751_; 
v___x_2751_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2751_, 0, v___x_2749_);
return v___x_2751_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___lam__5___boxed(lean_object* v___x_2752_, lean_object* v___y_2753_){
_start:
{
lean_object* v_res_2754_; 
v_res_2754_ = l_Lean_registerParametricAttribute___redArg___lam__5(v___x_2752_);
return v_res_2754_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___lam__7(lean_object* v_getParam_2755_, lean_object* v_a_2756_, lean_object* v_afterSet_2757_, lean_object* v_name_2758_, lean_object* v_decl_2759_, lean_object* v_stx_2760_, uint8_t v_kind_2761_, lean_object* v___y_2762_, lean_object* v___y_2763_){
_start:
{
lean_object* v___y_2766_; lean_object* v___y_2767_; lean_object* v___y_2768_; lean_object* v___y_2769_; uint8_t v___y_2770_; lean_object* v___y_2773_; lean_object* v___y_2774_; lean_object* v___y_2775_; uint8_t v___x_2818_; uint8_t v___x_2819_; 
v___x_2818_ = 0;
v___x_2819_ = l_Lean_instBEqAttributeKind_beq(v_kind_2761_, v___x_2818_);
if (v___x_2819_ == 0)
{
lean_object* v___x_2820_; 
lean_dec(v_stx_2760_);
lean_dec(v_decl_2759_);
lean_dec_ref(v_afterSet_2757_);
lean_dec_ref(v_a_2756_);
lean_dec_ref(v_getParam_2755_);
v___x_2820_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg(v_name_2758_, v_kind_2761_, v___y_2762_, v___y_2763_);
return v___x_2820_;
}
else
{
goto v___jp_2813_;
}
v___jp_2765_:
{
if (v___y_2770_ == 0)
{
lean_object* v___x_2771_; 
lean_dec_ref(v___y_2768_);
v___x_2771_ = l_Lean_setEnv___at___00Lean_registerParametricAttribute_spec__4___redArg(v___y_2767_, v___y_2769_);
return v___x_2771_;
}
else
{
lean_dec_ref(v___y_2767_);
return v___y_2768_;
}
}
v___jp_2772_:
{
lean_object* v___x_2776_; 
lean_inc(v___y_2775_);
lean_inc_ref(v___y_2774_);
lean_inc(v_decl_2759_);
v___x_2776_ = lean_apply_5(v_getParam_2755_, v_decl_2759_, v_stx_2760_, v___y_2774_, v___y_2775_, lean_box(0));
if (lean_obj_tag(v___x_2776_) == 0)
{
lean_object* v_a_2777_; lean_object* v___x_2778_; lean_object* v_toEnvExtension_2779_; lean_object* v_env_2780_; lean_object* v_nextMacroScope_2781_; lean_object* v_ngen_2782_; lean_object* v_auxDeclNGen_2783_; lean_object* v_traceState_2784_; lean_object* v_messages_2785_; lean_object* v_infoState_2786_; lean_object* v_snapshotTasks_2787_; lean_object* v___x_2789_; uint8_t v_isShared_2790_; uint8_t v_isSharedCheck_2803_; 
v_a_2777_ = lean_ctor_get(v___x_2776_, 0);
lean_inc(v_a_2777_);
lean_dec_ref_known(v___x_2776_, 1);
v___x_2778_ = lean_st_ref_take(v___y_2775_);
v_toEnvExtension_2779_ = lean_ctor_get(v_a_2756_, 0);
v_env_2780_ = lean_ctor_get(v___x_2778_, 0);
v_nextMacroScope_2781_ = lean_ctor_get(v___x_2778_, 1);
v_ngen_2782_ = lean_ctor_get(v___x_2778_, 2);
v_auxDeclNGen_2783_ = lean_ctor_get(v___x_2778_, 3);
v_traceState_2784_ = lean_ctor_get(v___x_2778_, 4);
v_messages_2785_ = lean_ctor_get(v___x_2778_, 6);
v_infoState_2786_ = lean_ctor_get(v___x_2778_, 7);
v_snapshotTasks_2787_ = lean_ctor_get(v___x_2778_, 8);
v_isSharedCheck_2803_ = !lean_is_exclusive(v___x_2778_);
if (v_isSharedCheck_2803_ == 0)
{
lean_object* v_unused_2804_; 
v_unused_2804_ = lean_ctor_get(v___x_2778_, 5);
lean_dec(v_unused_2804_);
v___x_2789_ = v___x_2778_;
v_isShared_2790_ = v_isSharedCheck_2803_;
goto v_resetjp_2788_;
}
else
{
lean_inc(v_snapshotTasks_2787_);
lean_inc(v_infoState_2786_);
lean_inc(v_messages_2785_);
lean_inc(v_traceState_2784_);
lean_inc(v_auxDeclNGen_2783_);
lean_inc(v_ngen_2782_);
lean_inc(v_nextMacroScope_2781_);
lean_inc(v_env_2780_);
lean_dec(v___x_2778_);
v___x_2789_ = lean_box(0);
v_isShared_2790_ = v_isSharedCheck_2803_;
goto v_resetjp_2788_;
}
v_resetjp_2788_:
{
lean_object* v_asyncMode_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; lean_object* v___x_2794_; lean_object* v___x_2796_; 
v_asyncMode_2791_ = lean_ctor_get(v_toEnvExtension_2779_, 2);
lean_inc(v_asyncMode_2791_);
lean_inc(v_a_2777_);
lean_inc_n(v_decl_2759_, 2);
v___x_2792_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2792_, 0, v_decl_2759_);
lean_ctor_set(v___x_2792_, 1, v_a_2777_);
v___x_2793_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_a_2756_, v_env_2780_, v___x_2792_, v_asyncMode_2791_, v_decl_2759_);
lean_dec(v_asyncMode_2791_);
v___x_2794_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2);
if (v_isShared_2790_ == 0)
{
lean_ctor_set(v___x_2789_, 5, v___x_2794_);
lean_ctor_set(v___x_2789_, 0, v___x_2793_);
v___x_2796_ = v___x_2789_;
goto v_reusejp_2795_;
}
else
{
lean_object* v_reuseFailAlloc_2802_; 
v_reuseFailAlloc_2802_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2802_, 0, v___x_2793_);
lean_ctor_set(v_reuseFailAlloc_2802_, 1, v_nextMacroScope_2781_);
lean_ctor_set(v_reuseFailAlloc_2802_, 2, v_ngen_2782_);
lean_ctor_set(v_reuseFailAlloc_2802_, 3, v_auxDeclNGen_2783_);
lean_ctor_set(v_reuseFailAlloc_2802_, 4, v_traceState_2784_);
lean_ctor_set(v_reuseFailAlloc_2802_, 5, v___x_2794_);
lean_ctor_set(v_reuseFailAlloc_2802_, 6, v_messages_2785_);
lean_ctor_set(v_reuseFailAlloc_2802_, 7, v_infoState_2786_);
lean_ctor_set(v_reuseFailAlloc_2802_, 8, v_snapshotTasks_2787_);
v___x_2796_ = v_reuseFailAlloc_2802_;
goto v_reusejp_2795_;
}
v_reusejp_2795_:
{
lean_object* v___x_2797_; lean_object* v___x_2798_; 
v___x_2797_ = lean_st_ref_set(v___y_2775_, v___x_2796_);
lean_inc(v___y_2775_);
lean_inc_ref(v___y_2774_);
v___x_2798_ = lean_apply_5(v_afterSet_2757_, v_decl_2759_, v_a_2777_, v___y_2774_, v___y_2775_, lean_box(0));
if (lean_obj_tag(v___x_2798_) == 0)
{
lean_dec_ref(v___y_2773_);
return v___x_2798_;
}
else
{
lean_object* v_a_2799_; uint8_t v___x_2800_; 
v_a_2799_ = lean_ctor_get(v___x_2798_, 0);
lean_inc(v_a_2799_);
v___x_2800_ = l_Lean_Exception_isInterrupt(v_a_2799_);
if (v___x_2800_ == 0)
{
uint8_t v___x_2801_; 
v___x_2801_ = l_Lean_Exception_isRuntime(v_a_2799_);
v___y_2766_ = v___y_2774_;
v___y_2767_ = v___y_2773_;
v___y_2768_ = v___x_2798_;
v___y_2769_ = v___y_2775_;
v___y_2770_ = v___x_2801_;
goto v___jp_2765_;
}
else
{
lean_dec(v_a_2799_);
v___y_2766_ = v___y_2774_;
v___y_2767_ = v___y_2773_;
v___y_2768_ = v___x_2798_;
v___y_2769_ = v___y_2775_;
v___y_2770_ = v___x_2800_;
goto v___jp_2765_;
}
}
}
}
}
else
{
lean_object* v_a_2805_; lean_object* v___x_2807_; uint8_t v_isShared_2808_; uint8_t v_isSharedCheck_2812_; 
lean_dec_ref(v___y_2773_);
lean_dec(v_decl_2759_);
lean_dec_ref(v_afterSet_2757_);
lean_dec_ref(v_a_2756_);
v_a_2805_ = lean_ctor_get(v___x_2776_, 0);
v_isSharedCheck_2812_ = !lean_is_exclusive(v___x_2776_);
if (v_isSharedCheck_2812_ == 0)
{
v___x_2807_ = v___x_2776_;
v_isShared_2808_ = v_isSharedCheck_2812_;
goto v_resetjp_2806_;
}
else
{
lean_inc(v_a_2805_);
lean_dec(v___x_2776_);
v___x_2807_ = lean_box(0);
v_isShared_2808_ = v_isSharedCheck_2812_;
goto v_resetjp_2806_;
}
v_resetjp_2806_:
{
lean_object* v___x_2810_; 
if (v_isShared_2808_ == 0)
{
v___x_2810_ = v___x_2807_;
goto v_reusejp_2809_;
}
else
{
lean_object* v_reuseFailAlloc_2811_; 
v_reuseFailAlloc_2811_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2811_, 0, v_a_2805_);
v___x_2810_ = v_reuseFailAlloc_2811_;
goto v_reusejp_2809_;
}
v_reusejp_2809_:
{
return v___x_2810_;
}
}
}
}
v___jp_2813_:
{
lean_object* v___x_2814_; lean_object* v_env_2815_; lean_object* v___x_2816_; 
v___x_2814_ = lean_st_ref_get(v___y_2763_);
v_env_2815_ = lean_ctor_get(v___x_2814_, 0);
lean_inc_ref(v_env_2815_);
lean_dec(v___x_2814_);
v___x_2816_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2815_, v_decl_2759_);
if (lean_obj_tag(v___x_2816_) == 0)
{
lean_dec(v_name_2758_);
v___y_2773_ = v_env_2815_;
v___y_2774_ = v___y_2762_;
v___y_2775_ = v___y_2763_;
goto v___jp_2772_;
}
else
{
lean_object* v___x_2817_; 
lean_dec_ref_known(v___x_2816_, 1);
lean_dec_ref(v_env_2815_);
lean_dec(v_stx_2760_);
lean_dec_ref(v_afterSet_2757_);
lean_dec_ref(v_a_2756_);
lean_dec_ref(v_getParam_2755_);
v___x_2817_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg(v_name_2758_, v_decl_2759_, v___y_2762_, v___y_2763_);
return v___x_2817_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___lam__7___boxed(lean_object* v_getParam_2821_, lean_object* v_a_2822_, lean_object* v_afterSet_2823_, lean_object* v_name_2824_, lean_object* v_decl_2825_, lean_object* v_stx_2826_, lean_object* v_kind_2827_, lean_object* v___y_2828_, lean_object* v___y_2829_, lean_object* v___y_2830_){
_start:
{
uint8_t v_kind_boxed_2831_; lean_object* v_res_2832_; 
v_kind_boxed_2831_ = lean_unbox(v_kind_2827_);
v_res_2832_ = l_Lean_registerParametricAttribute___redArg___lam__7(v_getParam_2821_, v_a_2822_, v_afterSet_2823_, v_name_2824_, v_decl_2825_, v_stx_2826_, v_kind_boxed_2831_, v___y_2828_, v___y_2829_);
lean_dec(v___y_2829_);
lean_dec_ref(v___y_2828_);
return v_res_2832_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg(lean_object* v_impl_2843_){
_start:
{
lean_object* v_toAttributeImplCore_2845_; lean_object* v_getParam_2846_; lean_object* v_afterSet_2847_; uint8_t v_preserveOrder_2848_; lean_object* v_ref_2849_; lean_object* v_name_2850_; lean_object* v___f_2851_; lean_object* v___x_2852_; lean_object* v___f_2853_; lean_object* v___f_2854_; lean_object* v___f_2855_; lean_object* v___f_2856_; lean_object* v___f_2857_; lean_object* v___x_2858_; lean_object* v___x_2859_; lean_object* v___x_2860_; lean_object* v___x_2861_; lean_object* v___x_2862_; 
v_toAttributeImplCore_2845_ = lean_ctor_get(v_impl_2843_, 0);
lean_inc_ref(v_toAttributeImplCore_2845_);
v_getParam_2846_ = lean_ctor_get(v_impl_2843_, 1);
lean_inc_ref(v_getParam_2846_);
v_afterSet_2847_ = lean_ctor_get(v_impl_2843_, 2);
lean_inc_ref(v_afterSet_2847_);
v_preserveOrder_2848_ = lean_ctor_get_uint8(v_impl_2843_, sizeof(void*)*4);
v_ref_2849_ = lean_ctor_get(v_toAttributeImplCore_2845_, 0);
v_name_2850_ = lean_ctor_get(v_toAttributeImplCore_2845_, 1);
v___f_2851_ = ((lean_object*)(l_Lean_registerParametricAttribute___redArg___closed__0));
v___x_2852_ = lean_box(v_preserveOrder_2848_);
v___f_2853_ = lean_alloc_closure((void*)(l_Lean_registerParametricAttribute___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_2853_, 0, v_impl_2843_);
lean_closure_set(v___f_2853_, 1, v___x_2852_);
v___f_2854_ = ((lean_object*)(l_Lean_registerParametricAttribute___redArg___closed__1));
v___f_2855_ = ((lean_object*)(l_Lean_registerParametricAttribute___redArg___closed__2));
v___f_2856_ = ((lean_object*)(l_Lean_registerParametricAttribute___redArg___closed__4));
v___f_2857_ = ((lean_object*)(l_Lean_registerParametricAttribute___redArg___closed__5));
v___x_2858_ = lean_box(2);
v___x_2859_ = lean_box(0);
lean_inc(v_ref_2849_);
v___x_2860_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_2860_, 0, v_ref_2849_);
lean_ctor_set(v___x_2860_, 1, v___f_2857_);
lean_ctor_set(v___x_2860_, 2, v___f_2856_);
lean_ctor_set(v___x_2860_, 3, v___f_2851_);
lean_ctor_set(v___x_2860_, 4, v___f_2853_);
lean_ctor_set(v___x_2860_, 5, v___f_2854_);
lean_ctor_set(v___x_2860_, 6, v___x_2858_);
lean_ctor_set(v___x_2860_, 7, v___x_2859_);
v___x_2861_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2861_, 0, v___x_2860_);
lean_ctor_set(v___x_2861_, 1, v___f_2855_);
v___x_2862_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_2861_);
if (lean_obj_tag(v___x_2862_) == 0)
{
lean_object* v_a_2863_; lean_object* v___f_2864_; lean_object* v___f_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; 
v_a_2863_ = lean_ctor_get(v___x_2862_, 0);
lean_inc_n(v_a_2863_, 2);
lean_dec_ref_known(v___x_2862_, 1);
lean_inc_n(v_name_2850_, 2);
v___f_2864_ = lean_alloc_closure((void*)(l_Lean_registerTagAttribute___lam__6___boxed), 5, 1);
lean_closure_set(v___f_2864_, 0, v_name_2850_);
v___f_2865_ = lean_alloc_closure((void*)(l_Lean_registerParametricAttribute___redArg___lam__7___boxed), 10, 4);
lean_closure_set(v___f_2865_, 0, v_getParam_2846_);
lean_closure_set(v___f_2865_, 1, v_a_2863_);
lean_closure_set(v___f_2865_, 2, v_afterSet_2847_);
lean_closure_set(v___f_2865_, 3, v_name_2850_);
v___x_2866_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2866_, 0, v_toAttributeImplCore_2845_);
lean_ctor_set(v___x_2866_, 1, v___f_2865_);
lean_ctor_set(v___x_2866_, 2, v___f_2864_);
lean_inc_ref(v___x_2866_);
v___x_2867_ = l_Lean_registerBuiltinAttribute(v___x_2866_);
if (lean_obj_tag(v___x_2867_) == 0)
{
lean_object* v___x_2869_; uint8_t v_isShared_2870_; uint8_t v_isSharedCheck_2875_; 
v_isSharedCheck_2875_ = !lean_is_exclusive(v___x_2867_);
if (v_isSharedCheck_2875_ == 0)
{
lean_object* v_unused_2876_; 
v_unused_2876_ = lean_ctor_get(v___x_2867_, 0);
lean_dec(v_unused_2876_);
v___x_2869_ = v___x_2867_;
v_isShared_2870_ = v_isSharedCheck_2875_;
goto v_resetjp_2868_;
}
else
{
lean_dec(v___x_2867_);
v___x_2869_ = lean_box(0);
v_isShared_2870_ = v_isSharedCheck_2875_;
goto v_resetjp_2868_;
}
v_resetjp_2868_:
{
lean_object* v___x_2871_; lean_object* v___x_2873_; 
v___x_2871_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2871_, 0, v___x_2866_);
lean_ctor_set(v___x_2871_, 1, v_a_2863_);
lean_ctor_set_uint8(v___x_2871_, sizeof(void*)*2, v_preserveOrder_2848_);
if (v_isShared_2870_ == 0)
{
lean_ctor_set(v___x_2869_, 0, v___x_2871_);
v___x_2873_ = v___x_2869_;
goto v_reusejp_2872_;
}
else
{
lean_object* v_reuseFailAlloc_2874_; 
v_reuseFailAlloc_2874_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2874_, 0, v___x_2871_);
v___x_2873_ = v_reuseFailAlloc_2874_;
goto v_reusejp_2872_;
}
v_reusejp_2872_:
{
return v___x_2873_;
}
}
}
else
{
lean_object* v_a_2877_; lean_object* v___x_2879_; uint8_t v_isShared_2880_; uint8_t v_isSharedCheck_2884_; 
lean_dec_ref_known(v___x_2866_, 3);
lean_dec(v_a_2863_);
v_a_2877_ = lean_ctor_get(v___x_2867_, 0);
v_isSharedCheck_2884_ = !lean_is_exclusive(v___x_2867_);
if (v_isSharedCheck_2884_ == 0)
{
v___x_2879_ = v___x_2867_;
v_isShared_2880_ = v_isSharedCheck_2884_;
goto v_resetjp_2878_;
}
else
{
lean_inc(v_a_2877_);
lean_dec(v___x_2867_);
v___x_2879_ = lean_box(0);
v_isShared_2880_ = v_isSharedCheck_2884_;
goto v_resetjp_2878_;
}
v_resetjp_2878_:
{
lean_object* v___x_2882_; 
if (v_isShared_2880_ == 0)
{
v___x_2882_ = v___x_2879_;
goto v_reusejp_2881_;
}
else
{
lean_object* v_reuseFailAlloc_2883_; 
v_reuseFailAlloc_2883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2883_, 0, v_a_2877_);
v___x_2882_ = v_reuseFailAlloc_2883_;
goto v_reusejp_2881_;
}
v_reusejp_2881_:
{
return v___x_2882_;
}
}
}
}
else
{
lean_object* v_a_2885_; lean_object* v___x_2887_; uint8_t v_isShared_2888_; uint8_t v_isSharedCheck_2892_; 
lean_dec_ref(v_afterSet_2847_);
lean_dec_ref(v_getParam_2846_);
lean_dec_ref(v_toAttributeImplCore_2845_);
v_a_2885_ = lean_ctor_get(v___x_2862_, 0);
v_isSharedCheck_2892_ = !lean_is_exclusive(v___x_2862_);
if (v_isSharedCheck_2892_ == 0)
{
v___x_2887_ = v___x_2862_;
v_isShared_2888_ = v_isSharedCheck_2892_;
goto v_resetjp_2886_;
}
else
{
lean_inc(v_a_2885_);
lean_dec(v___x_2862_);
v___x_2887_ = lean_box(0);
v_isShared_2888_ = v_isSharedCheck_2892_;
goto v_resetjp_2886_;
}
v_resetjp_2886_:
{
lean_object* v___x_2890_; 
if (v_isShared_2888_ == 0)
{
v___x_2890_ = v___x_2887_;
goto v_reusejp_2889_;
}
else
{
lean_object* v_reuseFailAlloc_2891_; 
v_reuseFailAlloc_2891_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2891_, 0, v_a_2885_);
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
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___boxed(lean_object* v_impl_2893_, lean_object* v_a_2894_){
_start:
{
lean_object* v_res_2895_; 
v_res_2895_ = l_Lean_registerParametricAttribute___redArg(v_impl_2893_);
return v_res_2895_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute(lean_object* v_00_u03b1_2896_, lean_object* v_impl_2897_){
_start:
{
lean_object* v___x_2899_; 
v___x_2899_ = l_Lean_registerParametricAttribute___redArg(v_impl_2897_);
return v___x_2899_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___boxed(lean_object* v_00_u03b1_2900_, lean_object* v_impl_2901_, lean_object* v_a_2902_){
_start:
{
lean_object* v_res_2903_; 
v_res_2903_ = l_Lean_registerParametricAttribute(v_00_u03b1_2900_, v_impl_2901_);
return v_res_2903_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttribute_spec__0(lean_object* v_00_u03b1_2904_, lean_object* v_impl_2905_, lean_object* v_env_2906_, lean_object* v_as_2907_, size_t v_i_2908_, size_t v_stop_2909_, lean_object* v_b_2910_){
_start:
{
lean_object* v___x_2911_; 
v___x_2911_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttribute_spec__0___redArg(v_impl_2905_, v_env_2906_, v_as_2907_, v_i_2908_, v_stop_2909_, v_b_2910_);
return v___x_2911_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttribute_spec__0___boxed(lean_object* v_00_u03b1_2912_, lean_object* v_impl_2913_, lean_object* v_env_2914_, lean_object* v_as_2915_, lean_object* v_i_2916_, lean_object* v_stop_2917_, lean_object* v_b_2918_){
_start:
{
size_t v_i_boxed_2919_; size_t v_stop_boxed_2920_; lean_object* v_res_2921_; 
v_i_boxed_2919_ = lean_unbox_usize(v_i_2916_);
lean_dec(v_i_2916_);
v_stop_boxed_2920_ = lean_unbox_usize(v_stop_2917_);
lean_dec(v_stop_2917_);
v_res_2921_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttribute_spec__0(v_00_u03b1_2912_, v_impl_2913_, v_env_2914_, v_as_2915_, v_i_boxed_2919_, v_stop_boxed_2920_, v_b_2918_);
lean_dec_ref(v_as_2915_);
return v_res_2921_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1___redArg(lean_object* v_init_2922_, lean_object* v_t_2923_){
_start:
{
lean_object* v___x_2924_; 
v___x_2924_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1_spec__1___redArg(v_init_2922_, v_t_2923_);
return v___x_2924_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1___redArg___boxed(lean_object* v_init_2925_, lean_object* v_t_2926_){
_start:
{
lean_object* v_res_2927_; 
v_res_2927_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1___redArg(v_init_2925_, v_t_2926_);
lean_dec(v_t_2926_);
return v_res_2927_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1(lean_object* v_00_u03b1_2928_, lean_object* v_init_2929_, lean_object* v_t_2930_){
_start:
{
lean_object* v___x_2931_; 
v___x_2931_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1_spec__1___redArg(v_init_2929_, v_t_2930_);
return v___x_2931_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1___boxed(lean_object* v_00_u03b1_2932_, lean_object* v_init_2933_, lean_object* v_t_2934_){
_start:
{
lean_object* v_res_2935_; 
v_res_2935_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1(v_00_u03b1_2932_, v_init_2933_, v_t_2934_);
lean_dec(v_t_2934_);
return v_res_2935_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2(lean_object* v_00_u03b1_2936_, lean_object* v_n_2937_, lean_object* v_as_2938_, lean_object* v_lo_2939_, lean_object* v_hi_2940_, lean_object* v_w_2941_, lean_object* v_hlo_2942_, lean_object* v_hhi_2943_){
_start:
{
lean_object* v___x_2944_; 
v___x_2944_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2___redArg(v_n_2937_, v_as_2938_, v_lo_2939_, v_hi_2940_);
return v___x_2944_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2___boxed(lean_object* v_00_u03b1_2945_, lean_object* v_n_2946_, lean_object* v_as_2947_, lean_object* v_lo_2948_, lean_object* v_hi_2949_, lean_object* v_w_2950_, lean_object* v_hlo_2951_, lean_object* v_hhi_2952_){
_start:
{
lean_object* v_res_2953_; 
v_res_2953_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2(v_00_u03b1_2945_, v_n_2946_, v_as_2947_, v_lo_2948_, v_hi_2949_, v_w_2950_, v_hlo_2951_, v_hhi_2952_);
lean_dec(v_hi_2949_);
lean_dec(v_n_2946_);
return v_res_2953_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3(lean_object* v_00_u03b1_2954_, lean_object* v_snd_2955_, lean_object* v_as_2956_, lean_object* v_start_2957_, lean_object* v_stop_2958_){
_start:
{
lean_object* v___x_2959_; 
v___x_2959_ = l_Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3___redArg(v_snd_2955_, v_as_2956_, v_start_2957_, v_stop_2958_);
return v___x_2959_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3___boxed(lean_object* v_00_u03b1_2960_, lean_object* v_snd_2961_, lean_object* v_as_2962_, lean_object* v_start_2963_, lean_object* v_stop_2964_){
_start:
{
lean_object* v_res_2965_; 
v_res_2965_ = l_Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3(v_00_u03b1_2960_, v_snd_2961_, v_as_2962_, v_start_2963_, v_stop_2964_);
lean_dec(v_stop_2964_);
lean_dec(v_start_2963_);
lean_dec_ref(v_as_2962_);
lean_dec(v_snd_2961_);
return v_res_2965_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1_spec__1(lean_object* v_00_u03b1_2966_, lean_object* v_init_2967_, lean_object* v_x_2968_){
_start:
{
lean_object* v___x_2969_; 
v___x_2969_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1_spec__1___redArg(v_init_2967_, v_x_2968_);
return v___x_2969_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1_spec__1___boxed(lean_object* v_00_u03b1_2970_, lean_object* v_init_2971_, lean_object* v_x_2972_){
_start:
{
lean_object* v_res_2973_; 
v_res_2973_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1_spec__1(v_00_u03b1_2970_, v_init_2971_, v_x_2972_);
lean_dec(v_x_2972_);
return v_res_2973_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2_spec__3(lean_object* v_00_u03b1_2974_, lean_object* v_n_2975_, lean_object* v_lo_2976_, lean_object* v_hi_2977_, lean_object* v_hhi_2978_, lean_object* v_pivot_2979_, lean_object* v_as_2980_, lean_object* v_i_2981_, lean_object* v_k_2982_, lean_object* v_ilo_2983_, lean_object* v_ik_2984_, lean_object* v_w_2985_){
_start:
{
lean_object* v___x_2986_; 
v___x_2986_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2_spec__3___redArg(v_hi_2977_, v_pivot_2979_, v_as_2980_, v_i_2981_, v_k_2982_);
return v___x_2986_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2_spec__3___boxed(lean_object* v_00_u03b1_2987_, lean_object* v_n_2988_, lean_object* v_lo_2989_, lean_object* v_hi_2990_, lean_object* v_hhi_2991_, lean_object* v_pivot_2992_, lean_object* v_as_2993_, lean_object* v_i_2994_, lean_object* v_k_2995_, lean_object* v_ilo_2996_, lean_object* v_ik_2997_, lean_object* v_w_2998_){
_start:
{
lean_object* v_res_2999_; 
v_res_2999_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2_spec__3(v_00_u03b1_2987_, v_n_2988_, v_lo_2989_, v_hi_2990_, v_hhi_2991_, v_pivot_2992_, v_as_2993_, v_i_2994_, v_k_2995_, v_ilo_2996_, v_ik_2997_, v_w_2998_);
lean_dec_ref(v_pivot_2992_);
lean_dec(v_hi_2990_);
lean_dec(v_lo_2989_);
lean_dec(v_n_2988_);
return v_res_2999_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3_spec__5(lean_object* v_00_u03b1_3000_, lean_object* v_snd_3001_, lean_object* v_as_3002_, size_t v_i_3003_, size_t v_stop_3004_, lean_object* v_b_3005_){
_start:
{
lean_object* v___x_3006_; 
v___x_3006_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3_spec__5___redArg(v_snd_3001_, v_as_3002_, v_i_3003_, v_stop_3004_, v_b_3005_);
return v___x_3006_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3_spec__5___boxed(lean_object* v_00_u03b1_3007_, lean_object* v_snd_3008_, lean_object* v_as_3009_, lean_object* v_i_3010_, lean_object* v_stop_3011_, lean_object* v_b_3012_){
_start:
{
size_t v_i_boxed_3013_; size_t v_stop_boxed_3014_; lean_object* v_res_3015_; 
v_i_boxed_3013_ = lean_unbox_usize(v_i_3010_);
lean_dec(v_i_3010_);
v_stop_boxed_3014_ = lean_unbox_usize(v_stop_3011_);
lean_dec(v_stop_3011_);
v_res_3015_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3_spec__5(v_00_u03b1_3007_, v_snd_3008_, v_as_3009_, v_i_boxed_3013_, v_stop_boxed_3014_, v_b_3012_);
lean_dec_ref(v_as_3009_);
lean_dec(v_snd_3008_);
return v_res_3015_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParam_x3f___redArg___lam__1(lean_object* v_decl_3016_, lean_object* v___x_3017_, lean_object* v___x_3018_, lean_object* v_a_3019_, lean_object* v_x_3020_, lean_object* v___y_3021_){
_start:
{
lean_object* v_fst_3022_; uint8_t v___x_3023_; 
v_fst_3022_ = lean_ctor_get(v_a_3019_, 0);
v___x_3023_ = lean_name_eq(v_fst_3022_, v_decl_3016_);
if (v___x_3023_ == 0)
{
lean_object* v___x_3024_; 
lean_dec_ref(v_a_3019_);
v___x_3024_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3024_, 0, v___x_3017_);
return v___x_3024_;
}
else
{
lean_object* v___x_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; lean_object* v___x_3028_; 
lean_dec_ref(v___x_3017_);
v___x_3025_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3025_, 0, v_a_3019_);
v___x_3026_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3026_, 0, v___x_3025_);
v___x_3027_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3027_, 0, v___x_3026_);
lean_ctor_set(v___x_3027_, 1, v___x_3018_);
v___x_3028_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3028_, 0, v___x_3027_);
return v___x_3028_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParam_x3f___redArg___lam__1___boxed(lean_object* v_decl_3029_, lean_object* v___x_3030_, lean_object* v___x_3031_, lean_object* v_a_3032_, lean_object* v_x_3033_, lean_object* v___y_3034_){
_start:
{
lean_object* v_res_3035_; 
v_res_3035_ = l_Lean_ParametricAttribute_getParam_x3f___redArg___lam__1(v_decl_3029_, v___x_3030_, v___x_3031_, v_a_3032_, v_x_3033_, v___y_3034_);
lean_dec_ref(v___y_3034_);
lean_dec(v_decl_3029_);
return v_res_3035_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParam_x3f___redArg(lean_object* v_inst_3063_, lean_object* v_attr_3064_, lean_object* v_env_3065_, lean_object* v_decl_3066_){
_start:
{
lean_object* v___y_3068_; lean_object* v___x_3079_; lean_object* v___x_3080_; 
v___x_3079_ = ((lean_object*)(l_Lean_ParametricAttribute_getParam_x3f___redArg___closed__0));
v___x_3080_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3065_, v_decl_3066_);
if (lean_obj_tag(v___x_3080_) == 0)
{
lean_object* v_ext_3081_; lean_object* v_toEnvExtension_3082_; lean_object* v_asyncMode_3083_; lean_object* v___x_3084_; lean_object* v___x_3085_; lean_object* v_snd_3086_; lean_object* v___x_3087_; 
lean_dec(v_inst_3063_);
v_ext_3081_ = lean_ctor_get(v_attr_3064_, 1);
v_toEnvExtension_3082_ = lean_ctor_get(v_ext_3081_, 0);
v_asyncMode_3083_ = lean_ctor_get(v_toEnvExtension_3082_, 2);
v___x_3084_ = lean_box(0);
v___x_3085_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3079_, v_ext_3081_, v_env_3065_, v_asyncMode_3083_, v___x_3084_);
v_snd_3086_ = lean_ctor_get(v___x_3085_, 1);
lean_inc(v_snd_3086_);
lean_dec(v___x_3085_);
v___x_3087_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_snd_3086_, v_decl_3066_);
lean_dec(v_decl_3066_);
lean_dec(v_snd_3086_);
return v___x_3087_;
}
else
{
uint8_t v_preserveOrder_3088_; 
v_preserveOrder_3088_ = lean_ctor_get_uint8(v_attr_3064_, sizeof(void*)*2);
if (v_preserveOrder_3088_ == 0)
{
lean_object* v_val_3089_; lean_object* v_ext_3090_; uint8_t v___x_3091_; lean_object* v___x_3092_; lean_object* v___x_3093_; lean_object* v___x_3094_; uint8_t v___x_3095_; 
v_val_3089_ = lean_ctor_get(v___x_3080_, 0);
lean_inc(v_val_3089_);
lean_dec_ref_known(v___x_3080_, 1);
v_ext_3090_ = lean_ctor_get(v_attr_3064_, 1);
v___x_3091_ = 0;
v___x_3092_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_3079_, v_ext_3090_, v_env_3065_, v_val_3089_, v___x_3091_);
lean_dec(v_val_3089_);
lean_dec_ref(v_env_3065_);
v___x_3093_ = lean_unsigned_to_nat(0u);
v___x_3094_ = lean_array_get_size(v___x_3092_);
v___x_3095_ = lean_nat_dec_lt(v___x_3093_, v___x_3094_);
if (v___x_3095_ == 0)
{
lean_object* v___x_3096_; 
lean_dec_ref(v___x_3092_);
lean_dec(v_decl_3066_);
lean_dec(v_inst_3063_);
v___x_3096_ = lean_box(0);
return v___x_3096_;
}
else
{
lean_object* v___x_3097_; lean_object* v___x_3098_; uint8_t v___x_3099_; 
v___x_3097_ = lean_unsigned_to_nat(1u);
v___x_3098_ = lean_nat_sub(v___x_3094_, v___x_3097_);
v___x_3099_ = lean_nat_dec_le(v___x_3093_, v___x_3098_);
if (v___x_3099_ == 0)
{
lean_object* v___x_3100_; 
lean_dec(v___x_3098_);
lean_dec_ref(v___x_3092_);
lean_dec(v_decl_3066_);
lean_dec(v_inst_3063_);
v___x_3100_ = lean_box(0);
return v___x_3100_;
}
else
{
lean_object* v___f_3101_; lean_object* v___x_3102_; lean_object* v___x_3103_; lean_object* v___x_3104_; 
v___f_3101_ = ((lean_object*)(l_Lean_ParametricAttribute_getParam_x3f___redArg___closed__1));
v___x_3102_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3102_, 0, v_decl_3066_);
lean_ctor_set(v___x_3102_, 1, v_inst_3063_);
v___x_3103_ = ((lean_object*)(l_Lean_ParametricAttribute_getParam_x3f___redArg___closed__2));
v___x_3104_ = l_Array_binSearchAux___redArg(v___f_3101_, v___x_3103_, v___x_3092_, v___x_3102_, v___x_3093_, v___x_3098_);
lean_dec_ref(v___x_3092_);
v___y_3068_ = v___x_3104_;
goto v___jp_3067_;
}
}
}
else
{
lean_object* v_val_3105_; lean_object* v_ext_3106_; uint8_t v___x_3107_; lean_object* v___x_3108_; lean_object* v___x_3109_; lean_object* v___x_3110_; lean_object* v___x_3111_; lean_object* v___x_3112_; lean_object* v___f_3113_; size_t v_sz_3114_; size_t v___x_3115_; lean_object* v___x_3116_; lean_object* v_fst_3117_; 
lean_dec(v_inst_3063_);
v_val_3105_ = lean_ctor_get(v___x_3080_, 0);
lean_inc(v_val_3105_);
lean_dec_ref_known(v___x_3080_, 1);
v_ext_3106_ = lean_ctor_get(v_attr_3064_, 1);
v___x_3107_ = 0;
v___x_3108_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_3079_, v_ext_3106_, v_env_3065_, v_val_3105_, v___x_3107_);
lean_dec(v_val_3105_);
lean_dec_ref(v_env_3065_);
v___x_3109_ = ((lean_object*)(l_Lean_ParametricAttribute_getParam_x3f___redArg___closed__12));
v___x_3110_ = lean_box(0);
v___x_3111_ = lean_box(0);
v___x_3112_ = ((lean_object*)(l_Lean_ParametricAttribute_getParam_x3f___redArg___closed__13));
v___f_3113_ = lean_alloc_closure((void*)(l_Lean_ParametricAttribute_getParam_x3f___redArg___lam__1___boxed), 6, 3);
lean_closure_set(v___f_3113_, 0, v_decl_3066_);
lean_closure_set(v___f_3113_, 1, v___x_3112_);
lean_closure_set(v___f_3113_, 2, v___x_3111_);
v_sz_3114_ = lean_array_size(v___x_3108_);
v___x_3115_ = ((size_t)0ULL);
v___x_3116_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_3109_, v___x_3108_, v___f_3113_, v_sz_3114_, v___x_3115_, v___x_3112_);
v_fst_3117_ = lean_ctor_get(v___x_3116_, 0);
lean_inc(v_fst_3117_);
lean_dec(v___x_3116_);
if (lean_obj_tag(v_fst_3117_) == 0)
{
return v___x_3110_;
}
else
{
lean_object* v_val_3118_; 
v_val_3118_ = lean_ctor_get(v_fst_3117_, 0);
lean_inc(v_val_3118_);
lean_dec_ref_known(v_fst_3117_, 1);
v___y_3068_ = v_val_3118_;
goto v___jp_3067_;
}
}
}
v___jp_3067_:
{
if (lean_obj_tag(v___y_3068_) == 0)
{
lean_object* v___x_3069_; 
v___x_3069_ = lean_box(0);
return v___x_3069_;
}
else
{
lean_object* v_val_3070_; lean_object* v___x_3072_; uint8_t v_isShared_3073_; uint8_t v_isSharedCheck_3078_; 
v_val_3070_ = lean_ctor_get(v___y_3068_, 0);
v_isSharedCheck_3078_ = !lean_is_exclusive(v___y_3068_);
if (v_isSharedCheck_3078_ == 0)
{
v___x_3072_ = v___y_3068_;
v_isShared_3073_ = v_isSharedCheck_3078_;
goto v_resetjp_3071_;
}
else
{
lean_inc(v_val_3070_);
lean_dec(v___y_3068_);
v___x_3072_ = lean_box(0);
v_isShared_3073_ = v_isSharedCheck_3078_;
goto v_resetjp_3071_;
}
v_resetjp_3071_:
{
lean_object* v_snd_3074_; lean_object* v___x_3076_; 
v_snd_3074_ = lean_ctor_get(v_val_3070_, 1);
lean_inc(v_snd_3074_);
lean_dec(v_val_3070_);
if (v_isShared_3073_ == 0)
{
lean_ctor_set(v___x_3072_, 0, v_snd_3074_);
v___x_3076_ = v___x_3072_;
goto v_reusejp_3075_;
}
else
{
lean_object* v_reuseFailAlloc_3077_; 
v_reuseFailAlloc_3077_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3077_, 0, v_snd_3074_);
v___x_3076_ = v_reuseFailAlloc_3077_;
goto v_reusejp_3075_;
}
v_reusejp_3075_:
{
return v___x_3076_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParam_x3f___redArg___boxed(lean_object* v_inst_3119_, lean_object* v_attr_3120_, lean_object* v_env_3121_, lean_object* v_decl_3122_){
_start:
{
lean_object* v_res_3123_; 
v_res_3123_ = l_Lean_ParametricAttribute_getParam_x3f___redArg(v_inst_3119_, v_attr_3120_, v_env_3121_, v_decl_3122_);
lean_dec_ref(v_attr_3120_);
return v_res_3123_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParam_x3f(lean_object* v_00_u03b1_3124_, lean_object* v_inst_3125_, lean_object* v_attr_3126_, lean_object* v_env_3127_, lean_object* v_decl_3128_){
_start:
{
lean_object* v___x_3129_; 
v___x_3129_ = l_Lean_ParametricAttribute_getParam_x3f___redArg(v_inst_3125_, v_attr_3126_, v_env_3127_, v_decl_3128_);
return v___x_3129_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParam_x3f___boxed(lean_object* v_00_u03b1_3130_, lean_object* v_inst_3131_, lean_object* v_attr_3132_, lean_object* v_env_3133_, lean_object* v_decl_3134_){
_start:
{
lean_object* v_res_3135_; 
v_res_3135_ = l_Lean_ParametricAttribute_getParam_x3f(v_00_u03b1_3130_, v_inst_3131_, v_attr_3132_, v_env_3133_, v_decl_3134_);
lean_dec_ref(v_attr_3132_);
return v_res_3135_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_setParam___redArg(lean_object* v_attr_3140_, lean_object* v_env_3141_, lean_object* v_decl_3142_, lean_object* v_param_3143_){
_start:
{
lean_object* v___x_3144_; 
v___x_3144_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3141_, v_decl_3142_);
if (lean_obj_tag(v___x_3144_) == 0)
{
lean_object* v_ext_3145_; lean_object* v_toEnvExtension_3146_; lean_object* v_attr_3147_; lean_object* v_asyncMode_3148_; lean_object* v___x_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; lean_object* v_snd_3152_; lean_object* v___x_3154_; uint8_t v_isShared_3155_; uint8_t v_isSharedCheck_3182_; 
v_ext_3145_ = lean_ctor_get(v_attr_3140_, 1);
lean_inc_ref(v_ext_3145_);
v_toEnvExtension_3146_ = lean_ctor_get(v_ext_3145_, 0);
v_attr_3147_ = lean_ctor_get(v_attr_3140_, 0);
lean_inc_ref(v_attr_3147_);
lean_dec_ref(v_attr_3140_);
v_asyncMode_3148_ = lean_ctor_get(v_toEnvExtension_3146_, 2);
lean_inc(v_asyncMode_3148_);
v___x_3149_ = ((lean_object*)(l_Lean_ParametricAttribute_getParam_x3f___redArg___closed__0));
v___x_3150_ = lean_box(0);
lean_inc_ref(v_env_3141_);
v___x_3151_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3149_, v_ext_3145_, v_env_3141_, v_asyncMode_3148_, v___x_3150_);
v_snd_3152_ = lean_ctor_get(v___x_3151_, 1);
v_isSharedCheck_3182_ = !lean_is_exclusive(v___x_3151_);
if (v_isSharedCheck_3182_ == 0)
{
lean_object* v_unused_3183_; 
v_unused_3183_ = lean_ctor_get(v___x_3151_, 0);
lean_dec(v_unused_3183_);
v___x_3154_ = v___x_3151_;
v_isShared_3155_ = v_isSharedCheck_3182_;
goto v_resetjp_3153_;
}
else
{
lean_inc(v_snd_3152_);
lean_dec(v___x_3151_);
v___x_3154_ = lean_box(0);
v_isShared_3155_ = v_isSharedCheck_3182_;
goto v_resetjp_3153_;
}
v_resetjp_3153_:
{
lean_object* v___x_3156_; 
v___x_3156_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_snd_3152_, v_decl_3142_);
lean_dec(v_snd_3152_);
if (lean_obj_tag(v___x_3156_) == 0)
{
lean_object* v___x_3158_; 
lean_dec_ref(v_attr_3147_);
if (v_isShared_3155_ == 0)
{
lean_ctor_set(v___x_3154_, 1, v_param_3143_);
lean_ctor_set(v___x_3154_, 0, v_decl_3142_);
v___x_3158_ = v___x_3154_;
goto v_reusejp_3157_;
}
else
{
lean_object* v_reuseFailAlloc_3161_; 
v_reuseFailAlloc_3161_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3161_, 0, v_decl_3142_);
lean_ctor_set(v_reuseFailAlloc_3161_, 1, v_param_3143_);
v___x_3158_ = v_reuseFailAlloc_3161_;
goto v_reusejp_3157_;
}
v_reusejp_3157_:
{
lean_object* v___x_3159_; lean_object* v___x_3160_; 
v___x_3159_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_ext_3145_, v_env_3141_, v___x_3158_, v_asyncMode_3148_, v___x_3150_);
lean_dec(v_asyncMode_3148_);
v___x_3160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3160_, 0, v___x_3159_);
return v___x_3160_;
}
}
else
{
lean_object* v___x_3163_; uint8_t v_isShared_3164_; uint8_t v_isSharedCheck_3180_; 
lean_del_object(v___x_3154_);
lean_dec(v_asyncMode_3148_);
lean_dec_ref(v_ext_3145_);
lean_dec(v_param_3143_);
lean_dec_ref(v_env_3141_);
v_isSharedCheck_3180_ = !lean_is_exclusive(v___x_3156_);
if (v_isSharedCheck_3180_ == 0)
{
lean_object* v_unused_3181_; 
v_unused_3181_ = lean_ctor_get(v___x_3156_, 0);
lean_dec(v_unused_3181_);
v___x_3163_ = v___x_3156_;
v_isShared_3164_ = v_isSharedCheck_3180_;
goto v_resetjp_3162_;
}
else
{
lean_dec(v___x_3156_);
v___x_3163_ = lean_box(0);
v_isShared_3164_ = v_isSharedCheck_3180_;
goto v_resetjp_3162_;
}
v_resetjp_3162_:
{
lean_object* v_toAttributeImplCore_3165_; lean_object* v_name_3166_; uint8_t v___x_3167_; lean_object* v___x_3168_; lean_object* v___x_3169_; lean_object* v___x_3170_; lean_object* v___x_3171_; lean_object* v___x_3172_; lean_object* v___x_3173_; lean_object* v___x_3174_; lean_object* v___x_3175_; lean_object* v___x_3176_; lean_object* v___x_3178_; 
v_toAttributeImplCore_3165_ = lean_ctor_get(v_attr_3147_, 0);
lean_inc_ref(v_toAttributeImplCore_3165_);
lean_dec_ref(v_attr_3147_);
v_name_3166_ = lean_ctor_get(v_toAttributeImplCore_3165_, 1);
lean_inc(v_name_3166_);
lean_dec_ref(v_toAttributeImplCore_3165_);
v___x_3167_ = 1;
v___x_3168_ = ((lean_object*)(l_Lean_ParametricAttribute_setParam___redArg___closed__0));
v___x_3169_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_3166_, v___x_3167_);
v___x_3170_ = lean_string_append(v___x_3168_, v___x_3169_);
lean_dec_ref(v___x_3169_);
v___x_3171_ = ((lean_object*)(l_Lean_ParametricAttribute_setParam___redArg___closed__1));
v___x_3172_ = lean_string_append(v___x_3170_, v___x_3171_);
v___x_3173_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_decl_3142_, v___x_3167_);
v___x_3174_ = lean_string_append(v___x_3172_, v___x_3173_);
lean_dec_ref(v___x_3173_);
v___x_3175_ = ((lean_object*)(l_Lean_ParametricAttribute_setParam___redArg___closed__2));
v___x_3176_ = lean_string_append(v___x_3174_, v___x_3175_);
if (v_isShared_3164_ == 0)
{
lean_ctor_set_tag(v___x_3163_, 0);
lean_ctor_set(v___x_3163_, 0, v___x_3176_);
v___x_3178_ = v___x_3163_;
goto v_reusejp_3177_;
}
else
{
lean_object* v_reuseFailAlloc_3179_; 
v_reuseFailAlloc_3179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3179_, 0, v___x_3176_);
v___x_3178_ = v_reuseFailAlloc_3179_;
goto v_reusejp_3177_;
}
v_reusejp_3177_:
{
return v___x_3178_;
}
}
}
}
}
else
{
lean_object* v___x_3185_; uint8_t v_isShared_3186_; uint8_t v_isSharedCheck_3203_; 
lean_dec(v_param_3143_);
lean_dec_ref(v_env_3141_);
v_isSharedCheck_3203_ = !lean_is_exclusive(v___x_3144_);
if (v_isSharedCheck_3203_ == 0)
{
lean_object* v_unused_3204_; 
v_unused_3204_ = lean_ctor_get(v___x_3144_, 0);
lean_dec(v_unused_3204_);
v___x_3185_ = v___x_3144_;
v_isShared_3186_ = v_isSharedCheck_3203_;
goto v_resetjp_3184_;
}
else
{
lean_dec(v___x_3144_);
v___x_3185_ = lean_box(0);
v_isShared_3186_ = v_isSharedCheck_3203_;
goto v_resetjp_3184_;
}
v_resetjp_3184_:
{
lean_object* v_attr_3187_; lean_object* v_toAttributeImplCore_3188_; lean_object* v_name_3189_; uint8_t v___x_3190_; lean_object* v___x_3191_; lean_object* v___x_3192_; lean_object* v___x_3193_; lean_object* v___x_3194_; lean_object* v___x_3195_; lean_object* v___x_3196_; lean_object* v___x_3197_; lean_object* v___x_3198_; lean_object* v___x_3199_; lean_object* v___x_3201_; 
v_attr_3187_ = lean_ctor_get(v_attr_3140_, 0);
lean_inc_ref(v_attr_3187_);
lean_dec_ref(v_attr_3140_);
v_toAttributeImplCore_3188_ = lean_ctor_get(v_attr_3187_, 0);
lean_inc_ref(v_toAttributeImplCore_3188_);
lean_dec_ref(v_attr_3187_);
v_name_3189_ = lean_ctor_get(v_toAttributeImplCore_3188_, 1);
lean_inc(v_name_3189_);
lean_dec_ref(v_toAttributeImplCore_3188_);
v___x_3190_ = 1;
v___x_3191_ = ((lean_object*)(l_Lean_ParametricAttribute_setParam___redArg___closed__0));
v___x_3192_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_3189_, v___x_3190_);
v___x_3193_ = lean_string_append(v___x_3191_, v___x_3192_);
lean_dec_ref(v___x_3192_);
v___x_3194_ = ((lean_object*)(l_Lean_ParametricAttribute_setParam___redArg___closed__1));
v___x_3195_ = lean_string_append(v___x_3193_, v___x_3194_);
v___x_3196_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_decl_3142_, v___x_3190_);
v___x_3197_ = lean_string_append(v___x_3195_, v___x_3196_);
lean_dec_ref(v___x_3196_);
v___x_3198_ = ((lean_object*)(l_Lean_ParametricAttribute_setParam___redArg___closed__3));
v___x_3199_ = lean_string_append(v___x_3197_, v___x_3198_);
if (v_isShared_3186_ == 0)
{
lean_ctor_set_tag(v___x_3185_, 0);
lean_ctor_set(v___x_3185_, 0, v___x_3199_);
v___x_3201_ = v___x_3185_;
goto v_reusejp_3200_;
}
else
{
lean_object* v_reuseFailAlloc_3202_; 
v_reuseFailAlloc_3202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3202_, 0, v___x_3199_);
v___x_3201_ = v_reuseFailAlloc_3202_;
goto v_reusejp_3200_;
}
v_reusejp_3200_:
{
return v___x_3201_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_setParam(lean_object* v_00_u03b1_3205_, lean_object* v_attr_3206_, lean_object* v_env_3207_, lean_object* v_decl_3208_, lean_object* v_param_3209_){
_start:
{
lean_object* v___x_3210_; 
v___x_3210_ = l_Lean_ParametricAttribute_setParam___redArg(v_attr_3206_, v_env_3207_, v_decl_3208_, v_param_3209_);
return v___x_3210_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___lam__0(lean_object* v_x_3211_, lean_object* v___y_3212_){
_start:
{
lean_object* v___x_3214_; lean_object* v___x_3215_; 
v___x_3214_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___lam__0___closed__1));
v___x_3215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3215_, 0, v___x_3214_);
return v___x_3215_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___lam__0___boxed(lean_object* v_x_3216_, lean_object* v___y_3217_, lean_object* v___y_3218_){
_start:
{
lean_object* v_res_3219_; 
v_res_3219_ = l_Lean_instInhabitedEnumAttributes_default___lam__0(v_x_3216_, v___y_3217_);
lean_dec_ref(v___y_3217_);
lean_dec_ref(v_x_3216_);
return v_res_3219_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___lam__1(lean_object* v_s_3220_, lean_object* v_x_3221_){
_start:
{
lean_inc(v_s_3220_);
return v_s_3220_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___lam__1___boxed(lean_object* v_s_3222_, lean_object* v_x_3223_){
_start:
{
lean_object* v_res_3224_; 
v_res_3224_ = l_Lean_instInhabitedEnumAttributes_default___lam__1(v_s_3222_, v_x_3223_);
lean_dec_ref(v_x_3223_);
lean_dec(v_s_3222_);
return v_res_3224_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___lam__2(lean_object* v_x_3225_, lean_object* v_x_3226_){
_start:
{
lean_object* v___x_3227_; 
v___x_3227_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___lam__2___closed__1));
return v___x_3227_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___lam__2___boxed(lean_object* v_x_3228_, lean_object* v_x_3229_){
_start:
{
lean_object* v_res_3230_; 
v_res_3230_ = l_Lean_instInhabitedEnumAttributes_default___lam__2(v_x_3228_, v_x_3229_);
lean_dec(v_x_3229_);
lean_dec_ref(v_x_3228_);
return v_res_3230_;
}
}
static lean_object* _init_l_Lean_instInhabitedEnumAttributes_default___closed__3(void){
_start:
{
lean_object* v___x_3234_; 
v___x_3234_ = l_Lean_instInhabitedEnvExtension_default(lean_box(0));
return v___x_3234_;
}
}
static lean_object* _init_l_Lean_instInhabitedEnumAttributes_default___closed__4(void){
_start:
{
lean_object* v___f_3235_; lean_object* v___f_3236_; lean_object* v___f_3237_; lean_object* v___f_3238_; lean_object* v___x_3239_; lean_object* v___x_3240_; lean_object* v___x_3241_; 
v___f_3235_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___closed__3));
v___f_3236_ = ((lean_object*)(l_Lean_instInhabitedEnumAttributes_default___closed__2));
v___f_3237_ = ((lean_object*)(l_Lean_instInhabitedEnumAttributes_default___closed__1));
v___f_3238_ = ((lean_object*)(l_Lean_instInhabitedEnumAttributes_default___closed__0));
v___x_3239_ = lean_box(0);
v___x_3240_ = lean_obj_once(&l_Lean_instInhabitedEnumAttributes_default___closed__3, &l_Lean_instInhabitedEnumAttributes_default___closed__3_once, _init_l_Lean_instInhabitedEnumAttributes_default___closed__3);
v___x_3241_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3241_, 0, v___x_3240_);
lean_ctor_set(v___x_3241_, 1, v___x_3239_);
lean_ctor_set(v___x_3241_, 2, v___f_3238_);
lean_ctor_set(v___x_3241_, 3, v___f_3237_);
lean_ctor_set(v___x_3241_, 4, v___f_3236_);
lean_ctor_set(v___x_3241_, 5, v___f_3235_);
return v___x_3241_;
}
}
static lean_object* _init_l_Lean_instInhabitedEnumAttributes_default___closed__5(void){
_start:
{
lean_object* v___x_3242_; lean_object* v___x_3243_; lean_object* v___x_3244_; 
v___x_3242_ = lean_obj_once(&l_Lean_instInhabitedEnumAttributes_default___closed__4, &l_Lean_instInhabitedEnumAttributes_default___closed__4_once, _init_l_Lean_instInhabitedEnumAttributes_default___closed__4);
v___x_3243_ = lean_box(0);
v___x_3244_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3244_, 0, v___x_3243_);
lean_ctor_set(v___x_3244_, 1, v___x_3242_);
return v___x_3244_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default(lean_object* v_00_u03b1_3245_){
_start:
{
lean_object* v___x_3246_; 
v___x_3246_ = lean_obj_once(&l_Lean_instInhabitedEnumAttributes_default___closed__5, &l_Lean_instInhabitedEnumAttributes_default___closed__5_once, _init_l_Lean_instInhabitedEnumAttributes_default___closed__5);
return v___x_3246_;
}
}
static lean_object* _init_l_Lean_instInhabitedEnumAttributes___closed__0(void){
_start:
{
lean_object* v___x_3247_; 
v___x_3247_ = l_Lean_instInhabitedEnumAttributes_default(lean_box(0));
return v___x_3247_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes(lean_object* v_a_3248_){
_start:
{
lean_object* v___x_3249_; 
v___x_3249_ = lean_obj_once(&l_Lean_instInhabitedEnumAttributes___closed__0, &l_Lean_instInhabitedEnumAttributes___closed__0_once, _init_l_Lean_instInhabitedEnumAttributes___closed__0);
return v___x_3249_;
}
}
static lean_object* _init_l_Lean_registerEnumAttributes___auto__1(void){
_start:
{
lean_object* v___x_3250_; 
v___x_3250_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__28, &l_Lean_AttributeImplCore_ref___autoParam___closed__28_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__28);
return v___x_3250_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__0(lean_object* v_x_3251_){
_start:
{
lean_object* v___x_3252_; 
v___x_3252_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___lam__2___closed__0));
return v___x_3252_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__0___boxed(lean_object* v_x_3253_){
_start:
{
lean_object* v_res_3254_; 
v_res_3254_ = l_Lean_registerEnumAttributes___redArg___lam__0(v_x_3253_);
lean_dec(v_x_3253_);
return v_res_3254_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___redArg(lean_object* v_newState_3255_, lean_object* v_x_3256_, lean_object* v_x_3257_){
_start:
{
if (lean_obj_tag(v_x_3257_) == 0)
{
return v_x_3256_;
}
else
{
lean_object* v_head_3258_; lean_object* v_tail_3259_; lean_object* v___x_3260_; 
v_head_3258_ = lean_ctor_get(v_x_3257_, 0);
lean_inc(v_head_3258_);
v_tail_3259_ = lean_ctor_get(v_x_3257_, 1);
lean_inc(v_tail_3259_);
lean_dec_ref_known(v_x_3257_, 2);
v___x_3260_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_newState_3255_, v_head_3258_);
if (lean_obj_tag(v___x_3260_) == 1)
{
lean_object* v_val_3261_; lean_object* v___x_3262_; 
v_val_3261_ = lean_ctor_get(v___x_3260_, 0);
lean_inc(v_val_3261_);
lean_dec_ref_known(v___x_3260_, 1);
v___x_3262_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_head_3258_, v_val_3261_, v_x_3256_);
v_x_3256_ = v___x_3262_;
v_x_3257_ = v_tail_3259_;
goto _start;
}
else
{
lean_dec(v___x_3260_);
lean_dec(v_head_3258_);
v_x_3257_ = v_tail_3259_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___redArg___boxed(lean_object* v_newState_3265_, lean_object* v_x_3266_, lean_object* v_x_3267_){
_start:
{
lean_object* v_res_3268_; 
v_res_3268_ = l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___redArg(v_newState_3265_, v_x_3266_, v_x_3267_);
lean_dec(v_newState_3265_);
return v_res_3268_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__1(lean_object* v_x_3269_, lean_object* v_newState_3270_, lean_object* v_consts_3271_, lean_object* v_st_3272_){
_start:
{
lean_object* v___x_3273_; 
v___x_3273_ = l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___redArg(v_newState_3270_, v_st_3272_, v_consts_3271_);
return v___x_3273_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__1___boxed(lean_object* v_x_3274_, lean_object* v_newState_3275_, lean_object* v_consts_3276_, lean_object* v_st_3277_){
_start:
{
lean_object* v_res_3278_; 
v_res_3278_ = l_Lean_registerEnumAttributes___redArg___lam__1(v_x_3274_, v_newState_3275_, v_consts_3276_, v_st_3277_);
lean_dec(v_newState_3275_);
lean_dec(v_x_3274_);
return v_res_3278_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__2(lean_object* v_s_3288_){
_start:
{
lean_object* v___x_3289_; lean_object* v___y_3291_; 
v___x_3289_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___lam__2___closed__3));
if (lean_obj_tag(v_s_3288_) == 0)
{
lean_object* v_size_3295_; 
v_size_3295_ = lean_ctor_get(v_s_3288_, 0);
lean_inc(v_size_3295_);
lean_dec_ref_known(v_s_3288_, 5);
v___y_3291_ = v_size_3295_;
goto v___jp_3290_;
}
else
{
lean_object* v___x_3296_; 
v___x_3296_ = lean_unsigned_to_nat(0u);
v___y_3291_ = v___x_3296_;
goto v___jp_3290_;
}
v___jp_3290_:
{
lean_object* v___x_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; 
v___x_3292_ = l_Nat_reprFast(v___y_3291_);
v___x_3293_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3293_, 0, v___x_3292_);
v___x_3294_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3294_, 0, v___x_3289_);
lean_ctor_set(v___x_3294_, 1, v___x_3293_);
return v___x_3294_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg(lean_object* v_env_3297_, lean_object* v_as_3298_, size_t v_i_3299_, size_t v_stop_3300_, lean_object* v_b_3301_){
_start:
{
lean_object* v___y_3303_; uint8_t v___x_3307_; 
v___x_3307_ = lean_usize_dec_eq(v_i_3299_, v_stop_3300_);
if (v___x_3307_ == 0)
{
lean_object* v___x_3308_; lean_object* v_fst_3309_; uint8_t v___x_3310_; lean_object* v___x_3311_; uint8_t v___x_3312_; 
v___x_3308_ = lean_array_uget_borrowed(v_as_3298_, v_i_3299_);
v_fst_3309_ = lean_ctor_get(v___x_3308_, 0);
v___x_3310_ = 1;
lean_inc_ref(v_env_3297_);
v___x_3311_ = l_Lean_Environment_setExporting(v_env_3297_, v___x_3310_);
lean_inc(v_fst_3309_);
v___x_3312_ = l_Lean_Environment_contains(v___x_3311_, v_fst_3309_, v___x_3307_);
if (v___x_3312_ == 0)
{
v___y_3303_ = v_b_3301_;
goto v___jp_3302_;
}
else
{
lean_object* v___x_3313_; 
lean_inc(v___x_3308_);
v___x_3313_ = lean_array_push(v_b_3301_, v___x_3308_);
v___y_3303_ = v___x_3313_;
goto v___jp_3302_;
}
}
else
{
lean_dec_ref(v_env_3297_);
return v_b_3301_;
}
v___jp_3302_:
{
size_t v___x_3304_; size_t v___x_3305_; 
v___x_3304_ = ((size_t)1ULL);
v___x_3305_ = lean_usize_add(v_i_3299_, v___x_3304_);
v_i_3299_ = v___x_3305_;
v_b_3301_ = v___y_3303_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg___boxed(lean_object* v_env_3314_, lean_object* v_as_3315_, lean_object* v_i_3316_, lean_object* v_stop_3317_, lean_object* v_b_3318_){
_start:
{
size_t v_i_boxed_3319_; size_t v_stop_boxed_3320_; lean_object* v_res_3321_; 
v_i_boxed_3319_ = lean_unbox_usize(v_i_3316_);
lean_dec(v_i_3316_);
v_stop_boxed_3320_ = lean_unbox_usize(v_stop_3317_);
lean_dec(v_stop_3317_);
v_res_3321_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg(v_env_3314_, v_as_3315_, v_i_boxed_3319_, v_stop_boxed_3320_, v_b_3318_);
lean_dec_ref(v_as_3315_);
return v_res_3321_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__3(lean_object* v_env_3322_, lean_object* v_m_3323_){
_start:
{
lean_object* v___x_3324_; lean_object* v___x_3325_; lean_object* v___y_3327_; lean_object* v___x_3341_; lean_object* v___x_3342_; lean_object* v___y_3344_; lean_object* v___y_3345_; uint8_t v___x_3347_; 
v___x_3324_ = lean_unsigned_to_nat(0u);
v___x_3325_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___lam__2___closed__0));
v___x_3341_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1_spec__1___redArg(v___x_3325_, v_m_3323_);
v___x_3342_ = lean_array_get_size(v___x_3341_);
v___x_3347_ = lean_nat_dec_eq(v___x_3342_, v___x_3324_);
if (v___x_3347_ == 0)
{
lean_object* v___x_3348_; lean_object* v___x_3349_; lean_object* v___y_3351_; uint8_t v___x_3353_; 
v___x_3348_ = lean_unsigned_to_nat(1u);
v___x_3349_ = lean_nat_sub(v___x_3342_, v___x_3348_);
v___x_3353_ = lean_nat_dec_le(v___x_3324_, v___x_3349_);
if (v___x_3353_ == 0)
{
lean_inc(v___x_3349_);
v___y_3351_ = v___x_3349_;
goto v___jp_3350_;
}
else
{
v___y_3351_ = v___x_3324_;
goto v___jp_3350_;
}
v___jp_3350_:
{
uint8_t v___x_3352_; 
v___x_3352_ = lean_nat_dec_le(v___y_3351_, v___x_3349_);
if (v___x_3352_ == 0)
{
lean_dec(v___x_3349_);
lean_inc(v___y_3351_);
v___y_3344_ = v___y_3351_;
v___y_3345_ = v___y_3351_;
goto v___jp_3343_;
}
else
{
v___y_3344_ = v___y_3351_;
v___y_3345_ = v___x_3349_;
goto v___jp_3343_;
}
}
}
else
{
v___y_3327_ = v___x_3341_;
goto v___jp_3326_;
}
v___jp_3326_:
{
lean_object* v___x_3328_; uint8_t v___x_3329_; 
v___x_3328_ = lean_array_get_size(v___y_3327_);
v___x_3329_ = lean_nat_dec_lt(v___x_3324_, v___x_3328_);
if (v___x_3329_ == 0)
{
lean_object* v___x_3330_; 
lean_dec_ref(v_env_3322_);
v___x_3330_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3330_, 0, v___x_3325_);
lean_ctor_set(v___x_3330_, 1, v___x_3325_);
lean_ctor_set(v___x_3330_, 2, v___y_3327_);
return v___x_3330_;
}
else
{
uint8_t v___x_3331_; 
v___x_3331_ = lean_nat_dec_le(v___x_3328_, v___x_3328_);
if (v___x_3331_ == 0)
{
if (v___x_3329_ == 0)
{
lean_object* v___x_3332_; 
lean_dec_ref(v_env_3322_);
v___x_3332_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3332_, 0, v___x_3325_);
lean_ctor_set(v___x_3332_, 1, v___x_3325_);
lean_ctor_set(v___x_3332_, 2, v___y_3327_);
return v___x_3332_;
}
else
{
size_t v___x_3333_; size_t v___x_3334_; lean_object* v___x_3335_; lean_object* v___x_3336_; 
v___x_3333_ = ((size_t)0ULL);
v___x_3334_ = lean_usize_of_nat(v___x_3328_);
v___x_3335_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg(v_env_3322_, v___y_3327_, v___x_3333_, v___x_3334_, v___x_3325_);
lean_inc_ref(v___x_3335_);
v___x_3336_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3336_, 0, v___x_3335_);
lean_ctor_set(v___x_3336_, 1, v___x_3335_);
lean_ctor_set(v___x_3336_, 2, v___y_3327_);
return v___x_3336_;
}
}
else
{
size_t v___x_3337_; size_t v___x_3338_; lean_object* v___x_3339_; lean_object* v___x_3340_; 
v___x_3337_ = ((size_t)0ULL);
v___x_3338_ = lean_usize_of_nat(v___x_3328_);
v___x_3339_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg(v_env_3322_, v___y_3327_, v___x_3337_, v___x_3338_, v___x_3325_);
lean_inc_ref(v___x_3339_);
v___x_3340_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3340_, 0, v___x_3339_);
lean_ctor_set(v___x_3340_, 1, v___x_3339_);
lean_ctor_set(v___x_3340_, 2, v___y_3327_);
return v___x_3340_;
}
}
}
v___jp_3343_:
{
lean_object* v___x_3346_; 
v___x_3346_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2___redArg(v___x_3342_, v___x_3341_, v___y_3344_, v___y_3345_);
lean_dec(v___y_3345_);
v___y_3327_ = v___x_3346_;
goto v___jp_3326_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__3___boxed(lean_object* v_env_3354_, lean_object* v_m_3355_){
_start:
{
lean_object* v_res_3356_; 
v_res_3356_ = l_Lean_registerEnumAttributes___redArg___lam__3(v_env_3354_, v_m_3355_);
lean_dec(v_m_3355_);
return v_res_3356_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__4(lean_object* v_s_3357_, lean_object* v_p_3358_){
_start:
{
lean_object* v_fst_3359_; lean_object* v_snd_3360_; lean_object* v___x_3361_; 
v_fst_3359_ = lean_ctor_get(v_p_3358_, 0);
lean_inc(v_fst_3359_);
v_snd_3360_ = lean_ctor_get(v_p_3358_, 1);
lean_inc(v_snd_3360_);
lean_dec_ref(v_p_3358_);
v___x_3361_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_3359_, v_snd_3360_, v_s_3357_);
return v___x_3361_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__6(lean_object* v___x_3362_, lean_object* v_x_3363_, lean_object* v_x_3364_){
_start:
{
lean_object* v___x_3366_; 
v___x_3366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3366_, 0, v___x_3362_);
return v___x_3366_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__6___boxed(lean_object* v___x_3367_, lean_object* v_x_3368_, lean_object* v_x_3369_, lean_object* v___y_3370_){
_start:
{
lean_object* v_res_3371_; 
v_res_3371_ = l_Lean_registerEnumAttributes___redArg___lam__6(v___x_3367_, v_x_3368_, v_x_3369_);
lean_dec_ref(v_x_3369_);
lean_dec_ref(v_x_3368_);
return v_res_3371_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_registerEnumAttributes_spec__3(lean_object* v_as_3372_){
_start:
{
if (lean_obj_tag(v_as_3372_) == 0)
{
lean_object* v___x_3374_; lean_object* v___x_3375_; 
v___x_3374_ = lean_box(0);
v___x_3375_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3375_, 0, v___x_3374_);
return v___x_3375_;
}
else
{
lean_object* v_head_3376_; lean_object* v_tail_3377_; lean_object* v___x_3378_; 
v_head_3376_ = lean_ctor_get(v_as_3372_, 0);
lean_inc(v_head_3376_);
v_tail_3377_ = lean_ctor_get(v_as_3372_, 1);
lean_inc(v_tail_3377_);
lean_dec_ref_known(v_as_3372_, 2);
v___x_3378_ = l_Lean_registerBuiltinAttribute(v_head_3376_);
if (lean_obj_tag(v___x_3378_) == 0)
{
lean_dec_ref_known(v___x_3378_, 1);
v_as_3372_ = v_tail_3377_;
goto _start;
}
else
{
lean_dec(v_tail_3377_);
return v___x_3378_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_registerEnumAttributes_spec__3___boxed(lean_object* v_as_3380_, lean_object* v___y_3381_){
_start:
{
lean_object* v_res_3382_; 
v_res_3382_ = l_List_forM___at___00Lean_registerEnumAttributes_spec__3(v_as_3380_);
return v_res_3382_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__1(lean_object* v_validate_3383_, lean_object* v_snd_3384_, lean_object* v_a_3385_, lean_object* v_fst_3386_, lean_object* v_decl_3387_, lean_object* v_stx_3388_, uint8_t v_kind_3389_, lean_object* v___y_3390_, lean_object* v___y_3391_){
_start:
{
lean_object* v___y_3394_; lean_object* v___y_3395_; lean_object* v___y_3430_; lean_object* v___y_3431_; lean_object* v___x_3436_; 
v___x_3436_ = l_Lean_Attribute_Builtin_ensureNoArgs(v_stx_3388_, v___y_3390_, v___y_3391_);
if (lean_obj_tag(v___x_3436_) == 0)
{
uint8_t v___x_3437_; uint8_t v___x_3438_; 
lean_dec_ref_known(v___x_3436_, 1);
v___x_3437_ = 0;
v___x_3438_ = l_Lean_instBEqAttributeKind_beq(v_kind_3389_, v___x_3437_);
if (v___x_3438_ == 0)
{
lean_object* v___x_3439_; 
lean_dec(v_decl_3387_);
lean_dec_ref(v_a_3385_);
lean_dec(v_snd_3384_);
lean_dec_ref(v_validate_3383_);
v___x_3439_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg(v_fst_3386_, v_kind_3389_, v___y_3390_, v___y_3391_);
return v___x_3439_;
}
else
{
v___y_3430_ = v___y_3390_;
v___y_3431_ = v___y_3391_;
goto v___jp_3429_;
}
}
else
{
lean_dec(v_decl_3387_);
lean_dec(v_fst_3386_);
lean_dec_ref(v_a_3385_);
lean_dec(v_snd_3384_);
lean_dec_ref(v_validate_3383_);
return v___x_3436_;
}
v___jp_3393_:
{
lean_object* v___x_3396_; 
lean_inc(v___y_3395_);
lean_inc_ref(v___y_3394_);
lean_inc(v_snd_3384_);
lean_inc(v_decl_3387_);
v___x_3396_ = lean_apply_5(v_validate_3383_, v_decl_3387_, v_snd_3384_, v___y_3394_, v___y_3395_, lean_box(0));
if (lean_obj_tag(v___x_3396_) == 0)
{
lean_object* v___x_3398_; uint8_t v_isShared_3399_; uint8_t v_isSharedCheck_3427_; 
v_isSharedCheck_3427_ = !lean_is_exclusive(v___x_3396_);
if (v_isSharedCheck_3427_ == 0)
{
lean_object* v_unused_3428_; 
v_unused_3428_ = lean_ctor_get(v___x_3396_, 0);
lean_dec(v_unused_3428_);
v___x_3398_ = v___x_3396_;
v_isShared_3399_ = v_isSharedCheck_3427_;
goto v_resetjp_3397_;
}
else
{
lean_dec(v___x_3396_);
v___x_3398_ = lean_box(0);
v_isShared_3399_ = v_isSharedCheck_3427_;
goto v_resetjp_3397_;
}
v_resetjp_3397_:
{
lean_object* v___x_3400_; lean_object* v_toEnvExtension_3401_; lean_object* v_env_3402_; lean_object* v_nextMacroScope_3403_; lean_object* v_ngen_3404_; lean_object* v_auxDeclNGen_3405_; lean_object* v_traceState_3406_; lean_object* v_messages_3407_; lean_object* v_infoState_3408_; lean_object* v_snapshotTasks_3409_; lean_object* v___x_3411_; uint8_t v_isShared_3412_; uint8_t v_isSharedCheck_3425_; 
v___x_3400_ = lean_st_ref_take(v___y_3395_);
v_toEnvExtension_3401_ = lean_ctor_get(v_a_3385_, 0);
v_env_3402_ = lean_ctor_get(v___x_3400_, 0);
v_nextMacroScope_3403_ = lean_ctor_get(v___x_3400_, 1);
v_ngen_3404_ = lean_ctor_get(v___x_3400_, 2);
v_auxDeclNGen_3405_ = lean_ctor_get(v___x_3400_, 3);
v_traceState_3406_ = lean_ctor_get(v___x_3400_, 4);
v_messages_3407_ = lean_ctor_get(v___x_3400_, 6);
v_infoState_3408_ = lean_ctor_get(v___x_3400_, 7);
v_snapshotTasks_3409_ = lean_ctor_get(v___x_3400_, 8);
v_isSharedCheck_3425_ = !lean_is_exclusive(v___x_3400_);
if (v_isSharedCheck_3425_ == 0)
{
lean_object* v_unused_3426_; 
v_unused_3426_ = lean_ctor_get(v___x_3400_, 5);
lean_dec(v_unused_3426_);
v___x_3411_ = v___x_3400_;
v_isShared_3412_ = v_isSharedCheck_3425_;
goto v_resetjp_3410_;
}
else
{
lean_inc(v_snapshotTasks_3409_);
lean_inc(v_infoState_3408_);
lean_inc(v_messages_3407_);
lean_inc(v_traceState_3406_);
lean_inc(v_auxDeclNGen_3405_);
lean_inc(v_ngen_3404_);
lean_inc(v_nextMacroScope_3403_);
lean_inc(v_env_3402_);
lean_dec(v___x_3400_);
v___x_3411_ = lean_box(0);
v_isShared_3412_ = v_isSharedCheck_3425_;
goto v_resetjp_3410_;
}
v_resetjp_3410_:
{
lean_object* v_asyncMode_3413_; lean_object* v___x_3414_; lean_object* v___x_3415_; lean_object* v___x_3416_; lean_object* v___x_3418_; 
v_asyncMode_3413_ = lean_ctor_get(v_toEnvExtension_3401_, 2);
lean_inc(v_asyncMode_3413_);
lean_inc(v_decl_3387_);
v___x_3414_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3414_, 0, v_decl_3387_);
lean_ctor_set(v___x_3414_, 1, v_snd_3384_);
v___x_3415_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_a_3385_, v_env_3402_, v___x_3414_, v_asyncMode_3413_, v_decl_3387_);
lean_dec(v_asyncMode_3413_);
v___x_3416_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2);
if (v_isShared_3412_ == 0)
{
lean_ctor_set(v___x_3411_, 5, v___x_3416_);
lean_ctor_set(v___x_3411_, 0, v___x_3415_);
v___x_3418_ = v___x_3411_;
goto v_reusejp_3417_;
}
else
{
lean_object* v_reuseFailAlloc_3424_; 
v_reuseFailAlloc_3424_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3424_, 0, v___x_3415_);
lean_ctor_set(v_reuseFailAlloc_3424_, 1, v_nextMacroScope_3403_);
lean_ctor_set(v_reuseFailAlloc_3424_, 2, v_ngen_3404_);
lean_ctor_set(v_reuseFailAlloc_3424_, 3, v_auxDeclNGen_3405_);
lean_ctor_set(v_reuseFailAlloc_3424_, 4, v_traceState_3406_);
lean_ctor_set(v_reuseFailAlloc_3424_, 5, v___x_3416_);
lean_ctor_set(v_reuseFailAlloc_3424_, 6, v_messages_3407_);
lean_ctor_set(v_reuseFailAlloc_3424_, 7, v_infoState_3408_);
lean_ctor_set(v_reuseFailAlloc_3424_, 8, v_snapshotTasks_3409_);
v___x_3418_ = v_reuseFailAlloc_3424_;
goto v_reusejp_3417_;
}
v_reusejp_3417_:
{
lean_object* v___x_3419_; lean_object* v___x_3420_; lean_object* v___x_3422_; 
v___x_3419_ = lean_st_ref_set(v___y_3395_, v___x_3418_);
v___x_3420_ = lean_box(0);
if (v_isShared_3399_ == 0)
{
lean_ctor_set(v___x_3398_, 0, v___x_3420_);
v___x_3422_ = v___x_3398_;
goto v_reusejp_3421_;
}
else
{
lean_object* v_reuseFailAlloc_3423_; 
v_reuseFailAlloc_3423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3423_, 0, v___x_3420_);
v___x_3422_ = v_reuseFailAlloc_3423_;
goto v_reusejp_3421_;
}
v_reusejp_3421_:
{
return v___x_3422_;
}
}
}
}
}
else
{
lean_dec(v_decl_3387_);
lean_dec_ref(v_a_3385_);
lean_dec(v_snd_3384_);
return v___x_3396_;
}
}
v___jp_3429_:
{
lean_object* v___x_3432_; lean_object* v_env_3433_; lean_object* v___x_3434_; 
v___x_3432_ = lean_st_ref_get(v___y_3431_);
v_env_3433_ = lean_ctor_get(v___x_3432_, 0);
lean_inc_ref(v_env_3433_);
lean_dec(v___x_3432_);
v___x_3434_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3433_, v_decl_3387_);
lean_dec_ref(v_env_3433_);
if (lean_obj_tag(v___x_3434_) == 0)
{
lean_dec(v_fst_3386_);
v___y_3394_ = v___y_3430_;
v___y_3395_ = v___y_3431_;
goto v___jp_3393_;
}
else
{
lean_object* v___x_3435_; 
lean_dec_ref_known(v___x_3434_, 1);
lean_dec_ref(v_a_3385_);
lean_dec(v_snd_3384_);
lean_dec_ref(v_validate_3383_);
v___x_3435_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg(v_fst_3386_, v_decl_3387_, v___y_3430_, v___y_3431_);
return v___x_3435_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__1___boxed(lean_object* v_validate_3440_, lean_object* v_snd_3441_, lean_object* v_a_3442_, lean_object* v_fst_3443_, lean_object* v_decl_3444_, lean_object* v_stx_3445_, lean_object* v_kind_3446_, lean_object* v___y_3447_, lean_object* v___y_3448_, lean_object* v___y_3449_){
_start:
{
uint8_t v_kind_boxed_3450_; lean_object* v_res_3451_; 
v_kind_boxed_3450_ = lean_unbox(v_kind_3446_);
v_res_3451_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__1(v_validate_3440_, v_snd_3441_, v_a_3442_, v_fst_3443_, v_decl_3444_, v_stx_3445_, v_kind_boxed_3450_, v___y_3447_, v___y_3448_);
lean_dec(v___y_3448_);
lean_dec_ref(v___y_3447_);
return v_res_3451_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__0(lean_object* v_fst_3452_, lean_object* v_decl_3453_, lean_object* v___y_3454_, lean_object* v___y_3455_){
_start:
{
lean_object* v___x_3457_; lean_object* v___x_3458_; lean_object* v___x_3459_; lean_object* v___x_3460_; lean_object* v___x_3461_; lean_object* v___x_3462_; 
v___x_3457_ = lean_obj_once(&l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1, &l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1_once, _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1);
v___x_3458_ = l_Lean_MessageData_ofName(v_fst_3452_);
v___x_3459_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3459_, 0, v___x_3457_);
lean_ctor_set(v___x_3459_, 1, v___x_3458_);
v___x_3460_ = lean_obj_once(&l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3, &l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3_once, _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3);
v___x_3461_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3461_, 0, v___x_3459_);
lean_ctor_set(v___x_3461_, 1, v___x_3460_);
v___x_3462_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_3461_, v___y_3454_, v___y_3455_);
return v___x_3462_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__0___boxed(lean_object* v_fst_3463_, lean_object* v_decl_3464_, lean_object* v___y_3465_, lean_object* v___y_3466_, lean_object* v___y_3467_){
_start:
{
lean_object* v_res_3468_; 
v_res_3468_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__0(v_fst_3463_, v_decl_3464_, v___y_3465_, v___y_3466_);
lean_dec(v___y_3466_);
lean_dec_ref(v___y_3465_);
lean_dec(v_decl_3464_);
return v_res_3468_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg(lean_object* v_validate_3469_, lean_object* v_a_3470_, lean_object* v_ref_3471_, uint8_t v_applicationTime_3472_, lean_object* v_a_3473_, lean_object* v_a_3474_){
_start:
{
if (lean_obj_tag(v_a_3473_) == 0)
{
lean_object* v___x_3475_; 
lean_dec(v_ref_3471_);
lean_dec_ref(v_a_3470_);
lean_dec_ref(v_validate_3469_);
v___x_3475_ = l_List_reverse___redArg(v_a_3474_);
return v___x_3475_;
}
else
{
lean_object* v_head_3476_; lean_object* v_snd_3477_; lean_object* v_tail_3478_; lean_object* v___x_3480_; uint8_t v_isShared_3481_; uint8_t v_isSharedCheck_3493_; 
v_head_3476_ = lean_ctor_get(v_a_3473_, 0);
lean_inc(v_head_3476_);
v_snd_3477_ = lean_ctor_get(v_head_3476_, 1);
lean_inc(v_snd_3477_);
v_tail_3478_ = lean_ctor_get(v_a_3473_, 1);
v_isSharedCheck_3493_ = !lean_is_exclusive(v_a_3473_);
if (v_isSharedCheck_3493_ == 0)
{
lean_object* v_unused_3494_; 
v_unused_3494_ = lean_ctor_get(v_a_3473_, 0);
lean_dec(v_unused_3494_);
v___x_3480_ = v_a_3473_;
v_isShared_3481_ = v_isSharedCheck_3493_;
goto v_resetjp_3479_;
}
else
{
lean_inc(v_tail_3478_);
lean_dec(v_a_3473_);
v___x_3480_ = lean_box(0);
v_isShared_3481_ = v_isSharedCheck_3493_;
goto v_resetjp_3479_;
}
v_resetjp_3479_:
{
lean_object* v_fst_3482_; lean_object* v_fst_3483_; lean_object* v_snd_3484_; lean_object* v___f_3485_; lean_object* v___f_3486_; lean_object* v___x_3487_; lean_object* v___x_3488_; lean_object* v___x_3490_; 
v_fst_3482_ = lean_ctor_get(v_head_3476_, 0);
lean_inc_n(v_fst_3482_, 3);
lean_dec(v_head_3476_);
v_fst_3483_ = lean_ctor_get(v_snd_3477_, 0);
lean_inc(v_fst_3483_);
v_snd_3484_ = lean_ctor_get(v_snd_3477_, 1);
lean_inc(v_snd_3484_);
lean_dec(v_snd_3477_);
v___f_3485_ = lean_alloc_closure((void*)(l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__0___boxed), 5, 1);
lean_closure_set(v___f_3485_, 0, v_fst_3482_);
lean_inc_ref(v_a_3470_);
lean_inc_ref(v_validate_3469_);
v___f_3486_ = lean_alloc_closure((void*)(l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__1___boxed), 10, 4);
lean_closure_set(v___f_3486_, 0, v_validate_3469_);
lean_closure_set(v___f_3486_, 1, v_snd_3484_);
lean_closure_set(v___f_3486_, 2, v_a_3470_);
lean_closure_set(v___f_3486_, 3, v_fst_3482_);
lean_inc(v_ref_3471_);
v___x_3487_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_3487_, 0, v_ref_3471_);
lean_ctor_set(v___x_3487_, 1, v_fst_3482_);
lean_ctor_set(v___x_3487_, 2, v_fst_3483_);
lean_ctor_set_uint8(v___x_3487_, sizeof(void*)*3, v_applicationTime_3472_);
v___x_3488_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3488_, 0, v___x_3487_);
lean_ctor_set(v___x_3488_, 1, v___f_3486_);
lean_ctor_set(v___x_3488_, 2, v___f_3485_);
if (v_isShared_3481_ == 0)
{
lean_ctor_set(v___x_3480_, 1, v_a_3474_);
lean_ctor_set(v___x_3480_, 0, v___x_3488_);
v___x_3490_ = v___x_3480_;
goto v_reusejp_3489_;
}
else
{
lean_object* v_reuseFailAlloc_3492_; 
v_reuseFailAlloc_3492_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3492_, 0, v___x_3488_);
lean_ctor_set(v_reuseFailAlloc_3492_, 1, v_a_3474_);
v___x_3490_ = v_reuseFailAlloc_3492_;
goto v_reusejp_3489_;
}
v_reusejp_3489_:
{
v_a_3473_ = v_tail_3478_;
v_a_3474_ = v___x_3490_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___boxed(lean_object* v_validate_3495_, lean_object* v_a_3496_, lean_object* v_ref_3497_, lean_object* v_applicationTime_3498_, lean_object* v_a_3499_, lean_object* v_a_3500_){
_start:
{
uint8_t v_applicationTime_boxed_3501_; lean_object* v_res_3502_; 
v_applicationTime_boxed_3501_ = lean_unbox(v_applicationTime_3498_);
v_res_3502_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg(v_validate_3495_, v_a_3496_, v_ref_3497_, v_applicationTime_boxed_3501_, v_a_3499_, v_a_3500_);
return v_res_3502_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg(lean_object* v_attrDescrs_3516_, lean_object* v_validate_3517_, uint8_t v_applicationTime_3518_, lean_object* v_ref_3519_){
_start:
{
lean_object* v___f_3521_; lean_object* v___f_3522_; lean_object* v___f_3523_; lean_object* v___f_3524_; lean_object* v___f_3525_; lean_object* v___f_3526_; lean_object* v___x_3527_; lean_object* v___x_3528_; lean_object* v___x_3529_; lean_object* v___x_3530_; lean_object* v___x_3531_; 
v___f_3521_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__0));
v___f_3522_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__2));
v___f_3523_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__3));
v___f_3524_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__4));
v___f_3525_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__5));
v___f_3526_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__6));
v___x_3527_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__7));
v___x_3528_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__8));
lean_inc(v_ref_3519_);
v___x_3529_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_3529_, 0, v_ref_3519_);
lean_ctor_set(v___x_3529_, 1, v___f_3525_);
lean_ctor_set(v___x_3529_, 2, v___f_3526_);
lean_ctor_set(v___x_3529_, 3, v___f_3524_);
lean_ctor_set(v___x_3529_, 4, v___f_3523_);
lean_ctor_set(v___x_3529_, 5, v___f_3522_);
lean_ctor_set(v___x_3529_, 6, v___x_3527_);
lean_ctor_set(v___x_3529_, 7, v___x_3528_);
v___x_3530_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3530_, 0, v___x_3529_);
lean_ctor_set(v___x_3530_, 1, v___f_3521_);
v___x_3531_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_3530_);
if (lean_obj_tag(v___x_3531_) == 0)
{
lean_object* v_a_3532_; lean_object* v___x_3533_; lean_object* v___x_3534_; lean_object* v___x_3535_; 
v_a_3532_ = lean_ctor_get(v___x_3531_, 0);
lean_inc_n(v_a_3532_, 2);
lean_dec_ref_known(v___x_3531_, 1);
v___x_3533_ = lean_box(0);
v___x_3534_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg(v_validate_3517_, v_a_3532_, v_ref_3519_, v_applicationTime_3518_, v_attrDescrs_3516_, v___x_3533_);
lean_inc(v___x_3534_);
v___x_3535_ = l_List_forM___at___00Lean_registerEnumAttributes_spec__3(v___x_3534_);
if (lean_obj_tag(v___x_3535_) == 0)
{
lean_object* v___x_3537_; uint8_t v_isShared_3538_; uint8_t v_isSharedCheck_3543_; 
v_isSharedCheck_3543_ = !lean_is_exclusive(v___x_3535_);
if (v_isSharedCheck_3543_ == 0)
{
lean_object* v_unused_3544_; 
v_unused_3544_ = lean_ctor_get(v___x_3535_, 0);
lean_dec(v_unused_3544_);
v___x_3537_ = v___x_3535_;
v_isShared_3538_ = v_isSharedCheck_3543_;
goto v_resetjp_3536_;
}
else
{
lean_dec(v___x_3535_);
v___x_3537_ = lean_box(0);
v_isShared_3538_ = v_isSharedCheck_3543_;
goto v_resetjp_3536_;
}
v_resetjp_3536_:
{
lean_object* v___x_3539_; lean_object* v___x_3541_; 
v___x_3539_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3539_, 0, v___x_3534_);
lean_ctor_set(v___x_3539_, 1, v_a_3532_);
if (v_isShared_3538_ == 0)
{
lean_ctor_set(v___x_3537_, 0, v___x_3539_);
v___x_3541_ = v___x_3537_;
goto v_reusejp_3540_;
}
else
{
lean_object* v_reuseFailAlloc_3542_; 
v_reuseFailAlloc_3542_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3542_, 0, v___x_3539_);
v___x_3541_ = v_reuseFailAlloc_3542_;
goto v_reusejp_3540_;
}
v_reusejp_3540_:
{
return v___x_3541_;
}
}
}
else
{
lean_object* v_a_3545_; lean_object* v___x_3547_; uint8_t v_isShared_3548_; uint8_t v_isSharedCheck_3552_; 
lean_dec(v___x_3534_);
lean_dec(v_a_3532_);
v_a_3545_ = lean_ctor_get(v___x_3535_, 0);
v_isSharedCheck_3552_ = !lean_is_exclusive(v___x_3535_);
if (v_isSharedCheck_3552_ == 0)
{
v___x_3547_ = v___x_3535_;
v_isShared_3548_ = v_isSharedCheck_3552_;
goto v_resetjp_3546_;
}
else
{
lean_inc(v_a_3545_);
lean_dec(v___x_3535_);
v___x_3547_ = lean_box(0);
v_isShared_3548_ = v_isSharedCheck_3552_;
goto v_resetjp_3546_;
}
v_resetjp_3546_:
{
lean_object* v___x_3550_; 
if (v_isShared_3548_ == 0)
{
v___x_3550_ = v___x_3547_;
goto v_reusejp_3549_;
}
else
{
lean_object* v_reuseFailAlloc_3551_; 
v_reuseFailAlloc_3551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3551_, 0, v_a_3545_);
v___x_3550_ = v_reuseFailAlloc_3551_;
goto v_reusejp_3549_;
}
v_reusejp_3549_:
{
return v___x_3550_;
}
}
}
}
else
{
lean_object* v_a_3553_; lean_object* v___x_3555_; uint8_t v_isShared_3556_; uint8_t v_isSharedCheck_3560_; 
lean_dec(v_ref_3519_);
lean_dec_ref(v_validate_3517_);
lean_dec(v_attrDescrs_3516_);
v_a_3553_ = lean_ctor_get(v___x_3531_, 0);
v_isSharedCheck_3560_ = !lean_is_exclusive(v___x_3531_);
if (v_isSharedCheck_3560_ == 0)
{
v___x_3555_ = v___x_3531_;
v_isShared_3556_ = v_isSharedCheck_3560_;
goto v_resetjp_3554_;
}
else
{
lean_inc(v_a_3553_);
lean_dec(v___x_3531_);
v___x_3555_ = lean_box(0);
v_isShared_3556_ = v_isSharedCheck_3560_;
goto v_resetjp_3554_;
}
v_resetjp_3554_:
{
lean_object* v___x_3558_; 
if (v_isShared_3556_ == 0)
{
v___x_3558_ = v___x_3555_;
goto v_reusejp_3557_;
}
else
{
lean_object* v_reuseFailAlloc_3559_; 
v_reuseFailAlloc_3559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3559_, 0, v_a_3553_);
v___x_3558_ = v_reuseFailAlloc_3559_;
goto v_reusejp_3557_;
}
v_reusejp_3557_:
{
return v___x_3558_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___boxed(lean_object* v_attrDescrs_3561_, lean_object* v_validate_3562_, lean_object* v_applicationTime_3563_, lean_object* v_ref_3564_, lean_object* v_a_3565_){
_start:
{
uint8_t v_applicationTime_boxed_3566_; lean_object* v_res_3567_; 
v_applicationTime_boxed_3566_ = lean_unbox(v_applicationTime_3563_);
v_res_3567_ = l_Lean_registerEnumAttributes___redArg(v_attrDescrs_3561_, v_validate_3562_, v_applicationTime_boxed_3566_, v_ref_3564_);
return v_res_3567_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes(lean_object* v_00_u03b1_3568_, lean_object* v_attrDescrs_3569_, lean_object* v_validate_3570_, uint8_t v_applicationTime_3571_, lean_object* v_ref_3572_){
_start:
{
lean_object* v___x_3574_; 
v___x_3574_ = l_Lean_registerEnumAttributes___redArg(v_attrDescrs_3569_, v_validate_3570_, v_applicationTime_3571_, v_ref_3572_);
return v___x_3574_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___boxed(lean_object* v_00_u03b1_3575_, lean_object* v_attrDescrs_3576_, lean_object* v_validate_3577_, lean_object* v_applicationTime_3578_, lean_object* v_ref_3579_, lean_object* v_a_3580_){
_start:
{
uint8_t v_applicationTime_boxed_3581_; lean_object* v_res_3582_; 
v_applicationTime_boxed_3581_ = lean_unbox(v_applicationTime_3578_);
v_res_3582_ = l_Lean_registerEnumAttributes(v_00_u03b1_3575_, v_attrDescrs_3576_, v_validate_3577_, v_applicationTime_boxed_3581_, v_ref_3579_);
return v_res_3582_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0(lean_object* v_00_u03b1_3583_, lean_object* v_env_3584_, lean_object* v_as_3585_, size_t v_i_3586_, size_t v_stop_3587_, lean_object* v_b_3588_){
_start:
{
lean_object* v___x_3589_; 
v___x_3589_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg(v_env_3584_, v_as_3585_, v_i_3586_, v_stop_3587_, v_b_3588_);
return v___x_3589_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___boxed(lean_object* v_00_u03b1_3590_, lean_object* v_env_3591_, lean_object* v_as_3592_, lean_object* v_i_3593_, lean_object* v_stop_3594_, lean_object* v_b_3595_){
_start:
{
size_t v_i_boxed_3596_; size_t v_stop_boxed_3597_; lean_object* v_res_3598_; 
v_i_boxed_3596_ = lean_unbox_usize(v_i_3593_);
lean_dec(v_i_3593_);
v_stop_boxed_3597_ = lean_unbox_usize(v_stop_3594_);
lean_dec(v_stop_3594_);
v_res_3598_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0(v_00_u03b1_3590_, v_env_3591_, v_as_3592_, v_i_boxed_3596_, v_stop_boxed_3597_, v_b_3595_);
lean_dec_ref(v_as_3592_);
return v_res_3598_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerEnumAttributes_spec__1(lean_object* v_00_u03b1_3599_, lean_object* v_newState_3600_, lean_object* v_x_3601_, lean_object* v_x_3602_){
_start:
{
lean_object* v___x_3603_; 
v___x_3603_ = l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___redArg(v_newState_3600_, v_x_3601_, v_x_3602_);
return v___x_3603_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___boxed(lean_object* v_00_u03b1_3604_, lean_object* v_newState_3605_, lean_object* v_x_3606_, lean_object* v_x_3607_){
_start:
{
lean_object* v_res_3608_; 
v_res_3608_ = l_List_foldl___at___00Lean_registerEnumAttributes_spec__1(v_00_u03b1_3604_, v_newState_3605_, v_x_3606_, v_x_3607_);
lean_dec(v_newState_3605_);
return v_res_3608_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2(lean_object* v_00_u03b1_3609_, lean_object* v_validate_3610_, lean_object* v_a_3611_, lean_object* v_ref_3612_, uint8_t v_applicationTime_3613_, lean_object* v_a_3614_, lean_object* v_a_3615_){
_start:
{
lean_object* v___x_3616_; 
v___x_3616_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg(v_validate_3610_, v_a_3611_, v_ref_3612_, v_applicationTime_3613_, v_a_3614_, v_a_3615_);
return v___x_3616_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___boxed(lean_object* v_00_u03b1_3617_, lean_object* v_validate_3618_, lean_object* v_a_3619_, lean_object* v_ref_3620_, lean_object* v_applicationTime_3621_, lean_object* v_a_3622_, lean_object* v_a_3623_){
_start:
{
uint8_t v_applicationTime_boxed_3624_; lean_object* v_res_3625_; 
v_applicationTime_boxed_3624_ = lean_unbox(v_applicationTime_3621_);
v_res_3625_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2(v_00_u03b1_3617_, v_validate_3618_, v_a_3619_, v_ref_3620_, v_applicationTime_boxed_3624_, v_a_3622_, v_a_3623_);
return v_res_3625_;
}
}
LEAN_EXPORT lean_object* l_Lean_EnumAttributes_getValue___redArg(lean_object* v_inst_3626_, lean_object* v_attr_3627_, lean_object* v_env_3628_, lean_object* v_decl_3629_){
_start:
{
lean_object* v___x_3630_; lean_object* v___x_3631_; 
v___x_3630_ = lean_box(1);
v___x_3631_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3628_, v_decl_3629_);
if (lean_obj_tag(v___x_3631_) == 0)
{
lean_object* v_ext_3632_; lean_object* v_toEnvExtension_3633_; lean_object* v_asyncMode_3634_; lean_object* v___x_3635_; lean_object* v___x_3636_; 
lean_dec(v_inst_3626_);
v_ext_3632_ = lean_ctor_get(v_attr_3627_, 1);
lean_inc_ref(v_ext_3632_);
lean_dec_ref(v_attr_3627_);
v_toEnvExtension_3633_ = lean_ctor_get(v_ext_3632_, 0);
v_asyncMode_3634_ = lean_ctor_get(v_toEnvExtension_3633_, 2);
lean_inc(v_asyncMode_3634_);
lean_inc(v_decl_3629_);
v___x_3635_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3630_, v_ext_3632_, v_env_3628_, v_asyncMode_3634_, v_decl_3629_);
lean_dec(v_asyncMode_3634_);
lean_dec_ref(v_ext_3632_);
v___x_3636_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_3635_, v_decl_3629_);
lean_dec(v_decl_3629_);
lean_dec(v___x_3635_);
return v___x_3636_;
}
else
{
lean_object* v_val_3637_; lean_object* v_ext_3638_; lean_object* v___x_3640_; uint8_t v_isShared_3641_; uint8_t v_isSharedCheck_3668_; 
v_val_3637_ = lean_ctor_get(v___x_3631_, 0);
lean_inc(v_val_3637_);
lean_dec_ref_known(v___x_3631_, 1);
v_ext_3638_ = lean_ctor_get(v_attr_3627_, 1);
v_isSharedCheck_3668_ = !lean_is_exclusive(v_attr_3627_);
if (v_isSharedCheck_3668_ == 0)
{
lean_object* v_unused_3669_; 
v_unused_3669_ = lean_ctor_get(v_attr_3627_, 0);
lean_dec(v_unused_3669_);
v___x_3640_ = v_attr_3627_;
v_isShared_3641_ = v_isSharedCheck_3668_;
goto v_resetjp_3639_;
}
else
{
lean_inc(v_ext_3638_);
lean_dec(v_attr_3627_);
v___x_3640_ = lean_box(0);
v_isShared_3641_ = v_isSharedCheck_3668_;
goto v_resetjp_3639_;
}
v_resetjp_3639_:
{
uint8_t v___x_3642_; lean_object* v___x_3643_; lean_object* v___x_3644_; lean_object* v___x_3645_; uint8_t v___x_3646_; 
v___x_3642_ = 0;
v___x_3643_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_3630_, v_ext_3638_, v_env_3628_, v_val_3637_, v___x_3642_);
lean_dec(v_val_3637_);
lean_dec_ref(v_env_3628_);
lean_dec_ref(v_ext_3638_);
v___x_3644_ = lean_unsigned_to_nat(0u);
v___x_3645_ = lean_array_get_size(v___x_3643_);
v___x_3646_ = lean_nat_dec_lt(v___x_3644_, v___x_3645_);
if (v___x_3646_ == 0)
{
lean_object* v___x_3647_; 
lean_dec_ref(v___x_3643_);
lean_del_object(v___x_3640_);
lean_dec(v_decl_3629_);
lean_dec(v_inst_3626_);
v___x_3647_ = lean_box(0);
return v___x_3647_;
}
else
{
lean_object* v___x_3648_; lean_object* v___x_3649_; uint8_t v___x_3650_; 
v___x_3648_ = lean_unsigned_to_nat(1u);
v___x_3649_ = lean_nat_sub(v___x_3645_, v___x_3648_);
v___x_3650_ = lean_nat_dec_le(v___x_3644_, v___x_3649_);
if (v___x_3650_ == 0)
{
lean_object* v___x_3651_; 
lean_dec(v___x_3649_);
lean_dec_ref(v___x_3643_);
lean_del_object(v___x_3640_);
lean_dec(v_decl_3629_);
lean_dec(v_inst_3626_);
v___x_3651_ = lean_box(0);
return v___x_3651_;
}
else
{
lean_object* v___f_3652_; lean_object* v___x_3654_; 
v___f_3652_ = ((lean_object*)(l_Lean_ParametricAttribute_getParam_x3f___redArg___closed__1));
if (v_isShared_3641_ == 0)
{
lean_ctor_set(v___x_3640_, 1, v_inst_3626_);
lean_ctor_set(v___x_3640_, 0, v_decl_3629_);
v___x_3654_ = v___x_3640_;
goto v_reusejp_3653_;
}
else
{
lean_object* v_reuseFailAlloc_3667_; 
v_reuseFailAlloc_3667_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3667_, 0, v_decl_3629_);
lean_ctor_set(v_reuseFailAlloc_3667_, 1, v_inst_3626_);
v___x_3654_ = v_reuseFailAlloc_3667_;
goto v_reusejp_3653_;
}
v_reusejp_3653_:
{
lean_object* v___x_3655_; lean_object* v___x_3656_; 
v___x_3655_ = ((lean_object*)(l_Lean_ParametricAttribute_getParam_x3f___redArg___closed__2));
v___x_3656_ = l_Array_binSearchAux___redArg(v___f_3652_, v___x_3655_, v___x_3643_, v___x_3654_, v___x_3644_, v___x_3649_);
lean_dec_ref(v___x_3643_);
if (lean_obj_tag(v___x_3656_) == 0)
{
lean_object* v___x_3657_; 
v___x_3657_ = lean_box(0);
return v___x_3657_;
}
else
{
lean_object* v_val_3658_; lean_object* v___x_3660_; uint8_t v_isShared_3661_; uint8_t v_isSharedCheck_3666_; 
v_val_3658_ = lean_ctor_get(v___x_3656_, 0);
v_isSharedCheck_3666_ = !lean_is_exclusive(v___x_3656_);
if (v_isSharedCheck_3666_ == 0)
{
v___x_3660_ = v___x_3656_;
v_isShared_3661_ = v_isSharedCheck_3666_;
goto v_resetjp_3659_;
}
else
{
lean_inc(v_val_3658_);
lean_dec(v___x_3656_);
v___x_3660_ = lean_box(0);
v_isShared_3661_ = v_isSharedCheck_3666_;
goto v_resetjp_3659_;
}
v_resetjp_3659_:
{
lean_object* v_snd_3662_; lean_object* v___x_3664_; 
v_snd_3662_ = lean_ctor_get(v_val_3658_, 1);
lean_inc(v_snd_3662_);
lean_dec(v_val_3658_);
if (v_isShared_3661_ == 0)
{
lean_ctor_set(v___x_3660_, 0, v_snd_3662_);
v___x_3664_ = v___x_3660_;
goto v_reusejp_3663_;
}
else
{
lean_object* v_reuseFailAlloc_3665_; 
v_reuseFailAlloc_3665_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3665_, 0, v_snd_3662_);
v___x_3664_ = v_reuseFailAlloc_3665_;
goto v_reusejp_3663_;
}
v_reusejp_3663_:
{
return v___x_3664_;
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
LEAN_EXPORT lean_object* l_Lean_EnumAttributes_getValue(lean_object* v_00_u03b1_3670_, lean_object* v_inst_3671_, lean_object* v_attr_3672_, lean_object* v_env_3673_, lean_object* v_decl_3674_){
_start:
{
lean_object* v___x_3675_; 
v___x_3675_ = l_Lean_EnumAttributes_getValue___redArg(v_inst_3671_, v_attr_3672_, v_env_3673_, v_decl_3674_);
return v___x_3675_;
}
}
LEAN_EXPORT lean_object* l_Lean_EnumAttributes_setValue___redArg(lean_object* v_attrs_3684_, lean_object* v_env_3685_, lean_object* v_decl_3686_, lean_object* v_val_3687_){
_start:
{
lean_object* v_ext_3688_; lean_object* v___x_3690_; uint8_t v_isShared_3691_; uint8_t v_isSharedCheck_3752_; 
v_ext_3688_ = lean_ctor_get(v_attrs_3684_, 1);
v_isSharedCheck_3752_ = !lean_is_exclusive(v_attrs_3684_);
if (v_isSharedCheck_3752_ == 0)
{
lean_object* v_unused_3753_; 
v_unused_3753_ = lean_ctor_get(v_attrs_3684_, 0);
lean_dec(v_unused_3753_);
v___x_3690_ = v_attrs_3684_;
v_isShared_3691_ = v_isSharedCheck_3752_;
goto v_resetjp_3689_;
}
else
{
lean_inc(v_ext_3688_);
lean_dec(v_attrs_3684_);
v___x_3690_ = lean_box(0);
v_isShared_3691_ = v_isSharedCheck_3752_;
goto v_resetjp_3689_;
}
v_resetjp_3689_:
{
lean_object* v_toEnvExtension_3692_; lean_object* v_name_3693_; lean_object* v___x_3694_; uint8_t v___x_3695_; lean_object* v___x_3696_; lean_object* v___x_3697_; lean_object* v___x_3698_; lean_object* v___x_3699_; lean_object* v___x_3700_; lean_object* v___x_3701_; lean_object* v___x_3702_; lean_object* v_pfx_3703_; lean_object* v___x_3704_; 
v_toEnvExtension_3692_ = lean_ctor_get(v_ext_3688_, 0);
v_name_3693_ = lean_ctor_get(v_ext_3688_, 1);
v___x_3694_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__0));
v___x_3695_ = 1;
lean_inc(v_name_3693_);
v___x_3696_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_3693_, v___x_3695_);
v___x_3697_ = lean_string_append(v___x_3694_, v___x_3696_);
lean_dec_ref(v___x_3696_);
v___x_3698_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__1));
v___x_3699_ = lean_string_append(v___x_3697_, v___x_3698_);
lean_inc(v_decl_3686_);
v___x_3700_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_decl_3686_, v___x_3695_);
v___x_3701_ = lean_string_append(v___x_3699_, v___x_3700_);
lean_dec_ref(v___x_3700_);
v___x_3702_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__4));
v_pfx_3703_ = lean_string_append(v___x_3701_, v___x_3702_);
v___x_3704_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3685_, v_decl_3686_);
if (lean_obj_tag(v___x_3704_) == 0)
{
lean_object* v_asyncMode_3705_; uint8_t v___x_3712_; 
v_asyncMode_3705_ = lean_ctor_get(v_toEnvExtension_3692_, 2);
lean_inc(v_asyncMode_3705_);
lean_inc(v_decl_3686_);
lean_inc_ref(v_env_3685_);
v___x_3712_ = l_Lean_EnvExtension_asyncMayModify___redArg(v_env_3685_, v_decl_3686_, v_asyncMode_3705_);
if (v___x_3712_ == 0)
{
lean_object* v___x_3713_; lean_object* v___x_3714_; lean_object* v___y_3716_; lean_object* v___x_3720_; 
lean_dec(v_asyncMode_3705_);
lean_del_object(v___x_3690_);
lean_dec_ref(v_ext_3688_);
lean_dec(v_val_3687_);
lean_dec(v_decl_3686_);
v___x_3713_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__2));
v___x_3714_ = lean_string_append(v_pfx_3703_, v___x_3713_);
v___x_3720_ = l_Lean_Environment_asyncPrefix_x3f(v_env_3685_);
if (lean_obj_tag(v___x_3720_) == 0)
{
lean_object* v___x_3721_; 
v___x_3721_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__3));
v___y_3716_ = v___x_3721_;
goto v___jp_3715_;
}
else
{
lean_object* v_val_3722_; lean_object* v___x_3723_; lean_object* v___x_3724_; lean_object* v___x_3725_; lean_object* v___x_3726_; lean_object* v___x_3727_; lean_object* v___x_3728_; 
v_val_3722_ = lean_ctor_get(v___x_3720_, 0);
lean_inc(v_val_3722_);
lean_dec_ref_known(v___x_3720_, 1);
v___x_3723_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__4));
v___x_3724_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_val_3722_, v___x_3695_);
v___x_3725_ = l_addParenHeuristic(v___x_3724_);
v___x_3726_ = lean_string_append(v___x_3723_, v___x_3725_);
lean_dec_ref(v___x_3725_);
v___x_3727_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__5));
v___x_3728_ = lean_string_append(v___x_3726_, v___x_3727_);
v___y_3716_ = v___x_3728_;
goto v___jp_3715_;
}
v___jp_3715_:
{
lean_object* v___x_3717_; lean_object* v___x_3718_; lean_object* v___x_3719_; 
v___x_3717_ = lean_string_append(v___x_3714_, v___y_3716_);
lean_dec_ref(v___y_3716_);
v___x_3718_ = lean_string_append(v___x_3717_, v___x_3702_);
v___x_3719_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3719_, 0, v___x_3718_);
return v___x_3719_;
}
}
else
{
lean_object* v___x_3729_; lean_object* v___x_3730_; lean_object* v___x_3731_; 
v___x_3729_ = lean_box(1);
lean_inc(v_decl_3686_);
lean_inc_ref(v_env_3685_);
v___x_3730_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3729_, v_ext_3688_, v_env_3685_, v_asyncMode_3705_, v_decl_3686_);
v___x_3731_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_3730_, v_decl_3686_);
lean_dec(v___x_3730_);
if (lean_obj_tag(v___x_3731_) == 0)
{
lean_dec_ref(v_pfx_3703_);
goto v___jp_3706_;
}
else
{
lean_object* v___x_3733_; uint8_t v_isShared_3734_; uint8_t v_isSharedCheck_3740_; 
v_isSharedCheck_3740_ = !lean_is_exclusive(v___x_3731_);
if (v_isSharedCheck_3740_ == 0)
{
lean_object* v_unused_3741_; 
v_unused_3741_ = lean_ctor_get(v___x_3731_, 0);
lean_dec(v_unused_3741_);
v___x_3733_ = v___x_3731_;
v_isShared_3734_ = v_isSharedCheck_3740_;
goto v_resetjp_3732_;
}
else
{
lean_dec(v___x_3731_);
v___x_3733_ = lean_box(0);
v_isShared_3734_ = v_isSharedCheck_3740_;
goto v_resetjp_3732_;
}
v_resetjp_3732_:
{
if (v___x_3712_ == 0)
{
lean_del_object(v___x_3733_);
lean_dec_ref(v_pfx_3703_);
goto v___jp_3706_;
}
else
{
lean_object* v___x_3735_; lean_object* v___x_3736_; lean_object* v___x_3738_; 
lean_dec(v_asyncMode_3705_);
lean_del_object(v___x_3690_);
lean_dec_ref(v_ext_3688_);
lean_dec(v_val_3687_);
lean_dec(v_decl_3686_);
lean_dec_ref(v_env_3685_);
v___x_3735_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__6));
v___x_3736_ = lean_string_append(v_pfx_3703_, v___x_3735_);
if (v_isShared_3734_ == 0)
{
lean_ctor_set_tag(v___x_3733_, 0);
lean_ctor_set(v___x_3733_, 0, v___x_3736_);
v___x_3738_ = v___x_3733_;
goto v_reusejp_3737_;
}
else
{
lean_object* v_reuseFailAlloc_3739_; 
v_reuseFailAlloc_3739_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3739_, 0, v___x_3736_);
v___x_3738_ = v_reuseFailAlloc_3739_;
goto v_reusejp_3737_;
}
v_reusejp_3737_:
{
return v___x_3738_;
}
}
}
}
}
v___jp_3706_:
{
lean_object* v___x_3708_; 
lean_inc(v_decl_3686_);
if (v_isShared_3691_ == 0)
{
lean_ctor_set(v___x_3690_, 1, v_val_3687_);
lean_ctor_set(v___x_3690_, 0, v_decl_3686_);
v___x_3708_ = v___x_3690_;
goto v_reusejp_3707_;
}
else
{
lean_object* v_reuseFailAlloc_3711_; 
v_reuseFailAlloc_3711_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3711_, 0, v_decl_3686_);
lean_ctor_set(v_reuseFailAlloc_3711_, 1, v_val_3687_);
v___x_3708_ = v_reuseFailAlloc_3711_;
goto v_reusejp_3707_;
}
v_reusejp_3707_:
{
lean_object* v___x_3709_; lean_object* v___x_3710_; 
v___x_3709_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_ext_3688_, v_env_3685_, v___x_3708_, v_asyncMode_3705_, v_decl_3686_);
lean_dec(v_asyncMode_3705_);
v___x_3710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3710_, 0, v___x_3709_);
return v___x_3710_;
}
}
}
else
{
lean_object* v___x_3743_; uint8_t v_isShared_3744_; uint8_t v_isSharedCheck_3750_; 
lean_del_object(v___x_3690_);
lean_dec_ref(v_ext_3688_);
lean_dec(v_val_3687_);
lean_dec(v_decl_3686_);
lean_dec_ref(v_env_3685_);
v_isSharedCheck_3750_ = !lean_is_exclusive(v___x_3704_);
if (v_isSharedCheck_3750_ == 0)
{
lean_object* v_unused_3751_; 
v_unused_3751_ = lean_ctor_get(v___x_3704_, 0);
lean_dec(v_unused_3751_);
v___x_3743_ = v___x_3704_;
v_isShared_3744_ = v_isSharedCheck_3750_;
goto v_resetjp_3742_;
}
else
{
lean_dec(v___x_3704_);
v___x_3743_ = lean_box(0);
v_isShared_3744_ = v_isSharedCheck_3750_;
goto v_resetjp_3742_;
}
v_resetjp_3742_:
{
lean_object* v___x_3745_; lean_object* v___x_3746_; lean_object* v___x_3748_; 
v___x_3745_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__7));
v___x_3746_ = lean_string_append(v_pfx_3703_, v___x_3745_);
if (v_isShared_3744_ == 0)
{
lean_ctor_set_tag(v___x_3743_, 0);
lean_ctor_set(v___x_3743_, 0, v___x_3746_);
v___x_3748_ = v___x_3743_;
goto v_reusejp_3747_;
}
else
{
lean_object* v_reuseFailAlloc_3749_; 
v_reuseFailAlloc_3749_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3749_, 0, v___x_3746_);
v___x_3748_ = v_reuseFailAlloc_3749_;
goto v_reusejp_3747_;
}
v_reusejp_3747_:
{
return v___x_3748_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_EnumAttributes_setValue(lean_object* v_00_u03b1_3754_, lean_object* v_attrs_3755_, lean_object* v_env_3756_, lean_object* v_decl_3757_, lean_object* v_val_3758_){
_start:
{
lean_object* v___x_3759_; 
v___x_3759_ = l_Lean_EnumAttributes_setValue___redArg(v_attrs_3755_, v_env_3756_, v_decl_3757_, v_val_3758_);
return v___x_3759_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_2990505691____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3761_; lean_object* v___x_3762_; lean_object* v___x_3763_; 
v___x_3761_ = lean_obj_once(&l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_, &l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2__once, _init_l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_);
v___x_3762_ = lean_st_mk_ref(v___x_3761_);
v___x_3763_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3763_, 0, v___x_3762_);
return v___x_3763_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_2990505691____hygCtx___hyg_2____boxed(lean_object* v_a_3764_){
_start:
{
lean_object* v_res_3765_; 
v_res_3765_ = l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_2990505691____hygCtx___hyg_2_();
return v_res_3765_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerAttributeImplBuilder(lean_object* v_builderId_3768_, lean_object* v_builder_3769_){
_start:
{
lean_object* v___x_3771_; lean_object* v___x_3772_; uint8_t v___x_3773_; 
v___x_3771_ = l_Lean_attributeImplBuilderTableRef;
v___x_3772_ = lean_st_ref_get(v___x_3771_);
v___x_3773_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(v___x_3772_, v_builderId_3768_);
lean_dec(v___x_3772_);
if (v___x_3773_ == 0)
{
lean_object* v___x_3774_; lean_object* v___x_3775_; lean_object* v___x_3776_; lean_object* v___x_3777_; 
v___x_3774_ = lean_st_ref_take(v___x_3771_);
v___x_3775_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1___redArg(v___x_3774_, v_builderId_3768_, v_builder_3769_);
v___x_3776_ = lean_st_ref_set(v___x_3771_, v___x_3775_);
v___x_3777_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3777_, 0, v___x_3776_);
return v___x_3777_;
}
else
{
lean_object* v___x_3778_; lean_object* v___x_3779_; lean_object* v___x_3780_; lean_object* v___x_3781_; lean_object* v___x_3782_; lean_object* v___x_3783_; lean_object* v___x_3784_; 
lean_dec_ref(v_builder_3769_);
v___x_3778_ = ((lean_object*)(l_Lean_registerAttributeImplBuilder___closed__0));
v___x_3779_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_builderId_3768_, v___x_3773_);
v___x_3780_ = lean_string_append(v___x_3778_, v___x_3779_);
lean_dec_ref(v___x_3779_);
v___x_3781_ = ((lean_object*)(l_Lean_registerAttributeImplBuilder___closed__1));
v___x_3782_ = lean_string_append(v___x_3780_, v___x_3781_);
v___x_3783_ = lean_mk_io_user_error(v___x_3782_);
v___x_3784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3784_, 0, v___x_3783_);
return v___x_3784_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerAttributeImplBuilder___boxed(lean_object* v_builderId_3785_, lean_object* v_builder_3786_, lean_object* v_a_3787_){
_start:
{
lean_object* v_res_3788_; 
v_res_3788_ = l_Lean_registerAttributeImplBuilder(v_builderId_3785_, v_builder_3786_);
return v_res_3788_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___redArg(lean_object* v_e_3789_){
_start:
{
if (lean_obj_tag(v_e_3789_) == 0)
{
lean_object* v_a_3791_; lean_object* v___x_3793_; uint8_t v_isShared_3794_; uint8_t v_isSharedCheck_3799_; 
v_a_3791_ = lean_ctor_get(v_e_3789_, 0);
v_isSharedCheck_3799_ = !lean_is_exclusive(v_e_3789_);
if (v_isSharedCheck_3799_ == 0)
{
v___x_3793_ = v_e_3789_;
v_isShared_3794_ = v_isSharedCheck_3799_;
goto v_resetjp_3792_;
}
else
{
lean_inc(v_a_3791_);
lean_dec(v_e_3789_);
v___x_3793_ = lean_box(0);
v_isShared_3794_ = v_isSharedCheck_3799_;
goto v_resetjp_3792_;
}
v_resetjp_3792_:
{
lean_object* v___x_3795_; lean_object* v___x_3797_; 
v___x_3795_ = lean_mk_io_user_error(v_a_3791_);
if (v_isShared_3794_ == 0)
{
lean_ctor_set_tag(v___x_3793_, 1);
lean_ctor_set(v___x_3793_, 0, v___x_3795_);
v___x_3797_ = v___x_3793_;
goto v_reusejp_3796_;
}
else
{
lean_object* v_reuseFailAlloc_3798_; 
v_reuseFailAlloc_3798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3798_, 0, v___x_3795_);
v___x_3797_ = v_reuseFailAlloc_3798_;
goto v_reusejp_3796_;
}
v_reusejp_3796_:
{
return v___x_3797_;
}
}
}
else
{
lean_object* v_a_3800_; lean_object* v___x_3802_; uint8_t v_isShared_3803_; uint8_t v_isSharedCheck_3807_; 
v_a_3800_ = lean_ctor_get(v_e_3789_, 0);
v_isSharedCheck_3807_ = !lean_is_exclusive(v_e_3789_);
if (v_isSharedCheck_3807_ == 0)
{
v___x_3802_ = v_e_3789_;
v_isShared_3803_ = v_isSharedCheck_3807_;
goto v_resetjp_3801_;
}
else
{
lean_inc(v_a_3800_);
lean_dec(v_e_3789_);
v___x_3802_ = lean_box(0);
v_isShared_3803_ = v_isSharedCheck_3807_;
goto v_resetjp_3801_;
}
v_resetjp_3801_:
{
lean_object* v___x_3805_; 
if (v_isShared_3803_ == 0)
{
lean_ctor_set_tag(v___x_3802_, 0);
v___x_3805_ = v___x_3802_;
goto v_reusejp_3804_;
}
else
{
lean_object* v_reuseFailAlloc_3806_; 
v_reuseFailAlloc_3806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3806_, 0, v_a_3800_);
v___x_3805_ = v_reuseFailAlloc_3806_;
goto v_reusejp_3804_;
}
v_reusejp_3804_:
{
return v___x_3805_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___redArg___boxed(lean_object* v_e_3808_, lean_object* v_a_3809_){
_start:
{
lean_object* v_res_3810_; 
v_res_3810_ = l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___redArg(v_e_3808_);
return v_res_3810_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1(lean_object* v_00_u03b1_3811_, lean_object* v_e_3812_){
_start:
{
lean_object* v___x_3814_; 
v___x_3814_ = l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___redArg(v_e_3812_);
return v___x_3814_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___boxed(lean_object* v_00_u03b1_3815_, lean_object* v_e_3816_, lean_object* v_a_3817_){
_start:
{
lean_object* v_res_3818_; 
v_res_3818_ = l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1(v_00_u03b1_3815_, v_e_3816_);
return v_res_3818_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___redArg(lean_object* v_a_3819_, lean_object* v_x_3820_){
_start:
{
if (lean_obj_tag(v_x_3820_) == 0)
{
lean_object* v___x_3821_; 
v___x_3821_ = lean_box(0);
return v___x_3821_;
}
else
{
lean_object* v_key_3822_; lean_object* v_value_3823_; lean_object* v_tail_3824_; uint8_t v___x_3825_; 
v_key_3822_ = lean_ctor_get(v_x_3820_, 0);
v_value_3823_ = lean_ctor_get(v_x_3820_, 1);
v_tail_3824_ = lean_ctor_get(v_x_3820_, 2);
v___x_3825_ = lean_name_eq(v_key_3822_, v_a_3819_);
if (v___x_3825_ == 0)
{
v_x_3820_ = v_tail_3824_;
goto _start;
}
else
{
lean_object* v___x_3827_; 
lean_inc(v_value_3823_);
v___x_3827_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3827_, 0, v_value_3823_);
return v___x_3827_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___redArg___boxed(lean_object* v_a_3828_, lean_object* v_x_3829_){
_start:
{
lean_object* v_res_3830_; 
v_res_3830_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___redArg(v_a_3828_, v_x_3829_);
lean_dec(v_x_3829_);
lean_dec(v_a_3828_);
return v_res_3830_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(lean_object* v_m_3831_, lean_object* v_a_3832_){
_start:
{
lean_object* v_buckets_3833_; lean_object* v___x_3834_; uint64_t v___y_3836_; 
v_buckets_3833_ = lean_ctor_get(v_m_3831_, 1);
v___x_3834_ = lean_array_get_size(v_buckets_3833_);
if (lean_obj_tag(v_a_3832_) == 0)
{
uint64_t v___x_3850_; 
v___x_3850_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg___closed__0);
v___y_3836_ = v___x_3850_;
goto v___jp_3835_;
}
else
{
uint64_t v_hash_3851_; 
v_hash_3851_ = lean_ctor_get_uint64(v_a_3832_, sizeof(void*)*2);
v___y_3836_ = v_hash_3851_;
goto v___jp_3835_;
}
v___jp_3835_:
{
uint64_t v___x_3837_; uint64_t v___x_3838_; uint64_t v_fold_3839_; uint64_t v___x_3840_; uint64_t v___x_3841_; uint64_t v___x_3842_; size_t v___x_3843_; size_t v___x_3844_; size_t v___x_3845_; size_t v___x_3846_; size_t v___x_3847_; lean_object* v___x_3848_; lean_object* v___x_3849_; 
v___x_3837_ = 32ULL;
v___x_3838_ = lean_uint64_shift_right(v___y_3836_, v___x_3837_);
v_fold_3839_ = lean_uint64_xor(v___y_3836_, v___x_3838_);
v___x_3840_ = 16ULL;
v___x_3841_ = lean_uint64_shift_right(v_fold_3839_, v___x_3840_);
v___x_3842_ = lean_uint64_xor(v_fold_3839_, v___x_3841_);
v___x_3843_ = lean_uint64_to_usize(v___x_3842_);
v___x_3844_ = lean_usize_of_nat(v___x_3834_);
v___x_3845_ = ((size_t)1ULL);
v___x_3846_ = lean_usize_sub(v___x_3844_, v___x_3845_);
v___x_3847_ = lean_usize_land(v___x_3843_, v___x_3846_);
v___x_3848_ = lean_array_uget_borrowed(v_buckets_3833_, v___x_3847_);
v___x_3849_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___redArg(v_a_3832_, v___x_3848_);
return v___x_3849_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg___boxed(lean_object* v_m_3852_, lean_object* v_a_3853_){
_start:
{
lean_object* v_res_3854_; 
v_res_3854_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(v_m_3852_, v_a_3853_);
lean_dec(v_a_3853_);
lean_dec_ref(v_m_3852_);
return v_res_3854_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAttributeImplOfEntry(lean_object* v_e_3856_){
_start:
{
lean_object* v___x_3858_; lean_object* v___x_3859_; lean_object* v_builderId_3860_; lean_object* v_ref_3861_; lean_object* v_args_3862_; lean_object* v___x_3863_; 
v___x_3858_ = l_Lean_attributeImplBuilderTableRef;
v___x_3859_ = lean_st_ref_get(v___x_3858_);
v_builderId_3860_ = lean_ctor_get(v_e_3856_, 0);
lean_inc(v_builderId_3860_);
v_ref_3861_ = lean_ctor_get(v_e_3856_, 1);
lean_inc(v_ref_3861_);
v_args_3862_ = lean_ctor_get(v_e_3856_, 2);
lean_inc(v_args_3862_);
lean_dec_ref(v_e_3856_);
v___x_3863_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(v___x_3859_, v_builderId_3860_);
lean_dec(v___x_3859_);
if (lean_obj_tag(v___x_3863_) == 0)
{
lean_object* v___x_3864_; uint8_t v___x_3865_; lean_object* v___x_3866_; lean_object* v___x_3867_; lean_object* v___x_3868_; lean_object* v___x_3869_; lean_object* v___x_3870_; lean_object* v___x_3871_; 
lean_dec(v_args_3862_);
lean_dec(v_ref_3861_);
v___x_3864_ = ((lean_object*)(l_Lean_mkAttributeImplOfEntry___closed__0));
v___x_3865_ = 1;
v___x_3866_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_builderId_3860_, v___x_3865_);
v___x_3867_ = lean_string_append(v___x_3864_, v___x_3866_);
lean_dec_ref(v___x_3866_);
v___x_3868_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__4));
v___x_3869_ = lean_string_append(v___x_3867_, v___x_3868_);
v___x_3870_ = lean_mk_io_user_error(v___x_3869_);
v___x_3871_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3871_, 0, v___x_3870_);
return v___x_3871_;
}
else
{
lean_object* v_val_3872_; lean_object* v___x_3873_; lean_object* v___x_3874_; 
lean_dec(v_builderId_3860_);
v_val_3872_ = lean_ctor_get(v___x_3863_, 0);
lean_inc(v_val_3872_);
lean_dec_ref_known(v___x_3863_, 1);
v___x_3873_ = lean_apply_2(v_val_3872_, v_ref_3861_, v_args_3862_);
v___x_3874_ = l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___redArg(v___x_3873_);
return v___x_3874_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkAttributeImplOfEntry___boxed(lean_object* v_e_3875_, lean_object* v_a_3876_){
_start:
{
lean_object* v_res_3877_; 
v_res_3877_ = l_Lean_mkAttributeImplOfEntry(v_e_3875_);
return v_res_3877_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0(lean_object* v_00_u03b2_3878_, lean_object* v_m_3879_, lean_object* v_a_3880_){
_start:
{
lean_object* v___x_3881_; 
v___x_3881_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(v_m_3879_, v_a_3880_);
return v___x_3881_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___boxed(lean_object* v_00_u03b2_3882_, lean_object* v_m_3883_, lean_object* v_a_3884_){
_start:
{
lean_object* v_res_3885_; 
v_res_3885_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0(v_00_u03b2_3882_, v_m_3883_, v_a_3884_);
lean_dec(v_a_3884_);
lean_dec_ref(v_m_3883_);
return v_res_3885_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0(lean_object* v_00_u03b2_3886_, lean_object* v_a_3887_, lean_object* v_x_3888_){
_start:
{
lean_object* v___x_3889_; 
v___x_3889_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___redArg(v_a_3887_, v_x_3888_);
return v___x_3889_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3890_, lean_object* v_a_3891_, lean_object* v_x_3892_){
_start:
{
lean_object* v_res_3893_; 
v_res_3893_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0(v_00_u03b2_3890_, v_a_3891_, v_x_3892_);
lean_dec(v_x_3892_);
lean_dec(v_a_3891_);
return v_res_3893_;
}
}
static lean_object* _init_l_Lean_instInhabitedAttributeExtensionState_default___closed__0(void){
_start:
{
lean_object* v___x_3894_; lean_object* v___x_3895_; lean_object* v___x_3896_; 
v___x_3894_ = lean_obj_once(&l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_, &l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2__once, _init_l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_);
v___x_3895_ = lean_box(0);
v___x_3896_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3896_, 0, v___x_3895_);
lean_ctor_set(v___x_3896_, 1, v___x_3894_);
return v___x_3896_;
}
}
static lean_object* _init_l_Lean_instInhabitedAttributeExtensionState_default(void){
_start:
{
lean_object* v___x_3897_; 
v___x_3897_ = lean_obj_once(&l_Lean_instInhabitedAttributeExtensionState_default___closed__0, &l_Lean_instInhabitedAttributeExtensionState_default___closed__0_once, _init_l_Lean_instInhabitedAttributeExtensionState_default___closed__0);
return v___x_3897_;
}
}
static lean_object* _init_l_Lean_instInhabitedAttributeExtensionState(void){
_start:
{
lean_object* v___x_3898_; 
v___x_3898_ = l_Lean_instInhabitedAttributeExtensionState_default;
return v___x_3898_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_AttributeExtension_mkInitial(){
_start:
{
lean_object* v___x_3900_; lean_object* v___x_3901_; lean_object* v___x_3902_; lean_object* v___x_3903_; lean_object* v___x_3904_; 
v___x_3900_ = l_Lean_attributeMapRef;
v___x_3901_ = lean_st_ref_get(v___x_3900_);
v___x_3902_ = lean_box(0);
v___x_3903_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3903_, 0, v___x_3902_);
lean_ctor_set(v___x_3903_, 1, v___x_3901_);
v___x_3904_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3904_, 0, v___x_3903_);
return v___x_3904_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_AttributeExtension_mkInitial___boxed(lean_object* v_a_3905_){
_start:
{
lean_object* v_res_3906_; 
v_res_3906_ = l___private_Lean_Attributes_0__Lean_AttributeExtension_mkInitial();
return v_res_3906_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAttributeImplOfConstantUnsafe(lean_object* v_env_3912_, lean_object* v_opts_3913_, lean_object* v_declName_3914_){
_start:
{
uint8_t v___x_3917_; lean_object* v___x_3918_; 
v___x_3917_ = 0;
lean_inc(v_declName_3914_);
lean_inc_ref(v_env_3912_);
v___x_3918_ = l_Lean_Environment_find_x3f(v_env_3912_, v_declName_3914_, v___x_3917_);
if (lean_obj_tag(v___x_3918_) == 0)
{
lean_object* v___x_3919_; uint8_t v___x_3920_; lean_object* v___x_3921_; lean_object* v___x_3922_; lean_object* v___x_3923_; lean_object* v___x_3924_; lean_object* v___x_3925_; 
lean_dec_ref(v_env_3912_);
v___x_3919_ = ((lean_object*)(l_Lean_mkAttributeImplOfConstantUnsafe___closed__2));
v___x_3920_ = 1;
v___x_3921_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_declName_3914_, v___x_3920_);
v___x_3922_ = lean_string_append(v___x_3919_, v___x_3921_);
lean_dec_ref(v___x_3921_);
v___x_3923_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__4));
v___x_3924_ = lean_string_append(v___x_3922_, v___x_3923_);
v___x_3925_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3925_, 0, v___x_3924_);
return v___x_3925_;
}
else
{
lean_object* v_val_3926_; lean_object* v___x_3927_; 
v_val_3926_ = lean_ctor_get(v___x_3918_, 0);
lean_inc(v_val_3926_);
lean_dec_ref_known(v___x_3918_, 1);
v___x_3927_ = l_Lean_ConstantInfo_type(v_val_3926_);
lean_dec(v_val_3926_);
if (lean_obj_tag(v___x_3927_) == 4)
{
lean_object* v_declName_3928_; 
v_declName_3928_ = lean_ctor_get(v___x_3927_, 0);
lean_inc(v_declName_3928_);
lean_dec_ref_known(v___x_3927_, 2);
if (lean_obj_tag(v_declName_3928_) == 1)
{
lean_object* v_pre_3929_; 
v_pre_3929_ = lean_ctor_get(v_declName_3928_, 0);
lean_inc(v_pre_3929_);
if (lean_obj_tag(v_pre_3929_) == 1)
{
lean_object* v_pre_3930_; 
v_pre_3930_ = lean_ctor_get(v_pre_3929_, 0);
if (lean_obj_tag(v_pre_3930_) == 0)
{
lean_object* v_str_3931_; lean_object* v_str_3932_; lean_object* v___x_3933_; uint8_t v___x_3934_; 
v_str_3931_ = lean_ctor_get(v_declName_3928_, 1);
lean_inc_ref(v_str_3931_);
lean_dec_ref_known(v_declName_3928_, 2);
v_str_3932_ = lean_ctor_get(v_pre_3929_, 1);
lean_inc_ref(v_str_3932_);
lean_dec_ref_known(v_pre_3929_, 2);
v___x_3933_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__0));
v___x_3934_ = lean_string_dec_eq(v_str_3932_, v___x_3933_);
lean_dec_ref(v_str_3932_);
if (v___x_3934_ == 0)
{
lean_dec_ref(v_str_3931_);
lean_dec(v_declName_3914_);
lean_dec_ref(v_env_3912_);
goto v___jp_3915_;
}
else
{
lean_object* v___x_3935_; uint8_t v___x_3936_; 
v___x_3935_ = ((lean_object*)(l_Lean_mkAttributeImplOfConstantUnsafe___closed__3));
v___x_3936_ = lean_string_dec_eq(v_str_3931_, v___x_3935_);
lean_dec_ref(v_str_3931_);
if (v___x_3936_ == 0)
{
lean_dec(v_declName_3914_);
lean_dec_ref(v_env_3912_);
goto v___jp_3915_;
}
else
{
lean_object* v___x_3937_; 
v___x_3937_ = l_Lean_Environment_evalConst___redArg(v_env_3912_, v_opts_3913_, v_declName_3914_, v___x_3936_);
lean_dec(v_declName_3914_);
lean_dec_ref(v_env_3912_);
return v___x_3937_;
}
}
}
else
{
lean_dec_ref_known(v_pre_3929_, 2);
lean_dec_ref_known(v_declName_3928_, 2);
lean_dec(v_declName_3914_);
lean_dec_ref(v_env_3912_);
goto v___jp_3915_;
}
}
else
{
lean_dec(v_pre_3929_);
lean_dec_ref_known(v_declName_3928_, 2);
lean_dec(v_declName_3914_);
lean_dec_ref(v_env_3912_);
goto v___jp_3915_;
}
}
else
{
lean_dec(v_declName_3928_);
lean_dec(v_declName_3914_);
lean_dec_ref(v_env_3912_);
goto v___jp_3915_;
}
}
else
{
lean_dec_ref(v___x_3927_);
lean_dec(v_declName_3914_);
lean_dec_ref(v_env_3912_);
goto v___jp_3915_;
}
}
v___jp_3915_:
{
lean_object* v___x_3916_; 
v___x_3916_ = ((lean_object*)(l_Lean_mkAttributeImplOfConstantUnsafe___closed__1));
return v___x_3916_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkAttributeImplOfConstantUnsafe___boxed(lean_object* v_env_3938_, lean_object* v_opts_3939_, lean_object* v_declName_3940_){
_start:
{
lean_object* v_res_3941_; 
v_res_3941_ = l_Lean_mkAttributeImplOfConstantUnsafe(v_env_3938_, v_opts_3939_, v_declName_3940_);
lean_dec_ref(v_opts_3939_);
return v_res_3941_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg(lean_object* v_as_3942_, size_t v_i_3943_, size_t v_stop_3944_, lean_object* v_b_3945_){
_start:
{
uint8_t v___x_3947_; 
v___x_3947_ = lean_usize_dec_eq(v_i_3943_, v_stop_3944_);
if (v___x_3947_ == 0)
{
lean_object* v___x_3948_; lean_object* v___x_3949_; 
v___x_3948_ = lean_array_uget_borrowed(v_as_3942_, v_i_3943_);
lean_inc(v___x_3948_);
v___x_3949_ = l_Lean_mkAttributeImplOfEntry(v___x_3948_);
if (lean_obj_tag(v___x_3949_) == 0)
{
lean_object* v_a_3950_; lean_object* v_toAttributeImplCore_3951_; lean_object* v_name_3952_; lean_object* v___x_3953_; size_t v___x_3954_; size_t v___x_3955_; 
v_a_3950_ = lean_ctor_get(v___x_3949_, 0);
lean_inc(v_a_3950_);
lean_dec_ref_known(v___x_3949_, 1);
v_toAttributeImplCore_3951_ = lean_ctor_get(v_a_3950_, 0);
v_name_3952_ = lean_ctor_get(v_toAttributeImplCore_3951_, 1);
lean_inc(v_name_3952_);
v___x_3953_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1___redArg(v_b_3945_, v_name_3952_, v_a_3950_);
v___x_3954_ = ((size_t)1ULL);
v___x_3955_ = lean_usize_add(v_i_3943_, v___x_3954_);
v_i_3943_ = v___x_3955_;
v_b_3945_ = v___x_3953_;
goto _start;
}
else
{
lean_object* v_a_3957_; lean_object* v___x_3959_; uint8_t v_isShared_3960_; uint8_t v_isSharedCheck_3964_; 
lean_dec_ref(v_b_3945_);
v_a_3957_ = lean_ctor_get(v___x_3949_, 0);
v_isSharedCheck_3964_ = !lean_is_exclusive(v___x_3949_);
if (v_isSharedCheck_3964_ == 0)
{
v___x_3959_ = v___x_3949_;
v_isShared_3960_ = v_isSharedCheck_3964_;
goto v_resetjp_3958_;
}
else
{
lean_inc(v_a_3957_);
lean_dec(v___x_3949_);
v___x_3959_ = lean_box(0);
v_isShared_3960_ = v_isSharedCheck_3964_;
goto v_resetjp_3958_;
}
v_resetjp_3958_:
{
lean_object* v___x_3962_; 
if (v_isShared_3960_ == 0)
{
v___x_3962_ = v___x_3959_;
goto v_reusejp_3961_;
}
else
{
lean_object* v_reuseFailAlloc_3963_; 
v_reuseFailAlloc_3963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3963_, 0, v_a_3957_);
v___x_3962_ = v_reuseFailAlloc_3963_;
goto v_reusejp_3961_;
}
v_reusejp_3961_:
{
return v___x_3962_;
}
}
}
}
else
{
lean_object* v___x_3965_; 
v___x_3965_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3965_, 0, v_b_3945_);
return v___x_3965_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg___boxed(lean_object* v_as_3966_, lean_object* v_i_3967_, lean_object* v_stop_3968_, lean_object* v_b_3969_, lean_object* v___y_3970_){
_start:
{
size_t v_i_boxed_3971_; size_t v_stop_boxed_3972_; lean_object* v_res_3973_; 
v_i_boxed_3971_ = lean_unbox_usize(v_i_3967_);
lean_dec(v_i_3967_);
v_stop_boxed_3972_ = lean_unbox_usize(v_stop_3968_);
lean_dec(v_stop_3968_);
v_res_3973_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg(v_as_3966_, v_i_boxed_3971_, v_stop_boxed_3972_, v_b_3969_);
lean_dec_ref(v_as_3966_);
return v_res_3973_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__1(lean_object* v_as_3974_, size_t v_i_3975_, size_t v_stop_3976_, lean_object* v_b_3977_, lean_object* v___y_3978_){
_start:
{
lean_object* v_a_3981_; lean_object* v___y_3986_; uint8_t v___x_3988_; 
v___x_3988_ = lean_usize_dec_eq(v_i_3975_, v_stop_3976_);
if (v___x_3988_ == 0)
{
lean_object* v___x_3989_; lean_object* v___x_3990_; lean_object* v___x_3991_; uint8_t v___x_3992_; 
v___x_3989_ = lean_array_uget_borrowed(v_as_3974_, v_i_3975_);
v___x_3990_ = lean_unsigned_to_nat(0u);
v___x_3991_ = lean_array_get_size(v___x_3989_);
v___x_3992_ = lean_nat_dec_lt(v___x_3990_, v___x_3991_);
if (v___x_3992_ == 0)
{
v_a_3981_ = v_b_3977_;
goto v___jp_3980_;
}
else
{
uint8_t v___x_3993_; 
v___x_3993_ = lean_nat_dec_le(v___x_3991_, v___x_3991_);
if (v___x_3993_ == 0)
{
if (v___x_3992_ == 0)
{
v_a_3981_ = v_b_3977_;
goto v___jp_3980_;
}
else
{
size_t v___x_3994_; size_t v___x_3995_; lean_object* v___x_3996_; 
v___x_3994_ = ((size_t)0ULL);
v___x_3995_ = lean_usize_of_nat(v___x_3991_);
v___x_3996_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg(v___x_3989_, v___x_3994_, v___x_3995_, v_b_3977_);
v___y_3986_ = v___x_3996_;
goto v___jp_3985_;
}
}
else
{
size_t v___x_3997_; size_t v___x_3998_; lean_object* v___x_3999_; 
v___x_3997_ = ((size_t)0ULL);
v___x_3998_ = lean_usize_of_nat(v___x_3991_);
v___x_3999_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg(v___x_3989_, v___x_3997_, v___x_3998_, v_b_3977_);
v___y_3986_ = v___x_3999_;
goto v___jp_3985_;
}
}
}
else
{
lean_object* v___x_4000_; 
v___x_4000_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4000_, 0, v_b_3977_);
return v___x_4000_;
}
v___jp_3980_:
{
size_t v___x_3982_; size_t v___x_3983_; 
v___x_3982_ = ((size_t)1ULL);
v___x_3983_ = lean_usize_add(v_i_3975_, v___x_3982_);
v_i_3975_ = v___x_3983_;
v_b_3977_ = v_a_3981_;
goto _start;
}
v___jp_3985_:
{
if (lean_obj_tag(v___y_3986_) == 0)
{
lean_object* v_a_3987_; 
v_a_3987_ = lean_ctor_get(v___y_3986_, 0);
lean_inc(v_a_3987_);
lean_dec_ref_known(v___y_3986_, 1);
v_a_3981_ = v_a_3987_;
goto v___jp_3980_;
}
else
{
return v___y_3986_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__1___boxed(lean_object* v_as_4001_, lean_object* v_i_4002_, lean_object* v_stop_4003_, lean_object* v_b_4004_, lean_object* v___y_4005_, lean_object* v___y_4006_){
_start:
{
size_t v_i_boxed_4007_; size_t v_stop_boxed_4008_; lean_object* v_res_4009_; 
v_i_boxed_4007_ = lean_unbox_usize(v_i_4002_);
lean_dec(v_i_4002_);
v_stop_boxed_4008_ = lean_unbox_usize(v_stop_4003_);
lean_dec(v_stop_4003_);
v_res_4009_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__1(v_as_4001_, v_i_boxed_4007_, v_stop_boxed_4008_, v_b_4004_, v___y_4005_);
lean_dec_ref(v___y_4005_);
lean_dec_ref(v_as_4001_);
return v_res_4009_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_AttributeExtension_addImported(lean_object* v_es_4010_, lean_object* v_a_4011_){
_start:
{
lean_object* v_a_4014_; lean_object* v___y_4019_; lean_object* v___x_4029_; lean_object* v___x_4030_; lean_object* v___x_4031_; lean_object* v___x_4032_; uint8_t v___x_4033_; 
v___x_4029_ = l_Lean_attributeMapRef;
v___x_4030_ = lean_st_ref_get(v___x_4029_);
v___x_4031_ = lean_unsigned_to_nat(0u);
v___x_4032_ = lean_array_get_size(v_es_4010_);
v___x_4033_ = lean_nat_dec_lt(v___x_4031_, v___x_4032_);
if (v___x_4033_ == 0)
{
v_a_4014_ = v___x_4030_;
goto v___jp_4013_;
}
else
{
uint8_t v___x_4034_; 
v___x_4034_ = lean_nat_dec_le(v___x_4032_, v___x_4032_);
if (v___x_4034_ == 0)
{
if (v___x_4033_ == 0)
{
v_a_4014_ = v___x_4030_;
goto v___jp_4013_;
}
else
{
size_t v___x_4035_; size_t v___x_4036_; lean_object* v___x_4037_; 
v___x_4035_ = ((size_t)0ULL);
v___x_4036_ = lean_usize_of_nat(v___x_4032_);
v___x_4037_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__1(v_es_4010_, v___x_4035_, v___x_4036_, v___x_4030_, v_a_4011_);
v___y_4019_ = v___x_4037_;
goto v___jp_4018_;
}
}
else
{
size_t v___x_4038_; size_t v___x_4039_; lean_object* v___x_4040_; 
v___x_4038_ = ((size_t)0ULL);
v___x_4039_ = lean_usize_of_nat(v___x_4032_);
v___x_4040_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__1(v_es_4010_, v___x_4038_, v___x_4039_, v___x_4030_, v_a_4011_);
v___y_4019_ = v___x_4040_;
goto v___jp_4018_;
}
}
v___jp_4013_:
{
lean_object* v___x_4015_; lean_object* v___x_4016_; lean_object* v___x_4017_; 
v___x_4015_ = lean_box(0);
v___x_4016_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4016_, 0, v___x_4015_);
lean_ctor_set(v___x_4016_, 1, v_a_4014_);
v___x_4017_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4017_, 0, v___x_4016_);
return v___x_4017_;
}
v___jp_4018_:
{
if (lean_obj_tag(v___y_4019_) == 0)
{
lean_object* v_a_4020_; 
v_a_4020_ = lean_ctor_get(v___y_4019_, 0);
lean_inc(v_a_4020_);
lean_dec_ref_known(v___y_4019_, 1);
v_a_4014_ = v_a_4020_;
goto v___jp_4013_;
}
else
{
lean_object* v_a_4021_; lean_object* v___x_4023_; uint8_t v_isShared_4024_; uint8_t v_isSharedCheck_4028_; 
v_a_4021_ = lean_ctor_get(v___y_4019_, 0);
v_isSharedCheck_4028_ = !lean_is_exclusive(v___y_4019_);
if (v_isSharedCheck_4028_ == 0)
{
v___x_4023_ = v___y_4019_;
v_isShared_4024_ = v_isSharedCheck_4028_;
goto v_resetjp_4022_;
}
else
{
lean_inc(v_a_4021_);
lean_dec(v___y_4019_);
v___x_4023_ = lean_box(0);
v_isShared_4024_ = v_isSharedCheck_4028_;
goto v_resetjp_4022_;
}
v_resetjp_4022_:
{
lean_object* v___x_4026_; 
if (v_isShared_4024_ == 0)
{
v___x_4026_ = v___x_4023_;
goto v_reusejp_4025_;
}
else
{
lean_object* v_reuseFailAlloc_4027_; 
v_reuseFailAlloc_4027_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4027_, 0, v_a_4021_);
v___x_4026_ = v_reuseFailAlloc_4027_;
goto v_reusejp_4025_;
}
v_reusejp_4025_:
{
return v___x_4026_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_AttributeExtension_addImported___boxed(lean_object* v_es_4041_, lean_object* v_a_4042_, lean_object* v_a_4043_){
_start:
{
lean_object* v_res_4044_; 
v_res_4044_ = l___private_Lean_Attributes_0__Lean_AttributeExtension_addImported(v_es_4041_, v_a_4042_);
lean_dec_ref(v_a_4042_);
lean_dec_ref(v_es_4041_);
return v_res_4044_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0(lean_object* v_as_4045_, size_t v_i_4046_, size_t v_stop_4047_, lean_object* v_b_4048_, lean_object* v___y_4049_){
_start:
{
lean_object* v___x_4051_; 
v___x_4051_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg(v_as_4045_, v_i_4046_, v_stop_4047_, v_b_4048_);
return v___x_4051_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___boxed(lean_object* v_as_4052_, lean_object* v_i_4053_, lean_object* v_stop_4054_, lean_object* v_b_4055_, lean_object* v___y_4056_, lean_object* v___y_4057_){
_start:
{
size_t v_i_boxed_4058_; size_t v_stop_boxed_4059_; lean_object* v_res_4060_; 
v_i_boxed_4058_ = lean_unbox_usize(v_i_4053_);
lean_dec(v_i_4053_);
v_stop_boxed_4059_ = lean_unbox_usize(v_stop_4054_);
lean_dec(v_stop_4054_);
v_res_4060_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0(v_as_4052_, v_i_boxed_4058_, v_stop_boxed_4059_, v_b_4055_, v___y_4056_);
lean_dec_ref(v___y_4056_);
lean_dec_ref(v_as_4052_);
return v_res_4060_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_addAttrEntry(lean_object* v_s_4061_, lean_object* v_e_4062_){
_start:
{
lean_object* v_snd_4063_; lean_object* v_toAttributeImplCore_4064_; lean_object* v_fst_4065_; lean_object* v___x_4067_; uint8_t v_isShared_4068_; uint8_t v_isSharedCheck_4083_; 
v_snd_4063_ = lean_ctor_get(v_e_4062_, 1);
lean_inc(v_snd_4063_);
v_toAttributeImplCore_4064_ = lean_ctor_get(v_snd_4063_, 0);
v_fst_4065_ = lean_ctor_get(v_e_4062_, 0);
v_isSharedCheck_4083_ = !lean_is_exclusive(v_e_4062_);
if (v_isSharedCheck_4083_ == 0)
{
lean_object* v_unused_4084_; 
v_unused_4084_ = lean_ctor_get(v_e_4062_, 1);
lean_dec(v_unused_4084_);
v___x_4067_ = v_e_4062_;
v_isShared_4068_ = v_isSharedCheck_4083_;
goto v_resetjp_4066_;
}
else
{
lean_inc(v_fst_4065_);
lean_dec(v_e_4062_);
v___x_4067_ = lean_box(0);
v_isShared_4068_ = v_isSharedCheck_4083_;
goto v_resetjp_4066_;
}
v_resetjp_4066_:
{
lean_object* v_newEntries_4069_; lean_object* v_map_4070_; lean_object* v___x_4072_; uint8_t v_isShared_4073_; uint8_t v_isSharedCheck_4082_; 
v_newEntries_4069_ = lean_ctor_get(v_s_4061_, 0);
v_map_4070_ = lean_ctor_get(v_s_4061_, 1);
v_isSharedCheck_4082_ = !lean_is_exclusive(v_s_4061_);
if (v_isSharedCheck_4082_ == 0)
{
v___x_4072_ = v_s_4061_;
v_isShared_4073_ = v_isSharedCheck_4082_;
goto v_resetjp_4071_;
}
else
{
lean_inc(v_map_4070_);
lean_inc(v_newEntries_4069_);
lean_dec(v_s_4061_);
v___x_4072_ = lean_box(0);
v_isShared_4073_ = v_isSharedCheck_4082_;
goto v_resetjp_4071_;
}
v_resetjp_4071_:
{
lean_object* v_name_4074_; lean_object* v___x_4076_; 
v_name_4074_ = lean_ctor_get(v_toAttributeImplCore_4064_, 1);
lean_inc(v_name_4074_);
if (v_isShared_4068_ == 0)
{
lean_ctor_set_tag(v___x_4067_, 1);
lean_ctor_set(v___x_4067_, 1, v_newEntries_4069_);
v___x_4076_ = v___x_4067_;
goto v_reusejp_4075_;
}
else
{
lean_object* v_reuseFailAlloc_4081_; 
v_reuseFailAlloc_4081_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4081_, 0, v_fst_4065_);
lean_ctor_set(v_reuseFailAlloc_4081_, 1, v_newEntries_4069_);
v___x_4076_ = v_reuseFailAlloc_4081_;
goto v_reusejp_4075_;
}
v_reusejp_4075_:
{
lean_object* v___x_4077_; lean_object* v___x_4079_; 
v___x_4077_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1___redArg(v_map_4070_, v_name_4074_, v_snd_4063_);
if (v_isShared_4073_ == 0)
{
lean_ctor_set(v___x_4072_, 1, v___x_4077_);
lean_ctor_set(v___x_4072_, 0, v___x_4076_);
v___x_4079_ = v___x_4072_;
goto v_reusejp_4078_;
}
else
{
lean_object* v_reuseFailAlloc_4080_; 
v_reuseFailAlloc_4080_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4080_, 0, v___x_4076_);
lean_ctor_set(v_reuseFailAlloc_4080_, 1, v___x_4077_);
v___x_4079_ = v_reuseFailAlloc_4080_;
goto v_reusejp_4078_;
}
v_reusejp_4078_:
{
return v___x_4079_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn___lam__0_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(lean_object* v_x_4085_, lean_object* v_s_4086_){
_start:
{
lean_object* v_newEntries_4087_; lean_object* v___x_4088_; lean_object* v___x_4089_; lean_object* v___x_4090_; 
v_newEntries_4087_ = lean_ctor_get(v_s_4086_, 0);
lean_inc(v_newEntries_4087_);
lean_dec_ref(v_s_4086_);
v___x_4088_ = l_List_reverse___redArg(v_newEntries_4087_);
v___x_4089_ = lean_array_mk(v___x_4088_);
lean_inc_ref_n(v___x_4089_, 2);
v___x_4090_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4090_, 0, v___x_4089_);
lean_ctor_set(v___x_4090_, 1, v___x_4089_);
lean_ctor_set(v___x_4090_, 2, v___x_4089_);
return v___x_4090_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn___lam__0_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2____boxed(lean_object* v_x_4091_, lean_object* v_s_4092_){
_start:
{
lean_object* v_res_4093_; 
v_res_4093_ = l___private_Lean_Attributes_0__Lean_initFn___lam__0_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(v_x_4091_, v_s_4092_);
lean_dec_ref(v_x_4091_);
return v_res_4093_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn___lam__1_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(lean_object* v_s_4094_){
_start:
{
lean_object* v_newEntries_4095_; lean_object* v___x_4097_; uint8_t v_isShared_4098_; uint8_t v_isSharedCheck_4106_; 
v_newEntries_4095_ = lean_ctor_get(v_s_4094_, 0);
v_isSharedCheck_4106_ = !lean_is_exclusive(v_s_4094_);
if (v_isSharedCheck_4106_ == 0)
{
lean_object* v_unused_4107_; 
v_unused_4107_ = lean_ctor_get(v_s_4094_, 1);
lean_dec(v_unused_4107_);
v___x_4097_ = v_s_4094_;
v_isShared_4098_ = v_isSharedCheck_4106_;
goto v_resetjp_4096_;
}
else
{
lean_inc(v_newEntries_4095_);
lean_dec(v_s_4094_);
v___x_4097_ = lean_box(0);
v_isShared_4098_ = v_isSharedCheck_4106_;
goto v_resetjp_4096_;
}
v_resetjp_4096_:
{
lean_object* v___x_4099_; lean_object* v___x_4100_; lean_object* v___x_4101_; lean_object* v___x_4102_; lean_object* v___x_4104_; 
v___x_4099_ = ((lean_object*)(l_Lean_registerTagAttribute___lam__2___closed__4));
v___x_4100_ = l_List_lengthTR___redArg(v_newEntries_4095_);
lean_dec(v_newEntries_4095_);
v___x_4101_ = l_Nat_reprFast(v___x_4100_);
v___x_4102_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4102_, 0, v___x_4101_);
if (v_isShared_4098_ == 0)
{
lean_ctor_set_tag(v___x_4097_, 5);
lean_ctor_set(v___x_4097_, 1, v___x_4102_);
lean_ctor_set(v___x_4097_, 0, v___x_4099_);
v___x_4104_ = v___x_4097_;
goto v_reusejp_4103_;
}
else
{
lean_object* v_reuseFailAlloc_4105_; 
v_reuseFailAlloc_4105_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4105_, 0, v___x_4099_);
lean_ctor_set(v_reuseFailAlloc_4105_, 1, v___x_4102_);
v___x_4104_ = v_reuseFailAlloc_4105_;
goto v_reusejp_4103_;
}
v_reusejp_4103_:
{
return v___x_4104_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn___lam__2_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(lean_object* v_s_4108_){
_start:
{
lean_object* v_newEntries_4109_; lean_object* v___x_4110_; lean_object* v___x_4111_; 
v_newEntries_4109_ = lean_ctor_get(v_s_4108_, 0);
lean_inc(v_newEntries_4109_);
lean_dec_ref(v_s_4108_);
v___x_4110_ = l_List_reverse___redArg(v_newEntries_4109_);
v___x_4111_ = lean_array_mk(v___x_4110_);
return v___x_4111_;
}
}
static lean_object* _init_l___private_Lean_Attributes_0__Lean_initFn___closed__7_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4121_; lean_object* v___x_4122_; lean_object* v___f_4123_; lean_object* v___f_4124_; lean_object* v___x_4125_; lean_object* v___x_4126_; lean_object* v___x_4127_; lean_object* v___x_4128_; lean_object* v___x_4129_; 
v___x_4121_ = lean_box(0);
v___x_4122_ = lean_box(2);
v___f_4123_ = ((lean_object*)(l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___f_4124_ = ((lean_object*)(l___private_Lean_Attributes_0__Lean_initFn___closed__0_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___x_4125_ = ((lean_object*)(l___private_Lean_Attributes_0__Lean_initFn___closed__6_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___x_4126_ = ((lean_object*)(l___private_Lean_Attributes_0__Lean_initFn___closed__5_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___x_4127_ = lean_alloc_closure((void*)(l___private_Lean_Attributes_0__Lean_AttributeExtension_mkInitial___boxed), 1, 0);
v___x_4128_ = ((lean_object*)(l___private_Lean_Attributes_0__Lean_initFn___closed__4_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___x_4129_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_4129_, 0, v___x_4128_);
lean_ctor_set(v___x_4129_, 1, v___x_4127_);
lean_ctor_set(v___x_4129_, 2, v___x_4126_);
lean_ctor_set(v___x_4129_, 3, v___x_4125_);
lean_ctor_set(v___x_4129_, 4, v___f_4124_);
lean_ctor_set(v___x_4129_, 5, v___f_4123_);
lean_ctor_set(v___x_4129_, 6, v___x_4122_);
lean_ctor_set(v___x_4129_, 7, v___x_4121_);
return v___x_4129_;
}
}
static lean_object* _init_l___private_Lean_Attributes_0__Lean_initFn___closed__8_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_4130_; lean_object* v___x_4131_; lean_object* v___x_4132_; 
v___f_4130_ = ((lean_object*)(l___private_Lean_Attributes_0__Lean_initFn___closed__2_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___x_4131_ = lean_obj_once(&l___private_Lean_Attributes_0__Lean_initFn___closed__7_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_, &l___private_Lean_Attributes_0__Lean_initFn___closed__7_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2__once, _init_l___private_Lean_Attributes_0__Lean_initFn___closed__7_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_);
v___x_4132_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4132_, 0, v___x_4131_);
lean_ctor_set(v___x_4132_, 1, v___f_4130_);
return v___x_4132_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4134_; lean_object* v___x_4135_; 
v___x_4134_ = lean_obj_once(&l___private_Lean_Attributes_0__Lean_initFn___closed__8_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_, &l___private_Lean_Attributes_0__Lean_initFn___closed__8_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2__once, _init_l___private_Lean_Attributes_0__Lean_initFn___closed__8_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_);
v___x_4135_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_4134_);
return v___x_4135_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2____boxed(lean_object* v_a_4136_){
_start:
{
lean_object* v_res_4137_; 
v_res_4137_ = l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_();
return v_res_4137_;
}
}
LEAN_EXPORT lean_object* l_Lean_isBuiltinAttribute(lean_object* v_n_4138_){
_start:
{
lean_object* v___x_4140_; lean_object* v___x_4141_; uint8_t v___x_4142_; lean_object* v___x_4143_; lean_object* v___x_4144_; 
v___x_4140_ = l_Lean_attributeMapRef;
v___x_4141_ = lean_st_ref_get(v___x_4140_);
v___x_4142_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(v___x_4141_, v_n_4138_);
lean_dec(v___x_4141_);
v___x_4143_ = lean_box(v___x_4142_);
v___x_4144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4144_, 0, v___x_4143_);
return v___x_4144_;
}
}
LEAN_EXPORT lean_object* l_Lean_isBuiltinAttribute___boxed(lean_object* v_n_4145_, lean_object* v_a_4146_){
_start:
{
lean_object* v_res_4147_; 
v_res_4147_ = l_Lean_isBuiltinAttribute(v_n_4145_);
lean_dec(v_n_4145_);
return v_res_4147_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_getBuiltinAttributeNames_spec__0(lean_object* v_x_4148_, lean_object* v_x_4149_){
_start:
{
if (lean_obj_tag(v_x_4149_) == 0)
{
return v_x_4148_;
}
else
{
lean_object* v_key_4150_; lean_object* v_tail_4151_; lean_object* v___x_4152_; 
v_key_4150_ = lean_ctor_get(v_x_4149_, 0);
v_tail_4151_ = lean_ctor_get(v_x_4149_, 2);
lean_inc(v_key_4150_);
v___x_4152_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4152_, 0, v_key_4150_);
lean_ctor_set(v___x_4152_, 1, v_x_4148_);
v_x_4148_ = v___x_4152_;
v_x_4149_ = v_tail_4151_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_getBuiltinAttributeNames_spec__0___boxed(lean_object* v_x_4154_, lean_object* v_x_4155_){
_start:
{
lean_object* v_res_4156_; 
v_res_4156_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_getBuiltinAttributeNames_spec__0(v_x_4154_, v_x_4155_);
lean_dec(v_x_4155_);
return v_res_4156_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1(lean_object* v_as_4157_, size_t v_i_4158_, size_t v_stop_4159_, lean_object* v_b_4160_){
_start:
{
uint8_t v___x_4161_; 
v___x_4161_ = lean_usize_dec_eq(v_i_4158_, v_stop_4159_);
if (v___x_4161_ == 0)
{
lean_object* v___x_4162_; lean_object* v___x_4163_; size_t v___x_4164_; size_t v___x_4165_; 
v___x_4162_ = lean_array_uget_borrowed(v_as_4157_, v_i_4158_);
v___x_4163_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_getBuiltinAttributeNames_spec__0(v_b_4160_, v___x_4162_);
v___x_4164_ = ((size_t)1ULL);
v___x_4165_ = lean_usize_add(v_i_4158_, v___x_4164_);
v_i_4158_ = v___x_4165_;
v_b_4160_ = v___x_4163_;
goto _start;
}
else
{
return v_b_4160_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1___boxed(lean_object* v_as_4167_, lean_object* v_i_4168_, lean_object* v_stop_4169_, lean_object* v_b_4170_){
_start:
{
size_t v_i_boxed_4171_; size_t v_stop_boxed_4172_; lean_object* v_res_4173_; 
v_i_boxed_4171_ = lean_unbox_usize(v_i_4168_);
lean_dec(v_i_4168_);
v_stop_boxed_4172_ = lean_unbox_usize(v_stop_4169_);
lean_dec(v_stop_4169_);
v_res_4173_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1(v_as_4167_, v_i_boxed_4171_, v_stop_boxed_4172_, v_b_4170_);
lean_dec_ref(v_as_4167_);
return v_res_4173_;
}
}
LEAN_EXPORT lean_object* l_Lean_getBuiltinAttributeNames(){
_start:
{
lean_object* v___x_4175_; lean_object* v___x_4176_; lean_object* v_buckets_4177_; lean_object* v___x_4178_; lean_object* v___x_4179_; lean_object* v___x_4180_; uint8_t v___x_4181_; 
v___x_4175_ = l_Lean_attributeMapRef;
v___x_4176_ = lean_st_ref_get(v___x_4175_);
v_buckets_4177_ = lean_ctor_get(v___x_4176_, 1);
lean_inc_ref(v_buckets_4177_);
lean_dec(v___x_4176_);
v___x_4178_ = lean_box(0);
v___x_4179_ = lean_unsigned_to_nat(0u);
v___x_4180_ = lean_array_get_size(v_buckets_4177_);
v___x_4181_ = lean_nat_dec_lt(v___x_4179_, v___x_4180_);
if (v___x_4181_ == 0)
{
lean_object* v___x_4182_; 
lean_dec_ref(v_buckets_4177_);
v___x_4182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4182_, 0, v___x_4178_);
return v___x_4182_;
}
else
{
uint8_t v___x_4183_; 
v___x_4183_ = lean_nat_dec_le(v___x_4180_, v___x_4180_);
if (v___x_4183_ == 0)
{
if (v___x_4181_ == 0)
{
lean_object* v___x_4184_; 
lean_dec_ref(v_buckets_4177_);
v___x_4184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4184_, 0, v___x_4178_);
return v___x_4184_;
}
else
{
size_t v___x_4185_; size_t v___x_4186_; lean_object* v___x_4187_; lean_object* v___x_4188_; 
v___x_4185_ = ((size_t)0ULL);
v___x_4186_ = lean_usize_of_nat(v___x_4180_);
v___x_4187_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1(v_buckets_4177_, v___x_4185_, v___x_4186_, v___x_4178_);
lean_dec_ref(v_buckets_4177_);
v___x_4188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4188_, 0, v___x_4187_);
return v___x_4188_;
}
}
else
{
size_t v___x_4189_; size_t v___x_4190_; lean_object* v___x_4191_; lean_object* v___x_4192_; 
v___x_4189_ = ((size_t)0ULL);
v___x_4190_ = lean_usize_of_nat(v___x_4180_);
v___x_4191_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1(v_buckets_4177_, v___x_4189_, v___x_4190_, v___x_4178_);
lean_dec_ref(v_buckets_4177_);
v___x_4192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4192_, 0, v___x_4191_);
return v___x_4192_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getBuiltinAttributeNames___boxed(lean_object* v_a_4193_){
_start:
{
lean_object* v_res_4194_; 
v_res_4194_ = l_Lean_getBuiltinAttributeNames();
return v_res_4194_;
}
}
LEAN_EXPORT lean_object* l_Lean_getBuiltinAttributeImpl(lean_object* v_attrName_4196_){
_start:
{
lean_object* v___x_4198_; lean_object* v___x_4199_; lean_object* v___x_4200_; 
v___x_4198_ = l_Lean_attributeMapRef;
v___x_4199_ = lean_st_ref_get(v___x_4198_);
v___x_4200_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(v___x_4199_, v_attrName_4196_);
lean_dec(v___x_4199_);
if (lean_obj_tag(v___x_4200_) == 0)
{
lean_object* v___x_4201_; uint8_t v___x_4202_; lean_object* v___x_4203_; lean_object* v___x_4204_; lean_object* v___x_4205_; lean_object* v___x_4206_; lean_object* v___x_4207_; lean_object* v___x_4208_; 
v___x_4201_ = ((lean_object*)(l_Lean_getBuiltinAttributeImpl___closed__0));
v___x_4202_ = 1;
v___x_4203_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_attrName_4196_, v___x_4202_);
v___x_4204_ = lean_string_append(v___x_4201_, v___x_4203_);
lean_dec_ref(v___x_4203_);
v___x_4205_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__4));
v___x_4206_ = lean_string_append(v___x_4204_, v___x_4205_);
v___x_4207_ = lean_mk_io_user_error(v___x_4206_);
v___x_4208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4208_, 0, v___x_4207_);
return v___x_4208_;
}
else
{
lean_object* v_val_4209_; lean_object* v___x_4211_; uint8_t v_isShared_4212_; uint8_t v_isSharedCheck_4216_; 
lean_dec(v_attrName_4196_);
v_val_4209_ = lean_ctor_get(v___x_4200_, 0);
v_isSharedCheck_4216_ = !lean_is_exclusive(v___x_4200_);
if (v_isSharedCheck_4216_ == 0)
{
v___x_4211_ = v___x_4200_;
v_isShared_4212_ = v_isSharedCheck_4216_;
goto v_resetjp_4210_;
}
else
{
lean_inc(v_val_4209_);
lean_dec(v___x_4200_);
v___x_4211_ = lean_box(0);
v_isShared_4212_ = v_isSharedCheck_4216_;
goto v_resetjp_4210_;
}
v_resetjp_4210_:
{
lean_object* v___x_4214_; 
if (v_isShared_4212_ == 0)
{
lean_ctor_set_tag(v___x_4211_, 0);
v___x_4214_ = v___x_4211_;
goto v_reusejp_4213_;
}
else
{
lean_object* v_reuseFailAlloc_4215_; 
v_reuseFailAlloc_4215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4215_, 0, v_val_4209_);
v___x_4214_ = v_reuseFailAlloc_4215_;
goto v_reusejp_4213_;
}
v_reusejp_4213_:
{
return v___x_4214_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getBuiltinAttributeImpl___boxed(lean_object* v_attrName_4217_, lean_object* v_a_4218_){
_start:
{
lean_object* v_res_4219_; 
v_res_4219_ = l_Lean_getBuiltinAttributeImpl(v_attrName_4217_);
return v_res_4219_;
}
}
LEAN_EXPORT uint8_t l_Lean_isAttribute(lean_object* v_env_4220_, lean_object* v_attrName_4221_){
_start:
{
lean_object* v___x_4222_; lean_object* v_toEnvExtension_4223_; lean_object* v_asyncMode_4224_; lean_object* v___x_4225_; lean_object* v___x_4226_; lean_object* v___x_4227_; lean_object* v_map_4228_; uint8_t v___x_4229_; 
v___x_4222_ = l_Lean_attributeExtension;
v_toEnvExtension_4223_ = lean_ctor_get(v___x_4222_, 0);
v_asyncMode_4224_ = lean_ctor_get(v_toEnvExtension_4223_, 2);
v___x_4225_ = l_Lean_instInhabitedAttributeExtensionState_default;
v___x_4226_ = lean_box(0);
v___x_4227_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_4225_, v___x_4222_, v_env_4220_, v_asyncMode_4224_, v___x_4226_);
v_map_4228_ = lean_ctor_get(v___x_4227_, 1);
lean_inc_ref(v_map_4228_);
lean_dec(v___x_4227_);
v___x_4229_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(v_map_4228_, v_attrName_4221_);
lean_dec_ref(v_map_4228_);
return v___x_4229_;
}
}
LEAN_EXPORT lean_object* l_Lean_isAttribute___boxed(lean_object* v_env_4230_, lean_object* v_attrName_4231_){
_start:
{
uint8_t v_res_4232_; lean_object* v_r_4233_; 
v_res_4232_ = l_Lean_isAttribute(v_env_4230_, v_attrName_4231_);
lean_dec(v_attrName_4231_);
v_r_4233_ = lean_box(v_res_4232_);
return v_r_4233_;
}
}
LEAN_EXPORT lean_object* l_Lean_getAttributeNames(lean_object* v_env_4234_){
_start:
{
lean_object* v___x_4235_; lean_object* v_toEnvExtension_4236_; lean_object* v_asyncMode_4237_; lean_object* v___x_4238_; lean_object* v___x_4239_; lean_object* v___x_4240_; lean_object* v_map_4241_; lean_object* v_buckets_4242_; lean_object* v___x_4243_; lean_object* v___x_4244_; lean_object* v___x_4245_; uint8_t v___x_4246_; 
v___x_4235_ = l_Lean_attributeExtension;
v_toEnvExtension_4236_ = lean_ctor_get(v___x_4235_, 0);
v_asyncMode_4237_ = lean_ctor_get(v_toEnvExtension_4236_, 2);
v___x_4238_ = l_Lean_instInhabitedAttributeExtensionState_default;
v___x_4239_ = lean_box(0);
v___x_4240_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_4238_, v___x_4235_, v_env_4234_, v_asyncMode_4237_, v___x_4239_);
v_map_4241_ = lean_ctor_get(v___x_4240_, 1);
lean_inc_ref(v_map_4241_);
lean_dec(v___x_4240_);
v_buckets_4242_ = lean_ctor_get(v_map_4241_, 1);
lean_inc_ref(v_buckets_4242_);
lean_dec_ref(v_map_4241_);
v___x_4243_ = lean_box(0);
v___x_4244_ = lean_unsigned_to_nat(0u);
v___x_4245_ = lean_array_get_size(v_buckets_4242_);
v___x_4246_ = lean_nat_dec_lt(v___x_4244_, v___x_4245_);
if (v___x_4246_ == 0)
{
lean_dec_ref(v_buckets_4242_);
return v___x_4243_;
}
else
{
uint8_t v___x_4247_; 
v___x_4247_ = lean_nat_dec_le(v___x_4245_, v___x_4245_);
if (v___x_4247_ == 0)
{
if (v___x_4246_ == 0)
{
lean_dec_ref(v_buckets_4242_);
return v___x_4243_;
}
else
{
size_t v___x_4248_; size_t v___x_4249_; lean_object* v___x_4250_; 
v___x_4248_ = ((size_t)0ULL);
v___x_4249_ = lean_usize_of_nat(v___x_4245_);
v___x_4250_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1(v_buckets_4242_, v___x_4248_, v___x_4249_, v___x_4243_);
lean_dec_ref(v_buckets_4242_);
return v___x_4250_;
}
}
else
{
size_t v___x_4251_; size_t v___x_4252_; lean_object* v___x_4253_; 
v___x_4251_ = ((size_t)0ULL);
v___x_4252_ = lean_usize_of_nat(v___x_4245_);
v___x_4253_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1(v_buckets_4242_, v___x_4251_, v___x_4252_, v___x_4243_);
lean_dec_ref(v_buckets_4242_);
return v___x_4253_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getAttributeImpl(lean_object* v_env_4254_, lean_object* v_attrName_4255_){
_start:
{
lean_object* v___x_4256_; lean_object* v_toEnvExtension_4257_; lean_object* v_asyncMode_4258_; lean_object* v___x_4259_; lean_object* v___x_4260_; lean_object* v___x_4261_; lean_object* v_map_4262_; lean_object* v___x_4263_; 
v___x_4256_ = l_Lean_attributeExtension;
v_toEnvExtension_4257_ = lean_ctor_get(v___x_4256_, 0);
v_asyncMode_4258_ = lean_ctor_get(v_toEnvExtension_4257_, 2);
v___x_4259_ = l_Lean_instInhabitedAttributeExtensionState_default;
v___x_4260_ = lean_box(0);
v___x_4261_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_4259_, v___x_4256_, v_env_4254_, v_asyncMode_4258_, v___x_4260_);
v_map_4262_ = lean_ctor_get(v___x_4261_, 1);
lean_inc_ref(v_map_4262_);
lean_dec(v___x_4261_);
v___x_4263_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(v_map_4262_, v_attrName_4255_);
lean_dec_ref(v_map_4262_);
if (lean_obj_tag(v___x_4263_) == 0)
{
lean_object* v___x_4264_; uint8_t v___x_4265_; lean_object* v___x_4266_; lean_object* v___x_4267_; lean_object* v___x_4268_; lean_object* v___x_4269_; lean_object* v___x_4270_; 
v___x_4264_ = ((lean_object*)(l_Lean_getBuiltinAttributeImpl___closed__0));
v___x_4265_ = 1;
v___x_4266_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_attrName_4255_, v___x_4265_);
v___x_4267_ = lean_string_append(v___x_4264_, v___x_4266_);
lean_dec_ref(v___x_4266_);
v___x_4268_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__4));
v___x_4269_ = lean_string_append(v___x_4267_, v___x_4268_);
v___x_4270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4270_, 0, v___x_4269_);
return v___x_4270_;
}
else
{
lean_object* v_val_4271_; lean_object* v___x_4273_; uint8_t v_isShared_4274_; uint8_t v_isSharedCheck_4278_; 
lean_dec(v_attrName_4255_);
v_val_4271_ = lean_ctor_get(v___x_4263_, 0);
v_isSharedCheck_4278_ = !lean_is_exclusive(v___x_4263_);
if (v_isSharedCheck_4278_ == 0)
{
v___x_4273_ = v___x_4263_;
v_isShared_4274_ = v_isSharedCheck_4278_;
goto v_resetjp_4272_;
}
else
{
lean_inc(v_val_4271_);
lean_dec(v___x_4263_);
v___x_4273_ = lean_box(0);
v_isShared_4274_ = v_isSharedCheck_4278_;
goto v_resetjp_4272_;
}
v_resetjp_4272_:
{
lean_object* v___x_4276_; 
if (v_isShared_4274_ == 0)
{
v___x_4276_ = v___x_4273_;
goto v_reusejp_4275_;
}
else
{
lean_object* v_reuseFailAlloc_4277_; 
v_reuseFailAlloc_4277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4277_, 0, v_val_4271_);
v___x_4276_ = v_reuseFailAlloc_4277_;
goto v_reusejp_4275_;
}
v_reusejp_4275_:
{
return v___x_4276_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerAttributeOfBuilder(lean_object* v_env_4279_, lean_object* v_builderId_4280_, lean_object* v_ref_4281_, lean_object* v_args_4282_){
_start:
{
lean_object* v_entry_4284_; lean_object* v___x_4285_; 
v_entry_4284_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_entry_4284_, 0, v_builderId_4280_);
lean_ctor_set(v_entry_4284_, 1, v_ref_4281_);
lean_ctor_set(v_entry_4284_, 2, v_args_4282_);
lean_inc_ref(v_entry_4284_);
v___x_4285_ = l_Lean_mkAttributeImplOfEntry(v_entry_4284_);
if (lean_obj_tag(v___x_4285_) == 0)
{
lean_object* v_a_4286_; lean_object* v___x_4288_; uint8_t v_isShared_4289_; uint8_t v_isSharedCheck_4311_; 
v_a_4286_ = lean_ctor_get(v___x_4285_, 0);
v_isSharedCheck_4311_ = !lean_is_exclusive(v___x_4285_);
if (v_isSharedCheck_4311_ == 0)
{
v___x_4288_ = v___x_4285_;
v_isShared_4289_ = v_isSharedCheck_4311_;
goto v_resetjp_4287_;
}
else
{
lean_inc(v_a_4286_);
lean_dec(v___x_4285_);
v___x_4288_ = lean_box(0);
v_isShared_4289_ = v_isSharedCheck_4311_;
goto v_resetjp_4287_;
}
v_resetjp_4287_:
{
lean_object* v_toAttributeImplCore_4290_; lean_object* v_name_4291_; uint8_t v___x_4292_; 
v_toAttributeImplCore_4290_ = lean_ctor_get(v_a_4286_, 0);
v_name_4291_ = lean_ctor_get(v_toAttributeImplCore_4290_, 1);
lean_inc_ref(v_env_4279_);
v___x_4292_ = l_Lean_isAttribute(v_env_4279_, v_name_4291_);
if (v___x_4292_ == 0)
{
lean_object* v___x_4293_; lean_object* v_toEnvExtension_4294_; lean_object* v_asyncMode_4295_; lean_object* v___x_4296_; lean_object* v___x_4297_; lean_object* v___x_4298_; lean_object* v___x_4300_; 
v___x_4293_ = l_Lean_attributeExtension;
v_toEnvExtension_4294_ = lean_ctor_get(v___x_4293_, 0);
v_asyncMode_4295_ = lean_ctor_get(v_toEnvExtension_4294_, 2);
v___x_4296_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4296_, 0, v_entry_4284_);
lean_ctor_set(v___x_4296_, 1, v_a_4286_);
v___x_4297_ = lean_box(0);
v___x_4298_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_4293_, v_env_4279_, v___x_4296_, v_asyncMode_4295_, v___x_4297_);
if (v_isShared_4289_ == 0)
{
lean_ctor_set(v___x_4288_, 0, v___x_4298_);
v___x_4300_ = v___x_4288_;
goto v_reusejp_4299_;
}
else
{
lean_object* v_reuseFailAlloc_4301_; 
v_reuseFailAlloc_4301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4301_, 0, v___x_4298_);
v___x_4300_ = v_reuseFailAlloc_4301_;
goto v_reusejp_4299_;
}
v_reusejp_4299_:
{
return v___x_4300_;
}
}
else
{
lean_object* v___x_4302_; lean_object* v___x_4303_; lean_object* v___x_4304_; lean_object* v___x_4305_; lean_object* v___x_4306_; lean_object* v___x_4307_; lean_object* v___x_4309_; 
lean_inc(v_name_4291_);
lean_dec(v_a_4286_);
lean_dec_ref_known(v_entry_4284_, 3);
lean_dec_ref(v_env_4279_);
v___x_4302_ = ((lean_object*)(l_Lean_registerBuiltinAttribute___closed__2));
v___x_4303_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_4291_, v___x_4292_);
v___x_4304_ = lean_string_append(v___x_4302_, v___x_4303_);
lean_dec_ref(v___x_4303_);
v___x_4305_ = ((lean_object*)(l_Lean_registerBuiltinAttribute___closed__3));
v___x_4306_ = lean_string_append(v___x_4304_, v___x_4305_);
v___x_4307_ = lean_mk_io_user_error(v___x_4306_);
if (v_isShared_4289_ == 0)
{
lean_ctor_set_tag(v___x_4288_, 1);
lean_ctor_set(v___x_4288_, 0, v___x_4307_);
v___x_4309_ = v___x_4288_;
goto v_reusejp_4308_;
}
else
{
lean_object* v_reuseFailAlloc_4310_; 
v_reuseFailAlloc_4310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4310_, 0, v___x_4307_);
v___x_4309_ = v_reuseFailAlloc_4310_;
goto v_reusejp_4308_;
}
v_reusejp_4308_:
{
return v___x_4309_;
}
}
}
}
else
{
lean_object* v_a_4312_; lean_object* v___x_4314_; uint8_t v_isShared_4315_; uint8_t v_isSharedCheck_4319_; 
lean_dec_ref_known(v_entry_4284_, 3);
lean_dec_ref(v_env_4279_);
v_a_4312_ = lean_ctor_get(v___x_4285_, 0);
v_isSharedCheck_4319_ = !lean_is_exclusive(v___x_4285_);
if (v_isSharedCheck_4319_ == 0)
{
v___x_4314_ = v___x_4285_;
v_isShared_4315_ = v_isSharedCheck_4319_;
goto v_resetjp_4313_;
}
else
{
lean_inc(v_a_4312_);
lean_dec(v___x_4285_);
v___x_4314_ = lean_box(0);
v_isShared_4315_ = v_isSharedCheck_4319_;
goto v_resetjp_4313_;
}
v_resetjp_4313_:
{
lean_object* v___x_4317_; 
if (v_isShared_4315_ == 0)
{
v___x_4317_ = v___x_4314_;
goto v_reusejp_4316_;
}
else
{
lean_object* v_reuseFailAlloc_4318_; 
v_reuseFailAlloc_4318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4318_, 0, v_a_4312_);
v___x_4317_ = v_reuseFailAlloc_4318_;
goto v_reusejp_4316_;
}
v_reusejp_4316_:
{
return v___x_4317_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerAttributeOfBuilder___boxed(lean_object* v_env_4320_, lean_object* v_builderId_4321_, lean_object* v_ref_4322_, lean_object* v_args_4323_, lean_object* v_a_4324_){
_start:
{
lean_object* v_res_4325_; 
v_res_4325_ = l_Lean_registerAttributeOfBuilder(v_env_4320_, v_builderId_4321_, v_ref_4322_, v_args_4323_);
return v_res_4325_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg(lean_object* v_x_4326_, lean_object* v___y_4327_, lean_object* v___y_4328_){
_start:
{
if (lean_obj_tag(v_x_4326_) == 0)
{
lean_object* v_a_4330_; lean_object* v___x_4331_; lean_object* v___x_4332_; 
v_a_4330_ = lean_ctor_get(v_x_4326_, 0);
lean_inc(v_a_4330_);
lean_dec_ref_known(v_x_4326_, 1);
v___x_4331_ = l_Lean_stringToMessageData(v_a_4330_);
v___x_4332_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_4331_, v___y_4327_, v___y_4328_);
return v___x_4332_;
}
else
{
lean_object* v_a_4333_; lean_object* v___x_4335_; uint8_t v_isShared_4336_; uint8_t v_isSharedCheck_4340_; 
v_a_4333_ = lean_ctor_get(v_x_4326_, 0);
v_isSharedCheck_4340_ = !lean_is_exclusive(v_x_4326_);
if (v_isSharedCheck_4340_ == 0)
{
v___x_4335_ = v_x_4326_;
v_isShared_4336_ = v_isSharedCheck_4340_;
goto v_resetjp_4334_;
}
else
{
lean_inc(v_a_4333_);
lean_dec(v_x_4326_);
v___x_4335_ = lean_box(0);
v_isShared_4336_ = v_isSharedCheck_4340_;
goto v_resetjp_4334_;
}
v_resetjp_4334_:
{
lean_object* v___x_4338_; 
if (v_isShared_4336_ == 0)
{
lean_ctor_set_tag(v___x_4335_, 0);
v___x_4338_ = v___x_4335_;
goto v_reusejp_4337_;
}
else
{
lean_object* v_reuseFailAlloc_4339_; 
v_reuseFailAlloc_4339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4339_, 0, v_a_4333_);
v___x_4338_ = v_reuseFailAlloc_4339_;
goto v_reusejp_4337_;
}
v_reusejp_4337_:
{
return v___x_4338_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg___boxed(lean_object* v_x_4341_, lean_object* v___y_4342_, lean_object* v___y_4343_, lean_object* v___y_4344_){
_start:
{
lean_object* v_res_4345_; 
v_res_4345_ = l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg(v_x_4341_, v___y_4342_, v___y_4343_);
lean_dec(v___y_4343_);
lean_dec_ref(v___y_4342_);
return v_res_4345_;
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_add(lean_object* v_declName_4346_, lean_object* v_attrName_4347_, lean_object* v_stx_4348_, uint8_t v_kind_4349_, lean_object* v_a_4350_, lean_object* v_a_4351_){
_start:
{
lean_object* v___x_4353_; lean_object* v_env_4354_; lean_object* v___x_4355_; lean_object* v___x_4356_; 
v___x_4353_ = lean_st_ref_get(v_a_4351_);
v_env_4354_ = lean_ctor_get(v___x_4353_, 0);
lean_inc_ref(v_env_4354_);
lean_dec(v___x_4353_);
v___x_4355_ = l_Lean_getAttributeImpl(v_env_4354_, v_attrName_4347_);
v___x_4356_ = l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg(v___x_4355_, v_a_4350_, v_a_4351_);
if (lean_obj_tag(v___x_4356_) == 0)
{
lean_object* v_a_4357_; lean_object* v_add_4358_; lean_object* v___x_4359_; lean_object* v___x_4360_; 
v_a_4357_ = lean_ctor_get(v___x_4356_, 0);
lean_inc(v_a_4357_);
lean_dec_ref_known(v___x_4356_, 1);
v_add_4358_ = lean_ctor_get(v_a_4357_, 1);
lean_inc_ref(v_add_4358_);
lean_dec(v_a_4357_);
v___x_4359_ = lean_box(v_kind_4349_);
lean_inc(v_a_4351_);
lean_inc_ref(v_a_4350_);
v___x_4360_ = lean_apply_6(v_add_4358_, v_declName_4346_, v_stx_4348_, v___x_4359_, v_a_4350_, v_a_4351_, lean_box(0));
return v___x_4360_;
}
else
{
lean_object* v_a_4361_; lean_object* v___x_4363_; uint8_t v_isShared_4364_; uint8_t v_isSharedCheck_4368_; 
lean_dec(v_stx_4348_);
lean_dec(v_declName_4346_);
v_a_4361_ = lean_ctor_get(v___x_4356_, 0);
v_isSharedCheck_4368_ = !lean_is_exclusive(v___x_4356_);
if (v_isSharedCheck_4368_ == 0)
{
v___x_4363_ = v___x_4356_;
v_isShared_4364_ = v_isSharedCheck_4368_;
goto v_resetjp_4362_;
}
else
{
lean_inc(v_a_4361_);
lean_dec(v___x_4356_);
v___x_4363_ = lean_box(0);
v_isShared_4364_ = v_isSharedCheck_4368_;
goto v_resetjp_4362_;
}
v_resetjp_4362_:
{
lean_object* v___x_4366_; 
if (v_isShared_4364_ == 0)
{
v___x_4366_ = v___x_4363_;
goto v_reusejp_4365_;
}
else
{
lean_object* v_reuseFailAlloc_4367_; 
v_reuseFailAlloc_4367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4367_, 0, v_a_4361_);
v___x_4366_ = v_reuseFailAlloc_4367_;
goto v_reusejp_4365_;
}
v_reusejp_4365_:
{
return v___x_4366_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_add___boxed(lean_object* v_declName_4369_, lean_object* v_attrName_4370_, lean_object* v_stx_4371_, lean_object* v_kind_4372_, lean_object* v_a_4373_, lean_object* v_a_4374_, lean_object* v_a_4375_){
_start:
{
uint8_t v_kind_boxed_4376_; lean_object* v_res_4377_; 
v_kind_boxed_4376_ = lean_unbox(v_kind_4372_);
v_res_4377_ = l_Lean_Attribute_add(v_declName_4369_, v_attrName_4370_, v_stx_4371_, v_kind_boxed_4376_, v_a_4373_, v_a_4374_);
lean_dec(v_a_4374_);
lean_dec_ref(v_a_4373_);
return v_res_4377_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0(lean_object* v_00_u03b1_4378_, lean_object* v_x_4379_, lean_object* v___y_4380_, lean_object* v___y_4381_){
_start:
{
lean_object* v___x_4383_; 
v___x_4383_ = l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg(v_x_4379_, v___y_4380_, v___y_4381_);
return v___x_4383_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___boxed(lean_object* v_00_u03b1_4384_, lean_object* v_x_4385_, lean_object* v___y_4386_, lean_object* v___y_4387_, lean_object* v___y_4388_){
_start:
{
lean_object* v_res_4389_; 
v_res_4389_ = l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0(v_00_u03b1_4384_, v_x_4385_, v___y_4386_, v___y_4387_);
lean_dec(v___y_4387_);
lean_dec_ref(v___y_4386_);
return v_res_4389_;
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_erase(lean_object* v_declName_4390_, lean_object* v_attrName_4391_, lean_object* v_a_4392_, lean_object* v_a_4393_){
_start:
{
lean_object* v___x_4395_; lean_object* v_env_4396_; lean_object* v___x_4397_; lean_object* v___x_4398_; 
v___x_4395_ = lean_st_ref_get(v_a_4393_);
v_env_4396_ = lean_ctor_get(v___x_4395_, 0);
lean_inc_ref(v_env_4396_);
lean_dec(v___x_4395_);
v___x_4397_ = l_Lean_getAttributeImpl(v_env_4396_, v_attrName_4391_);
v___x_4398_ = l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg(v___x_4397_, v_a_4392_, v_a_4393_);
if (lean_obj_tag(v___x_4398_) == 0)
{
lean_object* v_a_4399_; lean_object* v_erase_4400_; lean_object* v___x_4401_; 
v_a_4399_ = lean_ctor_get(v___x_4398_, 0);
lean_inc(v_a_4399_);
lean_dec_ref_known(v___x_4398_, 1);
v_erase_4400_ = lean_ctor_get(v_a_4399_, 2);
lean_inc_ref(v_erase_4400_);
lean_dec(v_a_4399_);
lean_inc(v_a_4393_);
lean_inc_ref(v_a_4392_);
v___x_4401_ = lean_apply_4(v_erase_4400_, v_declName_4390_, v_a_4392_, v_a_4393_, lean_box(0));
return v___x_4401_;
}
else
{
lean_object* v_a_4402_; lean_object* v___x_4404_; uint8_t v_isShared_4405_; uint8_t v_isSharedCheck_4409_; 
lean_dec(v_declName_4390_);
v_a_4402_ = lean_ctor_get(v___x_4398_, 0);
v_isSharedCheck_4409_ = !lean_is_exclusive(v___x_4398_);
if (v_isSharedCheck_4409_ == 0)
{
v___x_4404_ = v___x_4398_;
v_isShared_4405_ = v_isSharedCheck_4409_;
goto v_resetjp_4403_;
}
else
{
lean_inc(v_a_4402_);
lean_dec(v___x_4398_);
v___x_4404_ = lean_box(0);
v_isShared_4405_ = v_isSharedCheck_4409_;
goto v_resetjp_4403_;
}
v_resetjp_4403_:
{
lean_object* v___x_4407_; 
if (v_isShared_4405_ == 0)
{
v___x_4407_ = v___x_4404_;
goto v_reusejp_4406_;
}
else
{
lean_object* v_reuseFailAlloc_4408_; 
v_reuseFailAlloc_4408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4408_, 0, v_a_4402_);
v___x_4407_ = v_reuseFailAlloc_4408_;
goto v_reusejp_4406_;
}
v_reusejp_4406_:
{
return v___x_4407_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_erase___boxed(lean_object* v_declName_4410_, lean_object* v_attrName_4411_, lean_object* v_a_4412_, lean_object* v_a_4413_, lean_object* v_a_4414_){
_start:
{
lean_object* v_res_4415_; 
v_res_4415_ = l_Lean_Attribute_erase(v_declName_4410_, v_attrName_4411_, v_a_4412_, v_a_4413_);
lean_dec(v_a_4413_);
lean_dec_ref(v_a_4412_);
return v_res_4415_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_updateEnvAttributesImpl_spec__0(lean_object* v_x_4416_, lean_object* v_x_4417_){
_start:
{
if (lean_obj_tag(v_x_4417_) == 0)
{
return v_x_4416_;
}
else
{
lean_object* v_key_4418_; lean_object* v_value_4419_; lean_object* v_tail_4420_; lean_object* v_newEntries_4421_; lean_object* v_map_4422_; uint8_t v___x_4423_; 
v_key_4418_ = lean_ctor_get(v_x_4417_, 0);
lean_inc(v_key_4418_);
v_value_4419_ = lean_ctor_get(v_x_4417_, 1);
lean_inc(v_value_4419_);
v_tail_4420_ = lean_ctor_get(v_x_4417_, 2);
lean_inc(v_tail_4420_);
lean_dec_ref_known(v_x_4417_, 3);
v_newEntries_4421_ = lean_ctor_get(v_x_4416_, 0);
v_map_4422_ = lean_ctor_get(v_x_4416_, 1);
v___x_4423_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(v_map_4422_, v_key_4418_);
if (v___x_4423_ == 0)
{
lean_object* v___x_4425_; uint8_t v_isShared_4426_; uint8_t v_isSharedCheck_4432_; 
lean_inc_ref(v_map_4422_);
lean_inc(v_newEntries_4421_);
v_isSharedCheck_4432_ = !lean_is_exclusive(v_x_4416_);
if (v_isSharedCheck_4432_ == 0)
{
lean_object* v_unused_4433_; lean_object* v_unused_4434_; 
v_unused_4433_ = lean_ctor_get(v_x_4416_, 1);
lean_dec(v_unused_4433_);
v_unused_4434_ = lean_ctor_get(v_x_4416_, 0);
lean_dec(v_unused_4434_);
v___x_4425_ = v_x_4416_;
v_isShared_4426_ = v_isSharedCheck_4432_;
goto v_resetjp_4424_;
}
else
{
lean_dec(v_x_4416_);
v___x_4425_ = lean_box(0);
v_isShared_4426_ = v_isSharedCheck_4432_;
goto v_resetjp_4424_;
}
v_resetjp_4424_:
{
lean_object* v___x_4427_; lean_object* v___x_4429_; 
v___x_4427_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1___redArg(v_map_4422_, v_key_4418_, v_value_4419_);
if (v_isShared_4426_ == 0)
{
lean_ctor_set(v___x_4425_, 1, v___x_4427_);
v___x_4429_ = v___x_4425_;
goto v_reusejp_4428_;
}
else
{
lean_object* v_reuseFailAlloc_4431_; 
v_reuseFailAlloc_4431_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4431_, 0, v_newEntries_4421_);
lean_ctor_set(v_reuseFailAlloc_4431_, 1, v___x_4427_);
v___x_4429_ = v_reuseFailAlloc_4431_;
goto v_reusejp_4428_;
}
v_reusejp_4428_:
{
v_x_4416_ = v___x_4429_;
v_x_4417_ = v_tail_4420_;
goto _start;
}
}
}
else
{
lean_dec(v_value_4419_);
lean_dec(v_key_4418_);
v_x_4417_ = v_tail_4420_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_updateEnvAttributesImpl_spec__1(lean_object* v_as_4436_, size_t v_i_4437_, size_t v_stop_4438_, lean_object* v_b_4439_){
_start:
{
uint8_t v___x_4440_; 
v___x_4440_ = lean_usize_dec_eq(v_i_4437_, v_stop_4438_);
if (v___x_4440_ == 0)
{
lean_object* v___x_4441_; lean_object* v___x_4442_; size_t v___x_4443_; size_t v___x_4444_; 
v___x_4441_ = lean_array_uget_borrowed(v_as_4436_, v_i_4437_);
lean_inc(v___x_4441_);
v___x_4442_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_updateEnvAttributesImpl_spec__0(v_b_4439_, v___x_4441_);
v___x_4443_ = ((size_t)1ULL);
v___x_4444_ = lean_usize_add(v_i_4437_, v___x_4443_);
v_i_4437_ = v___x_4444_;
v_b_4439_ = v___x_4442_;
goto _start;
}
else
{
return v_b_4439_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_updateEnvAttributesImpl_spec__1___boxed(lean_object* v_as_4446_, lean_object* v_i_4447_, lean_object* v_stop_4448_, lean_object* v_b_4449_){
_start:
{
size_t v_i_boxed_4450_; size_t v_stop_boxed_4451_; lean_object* v_res_4452_; 
v_i_boxed_4450_ = lean_unbox_usize(v_i_4447_);
lean_dec(v_i_4447_);
v_stop_boxed_4451_ = lean_unbox_usize(v_stop_4448_);
lean_dec(v_stop_4448_);
v_res_4452_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_updateEnvAttributesImpl_spec__1(v_as_4446_, v_i_boxed_4450_, v_stop_boxed_4451_, v_b_4449_);
lean_dec_ref(v_as_4446_);
return v_res_4452_;
}
}
LEAN_EXPORT lean_object* lean_update_env_attributes(lean_object* v_env_4453_){
_start:
{
lean_object* v___x_4455_; lean_object* v___x_4456_; lean_object* v___x_4457_; lean_object* v___y_4459_; lean_object* v_toEnvExtension_4462_; lean_object* v_asyncMode_4463_; lean_object* v_buckets_4464_; lean_object* v___x_4465_; lean_object* v___x_4466_; lean_object* v___x_4467_; lean_object* v___x_4468_; lean_object* v___x_4469_; uint8_t v___x_4470_; 
v___x_4455_ = l_Lean_attributeMapRef;
v___x_4456_ = lean_st_ref_get(v___x_4455_);
v___x_4457_ = l_Lean_attributeExtension;
v_toEnvExtension_4462_ = lean_ctor_get(v___x_4457_, 0);
v_asyncMode_4463_ = lean_ctor_get(v_toEnvExtension_4462_, 2);
v_buckets_4464_ = lean_ctor_get(v___x_4456_, 1);
lean_inc_ref(v_buckets_4464_);
lean_dec(v___x_4456_);
v___x_4465_ = l_Lean_instInhabitedAttributeExtensionState_default;
v___x_4466_ = lean_box(0);
lean_inc_ref(v_env_4453_);
v___x_4467_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_4465_, v___x_4457_, v_env_4453_, v_asyncMode_4463_, v___x_4466_);
v___x_4468_ = lean_unsigned_to_nat(0u);
v___x_4469_ = lean_array_get_size(v_buckets_4464_);
v___x_4470_ = lean_nat_dec_lt(v___x_4468_, v___x_4469_);
if (v___x_4470_ == 0)
{
lean_dec_ref(v_buckets_4464_);
v___y_4459_ = v___x_4467_;
goto v___jp_4458_;
}
else
{
uint8_t v___x_4471_; 
v___x_4471_ = lean_nat_dec_le(v___x_4469_, v___x_4469_);
if (v___x_4471_ == 0)
{
if (v___x_4470_ == 0)
{
lean_dec_ref(v_buckets_4464_);
v___y_4459_ = v___x_4467_;
goto v___jp_4458_;
}
else
{
size_t v___x_4472_; size_t v___x_4473_; lean_object* v___x_4474_; 
v___x_4472_ = ((size_t)0ULL);
v___x_4473_ = lean_usize_of_nat(v___x_4469_);
v___x_4474_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_updateEnvAttributesImpl_spec__1(v_buckets_4464_, v___x_4472_, v___x_4473_, v___x_4467_);
lean_dec_ref(v_buckets_4464_);
v___y_4459_ = v___x_4474_;
goto v___jp_4458_;
}
}
else
{
size_t v___x_4475_; size_t v___x_4476_; lean_object* v___x_4477_; 
v___x_4475_ = ((size_t)0ULL);
v___x_4476_ = lean_usize_of_nat(v___x_4469_);
v___x_4477_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_updateEnvAttributesImpl_spec__1(v_buckets_4464_, v___x_4475_, v___x_4476_, v___x_4467_);
lean_dec_ref(v_buckets_4464_);
v___y_4459_ = v___x_4477_;
goto v___jp_4458_;
}
}
v___jp_4458_:
{
lean_object* v___x_4460_; lean_object* v___x_4461_; 
v___x_4460_ = l_Lean_PersistentEnvExtension_setState___redArg(v___x_4457_, v_env_4453_, v___y_4459_);
v___x_4461_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4461_, 0, v___x_4460_);
return v___x_4461_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_updateEnvAttributesImpl___boxed(lean_object* v_env_4478_, lean_object* v_a_4479_){
_start:
{
lean_object* v_res_4480_; 
v_res_4480_ = lean_update_env_attributes(v_env_4478_);
return v_res_4480_;
}
}
LEAN_EXPORT lean_object* lean_get_num_attributes(){
_start:
{
lean_object* v___x_4482_; lean_object* v___x_4483_; lean_object* v_size_4484_; lean_object* v___x_4485_; 
v___x_4482_ = l_Lean_attributeMapRef;
v___x_4483_ = lean_st_ref_get(v___x_4482_);
v_size_4484_ = lean_ctor_get(v___x_4483_, 0);
lean_inc(v_size_4484_);
lean_dec(v___x_4483_);
v___x_4485_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4485_, 0, v_size_4484_);
return v___x_4485_;
}
}
LEAN_EXPORT lean_object* l_Lean_getNumBuiltinAttributesImpl___boxed(lean_object* v_a_4486_){
_start:
{
lean_object* v_res_4487_; 
v_res_4487_ = lean_get_num_attributes();
return v_res_4487_;
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
