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
lean_object* l_Lean_Environment_header(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4___redArg(lean_object* v_hi_1758_, lean_object* v_pivot_1759_, lean_object* v_as_1760_, lean_object* v_i_1761_, lean_object* v_k_1762_){
_start:
{
uint8_t v___x_1763_; 
v___x_1763_ = lean_nat_dec_lt(v_k_1762_, v_hi_1758_);
if (v___x_1763_ == 0)
{
lean_object* v___x_1764_; lean_object* v___x_1765_; 
lean_dec(v_k_1762_);
v___x_1764_ = lean_array_fswap(v_as_1760_, v_i_1761_, v_hi_1758_);
v___x_1765_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1765_, 0, v_i_1761_);
lean_ctor_set(v___x_1765_, 1, v___x_1764_);
return v___x_1765_;
}
else
{
lean_object* v___x_1766_; uint8_t v___x_1767_; 
v___x_1766_ = lean_array_fget_borrowed(v_as_1760_, v_k_1762_);
v___x_1767_ = l_Lean_Name_quickLt(v___x_1766_, v_pivot_1759_);
if (v___x_1767_ == 0)
{
lean_object* v___x_1768_; lean_object* v___x_1769_; 
v___x_1768_ = lean_unsigned_to_nat(1u);
v___x_1769_ = lean_nat_add(v_k_1762_, v___x_1768_);
lean_dec(v_k_1762_);
v_k_1762_ = v___x_1769_;
goto _start;
}
else
{
lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; 
v___x_1771_ = lean_array_fswap(v_as_1760_, v_i_1761_, v_k_1762_);
v___x_1772_ = lean_unsigned_to_nat(1u);
v___x_1773_ = lean_nat_add(v_i_1761_, v___x_1772_);
lean_dec(v_i_1761_);
v___x_1774_ = lean_nat_add(v_k_1762_, v___x_1772_);
lean_dec(v_k_1762_);
v_as_1760_ = v___x_1771_;
v_i_1761_ = v___x_1773_;
v_k_1762_ = v___x_1774_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4___redArg___boxed(lean_object* v_hi_1776_, lean_object* v_pivot_1777_, lean_object* v_as_1778_, lean_object* v_i_1779_, lean_object* v_k_1780_){
_start:
{
lean_object* v_res_1781_; 
v_res_1781_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4___redArg(v_hi_1776_, v_pivot_1777_, v_as_1778_, v_i_1779_, v_k_1780_);
lean_dec(v_pivot_1777_);
lean_dec(v_hi_1776_);
return v_res_1781_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___redArg(lean_object* v_n_1782_, lean_object* v_as_1783_, lean_object* v_lo_1784_, lean_object* v_hi_1785_){
_start:
{
lean_object* v___y_1787_; uint8_t v___x_1797_; 
v___x_1797_ = lean_nat_dec_lt(v_lo_1784_, v_hi_1785_);
if (v___x_1797_ == 0)
{
lean_dec(v_lo_1784_);
return v_as_1783_;
}
else
{
lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v_mid_1800_; lean_object* v___y_1802_; lean_object* v___y_1808_; lean_object* v___x_1813_; lean_object* v___x_1814_; uint8_t v___x_1815_; 
v___x_1798_ = lean_nat_add(v_lo_1784_, v_hi_1785_);
v___x_1799_ = lean_unsigned_to_nat(1u);
v_mid_1800_ = lean_nat_shiftr(v___x_1798_, v___x_1799_);
lean_dec(v___x_1798_);
v___x_1813_ = lean_array_fget_borrowed(v_as_1783_, v_mid_1800_);
v___x_1814_ = lean_array_fget_borrowed(v_as_1783_, v_lo_1784_);
v___x_1815_ = l_Lean_Name_quickLt(v___x_1813_, v___x_1814_);
if (v___x_1815_ == 0)
{
v___y_1808_ = v_as_1783_;
goto v___jp_1807_;
}
else
{
lean_object* v___x_1816_; 
v___x_1816_ = lean_array_fswap(v_as_1783_, v_lo_1784_, v_mid_1800_);
v___y_1808_ = v___x_1816_;
goto v___jp_1807_;
}
v___jp_1801_:
{
lean_object* v___x_1803_; lean_object* v___x_1804_; uint8_t v___x_1805_; 
v___x_1803_ = lean_array_fget_borrowed(v___y_1802_, v_mid_1800_);
v___x_1804_ = lean_array_fget_borrowed(v___y_1802_, v_hi_1785_);
v___x_1805_ = l_Lean_Name_quickLt(v___x_1803_, v___x_1804_);
if (v___x_1805_ == 0)
{
lean_dec(v_mid_1800_);
v___y_1787_ = v___y_1802_;
goto v___jp_1786_;
}
else
{
lean_object* v___x_1806_; 
v___x_1806_ = lean_array_fswap(v___y_1802_, v_mid_1800_, v_hi_1785_);
lean_dec(v_mid_1800_);
v___y_1787_ = v___x_1806_;
goto v___jp_1786_;
}
}
v___jp_1807_:
{
lean_object* v___x_1809_; lean_object* v___x_1810_; uint8_t v___x_1811_; 
v___x_1809_ = lean_array_fget_borrowed(v___y_1808_, v_hi_1785_);
v___x_1810_ = lean_array_fget_borrowed(v___y_1808_, v_lo_1784_);
v___x_1811_ = l_Lean_Name_quickLt(v___x_1809_, v___x_1810_);
if (v___x_1811_ == 0)
{
v___y_1802_ = v___y_1808_;
goto v___jp_1801_;
}
else
{
lean_object* v___x_1812_; 
v___x_1812_ = lean_array_fswap(v___y_1808_, v_lo_1784_, v_hi_1785_);
v___y_1802_ = v___x_1812_;
goto v___jp_1801_;
}
}
}
v___jp_1786_:
{
lean_object* v_pivot_1788_; lean_object* v___x_1789_; lean_object* v_fst_1790_; lean_object* v_snd_1791_; uint8_t v___x_1792_; 
v_pivot_1788_ = lean_array_fget(v___y_1787_, v_hi_1785_);
lean_inc_n(v_lo_1784_, 2);
v___x_1789_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4___redArg(v_hi_1785_, v_pivot_1788_, v___y_1787_, v_lo_1784_, v_lo_1784_);
lean_dec(v_pivot_1788_);
v_fst_1790_ = lean_ctor_get(v___x_1789_, 0);
lean_inc(v_fst_1790_);
v_snd_1791_ = lean_ctor_get(v___x_1789_, 1);
lean_inc(v_snd_1791_);
lean_dec_ref(v___x_1789_);
v___x_1792_ = lean_nat_dec_le(v_hi_1785_, v_fst_1790_);
if (v___x_1792_ == 0)
{
lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; 
v___x_1793_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___redArg(v_n_1782_, v_snd_1791_, v_lo_1784_, v_fst_1790_);
v___x_1794_ = lean_unsigned_to_nat(1u);
v___x_1795_ = lean_nat_add(v_fst_1790_, v___x_1794_);
lean_dec(v_fst_1790_);
v_as_1783_ = v___x_1793_;
v_lo_1784_ = v___x_1795_;
goto _start;
}
else
{
lean_dec(v_fst_1790_);
lean_dec(v_lo_1784_);
return v_snd_1791_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___redArg___boxed(lean_object* v_n_1817_, lean_object* v_as_1818_, lean_object* v_lo_1819_, lean_object* v_hi_1820_){
_start:
{
lean_object* v_res_1821_; 
v_res_1821_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___redArg(v_n_1817_, v_as_1818_, v_lo_1819_, v_hi_1820_);
lean_dec(v_hi_1820_);
lean_dec(v_n_1817_);
return v_res_1821_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerTagAttribute_spec__2(lean_object* v_env_1822_, lean_object* v_as_1823_, size_t v_i_1824_, size_t v_stop_1825_, lean_object* v_b_1826_){
_start:
{
lean_object* v___y_1828_; uint8_t v___x_1832_; 
v___x_1832_ = lean_usize_dec_eq(v_i_1824_, v_stop_1825_);
if (v___x_1832_ == 0)
{
lean_object* v___x_1833_; uint8_t v___x_1834_; lean_object* v___x_1835_; uint8_t v___x_1836_; 
v___x_1833_ = lean_array_uget_borrowed(v_as_1823_, v_i_1824_);
v___x_1834_ = 1;
lean_inc_ref(v_env_1822_);
v___x_1835_ = l_Lean_Environment_setExporting(v_env_1822_, v___x_1834_);
lean_inc(v___x_1833_);
v___x_1836_ = l_Lean_Environment_contains(v___x_1835_, v___x_1833_, v___x_1832_);
if (v___x_1836_ == 0)
{
v___y_1828_ = v_b_1826_;
goto v___jp_1827_;
}
else
{
lean_object* v___x_1837_; 
lean_inc(v___x_1833_);
v___x_1837_ = lean_array_push(v_b_1826_, v___x_1833_);
v___y_1828_ = v___x_1837_;
goto v___jp_1827_;
}
}
else
{
lean_dec_ref(v_env_1822_);
return v_b_1826_;
}
v___jp_1827_:
{
size_t v___x_1829_; size_t v___x_1830_; 
v___x_1829_ = ((size_t)1ULL);
v___x_1830_ = lean_usize_add(v_i_1824_, v___x_1829_);
v_i_1824_ = v___x_1830_;
v_b_1826_ = v___y_1828_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerTagAttribute_spec__2___boxed(lean_object* v_env_1838_, lean_object* v_as_1839_, lean_object* v_i_1840_, lean_object* v_stop_1841_, lean_object* v_b_1842_){
_start:
{
size_t v_i_boxed_1843_; size_t v_stop_boxed_1844_; lean_object* v_res_1845_; 
v_i_boxed_1843_ = lean_unbox_usize(v_i_1840_);
lean_dec(v_i_1840_);
v_stop_boxed_1844_ = lean_unbox_usize(v_stop_1841_);
lean_dec(v_stop_1841_);
v_res_1845_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerTagAttribute_spec__2(v_env_1838_, v_as_1839_, v_i_boxed_1843_, v_stop_boxed_1844_, v_b_1842_);
lean_dec_ref(v_as_1839_);
return v_res_1845_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerTagAttribute_spec__1_spec__1(lean_object* v_init_1846_, lean_object* v_x_1847_){
_start:
{
if (lean_obj_tag(v_x_1847_) == 0)
{
lean_object* v_k_1848_; lean_object* v_l_1849_; lean_object* v_r_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; 
v_k_1848_ = lean_ctor_get(v_x_1847_, 1);
lean_inc(v_k_1848_);
v_l_1849_ = lean_ctor_get(v_x_1847_, 3);
lean_inc(v_l_1849_);
v_r_1850_ = lean_ctor_get(v_x_1847_, 4);
lean_inc(v_r_1850_);
lean_dec_ref(v_x_1847_);
v___x_1851_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerTagAttribute_spec__1_spec__1(v_init_1846_, v_l_1849_);
v___x_1852_ = lean_array_push(v___x_1851_, v_k_1848_);
v_init_1846_ = v___x_1852_;
v_x_1847_ = v_r_1850_;
goto _start;
}
else
{
return v_init_1846_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__3(lean_object* v_env_1854_, lean_object* v_es_1855_){
_start:
{
lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___y_1859_; lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___y_1876_; lean_object* v___y_1877_; uint8_t v___x_1879_; 
v___x_1856_ = lean_unsigned_to_nat(0u);
v___x_1857_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___lam__2___closed__0));
v___x_1873_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerTagAttribute_spec__1_spec__1(v___x_1857_, v_es_1855_);
v___x_1874_ = lean_array_get_size(v___x_1873_);
v___x_1879_ = lean_nat_dec_eq(v___x_1874_, v___x_1856_);
if (v___x_1879_ == 0)
{
lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___y_1883_; uint8_t v___x_1885_; 
v___x_1880_ = lean_unsigned_to_nat(1u);
v___x_1881_ = lean_nat_sub(v___x_1874_, v___x_1880_);
v___x_1885_ = lean_nat_dec_le(v___x_1856_, v___x_1881_);
if (v___x_1885_ == 0)
{
lean_inc(v___x_1881_);
v___y_1883_ = v___x_1881_;
goto v___jp_1882_;
}
else
{
v___y_1883_ = v___x_1856_;
goto v___jp_1882_;
}
v___jp_1882_:
{
uint8_t v___x_1884_; 
v___x_1884_ = lean_nat_dec_le(v___y_1883_, v___x_1881_);
if (v___x_1884_ == 0)
{
lean_dec(v___x_1881_);
lean_inc(v___y_1883_);
v___y_1876_ = v___y_1883_;
v___y_1877_ = v___y_1883_;
goto v___jp_1875_;
}
else
{
v___y_1876_ = v___y_1883_;
v___y_1877_ = v___x_1881_;
goto v___jp_1875_;
}
}
}
else
{
v___y_1859_ = v___x_1873_;
goto v___jp_1858_;
}
v___jp_1858_:
{
lean_object* v___x_1860_; uint8_t v___x_1861_; 
v___x_1860_ = lean_array_get_size(v___y_1859_);
v___x_1861_ = lean_nat_dec_lt(v___x_1856_, v___x_1860_);
if (v___x_1861_ == 0)
{
lean_object* v___x_1862_; 
lean_dec_ref(v_env_1854_);
v___x_1862_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1862_, 0, v___x_1857_);
lean_ctor_set(v___x_1862_, 1, v___x_1857_);
lean_ctor_set(v___x_1862_, 2, v___y_1859_);
return v___x_1862_;
}
else
{
uint8_t v___x_1863_; 
v___x_1863_ = lean_nat_dec_le(v___x_1860_, v___x_1860_);
if (v___x_1863_ == 0)
{
if (v___x_1861_ == 0)
{
lean_object* v___x_1864_; 
lean_dec_ref(v_env_1854_);
v___x_1864_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1864_, 0, v___x_1857_);
lean_ctor_set(v___x_1864_, 1, v___x_1857_);
lean_ctor_set(v___x_1864_, 2, v___y_1859_);
return v___x_1864_;
}
else
{
size_t v___x_1865_; size_t v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; 
v___x_1865_ = ((size_t)0ULL);
v___x_1866_ = lean_usize_of_nat(v___x_1860_);
v___x_1867_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerTagAttribute_spec__2(v_env_1854_, v___y_1859_, v___x_1865_, v___x_1866_, v___x_1857_);
lean_inc_ref(v___x_1867_);
v___x_1868_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1868_, 0, v___x_1867_);
lean_ctor_set(v___x_1868_, 1, v___x_1867_);
lean_ctor_set(v___x_1868_, 2, v___y_1859_);
return v___x_1868_;
}
}
else
{
size_t v___x_1869_; size_t v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; 
v___x_1869_ = ((size_t)0ULL);
v___x_1870_ = lean_usize_of_nat(v___x_1860_);
v___x_1871_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerTagAttribute_spec__2(v_env_1854_, v___y_1859_, v___x_1869_, v___x_1870_, v___x_1857_);
lean_inc_ref(v___x_1871_);
v___x_1872_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1872_, 0, v___x_1871_);
lean_ctor_set(v___x_1872_, 1, v___x_1871_);
lean_ctor_set(v___x_1872_, 2, v___y_1859_);
return v___x_1872_;
}
}
}
v___jp_1875_:
{
lean_object* v___x_1878_; 
v___x_1878_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___redArg(v___x_1874_, v___x_1873_, v___y_1876_, v___y_1877_);
lean_dec(v___y_1877_);
v___y_1859_ = v___x_1878_;
goto v___jp_1858_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__4(lean_object* v___x_1886_, lean_object* v_x_1887_, lean_object* v_x_1888_){
_start:
{
lean_object* v___x_1890_; 
v___x_1890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1890_, 0, v___x_1886_);
return v___x_1890_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__4___boxed(lean_object* v___x_1891_, lean_object* v_x_1892_, lean_object* v_x_1893_, lean_object* v___y_1894_){
_start:
{
lean_object* v_res_1895_; 
v_res_1895_ = l_Lean_registerTagAttribute___lam__4(v___x_1891_, v_x_1892_, v_x_1893_);
lean_dec_ref(v_x_1893_);
lean_dec_ref(v_x_1892_);
return v_res_1895_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__5(lean_object* v___x_1896_){
_start:
{
lean_object* v___x_1898_; 
v___x_1898_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1898_, 0, v___x_1896_);
return v___x_1898_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__5___boxed(lean_object* v___x_1899_, lean_object* v___y_1900_){
_start:
{
lean_object* v_res_1901_; 
v_res_1901_ = l_Lean_registerTagAttribute___lam__5(v___x_1899_);
return v_res_1901_;
}
}
static lean_object* _init_l_Lean_registerTagAttribute___lam__6___closed__1(void){
_start:
{
lean_object* v___x_1903_; lean_object* v___x_1904_; 
v___x_1903_ = ((lean_object*)(l_Lean_registerTagAttribute___lam__6___closed__0));
v___x_1904_ = l_Lean_stringToMessageData(v___x_1903_);
return v___x_1904_;
}
}
static lean_object* _init_l_Lean_registerTagAttribute___lam__6___closed__3(void){
_start:
{
lean_object* v___x_1906_; lean_object* v___x_1907_; 
v___x_1906_ = ((lean_object*)(l_Lean_registerTagAttribute___lam__6___closed__2));
v___x_1907_ = l_Lean_stringToMessageData(v___x_1906_);
return v___x_1907_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__6(lean_object* v_name_1908_, lean_object* v_decl_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_){
_start:
{
lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; 
v___x_1913_ = lean_obj_once(&l_Lean_registerTagAttribute___lam__6___closed__1, &l_Lean_registerTagAttribute___lam__6___closed__1_once, _init_l_Lean_registerTagAttribute___lam__6___closed__1);
v___x_1914_ = l_Lean_MessageData_ofName(v_name_1908_);
v___x_1915_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1915_, 0, v___x_1913_);
lean_ctor_set(v___x_1915_, 1, v___x_1914_);
v___x_1916_ = lean_obj_once(&l_Lean_registerTagAttribute___lam__6___closed__3, &l_Lean_registerTagAttribute___lam__6___closed__3_once, _init_l_Lean_registerTagAttribute___lam__6___closed__3);
v___x_1917_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1917_, 0, v___x_1915_);
lean_ctor_set(v___x_1917_, 1, v___x_1916_);
v___x_1918_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0_spec__0___redArg(v___x_1917_, v___y_1910_, v___y_1911_);
return v___x_1918_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__6___boxed(lean_object* v_name_1919_, lean_object* v_decl_1920_, lean_object* v___y_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_){
_start:
{
lean_object* v_res_1924_; 
v_res_1924_ = l_Lean_registerTagAttribute___lam__6(v_name_1919_, v_decl_1920_, v___y_1921_, v___y_1922_);
lean_dec(v___y_1922_);
lean_dec_ref(v___y_1921_);
lean_dec(v_decl_1920_);
return v_res_1924_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg(lean_object* v_attrName_1925_, lean_object* v_declName_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_){
_start:
{
lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; uint8_t v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; 
v___x_1930_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1);
v___x_1931_ = l_Lean_MessageData_ofName(v_attrName_1925_);
v___x_1932_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1932_, 0, v___x_1930_);
lean_ctor_set(v___x_1932_, 1, v___x_1931_);
v___x_1933_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__3, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__3_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__3);
v___x_1934_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1934_, 0, v___x_1932_);
lean_ctor_set(v___x_1934_, 1, v___x_1933_);
v___x_1935_ = 0;
v___x_1936_ = l_Lean_MessageData_ofConstName(v_declName_1926_, v___x_1935_);
v___x_1937_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1937_, 0, v___x_1934_);
lean_ctor_set(v___x_1937_, 1, v___x_1936_);
v___x_1938_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__5, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__5_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__5);
v___x_1939_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1939_, 0, v___x_1937_);
lean_ctor_set(v___x_1939_, 1, v___x_1938_);
v___x_1940_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0_spec__0___redArg(v___x_1939_, v___y_1927_, v___y_1928_);
return v___x_1940_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg___boxed(lean_object* v_attrName_1941_, lean_object* v_declName_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_){
_start:
{
lean_object* v_res_1946_; 
v_res_1946_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg(v_attrName_1941_, v_declName_1942_, v___y_1943_, v___y_1944_);
lean_dec(v___y_1944_);
lean_dec_ref(v___y_1943_);
return v_res_1946_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___redArg(lean_object* v_attrName_1947_, lean_object* v_declName_1948_, lean_object* v_asyncPrefix_x3f_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_){
_start:
{
lean_object* v___y_1954_; 
if (lean_obj_tag(v_asyncPrefix_x3f_1949_) == 0)
{
lean_object* v___x_1967_; 
v___x_1967_ = l_Lean_MessageData_nil;
v___y_1954_ = v___x_1967_;
goto v___jp_1953_;
}
else
{
lean_object* v_val_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; lean_object* v___x_1972_; lean_object* v___x_1973_; 
v_val_1968_ = lean_ctor_get(v_asyncPrefix_x3f_1949_, 0);
lean_inc(v_val_1968_);
lean_dec_ref(v_asyncPrefix_x3f_1949_);
v___x_1969_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___redArg___closed__3, &l_Lean_throwAttrNotInAsyncCtx___redArg___closed__3_once, _init_l_Lean_throwAttrNotInAsyncCtx___redArg___closed__3);
v___x_1970_ = l_Lean_MessageData_ofName(v_val_1968_);
v___x_1971_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1971_, 0, v___x_1969_);
lean_ctor_set(v___x_1971_, 1, v___x_1970_);
v___x_1972_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__5, &l_Lean_throwAttrMustBeGlobal___redArg___closed__5_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__5);
v___x_1973_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1973_, 0, v___x_1971_);
lean_ctor_set(v___x_1973_, 1, v___x_1972_);
v___y_1954_ = v___x_1973_;
goto v___jp_1953_;
}
v___jp_1953_:
{
lean_object* v___x_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; uint8_t v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; 
v___x_1955_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1);
v___x_1956_ = l_Lean_MessageData_ofName(v_attrName_1947_);
v___x_1957_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1957_, 0, v___x_1955_);
lean_ctor_set(v___x_1957_, 1, v___x_1956_);
v___x_1958_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__3, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__3_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__3);
v___x_1959_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1959_, 0, v___x_1957_);
lean_ctor_set(v___x_1959_, 1, v___x_1958_);
v___x_1960_ = 0;
v___x_1961_ = l_Lean_MessageData_ofConstName(v_declName_1948_, v___x_1960_);
v___x_1962_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1962_, 0, v___x_1959_);
lean_ctor_set(v___x_1962_, 1, v___x_1961_);
v___x_1963_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___redArg___closed__1, &l_Lean_throwAttrNotInAsyncCtx___redArg___closed__1_once, _init_l_Lean_throwAttrNotInAsyncCtx___redArg___closed__1);
v___x_1964_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1964_, 0, v___x_1962_);
lean_ctor_set(v___x_1964_, 1, v___x_1963_);
v___x_1965_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1965_, 0, v___x_1964_);
lean_ctor_set(v___x_1965_, 1, v___y_1954_);
v___x_1966_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0_spec__0___redArg(v___x_1965_, v___y_1950_, v___y_1951_);
return v___x_1966_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___redArg___boxed(lean_object* v_attrName_1974_, lean_object* v_declName_1975_, lean_object* v_asyncPrefix_x3f_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_){
_start:
{
lean_object* v_res_1980_; 
v_res_1980_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___redArg(v_attrName_1974_, v_declName_1975_, v_asyncPrefix_x3f_1976_, v___y_1977_, v___y_1978_);
lean_dec(v___y_1978_);
lean_dec_ref(v___y_1977_);
return v_res_1980_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg(lean_object* v_name_1981_, uint8_t v_kind_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_){
_start:
{
lean_object* v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___y_1992_; 
v___x_1986_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__1, &l_Lean_throwAttrMustBeGlobal___redArg___closed__1_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__1);
v___x_1987_ = l_Lean_MessageData_ofName(v_name_1981_);
v___x_1988_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1988_, 0, v___x_1986_);
lean_ctor_set(v___x_1988_, 1, v___x_1987_);
v___x_1989_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__3, &l_Lean_throwAttrMustBeGlobal___redArg___closed__3_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__3);
v___x_1990_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1990_, 0, v___x_1988_);
lean_ctor_set(v___x_1990_, 1, v___x_1989_);
switch(v_kind_1982_)
{
case 0:
{
lean_object* v___x_1999_; 
v___x_1999_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__0));
v___y_1992_ = v___x_1999_;
goto v___jp_1991_;
}
case 1:
{
lean_object* v___x_2000_; 
v___x_2000_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__1));
v___y_1992_ = v___x_2000_;
goto v___jp_1991_;
}
default: 
{
lean_object* v___x_2001_; 
v___x_2001_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__2));
v___y_1992_ = v___x_2001_;
goto v___jp_1991_;
}
}
v___jp_1991_:
{
lean_object* v___x_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; 
lean_inc_ref(v___y_1992_);
v___x_1993_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1993_, 0, v___y_1992_);
v___x_1994_ = l_Lean_MessageData_ofFormat(v___x_1993_);
v___x_1995_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1995_, 0, v___x_1990_);
lean_ctor_set(v___x_1995_, 1, v___x_1994_);
v___x_1996_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__5, &l_Lean_throwAttrMustBeGlobal___redArg___closed__5_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__5);
v___x_1997_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1997_, 0, v___x_1995_);
lean_ctor_set(v___x_1997_, 1, v___x_1996_);
v___x_1998_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0_spec__0___redArg(v___x_1997_, v___y_1983_, v___y_1984_);
return v___x_1998_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg___boxed(lean_object* v_name_2002_, lean_object* v_kind_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_){
_start:
{
uint8_t v_kind_boxed_2007_; lean_object* v_res_2008_; 
v_kind_boxed_2007_ = lean_unbox(v_kind_2003_);
v_res_2008_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg(v_name_2002_, v_kind_boxed_2007_, v___y_2004_, v___y_2005_);
lean_dec(v___y_2005_);
lean_dec_ref(v___y_2004_);
return v_res_2008_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__7(lean_object* v_validate_2009_, lean_object* v_a_2010_, lean_object* v_name_2011_, lean_object* v_decl_2012_, lean_object* v_stx_2013_, uint8_t v_kind_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_){
_start:
{
lean_object* v___y_2019_; lean_object* v___y_2020_; lean_object* v___y_2054_; lean_object* v___y_2055_; lean_object* v___y_2056_; lean_object* v___y_2063_; lean_object* v___y_2064_; lean_object* v___x_2069_; 
v___x_2069_ = l_Lean_Attribute_Builtin_ensureNoArgs(v_stx_2013_, v___y_2015_, v___y_2016_);
if (lean_obj_tag(v___x_2069_) == 0)
{
uint8_t v___x_2070_; uint8_t v___x_2071_; 
lean_dec_ref(v___x_2069_);
v___x_2070_ = 0;
v___x_2071_ = l_Lean_instBEqAttributeKind_beq(v_kind_2014_, v___x_2070_);
if (v___x_2071_ == 0)
{
lean_object* v___x_2072_; 
lean_dec(v_decl_2012_);
lean_dec_ref(v_a_2010_);
lean_dec_ref(v_validate_2009_);
v___x_2072_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg(v_name_2011_, v_kind_2014_, v___y_2015_, v___y_2016_);
return v___x_2072_;
}
else
{
v___y_2063_ = v___y_2015_;
v___y_2064_ = v___y_2016_;
goto v___jp_2062_;
}
}
else
{
lean_dec(v_decl_2012_);
lean_dec(v_name_2011_);
lean_dec_ref(v_a_2010_);
lean_dec_ref(v_validate_2009_);
return v___x_2069_;
}
v___jp_2018_:
{
lean_object* v___x_2021_; 
lean_inc(v___y_2020_);
lean_inc_ref(v___y_2019_);
lean_inc(v_decl_2012_);
v___x_2021_ = lean_apply_4(v_validate_2009_, v_decl_2012_, v___y_2019_, v___y_2020_, lean_box(0));
if (lean_obj_tag(v___x_2021_) == 0)
{
lean_object* v___x_2023_; uint8_t v_isShared_2024_; uint8_t v_isSharedCheck_2051_; 
v_isSharedCheck_2051_ = !lean_is_exclusive(v___x_2021_);
if (v_isSharedCheck_2051_ == 0)
{
lean_object* v_unused_2052_; 
v_unused_2052_ = lean_ctor_get(v___x_2021_, 0);
lean_dec(v_unused_2052_);
v___x_2023_ = v___x_2021_;
v_isShared_2024_ = v_isSharedCheck_2051_;
goto v_resetjp_2022_;
}
else
{
lean_dec(v___x_2021_);
v___x_2023_ = lean_box(0);
v_isShared_2024_ = v_isSharedCheck_2051_;
goto v_resetjp_2022_;
}
v_resetjp_2022_:
{
lean_object* v___x_2025_; lean_object* v_toEnvExtension_2026_; lean_object* v_env_2027_; lean_object* v_nextMacroScope_2028_; lean_object* v_ngen_2029_; lean_object* v_auxDeclNGen_2030_; lean_object* v_traceState_2031_; lean_object* v_messages_2032_; lean_object* v_infoState_2033_; lean_object* v_snapshotTasks_2034_; lean_object* v___x_2036_; uint8_t v_isShared_2037_; uint8_t v_isSharedCheck_2049_; 
v___x_2025_ = lean_st_ref_take(v___y_2020_);
v_toEnvExtension_2026_ = lean_ctor_get(v_a_2010_, 0);
v_env_2027_ = lean_ctor_get(v___x_2025_, 0);
v_nextMacroScope_2028_ = lean_ctor_get(v___x_2025_, 1);
v_ngen_2029_ = lean_ctor_get(v___x_2025_, 2);
v_auxDeclNGen_2030_ = lean_ctor_get(v___x_2025_, 3);
v_traceState_2031_ = lean_ctor_get(v___x_2025_, 4);
v_messages_2032_ = lean_ctor_get(v___x_2025_, 6);
v_infoState_2033_ = lean_ctor_get(v___x_2025_, 7);
v_snapshotTasks_2034_ = lean_ctor_get(v___x_2025_, 8);
v_isSharedCheck_2049_ = !lean_is_exclusive(v___x_2025_);
if (v_isSharedCheck_2049_ == 0)
{
lean_object* v_unused_2050_; 
v_unused_2050_ = lean_ctor_get(v___x_2025_, 5);
lean_dec(v_unused_2050_);
v___x_2036_ = v___x_2025_;
v_isShared_2037_ = v_isSharedCheck_2049_;
goto v_resetjp_2035_;
}
else
{
lean_inc(v_snapshotTasks_2034_);
lean_inc(v_infoState_2033_);
lean_inc(v_messages_2032_);
lean_inc(v_traceState_2031_);
lean_inc(v_auxDeclNGen_2030_);
lean_inc(v_ngen_2029_);
lean_inc(v_nextMacroScope_2028_);
lean_inc(v_env_2027_);
lean_dec(v___x_2025_);
v___x_2036_ = lean_box(0);
v_isShared_2037_ = v_isSharedCheck_2049_;
goto v_resetjp_2035_;
}
v_resetjp_2035_:
{
lean_object* v_asyncMode_2038_; lean_object* v___x_2039_; lean_object* v___x_2040_; lean_object* v___x_2042_; 
v_asyncMode_2038_ = lean_ctor_get(v_toEnvExtension_2026_, 2);
lean_inc(v_asyncMode_2038_);
lean_inc(v_decl_2012_);
v___x_2039_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_a_2010_, v_env_2027_, v_decl_2012_, v_asyncMode_2038_, v_decl_2012_);
lean_dec(v_asyncMode_2038_);
v___x_2040_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2);
if (v_isShared_2037_ == 0)
{
lean_ctor_set(v___x_2036_, 5, v___x_2040_);
lean_ctor_set(v___x_2036_, 0, v___x_2039_);
v___x_2042_ = v___x_2036_;
goto v_reusejp_2041_;
}
else
{
lean_object* v_reuseFailAlloc_2048_; 
v_reuseFailAlloc_2048_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2048_, 0, v___x_2039_);
lean_ctor_set(v_reuseFailAlloc_2048_, 1, v_nextMacroScope_2028_);
lean_ctor_set(v_reuseFailAlloc_2048_, 2, v_ngen_2029_);
lean_ctor_set(v_reuseFailAlloc_2048_, 3, v_auxDeclNGen_2030_);
lean_ctor_set(v_reuseFailAlloc_2048_, 4, v_traceState_2031_);
lean_ctor_set(v_reuseFailAlloc_2048_, 5, v___x_2040_);
lean_ctor_set(v_reuseFailAlloc_2048_, 6, v_messages_2032_);
lean_ctor_set(v_reuseFailAlloc_2048_, 7, v_infoState_2033_);
lean_ctor_set(v_reuseFailAlloc_2048_, 8, v_snapshotTasks_2034_);
v___x_2042_ = v_reuseFailAlloc_2048_;
goto v_reusejp_2041_;
}
v_reusejp_2041_:
{
lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2046_; 
v___x_2043_ = lean_st_ref_set(v___y_2020_, v___x_2042_);
v___x_2044_ = lean_box(0);
if (v_isShared_2024_ == 0)
{
lean_ctor_set(v___x_2023_, 0, v___x_2044_);
v___x_2046_ = v___x_2023_;
goto v_reusejp_2045_;
}
else
{
lean_object* v_reuseFailAlloc_2047_; 
v_reuseFailAlloc_2047_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2047_, 0, v___x_2044_);
v___x_2046_ = v_reuseFailAlloc_2047_;
goto v_reusejp_2045_;
}
v_reusejp_2045_:
{
return v___x_2046_;
}
}
}
}
}
else
{
lean_dec(v_decl_2012_);
lean_dec_ref(v_a_2010_);
return v___x_2021_;
}
}
v___jp_2053_:
{
lean_object* v_toEnvExtension_2057_; lean_object* v_asyncMode_2058_; uint8_t v___x_2059_; 
v_toEnvExtension_2057_ = lean_ctor_get(v_a_2010_, 0);
v_asyncMode_2058_ = lean_ctor_get(v_toEnvExtension_2057_, 2);
lean_inc(v_decl_2012_);
lean_inc_ref(v___y_2054_);
v___x_2059_ = l_Lean_EnvExtension_asyncMayModify___redArg(v___y_2054_, v_decl_2012_, v_asyncMode_2058_);
if (v___x_2059_ == 0)
{
lean_object* v___x_2060_; lean_object* v___x_2061_; 
lean_dec_ref(v_a_2010_);
lean_dec_ref(v_validate_2009_);
v___x_2060_ = l_Lean_Environment_asyncPrefix_x3f(v___y_2054_);
v___x_2061_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___redArg(v_name_2011_, v_decl_2012_, v___x_2060_, v___y_2055_, v___y_2056_);
return v___x_2061_;
}
else
{
lean_dec_ref(v___y_2054_);
lean_dec(v_name_2011_);
v___y_2019_ = v___y_2055_;
v___y_2020_ = v___y_2056_;
goto v___jp_2018_;
}
}
v___jp_2062_:
{
lean_object* v___x_2065_; lean_object* v_env_2066_; lean_object* v___x_2067_; 
v___x_2065_ = lean_st_ref_get(v___y_2064_);
v_env_2066_ = lean_ctor_get(v___x_2065_, 0);
lean_inc_ref(v_env_2066_);
lean_dec(v___x_2065_);
v___x_2067_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2066_, v_decl_2012_);
if (lean_obj_tag(v___x_2067_) == 0)
{
v___y_2054_ = v_env_2066_;
v___y_2055_ = v___y_2063_;
v___y_2056_ = v___y_2064_;
goto v___jp_2053_;
}
else
{
lean_object* v___x_2068_; 
lean_dec_ref(v___x_2067_);
lean_dec_ref(v_env_2066_);
lean_dec_ref(v_a_2010_);
lean_dec_ref(v_validate_2009_);
v___x_2068_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg(v_name_2011_, v_decl_2012_, v___y_2063_, v___y_2064_);
return v___x_2068_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__7___boxed(lean_object* v_validate_2073_, lean_object* v_a_2074_, lean_object* v_name_2075_, lean_object* v_decl_2076_, lean_object* v_stx_2077_, lean_object* v_kind_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_){
_start:
{
uint8_t v_kind_boxed_2082_; lean_object* v_res_2083_; 
v_kind_boxed_2082_ = lean_unbox(v_kind_2078_);
v_res_2083_ = l_Lean_registerTagAttribute___lam__7(v_validate_2073_, v_a_2074_, v_name_2075_, v_decl_2076_, v_stx_2077_, v_kind_boxed_2082_, v___y_2079_, v___y_2080_);
lean_dec(v___y_2080_);
lean_dec_ref(v___y_2079_);
return v_res_2083_;
}
}
static lean_object* _init_l_Lean_registerTagAttribute___closed__5(void){
_start:
{
lean_object* v___x_2089_; lean_object* v___f_2090_; 
v___x_2089_ = l_Lean_NameSet_empty;
v___f_2090_ = lean_alloc_closure((void*)(l_Lean_registerTagAttribute___lam__4___boxed), 4, 1);
lean_closure_set(v___f_2090_, 0, v___x_2089_);
return v___f_2090_;
}
}
static lean_object* _init_l_Lean_registerTagAttribute___closed__6(void){
_start:
{
lean_object* v___x_2091_; lean_object* v___f_2092_; 
v___x_2091_ = l_Lean_NameSet_empty;
v___f_2092_ = lean_alloc_closure((void*)(l_Lean_registerTagAttribute___lam__5___boxed), 2, 1);
lean_closure_set(v___f_2092_, 0, v___x_2091_);
return v___f_2092_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute(lean_object* v_name_2095_, lean_object* v_descr_2096_, lean_object* v_validate_2097_, lean_object* v_ref_2098_, uint8_t v_applicationTime_2099_, lean_object* v_asyncMode_2100_){
_start:
{
lean_object* v___f_2102_; lean_object* v___f_2103_; lean_object* v___f_2104_; lean_object* v___f_2105_; lean_object* v___f_2106_; lean_object* v___f_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; 
v___f_2102_ = ((lean_object*)(l_Lean_registerTagAttribute___closed__0));
v___f_2103_ = ((lean_object*)(l_Lean_registerTagAttribute___closed__2));
v___f_2104_ = ((lean_object*)(l_Lean_registerTagAttribute___closed__3));
v___f_2105_ = ((lean_object*)(l_Lean_registerTagAttribute___closed__4));
v___f_2106_ = lean_obj_once(&l_Lean_registerTagAttribute___closed__5, &l_Lean_registerTagAttribute___closed__5_once, _init_l_Lean_registerTagAttribute___closed__5);
v___f_2107_ = lean_obj_once(&l_Lean_registerTagAttribute___closed__6, &l_Lean_registerTagAttribute___closed__6_once, _init_l_Lean_registerTagAttribute___closed__6);
v___x_2108_ = ((lean_object*)(l_Lean_registerTagAttribute___closed__7));
lean_inc(v_ref_2098_);
v___x_2109_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_2109_, 0, v_ref_2098_);
lean_ctor_set(v___x_2109_, 1, v___f_2107_);
lean_ctor_set(v___x_2109_, 2, v___f_2106_);
lean_ctor_set(v___x_2109_, 3, v___f_2105_);
lean_ctor_set(v___x_2109_, 4, v___f_2104_);
lean_ctor_set(v___x_2109_, 5, v___f_2103_);
lean_ctor_set(v___x_2109_, 6, v_asyncMode_2100_);
lean_ctor_set(v___x_2109_, 7, v___x_2108_);
v___x_2110_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2110_, 0, v___x_2109_);
lean_ctor_set(v___x_2110_, 1, v___f_2102_);
v___x_2111_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_2110_);
if (lean_obj_tag(v___x_2111_) == 0)
{
lean_object* v_a_2112_; lean_object* v___f_2113_; lean_object* v___f_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; 
v_a_2112_ = lean_ctor_get(v___x_2111_, 0);
lean_inc_n(v_a_2112_, 2);
lean_dec_ref(v___x_2111_);
lean_inc_n(v_name_2095_, 2);
v___f_2113_ = lean_alloc_closure((void*)(l_Lean_registerTagAttribute___lam__6___boxed), 5, 1);
lean_closure_set(v___f_2113_, 0, v_name_2095_);
v___f_2114_ = lean_alloc_closure((void*)(l_Lean_registerTagAttribute___lam__7___boxed), 9, 3);
lean_closure_set(v___f_2114_, 0, v_validate_2097_);
lean_closure_set(v___f_2114_, 1, v_a_2112_);
lean_closure_set(v___f_2114_, 2, v_name_2095_);
v___x_2115_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2115_, 0, v_ref_2098_);
lean_ctor_set(v___x_2115_, 1, v_name_2095_);
lean_ctor_set(v___x_2115_, 2, v_descr_2096_);
lean_ctor_set_uint8(v___x_2115_, sizeof(void*)*3, v_applicationTime_2099_);
v___x_2116_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2116_, 0, v___x_2115_);
lean_ctor_set(v___x_2116_, 1, v___f_2114_);
lean_ctor_set(v___x_2116_, 2, v___f_2113_);
lean_inc_ref(v___x_2116_);
v___x_2117_ = l_Lean_registerBuiltinAttribute(v___x_2116_);
if (lean_obj_tag(v___x_2117_) == 0)
{
lean_object* v___x_2119_; uint8_t v_isShared_2120_; uint8_t v_isSharedCheck_2125_; 
v_isSharedCheck_2125_ = !lean_is_exclusive(v___x_2117_);
if (v_isSharedCheck_2125_ == 0)
{
lean_object* v_unused_2126_; 
v_unused_2126_ = lean_ctor_get(v___x_2117_, 0);
lean_dec(v_unused_2126_);
v___x_2119_ = v___x_2117_;
v_isShared_2120_ = v_isSharedCheck_2125_;
goto v_resetjp_2118_;
}
else
{
lean_dec(v___x_2117_);
v___x_2119_ = lean_box(0);
v_isShared_2120_ = v_isSharedCheck_2125_;
goto v_resetjp_2118_;
}
v_resetjp_2118_:
{
lean_object* v___x_2121_; lean_object* v___x_2123_; 
v___x_2121_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2121_, 0, v___x_2116_);
lean_ctor_set(v___x_2121_, 1, v_a_2112_);
if (v_isShared_2120_ == 0)
{
lean_ctor_set(v___x_2119_, 0, v___x_2121_);
v___x_2123_ = v___x_2119_;
goto v_reusejp_2122_;
}
else
{
lean_object* v_reuseFailAlloc_2124_; 
v_reuseFailAlloc_2124_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2124_, 0, v___x_2121_);
v___x_2123_ = v_reuseFailAlloc_2124_;
goto v_reusejp_2122_;
}
v_reusejp_2122_:
{
return v___x_2123_;
}
}
}
else
{
lean_object* v_a_2127_; lean_object* v___x_2129_; uint8_t v_isShared_2130_; uint8_t v_isSharedCheck_2134_; 
lean_dec_ref(v___x_2116_);
lean_dec(v_a_2112_);
v_a_2127_ = lean_ctor_get(v___x_2117_, 0);
v_isSharedCheck_2134_ = !lean_is_exclusive(v___x_2117_);
if (v_isSharedCheck_2134_ == 0)
{
v___x_2129_ = v___x_2117_;
v_isShared_2130_ = v_isSharedCheck_2134_;
goto v_resetjp_2128_;
}
else
{
lean_inc(v_a_2127_);
lean_dec(v___x_2117_);
v___x_2129_ = lean_box(0);
v_isShared_2130_ = v_isSharedCheck_2134_;
goto v_resetjp_2128_;
}
v_resetjp_2128_:
{
lean_object* v___x_2132_; 
if (v_isShared_2130_ == 0)
{
v___x_2132_ = v___x_2129_;
goto v_reusejp_2131_;
}
else
{
lean_object* v_reuseFailAlloc_2133_; 
v_reuseFailAlloc_2133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2133_, 0, v_a_2127_);
v___x_2132_ = v_reuseFailAlloc_2133_;
goto v_reusejp_2131_;
}
v_reusejp_2131_:
{
return v___x_2132_;
}
}
}
}
else
{
lean_object* v_a_2135_; lean_object* v___x_2137_; uint8_t v_isShared_2138_; uint8_t v_isSharedCheck_2142_; 
lean_dec(v_ref_2098_);
lean_dec_ref(v_validate_2097_);
lean_dec_ref(v_descr_2096_);
lean_dec(v_name_2095_);
v_a_2135_ = lean_ctor_get(v___x_2111_, 0);
v_isSharedCheck_2142_ = !lean_is_exclusive(v___x_2111_);
if (v_isSharedCheck_2142_ == 0)
{
v___x_2137_ = v___x_2111_;
v_isShared_2138_ = v_isSharedCheck_2142_;
goto v_resetjp_2136_;
}
else
{
lean_inc(v_a_2135_);
lean_dec(v___x_2111_);
v___x_2137_ = lean_box(0);
v_isShared_2138_ = v_isSharedCheck_2142_;
goto v_resetjp_2136_;
}
v_resetjp_2136_:
{
lean_object* v___x_2140_; 
if (v_isShared_2138_ == 0)
{
v___x_2140_ = v___x_2137_;
goto v_reusejp_2139_;
}
else
{
lean_object* v_reuseFailAlloc_2141_; 
v_reuseFailAlloc_2141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2141_, 0, v_a_2135_);
v___x_2140_ = v_reuseFailAlloc_2141_;
goto v_reusejp_2139_;
}
v_reusejp_2139_:
{
return v___x_2140_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___boxed(lean_object* v_name_2143_, lean_object* v_descr_2144_, lean_object* v_validate_2145_, lean_object* v_ref_2146_, lean_object* v_applicationTime_2147_, lean_object* v_asyncMode_2148_, lean_object* v_a_2149_){
_start:
{
uint8_t v_applicationTime_boxed_2150_; lean_object* v_res_2151_; 
v_applicationTime_boxed_2150_ = lean_unbox(v_applicationTime_2147_);
v_res_2151_ = l_Lean_registerTagAttribute(v_name_2143_, v_descr_2144_, v_validate_2145_, v_ref_2146_, v_applicationTime_boxed_2150_, v_asyncMode_2148_);
return v_res_2151_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerTagAttribute_spec__1(lean_object* v_init_2152_, lean_object* v_t_2153_){
_start:
{
lean_object* v___x_2154_; 
v___x_2154_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerTagAttribute_spec__1_spec__1(v_init_2152_, v_t_2153_);
return v___x_2154_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3(lean_object* v_n_2155_, lean_object* v_as_2156_, lean_object* v_lo_2157_, lean_object* v_hi_2158_, lean_object* v_w_2159_, lean_object* v_hlo_2160_, lean_object* v_hhi_2161_){
_start:
{
lean_object* v___x_2162_; 
v___x_2162_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___redArg(v_n_2155_, v_as_2156_, v_lo_2157_, v_hi_2158_);
return v___x_2162_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___boxed(lean_object* v_n_2163_, lean_object* v_as_2164_, lean_object* v_lo_2165_, lean_object* v_hi_2166_, lean_object* v_w_2167_, lean_object* v_hlo_2168_, lean_object* v_hhi_2169_){
_start:
{
lean_object* v_res_2170_; 
v_res_2170_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3(v_n_2163_, v_as_2164_, v_lo_2165_, v_hi_2166_, v_w_2167_, v_hlo_2168_, v_hhi_2169_);
lean_dec(v_hi_2166_);
lean_dec(v_n_2163_);
return v_res_2170_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4(lean_object* v_00_u03b1_2171_, lean_object* v_attrName_2172_, lean_object* v_declName_2173_, lean_object* v_asyncPrefix_x3f_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_){
_start:
{
lean_object* v___x_2178_; 
v___x_2178_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___redArg(v_attrName_2172_, v_declName_2173_, v_asyncPrefix_x3f_2174_, v___y_2175_, v___y_2176_);
return v___x_2178_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___boxed(lean_object* v_00_u03b1_2179_, lean_object* v_attrName_2180_, lean_object* v_declName_2181_, lean_object* v_asyncPrefix_x3f_2182_, lean_object* v___y_2183_, lean_object* v___y_2184_, lean_object* v___y_2185_){
_start:
{
lean_object* v_res_2186_; 
v_res_2186_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4(v_00_u03b1_2179_, v_attrName_2180_, v_declName_2181_, v_asyncPrefix_x3f_2182_, v___y_2183_, v___y_2184_);
lean_dec(v___y_2184_);
lean_dec_ref(v___y_2183_);
return v_res_2186_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5(lean_object* v_00_u03b1_2187_, lean_object* v_attrName_2188_, lean_object* v_declName_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_){
_start:
{
lean_object* v___x_2193_; 
v___x_2193_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg(v_attrName_2188_, v_declName_2189_, v___y_2190_, v___y_2191_);
return v___x_2193_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___boxed(lean_object* v_00_u03b1_2194_, lean_object* v_attrName_2195_, lean_object* v_declName_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_){
_start:
{
lean_object* v_res_2200_; 
v_res_2200_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5(v_00_u03b1_2194_, v_attrName_2195_, v_declName_2196_, v___y_2197_, v___y_2198_);
lean_dec(v___y_2198_);
lean_dec_ref(v___y_2197_);
return v_res_2200_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6(lean_object* v_00_u03b1_2201_, lean_object* v_name_2202_, uint8_t v_kind_2203_, lean_object* v___y_2204_, lean_object* v___y_2205_){
_start:
{
lean_object* v___x_2207_; 
v___x_2207_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg(v_name_2202_, v_kind_2203_, v___y_2204_, v___y_2205_);
return v___x_2207_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___boxed(lean_object* v_00_u03b1_2208_, lean_object* v_name_2209_, lean_object* v_kind_2210_, lean_object* v___y_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_){
_start:
{
uint8_t v_kind_boxed_2214_; lean_object* v_res_2215_; 
v_kind_boxed_2214_ = lean_unbox(v_kind_2210_);
v_res_2215_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6(v_00_u03b1_2208_, v_name_2209_, v_kind_boxed_2214_, v___y_2211_, v___y_2212_);
lean_dec(v___y_2212_);
lean_dec_ref(v___y_2211_);
return v_res_2215_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4(lean_object* v_n_2216_, lean_object* v_lo_2217_, lean_object* v_hi_2218_, lean_object* v_hhi_2219_, lean_object* v_pivot_2220_, lean_object* v_as_2221_, lean_object* v_i_2222_, lean_object* v_k_2223_, lean_object* v_ilo_2224_, lean_object* v_ik_2225_, lean_object* v_w_2226_){
_start:
{
lean_object* v___x_2227_; 
v___x_2227_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4___redArg(v_hi_2218_, v_pivot_2220_, v_as_2221_, v_i_2222_, v_k_2223_);
return v___x_2227_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4___boxed(lean_object* v_n_2228_, lean_object* v_lo_2229_, lean_object* v_hi_2230_, lean_object* v_hhi_2231_, lean_object* v_pivot_2232_, lean_object* v_as_2233_, lean_object* v_i_2234_, lean_object* v_k_2235_, lean_object* v_ilo_2236_, lean_object* v_ik_2237_, lean_object* v_w_2238_){
_start:
{
lean_object* v_res_2239_; 
v_res_2239_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4(v_n_2228_, v_lo_2229_, v_hi_2230_, v_hhi_2231_, v_pivot_2232_, v_as_2233_, v_i_2234_, v_k_2235_, v_ilo_2236_, v_ik_2237_, v_w_2238_);
lean_dec(v_pivot_2232_);
lean_dec(v_hi_2230_);
lean_dec(v_lo_2229_);
lean_dec(v_n_2228_);
return v_res_2239_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg___lam__0(lean_object* v_attr_2240_, lean_object* v_decl_2241_, lean_object* v_env_2242_){
_start:
{
lean_object* v_ext_2243_; lean_object* v_toEnvExtension_2244_; lean_object* v_asyncMode_2245_; lean_object* v___x_2246_; 
v_ext_2243_ = lean_ctor_get(v_attr_2240_, 1);
lean_inc_ref(v_ext_2243_);
lean_dec_ref(v_attr_2240_);
v_toEnvExtension_2244_ = lean_ctor_get(v_ext_2243_, 0);
v_asyncMode_2245_ = lean_ctor_get(v_toEnvExtension_2244_, 2);
lean_inc(v_asyncMode_2245_);
lean_inc(v_decl_2241_);
v___x_2246_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_ext_2243_, v_env_2242_, v_decl_2241_, v_asyncMode_2245_, v_decl_2241_);
lean_dec(v_asyncMode_2245_);
return v___x_2246_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg___lam__1(lean_object* v_modifyEnv_2247_, lean_object* v___f_2248_, lean_object* v_____r_2249_){
_start:
{
lean_object* v___x_2250_; 
v___x_2250_ = lean_apply_1(v_modifyEnv_2247_, v___f_2248_);
return v___x_2250_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg___lam__2(lean_object* v_attr_2251_, lean_object* v_env_2252_, lean_object* v_decl_2253_, lean_object* v_inst_2254_, lean_object* v_inst_2255_, lean_object* v_toBind_2256_, lean_object* v___f_2257_, lean_object* v_modifyEnv_2258_, lean_object* v___f_2259_, lean_object* v_____r_2260_){
_start:
{
lean_object* v_ext_2261_; lean_object* v_toEnvExtension_2262_; lean_object* v_attr_2263_; lean_object* v_asyncMode_2264_; uint8_t v___x_2265_; 
v_ext_2261_ = lean_ctor_get(v_attr_2251_, 1);
v_toEnvExtension_2262_ = lean_ctor_get(v_ext_2261_, 0);
lean_inc_ref(v_toEnvExtension_2262_);
v_attr_2263_ = lean_ctor_get(v_attr_2251_, 0);
lean_inc_ref(v_attr_2263_);
lean_dec_ref(v_attr_2251_);
v_asyncMode_2264_ = lean_ctor_get(v_toEnvExtension_2262_, 2);
lean_inc(v_asyncMode_2264_);
lean_dec_ref(v_toEnvExtension_2262_);
lean_inc(v_decl_2253_);
lean_inc_ref(v_env_2252_);
v___x_2265_ = l_Lean_EnvExtension_asyncMayModify___redArg(v_env_2252_, v_decl_2253_, v_asyncMode_2264_);
lean_dec(v_asyncMode_2264_);
if (v___x_2265_ == 0)
{
lean_object* v_toAttributeImplCore_2266_; lean_object* v_name_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; 
lean_dec_ref(v___f_2259_);
lean_dec(v_modifyEnv_2258_);
v_toAttributeImplCore_2266_ = lean_ctor_get(v_attr_2263_, 0);
lean_inc_ref(v_toAttributeImplCore_2266_);
lean_dec_ref(v_attr_2263_);
v_name_2267_ = lean_ctor_get(v_toAttributeImplCore_2266_, 1);
lean_inc(v_name_2267_);
lean_dec_ref(v_toAttributeImplCore_2266_);
v___x_2268_ = l_Lean_Environment_asyncPrefix_x3f(v_env_2252_);
v___x_2269_ = l_Lean_throwAttrNotInAsyncCtx___redArg(v_inst_2254_, v_inst_2255_, v_name_2267_, v_decl_2253_, v___x_2268_);
v___x_2270_ = lean_apply_4(v_toBind_2256_, lean_box(0), lean_box(0), v___x_2269_, v___f_2257_);
return v___x_2270_;
}
else
{
lean_object* v___x_2271_; 
lean_dec_ref(v_attr_2263_);
lean_dec(v___f_2257_);
lean_dec(v_toBind_2256_);
lean_dec_ref(v_inst_2255_);
lean_dec_ref(v_inst_2254_);
lean_dec(v_decl_2253_);
lean_dec_ref(v_env_2252_);
v___x_2271_ = lean_apply_1(v_modifyEnv_2258_, v___f_2259_);
return v___x_2271_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg___lam__3(lean_object* v___f_2272_, lean_object* v_____r_2273_){
_start:
{
lean_object* v___x_2274_; 
v___x_2274_ = lean_apply_1(v___f_2272_, v_____r_2273_);
return v___x_2274_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg___lam__4(lean_object* v_attr_2275_, lean_object* v_decl_2276_, lean_object* v_inst_2277_, lean_object* v_inst_2278_, lean_object* v_toBind_2279_, lean_object* v___f_2280_, lean_object* v_modifyEnv_2281_, lean_object* v___f_2282_, lean_object* v_env_2283_){
_start:
{
lean_object* v___f_2284_; lean_object* v___x_2285_; 
lean_inc_ref(v___f_2282_);
lean_inc(v_modifyEnv_2281_);
lean_inc(v___f_2280_);
lean_inc(v_toBind_2279_);
lean_inc_ref(v_inst_2278_);
lean_inc_ref(v_inst_2277_);
lean_inc(v_decl_2276_);
lean_inc_ref(v_env_2283_);
lean_inc_ref(v_attr_2275_);
v___f_2284_ = lean_alloc_closure((void*)(l_Lean_TagAttribute_setTag___redArg___lam__2), 10, 9);
lean_closure_set(v___f_2284_, 0, v_attr_2275_);
lean_closure_set(v___f_2284_, 1, v_env_2283_);
lean_closure_set(v___f_2284_, 2, v_decl_2276_);
lean_closure_set(v___f_2284_, 3, v_inst_2277_);
lean_closure_set(v___f_2284_, 4, v_inst_2278_);
lean_closure_set(v___f_2284_, 5, v_toBind_2279_);
lean_closure_set(v___f_2284_, 6, v___f_2280_);
lean_closure_set(v___f_2284_, 7, v_modifyEnv_2281_);
lean_closure_set(v___f_2284_, 8, v___f_2282_);
v___x_2285_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2283_, v_decl_2276_);
if (lean_obj_tag(v___x_2285_) == 0)
{
lean_object* v___x_2286_; lean_object* v___x_2287_; 
lean_dec_ref(v___f_2284_);
v___x_2286_ = lean_box(0);
v___x_2287_ = l_Lean_TagAttribute_setTag___redArg___lam__2(v_attr_2275_, v_env_2283_, v_decl_2276_, v_inst_2277_, v_inst_2278_, v_toBind_2279_, v___f_2280_, v_modifyEnv_2281_, v___f_2282_, v___x_2286_);
return v___x_2287_;
}
else
{
lean_object* v_attr_2288_; lean_object* v_toAttributeImplCore_2289_; lean_object* v_name_2290_; lean_object* v___f_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; 
lean_dec_ref(v___x_2285_);
lean_dec_ref(v_env_2283_);
lean_dec_ref(v___f_2282_);
lean_dec(v_modifyEnv_2281_);
lean_dec(v___f_2280_);
v_attr_2288_ = lean_ctor_get(v_attr_2275_, 0);
lean_inc_ref(v_attr_2288_);
lean_dec_ref(v_attr_2275_);
v_toAttributeImplCore_2289_ = lean_ctor_get(v_attr_2288_, 0);
lean_inc_ref(v_toAttributeImplCore_2289_);
lean_dec_ref(v_attr_2288_);
v_name_2290_ = lean_ctor_get(v_toAttributeImplCore_2289_, 1);
lean_inc(v_name_2290_);
lean_dec_ref(v_toAttributeImplCore_2289_);
v___f_2291_ = lean_alloc_closure((void*)(l_Lean_TagAttribute_setTag___redArg___lam__3), 2, 1);
lean_closure_set(v___f_2291_, 0, v___f_2284_);
v___x_2292_ = l_Lean_throwAttrDeclInImportedModule___redArg(v_inst_2277_, v_inst_2278_, v_name_2290_, v_decl_2276_);
v___x_2293_ = lean_apply_4(v_toBind_2279_, lean_box(0), lean_box(0), v___x_2292_, v___f_2291_);
return v___x_2293_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg(lean_object* v_inst_2294_, lean_object* v_inst_2295_, lean_object* v_inst_2296_, lean_object* v_attr_2297_, lean_object* v_decl_2298_){
_start:
{
lean_object* v_toBind_2299_; lean_object* v_getEnv_2300_; lean_object* v_modifyEnv_2301_; lean_object* v___f_2302_; lean_object* v___f_2303_; lean_object* v___f_2304_; lean_object* v___x_2305_; 
v_toBind_2299_ = lean_ctor_get(v_inst_2294_, 1);
lean_inc_n(v_toBind_2299_, 2);
v_getEnv_2300_ = lean_ctor_get(v_inst_2296_, 0);
lean_inc(v_getEnv_2300_);
v_modifyEnv_2301_ = lean_ctor_get(v_inst_2296_, 1);
lean_inc_n(v_modifyEnv_2301_, 2);
lean_dec_ref(v_inst_2296_);
lean_inc(v_decl_2298_);
lean_inc_ref(v_attr_2297_);
v___f_2302_ = lean_alloc_closure((void*)(l_Lean_TagAttribute_setTag___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2302_, 0, v_attr_2297_);
lean_closure_set(v___f_2302_, 1, v_decl_2298_);
lean_inc_ref(v___f_2302_);
v___f_2303_ = lean_alloc_closure((void*)(l_Lean_TagAttribute_setTag___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2303_, 0, v_modifyEnv_2301_);
lean_closure_set(v___f_2303_, 1, v___f_2302_);
v___f_2304_ = lean_alloc_closure((void*)(l_Lean_TagAttribute_setTag___redArg___lam__4), 9, 8);
lean_closure_set(v___f_2304_, 0, v_attr_2297_);
lean_closure_set(v___f_2304_, 1, v_decl_2298_);
lean_closure_set(v___f_2304_, 2, v_inst_2294_);
lean_closure_set(v___f_2304_, 3, v_inst_2295_);
lean_closure_set(v___f_2304_, 4, v_toBind_2299_);
lean_closure_set(v___f_2304_, 5, v___f_2303_);
lean_closure_set(v___f_2304_, 6, v_modifyEnv_2301_);
lean_closure_set(v___f_2304_, 7, v___f_2302_);
v___x_2305_ = lean_apply_4(v_toBind_2299_, lean_box(0), lean_box(0), v_getEnv_2300_, v___f_2304_);
return v___x_2305_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag(lean_object* v_m_2306_, lean_object* v_inst_2307_, lean_object* v_inst_2308_, lean_object* v_inst_2309_, lean_object* v_attr_2310_, lean_object* v_decl_2311_){
_start:
{
lean_object* v___x_2312_; 
v___x_2312_ = l_Lean_TagAttribute_setTag___redArg(v_inst_2307_, v_inst_2308_, v_inst_2309_, v_attr_2310_, v_decl_2311_);
return v___x_2312_;
}
}
LEAN_EXPORT uint8_t l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___redArg(lean_object* v_as_2313_, lean_object* v_k_2314_, lean_object* v_x_2315_, lean_object* v_x_2316_){
_start:
{
lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v_m_2319_; lean_object* v_a_2320_; uint8_t v___x_2321_; 
v___x_2317_ = lean_nat_add(v_x_2315_, v_x_2316_);
v___x_2318_ = lean_unsigned_to_nat(1u);
v_m_2319_ = lean_nat_shiftr(v___x_2317_, v___x_2318_);
lean_dec(v___x_2317_);
v_a_2320_ = lean_array_fget_borrowed(v_as_2313_, v_m_2319_);
v___x_2321_ = l_Lean_Name_quickLt(v_a_2320_, v_k_2314_);
if (v___x_2321_ == 0)
{
uint8_t v___x_2322_; 
lean_dec(v_x_2316_);
v___x_2322_ = l_Lean_Name_quickLt(v_k_2314_, v_a_2320_);
if (v___x_2322_ == 0)
{
uint8_t v___x_2323_; 
lean_dec(v_m_2319_);
lean_dec(v_x_2315_);
v___x_2323_ = 1;
return v___x_2323_;
}
else
{
lean_object* v___x_2324_; uint8_t v___x_2325_; 
v___x_2324_ = lean_unsigned_to_nat(0u);
v___x_2325_ = lean_nat_dec_eq(v_m_2319_, v___x_2324_);
if (v___x_2325_ == 0)
{
lean_object* v___x_2326_; uint8_t v___x_2327_; 
v___x_2326_ = lean_nat_sub(v_m_2319_, v___x_2318_);
lean_dec(v_m_2319_);
v___x_2327_ = lean_nat_dec_lt(v___x_2326_, v_x_2315_);
if (v___x_2327_ == 0)
{
v_x_2316_ = v___x_2326_;
goto _start;
}
else
{
lean_dec(v___x_2326_);
lean_dec(v_x_2315_);
return v___x_2321_;
}
}
else
{
lean_dec(v_m_2319_);
lean_dec(v_x_2315_);
return v___x_2321_;
}
}
}
else
{
lean_object* v___x_2329_; uint8_t v___x_2330_; 
lean_dec(v_x_2315_);
v___x_2329_ = lean_nat_add(v_m_2319_, v___x_2318_);
lean_dec(v_m_2319_);
v___x_2330_ = lean_nat_dec_le(v___x_2329_, v_x_2316_);
if (v___x_2330_ == 0)
{
lean_dec(v___x_2329_);
lean_dec(v_x_2316_);
return v___x_2330_;
}
else
{
v_x_2315_ = v___x_2329_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___redArg___boxed(lean_object* v_as_2332_, lean_object* v_k_2333_, lean_object* v_x_2334_, lean_object* v_x_2335_){
_start:
{
uint8_t v_res_2336_; lean_object* v_r_2337_; 
v_res_2336_ = l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___redArg(v_as_2332_, v_k_2333_, v_x_2334_, v_x_2335_);
lean_dec(v_k_2333_);
lean_dec_ref(v_as_2332_);
v_r_2337_ = lean_box(v_res_2336_);
return v_r_2337_;
}
}
LEAN_EXPORT uint8_t l_Lean_TagAttribute_hasTag(lean_object* v_attr_2338_, lean_object* v_env_2339_, lean_object* v_decl_2340_){
_start:
{
lean_object* v___x_2341_; lean_object* v___x_2342_; 
v___x_2341_ = lean_box(1);
v___x_2342_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2339_, v_decl_2340_);
if (lean_obj_tag(v___x_2342_) == 0)
{
lean_object* v_ext_2343_; lean_object* v_toEnvExtension_2344_; lean_object* v_asyncMode_2345_; lean_object* v___x_2346_; uint8_t v___x_2347_; 
v_ext_2343_ = lean_ctor_get(v_attr_2338_, 1);
v_toEnvExtension_2344_ = lean_ctor_get(v_ext_2343_, 0);
v_asyncMode_2345_ = lean_ctor_get(v_toEnvExtension_2344_, 2);
lean_inc(v_decl_2340_);
v___x_2346_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2341_, v_ext_2343_, v_env_2339_, v_asyncMode_2345_, v_decl_2340_);
v___x_2347_ = l_Lean_NameSet_contains(v___x_2346_, v_decl_2340_);
lean_dec(v_decl_2340_);
lean_dec(v___x_2346_);
return v___x_2347_;
}
else
{
lean_object* v_val_2348_; lean_object* v_ext_2349_; uint8_t v___x_2350_; lean_object* v___x_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; uint8_t v___x_2354_; 
v_val_2348_ = lean_ctor_get(v___x_2342_, 0);
lean_inc(v_val_2348_);
lean_dec_ref(v___x_2342_);
v_ext_2349_ = lean_ctor_get(v_attr_2338_, 1);
v___x_2350_ = 0;
v___x_2351_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_2341_, v_ext_2349_, v_env_2339_, v_val_2348_, v___x_2350_);
lean_dec(v_val_2348_);
lean_dec_ref(v_env_2339_);
v___x_2352_ = lean_unsigned_to_nat(0u);
v___x_2353_ = lean_array_get_size(v___x_2351_);
v___x_2354_ = lean_nat_dec_lt(v___x_2352_, v___x_2353_);
if (v___x_2354_ == 0)
{
lean_dec_ref(v___x_2351_);
lean_dec(v_decl_2340_);
return v___x_2354_;
}
else
{
lean_object* v___x_2355_; lean_object* v___x_2356_; uint8_t v___x_2357_; 
v___x_2355_ = lean_unsigned_to_nat(1u);
v___x_2356_ = lean_nat_sub(v___x_2353_, v___x_2355_);
v___x_2357_ = lean_nat_dec_le(v___x_2352_, v___x_2356_);
if (v___x_2357_ == 0)
{
lean_dec(v___x_2356_);
lean_dec_ref(v___x_2351_);
lean_dec(v_decl_2340_);
return v___x_2357_;
}
else
{
uint8_t v___x_2358_; 
v___x_2358_ = l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___redArg(v___x_2351_, v_decl_2340_, v___x_2352_, v___x_2356_);
lean_dec(v_decl_2340_);
lean_dec_ref(v___x_2351_);
return v___x_2358_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_hasTag___boxed(lean_object* v_attr_2359_, lean_object* v_env_2360_, lean_object* v_decl_2361_){
_start:
{
uint8_t v_res_2362_; lean_object* v_r_2363_; 
v_res_2362_ = l_Lean_TagAttribute_hasTag(v_attr_2359_, v_env_2360_, v_decl_2361_);
lean_dec_ref(v_attr_2359_);
v_r_2363_ = lean_box(v_res_2362_);
return v_r_2363_;
}
}
LEAN_EXPORT uint8_t l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0(lean_object* v_as_2364_, lean_object* v_k_2365_, lean_object* v_x_2366_, lean_object* v_x_2367_, lean_object* v_x_2368_){
_start:
{
uint8_t v___x_2369_; 
v___x_2369_ = l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___redArg(v_as_2364_, v_k_2365_, v_x_2366_, v_x_2367_);
return v___x_2369_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___boxed(lean_object* v_as_2370_, lean_object* v_k_2371_, lean_object* v_x_2372_, lean_object* v_x_2373_, lean_object* v_x_2374_){
_start:
{
uint8_t v_res_2375_; lean_object* v_r_2376_; 
v_res_2375_ = l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0(v_as_2370_, v_k_2371_, v_x_2372_, v_x_2373_, v_x_2374_);
lean_dec(v_k_2371_);
lean_dec_ref(v_as_2370_);
v_r_2376_ = lean_box(v_res_2375_);
return v_r_2376_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__0(lean_object* v_x_2377_, lean_object* v___y_2378_){
_start:
{
lean_object* v___x_2380_; lean_object* v___x_2381_; 
v___x_2380_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___lam__0___closed__1));
v___x_2381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2381_, 0, v___x_2380_);
return v___x_2381_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__0___boxed(lean_object* v_x_2382_, lean_object* v___y_2383_, lean_object* v___y_2384_){
_start:
{
lean_object* v_res_2385_; 
v_res_2385_ = l_Lean_instInhabitedParametricAttribute_default___lam__0(v_x_2382_, v___y_2383_);
lean_dec_ref(v___y_2383_);
lean_dec_ref(v_x_2382_);
return v_res_2385_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__1(lean_object* v_s_2386_, lean_object* v_x_2387_){
_start:
{
lean_inc_ref(v_s_2386_);
return v_s_2386_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__1___boxed(lean_object* v_s_2388_, lean_object* v_x_2389_){
_start:
{
lean_object* v_res_2390_; 
v_res_2390_ = l_Lean_instInhabitedParametricAttribute_default___lam__1(v_s_2388_, v_x_2389_);
lean_dec_ref(v_x_2389_);
lean_dec_ref(v_s_2388_);
return v_res_2390_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__2(lean_object* v_x_2395_, lean_object* v_x_2396_){
_start:
{
lean_object* v___x_2397_; 
v___x_2397_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___lam__2___closed__1));
return v___x_2397_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__2___boxed(lean_object* v_x_2398_, lean_object* v_x_2399_){
_start:
{
lean_object* v_res_2400_; 
v_res_2400_ = l_Lean_instInhabitedParametricAttribute_default___lam__2(v_x_2398_, v_x_2399_);
lean_dec_ref(v_x_2399_);
lean_dec_ref(v_x_2398_);
return v_res_2400_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__3(lean_object* v_x_2401_){
_start:
{
lean_object* v___x_2402_; 
v___x_2402_ = lean_box(0);
return v___x_2402_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__3___boxed(lean_object* v_x_2403_){
_start:
{
lean_object* v_res_2404_; 
v_res_2404_ = l_Lean_instInhabitedParametricAttribute_default___lam__3(v_x_2403_);
lean_dec_ref(v_x_2403_);
return v_res_2404_;
}
}
static lean_object* _init_l_Lean_instInhabitedParametricAttribute_default___closed__4(void){
_start:
{
lean_object* v___x_2409_; 
v___x_2409_ = l_Lean_instInhabitedEnvExtension_default(lean_box(0));
return v___x_2409_;
}
}
static lean_object* _init_l_Lean_instInhabitedParametricAttribute_default___closed__5(void){
_start:
{
lean_object* v___f_2410_; lean_object* v___f_2411_; lean_object* v___f_2412_; lean_object* v___f_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; lean_object* v___x_2416_; 
v___f_2410_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___closed__3));
v___f_2411_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___closed__2));
v___f_2412_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___closed__1));
v___f_2413_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___closed__0));
v___x_2414_ = lean_box(0);
v___x_2415_ = lean_obj_once(&l_Lean_instInhabitedParametricAttribute_default___closed__4, &l_Lean_instInhabitedParametricAttribute_default___closed__4_once, _init_l_Lean_instInhabitedParametricAttribute_default___closed__4);
v___x_2416_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2416_, 0, v___x_2415_);
lean_ctor_set(v___x_2416_, 1, v___x_2414_);
lean_ctor_set(v___x_2416_, 2, v___f_2413_);
lean_ctor_set(v___x_2416_, 3, v___f_2412_);
lean_ctor_set(v___x_2416_, 4, v___f_2411_);
lean_ctor_set(v___x_2416_, 5, v___f_2410_);
return v___x_2416_;
}
}
static lean_object* _init_l_Lean_instInhabitedParametricAttribute_default___closed__6(void){
_start:
{
uint8_t v___x_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; lean_object* v___x_2420_; 
v___x_2417_ = 0;
v___x_2418_ = lean_obj_once(&l_Lean_instInhabitedParametricAttribute_default___closed__5, &l_Lean_instInhabitedParametricAttribute_default___closed__5_once, _init_l_Lean_instInhabitedParametricAttribute_default___closed__5);
v___x_2419_ = ((lean_object*)(l_Lean_instInhabitedAttributeImpl_default));
v___x_2420_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2420_, 0, v___x_2419_);
lean_ctor_set(v___x_2420_, 1, v___x_2418_);
lean_ctor_set_uint8(v___x_2420_, sizeof(void*)*2, v___x_2417_);
return v___x_2420_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default(lean_object* v_00_u03b1_2421_){
_start:
{
lean_object* v___x_2422_; 
v___x_2422_ = lean_obj_once(&l_Lean_instInhabitedParametricAttribute_default___closed__6, &l_Lean_instInhabitedParametricAttribute_default___closed__6_once, _init_l_Lean_instInhabitedParametricAttribute_default___closed__6);
return v___x_2422_;
}
}
static lean_object* _init_l_Lean_instInhabitedParametricAttribute___closed__0(void){
_start:
{
lean_object* v___x_2423_; 
v___x_2423_ = l_Lean_instInhabitedParametricAttribute_default(lean_box(0));
return v___x_2423_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute(lean_object* v_a_2424_){
_start:
{
lean_object* v___x_2425_; 
v___x_2425_ = lean_obj_once(&l_Lean_instInhabitedParametricAttribute___closed__0, &l_Lean_instInhabitedParametricAttribute___closed__0_once, _init_l_Lean_instInhabitedParametricAttribute___closed__0);
return v___x_2425_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_registerParametricAttribute_spec__4___redArg(lean_object* v_env_2426_, lean_object* v___y_2427_){
_start:
{
lean_object* v___x_2429_; lean_object* v_nextMacroScope_2430_; lean_object* v_ngen_2431_; lean_object* v_auxDeclNGen_2432_; lean_object* v_traceState_2433_; lean_object* v_messages_2434_; lean_object* v_infoState_2435_; lean_object* v_snapshotTasks_2436_; lean_object* v___x_2438_; uint8_t v_isShared_2439_; uint8_t v_isSharedCheck_2447_; 
v___x_2429_ = lean_st_ref_take(v___y_2427_);
v_nextMacroScope_2430_ = lean_ctor_get(v___x_2429_, 1);
v_ngen_2431_ = lean_ctor_get(v___x_2429_, 2);
v_auxDeclNGen_2432_ = lean_ctor_get(v___x_2429_, 3);
v_traceState_2433_ = lean_ctor_get(v___x_2429_, 4);
v_messages_2434_ = lean_ctor_get(v___x_2429_, 6);
v_infoState_2435_ = lean_ctor_get(v___x_2429_, 7);
v_snapshotTasks_2436_ = lean_ctor_get(v___x_2429_, 8);
v_isSharedCheck_2447_ = !lean_is_exclusive(v___x_2429_);
if (v_isSharedCheck_2447_ == 0)
{
lean_object* v_unused_2448_; lean_object* v_unused_2449_; 
v_unused_2448_ = lean_ctor_get(v___x_2429_, 5);
lean_dec(v_unused_2448_);
v_unused_2449_ = lean_ctor_get(v___x_2429_, 0);
lean_dec(v_unused_2449_);
v___x_2438_ = v___x_2429_;
v_isShared_2439_ = v_isSharedCheck_2447_;
goto v_resetjp_2437_;
}
else
{
lean_inc(v_snapshotTasks_2436_);
lean_inc(v_infoState_2435_);
lean_inc(v_messages_2434_);
lean_inc(v_traceState_2433_);
lean_inc(v_auxDeclNGen_2432_);
lean_inc(v_ngen_2431_);
lean_inc(v_nextMacroScope_2430_);
lean_dec(v___x_2429_);
v___x_2438_ = lean_box(0);
v_isShared_2439_ = v_isSharedCheck_2447_;
goto v_resetjp_2437_;
}
v_resetjp_2437_:
{
lean_object* v___x_2440_; lean_object* v___x_2442_; 
v___x_2440_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2);
if (v_isShared_2439_ == 0)
{
lean_ctor_set(v___x_2438_, 5, v___x_2440_);
lean_ctor_set(v___x_2438_, 0, v_env_2426_);
v___x_2442_ = v___x_2438_;
goto v_reusejp_2441_;
}
else
{
lean_object* v_reuseFailAlloc_2446_; 
v_reuseFailAlloc_2446_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2446_, 0, v_env_2426_);
lean_ctor_set(v_reuseFailAlloc_2446_, 1, v_nextMacroScope_2430_);
lean_ctor_set(v_reuseFailAlloc_2446_, 2, v_ngen_2431_);
lean_ctor_set(v_reuseFailAlloc_2446_, 3, v_auxDeclNGen_2432_);
lean_ctor_set(v_reuseFailAlloc_2446_, 4, v_traceState_2433_);
lean_ctor_set(v_reuseFailAlloc_2446_, 5, v___x_2440_);
lean_ctor_set(v_reuseFailAlloc_2446_, 6, v_messages_2434_);
lean_ctor_set(v_reuseFailAlloc_2446_, 7, v_infoState_2435_);
lean_ctor_set(v_reuseFailAlloc_2446_, 8, v_snapshotTasks_2436_);
v___x_2442_ = v_reuseFailAlloc_2446_;
goto v_reusejp_2441_;
}
v_reusejp_2441_:
{
lean_object* v___x_2443_; lean_object* v___x_2444_; lean_object* v___x_2445_; 
v___x_2443_ = lean_st_ref_set(v___y_2427_, v___x_2442_);
v___x_2444_ = lean_box(0);
v___x_2445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2445_, 0, v___x_2444_);
return v___x_2445_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_registerParametricAttribute_spec__4___redArg___boxed(lean_object* v_env_2450_, lean_object* v___y_2451_, lean_object* v___y_2452_){
_start:
{
lean_object* v_res_2453_; 
v_res_2453_ = l_Lean_setEnv___at___00Lean_registerParametricAttribute_spec__4___redArg(v_env_2450_, v___y_2451_);
lean_dec(v___y_2451_);
return v_res_2453_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_registerParametricAttribute_spec__4(lean_object* v_env_2454_, lean_object* v___y_2455_, lean_object* v___y_2456_){
_start:
{
lean_object* v___x_2458_; 
v___x_2458_ = l_Lean_setEnv___at___00Lean_registerParametricAttribute_spec__4___redArg(v_env_2454_, v___y_2456_);
return v___x_2458_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_registerParametricAttribute_spec__4___boxed(lean_object* v_env_2459_, lean_object* v___y_2460_, lean_object* v___y_2461_, lean_object* v___y_2462_){
_start:
{
lean_object* v_res_2463_; 
v_res_2463_ = l_Lean_setEnv___at___00Lean_registerParametricAttribute_spec__4(v_env_2459_, v___y_2460_, v___y_2461_);
lean_dec(v___y_2461_);
lean_dec_ref(v___y_2460_);
return v_res_2463_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___lam__0(lean_object* v_x_2464_, lean_object* v_p_2465_){
_start:
{
lean_object* v_fst_2466_; lean_object* v_snd_2467_; lean_object* v___x_2469_; uint8_t v_isShared_2470_; uint8_t v_isSharedCheck_2484_; 
v_fst_2466_ = lean_ctor_get(v_x_2464_, 0);
v_snd_2467_ = lean_ctor_get(v_x_2464_, 1);
v_isSharedCheck_2484_ = !lean_is_exclusive(v_x_2464_);
if (v_isSharedCheck_2484_ == 0)
{
v___x_2469_ = v_x_2464_;
v_isShared_2470_ = v_isSharedCheck_2484_;
goto v_resetjp_2468_;
}
else
{
lean_inc(v_snd_2467_);
lean_inc(v_fst_2466_);
lean_dec(v_x_2464_);
v___x_2469_ = lean_box(0);
v_isShared_2470_ = v_isSharedCheck_2484_;
goto v_resetjp_2468_;
}
v_resetjp_2468_:
{
lean_object* v_fst_2471_; lean_object* v_snd_2472_; lean_object* v___x_2474_; uint8_t v_isShared_2475_; uint8_t v_isSharedCheck_2483_; 
v_fst_2471_ = lean_ctor_get(v_p_2465_, 0);
v_snd_2472_ = lean_ctor_get(v_p_2465_, 1);
v_isSharedCheck_2483_ = !lean_is_exclusive(v_p_2465_);
if (v_isSharedCheck_2483_ == 0)
{
v___x_2474_ = v_p_2465_;
v_isShared_2475_ = v_isSharedCheck_2483_;
goto v_resetjp_2473_;
}
else
{
lean_inc(v_snd_2472_);
lean_inc(v_fst_2471_);
lean_dec(v_p_2465_);
v___x_2474_ = lean_box(0);
v_isShared_2475_ = v_isSharedCheck_2483_;
goto v_resetjp_2473_;
}
v_resetjp_2473_:
{
lean_object* v___x_2477_; 
lean_inc(v_fst_2471_);
if (v_isShared_2470_ == 0)
{
lean_ctor_set_tag(v___x_2469_, 1);
lean_ctor_set(v___x_2469_, 1, v_fst_2466_);
lean_ctor_set(v___x_2469_, 0, v_fst_2471_);
v___x_2477_ = v___x_2469_;
goto v_reusejp_2476_;
}
else
{
lean_object* v_reuseFailAlloc_2482_; 
v_reuseFailAlloc_2482_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2482_, 0, v_fst_2471_);
lean_ctor_set(v_reuseFailAlloc_2482_, 1, v_fst_2466_);
v___x_2477_ = v_reuseFailAlloc_2482_;
goto v_reusejp_2476_;
}
v_reusejp_2476_:
{
lean_object* v___x_2478_; lean_object* v___x_2480_; 
v___x_2478_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_2471_, v_snd_2472_, v_snd_2467_);
if (v_isShared_2475_ == 0)
{
lean_ctor_set(v___x_2474_, 1, v___x_2478_);
lean_ctor_set(v___x_2474_, 0, v___x_2477_);
v___x_2480_ = v___x_2474_;
goto v_reusejp_2479_;
}
else
{
lean_object* v_reuseFailAlloc_2481_; 
v_reuseFailAlloc_2481_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2481_, 0, v___x_2477_);
lean_ctor_set(v_reuseFailAlloc_2481_, 1, v___x_2478_);
v___x_2480_ = v_reuseFailAlloc_2481_;
goto v_reusejp_2479_;
}
v_reusejp_2479_:
{
return v___x_2480_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1_spec__1___redArg(lean_object* v_init_2485_, lean_object* v_x_2486_){
_start:
{
if (lean_obj_tag(v_x_2486_) == 0)
{
lean_object* v_k_2487_; lean_object* v_v_2488_; lean_object* v_l_2489_; lean_object* v_r_2490_; lean_object* v___x_2491_; lean_object* v___x_2492_; lean_object* v___x_2493_; 
v_k_2487_ = lean_ctor_get(v_x_2486_, 1);
v_v_2488_ = lean_ctor_get(v_x_2486_, 2);
v_l_2489_ = lean_ctor_get(v_x_2486_, 3);
v_r_2490_ = lean_ctor_get(v_x_2486_, 4);
v___x_2491_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1_spec__1___redArg(v_init_2485_, v_l_2489_);
lean_inc(v_v_2488_);
lean_inc(v_k_2487_);
v___x_2492_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2492_, 0, v_k_2487_);
lean_ctor_set(v___x_2492_, 1, v_v_2488_);
v___x_2493_ = lean_array_push(v___x_2491_, v___x_2492_);
v_init_2485_ = v___x_2493_;
v_x_2486_ = v_r_2490_;
goto _start;
}
else
{
return v_init_2485_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1_spec__1___redArg___boxed(lean_object* v_init_2495_, lean_object* v_x_2496_){
_start:
{
lean_object* v_res_2497_; 
v_res_2497_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1_spec__1___redArg(v_init_2495_, v_x_2496_);
lean_dec(v_x_2496_);
return v_res_2497_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2_spec__3___redArg(lean_object* v_hi_2498_, lean_object* v_pivot_2499_, lean_object* v_as_2500_, lean_object* v_i_2501_, lean_object* v_k_2502_){
_start:
{
uint8_t v___x_2503_; 
v___x_2503_ = lean_nat_dec_lt(v_k_2502_, v_hi_2498_);
if (v___x_2503_ == 0)
{
lean_object* v___x_2504_; lean_object* v___x_2505_; 
lean_dec(v_k_2502_);
v___x_2504_ = lean_array_fswap(v_as_2500_, v_i_2501_, v_hi_2498_);
v___x_2505_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2505_, 0, v_i_2501_);
lean_ctor_set(v___x_2505_, 1, v___x_2504_);
return v___x_2505_;
}
else
{
lean_object* v___x_2506_; lean_object* v_fst_2507_; lean_object* v_fst_2508_; uint8_t v___x_2509_; 
v___x_2506_ = lean_array_fget_borrowed(v_as_2500_, v_k_2502_);
v_fst_2507_ = lean_ctor_get(v___x_2506_, 0);
v_fst_2508_ = lean_ctor_get(v_pivot_2499_, 0);
v___x_2509_ = l_Lean_Name_quickLt(v_fst_2507_, v_fst_2508_);
if (v___x_2509_ == 0)
{
lean_object* v___x_2510_; lean_object* v___x_2511_; 
v___x_2510_ = lean_unsigned_to_nat(1u);
v___x_2511_ = lean_nat_add(v_k_2502_, v___x_2510_);
lean_dec(v_k_2502_);
v_k_2502_ = v___x_2511_;
goto _start;
}
else
{
lean_object* v___x_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; 
v___x_2513_ = lean_array_fswap(v_as_2500_, v_i_2501_, v_k_2502_);
v___x_2514_ = lean_unsigned_to_nat(1u);
v___x_2515_ = lean_nat_add(v_i_2501_, v___x_2514_);
lean_dec(v_i_2501_);
v___x_2516_ = lean_nat_add(v_k_2502_, v___x_2514_);
lean_dec(v_k_2502_);
v_as_2500_ = v___x_2513_;
v_i_2501_ = v___x_2515_;
v_k_2502_ = v___x_2516_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2_spec__3___redArg___boxed(lean_object* v_hi_2518_, lean_object* v_pivot_2519_, lean_object* v_as_2520_, lean_object* v_i_2521_, lean_object* v_k_2522_){
_start:
{
lean_object* v_res_2523_; 
v_res_2523_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2_spec__3___redArg(v_hi_2518_, v_pivot_2519_, v_as_2520_, v_i_2521_, v_k_2522_);
lean_dec_ref(v_pivot_2519_);
lean_dec(v_hi_2518_);
return v_res_2523_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2___redArg___lam__0(lean_object* v_a_2524_, lean_object* v_b_2525_){
_start:
{
lean_object* v_fst_2526_; lean_object* v_fst_2527_; uint8_t v___x_2528_; 
v_fst_2526_ = lean_ctor_get(v_a_2524_, 0);
v_fst_2527_ = lean_ctor_get(v_b_2525_, 0);
v___x_2528_ = l_Lean_Name_quickLt(v_fst_2526_, v_fst_2527_);
return v___x_2528_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2___redArg___lam__0___boxed(lean_object* v_a_2529_, lean_object* v_b_2530_){
_start:
{
uint8_t v_res_2531_; lean_object* v_r_2532_; 
v_res_2531_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2___redArg___lam__0(v_a_2529_, v_b_2530_);
lean_dec_ref(v_b_2530_);
lean_dec_ref(v_a_2529_);
v_r_2532_ = lean_box(v_res_2531_);
return v_r_2532_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2___redArg(lean_object* v_n_2533_, lean_object* v_as_2534_, lean_object* v_lo_2535_, lean_object* v_hi_2536_){
_start:
{
lean_object* v___y_2538_; uint8_t v___x_2548_; 
v___x_2548_ = lean_nat_dec_lt(v_lo_2535_, v_hi_2536_);
if (v___x_2548_ == 0)
{
lean_dec(v_lo_2535_);
return v_as_2534_;
}
else
{
lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v_mid_2551_; lean_object* v___y_2553_; lean_object* v___y_2559_; lean_object* v___x_2564_; lean_object* v___x_2565_; uint8_t v___x_2566_; 
v___x_2549_ = lean_nat_add(v_lo_2535_, v_hi_2536_);
v___x_2550_ = lean_unsigned_to_nat(1u);
v_mid_2551_ = lean_nat_shiftr(v___x_2549_, v___x_2550_);
lean_dec(v___x_2549_);
v___x_2564_ = lean_array_fget_borrowed(v_as_2534_, v_mid_2551_);
v___x_2565_ = lean_array_fget_borrowed(v_as_2534_, v_lo_2535_);
v___x_2566_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2___redArg___lam__0(v___x_2564_, v___x_2565_);
if (v___x_2566_ == 0)
{
v___y_2559_ = v_as_2534_;
goto v___jp_2558_;
}
else
{
lean_object* v___x_2567_; 
v___x_2567_ = lean_array_fswap(v_as_2534_, v_lo_2535_, v_mid_2551_);
v___y_2559_ = v___x_2567_;
goto v___jp_2558_;
}
v___jp_2552_:
{
lean_object* v___x_2554_; lean_object* v___x_2555_; uint8_t v___x_2556_; 
v___x_2554_ = lean_array_fget_borrowed(v___y_2553_, v_mid_2551_);
v___x_2555_ = lean_array_fget_borrowed(v___y_2553_, v_hi_2536_);
v___x_2556_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2___redArg___lam__0(v___x_2554_, v___x_2555_);
if (v___x_2556_ == 0)
{
lean_dec(v_mid_2551_);
v___y_2538_ = v___y_2553_;
goto v___jp_2537_;
}
else
{
lean_object* v___x_2557_; 
v___x_2557_ = lean_array_fswap(v___y_2553_, v_mid_2551_, v_hi_2536_);
lean_dec(v_mid_2551_);
v___y_2538_ = v___x_2557_;
goto v___jp_2537_;
}
}
v___jp_2558_:
{
lean_object* v___x_2560_; lean_object* v___x_2561_; uint8_t v___x_2562_; 
v___x_2560_ = lean_array_fget_borrowed(v___y_2559_, v_hi_2536_);
v___x_2561_ = lean_array_fget_borrowed(v___y_2559_, v_lo_2535_);
v___x_2562_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2___redArg___lam__0(v___x_2560_, v___x_2561_);
if (v___x_2562_ == 0)
{
v___y_2553_ = v___y_2559_;
goto v___jp_2552_;
}
else
{
lean_object* v___x_2563_; 
v___x_2563_ = lean_array_fswap(v___y_2559_, v_lo_2535_, v_hi_2536_);
v___y_2553_ = v___x_2563_;
goto v___jp_2552_;
}
}
}
v___jp_2537_:
{
lean_object* v_pivot_2539_; lean_object* v___x_2540_; lean_object* v_fst_2541_; lean_object* v_snd_2542_; uint8_t v___x_2543_; 
v_pivot_2539_ = lean_array_fget(v___y_2538_, v_hi_2536_);
lean_inc_n(v_lo_2535_, 2);
v___x_2540_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2_spec__3___redArg(v_hi_2536_, v_pivot_2539_, v___y_2538_, v_lo_2535_, v_lo_2535_);
lean_dec(v_pivot_2539_);
v_fst_2541_ = lean_ctor_get(v___x_2540_, 0);
lean_inc(v_fst_2541_);
v_snd_2542_ = lean_ctor_get(v___x_2540_, 1);
lean_inc(v_snd_2542_);
lean_dec_ref(v___x_2540_);
v___x_2543_ = lean_nat_dec_le(v_hi_2536_, v_fst_2541_);
if (v___x_2543_ == 0)
{
lean_object* v___x_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; 
v___x_2544_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2___redArg(v_n_2533_, v_snd_2542_, v_lo_2535_, v_fst_2541_);
v___x_2545_ = lean_unsigned_to_nat(1u);
v___x_2546_ = lean_nat_add(v_fst_2541_, v___x_2545_);
lean_dec(v_fst_2541_);
v_as_2534_ = v___x_2544_;
v_lo_2535_ = v___x_2546_;
goto _start;
}
else
{
lean_dec(v_fst_2541_);
lean_dec(v_lo_2535_);
return v_snd_2542_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2___redArg___boxed(lean_object* v_n_2568_, lean_object* v_as_2569_, lean_object* v_lo_2570_, lean_object* v_hi_2571_){
_start:
{
lean_object* v_res_2572_; 
v_res_2572_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2___redArg(v_n_2568_, v_as_2569_, v_lo_2570_, v_hi_2571_);
lean_dec(v_hi_2571_);
lean_dec(v_n_2568_);
return v_res_2572_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3_spec__5___redArg(lean_object* v_snd_2573_, lean_object* v_as_2574_, size_t v_i_2575_, size_t v_stop_2576_, lean_object* v_b_2577_){
_start:
{
lean_object* v___y_2579_; uint8_t v___x_2583_; 
v___x_2583_ = lean_usize_dec_eq(v_i_2575_, v_stop_2576_);
if (v___x_2583_ == 0)
{
lean_object* v___x_2584_; lean_object* v___x_2585_; 
v___x_2584_ = lean_array_uget_borrowed(v_as_2574_, v_i_2575_);
v___x_2585_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_snd_2573_, v___x_2584_);
if (lean_obj_tag(v___x_2585_) == 0)
{
v___y_2579_ = v_b_2577_;
goto v___jp_2578_;
}
else
{
lean_object* v_val_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; 
v_val_2586_ = lean_ctor_get(v___x_2585_, 0);
lean_inc(v_val_2586_);
lean_dec_ref(v___x_2585_);
lean_inc(v___x_2584_);
v___x_2587_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2587_, 0, v___x_2584_);
lean_ctor_set(v___x_2587_, 1, v_val_2586_);
v___x_2588_ = lean_array_push(v_b_2577_, v___x_2587_);
v___y_2579_ = v___x_2588_;
goto v___jp_2578_;
}
}
else
{
return v_b_2577_;
}
v___jp_2578_:
{
size_t v___x_2580_; size_t v___x_2581_; 
v___x_2580_ = ((size_t)1ULL);
v___x_2581_ = lean_usize_add(v_i_2575_, v___x_2580_);
v_i_2575_ = v___x_2581_;
v_b_2577_ = v___y_2579_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3_spec__5___redArg___boxed(lean_object* v_snd_2589_, lean_object* v_as_2590_, lean_object* v_i_2591_, lean_object* v_stop_2592_, lean_object* v_b_2593_){
_start:
{
size_t v_i_boxed_2594_; size_t v_stop_boxed_2595_; lean_object* v_res_2596_; 
v_i_boxed_2594_ = lean_unbox_usize(v_i_2591_);
lean_dec(v_i_2591_);
v_stop_boxed_2595_ = lean_unbox_usize(v_stop_2592_);
lean_dec(v_stop_2592_);
v_res_2596_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3_spec__5___redArg(v_snd_2589_, v_as_2590_, v_i_boxed_2594_, v_stop_boxed_2595_, v_b_2593_);
lean_dec_ref(v_as_2590_);
lean_dec(v_snd_2589_);
return v_res_2596_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3___redArg(lean_object* v_snd_2597_, lean_object* v_as_2598_, lean_object* v_start_2599_, lean_object* v_stop_2600_){
_start:
{
lean_object* v___x_2601_; uint8_t v___x_2602_; 
v___x_2601_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___lam__2___closed__0));
v___x_2602_ = lean_nat_dec_lt(v_start_2599_, v_stop_2600_);
if (v___x_2602_ == 0)
{
return v___x_2601_;
}
else
{
lean_object* v___x_2603_; uint8_t v___x_2604_; 
v___x_2603_ = lean_array_get_size(v_as_2598_);
v___x_2604_ = lean_nat_dec_le(v_stop_2600_, v___x_2603_);
if (v___x_2604_ == 0)
{
uint8_t v___x_2605_; 
v___x_2605_ = lean_nat_dec_lt(v_start_2599_, v___x_2603_);
if (v___x_2605_ == 0)
{
return v___x_2601_;
}
else
{
size_t v___x_2606_; size_t v___x_2607_; lean_object* v___x_2608_; 
v___x_2606_ = lean_usize_of_nat(v_start_2599_);
v___x_2607_ = lean_usize_of_nat(v___x_2603_);
v___x_2608_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3_spec__5___redArg(v_snd_2597_, v_as_2598_, v___x_2606_, v___x_2607_, v___x_2601_);
return v___x_2608_;
}
}
else
{
size_t v___x_2609_; size_t v___x_2610_; lean_object* v___x_2611_; 
v___x_2609_ = lean_usize_of_nat(v_start_2599_);
v___x_2610_ = lean_usize_of_nat(v_stop_2600_);
v___x_2611_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3_spec__5___redArg(v_snd_2597_, v_as_2598_, v___x_2609_, v___x_2610_, v___x_2601_);
return v___x_2611_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3___redArg___boxed(lean_object* v_snd_2612_, lean_object* v_as_2613_, lean_object* v_start_2614_, lean_object* v_stop_2615_){
_start:
{
lean_object* v_res_2616_; 
v_res_2616_ = l_Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3___redArg(v_snd_2612_, v_as_2613_, v_start_2614_, v_stop_2615_);
lean_dec(v_stop_2615_);
lean_dec(v_start_2614_);
lean_dec_ref(v_as_2613_);
lean_dec(v_snd_2612_);
return v_res_2616_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttribute_spec__0___redArg(lean_object* v_impl_2617_, lean_object* v_env_2618_, lean_object* v_as_2619_, size_t v_i_2620_, size_t v_stop_2621_, lean_object* v_b_2622_){
_start:
{
lean_object* v___y_2624_; uint8_t v___x_2628_; 
v___x_2628_ = lean_usize_dec_eq(v_i_2620_, v_stop_2621_);
if (v___x_2628_ == 0)
{
lean_object* v___x_2629_; lean_object* v_fst_2630_; lean_object* v_snd_2631_; lean_object* v_filterExport_2632_; lean_object* v___x_2633_; uint8_t v___x_2634_; 
v___x_2629_ = lean_array_uget_borrowed(v_as_2619_, v_i_2620_);
v_fst_2630_ = lean_ctor_get(v___x_2629_, 0);
v_snd_2631_ = lean_ctor_get(v___x_2629_, 1);
v_filterExport_2632_ = lean_ctor_get(v_impl_2617_, 3);
lean_inc_ref(v_filterExport_2632_);
lean_inc(v_snd_2631_);
lean_inc(v_fst_2630_);
lean_inc_ref(v_env_2618_);
v___x_2633_ = lean_apply_3(v_filterExport_2632_, v_env_2618_, v_fst_2630_, v_snd_2631_);
v___x_2634_ = lean_unbox(v___x_2633_);
if (v___x_2634_ == 0)
{
v___y_2624_ = v_b_2622_;
goto v___jp_2623_;
}
else
{
lean_object* v___x_2635_; 
lean_inc(v___x_2629_);
v___x_2635_ = lean_array_push(v_b_2622_, v___x_2629_);
v___y_2624_ = v___x_2635_;
goto v___jp_2623_;
}
}
else
{
lean_dec_ref(v_env_2618_);
lean_dec_ref(v_impl_2617_);
return v_b_2622_;
}
v___jp_2623_:
{
size_t v___x_2625_; size_t v___x_2626_; 
v___x_2625_ = ((size_t)1ULL);
v___x_2626_ = lean_usize_add(v_i_2620_, v___x_2625_);
v_i_2620_ = v___x_2626_;
v_b_2622_ = v___y_2624_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttribute_spec__0___redArg___boxed(lean_object* v_impl_2636_, lean_object* v_env_2637_, lean_object* v_as_2638_, lean_object* v_i_2639_, lean_object* v_stop_2640_, lean_object* v_b_2641_){
_start:
{
size_t v_i_boxed_2642_; size_t v_stop_boxed_2643_; lean_object* v_res_2644_; 
v_i_boxed_2642_ = lean_unbox_usize(v_i_2639_);
lean_dec(v_i_2639_);
v_stop_boxed_2643_ = lean_unbox_usize(v_stop_2640_);
lean_dec(v_stop_2640_);
v_res_2644_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttribute_spec__0___redArg(v_impl_2636_, v_env_2637_, v_as_2638_, v_i_boxed_2642_, v_stop_boxed_2643_, v_b_2641_);
lean_dec_ref(v_as_2638_);
return v_res_2644_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___lam__1(lean_object* v_impl_2645_, uint8_t v_preserveOrder_2646_, lean_object* v_env_2647_, lean_object* v_x_2648_){
_start:
{
lean_object* v___y_2650_; 
if (v_preserveOrder_2646_ == 0)
{
lean_object* v_snd_2666_; lean_object* v___x_2667_; lean_object* v___x_2668_; lean_object* v_r_2669_; lean_object* v___x_2670_; lean_object* v___y_2672_; lean_object* v___y_2673_; uint8_t v___x_2675_; 
v_snd_2666_ = lean_ctor_get(v_x_2648_, 1);
lean_inc(v_snd_2666_);
lean_dec_ref(v_x_2648_);
v___x_2667_ = lean_unsigned_to_nat(0u);
v___x_2668_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___lam__2___closed__0));
v_r_2669_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1_spec__1___redArg(v___x_2668_, v_snd_2666_);
lean_dec(v_snd_2666_);
v___x_2670_ = lean_array_get_size(v_r_2669_);
v___x_2675_ = lean_nat_dec_eq(v___x_2670_, v___x_2667_);
if (v___x_2675_ == 0)
{
lean_object* v___x_2676_; lean_object* v___x_2677_; lean_object* v___y_2679_; uint8_t v___x_2681_; 
v___x_2676_ = lean_unsigned_to_nat(1u);
v___x_2677_ = lean_nat_sub(v___x_2670_, v___x_2676_);
v___x_2681_ = lean_nat_dec_le(v___x_2667_, v___x_2677_);
if (v___x_2681_ == 0)
{
lean_inc(v___x_2677_);
v___y_2679_ = v___x_2677_;
goto v___jp_2678_;
}
else
{
v___y_2679_ = v___x_2667_;
goto v___jp_2678_;
}
v___jp_2678_:
{
uint8_t v___x_2680_; 
v___x_2680_ = lean_nat_dec_le(v___y_2679_, v___x_2677_);
if (v___x_2680_ == 0)
{
lean_dec(v___x_2677_);
lean_inc(v___y_2679_);
v___y_2672_ = v___y_2679_;
v___y_2673_ = v___y_2679_;
goto v___jp_2671_;
}
else
{
v___y_2672_ = v___y_2679_;
v___y_2673_ = v___x_2677_;
goto v___jp_2671_;
}
}
}
else
{
v___y_2650_ = v_r_2669_;
goto v___jp_2649_;
}
v___jp_2671_:
{
lean_object* v___x_2674_; 
v___x_2674_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2___redArg(v___x_2670_, v_r_2669_, v___y_2672_, v___y_2673_);
lean_dec(v___y_2673_);
v___y_2650_ = v___x_2674_;
goto v___jp_2649_;
}
}
else
{
lean_object* v_fst_2682_; lean_object* v_snd_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; 
v_fst_2682_ = lean_ctor_get(v_x_2648_, 0);
lean_inc(v_fst_2682_);
v_snd_2683_ = lean_ctor_get(v_x_2648_, 1);
lean_inc(v_snd_2683_);
lean_dec_ref(v_x_2648_);
v___x_2684_ = lean_array_mk(v_fst_2682_);
v___x_2685_ = l_Array_reverse___redArg(v___x_2684_);
v___x_2686_ = lean_unsigned_to_nat(0u);
v___x_2687_ = lean_array_get_size(v___x_2685_);
v___x_2688_ = l_Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3___redArg(v_snd_2683_, v___x_2685_, v___x_2686_, v___x_2687_);
lean_dec_ref(v___x_2685_);
lean_dec(v_snd_2683_);
v___y_2650_ = v___x_2688_;
goto v___jp_2649_;
}
v___jp_2649_:
{
lean_object* v___x_2651_; lean_object* v___x_2652_; lean_object* v___x_2653_; uint8_t v___x_2654_; 
v___x_2651_ = lean_unsigned_to_nat(0u);
v___x_2652_ = lean_array_get_size(v___y_2650_);
v___x_2653_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___lam__2___closed__0));
v___x_2654_ = lean_nat_dec_lt(v___x_2651_, v___x_2652_);
if (v___x_2654_ == 0)
{
lean_object* v___x_2655_; 
lean_dec_ref(v_env_2647_);
lean_dec_ref(v_impl_2645_);
v___x_2655_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2655_, 0, v___x_2653_);
lean_ctor_set(v___x_2655_, 1, v___x_2653_);
lean_ctor_set(v___x_2655_, 2, v___y_2650_);
return v___x_2655_;
}
else
{
uint8_t v___x_2656_; 
v___x_2656_ = lean_nat_dec_le(v___x_2652_, v___x_2652_);
if (v___x_2656_ == 0)
{
if (v___x_2654_ == 0)
{
lean_object* v___x_2657_; 
lean_dec_ref(v_env_2647_);
lean_dec_ref(v_impl_2645_);
v___x_2657_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2657_, 0, v___x_2653_);
lean_ctor_set(v___x_2657_, 1, v___x_2653_);
lean_ctor_set(v___x_2657_, 2, v___y_2650_);
return v___x_2657_;
}
else
{
size_t v___x_2658_; size_t v___x_2659_; lean_object* v___x_2660_; lean_object* v___x_2661_; 
v___x_2658_ = ((size_t)0ULL);
v___x_2659_ = lean_usize_of_nat(v___x_2652_);
v___x_2660_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttribute_spec__0___redArg(v_impl_2645_, v_env_2647_, v___y_2650_, v___x_2658_, v___x_2659_, v___x_2653_);
lean_inc_ref(v___x_2660_);
v___x_2661_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2661_, 0, v___x_2660_);
lean_ctor_set(v___x_2661_, 1, v___x_2660_);
lean_ctor_set(v___x_2661_, 2, v___y_2650_);
return v___x_2661_;
}
}
else
{
size_t v___x_2662_; size_t v___x_2663_; lean_object* v___x_2664_; lean_object* v___x_2665_; 
v___x_2662_ = ((size_t)0ULL);
v___x_2663_ = lean_usize_of_nat(v___x_2652_);
v___x_2664_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttribute_spec__0___redArg(v_impl_2645_, v_env_2647_, v___y_2650_, v___x_2662_, v___x_2663_, v___x_2653_);
lean_inc_ref(v___x_2664_);
v___x_2665_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2665_, 0, v___x_2664_);
lean_ctor_set(v___x_2665_, 1, v___x_2664_);
lean_ctor_set(v___x_2665_, 2, v___y_2650_);
return v___x_2665_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___lam__1___boxed(lean_object* v_impl_2689_, lean_object* v_preserveOrder_2690_, lean_object* v_env_2691_, lean_object* v_x_2692_){
_start:
{
uint8_t v_preserveOrder_boxed_2693_; lean_object* v_res_2694_; 
v_preserveOrder_boxed_2693_ = lean_unbox(v_preserveOrder_2690_);
v_res_2694_ = l_Lean_registerParametricAttribute___redArg___lam__1(v_impl_2689_, v_preserveOrder_boxed_2693_, v_env_2691_, v_x_2692_);
return v_res_2694_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___lam__2(lean_object* v_x_2704_){
_start:
{
lean_object* v_snd_2705_; lean_object* v___x_2707_; uint8_t v_isShared_2708_; uint8_t v_isSharedCheck_2719_; 
v_snd_2705_ = lean_ctor_get(v_x_2704_, 1);
v_isSharedCheck_2719_ = !lean_is_exclusive(v_x_2704_);
if (v_isSharedCheck_2719_ == 0)
{
lean_object* v_unused_2720_; 
v_unused_2720_ = lean_ctor_get(v_x_2704_, 0);
lean_dec(v_unused_2720_);
v___x_2707_ = v_x_2704_;
v_isShared_2708_ = v_isSharedCheck_2719_;
goto v_resetjp_2706_;
}
else
{
lean_inc(v_snd_2705_);
lean_dec(v_x_2704_);
v___x_2707_ = lean_box(0);
v_isShared_2708_ = v_isSharedCheck_2719_;
goto v_resetjp_2706_;
}
v_resetjp_2706_:
{
lean_object* v___x_2709_; lean_object* v___y_2711_; 
v___x_2709_ = ((lean_object*)(l_Lean_registerParametricAttribute___redArg___lam__2___closed__3));
if (lean_obj_tag(v_snd_2705_) == 0)
{
lean_object* v_size_2717_; 
v_size_2717_ = lean_ctor_get(v_snd_2705_, 0);
lean_inc(v_size_2717_);
lean_dec_ref(v_snd_2705_);
v___y_2711_ = v_size_2717_;
goto v___jp_2710_;
}
else
{
lean_object* v___x_2718_; 
v___x_2718_ = lean_unsigned_to_nat(0u);
v___y_2711_ = v___x_2718_;
goto v___jp_2710_;
}
v___jp_2710_:
{
lean_object* v___x_2712_; lean_object* v___x_2713_; lean_object* v___x_2715_; 
v___x_2712_ = l_Nat_reprFast(v___y_2711_);
v___x_2713_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2713_, 0, v___x_2712_);
if (v_isShared_2708_ == 0)
{
lean_ctor_set_tag(v___x_2707_, 5);
lean_ctor_set(v___x_2707_, 1, v___x_2713_);
lean_ctor_set(v___x_2707_, 0, v___x_2709_);
v___x_2715_ = v___x_2707_;
goto v_reusejp_2714_;
}
else
{
lean_object* v_reuseFailAlloc_2716_; 
v_reuseFailAlloc_2716_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2716_, 0, v___x_2709_);
lean_ctor_set(v_reuseFailAlloc_2716_, 1, v___x_2713_);
v___x_2715_ = v_reuseFailAlloc_2716_;
goto v_reusejp_2714_;
}
v_reusejp_2714_:
{
return v___x_2715_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___lam__3(lean_object* v_x_2721_){
_start:
{
lean_object* v___x_2722_; 
v___x_2722_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___lam__2___closed__0));
return v___x_2722_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___lam__3___boxed(lean_object* v_x_2723_){
_start:
{
lean_object* v_res_2724_; 
v_res_2724_ = l_Lean_registerParametricAttribute___redArg___lam__3(v_x_2723_);
lean_dec_ref(v_x_2723_);
return v_res_2724_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___lam__4(lean_object* v___x_2725_, lean_object* v_x_2726_, lean_object* v___y_2727_){
_start:
{
lean_object* v___x_2729_; 
v___x_2729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2729_, 0, v___x_2725_);
return v___x_2729_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___lam__4___boxed(lean_object* v___x_2730_, lean_object* v_x_2731_, lean_object* v___y_2732_, lean_object* v___y_2733_){
_start:
{
lean_object* v_res_2734_; 
v_res_2734_ = l_Lean_registerParametricAttribute___redArg___lam__4(v___x_2730_, v_x_2731_, v___y_2732_);
lean_dec_ref(v___y_2732_);
lean_dec_ref(v_x_2731_);
return v_res_2734_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___lam__5(lean_object* v___x_2735_){
_start:
{
lean_object* v___x_2737_; 
v___x_2737_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2737_, 0, v___x_2735_);
return v___x_2737_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___lam__5___boxed(lean_object* v___x_2738_, lean_object* v___y_2739_){
_start:
{
lean_object* v_res_2740_; 
v_res_2740_ = l_Lean_registerParametricAttribute___redArg___lam__5(v___x_2738_);
return v_res_2740_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___lam__7(lean_object* v_getParam_2741_, lean_object* v_a_2742_, lean_object* v_afterSet_2743_, lean_object* v_name_2744_, lean_object* v_decl_2745_, lean_object* v_stx_2746_, uint8_t v_kind_2747_, lean_object* v___y_2748_, lean_object* v___y_2749_){
_start:
{
lean_object* v___y_2752_; lean_object* v___y_2753_; lean_object* v___y_2754_; lean_object* v___y_2755_; uint8_t v___y_2756_; lean_object* v___y_2759_; lean_object* v___y_2760_; lean_object* v___y_2761_; uint8_t v___x_2804_; uint8_t v___x_2805_; 
v___x_2804_ = 0;
v___x_2805_ = l_Lean_instBEqAttributeKind_beq(v_kind_2747_, v___x_2804_);
if (v___x_2805_ == 0)
{
lean_object* v___x_2806_; 
lean_dec(v_stx_2746_);
lean_dec(v_decl_2745_);
lean_dec_ref(v_afterSet_2743_);
lean_dec_ref(v_a_2742_);
lean_dec_ref(v_getParam_2741_);
v___x_2806_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg(v_name_2744_, v_kind_2747_, v___y_2748_, v___y_2749_);
return v___x_2806_;
}
else
{
goto v___jp_2799_;
}
v___jp_2751_:
{
if (v___y_2756_ == 0)
{
lean_object* v___x_2757_; 
lean_dec_ref(v___y_2753_);
v___x_2757_ = l_Lean_setEnv___at___00Lean_registerParametricAttribute_spec__4___redArg(v___y_2752_, v___y_2755_);
return v___x_2757_;
}
else
{
lean_dec_ref(v___y_2752_);
return v___y_2753_;
}
}
v___jp_2758_:
{
lean_object* v___x_2762_; 
lean_inc(v___y_2761_);
lean_inc_ref(v___y_2760_);
lean_inc(v_decl_2745_);
v___x_2762_ = lean_apply_5(v_getParam_2741_, v_decl_2745_, v_stx_2746_, v___y_2760_, v___y_2761_, lean_box(0));
if (lean_obj_tag(v___x_2762_) == 0)
{
lean_object* v_a_2763_; lean_object* v___x_2764_; lean_object* v_toEnvExtension_2765_; lean_object* v_env_2766_; lean_object* v_nextMacroScope_2767_; lean_object* v_ngen_2768_; lean_object* v_auxDeclNGen_2769_; lean_object* v_traceState_2770_; lean_object* v_messages_2771_; lean_object* v_infoState_2772_; lean_object* v_snapshotTasks_2773_; lean_object* v___x_2775_; uint8_t v_isShared_2776_; uint8_t v_isSharedCheck_2789_; 
v_a_2763_ = lean_ctor_get(v___x_2762_, 0);
lean_inc(v_a_2763_);
lean_dec_ref(v___x_2762_);
v___x_2764_ = lean_st_ref_take(v___y_2761_);
v_toEnvExtension_2765_ = lean_ctor_get(v_a_2742_, 0);
v_env_2766_ = lean_ctor_get(v___x_2764_, 0);
v_nextMacroScope_2767_ = lean_ctor_get(v___x_2764_, 1);
v_ngen_2768_ = lean_ctor_get(v___x_2764_, 2);
v_auxDeclNGen_2769_ = lean_ctor_get(v___x_2764_, 3);
v_traceState_2770_ = lean_ctor_get(v___x_2764_, 4);
v_messages_2771_ = lean_ctor_get(v___x_2764_, 6);
v_infoState_2772_ = lean_ctor_get(v___x_2764_, 7);
v_snapshotTasks_2773_ = lean_ctor_get(v___x_2764_, 8);
v_isSharedCheck_2789_ = !lean_is_exclusive(v___x_2764_);
if (v_isSharedCheck_2789_ == 0)
{
lean_object* v_unused_2790_; 
v_unused_2790_ = lean_ctor_get(v___x_2764_, 5);
lean_dec(v_unused_2790_);
v___x_2775_ = v___x_2764_;
v_isShared_2776_ = v_isSharedCheck_2789_;
goto v_resetjp_2774_;
}
else
{
lean_inc(v_snapshotTasks_2773_);
lean_inc(v_infoState_2772_);
lean_inc(v_messages_2771_);
lean_inc(v_traceState_2770_);
lean_inc(v_auxDeclNGen_2769_);
lean_inc(v_ngen_2768_);
lean_inc(v_nextMacroScope_2767_);
lean_inc(v_env_2766_);
lean_dec(v___x_2764_);
v___x_2775_ = lean_box(0);
v_isShared_2776_ = v_isSharedCheck_2789_;
goto v_resetjp_2774_;
}
v_resetjp_2774_:
{
lean_object* v_asyncMode_2777_; lean_object* v___x_2778_; lean_object* v___x_2779_; lean_object* v___x_2780_; lean_object* v___x_2782_; 
v_asyncMode_2777_ = lean_ctor_get(v_toEnvExtension_2765_, 2);
lean_inc(v_asyncMode_2777_);
lean_inc(v_a_2763_);
lean_inc_n(v_decl_2745_, 2);
v___x_2778_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2778_, 0, v_decl_2745_);
lean_ctor_set(v___x_2778_, 1, v_a_2763_);
v___x_2779_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_a_2742_, v_env_2766_, v___x_2778_, v_asyncMode_2777_, v_decl_2745_);
lean_dec(v_asyncMode_2777_);
v___x_2780_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2);
if (v_isShared_2776_ == 0)
{
lean_ctor_set(v___x_2775_, 5, v___x_2780_);
lean_ctor_set(v___x_2775_, 0, v___x_2779_);
v___x_2782_ = v___x_2775_;
goto v_reusejp_2781_;
}
else
{
lean_object* v_reuseFailAlloc_2788_; 
v_reuseFailAlloc_2788_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2788_, 0, v___x_2779_);
lean_ctor_set(v_reuseFailAlloc_2788_, 1, v_nextMacroScope_2767_);
lean_ctor_set(v_reuseFailAlloc_2788_, 2, v_ngen_2768_);
lean_ctor_set(v_reuseFailAlloc_2788_, 3, v_auxDeclNGen_2769_);
lean_ctor_set(v_reuseFailAlloc_2788_, 4, v_traceState_2770_);
lean_ctor_set(v_reuseFailAlloc_2788_, 5, v___x_2780_);
lean_ctor_set(v_reuseFailAlloc_2788_, 6, v_messages_2771_);
lean_ctor_set(v_reuseFailAlloc_2788_, 7, v_infoState_2772_);
lean_ctor_set(v_reuseFailAlloc_2788_, 8, v_snapshotTasks_2773_);
v___x_2782_ = v_reuseFailAlloc_2788_;
goto v_reusejp_2781_;
}
v_reusejp_2781_:
{
lean_object* v___x_2783_; lean_object* v___x_2784_; 
v___x_2783_ = lean_st_ref_set(v___y_2761_, v___x_2782_);
lean_inc(v___y_2761_);
lean_inc_ref(v___y_2760_);
v___x_2784_ = lean_apply_5(v_afterSet_2743_, v_decl_2745_, v_a_2763_, v___y_2760_, v___y_2761_, lean_box(0));
if (lean_obj_tag(v___x_2784_) == 0)
{
lean_dec_ref(v___y_2759_);
return v___x_2784_;
}
else
{
lean_object* v_a_2785_; uint8_t v___x_2786_; 
v_a_2785_ = lean_ctor_get(v___x_2784_, 0);
lean_inc(v_a_2785_);
v___x_2786_ = l_Lean_Exception_isInterrupt(v_a_2785_);
if (v___x_2786_ == 0)
{
uint8_t v___x_2787_; 
v___x_2787_ = l_Lean_Exception_isRuntime(v_a_2785_);
v___y_2752_ = v___y_2759_;
v___y_2753_ = v___x_2784_;
v___y_2754_ = v___y_2760_;
v___y_2755_ = v___y_2761_;
v___y_2756_ = v___x_2787_;
goto v___jp_2751_;
}
else
{
lean_dec(v_a_2785_);
v___y_2752_ = v___y_2759_;
v___y_2753_ = v___x_2784_;
v___y_2754_ = v___y_2760_;
v___y_2755_ = v___y_2761_;
v___y_2756_ = v___x_2786_;
goto v___jp_2751_;
}
}
}
}
}
else
{
lean_object* v_a_2791_; lean_object* v___x_2793_; uint8_t v_isShared_2794_; uint8_t v_isSharedCheck_2798_; 
lean_dec_ref(v___y_2759_);
lean_dec(v_decl_2745_);
lean_dec_ref(v_afterSet_2743_);
lean_dec_ref(v_a_2742_);
v_a_2791_ = lean_ctor_get(v___x_2762_, 0);
v_isSharedCheck_2798_ = !lean_is_exclusive(v___x_2762_);
if (v_isSharedCheck_2798_ == 0)
{
v___x_2793_ = v___x_2762_;
v_isShared_2794_ = v_isSharedCheck_2798_;
goto v_resetjp_2792_;
}
else
{
lean_inc(v_a_2791_);
lean_dec(v___x_2762_);
v___x_2793_ = lean_box(0);
v_isShared_2794_ = v_isSharedCheck_2798_;
goto v_resetjp_2792_;
}
v_resetjp_2792_:
{
lean_object* v___x_2796_; 
if (v_isShared_2794_ == 0)
{
v___x_2796_ = v___x_2793_;
goto v_reusejp_2795_;
}
else
{
lean_object* v_reuseFailAlloc_2797_; 
v_reuseFailAlloc_2797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2797_, 0, v_a_2791_);
v___x_2796_ = v_reuseFailAlloc_2797_;
goto v_reusejp_2795_;
}
v_reusejp_2795_:
{
return v___x_2796_;
}
}
}
}
v___jp_2799_:
{
lean_object* v___x_2800_; lean_object* v_env_2801_; lean_object* v___x_2802_; 
v___x_2800_ = lean_st_ref_get(v___y_2749_);
v_env_2801_ = lean_ctor_get(v___x_2800_, 0);
lean_inc_ref(v_env_2801_);
lean_dec(v___x_2800_);
v___x_2802_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2801_, v_decl_2745_);
if (lean_obj_tag(v___x_2802_) == 0)
{
lean_dec(v_name_2744_);
v___y_2759_ = v_env_2801_;
v___y_2760_ = v___y_2748_;
v___y_2761_ = v___y_2749_;
goto v___jp_2758_;
}
else
{
lean_object* v___x_2803_; 
lean_dec_ref(v___x_2802_);
lean_dec_ref(v_env_2801_);
lean_dec(v_stx_2746_);
lean_dec_ref(v_afterSet_2743_);
lean_dec_ref(v_a_2742_);
lean_dec_ref(v_getParam_2741_);
v___x_2803_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg(v_name_2744_, v_decl_2745_, v___y_2748_, v___y_2749_);
return v___x_2803_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___lam__7___boxed(lean_object* v_getParam_2807_, lean_object* v_a_2808_, lean_object* v_afterSet_2809_, lean_object* v_name_2810_, lean_object* v_decl_2811_, lean_object* v_stx_2812_, lean_object* v_kind_2813_, lean_object* v___y_2814_, lean_object* v___y_2815_, lean_object* v___y_2816_){
_start:
{
uint8_t v_kind_boxed_2817_; lean_object* v_res_2818_; 
v_kind_boxed_2817_ = lean_unbox(v_kind_2813_);
v_res_2818_ = l_Lean_registerParametricAttribute___redArg___lam__7(v_getParam_2807_, v_a_2808_, v_afterSet_2809_, v_name_2810_, v_decl_2811_, v_stx_2812_, v_kind_boxed_2817_, v___y_2814_, v___y_2815_);
lean_dec(v___y_2815_);
lean_dec_ref(v___y_2814_);
return v_res_2818_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg(lean_object* v_impl_2829_){
_start:
{
lean_object* v_toAttributeImplCore_2831_; lean_object* v_getParam_2832_; lean_object* v_afterSet_2833_; uint8_t v_preserveOrder_2834_; lean_object* v_ref_2835_; lean_object* v_name_2836_; lean_object* v___f_2837_; lean_object* v___x_2838_; lean_object* v___f_2839_; lean_object* v___f_2840_; lean_object* v___f_2841_; lean_object* v___f_2842_; lean_object* v___f_2843_; lean_object* v___x_2844_; lean_object* v___x_2845_; lean_object* v___x_2846_; lean_object* v___x_2847_; lean_object* v___x_2848_; 
v_toAttributeImplCore_2831_ = lean_ctor_get(v_impl_2829_, 0);
lean_inc_ref(v_toAttributeImplCore_2831_);
v_getParam_2832_ = lean_ctor_get(v_impl_2829_, 1);
lean_inc_ref(v_getParam_2832_);
v_afterSet_2833_ = lean_ctor_get(v_impl_2829_, 2);
lean_inc_ref(v_afterSet_2833_);
v_preserveOrder_2834_ = lean_ctor_get_uint8(v_impl_2829_, sizeof(void*)*4);
v_ref_2835_ = lean_ctor_get(v_toAttributeImplCore_2831_, 0);
v_name_2836_ = lean_ctor_get(v_toAttributeImplCore_2831_, 1);
v___f_2837_ = ((lean_object*)(l_Lean_registerParametricAttribute___redArg___closed__0));
v___x_2838_ = lean_box(v_preserveOrder_2834_);
v___f_2839_ = lean_alloc_closure((void*)(l_Lean_registerParametricAttribute___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_2839_, 0, v_impl_2829_);
lean_closure_set(v___f_2839_, 1, v___x_2838_);
v___f_2840_ = ((lean_object*)(l_Lean_registerParametricAttribute___redArg___closed__1));
v___f_2841_ = ((lean_object*)(l_Lean_registerParametricAttribute___redArg___closed__2));
v___f_2842_ = ((lean_object*)(l_Lean_registerParametricAttribute___redArg___closed__4));
v___f_2843_ = ((lean_object*)(l_Lean_registerParametricAttribute___redArg___closed__5));
v___x_2844_ = lean_box(2);
v___x_2845_ = lean_box(0);
lean_inc(v_ref_2835_);
v___x_2846_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_2846_, 0, v_ref_2835_);
lean_ctor_set(v___x_2846_, 1, v___f_2843_);
lean_ctor_set(v___x_2846_, 2, v___f_2842_);
lean_ctor_set(v___x_2846_, 3, v___f_2837_);
lean_ctor_set(v___x_2846_, 4, v___f_2839_);
lean_ctor_set(v___x_2846_, 5, v___f_2840_);
lean_ctor_set(v___x_2846_, 6, v___x_2844_);
lean_ctor_set(v___x_2846_, 7, v___x_2845_);
v___x_2847_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2847_, 0, v___x_2846_);
lean_ctor_set(v___x_2847_, 1, v___f_2841_);
v___x_2848_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_2847_);
if (lean_obj_tag(v___x_2848_) == 0)
{
lean_object* v_a_2849_; lean_object* v___f_2850_; lean_object* v___f_2851_; lean_object* v___x_2852_; lean_object* v___x_2853_; 
v_a_2849_ = lean_ctor_get(v___x_2848_, 0);
lean_inc_n(v_a_2849_, 2);
lean_dec_ref(v___x_2848_);
lean_inc_n(v_name_2836_, 2);
v___f_2850_ = lean_alloc_closure((void*)(l_Lean_registerTagAttribute___lam__6___boxed), 5, 1);
lean_closure_set(v___f_2850_, 0, v_name_2836_);
v___f_2851_ = lean_alloc_closure((void*)(l_Lean_registerParametricAttribute___redArg___lam__7___boxed), 10, 4);
lean_closure_set(v___f_2851_, 0, v_getParam_2832_);
lean_closure_set(v___f_2851_, 1, v_a_2849_);
lean_closure_set(v___f_2851_, 2, v_afterSet_2833_);
lean_closure_set(v___f_2851_, 3, v_name_2836_);
v___x_2852_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2852_, 0, v_toAttributeImplCore_2831_);
lean_ctor_set(v___x_2852_, 1, v___f_2851_);
lean_ctor_set(v___x_2852_, 2, v___f_2850_);
lean_inc_ref(v___x_2852_);
v___x_2853_ = l_Lean_registerBuiltinAttribute(v___x_2852_);
if (lean_obj_tag(v___x_2853_) == 0)
{
lean_object* v___x_2855_; uint8_t v_isShared_2856_; uint8_t v_isSharedCheck_2861_; 
v_isSharedCheck_2861_ = !lean_is_exclusive(v___x_2853_);
if (v_isSharedCheck_2861_ == 0)
{
lean_object* v_unused_2862_; 
v_unused_2862_ = lean_ctor_get(v___x_2853_, 0);
lean_dec(v_unused_2862_);
v___x_2855_ = v___x_2853_;
v_isShared_2856_ = v_isSharedCheck_2861_;
goto v_resetjp_2854_;
}
else
{
lean_dec(v___x_2853_);
v___x_2855_ = lean_box(0);
v_isShared_2856_ = v_isSharedCheck_2861_;
goto v_resetjp_2854_;
}
v_resetjp_2854_:
{
lean_object* v___x_2857_; lean_object* v___x_2859_; 
v___x_2857_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2857_, 0, v___x_2852_);
lean_ctor_set(v___x_2857_, 1, v_a_2849_);
lean_ctor_set_uint8(v___x_2857_, sizeof(void*)*2, v_preserveOrder_2834_);
if (v_isShared_2856_ == 0)
{
lean_ctor_set(v___x_2855_, 0, v___x_2857_);
v___x_2859_ = v___x_2855_;
goto v_reusejp_2858_;
}
else
{
lean_object* v_reuseFailAlloc_2860_; 
v_reuseFailAlloc_2860_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2860_, 0, v___x_2857_);
v___x_2859_ = v_reuseFailAlloc_2860_;
goto v_reusejp_2858_;
}
v_reusejp_2858_:
{
return v___x_2859_;
}
}
}
else
{
lean_object* v_a_2863_; lean_object* v___x_2865_; uint8_t v_isShared_2866_; uint8_t v_isSharedCheck_2870_; 
lean_dec_ref(v___x_2852_);
lean_dec(v_a_2849_);
v_a_2863_ = lean_ctor_get(v___x_2853_, 0);
v_isSharedCheck_2870_ = !lean_is_exclusive(v___x_2853_);
if (v_isSharedCheck_2870_ == 0)
{
v___x_2865_ = v___x_2853_;
v_isShared_2866_ = v_isSharedCheck_2870_;
goto v_resetjp_2864_;
}
else
{
lean_inc(v_a_2863_);
lean_dec(v___x_2853_);
v___x_2865_ = lean_box(0);
v_isShared_2866_ = v_isSharedCheck_2870_;
goto v_resetjp_2864_;
}
v_resetjp_2864_:
{
lean_object* v___x_2868_; 
if (v_isShared_2866_ == 0)
{
v___x_2868_ = v___x_2865_;
goto v_reusejp_2867_;
}
else
{
lean_object* v_reuseFailAlloc_2869_; 
v_reuseFailAlloc_2869_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2869_, 0, v_a_2863_);
v___x_2868_ = v_reuseFailAlloc_2869_;
goto v_reusejp_2867_;
}
v_reusejp_2867_:
{
return v___x_2868_;
}
}
}
}
else
{
lean_object* v_a_2871_; lean_object* v___x_2873_; uint8_t v_isShared_2874_; uint8_t v_isSharedCheck_2878_; 
lean_dec_ref(v_afterSet_2833_);
lean_dec_ref(v_getParam_2832_);
lean_dec_ref(v_toAttributeImplCore_2831_);
v_a_2871_ = lean_ctor_get(v___x_2848_, 0);
v_isSharedCheck_2878_ = !lean_is_exclusive(v___x_2848_);
if (v_isSharedCheck_2878_ == 0)
{
v___x_2873_ = v___x_2848_;
v_isShared_2874_ = v_isSharedCheck_2878_;
goto v_resetjp_2872_;
}
else
{
lean_inc(v_a_2871_);
lean_dec(v___x_2848_);
v___x_2873_ = lean_box(0);
v_isShared_2874_ = v_isSharedCheck_2878_;
goto v_resetjp_2872_;
}
v_resetjp_2872_:
{
lean_object* v___x_2876_; 
if (v_isShared_2874_ == 0)
{
v___x_2876_ = v___x_2873_;
goto v_reusejp_2875_;
}
else
{
lean_object* v_reuseFailAlloc_2877_; 
v_reuseFailAlloc_2877_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2877_, 0, v_a_2871_);
v___x_2876_ = v_reuseFailAlloc_2877_;
goto v_reusejp_2875_;
}
v_reusejp_2875_:
{
return v___x_2876_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___boxed(lean_object* v_impl_2879_, lean_object* v_a_2880_){
_start:
{
lean_object* v_res_2881_; 
v_res_2881_ = l_Lean_registerParametricAttribute___redArg(v_impl_2879_);
return v_res_2881_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute(lean_object* v_00_u03b1_2882_, lean_object* v_impl_2883_){
_start:
{
lean_object* v___x_2885_; 
v___x_2885_ = l_Lean_registerParametricAttribute___redArg(v_impl_2883_);
return v___x_2885_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___boxed(lean_object* v_00_u03b1_2886_, lean_object* v_impl_2887_, lean_object* v_a_2888_){
_start:
{
lean_object* v_res_2889_; 
v_res_2889_ = l_Lean_registerParametricAttribute(v_00_u03b1_2886_, v_impl_2887_);
return v_res_2889_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttribute_spec__0(lean_object* v_00_u03b1_2890_, lean_object* v_impl_2891_, lean_object* v_env_2892_, lean_object* v_as_2893_, size_t v_i_2894_, size_t v_stop_2895_, lean_object* v_b_2896_){
_start:
{
lean_object* v___x_2897_; 
v___x_2897_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttribute_spec__0___redArg(v_impl_2891_, v_env_2892_, v_as_2893_, v_i_2894_, v_stop_2895_, v_b_2896_);
return v___x_2897_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttribute_spec__0___boxed(lean_object* v_00_u03b1_2898_, lean_object* v_impl_2899_, lean_object* v_env_2900_, lean_object* v_as_2901_, lean_object* v_i_2902_, lean_object* v_stop_2903_, lean_object* v_b_2904_){
_start:
{
size_t v_i_boxed_2905_; size_t v_stop_boxed_2906_; lean_object* v_res_2907_; 
v_i_boxed_2905_ = lean_unbox_usize(v_i_2902_);
lean_dec(v_i_2902_);
v_stop_boxed_2906_ = lean_unbox_usize(v_stop_2903_);
lean_dec(v_stop_2903_);
v_res_2907_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttribute_spec__0(v_00_u03b1_2898_, v_impl_2899_, v_env_2900_, v_as_2901_, v_i_boxed_2905_, v_stop_boxed_2906_, v_b_2904_);
lean_dec_ref(v_as_2901_);
return v_res_2907_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1___redArg(lean_object* v_init_2908_, lean_object* v_t_2909_){
_start:
{
lean_object* v___x_2910_; 
v___x_2910_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1_spec__1___redArg(v_init_2908_, v_t_2909_);
return v___x_2910_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1___redArg___boxed(lean_object* v_init_2911_, lean_object* v_t_2912_){
_start:
{
lean_object* v_res_2913_; 
v_res_2913_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1___redArg(v_init_2911_, v_t_2912_);
lean_dec(v_t_2912_);
return v_res_2913_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1(lean_object* v_00_u03b1_2914_, lean_object* v_init_2915_, lean_object* v_t_2916_){
_start:
{
lean_object* v___x_2917_; 
v___x_2917_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1_spec__1___redArg(v_init_2915_, v_t_2916_);
return v___x_2917_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1___boxed(lean_object* v_00_u03b1_2918_, lean_object* v_init_2919_, lean_object* v_t_2920_){
_start:
{
lean_object* v_res_2921_; 
v_res_2921_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1(v_00_u03b1_2918_, v_init_2919_, v_t_2920_);
lean_dec(v_t_2920_);
return v_res_2921_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2(lean_object* v_00_u03b1_2922_, lean_object* v_n_2923_, lean_object* v_as_2924_, lean_object* v_lo_2925_, lean_object* v_hi_2926_, lean_object* v_w_2927_, lean_object* v_hlo_2928_, lean_object* v_hhi_2929_){
_start:
{
lean_object* v___x_2930_; 
v___x_2930_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2___redArg(v_n_2923_, v_as_2924_, v_lo_2925_, v_hi_2926_);
return v___x_2930_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2___boxed(lean_object* v_00_u03b1_2931_, lean_object* v_n_2932_, lean_object* v_as_2933_, lean_object* v_lo_2934_, lean_object* v_hi_2935_, lean_object* v_w_2936_, lean_object* v_hlo_2937_, lean_object* v_hhi_2938_){
_start:
{
lean_object* v_res_2939_; 
v_res_2939_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2(v_00_u03b1_2931_, v_n_2932_, v_as_2933_, v_lo_2934_, v_hi_2935_, v_w_2936_, v_hlo_2937_, v_hhi_2938_);
lean_dec(v_hi_2935_);
lean_dec(v_n_2932_);
return v_res_2939_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3(lean_object* v_00_u03b1_2940_, lean_object* v_snd_2941_, lean_object* v_as_2942_, lean_object* v_start_2943_, lean_object* v_stop_2944_){
_start:
{
lean_object* v___x_2945_; 
v___x_2945_ = l_Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3___redArg(v_snd_2941_, v_as_2942_, v_start_2943_, v_stop_2944_);
return v___x_2945_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3___boxed(lean_object* v_00_u03b1_2946_, lean_object* v_snd_2947_, lean_object* v_as_2948_, lean_object* v_start_2949_, lean_object* v_stop_2950_){
_start:
{
lean_object* v_res_2951_; 
v_res_2951_ = l_Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3(v_00_u03b1_2946_, v_snd_2947_, v_as_2948_, v_start_2949_, v_stop_2950_);
lean_dec(v_stop_2950_);
lean_dec(v_start_2949_);
lean_dec_ref(v_as_2948_);
lean_dec(v_snd_2947_);
return v_res_2951_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1_spec__1(lean_object* v_00_u03b1_2952_, lean_object* v_init_2953_, lean_object* v_x_2954_){
_start:
{
lean_object* v___x_2955_; 
v___x_2955_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1_spec__1___redArg(v_init_2953_, v_x_2954_);
return v___x_2955_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1_spec__1___boxed(lean_object* v_00_u03b1_2956_, lean_object* v_init_2957_, lean_object* v_x_2958_){
_start:
{
lean_object* v_res_2959_; 
v_res_2959_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1_spec__1(v_00_u03b1_2956_, v_init_2957_, v_x_2958_);
lean_dec(v_x_2958_);
return v_res_2959_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2_spec__3(lean_object* v_00_u03b1_2960_, lean_object* v_n_2961_, lean_object* v_lo_2962_, lean_object* v_hi_2963_, lean_object* v_hhi_2964_, lean_object* v_pivot_2965_, lean_object* v_as_2966_, lean_object* v_i_2967_, lean_object* v_k_2968_, lean_object* v_ilo_2969_, lean_object* v_ik_2970_, lean_object* v_w_2971_){
_start:
{
lean_object* v___x_2972_; 
v___x_2972_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2_spec__3___redArg(v_hi_2963_, v_pivot_2965_, v_as_2966_, v_i_2967_, v_k_2968_);
return v___x_2972_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2_spec__3___boxed(lean_object* v_00_u03b1_2973_, lean_object* v_n_2974_, lean_object* v_lo_2975_, lean_object* v_hi_2976_, lean_object* v_hhi_2977_, lean_object* v_pivot_2978_, lean_object* v_as_2979_, lean_object* v_i_2980_, lean_object* v_k_2981_, lean_object* v_ilo_2982_, lean_object* v_ik_2983_, lean_object* v_w_2984_){
_start:
{
lean_object* v_res_2985_; 
v_res_2985_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2_spec__3(v_00_u03b1_2973_, v_n_2974_, v_lo_2975_, v_hi_2976_, v_hhi_2977_, v_pivot_2978_, v_as_2979_, v_i_2980_, v_k_2981_, v_ilo_2982_, v_ik_2983_, v_w_2984_);
lean_dec_ref(v_pivot_2978_);
lean_dec(v_hi_2976_);
lean_dec(v_lo_2975_);
lean_dec(v_n_2974_);
return v_res_2985_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3_spec__5(lean_object* v_00_u03b1_2986_, lean_object* v_snd_2987_, lean_object* v_as_2988_, size_t v_i_2989_, size_t v_stop_2990_, lean_object* v_b_2991_){
_start:
{
lean_object* v___x_2992_; 
v___x_2992_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3_spec__5___redArg(v_snd_2987_, v_as_2988_, v_i_2989_, v_stop_2990_, v_b_2991_);
return v___x_2992_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3_spec__5___boxed(lean_object* v_00_u03b1_2993_, lean_object* v_snd_2994_, lean_object* v_as_2995_, lean_object* v_i_2996_, lean_object* v_stop_2997_, lean_object* v_b_2998_){
_start:
{
size_t v_i_boxed_2999_; size_t v_stop_boxed_3000_; lean_object* v_res_3001_; 
v_i_boxed_2999_ = lean_unbox_usize(v_i_2996_);
lean_dec(v_i_2996_);
v_stop_boxed_3000_ = lean_unbox_usize(v_stop_2997_);
lean_dec(v_stop_2997_);
v_res_3001_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3_spec__5(v_00_u03b1_2993_, v_snd_2994_, v_as_2995_, v_i_boxed_2999_, v_stop_boxed_3000_, v_b_2998_);
lean_dec_ref(v_as_2995_);
lean_dec(v_snd_2994_);
return v_res_3001_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParam_x3f___redArg___lam__1(lean_object* v_decl_3002_, lean_object* v___x_3003_, lean_object* v___x_3004_, lean_object* v_a_3005_, lean_object* v_x_3006_, lean_object* v___y_3007_){
_start:
{
lean_object* v_fst_3008_; uint8_t v___x_3009_; 
v_fst_3008_ = lean_ctor_get(v_a_3005_, 0);
v___x_3009_ = lean_name_eq(v_fst_3008_, v_decl_3002_);
if (v___x_3009_ == 0)
{
lean_object* v___x_3010_; 
lean_dec_ref(v_a_3005_);
v___x_3010_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3010_, 0, v___x_3003_);
return v___x_3010_;
}
else
{
lean_object* v___x_3011_; lean_object* v___x_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; 
lean_dec_ref(v___x_3003_);
v___x_3011_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3011_, 0, v_a_3005_);
v___x_3012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3012_, 0, v___x_3011_);
v___x_3013_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3013_, 0, v___x_3012_);
lean_ctor_set(v___x_3013_, 1, v___x_3004_);
v___x_3014_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3014_, 0, v___x_3013_);
return v___x_3014_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParam_x3f___redArg___lam__1___boxed(lean_object* v_decl_3015_, lean_object* v___x_3016_, lean_object* v___x_3017_, lean_object* v_a_3018_, lean_object* v_x_3019_, lean_object* v___y_3020_){
_start:
{
lean_object* v_res_3021_; 
v_res_3021_ = l_Lean_ParametricAttribute_getParam_x3f___redArg___lam__1(v_decl_3015_, v___x_3016_, v___x_3017_, v_a_3018_, v_x_3019_, v___y_3020_);
lean_dec_ref(v___y_3020_);
lean_dec(v_decl_3015_);
return v_res_3021_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParam_x3f___redArg(lean_object* v_inst_3049_, lean_object* v_attr_3050_, lean_object* v_env_3051_, lean_object* v_decl_3052_){
_start:
{
lean_object* v___y_3054_; lean_object* v___x_3065_; lean_object* v___x_3066_; 
v___x_3065_ = ((lean_object*)(l_Lean_ParametricAttribute_getParam_x3f___redArg___closed__0));
v___x_3066_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3051_, v_decl_3052_);
if (lean_obj_tag(v___x_3066_) == 0)
{
lean_object* v_ext_3067_; lean_object* v_toEnvExtension_3068_; lean_object* v_asyncMode_3069_; lean_object* v___x_3070_; lean_object* v___x_3071_; lean_object* v_snd_3072_; lean_object* v___x_3073_; 
lean_dec(v_inst_3049_);
v_ext_3067_ = lean_ctor_get(v_attr_3050_, 1);
v_toEnvExtension_3068_ = lean_ctor_get(v_ext_3067_, 0);
v_asyncMode_3069_ = lean_ctor_get(v_toEnvExtension_3068_, 2);
v___x_3070_ = lean_box(0);
v___x_3071_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3065_, v_ext_3067_, v_env_3051_, v_asyncMode_3069_, v___x_3070_);
v_snd_3072_ = lean_ctor_get(v___x_3071_, 1);
lean_inc(v_snd_3072_);
lean_dec(v___x_3071_);
v___x_3073_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_snd_3072_, v_decl_3052_);
lean_dec(v_decl_3052_);
lean_dec(v_snd_3072_);
return v___x_3073_;
}
else
{
uint8_t v_preserveOrder_3074_; 
v_preserveOrder_3074_ = lean_ctor_get_uint8(v_attr_3050_, sizeof(void*)*2);
if (v_preserveOrder_3074_ == 0)
{
lean_object* v_val_3075_; lean_object* v_ext_3076_; uint8_t v___x_3077_; lean_object* v___x_3078_; lean_object* v___x_3079_; lean_object* v___x_3080_; uint8_t v___x_3081_; 
v_val_3075_ = lean_ctor_get(v___x_3066_, 0);
lean_inc(v_val_3075_);
lean_dec_ref(v___x_3066_);
v_ext_3076_ = lean_ctor_get(v_attr_3050_, 1);
v___x_3077_ = 0;
v___x_3078_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_3065_, v_ext_3076_, v_env_3051_, v_val_3075_, v___x_3077_);
lean_dec(v_val_3075_);
lean_dec_ref(v_env_3051_);
v___x_3079_ = lean_unsigned_to_nat(0u);
v___x_3080_ = lean_array_get_size(v___x_3078_);
v___x_3081_ = lean_nat_dec_lt(v___x_3079_, v___x_3080_);
if (v___x_3081_ == 0)
{
lean_object* v___x_3082_; 
lean_dec_ref(v___x_3078_);
lean_dec(v_decl_3052_);
lean_dec(v_inst_3049_);
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
lean_dec(v_decl_3052_);
lean_dec(v_inst_3049_);
v___x_3086_ = lean_box(0);
return v___x_3086_;
}
else
{
lean_object* v___f_3087_; lean_object* v___x_3088_; lean_object* v___x_3089_; lean_object* v___x_3090_; 
v___f_3087_ = ((lean_object*)(l_Lean_ParametricAttribute_getParam_x3f___redArg___closed__1));
v___x_3088_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3088_, 0, v_decl_3052_);
lean_ctor_set(v___x_3088_, 1, v_inst_3049_);
v___x_3089_ = ((lean_object*)(l_Lean_ParametricAttribute_getParam_x3f___redArg___closed__2));
v___x_3090_ = l_Array_binSearchAux___redArg(v___f_3087_, v___x_3089_, v___x_3078_, v___x_3088_, v___x_3079_, v___x_3084_);
lean_dec_ref(v___x_3078_);
v___y_3054_ = v___x_3090_;
goto v___jp_3053_;
}
}
}
else
{
lean_object* v_val_3091_; lean_object* v_ext_3092_; uint8_t v___x_3093_; lean_object* v___x_3094_; lean_object* v___x_3095_; lean_object* v___x_3096_; lean_object* v___x_3097_; lean_object* v___x_3098_; lean_object* v___f_3099_; size_t v_sz_3100_; size_t v___x_3101_; lean_object* v___x_3102_; lean_object* v_fst_3103_; 
lean_dec(v_inst_3049_);
v_val_3091_ = lean_ctor_get(v___x_3066_, 0);
lean_inc(v_val_3091_);
lean_dec_ref(v___x_3066_);
v_ext_3092_ = lean_ctor_get(v_attr_3050_, 1);
v___x_3093_ = 0;
v___x_3094_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_3065_, v_ext_3092_, v_env_3051_, v_val_3091_, v___x_3093_);
lean_dec(v_val_3091_);
lean_dec_ref(v_env_3051_);
v___x_3095_ = ((lean_object*)(l_Lean_ParametricAttribute_getParam_x3f___redArg___closed__12));
v___x_3096_ = lean_box(0);
v___x_3097_ = lean_box(0);
v___x_3098_ = ((lean_object*)(l_Lean_ParametricAttribute_getParam_x3f___redArg___closed__13));
v___f_3099_ = lean_alloc_closure((void*)(l_Lean_ParametricAttribute_getParam_x3f___redArg___lam__1___boxed), 6, 3);
lean_closure_set(v___f_3099_, 0, v_decl_3052_);
lean_closure_set(v___f_3099_, 1, v___x_3098_);
lean_closure_set(v___f_3099_, 2, v___x_3097_);
v_sz_3100_ = lean_array_size(v___x_3094_);
v___x_3101_ = ((size_t)0ULL);
v___x_3102_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_3095_, v___x_3094_, v___f_3099_, v_sz_3100_, v___x_3101_, v___x_3098_);
v_fst_3103_ = lean_ctor_get(v___x_3102_, 0);
lean_inc(v_fst_3103_);
lean_dec(v___x_3102_);
if (lean_obj_tag(v_fst_3103_) == 0)
{
return v___x_3096_;
}
else
{
lean_object* v_val_3104_; 
v_val_3104_ = lean_ctor_get(v_fst_3103_, 0);
lean_inc(v_val_3104_);
lean_dec_ref(v_fst_3103_);
v___y_3054_ = v_val_3104_;
goto v___jp_3053_;
}
}
}
v___jp_3053_:
{
if (lean_obj_tag(v___y_3054_) == 0)
{
lean_object* v___x_3055_; 
v___x_3055_ = lean_box(0);
return v___x_3055_;
}
else
{
lean_object* v_val_3056_; lean_object* v___x_3058_; uint8_t v_isShared_3059_; uint8_t v_isSharedCheck_3064_; 
v_val_3056_ = lean_ctor_get(v___y_3054_, 0);
v_isSharedCheck_3064_ = !lean_is_exclusive(v___y_3054_);
if (v_isSharedCheck_3064_ == 0)
{
v___x_3058_ = v___y_3054_;
v_isShared_3059_ = v_isSharedCheck_3064_;
goto v_resetjp_3057_;
}
else
{
lean_inc(v_val_3056_);
lean_dec(v___y_3054_);
v___x_3058_ = lean_box(0);
v_isShared_3059_ = v_isSharedCheck_3064_;
goto v_resetjp_3057_;
}
v_resetjp_3057_:
{
lean_object* v_snd_3060_; lean_object* v___x_3062_; 
v_snd_3060_ = lean_ctor_get(v_val_3056_, 1);
lean_inc(v_snd_3060_);
lean_dec(v_val_3056_);
if (v_isShared_3059_ == 0)
{
lean_ctor_set(v___x_3058_, 0, v_snd_3060_);
v___x_3062_ = v___x_3058_;
goto v_reusejp_3061_;
}
else
{
lean_object* v_reuseFailAlloc_3063_; 
v_reuseFailAlloc_3063_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3063_, 0, v_snd_3060_);
v___x_3062_ = v_reuseFailAlloc_3063_;
goto v_reusejp_3061_;
}
v_reusejp_3061_:
{
return v___x_3062_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParam_x3f___redArg___boxed(lean_object* v_inst_3105_, lean_object* v_attr_3106_, lean_object* v_env_3107_, lean_object* v_decl_3108_){
_start:
{
lean_object* v_res_3109_; 
v_res_3109_ = l_Lean_ParametricAttribute_getParam_x3f___redArg(v_inst_3105_, v_attr_3106_, v_env_3107_, v_decl_3108_);
lean_dec_ref(v_attr_3106_);
return v_res_3109_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParam_x3f(lean_object* v_00_u03b1_3110_, lean_object* v_inst_3111_, lean_object* v_attr_3112_, lean_object* v_env_3113_, lean_object* v_decl_3114_){
_start:
{
lean_object* v___x_3115_; 
v___x_3115_ = l_Lean_ParametricAttribute_getParam_x3f___redArg(v_inst_3111_, v_attr_3112_, v_env_3113_, v_decl_3114_);
return v___x_3115_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParam_x3f___boxed(lean_object* v_00_u03b1_3116_, lean_object* v_inst_3117_, lean_object* v_attr_3118_, lean_object* v_env_3119_, lean_object* v_decl_3120_){
_start:
{
lean_object* v_res_3121_; 
v_res_3121_ = l_Lean_ParametricAttribute_getParam_x3f(v_00_u03b1_3116_, v_inst_3117_, v_attr_3118_, v_env_3119_, v_decl_3120_);
lean_dec_ref(v_attr_3118_);
return v_res_3121_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_setParam___redArg(lean_object* v_attr_3126_, lean_object* v_env_3127_, lean_object* v_decl_3128_, lean_object* v_param_3129_){
_start:
{
lean_object* v___x_3130_; 
v___x_3130_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3127_, v_decl_3128_);
if (lean_obj_tag(v___x_3130_) == 0)
{
lean_object* v_ext_3131_; lean_object* v_toEnvExtension_3132_; lean_object* v_attr_3133_; lean_object* v_asyncMode_3134_; lean_object* v___x_3135_; lean_object* v___x_3136_; lean_object* v___x_3137_; lean_object* v_snd_3138_; lean_object* v___x_3140_; uint8_t v_isShared_3141_; uint8_t v_isSharedCheck_3168_; 
v_ext_3131_ = lean_ctor_get(v_attr_3126_, 1);
lean_inc_ref(v_ext_3131_);
v_toEnvExtension_3132_ = lean_ctor_get(v_ext_3131_, 0);
v_attr_3133_ = lean_ctor_get(v_attr_3126_, 0);
lean_inc_ref(v_attr_3133_);
lean_dec_ref(v_attr_3126_);
v_asyncMode_3134_ = lean_ctor_get(v_toEnvExtension_3132_, 2);
lean_inc(v_asyncMode_3134_);
v___x_3135_ = ((lean_object*)(l_Lean_ParametricAttribute_getParam_x3f___redArg___closed__0));
v___x_3136_ = lean_box(0);
lean_inc_ref(v_env_3127_);
v___x_3137_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3135_, v_ext_3131_, v_env_3127_, v_asyncMode_3134_, v___x_3136_);
v_snd_3138_ = lean_ctor_get(v___x_3137_, 1);
v_isSharedCheck_3168_ = !lean_is_exclusive(v___x_3137_);
if (v_isSharedCheck_3168_ == 0)
{
lean_object* v_unused_3169_; 
v_unused_3169_ = lean_ctor_get(v___x_3137_, 0);
lean_dec(v_unused_3169_);
v___x_3140_ = v___x_3137_;
v_isShared_3141_ = v_isSharedCheck_3168_;
goto v_resetjp_3139_;
}
else
{
lean_inc(v_snd_3138_);
lean_dec(v___x_3137_);
v___x_3140_ = lean_box(0);
v_isShared_3141_ = v_isSharedCheck_3168_;
goto v_resetjp_3139_;
}
v_resetjp_3139_:
{
lean_object* v___x_3142_; 
v___x_3142_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_snd_3138_, v_decl_3128_);
lean_dec(v_snd_3138_);
if (lean_obj_tag(v___x_3142_) == 0)
{
lean_object* v___x_3144_; 
lean_dec_ref(v_attr_3133_);
if (v_isShared_3141_ == 0)
{
lean_ctor_set(v___x_3140_, 1, v_param_3129_);
lean_ctor_set(v___x_3140_, 0, v_decl_3128_);
v___x_3144_ = v___x_3140_;
goto v_reusejp_3143_;
}
else
{
lean_object* v_reuseFailAlloc_3147_; 
v_reuseFailAlloc_3147_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3147_, 0, v_decl_3128_);
lean_ctor_set(v_reuseFailAlloc_3147_, 1, v_param_3129_);
v___x_3144_ = v_reuseFailAlloc_3147_;
goto v_reusejp_3143_;
}
v_reusejp_3143_:
{
lean_object* v___x_3145_; lean_object* v___x_3146_; 
v___x_3145_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_ext_3131_, v_env_3127_, v___x_3144_, v_asyncMode_3134_, v___x_3136_);
lean_dec(v_asyncMode_3134_);
v___x_3146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3146_, 0, v___x_3145_);
return v___x_3146_;
}
}
else
{
lean_object* v___x_3149_; uint8_t v_isShared_3150_; uint8_t v_isSharedCheck_3166_; 
lean_del_object(v___x_3140_);
lean_dec(v_asyncMode_3134_);
lean_dec_ref(v_ext_3131_);
lean_dec(v_param_3129_);
lean_dec_ref(v_env_3127_);
v_isSharedCheck_3166_ = !lean_is_exclusive(v___x_3142_);
if (v_isSharedCheck_3166_ == 0)
{
lean_object* v_unused_3167_; 
v_unused_3167_ = lean_ctor_get(v___x_3142_, 0);
lean_dec(v_unused_3167_);
v___x_3149_ = v___x_3142_;
v_isShared_3150_ = v_isSharedCheck_3166_;
goto v_resetjp_3148_;
}
else
{
lean_dec(v___x_3142_);
v___x_3149_ = lean_box(0);
v_isShared_3150_ = v_isSharedCheck_3166_;
goto v_resetjp_3148_;
}
v_resetjp_3148_:
{
lean_object* v_toAttributeImplCore_3151_; lean_object* v_name_3152_; uint8_t v___x_3153_; lean_object* v___x_3154_; lean_object* v___x_3155_; lean_object* v___x_3156_; lean_object* v___x_3157_; lean_object* v___x_3158_; lean_object* v___x_3159_; lean_object* v___x_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; lean_object* v___x_3164_; 
v_toAttributeImplCore_3151_ = lean_ctor_get(v_attr_3133_, 0);
lean_inc_ref(v_toAttributeImplCore_3151_);
lean_dec_ref(v_attr_3133_);
v_name_3152_ = lean_ctor_get(v_toAttributeImplCore_3151_, 1);
lean_inc(v_name_3152_);
lean_dec_ref(v_toAttributeImplCore_3151_);
v___x_3153_ = 1;
v___x_3154_ = ((lean_object*)(l_Lean_ParametricAttribute_setParam___redArg___closed__0));
v___x_3155_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_3152_, v___x_3153_);
v___x_3156_ = lean_string_append(v___x_3154_, v___x_3155_);
lean_dec_ref(v___x_3155_);
v___x_3157_ = ((lean_object*)(l_Lean_ParametricAttribute_setParam___redArg___closed__1));
v___x_3158_ = lean_string_append(v___x_3156_, v___x_3157_);
v___x_3159_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_decl_3128_, v___x_3153_);
v___x_3160_ = lean_string_append(v___x_3158_, v___x_3159_);
lean_dec_ref(v___x_3159_);
v___x_3161_ = ((lean_object*)(l_Lean_ParametricAttribute_setParam___redArg___closed__2));
v___x_3162_ = lean_string_append(v___x_3160_, v___x_3161_);
if (v_isShared_3150_ == 0)
{
lean_ctor_set_tag(v___x_3149_, 0);
lean_ctor_set(v___x_3149_, 0, v___x_3162_);
v___x_3164_ = v___x_3149_;
goto v_reusejp_3163_;
}
else
{
lean_object* v_reuseFailAlloc_3165_; 
v_reuseFailAlloc_3165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3165_, 0, v___x_3162_);
v___x_3164_ = v_reuseFailAlloc_3165_;
goto v_reusejp_3163_;
}
v_reusejp_3163_:
{
return v___x_3164_;
}
}
}
}
}
else
{
lean_object* v___x_3171_; uint8_t v_isShared_3172_; uint8_t v_isSharedCheck_3189_; 
lean_dec(v_param_3129_);
lean_dec_ref(v_env_3127_);
v_isSharedCheck_3189_ = !lean_is_exclusive(v___x_3130_);
if (v_isSharedCheck_3189_ == 0)
{
lean_object* v_unused_3190_; 
v_unused_3190_ = lean_ctor_get(v___x_3130_, 0);
lean_dec(v_unused_3190_);
v___x_3171_ = v___x_3130_;
v_isShared_3172_ = v_isSharedCheck_3189_;
goto v_resetjp_3170_;
}
else
{
lean_dec(v___x_3130_);
v___x_3171_ = lean_box(0);
v_isShared_3172_ = v_isSharedCheck_3189_;
goto v_resetjp_3170_;
}
v_resetjp_3170_:
{
lean_object* v_attr_3173_; lean_object* v_toAttributeImplCore_3174_; lean_object* v_name_3175_; uint8_t v___x_3176_; lean_object* v___x_3177_; lean_object* v___x_3178_; lean_object* v___x_3179_; lean_object* v___x_3180_; lean_object* v___x_3181_; lean_object* v___x_3182_; lean_object* v___x_3183_; lean_object* v___x_3184_; lean_object* v___x_3185_; lean_object* v___x_3187_; 
v_attr_3173_ = lean_ctor_get(v_attr_3126_, 0);
lean_inc_ref(v_attr_3173_);
lean_dec_ref(v_attr_3126_);
v_toAttributeImplCore_3174_ = lean_ctor_get(v_attr_3173_, 0);
lean_inc_ref(v_toAttributeImplCore_3174_);
lean_dec_ref(v_attr_3173_);
v_name_3175_ = lean_ctor_get(v_toAttributeImplCore_3174_, 1);
lean_inc(v_name_3175_);
lean_dec_ref(v_toAttributeImplCore_3174_);
v___x_3176_ = 1;
v___x_3177_ = ((lean_object*)(l_Lean_ParametricAttribute_setParam___redArg___closed__0));
v___x_3178_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_3175_, v___x_3176_);
v___x_3179_ = lean_string_append(v___x_3177_, v___x_3178_);
lean_dec_ref(v___x_3178_);
v___x_3180_ = ((lean_object*)(l_Lean_ParametricAttribute_setParam___redArg___closed__1));
v___x_3181_ = lean_string_append(v___x_3179_, v___x_3180_);
v___x_3182_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_decl_3128_, v___x_3176_);
v___x_3183_ = lean_string_append(v___x_3181_, v___x_3182_);
lean_dec_ref(v___x_3182_);
v___x_3184_ = ((lean_object*)(l_Lean_ParametricAttribute_setParam___redArg___closed__3));
v___x_3185_ = lean_string_append(v___x_3183_, v___x_3184_);
if (v_isShared_3172_ == 0)
{
lean_ctor_set_tag(v___x_3171_, 0);
lean_ctor_set(v___x_3171_, 0, v___x_3185_);
v___x_3187_ = v___x_3171_;
goto v_reusejp_3186_;
}
else
{
lean_object* v_reuseFailAlloc_3188_; 
v_reuseFailAlloc_3188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3188_, 0, v___x_3185_);
v___x_3187_ = v_reuseFailAlloc_3188_;
goto v_reusejp_3186_;
}
v_reusejp_3186_:
{
return v___x_3187_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_setParam(lean_object* v_00_u03b1_3191_, lean_object* v_attr_3192_, lean_object* v_env_3193_, lean_object* v_decl_3194_, lean_object* v_param_3195_){
_start:
{
lean_object* v___x_3196_; 
v___x_3196_ = l_Lean_ParametricAttribute_setParam___redArg(v_attr_3192_, v_env_3193_, v_decl_3194_, v_param_3195_);
return v___x_3196_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___lam__0(lean_object* v_x_3197_, lean_object* v___y_3198_){
_start:
{
lean_object* v___x_3200_; lean_object* v___x_3201_; 
v___x_3200_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___lam__0___closed__1));
v___x_3201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3201_, 0, v___x_3200_);
return v___x_3201_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___lam__0___boxed(lean_object* v_x_3202_, lean_object* v___y_3203_, lean_object* v___y_3204_){
_start:
{
lean_object* v_res_3205_; 
v_res_3205_ = l_Lean_instInhabitedEnumAttributes_default___lam__0(v_x_3202_, v___y_3203_);
lean_dec_ref(v___y_3203_);
lean_dec_ref(v_x_3202_);
return v_res_3205_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___lam__1(lean_object* v_s_3206_, lean_object* v_x_3207_){
_start:
{
lean_inc(v_s_3206_);
return v_s_3206_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___lam__1___boxed(lean_object* v_s_3208_, lean_object* v_x_3209_){
_start:
{
lean_object* v_res_3210_; 
v_res_3210_ = l_Lean_instInhabitedEnumAttributes_default___lam__1(v_s_3208_, v_x_3209_);
lean_dec_ref(v_x_3209_);
lean_dec(v_s_3208_);
return v_res_3210_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___lam__2(lean_object* v_x_3211_, lean_object* v_x_3212_){
_start:
{
lean_object* v___x_3213_; 
v___x_3213_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___lam__2___closed__1));
return v___x_3213_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___lam__2___boxed(lean_object* v_x_3214_, lean_object* v_x_3215_){
_start:
{
lean_object* v_res_3216_; 
v_res_3216_ = l_Lean_instInhabitedEnumAttributes_default___lam__2(v_x_3214_, v_x_3215_);
lean_dec(v_x_3215_);
lean_dec_ref(v_x_3214_);
return v_res_3216_;
}
}
static lean_object* _init_l_Lean_instInhabitedEnumAttributes_default___closed__3(void){
_start:
{
lean_object* v___x_3220_; 
v___x_3220_ = l_Lean_instInhabitedEnvExtension_default(lean_box(0));
return v___x_3220_;
}
}
static lean_object* _init_l_Lean_instInhabitedEnumAttributes_default___closed__4(void){
_start:
{
lean_object* v___f_3221_; lean_object* v___f_3222_; lean_object* v___f_3223_; lean_object* v___f_3224_; lean_object* v___x_3225_; lean_object* v___x_3226_; lean_object* v___x_3227_; 
v___f_3221_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___closed__3));
v___f_3222_ = ((lean_object*)(l_Lean_instInhabitedEnumAttributes_default___closed__2));
v___f_3223_ = ((lean_object*)(l_Lean_instInhabitedEnumAttributes_default___closed__1));
v___f_3224_ = ((lean_object*)(l_Lean_instInhabitedEnumAttributes_default___closed__0));
v___x_3225_ = lean_box(0);
v___x_3226_ = lean_obj_once(&l_Lean_instInhabitedEnumAttributes_default___closed__3, &l_Lean_instInhabitedEnumAttributes_default___closed__3_once, _init_l_Lean_instInhabitedEnumAttributes_default___closed__3);
v___x_3227_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3227_, 0, v___x_3226_);
lean_ctor_set(v___x_3227_, 1, v___x_3225_);
lean_ctor_set(v___x_3227_, 2, v___f_3224_);
lean_ctor_set(v___x_3227_, 3, v___f_3223_);
lean_ctor_set(v___x_3227_, 4, v___f_3222_);
lean_ctor_set(v___x_3227_, 5, v___f_3221_);
return v___x_3227_;
}
}
static lean_object* _init_l_Lean_instInhabitedEnumAttributes_default___closed__5(void){
_start:
{
lean_object* v___x_3228_; lean_object* v___x_3229_; lean_object* v___x_3230_; 
v___x_3228_ = lean_obj_once(&l_Lean_instInhabitedEnumAttributes_default___closed__4, &l_Lean_instInhabitedEnumAttributes_default___closed__4_once, _init_l_Lean_instInhabitedEnumAttributes_default___closed__4);
v___x_3229_ = lean_box(0);
v___x_3230_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3230_, 0, v___x_3229_);
lean_ctor_set(v___x_3230_, 1, v___x_3228_);
return v___x_3230_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default(lean_object* v_00_u03b1_3231_){
_start:
{
lean_object* v___x_3232_; 
v___x_3232_ = lean_obj_once(&l_Lean_instInhabitedEnumAttributes_default___closed__5, &l_Lean_instInhabitedEnumAttributes_default___closed__5_once, _init_l_Lean_instInhabitedEnumAttributes_default___closed__5);
return v___x_3232_;
}
}
static lean_object* _init_l_Lean_instInhabitedEnumAttributes___closed__0(void){
_start:
{
lean_object* v___x_3233_; 
v___x_3233_ = l_Lean_instInhabitedEnumAttributes_default(lean_box(0));
return v___x_3233_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes(lean_object* v_a_3234_){
_start:
{
lean_object* v___x_3235_; 
v___x_3235_ = lean_obj_once(&l_Lean_instInhabitedEnumAttributes___closed__0, &l_Lean_instInhabitedEnumAttributes___closed__0_once, _init_l_Lean_instInhabitedEnumAttributes___closed__0);
return v___x_3235_;
}
}
static lean_object* _init_l_Lean_registerEnumAttributes___auto__1(void){
_start:
{
lean_object* v___x_3236_; 
v___x_3236_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__28, &l_Lean_AttributeImplCore_ref___autoParam___closed__28_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__28);
return v___x_3236_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__0(lean_object* v_x_3237_){
_start:
{
lean_object* v___x_3238_; 
v___x_3238_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___lam__2___closed__0));
return v___x_3238_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__0___boxed(lean_object* v_x_3239_){
_start:
{
lean_object* v_res_3240_; 
v_res_3240_ = l_Lean_registerEnumAttributes___redArg___lam__0(v_x_3239_);
lean_dec(v_x_3239_);
return v_res_3240_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___redArg(lean_object* v_newState_3241_, lean_object* v_x_3242_, lean_object* v_x_3243_){
_start:
{
if (lean_obj_tag(v_x_3243_) == 0)
{
return v_x_3242_;
}
else
{
lean_object* v_head_3244_; lean_object* v_tail_3245_; lean_object* v___x_3246_; 
v_head_3244_ = lean_ctor_get(v_x_3243_, 0);
lean_inc(v_head_3244_);
v_tail_3245_ = lean_ctor_get(v_x_3243_, 1);
lean_inc(v_tail_3245_);
lean_dec_ref(v_x_3243_);
v___x_3246_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_newState_3241_, v_head_3244_);
if (lean_obj_tag(v___x_3246_) == 1)
{
lean_object* v_val_3247_; lean_object* v___x_3248_; 
v_val_3247_ = lean_ctor_get(v___x_3246_, 0);
lean_inc(v_val_3247_);
lean_dec_ref(v___x_3246_);
v___x_3248_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_head_3244_, v_val_3247_, v_x_3242_);
v_x_3242_ = v___x_3248_;
v_x_3243_ = v_tail_3245_;
goto _start;
}
else
{
lean_dec(v___x_3246_);
lean_dec(v_head_3244_);
v_x_3243_ = v_tail_3245_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___redArg___boxed(lean_object* v_newState_3251_, lean_object* v_x_3252_, lean_object* v_x_3253_){
_start:
{
lean_object* v_res_3254_; 
v_res_3254_ = l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___redArg(v_newState_3251_, v_x_3252_, v_x_3253_);
lean_dec(v_newState_3251_);
return v_res_3254_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__1(lean_object* v_x_3255_, lean_object* v_newState_3256_, lean_object* v_consts_3257_, lean_object* v_st_3258_){
_start:
{
lean_object* v___x_3259_; 
v___x_3259_ = l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___redArg(v_newState_3256_, v_st_3258_, v_consts_3257_);
return v___x_3259_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__1___boxed(lean_object* v_x_3260_, lean_object* v_newState_3261_, lean_object* v_consts_3262_, lean_object* v_st_3263_){
_start:
{
lean_object* v_res_3264_; 
v_res_3264_ = l_Lean_registerEnumAttributes___redArg___lam__1(v_x_3260_, v_newState_3261_, v_consts_3262_, v_st_3263_);
lean_dec(v_newState_3261_);
lean_dec(v_x_3260_);
return v_res_3264_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__2(lean_object* v_s_3274_){
_start:
{
lean_object* v___x_3275_; lean_object* v___y_3277_; 
v___x_3275_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___lam__2___closed__3));
if (lean_obj_tag(v_s_3274_) == 0)
{
lean_object* v_size_3281_; 
v_size_3281_ = lean_ctor_get(v_s_3274_, 0);
lean_inc(v_size_3281_);
lean_dec_ref(v_s_3274_);
v___y_3277_ = v_size_3281_;
goto v___jp_3276_;
}
else
{
lean_object* v___x_3282_; 
v___x_3282_ = lean_unsigned_to_nat(0u);
v___y_3277_ = v___x_3282_;
goto v___jp_3276_;
}
v___jp_3276_:
{
lean_object* v___x_3278_; lean_object* v___x_3279_; lean_object* v___x_3280_; 
v___x_3278_ = l_Nat_reprFast(v___y_3277_);
v___x_3279_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3279_, 0, v___x_3278_);
v___x_3280_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3280_, 0, v___x_3275_);
lean_ctor_set(v___x_3280_, 1, v___x_3279_);
return v___x_3280_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg(lean_object* v_env_3283_, lean_object* v_as_3284_, size_t v_i_3285_, size_t v_stop_3286_, lean_object* v_b_3287_){
_start:
{
lean_object* v___y_3289_; uint8_t v___x_3293_; 
v___x_3293_ = lean_usize_dec_eq(v_i_3285_, v_stop_3286_);
if (v___x_3293_ == 0)
{
lean_object* v___x_3294_; lean_object* v_fst_3295_; uint8_t v___x_3296_; lean_object* v___x_3297_; uint8_t v___x_3298_; 
v___x_3294_ = lean_array_uget_borrowed(v_as_3284_, v_i_3285_);
v_fst_3295_ = lean_ctor_get(v___x_3294_, 0);
v___x_3296_ = 1;
lean_inc_ref(v_env_3283_);
v___x_3297_ = l_Lean_Environment_setExporting(v_env_3283_, v___x_3296_);
lean_inc(v_fst_3295_);
v___x_3298_ = l_Lean_Environment_contains(v___x_3297_, v_fst_3295_, v___x_3293_);
if (v___x_3298_ == 0)
{
v___y_3289_ = v_b_3287_;
goto v___jp_3288_;
}
else
{
lean_object* v___x_3299_; 
lean_inc(v___x_3294_);
v___x_3299_ = lean_array_push(v_b_3287_, v___x_3294_);
v___y_3289_ = v___x_3299_;
goto v___jp_3288_;
}
}
else
{
lean_dec_ref(v_env_3283_);
return v_b_3287_;
}
v___jp_3288_:
{
size_t v___x_3290_; size_t v___x_3291_; 
v___x_3290_ = ((size_t)1ULL);
v___x_3291_ = lean_usize_add(v_i_3285_, v___x_3290_);
v_i_3285_ = v___x_3291_;
v_b_3287_ = v___y_3289_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg___boxed(lean_object* v_env_3300_, lean_object* v_as_3301_, lean_object* v_i_3302_, lean_object* v_stop_3303_, lean_object* v_b_3304_){
_start:
{
size_t v_i_boxed_3305_; size_t v_stop_boxed_3306_; lean_object* v_res_3307_; 
v_i_boxed_3305_ = lean_unbox_usize(v_i_3302_);
lean_dec(v_i_3302_);
v_stop_boxed_3306_ = lean_unbox_usize(v_stop_3303_);
lean_dec(v_stop_3303_);
v_res_3307_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg(v_env_3300_, v_as_3301_, v_i_boxed_3305_, v_stop_boxed_3306_, v_b_3304_);
lean_dec_ref(v_as_3301_);
return v_res_3307_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__3(lean_object* v_env_3308_, lean_object* v_m_3309_){
_start:
{
lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v___y_3313_; lean_object* v___x_3327_; lean_object* v___x_3328_; lean_object* v___y_3330_; lean_object* v___y_3331_; uint8_t v___x_3333_; 
v___x_3310_ = lean_unsigned_to_nat(0u);
v___x_3311_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___lam__2___closed__0));
v___x_3327_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1_spec__1___redArg(v___x_3311_, v_m_3309_);
v___x_3328_ = lean_array_get_size(v___x_3327_);
v___x_3333_ = lean_nat_dec_eq(v___x_3328_, v___x_3310_);
if (v___x_3333_ == 0)
{
lean_object* v___x_3334_; lean_object* v___x_3335_; lean_object* v___y_3337_; uint8_t v___x_3339_; 
v___x_3334_ = lean_unsigned_to_nat(1u);
v___x_3335_ = lean_nat_sub(v___x_3328_, v___x_3334_);
v___x_3339_ = lean_nat_dec_le(v___x_3310_, v___x_3335_);
if (v___x_3339_ == 0)
{
lean_inc(v___x_3335_);
v___y_3337_ = v___x_3335_;
goto v___jp_3336_;
}
else
{
v___y_3337_ = v___x_3310_;
goto v___jp_3336_;
}
v___jp_3336_:
{
uint8_t v___x_3338_; 
v___x_3338_ = lean_nat_dec_le(v___y_3337_, v___x_3335_);
if (v___x_3338_ == 0)
{
lean_dec(v___x_3335_);
lean_inc(v___y_3337_);
v___y_3330_ = v___y_3337_;
v___y_3331_ = v___y_3337_;
goto v___jp_3329_;
}
else
{
v___y_3330_ = v___y_3337_;
v___y_3331_ = v___x_3335_;
goto v___jp_3329_;
}
}
}
else
{
v___y_3313_ = v___x_3327_;
goto v___jp_3312_;
}
v___jp_3312_:
{
lean_object* v___x_3314_; uint8_t v___x_3315_; 
v___x_3314_ = lean_array_get_size(v___y_3313_);
v___x_3315_ = lean_nat_dec_lt(v___x_3310_, v___x_3314_);
if (v___x_3315_ == 0)
{
lean_object* v___x_3316_; 
lean_dec_ref(v_env_3308_);
v___x_3316_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3316_, 0, v___x_3311_);
lean_ctor_set(v___x_3316_, 1, v___x_3311_);
lean_ctor_set(v___x_3316_, 2, v___y_3313_);
return v___x_3316_;
}
else
{
uint8_t v___x_3317_; 
v___x_3317_ = lean_nat_dec_le(v___x_3314_, v___x_3314_);
if (v___x_3317_ == 0)
{
if (v___x_3315_ == 0)
{
lean_object* v___x_3318_; 
lean_dec_ref(v_env_3308_);
v___x_3318_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3318_, 0, v___x_3311_);
lean_ctor_set(v___x_3318_, 1, v___x_3311_);
lean_ctor_set(v___x_3318_, 2, v___y_3313_);
return v___x_3318_;
}
else
{
size_t v___x_3319_; size_t v___x_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; 
v___x_3319_ = ((size_t)0ULL);
v___x_3320_ = lean_usize_of_nat(v___x_3314_);
v___x_3321_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg(v_env_3308_, v___y_3313_, v___x_3319_, v___x_3320_, v___x_3311_);
lean_inc_ref(v___x_3321_);
v___x_3322_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3322_, 0, v___x_3321_);
lean_ctor_set(v___x_3322_, 1, v___x_3321_);
lean_ctor_set(v___x_3322_, 2, v___y_3313_);
return v___x_3322_;
}
}
else
{
size_t v___x_3323_; size_t v___x_3324_; lean_object* v___x_3325_; lean_object* v___x_3326_; 
v___x_3323_ = ((size_t)0ULL);
v___x_3324_ = lean_usize_of_nat(v___x_3314_);
v___x_3325_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg(v_env_3308_, v___y_3313_, v___x_3323_, v___x_3324_, v___x_3311_);
lean_inc_ref(v___x_3325_);
v___x_3326_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3326_, 0, v___x_3325_);
lean_ctor_set(v___x_3326_, 1, v___x_3325_);
lean_ctor_set(v___x_3326_, 2, v___y_3313_);
return v___x_3326_;
}
}
}
v___jp_3329_:
{
lean_object* v___x_3332_; 
v___x_3332_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2___redArg(v___x_3328_, v___x_3327_, v___y_3330_, v___y_3331_);
lean_dec(v___y_3331_);
v___y_3313_ = v___x_3332_;
goto v___jp_3312_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__3___boxed(lean_object* v_env_3340_, lean_object* v_m_3341_){
_start:
{
lean_object* v_res_3342_; 
v_res_3342_ = l_Lean_registerEnumAttributes___redArg___lam__3(v_env_3340_, v_m_3341_);
lean_dec(v_m_3341_);
return v_res_3342_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__4(lean_object* v_s_3343_, lean_object* v_p_3344_){
_start:
{
lean_object* v_fst_3345_; lean_object* v_snd_3346_; lean_object* v___x_3347_; 
v_fst_3345_ = lean_ctor_get(v_p_3344_, 0);
lean_inc(v_fst_3345_);
v_snd_3346_ = lean_ctor_get(v_p_3344_, 1);
lean_inc(v_snd_3346_);
lean_dec_ref(v_p_3344_);
v___x_3347_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_3345_, v_snd_3346_, v_s_3343_);
return v___x_3347_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__6(lean_object* v___x_3348_, lean_object* v_x_3349_, lean_object* v_x_3350_){
_start:
{
lean_object* v___x_3352_; 
v___x_3352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3352_, 0, v___x_3348_);
return v___x_3352_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__6___boxed(lean_object* v___x_3353_, lean_object* v_x_3354_, lean_object* v_x_3355_, lean_object* v___y_3356_){
_start:
{
lean_object* v_res_3357_; 
v_res_3357_ = l_Lean_registerEnumAttributes___redArg___lam__6(v___x_3353_, v_x_3354_, v_x_3355_);
lean_dec_ref(v_x_3355_);
lean_dec_ref(v_x_3354_);
return v_res_3357_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_registerEnumAttributes_spec__3(lean_object* v_as_3358_){
_start:
{
if (lean_obj_tag(v_as_3358_) == 0)
{
lean_object* v___x_3360_; lean_object* v___x_3361_; 
v___x_3360_ = lean_box(0);
v___x_3361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3361_, 0, v___x_3360_);
return v___x_3361_;
}
else
{
lean_object* v_head_3362_; lean_object* v_tail_3363_; lean_object* v___x_3364_; 
v_head_3362_ = lean_ctor_get(v_as_3358_, 0);
lean_inc(v_head_3362_);
v_tail_3363_ = lean_ctor_get(v_as_3358_, 1);
lean_inc(v_tail_3363_);
lean_dec_ref(v_as_3358_);
v___x_3364_ = l_Lean_registerBuiltinAttribute(v_head_3362_);
if (lean_obj_tag(v___x_3364_) == 0)
{
lean_dec_ref(v___x_3364_);
v_as_3358_ = v_tail_3363_;
goto _start;
}
else
{
lean_dec(v_tail_3363_);
return v___x_3364_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_registerEnumAttributes_spec__3___boxed(lean_object* v_as_3366_, lean_object* v___y_3367_){
_start:
{
lean_object* v_res_3368_; 
v_res_3368_ = l_List_forM___at___00Lean_registerEnumAttributes_spec__3(v_as_3366_);
return v_res_3368_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__1(lean_object* v_validate_3369_, lean_object* v_snd_3370_, lean_object* v_a_3371_, lean_object* v_fst_3372_, lean_object* v_decl_3373_, lean_object* v_stx_3374_, uint8_t v_kind_3375_, lean_object* v___y_3376_, lean_object* v___y_3377_){
_start:
{
lean_object* v___y_3380_; lean_object* v___y_3381_; lean_object* v___y_3416_; lean_object* v___y_3417_; lean_object* v___x_3422_; 
v___x_3422_ = l_Lean_Attribute_Builtin_ensureNoArgs(v_stx_3374_, v___y_3376_, v___y_3377_);
if (lean_obj_tag(v___x_3422_) == 0)
{
uint8_t v___x_3423_; uint8_t v___x_3424_; 
lean_dec_ref(v___x_3422_);
v___x_3423_ = 0;
v___x_3424_ = l_Lean_instBEqAttributeKind_beq(v_kind_3375_, v___x_3423_);
if (v___x_3424_ == 0)
{
lean_object* v___x_3425_; 
lean_dec(v_decl_3373_);
lean_dec_ref(v_a_3371_);
lean_dec(v_snd_3370_);
lean_dec_ref(v_validate_3369_);
v___x_3425_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg(v_fst_3372_, v_kind_3375_, v___y_3376_, v___y_3377_);
return v___x_3425_;
}
else
{
v___y_3416_ = v___y_3376_;
v___y_3417_ = v___y_3377_;
goto v___jp_3415_;
}
}
else
{
lean_dec(v_decl_3373_);
lean_dec(v_fst_3372_);
lean_dec_ref(v_a_3371_);
lean_dec(v_snd_3370_);
lean_dec_ref(v_validate_3369_);
return v___x_3422_;
}
v___jp_3379_:
{
lean_object* v___x_3382_; 
lean_inc(v___y_3381_);
lean_inc_ref(v___y_3380_);
lean_inc(v_snd_3370_);
lean_inc(v_decl_3373_);
v___x_3382_ = lean_apply_5(v_validate_3369_, v_decl_3373_, v_snd_3370_, v___y_3380_, v___y_3381_, lean_box(0));
if (lean_obj_tag(v___x_3382_) == 0)
{
lean_object* v___x_3384_; uint8_t v_isShared_3385_; uint8_t v_isSharedCheck_3413_; 
v_isSharedCheck_3413_ = !lean_is_exclusive(v___x_3382_);
if (v_isSharedCheck_3413_ == 0)
{
lean_object* v_unused_3414_; 
v_unused_3414_ = lean_ctor_get(v___x_3382_, 0);
lean_dec(v_unused_3414_);
v___x_3384_ = v___x_3382_;
v_isShared_3385_ = v_isSharedCheck_3413_;
goto v_resetjp_3383_;
}
else
{
lean_dec(v___x_3382_);
v___x_3384_ = lean_box(0);
v_isShared_3385_ = v_isSharedCheck_3413_;
goto v_resetjp_3383_;
}
v_resetjp_3383_:
{
lean_object* v___x_3386_; lean_object* v_toEnvExtension_3387_; lean_object* v_env_3388_; lean_object* v_nextMacroScope_3389_; lean_object* v_ngen_3390_; lean_object* v_auxDeclNGen_3391_; lean_object* v_traceState_3392_; lean_object* v_messages_3393_; lean_object* v_infoState_3394_; lean_object* v_snapshotTasks_3395_; lean_object* v___x_3397_; uint8_t v_isShared_3398_; uint8_t v_isSharedCheck_3411_; 
v___x_3386_ = lean_st_ref_take(v___y_3381_);
v_toEnvExtension_3387_ = lean_ctor_get(v_a_3371_, 0);
v_env_3388_ = lean_ctor_get(v___x_3386_, 0);
v_nextMacroScope_3389_ = lean_ctor_get(v___x_3386_, 1);
v_ngen_3390_ = lean_ctor_get(v___x_3386_, 2);
v_auxDeclNGen_3391_ = lean_ctor_get(v___x_3386_, 3);
v_traceState_3392_ = lean_ctor_get(v___x_3386_, 4);
v_messages_3393_ = lean_ctor_get(v___x_3386_, 6);
v_infoState_3394_ = lean_ctor_get(v___x_3386_, 7);
v_snapshotTasks_3395_ = lean_ctor_get(v___x_3386_, 8);
v_isSharedCheck_3411_ = !lean_is_exclusive(v___x_3386_);
if (v_isSharedCheck_3411_ == 0)
{
lean_object* v_unused_3412_; 
v_unused_3412_ = lean_ctor_get(v___x_3386_, 5);
lean_dec(v_unused_3412_);
v___x_3397_ = v___x_3386_;
v_isShared_3398_ = v_isSharedCheck_3411_;
goto v_resetjp_3396_;
}
else
{
lean_inc(v_snapshotTasks_3395_);
lean_inc(v_infoState_3394_);
lean_inc(v_messages_3393_);
lean_inc(v_traceState_3392_);
lean_inc(v_auxDeclNGen_3391_);
lean_inc(v_ngen_3390_);
lean_inc(v_nextMacroScope_3389_);
lean_inc(v_env_3388_);
lean_dec(v___x_3386_);
v___x_3397_ = lean_box(0);
v_isShared_3398_ = v_isSharedCheck_3411_;
goto v_resetjp_3396_;
}
v_resetjp_3396_:
{
lean_object* v_asyncMode_3399_; lean_object* v___x_3400_; lean_object* v___x_3401_; lean_object* v___x_3402_; lean_object* v___x_3404_; 
v_asyncMode_3399_ = lean_ctor_get(v_toEnvExtension_3387_, 2);
lean_inc(v_asyncMode_3399_);
lean_inc(v_decl_3373_);
v___x_3400_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3400_, 0, v_decl_3373_);
lean_ctor_set(v___x_3400_, 1, v_snd_3370_);
v___x_3401_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_a_3371_, v_env_3388_, v___x_3400_, v_asyncMode_3399_, v_decl_3373_);
lean_dec(v_asyncMode_3399_);
v___x_3402_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2);
if (v_isShared_3398_ == 0)
{
lean_ctor_set(v___x_3397_, 5, v___x_3402_);
lean_ctor_set(v___x_3397_, 0, v___x_3401_);
v___x_3404_ = v___x_3397_;
goto v_reusejp_3403_;
}
else
{
lean_object* v_reuseFailAlloc_3410_; 
v_reuseFailAlloc_3410_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3410_, 0, v___x_3401_);
lean_ctor_set(v_reuseFailAlloc_3410_, 1, v_nextMacroScope_3389_);
lean_ctor_set(v_reuseFailAlloc_3410_, 2, v_ngen_3390_);
lean_ctor_set(v_reuseFailAlloc_3410_, 3, v_auxDeclNGen_3391_);
lean_ctor_set(v_reuseFailAlloc_3410_, 4, v_traceState_3392_);
lean_ctor_set(v_reuseFailAlloc_3410_, 5, v___x_3402_);
lean_ctor_set(v_reuseFailAlloc_3410_, 6, v_messages_3393_);
lean_ctor_set(v_reuseFailAlloc_3410_, 7, v_infoState_3394_);
lean_ctor_set(v_reuseFailAlloc_3410_, 8, v_snapshotTasks_3395_);
v___x_3404_ = v_reuseFailAlloc_3410_;
goto v_reusejp_3403_;
}
v_reusejp_3403_:
{
lean_object* v___x_3405_; lean_object* v___x_3406_; lean_object* v___x_3408_; 
v___x_3405_ = lean_st_ref_set(v___y_3381_, v___x_3404_);
v___x_3406_ = lean_box(0);
if (v_isShared_3385_ == 0)
{
lean_ctor_set(v___x_3384_, 0, v___x_3406_);
v___x_3408_ = v___x_3384_;
goto v_reusejp_3407_;
}
else
{
lean_object* v_reuseFailAlloc_3409_; 
v_reuseFailAlloc_3409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3409_, 0, v___x_3406_);
v___x_3408_ = v_reuseFailAlloc_3409_;
goto v_reusejp_3407_;
}
v_reusejp_3407_:
{
return v___x_3408_;
}
}
}
}
}
else
{
lean_dec(v_decl_3373_);
lean_dec_ref(v_a_3371_);
lean_dec(v_snd_3370_);
return v___x_3382_;
}
}
v___jp_3415_:
{
lean_object* v___x_3418_; lean_object* v_env_3419_; lean_object* v___x_3420_; 
v___x_3418_ = lean_st_ref_get(v___y_3417_);
v_env_3419_ = lean_ctor_get(v___x_3418_, 0);
lean_inc_ref(v_env_3419_);
lean_dec(v___x_3418_);
v___x_3420_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3419_, v_decl_3373_);
lean_dec_ref(v_env_3419_);
if (lean_obj_tag(v___x_3420_) == 0)
{
lean_dec(v_fst_3372_);
v___y_3380_ = v___y_3416_;
v___y_3381_ = v___y_3417_;
goto v___jp_3379_;
}
else
{
lean_object* v___x_3421_; 
lean_dec_ref(v___x_3420_);
lean_dec_ref(v_a_3371_);
lean_dec(v_snd_3370_);
lean_dec_ref(v_validate_3369_);
v___x_3421_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg(v_fst_3372_, v_decl_3373_, v___y_3416_, v___y_3417_);
return v___x_3421_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__1___boxed(lean_object* v_validate_3426_, lean_object* v_snd_3427_, lean_object* v_a_3428_, lean_object* v_fst_3429_, lean_object* v_decl_3430_, lean_object* v_stx_3431_, lean_object* v_kind_3432_, lean_object* v___y_3433_, lean_object* v___y_3434_, lean_object* v___y_3435_){
_start:
{
uint8_t v_kind_boxed_3436_; lean_object* v_res_3437_; 
v_kind_boxed_3436_ = lean_unbox(v_kind_3432_);
v_res_3437_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__1(v_validate_3426_, v_snd_3427_, v_a_3428_, v_fst_3429_, v_decl_3430_, v_stx_3431_, v_kind_boxed_3436_, v___y_3433_, v___y_3434_);
lean_dec(v___y_3434_);
lean_dec_ref(v___y_3433_);
return v_res_3437_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__0(lean_object* v_fst_3438_, lean_object* v_decl_3439_, lean_object* v___y_3440_, lean_object* v___y_3441_){
_start:
{
lean_object* v___x_3443_; lean_object* v___x_3444_; lean_object* v___x_3445_; lean_object* v___x_3446_; lean_object* v___x_3447_; lean_object* v___x_3448_; 
v___x_3443_ = lean_obj_once(&l_Lean_registerTagAttribute___lam__6___closed__1, &l_Lean_registerTagAttribute___lam__6___closed__1_once, _init_l_Lean_registerTagAttribute___lam__6___closed__1);
v___x_3444_ = l_Lean_MessageData_ofName(v_fst_3438_);
v___x_3445_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3445_, 0, v___x_3443_);
lean_ctor_set(v___x_3445_, 1, v___x_3444_);
v___x_3446_ = lean_obj_once(&l_Lean_registerTagAttribute___lam__6___closed__3, &l_Lean_registerTagAttribute___lam__6___closed__3_once, _init_l_Lean_registerTagAttribute___lam__6___closed__3);
v___x_3447_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3447_, 0, v___x_3445_);
lean_ctor_set(v___x_3447_, 1, v___x_3446_);
v___x_3448_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0_spec__0___redArg(v___x_3447_, v___y_3440_, v___y_3441_);
return v___x_3448_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__0___boxed(lean_object* v_fst_3449_, lean_object* v_decl_3450_, lean_object* v___y_3451_, lean_object* v___y_3452_, lean_object* v___y_3453_){
_start:
{
lean_object* v_res_3454_; 
v_res_3454_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__0(v_fst_3449_, v_decl_3450_, v___y_3451_, v___y_3452_);
lean_dec(v___y_3452_);
lean_dec_ref(v___y_3451_);
lean_dec(v_decl_3450_);
return v_res_3454_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg(lean_object* v_validate_3455_, lean_object* v_a_3456_, lean_object* v_ref_3457_, uint8_t v_applicationTime_3458_, lean_object* v_a_3459_, lean_object* v_a_3460_){
_start:
{
if (lean_obj_tag(v_a_3459_) == 0)
{
lean_object* v___x_3461_; 
lean_dec(v_ref_3457_);
lean_dec_ref(v_a_3456_);
lean_dec_ref(v_validate_3455_);
v___x_3461_ = l_List_reverse___redArg(v_a_3460_);
return v___x_3461_;
}
else
{
lean_object* v_head_3462_; lean_object* v_snd_3463_; lean_object* v_tail_3464_; lean_object* v___x_3466_; uint8_t v_isShared_3467_; uint8_t v_isSharedCheck_3479_; 
v_head_3462_ = lean_ctor_get(v_a_3459_, 0);
lean_inc(v_head_3462_);
v_snd_3463_ = lean_ctor_get(v_head_3462_, 1);
lean_inc(v_snd_3463_);
v_tail_3464_ = lean_ctor_get(v_a_3459_, 1);
v_isSharedCheck_3479_ = !lean_is_exclusive(v_a_3459_);
if (v_isSharedCheck_3479_ == 0)
{
lean_object* v_unused_3480_; 
v_unused_3480_ = lean_ctor_get(v_a_3459_, 0);
lean_dec(v_unused_3480_);
v___x_3466_ = v_a_3459_;
v_isShared_3467_ = v_isSharedCheck_3479_;
goto v_resetjp_3465_;
}
else
{
lean_inc(v_tail_3464_);
lean_dec(v_a_3459_);
v___x_3466_ = lean_box(0);
v_isShared_3467_ = v_isSharedCheck_3479_;
goto v_resetjp_3465_;
}
v_resetjp_3465_:
{
lean_object* v_fst_3468_; lean_object* v_fst_3469_; lean_object* v_snd_3470_; lean_object* v___f_3471_; lean_object* v___f_3472_; lean_object* v___x_3473_; lean_object* v___x_3474_; lean_object* v___x_3476_; 
v_fst_3468_ = lean_ctor_get(v_head_3462_, 0);
lean_inc_n(v_fst_3468_, 3);
lean_dec(v_head_3462_);
v_fst_3469_ = lean_ctor_get(v_snd_3463_, 0);
lean_inc(v_fst_3469_);
v_snd_3470_ = lean_ctor_get(v_snd_3463_, 1);
lean_inc(v_snd_3470_);
lean_dec(v_snd_3463_);
v___f_3471_ = lean_alloc_closure((void*)(l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__0___boxed), 5, 1);
lean_closure_set(v___f_3471_, 0, v_fst_3468_);
lean_inc_ref(v_a_3456_);
lean_inc_ref(v_validate_3455_);
v___f_3472_ = lean_alloc_closure((void*)(l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__1___boxed), 10, 4);
lean_closure_set(v___f_3472_, 0, v_validate_3455_);
lean_closure_set(v___f_3472_, 1, v_snd_3470_);
lean_closure_set(v___f_3472_, 2, v_a_3456_);
lean_closure_set(v___f_3472_, 3, v_fst_3468_);
lean_inc(v_ref_3457_);
v___x_3473_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_3473_, 0, v_ref_3457_);
lean_ctor_set(v___x_3473_, 1, v_fst_3468_);
lean_ctor_set(v___x_3473_, 2, v_fst_3469_);
lean_ctor_set_uint8(v___x_3473_, sizeof(void*)*3, v_applicationTime_3458_);
v___x_3474_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3474_, 0, v___x_3473_);
lean_ctor_set(v___x_3474_, 1, v___f_3472_);
lean_ctor_set(v___x_3474_, 2, v___f_3471_);
if (v_isShared_3467_ == 0)
{
lean_ctor_set(v___x_3466_, 1, v_a_3460_);
lean_ctor_set(v___x_3466_, 0, v___x_3474_);
v___x_3476_ = v___x_3466_;
goto v_reusejp_3475_;
}
else
{
lean_object* v_reuseFailAlloc_3478_; 
v_reuseFailAlloc_3478_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3478_, 0, v___x_3474_);
lean_ctor_set(v_reuseFailAlloc_3478_, 1, v_a_3460_);
v___x_3476_ = v_reuseFailAlloc_3478_;
goto v_reusejp_3475_;
}
v_reusejp_3475_:
{
v_a_3459_ = v_tail_3464_;
v_a_3460_ = v___x_3476_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___boxed(lean_object* v_validate_3481_, lean_object* v_a_3482_, lean_object* v_ref_3483_, lean_object* v_applicationTime_3484_, lean_object* v_a_3485_, lean_object* v_a_3486_){
_start:
{
uint8_t v_applicationTime_boxed_3487_; lean_object* v_res_3488_; 
v_applicationTime_boxed_3487_ = lean_unbox(v_applicationTime_3484_);
v_res_3488_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg(v_validate_3481_, v_a_3482_, v_ref_3483_, v_applicationTime_boxed_3487_, v_a_3485_, v_a_3486_);
return v_res_3488_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg(lean_object* v_attrDescrs_3502_, lean_object* v_validate_3503_, uint8_t v_applicationTime_3504_, lean_object* v_ref_3505_){
_start:
{
lean_object* v___f_3507_; lean_object* v___f_3508_; lean_object* v___f_3509_; lean_object* v___f_3510_; lean_object* v___f_3511_; lean_object* v___f_3512_; lean_object* v___x_3513_; lean_object* v___x_3514_; lean_object* v___x_3515_; lean_object* v___x_3516_; lean_object* v___x_3517_; 
v___f_3507_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__0));
v___f_3508_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__2));
v___f_3509_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__3));
v___f_3510_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__4));
v___f_3511_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__5));
v___f_3512_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__6));
v___x_3513_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__7));
v___x_3514_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__8));
lean_inc(v_ref_3505_);
v___x_3515_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_3515_, 0, v_ref_3505_);
lean_ctor_set(v___x_3515_, 1, v___f_3511_);
lean_ctor_set(v___x_3515_, 2, v___f_3512_);
lean_ctor_set(v___x_3515_, 3, v___f_3510_);
lean_ctor_set(v___x_3515_, 4, v___f_3509_);
lean_ctor_set(v___x_3515_, 5, v___f_3508_);
lean_ctor_set(v___x_3515_, 6, v___x_3513_);
lean_ctor_set(v___x_3515_, 7, v___x_3514_);
v___x_3516_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3516_, 0, v___x_3515_);
lean_ctor_set(v___x_3516_, 1, v___f_3507_);
v___x_3517_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_3516_);
if (lean_obj_tag(v___x_3517_) == 0)
{
lean_object* v_a_3518_; lean_object* v___x_3519_; lean_object* v___x_3520_; lean_object* v___x_3521_; 
v_a_3518_ = lean_ctor_get(v___x_3517_, 0);
lean_inc_n(v_a_3518_, 2);
lean_dec_ref(v___x_3517_);
v___x_3519_ = lean_box(0);
v___x_3520_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg(v_validate_3503_, v_a_3518_, v_ref_3505_, v_applicationTime_3504_, v_attrDescrs_3502_, v___x_3519_);
lean_inc(v___x_3520_);
v___x_3521_ = l_List_forM___at___00Lean_registerEnumAttributes_spec__3(v___x_3520_);
if (lean_obj_tag(v___x_3521_) == 0)
{
lean_object* v___x_3523_; uint8_t v_isShared_3524_; uint8_t v_isSharedCheck_3529_; 
v_isSharedCheck_3529_ = !lean_is_exclusive(v___x_3521_);
if (v_isSharedCheck_3529_ == 0)
{
lean_object* v_unused_3530_; 
v_unused_3530_ = lean_ctor_get(v___x_3521_, 0);
lean_dec(v_unused_3530_);
v___x_3523_ = v___x_3521_;
v_isShared_3524_ = v_isSharedCheck_3529_;
goto v_resetjp_3522_;
}
else
{
lean_dec(v___x_3521_);
v___x_3523_ = lean_box(0);
v_isShared_3524_ = v_isSharedCheck_3529_;
goto v_resetjp_3522_;
}
v_resetjp_3522_:
{
lean_object* v___x_3525_; lean_object* v___x_3527_; 
v___x_3525_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3525_, 0, v___x_3520_);
lean_ctor_set(v___x_3525_, 1, v_a_3518_);
if (v_isShared_3524_ == 0)
{
lean_ctor_set(v___x_3523_, 0, v___x_3525_);
v___x_3527_ = v___x_3523_;
goto v_reusejp_3526_;
}
else
{
lean_object* v_reuseFailAlloc_3528_; 
v_reuseFailAlloc_3528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3528_, 0, v___x_3525_);
v___x_3527_ = v_reuseFailAlloc_3528_;
goto v_reusejp_3526_;
}
v_reusejp_3526_:
{
return v___x_3527_;
}
}
}
else
{
lean_object* v_a_3531_; lean_object* v___x_3533_; uint8_t v_isShared_3534_; uint8_t v_isSharedCheck_3538_; 
lean_dec(v___x_3520_);
lean_dec(v_a_3518_);
v_a_3531_ = lean_ctor_get(v___x_3521_, 0);
v_isSharedCheck_3538_ = !lean_is_exclusive(v___x_3521_);
if (v_isSharedCheck_3538_ == 0)
{
v___x_3533_ = v___x_3521_;
v_isShared_3534_ = v_isSharedCheck_3538_;
goto v_resetjp_3532_;
}
else
{
lean_inc(v_a_3531_);
lean_dec(v___x_3521_);
v___x_3533_ = lean_box(0);
v_isShared_3534_ = v_isSharedCheck_3538_;
goto v_resetjp_3532_;
}
v_resetjp_3532_:
{
lean_object* v___x_3536_; 
if (v_isShared_3534_ == 0)
{
v___x_3536_ = v___x_3533_;
goto v_reusejp_3535_;
}
else
{
lean_object* v_reuseFailAlloc_3537_; 
v_reuseFailAlloc_3537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3537_, 0, v_a_3531_);
v___x_3536_ = v_reuseFailAlloc_3537_;
goto v_reusejp_3535_;
}
v_reusejp_3535_:
{
return v___x_3536_;
}
}
}
}
else
{
lean_object* v_a_3539_; lean_object* v___x_3541_; uint8_t v_isShared_3542_; uint8_t v_isSharedCheck_3546_; 
lean_dec(v_ref_3505_);
lean_dec_ref(v_validate_3503_);
lean_dec(v_attrDescrs_3502_);
v_a_3539_ = lean_ctor_get(v___x_3517_, 0);
v_isSharedCheck_3546_ = !lean_is_exclusive(v___x_3517_);
if (v_isSharedCheck_3546_ == 0)
{
v___x_3541_ = v___x_3517_;
v_isShared_3542_ = v_isSharedCheck_3546_;
goto v_resetjp_3540_;
}
else
{
lean_inc(v_a_3539_);
lean_dec(v___x_3517_);
v___x_3541_ = lean_box(0);
v_isShared_3542_ = v_isSharedCheck_3546_;
goto v_resetjp_3540_;
}
v_resetjp_3540_:
{
lean_object* v___x_3544_; 
if (v_isShared_3542_ == 0)
{
v___x_3544_ = v___x_3541_;
goto v_reusejp_3543_;
}
else
{
lean_object* v_reuseFailAlloc_3545_; 
v_reuseFailAlloc_3545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3545_, 0, v_a_3539_);
v___x_3544_ = v_reuseFailAlloc_3545_;
goto v_reusejp_3543_;
}
v_reusejp_3543_:
{
return v___x_3544_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___boxed(lean_object* v_attrDescrs_3547_, lean_object* v_validate_3548_, lean_object* v_applicationTime_3549_, lean_object* v_ref_3550_, lean_object* v_a_3551_){
_start:
{
uint8_t v_applicationTime_boxed_3552_; lean_object* v_res_3553_; 
v_applicationTime_boxed_3552_ = lean_unbox(v_applicationTime_3549_);
v_res_3553_ = l_Lean_registerEnumAttributes___redArg(v_attrDescrs_3547_, v_validate_3548_, v_applicationTime_boxed_3552_, v_ref_3550_);
return v_res_3553_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes(lean_object* v_00_u03b1_3554_, lean_object* v_attrDescrs_3555_, lean_object* v_validate_3556_, uint8_t v_applicationTime_3557_, lean_object* v_ref_3558_){
_start:
{
lean_object* v___x_3560_; 
v___x_3560_ = l_Lean_registerEnumAttributes___redArg(v_attrDescrs_3555_, v_validate_3556_, v_applicationTime_3557_, v_ref_3558_);
return v___x_3560_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___boxed(lean_object* v_00_u03b1_3561_, lean_object* v_attrDescrs_3562_, lean_object* v_validate_3563_, lean_object* v_applicationTime_3564_, lean_object* v_ref_3565_, lean_object* v_a_3566_){
_start:
{
uint8_t v_applicationTime_boxed_3567_; lean_object* v_res_3568_; 
v_applicationTime_boxed_3567_ = lean_unbox(v_applicationTime_3564_);
v_res_3568_ = l_Lean_registerEnumAttributes(v_00_u03b1_3561_, v_attrDescrs_3562_, v_validate_3563_, v_applicationTime_boxed_3567_, v_ref_3565_);
return v_res_3568_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0(lean_object* v_00_u03b1_3569_, lean_object* v_env_3570_, lean_object* v_as_3571_, size_t v_i_3572_, size_t v_stop_3573_, lean_object* v_b_3574_){
_start:
{
lean_object* v___x_3575_; 
v___x_3575_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg(v_env_3570_, v_as_3571_, v_i_3572_, v_stop_3573_, v_b_3574_);
return v___x_3575_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___boxed(lean_object* v_00_u03b1_3576_, lean_object* v_env_3577_, lean_object* v_as_3578_, lean_object* v_i_3579_, lean_object* v_stop_3580_, lean_object* v_b_3581_){
_start:
{
size_t v_i_boxed_3582_; size_t v_stop_boxed_3583_; lean_object* v_res_3584_; 
v_i_boxed_3582_ = lean_unbox_usize(v_i_3579_);
lean_dec(v_i_3579_);
v_stop_boxed_3583_ = lean_unbox_usize(v_stop_3580_);
lean_dec(v_stop_3580_);
v_res_3584_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0(v_00_u03b1_3576_, v_env_3577_, v_as_3578_, v_i_boxed_3582_, v_stop_boxed_3583_, v_b_3581_);
lean_dec_ref(v_as_3578_);
return v_res_3584_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerEnumAttributes_spec__1(lean_object* v_00_u03b1_3585_, lean_object* v_newState_3586_, lean_object* v_x_3587_, lean_object* v_x_3588_){
_start:
{
lean_object* v___x_3589_; 
v___x_3589_ = l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___redArg(v_newState_3586_, v_x_3587_, v_x_3588_);
return v___x_3589_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___boxed(lean_object* v_00_u03b1_3590_, lean_object* v_newState_3591_, lean_object* v_x_3592_, lean_object* v_x_3593_){
_start:
{
lean_object* v_res_3594_; 
v_res_3594_ = l_List_foldl___at___00Lean_registerEnumAttributes_spec__1(v_00_u03b1_3590_, v_newState_3591_, v_x_3592_, v_x_3593_);
lean_dec(v_newState_3591_);
return v_res_3594_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2(lean_object* v_00_u03b1_3595_, lean_object* v_validate_3596_, lean_object* v_a_3597_, lean_object* v_ref_3598_, uint8_t v_applicationTime_3599_, lean_object* v_a_3600_, lean_object* v_a_3601_){
_start:
{
lean_object* v___x_3602_; 
v___x_3602_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg(v_validate_3596_, v_a_3597_, v_ref_3598_, v_applicationTime_3599_, v_a_3600_, v_a_3601_);
return v___x_3602_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___boxed(lean_object* v_00_u03b1_3603_, lean_object* v_validate_3604_, lean_object* v_a_3605_, lean_object* v_ref_3606_, lean_object* v_applicationTime_3607_, lean_object* v_a_3608_, lean_object* v_a_3609_){
_start:
{
uint8_t v_applicationTime_boxed_3610_; lean_object* v_res_3611_; 
v_applicationTime_boxed_3610_ = lean_unbox(v_applicationTime_3607_);
v_res_3611_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2(v_00_u03b1_3603_, v_validate_3604_, v_a_3605_, v_ref_3606_, v_applicationTime_boxed_3610_, v_a_3608_, v_a_3609_);
return v_res_3611_;
}
}
LEAN_EXPORT lean_object* l_Lean_EnumAttributes_getValue___redArg(lean_object* v_inst_3612_, lean_object* v_attr_3613_, lean_object* v_env_3614_, lean_object* v_decl_3615_){
_start:
{
lean_object* v___x_3616_; lean_object* v___x_3617_; 
v___x_3616_ = lean_box(1);
v___x_3617_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3614_, v_decl_3615_);
if (lean_obj_tag(v___x_3617_) == 0)
{
lean_object* v_ext_3618_; lean_object* v_toEnvExtension_3619_; lean_object* v_asyncMode_3620_; lean_object* v___x_3621_; lean_object* v___x_3622_; 
lean_dec(v_inst_3612_);
v_ext_3618_ = lean_ctor_get(v_attr_3613_, 1);
lean_inc_ref(v_ext_3618_);
lean_dec_ref(v_attr_3613_);
v_toEnvExtension_3619_ = lean_ctor_get(v_ext_3618_, 0);
v_asyncMode_3620_ = lean_ctor_get(v_toEnvExtension_3619_, 2);
lean_inc(v_asyncMode_3620_);
lean_inc(v_decl_3615_);
v___x_3621_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3616_, v_ext_3618_, v_env_3614_, v_asyncMode_3620_, v_decl_3615_);
lean_dec(v_asyncMode_3620_);
lean_dec_ref(v_ext_3618_);
v___x_3622_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_3621_, v_decl_3615_);
lean_dec(v_decl_3615_);
lean_dec(v___x_3621_);
return v___x_3622_;
}
else
{
lean_object* v_val_3623_; lean_object* v_ext_3624_; lean_object* v___x_3626_; uint8_t v_isShared_3627_; uint8_t v_isSharedCheck_3654_; 
v_val_3623_ = lean_ctor_get(v___x_3617_, 0);
lean_inc(v_val_3623_);
lean_dec_ref(v___x_3617_);
v_ext_3624_ = lean_ctor_get(v_attr_3613_, 1);
v_isSharedCheck_3654_ = !lean_is_exclusive(v_attr_3613_);
if (v_isSharedCheck_3654_ == 0)
{
lean_object* v_unused_3655_; 
v_unused_3655_ = lean_ctor_get(v_attr_3613_, 0);
lean_dec(v_unused_3655_);
v___x_3626_ = v_attr_3613_;
v_isShared_3627_ = v_isSharedCheck_3654_;
goto v_resetjp_3625_;
}
else
{
lean_inc(v_ext_3624_);
lean_dec(v_attr_3613_);
v___x_3626_ = lean_box(0);
v_isShared_3627_ = v_isSharedCheck_3654_;
goto v_resetjp_3625_;
}
v_resetjp_3625_:
{
uint8_t v___x_3628_; lean_object* v___x_3629_; lean_object* v___x_3630_; lean_object* v___x_3631_; uint8_t v___x_3632_; 
v___x_3628_ = 0;
v___x_3629_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_3616_, v_ext_3624_, v_env_3614_, v_val_3623_, v___x_3628_);
lean_dec(v_val_3623_);
lean_dec_ref(v_env_3614_);
lean_dec_ref(v_ext_3624_);
v___x_3630_ = lean_unsigned_to_nat(0u);
v___x_3631_ = lean_array_get_size(v___x_3629_);
v___x_3632_ = lean_nat_dec_lt(v___x_3630_, v___x_3631_);
if (v___x_3632_ == 0)
{
lean_object* v___x_3633_; 
lean_dec_ref(v___x_3629_);
lean_del_object(v___x_3626_);
lean_dec(v_decl_3615_);
lean_dec(v_inst_3612_);
v___x_3633_ = lean_box(0);
return v___x_3633_;
}
else
{
lean_object* v___x_3634_; lean_object* v___x_3635_; uint8_t v___x_3636_; 
v___x_3634_ = lean_unsigned_to_nat(1u);
v___x_3635_ = lean_nat_sub(v___x_3631_, v___x_3634_);
v___x_3636_ = lean_nat_dec_le(v___x_3630_, v___x_3635_);
if (v___x_3636_ == 0)
{
lean_object* v___x_3637_; 
lean_dec(v___x_3635_);
lean_dec_ref(v___x_3629_);
lean_del_object(v___x_3626_);
lean_dec(v_decl_3615_);
lean_dec(v_inst_3612_);
v___x_3637_ = lean_box(0);
return v___x_3637_;
}
else
{
lean_object* v___f_3638_; lean_object* v___x_3640_; 
v___f_3638_ = ((lean_object*)(l_Lean_ParametricAttribute_getParam_x3f___redArg___closed__1));
if (v_isShared_3627_ == 0)
{
lean_ctor_set(v___x_3626_, 1, v_inst_3612_);
lean_ctor_set(v___x_3626_, 0, v_decl_3615_);
v___x_3640_ = v___x_3626_;
goto v_reusejp_3639_;
}
else
{
lean_object* v_reuseFailAlloc_3653_; 
v_reuseFailAlloc_3653_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3653_, 0, v_decl_3615_);
lean_ctor_set(v_reuseFailAlloc_3653_, 1, v_inst_3612_);
v___x_3640_ = v_reuseFailAlloc_3653_;
goto v_reusejp_3639_;
}
v_reusejp_3639_:
{
lean_object* v___x_3641_; lean_object* v___x_3642_; 
v___x_3641_ = ((lean_object*)(l_Lean_ParametricAttribute_getParam_x3f___redArg___closed__2));
v___x_3642_ = l_Array_binSearchAux___redArg(v___f_3638_, v___x_3641_, v___x_3629_, v___x_3640_, v___x_3630_, v___x_3635_);
lean_dec_ref(v___x_3629_);
if (lean_obj_tag(v___x_3642_) == 0)
{
lean_object* v___x_3643_; 
v___x_3643_ = lean_box(0);
return v___x_3643_;
}
else
{
lean_object* v_val_3644_; lean_object* v___x_3646_; uint8_t v_isShared_3647_; uint8_t v_isSharedCheck_3652_; 
v_val_3644_ = lean_ctor_get(v___x_3642_, 0);
v_isSharedCheck_3652_ = !lean_is_exclusive(v___x_3642_);
if (v_isSharedCheck_3652_ == 0)
{
v___x_3646_ = v___x_3642_;
v_isShared_3647_ = v_isSharedCheck_3652_;
goto v_resetjp_3645_;
}
else
{
lean_inc(v_val_3644_);
lean_dec(v___x_3642_);
v___x_3646_ = lean_box(0);
v_isShared_3647_ = v_isSharedCheck_3652_;
goto v_resetjp_3645_;
}
v_resetjp_3645_:
{
lean_object* v_snd_3648_; lean_object* v___x_3650_; 
v_snd_3648_ = lean_ctor_get(v_val_3644_, 1);
lean_inc(v_snd_3648_);
lean_dec(v_val_3644_);
if (v_isShared_3647_ == 0)
{
lean_ctor_set(v___x_3646_, 0, v_snd_3648_);
v___x_3650_ = v___x_3646_;
goto v_reusejp_3649_;
}
else
{
lean_object* v_reuseFailAlloc_3651_; 
v_reuseFailAlloc_3651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3651_, 0, v_snd_3648_);
v___x_3650_ = v_reuseFailAlloc_3651_;
goto v_reusejp_3649_;
}
v_reusejp_3649_:
{
return v___x_3650_;
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
LEAN_EXPORT lean_object* l_Lean_EnumAttributes_getValue(lean_object* v_00_u03b1_3656_, lean_object* v_inst_3657_, lean_object* v_attr_3658_, lean_object* v_env_3659_, lean_object* v_decl_3660_){
_start:
{
lean_object* v___x_3661_; 
v___x_3661_ = l_Lean_EnumAttributes_getValue___redArg(v_inst_3657_, v_attr_3658_, v_env_3659_, v_decl_3660_);
return v___x_3661_;
}
}
LEAN_EXPORT lean_object* l_Lean_EnumAttributes_setValue___redArg(lean_object* v_attrs_3670_, lean_object* v_env_3671_, lean_object* v_decl_3672_, lean_object* v_val_3673_){
_start:
{
lean_object* v_ext_3674_; lean_object* v___x_3676_; uint8_t v_isShared_3677_; uint8_t v_isSharedCheck_3738_; 
v_ext_3674_ = lean_ctor_get(v_attrs_3670_, 1);
v_isSharedCheck_3738_ = !lean_is_exclusive(v_attrs_3670_);
if (v_isSharedCheck_3738_ == 0)
{
lean_object* v_unused_3739_; 
v_unused_3739_ = lean_ctor_get(v_attrs_3670_, 0);
lean_dec(v_unused_3739_);
v___x_3676_ = v_attrs_3670_;
v_isShared_3677_ = v_isSharedCheck_3738_;
goto v_resetjp_3675_;
}
else
{
lean_inc(v_ext_3674_);
lean_dec(v_attrs_3670_);
v___x_3676_ = lean_box(0);
v_isShared_3677_ = v_isSharedCheck_3738_;
goto v_resetjp_3675_;
}
v_resetjp_3675_:
{
lean_object* v_toEnvExtension_3678_; lean_object* v_name_3679_; lean_object* v___x_3680_; uint8_t v___x_3681_; lean_object* v___x_3682_; lean_object* v___x_3683_; lean_object* v___x_3684_; lean_object* v___x_3685_; lean_object* v___x_3686_; lean_object* v___x_3687_; lean_object* v___x_3688_; lean_object* v_pfx_3689_; lean_object* v___x_3690_; 
v_toEnvExtension_3678_ = lean_ctor_get(v_ext_3674_, 0);
v_name_3679_ = lean_ctor_get(v_ext_3674_, 1);
v___x_3680_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__0));
v___x_3681_ = 1;
lean_inc(v_name_3679_);
v___x_3682_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_3679_, v___x_3681_);
v___x_3683_ = lean_string_append(v___x_3680_, v___x_3682_);
lean_dec_ref(v___x_3682_);
v___x_3684_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__1));
v___x_3685_ = lean_string_append(v___x_3683_, v___x_3684_);
lean_inc(v_decl_3672_);
v___x_3686_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_decl_3672_, v___x_3681_);
v___x_3687_ = lean_string_append(v___x_3685_, v___x_3686_);
lean_dec_ref(v___x_3686_);
v___x_3688_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__4));
v_pfx_3689_ = lean_string_append(v___x_3687_, v___x_3688_);
v___x_3690_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3671_, v_decl_3672_);
if (lean_obj_tag(v___x_3690_) == 0)
{
lean_object* v_asyncMode_3691_; uint8_t v___x_3698_; 
v_asyncMode_3691_ = lean_ctor_get(v_toEnvExtension_3678_, 2);
lean_inc(v_asyncMode_3691_);
lean_inc(v_decl_3672_);
lean_inc_ref(v_env_3671_);
v___x_3698_ = l_Lean_EnvExtension_asyncMayModify___redArg(v_env_3671_, v_decl_3672_, v_asyncMode_3691_);
if (v___x_3698_ == 0)
{
lean_object* v___x_3699_; lean_object* v___x_3700_; lean_object* v___y_3702_; lean_object* v___x_3706_; 
lean_dec(v_asyncMode_3691_);
lean_del_object(v___x_3676_);
lean_dec_ref(v_ext_3674_);
lean_dec(v_val_3673_);
lean_dec(v_decl_3672_);
v___x_3699_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__2));
v___x_3700_ = lean_string_append(v_pfx_3689_, v___x_3699_);
v___x_3706_ = l_Lean_Environment_asyncPrefix_x3f(v_env_3671_);
if (lean_obj_tag(v___x_3706_) == 0)
{
lean_object* v___x_3707_; 
v___x_3707_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__3));
v___y_3702_ = v___x_3707_;
goto v___jp_3701_;
}
else
{
lean_object* v_val_3708_; lean_object* v___x_3709_; lean_object* v___x_3710_; lean_object* v___x_3711_; lean_object* v___x_3712_; lean_object* v___x_3713_; lean_object* v___x_3714_; 
v_val_3708_ = lean_ctor_get(v___x_3706_, 0);
lean_inc(v_val_3708_);
lean_dec_ref(v___x_3706_);
v___x_3709_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__4));
v___x_3710_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_val_3708_, v___x_3681_);
v___x_3711_ = l_addParenHeuristic(v___x_3710_);
v___x_3712_ = lean_string_append(v___x_3709_, v___x_3711_);
lean_dec_ref(v___x_3711_);
v___x_3713_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__5));
v___x_3714_ = lean_string_append(v___x_3712_, v___x_3713_);
v___y_3702_ = v___x_3714_;
goto v___jp_3701_;
}
v___jp_3701_:
{
lean_object* v___x_3703_; lean_object* v___x_3704_; lean_object* v___x_3705_; 
v___x_3703_ = lean_string_append(v___x_3700_, v___y_3702_);
lean_dec_ref(v___y_3702_);
v___x_3704_ = lean_string_append(v___x_3703_, v___x_3688_);
v___x_3705_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3705_, 0, v___x_3704_);
return v___x_3705_;
}
}
else
{
lean_object* v___x_3715_; lean_object* v___x_3716_; lean_object* v___x_3717_; 
v___x_3715_ = lean_box(1);
lean_inc(v_decl_3672_);
lean_inc_ref(v_env_3671_);
v___x_3716_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3715_, v_ext_3674_, v_env_3671_, v_asyncMode_3691_, v_decl_3672_);
v___x_3717_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_3716_, v_decl_3672_);
lean_dec(v___x_3716_);
if (lean_obj_tag(v___x_3717_) == 0)
{
lean_dec_ref(v_pfx_3689_);
goto v___jp_3692_;
}
else
{
lean_object* v___x_3719_; uint8_t v_isShared_3720_; uint8_t v_isSharedCheck_3726_; 
v_isSharedCheck_3726_ = !lean_is_exclusive(v___x_3717_);
if (v_isSharedCheck_3726_ == 0)
{
lean_object* v_unused_3727_; 
v_unused_3727_ = lean_ctor_get(v___x_3717_, 0);
lean_dec(v_unused_3727_);
v___x_3719_ = v___x_3717_;
v_isShared_3720_ = v_isSharedCheck_3726_;
goto v_resetjp_3718_;
}
else
{
lean_dec(v___x_3717_);
v___x_3719_ = lean_box(0);
v_isShared_3720_ = v_isSharedCheck_3726_;
goto v_resetjp_3718_;
}
v_resetjp_3718_:
{
if (v___x_3698_ == 0)
{
lean_del_object(v___x_3719_);
lean_dec_ref(v_pfx_3689_);
goto v___jp_3692_;
}
else
{
lean_object* v___x_3721_; lean_object* v___x_3722_; lean_object* v___x_3724_; 
lean_dec(v_asyncMode_3691_);
lean_del_object(v___x_3676_);
lean_dec_ref(v_ext_3674_);
lean_dec(v_val_3673_);
lean_dec(v_decl_3672_);
lean_dec_ref(v_env_3671_);
v___x_3721_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__6));
v___x_3722_ = lean_string_append(v_pfx_3689_, v___x_3721_);
if (v_isShared_3720_ == 0)
{
lean_ctor_set_tag(v___x_3719_, 0);
lean_ctor_set(v___x_3719_, 0, v___x_3722_);
v___x_3724_ = v___x_3719_;
goto v_reusejp_3723_;
}
else
{
lean_object* v_reuseFailAlloc_3725_; 
v_reuseFailAlloc_3725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3725_, 0, v___x_3722_);
v___x_3724_ = v_reuseFailAlloc_3725_;
goto v_reusejp_3723_;
}
v_reusejp_3723_:
{
return v___x_3724_;
}
}
}
}
}
v___jp_3692_:
{
lean_object* v___x_3694_; 
lean_inc(v_decl_3672_);
if (v_isShared_3677_ == 0)
{
lean_ctor_set(v___x_3676_, 1, v_val_3673_);
lean_ctor_set(v___x_3676_, 0, v_decl_3672_);
v___x_3694_ = v___x_3676_;
goto v_reusejp_3693_;
}
else
{
lean_object* v_reuseFailAlloc_3697_; 
v_reuseFailAlloc_3697_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3697_, 0, v_decl_3672_);
lean_ctor_set(v_reuseFailAlloc_3697_, 1, v_val_3673_);
v___x_3694_ = v_reuseFailAlloc_3697_;
goto v_reusejp_3693_;
}
v_reusejp_3693_:
{
lean_object* v___x_3695_; lean_object* v___x_3696_; 
v___x_3695_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_ext_3674_, v_env_3671_, v___x_3694_, v_asyncMode_3691_, v_decl_3672_);
lean_dec(v_asyncMode_3691_);
v___x_3696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3696_, 0, v___x_3695_);
return v___x_3696_;
}
}
}
else
{
lean_object* v___x_3729_; uint8_t v_isShared_3730_; uint8_t v_isSharedCheck_3736_; 
lean_del_object(v___x_3676_);
lean_dec_ref(v_ext_3674_);
lean_dec(v_val_3673_);
lean_dec(v_decl_3672_);
lean_dec_ref(v_env_3671_);
v_isSharedCheck_3736_ = !lean_is_exclusive(v___x_3690_);
if (v_isSharedCheck_3736_ == 0)
{
lean_object* v_unused_3737_; 
v_unused_3737_ = lean_ctor_get(v___x_3690_, 0);
lean_dec(v_unused_3737_);
v___x_3729_ = v___x_3690_;
v_isShared_3730_ = v_isSharedCheck_3736_;
goto v_resetjp_3728_;
}
else
{
lean_dec(v___x_3690_);
v___x_3729_ = lean_box(0);
v_isShared_3730_ = v_isSharedCheck_3736_;
goto v_resetjp_3728_;
}
v_resetjp_3728_:
{
lean_object* v___x_3731_; lean_object* v___x_3732_; lean_object* v___x_3734_; 
v___x_3731_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__7));
v___x_3732_ = lean_string_append(v_pfx_3689_, v___x_3731_);
if (v_isShared_3730_ == 0)
{
lean_ctor_set_tag(v___x_3729_, 0);
lean_ctor_set(v___x_3729_, 0, v___x_3732_);
v___x_3734_ = v___x_3729_;
goto v_reusejp_3733_;
}
else
{
lean_object* v_reuseFailAlloc_3735_; 
v_reuseFailAlloc_3735_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3735_, 0, v___x_3732_);
v___x_3734_ = v_reuseFailAlloc_3735_;
goto v_reusejp_3733_;
}
v_reusejp_3733_:
{
return v___x_3734_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_EnumAttributes_setValue(lean_object* v_00_u03b1_3740_, lean_object* v_attrs_3741_, lean_object* v_env_3742_, lean_object* v_decl_3743_, lean_object* v_val_3744_){
_start:
{
lean_object* v___x_3745_; 
v___x_3745_ = l_Lean_EnumAttributes_setValue___redArg(v_attrs_3741_, v_env_3742_, v_decl_3743_, v_val_3744_);
return v___x_3745_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_2990505691____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3747_; lean_object* v___x_3748_; lean_object* v___x_3749_; 
v___x_3747_ = lean_obj_once(&l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_, &l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2__once, _init_l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_);
v___x_3748_ = lean_st_mk_ref(v___x_3747_);
v___x_3749_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3749_, 0, v___x_3748_);
return v___x_3749_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_2990505691____hygCtx___hyg_2____boxed(lean_object* v_a_3750_){
_start:
{
lean_object* v_res_3751_; 
v_res_3751_ = l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_2990505691____hygCtx___hyg_2_();
return v_res_3751_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerAttributeImplBuilder(lean_object* v_builderId_3754_, lean_object* v_builder_3755_){
_start:
{
lean_object* v___x_3757_; lean_object* v___x_3758_; uint8_t v___x_3759_; 
v___x_3757_ = l_Lean_attributeImplBuilderTableRef;
v___x_3758_ = lean_st_ref_get(v___x_3757_);
v___x_3759_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(v___x_3758_, v_builderId_3754_);
lean_dec(v___x_3758_);
if (v___x_3759_ == 0)
{
lean_object* v___x_3760_; lean_object* v___x_3761_; lean_object* v___x_3762_; lean_object* v___x_3763_; 
v___x_3760_ = lean_st_ref_take(v___x_3757_);
v___x_3761_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1___redArg(v___x_3760_, v_builderId_3754_, v_builder_3755_);
v___x_3762_ = lean_st_ref_set(v___x_3757_, v___x_3761_);
v___x_3763_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3763_, 0, v___x_3762_);
return v___x_3763_;
}
else
{
lean_object* v___x_3764_; lean_object* v___x_3765_; lean_object* v___x_3766_; lean_object* v___x_3767_; lean_object* v___x_3768_; lean_object* v___x_3769_; lean_object* v___x_3770_; 
lean_dec_ref(v_builder_3755_);
v___x_3764_ = ((lean_object*)(l_Lean_registerAttributeImplBuilder___closed__0));
v___x_3765_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_builderId_3754_, v___x_3759_);
v___x_3766_ = lean_string_append(v___x_3764_, v___x_3765_);
lean_dec_ref(v___x_3765_);
v___x_3767_ = ((lean_object*)(l_Lean_registerAttributeImplBuilder___closed__1));
v___x_3768_ = lean_string_append(v___x_3766_, v___x_3767_);
v___x_3769_ = lean_mk_io_user_error(v___x_3768_);
v___x_3770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3770_, 0, v___x_3769_);
return v___x_3770_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerAttributeImplBuilder___boxed(lean_object* v_builderId_3771_, lean_object* v_builder_3772_, lean_object* v_a_3773_){
_start:
{
lean_object* v_res_3774_; 
v_res_3774_ = l_Lean_registerAttributeImplBuilder(v_builderId_3771_, v_builder_3772_);
return v_res_3774_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___redArg(lean_object* v_e_3775_){
_start:
{
if (lean_obj_tag(v_e_3775_) == 0)
{
lean_object* v_a_3777_; lean_object* v___x_3779_; uint8_t v_isShared_3780_; uint8_t v_isSharedCheck_3785_; 
v_a_3777_ = lean_ctor_get(v_e_3775_, 0);
v_isSharedCheck_3785_ = !lean_is_exclusive(v_e_3775_);
if (v_isSharedCheck_3785_ == 0)
{
v___x_3779_ = v_e_3775_;
v_isShared_3780_ = v_isSharedCheck_3785_;
goto v_resetjp_3778_;
}
else
{
lean_inc(v_a_3777_);
lean_dec(v_e_3775_);
v___x_3779_ = lean_box(0);
v_isShared_3780_ = v_isSharedCheck_3785_;
goto v_resetjp_3778_;
}
v_resetjp_3778_:
{
lean_object* v___x_3781_; lean_object* v___x_3783_; 
v___x_3781_ = lean_mk_io_user_error(v_a_3777_);
if (v_isShared_3780_ == 0)
{
lean_ctor_set_tag(v___x_3779_, 1);
lean_ctor_set(v___x_3779_, 0, v___x_3781_);
v___x_3783_ = v___x_3779_;
goto v_reusejp_3782_;
}
else
{
lean_object* v_reuseFailAlloc_3784_; 
v_reuseFailAlloc_3784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3784_, 0, v___x_3781_);
v___x_3783_ = v_reuseFailAlloc_3784_;
goto v_reusejp_3782_;
}
v_reusejp_3782_:
{
return v___x_3783_;
}
}
}
else
{
lean_object* v_a_3786_; lean_object* v___x_3788_; uint8_t v_isShared_3789_; uint8_t v_isSharedCheck_3793_; 
v_a_3786_ = lean_ctor_get(v_e_3775_, 0);
v_isSharedCheck_3793_ = !lean_is_exclusive(v_e_3775_);
if (v_isSharedCheck_3793_ == 0)
{
v___x_3788_ = v_e_3775_;
v_isShared_3789_ = v_isSharedCheck_3793_;
goto v_resetjp_3787_;
}
else
{
lean_inc(v_a_3786_);
lean_dec(v_e_3775_);
v___x_3788_ = lean_box(0);
v_isShared_3789_ = v_isSharedCheck_3793_;
goto v_resetjp_3787_;
}
v_resetjp_3787_:
{
lean_object* v___x_3791_; 
if (v_isShared_3789_ == 0)
{
lean_ctor_set_tag(v___x_3788_, 0);
v___x_3791_ = v___x_3788_;
goto v_reusejp_3790_;
}
else
{
lean_object* v_reuseFailAlloc_3792_; 
v_reuseFailAlloc_3792_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3792_, 0, v_a_3786_);
v___x_3791_ = v_reuseFailAlloc_3792_;
goto v_reusejp_3790_;
}
v_reusejp_3790_:
{
return v___x_3791_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___redArg___boxed(lean_object* v_e_3794_, lean_object* v_a_3795_){
_start:
{
lean_object* v_res_3796_; 
v_res_3796_ = l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___redArg(v_e_3794_);
return v_res_3796_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1(lean_object* v_00_u03b1_3797_, lean_object* v_e_3798_){
_start:
{
lean_object* v___x_3800_; 
v___x_3800_ = l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___redArg(v_e_3798_);
return v___x_3800_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___boxed(lean_object* v_00_u03b1_3801_, lean_object* v_e_3802_, lean_object* v_a_3803_){
_start:
{
lean_object* v_res_3804_; 
v_res_3804_ = l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1(v_00_u03b1_3801_, v_e_3802_);
return v_res_3804_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___redArg(lean_object* v_a_3805_, lean_object* v_x_3806_){
_start:
{
if (lean_obj_tag(v_x_3806_) == 0)
{
lean_object* v___x_3807_; 
v___x_3807_ = lean_box(0);
return v___x_3807_;
}
else
{
lean_object* v_key_3808_; lean_object* v_value_3809_; lean_object* v_tail_3810_; uint8_t v___x_3811_; 
v_key_3808_ = lean_ctor_get(v_x_3806_, 0);
v_value_3809_ = lean_ctor_get(v_x_3806_, 1);
v_tail_3810_ = lean_ctor_get(v_x_3806_, 2);
v___x_3811_ = lean_name_eq(v_key_3808_, v_a_3805_);
if (v___x_3811_ == 0)
{
v_x_3806_ = v_tail_3810_;
goto _start;
}
else
{
lean_object* v___x_3813_; 
lean_inc(v_value_3809_);
v___x_3813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3813_, 0, v_value_3809_);
return v___x_3813_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___redArg___boxed(lean_object* v_a_3814_, lean_object* v_x_3815_){
_start:
{
lean_object* v_res_3816_; 
v_res_3816_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___redArg(v_a_3814_, v_x_3815_);
lean_dec(v_x_3815_);
lean_dec(v_a_3814_);
return v_res_3816_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(lean_object* v_m_3817_, lean_object* v_a_3818_){
_start:
{
lean_object* v_buckets_3819_; lean_object* v___x_3820_; uint64_t v___y_3822_; 
v_buckets_3819_ = lean_ctor_get(v_m_3817_, 1);
v___x_3820_ = lean_array_get_size(v_buckets_3819_);
if (lean_obj_tag(v_a_3818_) == 0)
{
uint64_t v___x_3836_; 
v___x_3836_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg___closed__0);
v___y_3822_ = v___x_3836_;
goto v___jp_3821_;
}
else
{
uint64_t v_hash_3837_; 
v_hash_3837_ = lean_ctor_get_uint64(v_a_3818_, sizeof(void*)*2);
v___y_3822_ = v_hash_3837_;
goto v___jp_3821_;
}
v___jp_3821_:
{
uint64_t v___x_3823_; uint64_t v___x_3824_; uint64_t v_fold_3825_; uint64_t v___x_3826_; uint64_t v___x_3827_; uint64_t v___x_3828_; size_t v___x_3829_; size_t v___x_3830_; size_t v___x_3831_; size_t v___x_3832_; size_t v___x_3833_; lean_object* v___x_3834_; lean_object* v___x_3835_; 
v___x_3823_ = 32ULL;
v___x_3824_ = lean_uint64_shift_right(v___y_3822_, v___x_3823_);
v_fold_3825_ = lean_uint64_xor(v___y_3822_, v___x_3824_);
v___x_3826_ = 16ULL;
v___x_3827_ = lean_uint64_shift_right(v_fold_3825_, v___x_3826_);
v___x_3828_ = lean_uint64_xor(v_fold_3825_, v___x_3827_);
v___x_3829_ = lean_uint64_to_usize(v___x_3828_);
v___x_3830_ = lean_usize_of_nat(v___x_3820_);
v___x_3831_ = ((size_t)1ULL);
v___x_3832_ = lean_usize_sub(v___x_3830_, v___x_3831_);
v___x_3833_ = lean_usize_land(v___x_3829_, v___x_3832_);
v___x_3834_ = lean_array_uget_borrowed(v_buckets_3819_, v___x_3833_);
v___x_3835_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___redArg(v_a_3818_, v___x_3834_);
return v___x_3835_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg___boxed(lean_object* v_m_3838_, lean_object* v_a_3839_){
_start:
{
lean_object* v_res_3840_; 
v_res_3840_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(v_m_3838_, v_a_3839_);
lean_dec(v_a_3839_);
lean_dec_ref(v_m_3838_);
return v_res_3840_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAttributeImplOfEntry(lean_object* v_e_3842_){
_start:
{
lean_object* v___x_3844_; lean_object* v___x_3845_; lean_object* v_builderId_3846_; lean_object* v_ref_3847_; lean_object* v_args_3848_; lean_object* v___x_3849_; 
v___x_3844_ = l_Lean_attributeImplBuilderTableRef;
v___x_3845_ = lean_st_ref_get(v___x_3844_);
v_builderId_3846_ = lean_ctor_get(v_e_3842_, 0);
lean_inc(v_builderId_3846_);
v_ref_3847_ = lean_ctor_get(v_e_3842_, 1);
lean_inc(v_ref_3847_);
v_args_3848_ = lean_ctor_get(v_e_3842_, 2);
lean_inc(v_args_3848_);
lean_dec_ref(v_e_3842_);
v___x_3849_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(v___x_3845_, v_builderId_3846_);
lean_dec(v___x_3845_);
if (lean_obj_tag(v___x_3849_) == 0)
{
lean_object* v___x_3850_; uint8_t v___x_3851_; lean_object* v___x_3852_; lean_object* v___x_3853_; lean_object* v___x_3854_; lean_object* v___x_3855_; lean_object* v___x_3856_; lean_object* v___x_3857_; 
lean_dec(v_args_3848_);
lean_dec(v_ref_3847_);
v___x_3850_ = ((lean_object*)(l_Lean_mkAttributeImplOfEntry___closed__0));
v___x_3851_ = 1;
v___x_3852_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_builderId_3846_, v___x_3851_);
v___x_3853_ = lean_string_append(v___x_3850_, v___x_3852_);
lean_dec_ref(v___x_3852_);
v___x_3854_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__4));
v___x_3855_ = lean_string_append(v___x_3853_, v___x_3854_);
v___x_3856_ = lean_mk_io_user_error(v___x_3855_);
v___x_3857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3857_, 0, v___x_3856_);
return v___x_3857_;
}
else
{
lean_object* v_val_3858_; lean_object* v___x_3859_; lean_object* v___x_3860_; 
lean_dec(v_builderId_3846_);
v_val_3858_ = lean_ctor_get(v___x_3849_, 0);
lean_inc(v_val_3858_);
lean_dec_ref(v___x_3849_);
v___x_3859_ = lean_apply_2(v_val_3858_, v_ref_3847_, v_args_3848_);
v___x_3860_ = l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___redArg(v___x_3859_);
return v___x_3860_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkAttributeImplOfEntry___boxed(lean_object* v_e_3861_, lean_object* v_a_3862_){
_start:
{
lean_object* v_res_3863_; 
v_res_3863_ = l_Lean_mkAttributeImplOfEntry(v_e_3861_);
return v_res_3863_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0(lean_object* v_00_u03b2_3864_, lean_object* v_m_3865_, lean_object* v_a_3866_){
_start:
{
lean_object* v___x_3867_; 
v___x_3867_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(v_m_3865_, v_a_3866_);
return v___x_3867_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___boxed(lean_object* v_00_u03b2_3868_, lean_object* v_m_3869_, lean_object* v_a_3870_){
_start:
{
lean_object* v_res_3871_; 
v_res_3871_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0(v_00_u03b2_3868_, v_m_3869_, v_a_3870_);
lean_dec(v_a_3870_);
lean_dec_ref(v_m_3869_);
return v_res_3871_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0(lean_object* v_00_u03b2_3872_, lean_object* v_a_3873_, lean_object* v_x_3874_){
_start:
{
lean_object* v___x_3875_; 
v___x_3875_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___redArg(v_a_3873_, v_x_3874_);
return v___x_3875_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3876_, lean_object* v_a_3877_, lean_object* v_x_3878_){
_start:
{
lean_object* v_res_3879_; 
v_res_3879_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0(v_00_u03b2_3876_, v_a_3877_, v_x_3878_);
lean_dec(v_x_3878_);
lean_dec(v_a_3877_);
return v_res_3879_;
}
}
static lean_object* _init_l_Lean_instInhabitedAttributeExtensionState_default___closed__0(void){
_start:
{
lean_object* v___x_3880_; lean_object* v___x_3881_; lean_object* v___x_3882_; 
v___x_3880_ = lean_obj_once(&l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_, &l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2__once, _init_l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_);
v___x_3881_ = lean_box(0);
v___x_3882_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3882_, 0, v___x_3881_);
lean_ctor_set(v___x_3882_, 1, v___x_3880_);
return v___x_3882_;
}
}
static lean_object* _init_l_Lean_instInhabitedAttributeExtensionState_default(void){
_start:
{
lean_object* v___x_3883_; 
v___x_3883_ = lean_obj_once(&l_Lean_instInhabitedAttributeExtensionState_default___closed__0, &l_Lean_instInhabitedAttributeExtensionState_default___closed__0_once, _init_l_Lean_instInhabitedAttributeExtensionState_default___closed__0);
return v___x_3883_;
}
}
static lean_object* _init_l_Lean_instInhabitedAttributeExtensionState(void){
_start:
{
lean_object* v___x_3884_; 
v___x_3884_ = l_Lean_instInhabitedAttributeExtensionState_default;
return v___x_3884_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_AttributeExtension_mkInitial(){
_start:
{
lean_object* v___x_3886_; lean_object* v___x_3887_; lean_object* v___x_3888_; lean_object* v___x_3889_; lean_object* v___x_3890_; 
v___x_3886_ = l_Lean_attributeMapRef;
v___x_3887_ = lean_st_ref_get(v___x_3886_);
v___x_3888_ = lean_box(0);
v___x_3889_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3889_, 0, v___x_3888_);
lean_ctor_set(v___x_3889_, 1, v___x_3887_);
v___x_3890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3890_, 0, v___x_3889_);
return v___x_3890_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_AttributeExtension_mkInitial___boxed(lean_object* v_a_3891_){
_start:
{
lean_object* v_res_3892_; 
v_res_3892_ = l___private_Lean_Attributes_0__Lean_AttributeExtension_mkInitial();
return v_res_3892_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAttributeImplOfConstantUnsafe(lean_object* v_env_3898_, lean_object* v_opts_3899_, lean_object* v_declName_3900_){
_start:
{
uint8_t v___x_3903_; lean_object* v___x_3904_; 
v___x_3903_ = 0;
lean_inc(v_declName_3900_);
lean_inc_ref(v_env_3898_);
v___x_3904_ = l_Lean_Environment_find_x3f(v_env_3898_, v_declName_3900_, v___x_3903_);
if (lean_obj_tag(v___x_3904_) == 0)
{
lean_object* v___x_3905_; uint8_t v___x_3906_; lean_object* v___x_3907_; lean_object* v___x_3908_; lean_object* v___x_3909_; lean_object* v___x_3910_; lean_object* v___x_3911_; 
lean_dec_ref(v_env_3898_);
v___x_3905_ = ((lean_object*)(l_Lean_mkAttributeImplOfConstantUnsafe___closed__2));
v___x_3906_ = 1;
v___x_3907_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_declName_3900_, v___x_3906_);
v___x_3908_ = lean_string_append(v___x_3905_, v___x_3907_);
lean_dec_ref(v___x_3907_);
v___x_3909_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__4));
v___x_3910_ = lean_string_append(v___x_3908_, v___x_3909_);
v___x_3911_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3911_, 0, v___x_3910_);
return v___x_3911_;
}
else
{
lean_object* v_val_3912_; lean_object* v___x_3913_; 
v_val_3912_ = lean_ctor_get(v___x_3904_, 0);
lean_inc(v_val_3912_);
lean_dec_ref(v___x_3904_);
v___x_3913_ = l_Lean_ConstantInfo_type(v_val_3912_);
lean_dec(v_val_3912_);
if (lean_obj_tag(v___x_3913_) == 4)
{
lean_object* v_declName_3914_; 
v_declName_3914_ = lean_ctor_get(v___x_3913_, 0);
lean_inc(v_declName_3914_);
lean_dec_ref(v___x_3913_);
if (lean_obj_tag(v_declName_3914_) == 1)
{
lean_object* v_pre_3915_; 
v_pre_3915_ = lean_ctor_get(v_declName_3914_, 0);
lean_inc(v_pre_3915_);
if (lean_obj_tag(v_pre_3915_) == 1)
{
lean_object* v_pre_3916_; 
v_pre_3916_ = lean_ctor_get(v_pre_3915_, 0);
if (lean_obj_tag(v_pre_3916_) == 0)
{
lean_object* v_str_3917_; lean_object* v_str_3918_; lean_object* v___x_3919_; uint8_t v___x_3920_; 
v_str_3917_ = lean_ctor_get(v_declName_3914_, 1);
lean_inc_ref(v_str_3917_);
lean_dec_ref(v_declName_3914_);
v_str_3918_ = lean_ctor_get(v_pre_3915_, 1);
lean_inc_ref(v_str_3918_);
lean_dec_ref(v_pre_3915_);
v___x_3919_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__0));
v___x_3920_ = lean_string_dec_eq(v_str_3918_, v___x_3919_);
lean_dec_ref(v_str_3918_);
if (v___x_3920_ == 0)
{
lean_dec_ref(v_str_3917_);
lean_dec(v_declName_3900_);
lean_dec_ref(v_env_3898_);
goto v___jp_3901_;
}
else
{
lean_object* v___x_3921_; uint8_t v___x_3922_; 
v___x_3921_ = ((lean_object*)(l_Lean_mkAttributeImplOfConstantUnsafe___closed__3));
v___x_3922_ = lean_string_dec_eq(v_str_3917_, v___x_3921_);
lean_dec_ref(v_str_3917_);
if (v___x_3922_ == 0)
{
lean_dec(v_declName_3900_);
lean_dec_ref(v_env_3898_);
goto v___jp_3901_;
}
else
{
lean_object* v___x_3923_; 
v___x_3923_ = l_Lean_Environment_evalConst___redArg(v_env_3898_, v_opts_3899_, v_declName_3900_, v___x_3922_);
lean_dec(v_declName_3900_);
lean_dec_ref(v_env_3898_);
return v___x_3923_;
}
}
}
else
{
lean_dec_ref(v_pre_3915_);
lean_dec_ref(v_declName_3914_);
lean_dec(v_declName_3900_);
lean_dec_ref(v_env_3898_);
goto v___jp_3901_;
}
}
else
{
lean_dec(v_pre_3915_);
lean_dec_ref(v_declName_3914_);
lean_dec(v_declName_3900_);
lean_dec_ref(v_env_3898_);
goto v___jp_3901_;
}
}
else
{
lean_dec(v_declName_3914_);
lean_dec(v_declName_3900_);
lean_dec_ref(v_env_3898_);
goto v___jp_3901_;
}
}
else
{
lean_dec_ref(v___x_3913_);
lean_dec(v_declName_3900_);
lean_dec_ref(v_env_3898_);
goto v___jp_3901_;
}
}
v___jp_3901_:
{
lean_object* v___x_3902_; 
v___x_3902_ = ((lean_object*)(l_Lean_mkAttributeImplOfConstantUnsafe___closed__1));
return v___x_3902_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkAttributeImplOfConstantUnsafe___boxed(lean_object* v_env_3924_, lean_object* v_opts_3925_, lean_object* v_declName_3926_){
_start:
{
lean_object* v_res_3927_; 
v_res_3927_ = l_Lean_mkAttributeImplOfConstantUnsafe(v_env_3924_, v_opts_3925_, v_declName_3926_);
lean_dec_ref(v_opts_3925_);
return v_res_3927_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg(lean_object* v_as_3928_, size_t v_i_3929_, size_t v_stop_3930_, lean_object* v_b_3931_){
_start:
{
uint8_t v___x_3933_; 
v___x_3933_ = lean_usize_dec_eq(v_i_3929_, v_stop_3930_);
if (v___x_3933_ == 0)
{
lean_object* v___x_3934_; lean_object* v___x_3935_; 
v___x_3934_ = lean_array_uget_borrowed(v_as_3928_, v_i_3929_);
lean_inc(v___x_3934_);
v___x_3935_ = l_Lean_mkAttributeImplOfEntry(v___x_3934_);
if (lean_obj_tag(v___x_3935_) == 0)
{
lean_object* v_a_3936_; lean_object* v_toAttributeImplCore_3937_; lean_object* v_name_3938_; lean_object* v___x_3939_; size_t v___x_3940_; size_t v___x_3941_; 
v_a_3936_ = lean_ctor_get(v___x_3935_, 0);
lean_inc(v_a_3936_);
lean_dec_ref(v___x_3935_);
v_toAttributeImplCore_3937_ = lean_ctor_get(v_a_3936_, 0);
v_name_3938_ = lean_ctor_get(v_toAttributeImplCore_3937_, 1);
lean_inc(v_name_3938_);
v___x_3939_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1___redArg(v_b_3931_, v_name_3938_, v_a_3936_);
v___x_3940_ = ((size_t)1ULL);
v___x_3941_ = lean_usize_add(v_i_3929_, v___x_3940_);
v_i_3929_ = v___x_3941_;
v_b_3931_ = v___x_3939_;
goto _start;
}
else
{
lean_object* v_a_3943_; lean_object* v___x_3945_; uint8_t v_isShared_3946_; uint8_t v_isSharedCheck_3950_; 
lean_dec_ref(v_b_3931_);
v_a_3943_ = lean_ctor_get(v___x_3935_, 0);
v_isSharedCheck_3950_ = !lean_is_exclusive(v___x_3935_);
if (v_isSharedCheck_3950_ == 0)
{
v___x_3945_ = v___x_3935_;
v_isShared_3946_ = v_isSharedCheck_3950_;
goto v_resetjp_3944_;
}
else
{
lean_inc(v_a_3943_);
lean_dec(v___x_3935_);
v___x_3945_ = lean_box(0);
v_isShared_3946_ = v_isSharedCheck_3950_;
goto v_resetjp_3944_;
}
v_resetjp_3944_:
{
lean_object* v___x_3948_; 
if (v_isShared_3946_ == 0)
{
v___x_3948_ = v___x_3945_;
goto v_reusejp_3947_;
}
else
{
lean_object* v_reuseFailAlloc_3949_; 
v_reuseFailAlloc_3949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3949_, 0, v_a_3943_);
v___x_3948_ = v_reuseFailAlloc_3949_;
goto v_reusejp_3947_;
}
v_reusejp_3947_:
{
return v___x_3948_;
}
}
}
}
else
{
lean_object* v___x_3951_; 
v___x_3951_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3951_, 0, v_b_3931_);
return v___x_3951_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg___boxed(lean_object* v_as_3952_, lean_object* v_i_3953_, lean_object* v_stop_3954_, lean_object* v_b_3955_, lean_object* v___y_3956_){
_start:
{
size_t v_i_boxed_3957_; size_t v_stop_boxed_3958_; lean_object* v_res_3959_; 
v_i_boxed_3957_ = lean_unbox_usize(v_i_3953_);
lean_dec(v_i_3953_);
v_stop_boxed_3958_ = lean_unbox_usize(v_stop_3954_);
lean_dec(v_stop_3954_);
v_res_3959_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg(v_as_3952_, v_i_boxed_3957_, v_stop_boxed_3958_, v_b_3955_);
lean_dec_ref(v_as_3952_);
return v_res_3959_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__1(lean_object* v_as_3960_, size_t v_i_3961_, size_t v_stop_3962_, lean_object* v_b_3963_, lean_object* v___y_3964_){
_start:
{
lean_object* v_a_3967_; lean_object* v___y_3972_; uint8_t v___x_3974_; 
v___x_3974_ = lean_usize_dec_eq(v_i_3961_, v_stop_3962_);
if (v___x_3974_ == 0)
{
lean_object* v___x_3975_; lean_object* v___x_3976_; lean_object* v___x_3977_; uint8_t v___x_3978_; 
v___x_3975_ = lean_array_uget_borrowed(v_as_3960_, v_i_3961_);
v___x_3976_ = lean_unsigned_to_nat(0u);
v___x_3977_ = lean_array_get_size(v___x_3975_);
v___x_3978_ = lean_nat_dec_lt(v___x_3976_, v___x_3977_);
if (v___x_3978_ == 0)
{
v_a_3967_ = v_b_3963_;
goto v___jp_3966_;
}
else
{
uint8_t v___x_3979_; 
v___x_3979_ = lean_nat_dec_le(v___x_3977_, v___x_3977_);
if (v___x_3979_ == 0)
{
if (v___x_3978_ == 0)
{
v_a_3967_ = v_b_3963_;
goto v___jp_3966_;
}
else
{
size_t v___x_3980_; size_t v___x_3981_; lean_object* v___x_3982_; 
v___x_3980_ = ((size_t)0ULL);
v___x_3981_ = lean_usize_of_nat(v___x_3977_);
v___x_3982_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg(v___x_3975_, v___x_3980_, v___x_3981_, v_b_3963_);
v___y_3972_ = v___x_3982_;
goto v___jp_3971_;
}
}
else
{
size_t v___x_3983_; size_t v___x_3984_; lean_object* v___x_3985_; 
v___x_3983_ = ((size_t)0ULL);
v___x_3984_ = lean_usize_of_nat(v___x_3977_);
v___x_3985_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg(v___x_3975_, v___x_3983_, v___x_3984_, v_b_3963_);
v___y_3972_ = v___x_3985_;
goto v___jp_3971_;
}
}
}
else
{
lean_object* v___x_3986_; 
v___x_3986_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3986_, 0, v_b_3963_);
return v___x_3986_;
}
v___jp_3966_:
{
size_t v___x_3968_; size_t v___x_3969_; 
v___x_3968_ = ((size_t)1ULL);
v___x_3969_ = lean_usize_add(v_i_3961_, v___x_3968_);
v_i_3961_ = v___x_3969_;
v_b_3963_ = v_a_3967_;
goto _start;
}
v___jp_3971_:
{
if (lean_obj_tag(v___y_3972_) == 0)
{
lean_object* v_a_3973_; 
v_a_3973_ = lean_ctor_get(v___y_3972_, 0);
lean_inc(v_a_3973_);
lean_dec_ref(v___y_3972_);
v_a_3967_ = v_a_3973_;
goto v___jp_3966_;
}
else
{
return v___y_3972_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__1___boxed(lean_object* v_as_3987_, lean_object* v_i_3988_, lean_object* v_stop_3989_, lean_object* v_b_3990_, lean_object* v___y_3991_, lean_object* v___y_3992_){
_start:
{
size_t v_i_boxed_3993_; size_t v_stop_boxed_3994_; lean_object* v_res_3995_; 
v_i_boxed_3993_ = lean_unbox_usize(v_i_3988_);
lean_dec(v_i_3988_);
v_stop_boxed_3994_ = lean_unbox_usize(v_stop_3989_);
lean_dec(v_stop_3989_);
v_res_3995_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__1(v_as_3987_, v_i_boxed_3993_, v_stop_boxed_3994_, v_b_3990_, v___y_3991_);
lean_dec_ref(v___y_3991_);
lean_dec_ref(v_as_3987_);
return v_res_3995_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_AttributeExtension_addImported(lean_object* v_es_3996_, lean_object* v_a_3997_){
_start:
{
lean_object* v_a_4000_; lean_object* v___y_4005_; lean_object* v___x_4015_; lean_object* v___x_4016_; lean_object* v___x_4017_; lean_object* v___x_4018_; uint8_t v___x_4019_; 
v___x_4015_ = l_Lean_attributeMapRef;
v___x_4016_ = lean_st_ref_get(v___x_4015_);
v___x_4017_ = lean_unsigned_to_nat(0u);
v___x_4018_ = lean_array_get_size(v_es_3996_);
v___x_4019_ = lean_nat_dec_lt(v___x_4017_, v___x_4018_);
if (v___x_4019_ == 0)
{
v_a_4000_ = v___x_4016_;
goto v___jp_3999_;
}
else
{
uint8_t v___x_4020_; 
v___x_4020_ = lean_nat_dec_le(v___x_4018_, v___x_4018_);
if (v___x_4020_ == 0)
{
if (v___x_4019_ == 0)
{
v_a_4000_ = v___x_4016_;
goto v___jp_3999_;
}
else
{
size_t v___x_4021_; size_t v___x_4022_; lean_object* v___x_4023_; 
v___x_4021_ = ((size_t)0ULL);
v___x_4022_ = lean_usize_of_nat(v___x_4018_);
v___x_4023_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__1(v_es_3996_, v___x_4021_, v___x_4022_, v___x_4016_, v_a_3997_);
v___y_4005_ = v___x_4023_;
goto v___jp_4004_;
}
}
else
{
size_t v___x_4024_; size_t v___x_4025_; lean_object* v___x_4026_; 
v___x_4024_ = ((size_t)0ULL);
v___x_4025_ = lean_usize_of_nat(v___x_4018_);
v___x_4026_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__1(v_es_3996_, v___x_4024_, v___x_4025_, v___x_4016_, v_a_3997_);
v___y_4005_ = v___x_4026_;
goto v___jp_4004_;
}
}
v___jp_3999_:
{
lean_object* v___x_4001_; lean_object* v___x_4002_; lean_object* v___x_4003_; 
v___x_4001_ = lean_box(0);
v___x_4002_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4002_, 0, v___x_4001_);
lean_ctor_set(v___x_4002_, 1, v_a_4000_);
v___x_4003_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4003_, 0, v___x_4002_);
return v___x_4003_;
}
v___jp_4004_:
{
if (lean_obj_tag(v___y_4005_) == 0)
{
lean_object* v_a_4006_; 
v_a_4006_ = lean_ctor_get(v___y_4005_, 0);
lean_inc(v_a_4006_);
lean_dec_ref(v___y_4005_);
v_a_4000_ = v_a_4006_;
goto v___jp_3999_;
}
else
{
lean_object* v_a_4007_; lean_object* v___x_4009_; uint8_t v_isShared_4010_; uint8_t v_isSharedCheck_4014_; 
v_a_4007_ = lean_ctor_get(v___y_4005_, 0);
v_isSharedCheck_4014_ = !lean_is_exclusive(v___y_4005_);
if (v_isSharedCheck_4014_ == 0)
{
v___x_4009_ = v___y_4005_;
v_isShared_4010_ = v_isSharedCheck_4014_;
goto v_resetjp_4008_;
}
else
{
lean_inc(v_a_4007_);
lean_dec(v___y_4005_);
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_AttributeExtension_addImported___boxed(lean_object* v_es_4027_, lean_object* v_a_4028_, lean_object* v_a_4029_){
_start:
{
lean_object* v_res_4030_; 
v_res_4030_ = l___private_Lean_Attributes_0__Lean_AttributeExtension_addImported(v_es_4027_, v_a_4028_);
lean_dec_ref(v_a_4028_);
lean_dec_ref(v_es_4027_);
return v_res_4030_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0(lean_object* v_as_4031_, size_t v_i_4032_, size_t v_stop_4033_, lean_object* v_b_4034_, lean_object* v___y_4035_){
_start:
{
lean_object* v___x_4037_; 
v___x_4037_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg(v_as_4031_, v_i_4032_, v_stop_4033_, v_b_4034_);
return v___x_4037_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___boxed(lean_object* v_as_4038_, lean_object* v_i_4039_, lean_object* v_stop_4040_, lean_object* v_b_4041_, lean_object* v___y_4042_, lean_object* v___y_4043_){
_start:
{
size_t v_i_boxed_4044_; size_t v_stop_boxed_4045_; lean_object* v_res_4046_; 
v_i_boxed_4044_ = lean_unbox_usize(v_i_4039_);
lean_dec(v_i_4039_);
v_stop_boxed_4045_ = lean_unbox_usize(v_stop_4040_);
lean_dec(v_stop_4040_);
v_res_4046_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0(v_as_4038_, v_i_boxed_4044_, v_stop_boxed_4045_, v_b_4041_, v___y_4042_);
lean_dec_ref(v___y_4042_);
lean_dec_ref(v_as_4038_);
return v_res_4046_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_addAttrEntry(lean_object* v_s_4047_, lean_object* v_e_4048_){
_start:
{
lean_object* v_snd_4049_; lean_object* v_toAttributeImplCore_4050_; lean_object* v_fst_4051_; lean_object* v___x_4053_; uint8_t v_isShared_4054_; uint8_t v_isSharedCheck_4069_; 
v_snd_4049_ = lean_ctor_get(v_e_4048_, 1);
lean_inc(v_snd_4049_);
v_toAttributeImplCore_4050_ = lean_ctor_get(v_snd_4049_, 0);
v_fst_4051_ = lean_ctor_get(v_e_4048_, 0);
v_isSharedCheck_4069_ = !lean_is_exclusive(v_e_4048_);
if (v_isSharedCheck_4069_ == 0)
{
lean_object* v_unused_4070_; 
v_unused_4070_ = lean_ctor_get(v_e_4048_, 1);
lean_dec(v_unused_4070_);
v___x_4053_ = v_e_4048_;
v_isShared_4054_ = v_isSharedCheck_4069_;
goto v_resetjp_4052_;
}
else
{
lean_inc(v_fst_4051_);
lean_dec(v_e_4048_);
v___x_4053_ = lean_box(0);
v_isShared_4054_ = v_isSharedCheck_4069_;
goto v_resetjp_4052_;
}
v_resetjp_4052_:
{
lean_object* v_newEntries_4055_; lean_object* v_map_4056_; lean_object* v___x_4058_; uint8_t v_isShared_4059_; uint8_t v_isSharedCheck_4068_; 
v_newEntries_4055_ = lean_ctor_get(v_s_4047_, 0);
v_map_4056_ = lean_ctor_get(v_s_4047_, 1);
v_isSharedCheck_4068_ = !lean_is_exclusive(v_s_4047_);
if (v_isSharedCheck_4068_ == 0)
{
v___x_4058_ = v_s_4047_;
v_isShared_4059_ = v_isSharedCheck_4068_;
goto v_resetjp_4057_;
}
else
{
lean_inc(v_map_4056_);
lean_inc(v_newEntries_4055_);
lean_dec(v_s_4047_);
v___x_4058_ = lean_box(0);
v_isShared_4059_ = v_isSharedCheck_4068_;
goto v_resetjp_4057_;
}
v_resetjp_4057_:
{
lean_object* v_name_4060_; lean_object* v___x_4062_; 
v_name_4060_ = lean_ctor_get(v_toAttributeImplCore_4050_, 1);
lean_inc(v_name_4060_);
if (v_isShared_4054_ == 0)
{
lean_ctor_set_tag(v___x_4053_, 1);
lean_ctor_set(v___x_4053_, 1, v_newEntries_4055_);
v___x_4062_ = v___x_4053_;
goto v_reusejp_4061_;
}
else
{
lean_object* v_reuseFailAlloc_4067_; 
v_reuseFailAlloc_4067_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4067_, 0, v_fst_4051_);
lean_ctor_set(v_reuseFailAlloc_4067_, 1, v_newEntries_4055_);
v___x_4062_ = v_reuseFailAlloc_4067_;
goto v_reusejp_4061_;
}
v_reusejp_4061_:
{
lean_object* v___x_4063_; lean_object* v___x_4065_; 
v___x_4063_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1___redArg(v_map_4056_, v_name_4060_, v_snd_4049_);
if (v_isShared_4059_ == 0)
{
lean_ctor_set(v___x_4058_, 1, v___x_4063_);
lean_ctor_set(v___x_4058_, 0, v___x_4062_);
v___x_4065_ = v___x_4058_;
goto v_reusejp_4064_;
}
else
{
lean_object* v_reuseFailAlloc_4066_; 
v_reuseFailAlloc_4066_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4066_, 0, v___x_4062_);
lean_ctor_set(v_reuseFailAlloc_4066_, 1, v___x_4063_);
v___x_4065_ = v_reuseFailAlloc_4066_;
goto v_reusejp_4064_;
}
v_reusejp_4064_:
{
return v___x_4065_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn___lam__0_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(lean_object* v_x_4071_, lean_object* v_s_4072_){
_start:
{
lean_object* v_newEntries_4073_; lean_object* v___x_4074_; lean_object* v___x_4075_; lean_object* v___x_4076_; 
v_newEntries_4073_ = lean_ctor_get(v_s_4072_, 0);
lean_inc(v_newEntries_4073_);
lean_dec_ref(v_s_4072_);
v___x_4074_ = l_List_reverse___redArg(v_newEntries_4073_);
v___x_4075_ = lean_array_mk(v___x_4074_);
lean_inc_ref_n(v___x_4075_, 2);
v___x_4076_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4076_, 0, v___x_4075_);
lean_ctor_set(v___x_4076_, 1, v___x_4075_);
lean_ctor_set(v___x_4076_, 2, v___x_4075_);
return v___x_4076_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn___lam__0_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2____boxed(lean_object* v_x_4077_, lean_object* v_s_4078_){
_start:
{
lean_object* v_res_4079_; 
v_res_4079_ = l___private_Lean_Attributes_0__Lean_initFn___lam__0_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(v_x_4077_, v_s_4078_);
lean_dec_ref(v_x_4077_);
return v_res_4079_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn___lam__1_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(lean_object* v_s_4080_){
_start:
{
lean_object* v_newEntries_4081_; lean_object* v___x_4083_; uint8_t v_isShared_4084_; uint8_t v_isSharedCheck_4092_; 
v_newEntries_4081_ = lean_ctor_get(v_s_4080_, 0);
v_isSharedCheck_4092_ = !lean_is_exclusive(v_s_4080_);
if (v_isSharedCheck_4092_ == 0)
{
lean_object* v_unused_4093_; 
v_unused_4093_ = lean_ctor_get(v_s_4080_, 1);
lean_dec(v_unused_4093_);
v___x_4083_ = v_s_4080_;
v_isShared_4084_ = v_isSharedCheck_4092_;
goto v_resetjp_4082_;
}
else
{
lean_inc(v_newEntries_4081_);
lean_dec(v_s_4080_);
v___x_4083_ = lean_box(0);
v_isShared_4084_ = v_isSharedCheck_4092_;
goto v_resetjp_4082_;
}
v_resetjp_4082_:
{
lean_object* v___x_4085_; lean_object* v___x_4086_; lean_object* v___x_4087_; lean_object* v___x_4088_; lean_object* v___x_4090_; 
v___x_4085_ = ((lean_object*)(l_Lean_registerTagAttribute___lam__2___closed__4));
v___x_4086_ = l_List_lengthTR___redArg(v_newEntries_4081_);
lean_dec(v_newEntries_4081_);
v___x_4087_ = l_Nat_reprFast(v___x_4086_);
v___x_4088_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4088_, 0, v___x_4087_);
if (v_isShared_4084_ == 0)
{
lean_ctor_set_tag(v___x_4083_, 5);
lean_ctor_set(v___x_4083_, 1, v___x_4088_);
lean_ctor_set(v___x_4083_, 0, v___x_4085_);
v___x_4090_ = v___x_4083_;
goto v_reusejp_4089_;
}
else
{
lean_object* v_reuseFailAlloc_4091_; 
v_reuseFailAlloc_4091_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4091_, 0, v___x_4085_);
lean_ctor_set(v_reuseFailAlloc_4091_, 1, v___x_4088_);
v___x_4090_ = v_reuseFailAlloc_4091_;
goto v_reusejp_4089_;
}
v_reusejp_4089_:
{
return v___x_4090_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn___lam__2_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(lean_object* v_s_4094_){
_start:
{
lean_object* v_newEntries_4095_; lean_object* v___x_4096_; lean_object* v___x_4097_; 
v_newEntries_4095_ = lean_ctor_get(v_s_4094_, 0);
lean_inc(v_newEntries_4095_);
lean_dec_ref(v_s_4094_);
v___x_4096_ = l_List_reverse___redArg(v_newEntries_4095_);
v___x_4097_ = lean_array_mk(v___x_4096_);
return v___x_4097_;
}
}
static lean_object* _init_l___private_Lean_Attributes_0__Lean_initFn___closed__7_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4107_; lean_object* v___x_4108_; lean_object* v___f_4109_; lean_object* v___f_4110_; lean_object* v___x_4111_; lean_object* v___x_4112_; lean_object* v___x_4113_; lean_object* v___x_4114_; lean_object* v___x_4115_; 
v___x_4107_ = lean_box(0);
v___x_4108_ = lean_box(2);
v___f_4109_ = ((lean_object*)(l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___f_4110_ = ((lean_object*)(l___private_Lean_Attributes_0__Lean_initFn___closed__0_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___x_4111_ = ((lean_object*)(l___private_Lean_Attributes_0__Lean_initFn___closed__6_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___x_4112_ = ((lean_object*)(l___private_Lean_Attributes_0__Lean_initFn___closed__5_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___x_4113_ = lean_alloc_closure((void*)(l___private_Lean_Attributes_0__Lean_AttributeExtension_mkInitial___boxed), 1, 0);
v___x_4114_ = ((lean_object*)(l___private_Lean_Attributes_0__Lean_initFn___closed__4_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___x_4115_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_4115_, 0, v___x_4114_);
lean_ctor_set(v___x_4115_, 1, v___x_4113_);
lean_ctor_set(v___x_4115_, 2, v___x_4112_);
lean_ctor_set(v___x_4115_, 3, v___x_4111_);
lean_ctor_set(v___x_4115_, 4, v___f_4110_);
lean_ctor_set(v___x_4115_, 5, v___f_4109_);
lean_ctor_set(v___x_4115_, 6, v___x_4108_);
lean_ctor_set(v___x_4115_, 7, v___x_4107_);
return v___x_4115_;
}
}
static lean_object* _init_l___private_Lean_Attributes_0__Lean_initFn___closed__8_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_4116_; lean_object* v___x_4117_; lean_object* v___x_4118_; 
v___f_4116_ = ((lean_object*)(l___private_Lean_Attributes_0__Lean_initFn___closed__2_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___x_4117_ = lean_obj_once(&l___private_Lean_Attributes_0__Lean_initFn___closed__7_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_, &l___private_Lean_Attributes_0__Lean_initFn___closed__7_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2__once, _init_l___private_Lean_Attributes_0__Lean_initFn___closed__7_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_);
v___x_4118_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4118_, 0, v___x_4117_);
lean_ctor_set(v___x_4118_, 1, v___f_4116_);
return v___x_4118_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4120_; lean_object* v___x_4121_; 
v___x_4120_ = lean_obj_once(&l___private_Lean_Attributes_0__Lean_initFn___closed__8_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_, &l___private_Lean_Attributes_0__Lean_initFn___closed__8_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2__once, _init_l___private_Lean_Attributes_0__Lean_initFn___closed__8_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_);
v___x_4121_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_4120_);
return v___x_4121_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2____boxed(lean_object* v_a_4122_){
_start:
{
lean_object* v_res_4123_; 
v_res_4123_ = l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_();
return v_res_4123_;
}
}
LEAN_EXPORT lean_object* lean_is_attribute(lean_object* v_n_4124_){
_start:
{
lean_object* v___x_4126_; lean_object* v___x_4127_; uint8_t v___x_4128_; lean_object* v___x_4129_; lean_object* v___x_4130_; 
v___x_4126_ = l_Lean_attributeMapRef;
v___x_4127_ = lean_st_ref_get(v___x_4126_);
v___x_4128_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(v___x_4127_, v_n_4124_);
lean_dec(v_n_4124_);
lean_dec(v___x_4127_);
v___x_4129_ = lean_box(v___x_4128_);
v___x_4130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4130_, 0, v___x_4129_);
return v___x_4130_;
}
}
LEAN_EXPORT lean_object* l_Lean_isBuiltinAttribute___boxed(lean_object* v_n_4131_, lean_object* v_a_4132_){
_start:
{
lean_object* v_res_4133_; 
v_res_4133_ = lean_is_attribute(v_n_4131_);
return v_res_4133_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_getBuiltinAttributeNames_spec__0(lean_object* v_x_4134_, lean_object* v_x_4135_){
_start:
{
if (lean_obj_tag(v_x_4135_) == 0)
{
return v_x_4134_;
}
else
{
lean_object* v_key_4136_; lean_object* v_tail_4137_; lean_object* v___x_4138_; 
v_key_4136_ = lean_ctor_get(v_x_4135_, 0);
v_tail_4137_ = lean_ctor_get(v_x_4135_, 2);
lean_inc(v_key_4136_);
v___x_4138_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4138_, 0, v_key_4136_);
lean_ctor_set(v___x_4138_, 1, v_x_4134_);
v_x_4134_ = v___x_4138_;
v_x_4135_ = v_tail_4137_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_getBuiltinAttributeNames_spec__0___boxed(lean_object* v_x_4140_, lean_object* v_x_4141_){
_start:
{
lean_object* v_res_4142_; 
v_res_4142_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_getBuiltinAttributeNames_spec__0(v_x_4140_, v_x_4141_);
lean_dec(v_x_4141_);
return v_res_4142_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1(lean_object* v_as_4143_, size_t v_i_4144_, size_t v_stop_4145_, lean_object* v_b_4146_){
_start:
{
uint8_t v___x_4147_; 
v___x_4147_ = lean_usize_dec_eq(v_i_4144_, v_stop_4145_);
if (v___x_4147_ == 0)
{
lean_object* v___x_4148_; lean_object* v___x_4149_; size_t v___x_4150_; size_t v___x_4151_; 
v___x_4148_ = lean_array_uget_borrowed(v_as_4143_, v_i_4144_);
v___x_4149_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_getBuiltinAttributeNames_spec__0(v_b_4146_, v___x_4148_);
v___x_4150_ = ((size_t)1ULL);
v___x_4151_ = lean_usize_add(v_i_4144_, v___x_4150_);
v_i_4144_ = v___x_4151_;
v_b_4146_ = v___x_4149_;
goto _start;
}
else
{
return v_b_4146_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1___boxed(lean_object* v_as_4153_, lean_object* v_i_4154_, lean_object* v_stop_4155_, lean_object* v_b_4156_){
_start:
{
size_t v_i_boxed_4157_; size_t v_stop_boxed_4158_; lean_object* v_res_4159_; 
v_i_boxed_4157_ = lean_unbox_usize(v_i_4154_);
lean_dec(v_i_4154_);
v_stop_boxed_4158_ = lean_unbox_usize(v_stop_4155_);
lean_dec(v_stop_4155_);
v_res_4159_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1(v_as_4153_, v_i_boxed_4157_, v_stop_boxed_4158_, v_b_4156_);
lean_dec_ref(v_as_4153_);
return v_res_4159_;
}
}
LEAN_EXPORT lean_object* l_Lean_getBuiltinAttributeNames(){
_start:
{
lean_object* v___x_4161_; lean_object* v___x_4162_; lean_object* v_buckets_4163_; lean_object* v___x_4164_; lean_object* v___x_4165_; lean_object* v___x_4166_; uint8_t v___x_4167_; 
v___x_4161_ = l_Lean_attributeMapRef;
v___x_4162_ = lean_st_ref_get(v___x_4161_);
v_buckets_4163_ = lean_ctor_get(v___x_4162_, 1);
lean_inc_ref(v_buckets_4163_);
lean_dec(v___x_4162_);
v___x_4164_ = lean_box(0);
v___x_4165_ = lean_unsigned_to_nat(0u);
v___x_4166_ = lean_array_get_size(v_buckets_4163_);
v___x_4167_ = lean_nat_dec_lt(v___x_4165_, v___x_4166_);
if (v___x_4167_ == 0)
{
lean_object* v___x_4168_; 
lean_dec_ref(v_buckets_4163_);
v___x_4168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4168_, 0, v___x_4164_);
return v___x_4168_;
}
else
{
uint8_t v___x_4169_; 
v___x_4169_ = lean_nat_dec_le(v___x_4166_, v___x_4166_);
if (v___x_4169_ == 0)
{
if (v___x_4167_ == 0)
{
lean_object* v___x_4170_; 
lean_dec_ref(v_buckets_4163_);
v___x_4170_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4170_, 0, v___x_4164_);
return v___x_4170_;
}
else
{
size_t v___x_4171_; size_t v___x_4172_; lean_object* v___x_4173_; lean_object* v___x_4174_; 
v___x_4171_ = ((size_t)0ULL);
v___x_4172_ = lean_usize_of_nat(v___x_4166_);
v___x_4173_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1(v_buckets_4163_, v___x_4171_, v___x_4172_, v___x_4164_);
lean_dec_ref(v_buckets_4163_);
v___x_4174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4174_, 0, v___x_4173_);
return v___x_4174_;
}
}
else
{
size_t v___x_4175_; size_t v___x_4176_; lean_object* v___x_4177_; lean_object* v___x_4178_; 
v___x_4175_ = ((size_t)0ULL);
v___x_4176_ = lean_usize_of_nat(v___x_4166_);
v___x_4177_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1(v_buckets_4163_, v___x_4175_, v___x_4176_, v___x_4164_);
lean_dec_ref(v_buckets_4163_);
v___x_4178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4178_, 0, v___x_4177_);
return v___x_4178_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getBuiltinAttributeNames___boxed(lean_object* v_a_4179_){
_start:
{
lean_object* v_res_4180_; 
v_res_4180_ = l_Lean_getBuiltinAttributeNames();
return v_res_4180_;
}
}
LEAN_EXPORT lean_object* l_Lean_getBuiltinAttributeImpl(lean_object* v_attrName_4182_){
_start:
{
lean_object* v___x_4184_; lean_object* v___x_4185_; lean_object* v___x_4186_; 
v___x_4184_ = l_Lean_attributeMapRef;
v___x_4185_ = lean_st_ref_get(v___x_4184_);
v___x_4186_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(v___x_4185_, v_attrName_4182_);
lean_dec(v___x_4185_);
if (lean_obj_tag(v___x_4186_) == 0)
{
lean_object* v___x_4187_; uint8_t v___x_4188_; lean_object* v___x_4189_; lean_object* v___x_4190_; lean_object* v___x_4191_; lean_object* v___x_4192_; lean_object* v___x_4193_; lean_object* v___x_4194_; 
v___x_4187_ = ((lean_object*)(l_Lean_getBuiltinAttributeImpl___closed__0));
v___x_4188_ = 1;
v___x_4189_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_attrName_4182_, v___x_4188_);
v___x_4190_ = lean_string_append(v___x_4187_, v___x_4189_);
lean_dec_ref(v___x_4189_);
v___x_4191_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__4));
v___x_4192_ = lean_string_append(v___x_4190_, v___x_4191_);
v___x_4193_ = lean_mk_io_user_error(v___x_4192_);
v___x_4194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4194_, 0, v___x_4193_);
return v___x_4194_;
}
else
{
lean_object* v_val_4195_; lean_object* v___x_4197_; uint8_t v_isShared_4198_; uint8_t v_isSharedCheck_4202_; 
lean_dec(v_attrName_4182_);
v_val_4195_ = lean_ctor_get(v___x_4186_, 0);
v_isSharedCheck_4202_ = !lean_is_exclusive(v___x_4186_);
if (v_isSharedCheck_4202_ == 0)
{
v___x_4197_ = v___x_4186_;
v_isShared_4198_ = v_isSharedCheck_4202_;
goto v_resetjp_4196_;
}
else
{
lean_inc(v_val_4195_);
lean_dec(v___x_4186_);
v___x_4197_ = lean_box(0);
v_isShared_4198_ = v_isSharedCheck_4202_;
goto v_resetjp_4196_;
}
v_resetjp_4196_:
{
lean_object* v___x_4200_; 
if (v_isShared_4198_ == 0)
{
lean_ctor_set_tag(v___x_4197_, 0);
v___x_4200_ = v___x_4197_;
goto v_reusejp_4199_;
}
else
{
lean_object* v_reuseFailAlloc_4201_; 
v_reuseFailAlloc_4201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4201_, 0, v_val_4195_);
v___x_4200_ = v_reuseFailAlloc_4201_;
goto v_reusejp_4199_;
}
v_reusejp_4199_:
{
return v___x_4200_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getBuiltinAttributeImpl___boxed(lean_object* v_attrName_4203_, lean_object* v_a_4204_){
_start:
{
lean_object* v_res_4205_; 
v_res_4205_ = l_Lean_getBuiltinAttributeImpl(v_attrName_4203_);
return v_res_4205_;
}
}
LEAN_EXPORT lean_object* lean_attribute_application_time(lean_object* v_n_4206_){
_start:
{
lean_object* v___x_4208_; 
v___x_4208_ = l_Lean_getBuiltinAttributeImpl(v_n_4206_);
if (lean_obj_tag(v___x_4208_) == 0)
{
lean_object* v_a_4209_; lean_object* v___x_4211_; uint8_t v_isShared_4212_; uint8_t v_isSharedCheck_4219_; 
v_a_4209_ = lean_ctor_get(v___x_4208_, 0);
v_isSharedCheck_4219_ = !lean_is_exclusive(v___x_4208_);
if (v_isSharedCheck_4219_ == 0)
{
v___x_4211_ = v___x_4208_;
v_isShared_4212_ = v_isSharedCheck_4219_;
goto v_resetjp_4210_;
}
else
{
lean_inc(v_a_4209_);
lean_dec(v___x_4208_);
v___x_4211_ = lean_box(0);
v_isShared_4212_ = v_isSharedCheck_4219_;
goto v_resetjp_4210_;
}
v_resetjp_4210_:
{
lean_object* v_toAttributeImplCore_4213_; uint8_t v_applicationTime_4214_; lean_object* v___x_4215_; lean_object* v___x_4217_; 
v_toAttributeImplCore_4213_ = lean_ctor_get(v_a_4209_, 0);
lean_inc_ref(v_toAttributeImplCore_4213_);
lean_dec(v_a_4209_);
v_applicationTime_4214_ = lean_ctor_get_uint8(v_toAttributeImplCore_4213_, sizeof(void*)*3);
lean_dec_ref(v_toAttributeImplCore_4213_);
v___x_4215_ = lean_box(v_applicationTime_4214_);
if (v_isShared_4212_ == 0)
{
lean_ctor_set(v___x_4211_, 0, v___x_4215_);
v___x_4217_ = v___x_4211_;
goto v_reusejp_4216_;
}
else
{
lean_object* v_reuseFailAlloc_4218_; 
v_reuseFailAlloc_4218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4218_, 0, v___x_4215_);
v___x_4217_ = v_reuseFailAlloc_4218_;
goto v_reusejp_4216_;
}
v_reusejp_4216_:
{
return v___x_4217_;
}
}
}
else
{
lean_object* v_a_4220_; lean_object* v___x_4222_; uint8_t v_isShared_4223_; uint8_t v_isSharedCheck_4227_; 
v_a_4220_ = lean_ctor_get(v___x_4208_, 0);
v_isSharedCheck_4227_ = !lean_is_exclusive(v___x_4208_);
if (v_isSharedCheck_4227_ == 0)
{
v___x_4222_ = v___x_4208_;
v_isShared_4223_ = v_isSharedCheck_4227_;
goto v_resetjp_4221_;
}
else
{
lean_inc(v_a_4220_);
lean_dec(v___x_4208_);
v___x_4222_ = lean_box(0);
v_isShared_4223_ = v_isSharedCheck_4227_;
goto v_resetjp_4221_;
}
v_resetjp_4221_:
{
lean_object* v___x_4225_; 
if (v_isShared_4223_ == 0)
{
v___x_4225_ = v___x_4222_;
goto v_reusejp_4224_;
}
else
{
lean_object* v_reuseFailAlloc_4226_; 
v_reuseFailAlloc_4226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4226_, 0, v_a_4220_);
v___x_4225_ = v_reuseFailAlloc_4226_;
goto v_reusejp_4224_;
}
v_reusejp_4224_:
{
return v___x_4225_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getBuiltinAttributeApplicationTime___boxed(lean_object* v_n_4228_, lean_object* v_a_4229_){
_start:
{
lean_object* v_res_4230_; 
v_res_4230_ = lean_attribute_application_time(v_n_4228_);
return v_res_4230_;
}
}
LEAN_EXPORT uint8_t l_Lean_isAttribute(lean_object* v_env_4231_, lean_object* v_attrName_4232_){
_start:
{
lean_object* v___x_4233_; lean_object* v_toEnvExtension_4234_; lean_object* v_asyncMode_4235_; lean_object* v___x_4236_; lean_object* v___x_4237_; lean_object* v___x_4238_; lean_object* v_map_4239_; uint8_t v___x_4240_; 
v___x_4233_ = l_Lean_attributeExtension;
v_toEnvExtension_4234_ = lean_ctor_get(v___x_4233_, 0);
v_asyncMode_4235_ = lean_ctor_get(v_toEnvExtension_4234_, 2);
v___x_4236_ = l_Lean_instInhabitedAttributeExtensionState_default;
v___x_4237_ = lean_box(0);
v___x_4238_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_4236_, v___x_4233_, v_env_4231_, v_asyncMode_4235_, v___x_4237_);
v_map_4239_ = lean_ctor_get(v___x_4238_, 1);
lean_inc_ref(v_map_4239_);
lean_dec(v___x_4238_);
v___x_4240_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(v_map_4239_, v_attrName_4232_);
lean_dec_ref(v_map_4239_);
return v___x_4240_;
}
}
LEAN_EXPORT lean_object* l_Lean_isAttribute___boxed(lean_object* v_env_4241_, lean_object* v_attrName_4242_){
_start:
{
uint8_t v_res_4243_; lean_object* v_r_4244_; 
v_res_4243_ = l_Lean_isAttribute(v_env_4241_, v_attrName_4242_);
lean_dec(v_attrName_4242_);
v_r_4244_ = lean_box(v_res_4243_);
return v_r_4244_;
}
}
LEAN_EXPORT lean_object* l_Lean_getAttributeNames(lean_object* v_env_4245_){
_start:
{
lean_object* v___x_4246_; lean_object* v_toEnvExtension_4247_; lean_object* v_asyncMode_4248_; lean_object* v___x_4249_; lean_object* v___x_4250_; lean_object* v___x_4251_; lean_object* v_map_4252_; lean_object* v_buckets_4253_; lean_object* v___x_4254_; lean_object* v___x_4255_; lean_object* v___x_4256_; uint8_t v___x_4257_; 
v___x_4246_ = l_Lean_attributeExtension;
v_toEnvExtension_4247_ = lean_ctor_get(v___x_4246_, 0);
v_asyncMode_4248_ = lean_ctor_get(v_toEnvExtension_4247_, 2);
v___x_4249_ = l_Lean_instInhabitedAttributeExtensionState_default;
v___x_4250_ = lean_box(0);
v___x_4251_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_4249_, v___x_4246_, v_env_4245_, v_asyncMode_4248_, v___x_4250_);
v_map_4252_ = lean_ctor_get(v___x_4251_, 1);
lean_inc_ref(v_map_4252_);
lean_dec(v___x_4251_);
v_buckets_4253_ = lean_ctor_get(v_map_4252_, 1);
lean_inc_ref(v_buckets_4253_);
lean_dec_ref(v_map_4252_);
v___x_4254_ = lean_box(0);
v___x_4255_ = lean_unsigned_to_nat(0u);
v___x_4256_ = lean_array_get_size(v_buckets_4253_);
v___x_4257_ = lean_nat_dec_lt(v___x_4255_, v___x_4256_);
if (v___x_4257_ == 0)
{
lean_dec_ref(v_buckets_4253_);
return v___x_4254_;
}
else
{
uint8_t v___x_4258_; 
v___x_4258_ = lean_nat_dec_le(v___x_4256_, v___x_4256_);
if (v___x_4258_ == 0)
{
if (v___x_4257_ == 0)
{
lean_dec_ref(v_buckets_4253_);
return v___x_4254_;
}
else
{
size_t v___x_4259_; size_t v___x_4260_; lean_object* v___x_4261_; 
v___x_4259_ = ((size_t)0ULL);
v___x_4260_ = lean_usize_of_nat(v___x_4256_);
v___x_4261_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1(v_buckets_4253_, v___x_4259_, v___x_4260_, v___x_4254_);
lean_dec_ref(v_buckets_4253_);
return v___x_4261_;
}
}
else
{
size_t v___x_4262_; size_t v___x_4263_; lean_object* v___x_4264_; 
v___x_4262_ = ((size_t)0ULL);
v___x_4263_ = lean_usize_of_nat(v___x_4256_);
v___x_4264_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1(v_buckets_4253_, v___x_4262_, v___x_4263_, v___x_4254_);
lean_dec_ref(v_buckets_4253_);
return v___x_4264_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getAttributeImpl(lean_object* v_env_4265_, lean_object* v_attrName_4266_){
_start:
{
lean_object* v___x_4267_; lean_object* v_toEnvExtension_4268_; lean_object* v_asyncMode_4269_; lean_object* v___x_4270_; lean_object* v___x_4271_; lean_object* v___x_4272_; lean_object* v_map_4273_; lean_object* v___x_4274_; 
v___x_4267_ = l_Lean_attributeExtension;
v_toEnvExtension_4268_ = lean_ctor_get(v___x_4267_, 0);
v_asyncMode_4269_ = lean_ctor_get(v_toEnvExtension_4268_, 2);
v___x_4270_ = l_Lean_instInhabitedAttributeExtensionState_default;
v___x_4271_ = lean_box(0);
v___x_4272_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_4270_, v___x_4267_, v_env_4265_, v_asyncMode_4269_, v___x_4271_);
v_map_4273_ = lean_ctor_get(v___x_4272_, 1);
lean_inc_ref(v_map_4273_);
lean_dec(v___x_4272_);
v___x_4274_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(v_map_4273_, v_attrName_4266_);
lean_dec_ref(v_map_4273_);
if (lean_obj_tag(v___x_4274_) == 0)
{
lean_object* v___x_4275_; uint8_t v___x_4276_; lean_object* v___x_4277_; lean_object* v___x_4278_; lean_object* v___x_4279_; lean_object* v___x_4280_; lean_object* v___x_4281_; 
v___x_4275_ = ((lean_object*)(l_Lean_getBuiltinAttributeImpl___closed__0));
v___x_4276_ = 1;
v___x_4277_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_attrName_4266_, v___x_4276_);
v___x_4278_ = lean_string_append(v___x_4275_, v___x_4277_);
lean_dec_ref(v___x_4277_);
v___x_4279_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__4));
v___x_4280_ = lean_string_append(v___x_4278_, v___x_4279_);
v___x_4281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4281_, 0, v___x_4280_);
return v___x_4281_;
}
else
{
lean_object* v_val_4282_; lean_object* v___x_4284_; uint8_t v_isShared_4285_; uint8_t v_isSharedCheck_4289_; 
lean_dec(v_attrName_4266_);
v_val_4282_ = lean_ctor_get(v___x_4274_, 0);
v_isSharedCheck_4289_ = !lean_is_exclusive(v___x_4274_);
if (v_isSharedCheck_4289_ == 0)
{
v___x_4284_ = v___x_4274_;
v_isShared_4285_ = v_isSharedCheck_4289_;
goto v_resetjp_4283_;
}
else
{
lean_inc(v_val_4282_);
lean_dec(v___x_4274_);
v___x_4284_ = lean_box(0);
v_isShared_4285_ = v_isSharedCheck_4289_;
goto v_resetjp_4283_;
}
v_resetjp_4283_:
{
lean_object* v___x_4287_; 
if (v_isShared_4285_ == 0)
{
v___x_4287_ = v___x_4284_;
goto v_reusejp_4286_;
}
else
{
lean_object* v_reuseFailAlloc_4288_; 
v_reuseFailAlloc_4288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4288_, 0, v_val_4282_);
v___x_4287_ = v_reuseFailAlloc_4288_;
goto v_reusejp_4286_;
}
v_reusejp_4286_:
{
return v___x_4287_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerAttributeOfBuilder(lean_object* v_env_4290_, lean_object* v_builderId_4291_, lean_object* v_ref_4292_, lean_object* v_args_4293_){
_start:
{
lean_object* v_entry_4295_; lean_object* v___x_4296_; 
v_entry_4295_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_entry_4295_, 0, v_builderId_4291_);
lean_ctor_set(v_entry_4295_, 1, v_ref_4292_);
lean_ctor_set(v_entry_4295_, 2, v_args_4293_);
lean_inc_ref(v_entry_4295_);
v___x_4296_ = l_Lean_mkAttributeImplOfEntry(v_entry_4295_);
if (lean_obj_tag(v___x_4296_) == 0)
{
lean_object* v_a_4297_; lean_object* v___x_4299_; uint8_t v_isShared_4300_; uint8_t v_isSharedCheck_4322_; 
v_a_4297_ = lean_ctor_get(v___x_4296_, 0);
v_isSharedCheck_4322_ = !lean_is_exclusive(v___x_4296_);
if (v_isSharedCheck_4322_ == 0)
{
v___x_4299_ = v___x_4296_;
v_isShared_4300_ = v_isSharedCheck_4322_;
goto v_resetjp_4298_;
}
else
{
lean_inc(v_a_4297_);
lean_dec(v___x_4296_);
v___x_4299_ = lean_box(0);
v_isShared_4300_ = v_isSharedCheck_4322_;
goto v_resetjp_4298_;
}
v_resetjp_4298_:
{
lean_object* v_toAttributeImplCore_4301_; lean_object* v_name_4302_; uint8_t v___x_4303_; 
v_toAttributeImplCore_4301_ = lean_ctor_get(v_a_4297_, 0);
v_name_4302_ = lean_ctor_get(v_toAttributeImplCore_4301_, 1);
lean_inc_ref(v_env_4290_);
v___x_4303_ = l_Lean_isAttribute(v_env_4290_, v_name_4302_);
if (v___x_4303_ == 0)
{
lean_object* v___x_4304_; lean_object* v_toEnvExtension_4305_; lean_object* v_asyncMode_4306_; lean_object* v___x_4307_; lean_object* v___x_4308_; lean_object* v___x_4309_; lean_object* v___x_4311_; 
v___x_4304_ = l_Lean_attributeExtension;
v_toEnvExtension_4305_ = lean_ctor_get(v___x_4304_, 0);
v_asyncMode_4306_ = lean_ctor_get(v_toEnvExtension_4305_, 2);
v___x_4307_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4307_, 0, v_entry_4295_);
lean_ctor_set(v___x_4307_, 1, v_a_4297_);
v___x_4308_ = lean_box(0);
v___x_4309_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_4304_, v_env_4290_, v___x_4307_, v_asyncMode_4306_, v___x_4308_);
if (v_isShared_4300_ == 0)
{
lean_ctor_set(v___x_4299_, 0, v___x_4309_);
v___x_4311_ = v___x_4299_;
goto v_reusejp_4310_;
}
else
{
lean_object* v_reuseFailAlloc_4312_; 
v_reuseFailAlloc_4312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4312_, 0, v___x_4309_);
v___x_4311_ = v_reuseFailAlloc_4312_;
goto v_reusejp_4310_;
}
v_reusejp_4310_:
{
return v___x_4311_;
}
}
else
{
lean_object* v___x_4313_; lean_object* v___x_4314_; lean_object* v___x_4315_; lean_object* v___x_4316_; lean_object* v___x_4317_; lean_object* v___x_4318_; lean_object* v___x_4320_; 
lean_inc(v_name_4302_);
lean_dec(v_a_4297_);
lean_dec_ref(v_entry_4295_);
lean_dec_ref(v_env_4290_);
v___x_4313_ = ((lean_object*)(l_Lean_registerBuiltinAttribute___closed__2));
v___x_4314_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_4302_, v___x_4303_);
v___x_4315_ = lean_string_append(v___x_4313_, v___x_4314_);
lean_dec_ref(v___x_4314_);
v___x_4316_ = ((lean_object*)(l_Lean_registerBuiltinAttribute___closed__3));
v___x_4317_ = lean_string_append(v___x_4315_, v___x_4316_);
v___x_4318_ = lean_mk_io_user_error(v___x_4317_);
if (v_isShared_4300_ == 0)
{
lean_ctor_set_tag(v___x_4299_, 1);
lean_ctor_set(v___x_4299_, 0, v___x_4318_);
v___x_4320_ = v___x_4299_;
goto v_reusejp_4319_;
}
else
{
lean_object* v_reuseFailAlloc_4321_; 
v_reuseFailAlloc_4321_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4321_, 0, v___x_4318_);
v___x_4320_ = v_reuseFailAlloc_4321_;
goto v_reusejp_4319_;
}
v_reusejp_4319_:
{
return v___x_4320_;
}
}
}
}
else
{
lean_object* v_a_4323_; lean_object* v___x_4325_; uint8_t v_isShared_4326_; uint8_t v_isSharedCheck_4330_; 
lean_dec_ref(v_entry_4295_);
lean_dec_ref(v_env_4290_);
v_a_4323_ = lean_ctor_get(v___x_4296_, 0);
v_isSharedCheck_4330_ = !lean_is_exclusive(v___x_4296_);
if (v_isSharedCheck_4330_ == 0)
{
v___x_4325_ = v___x_4296_;
v_isShared_4326_ = v_isSharedCheck_4330_;
goto v_resetjp_4324_;
}
else
{
lean_inc(v_a_4323_);
lean_dec(v___x_4296_);
v___x_4325_ = lean_box(0);
v_isShared_4326_ = v_isSharedCheck_4330_;
goto v_resetjp_4324_;
}
v_resetjp_4324_:
{
lean_object* v___x_4328_; 
if (v_isShared_4326_ == 0)
{
v___x_4328_ = v___x_4325_;
goto v_reusejp_4327_;
}
else
{
lean_object* v_reuseFailAlloc_4329_; 
v_reuseFailAlloc_4329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4329_, 0, v_a_4323_);
v___x_4328_ = v_reuseFailAlloc_4329_;
goto v_reusejp_4327_;
}
v_reusejp_4327_:
{
return v___x_4328_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerAttributeOfBuilder___boxed(lean_object* v_env_4331_, lean_object* v_builderId_4332_, lean_object* v_ref_4333_, lean_object* v_args_4334_, lean_object* v_a_4335_){
_start:
{
lean_object* v_res_4336_; 
v_res_4336_ = l_Lean_registerAttributeOfBuilder(v_env_4331_, v_builderId_4332_, v_ref_4333_, v_args_4334_);
return v_res_4336_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg(lean_object* v_x_4337_, lean_object* v___y_4338_, lean_object* v___y_4339_){
_start:
{
if (lean_obj_tag(v_x_4337_) == 0)
{
lean_object* v_a_4341_; lean_object* v___x_4342_; lean_object* v___x_4343_; 
v_a_4341_ = lean_ctor_get(v_x_4337_, 0);
lean_inc(v_a_4341_);
lean_dec_ref(v_x_4337_);
v___x_4342_ = l_Lean_stringToMessageData(v_a_4341_);
v___x_4343_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0_spec__0___redArg(v___x_4342_, v___y_4338_, v___y_4339_);
return v___x_4343_;
}
else
{
lean_object* v_a_4344_; lean_object* v___x_4346_; uint8_t v_isShared_4347_; uint8_t v_isSharedCheck_4351_; 
v_a_4344_ = lean_ctor_get(v_x_4337_, 0);
v_isSharedCheck_4351_ = !lean_is_exclusive(v_x_4337_);
if (v_isSharedCheck_4351_ == 0)
{
v___x_4346_ = v_x_4337_;
v_isShared_4347_ = v_isSharedCheck_4351_;
goto v_resetjp_4345_;
}
else
{
lean_inc(v_a_4344_);
lean_dec(v_x_4337_);
v___x_4346_ = lean_box(0);
v_isShared_4347_ = v_isSharedCheck_4351_;
goto v_resetjp_4345_;
}
v_resetjp_4345_:
{
lean_object* v___x_4349_; 
if (v_isShared_4347_ == 0)
{
lean_ctor_set_tag(v___x_4346_, 0);
v___x_4349_ = v___x_4346_;
goto v_reusejp_4348_;
}
else
{
lean_object* v_reuseFailAlloc_4350_; 
v_reuseFailAlloc_4350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4350_, 0, v_a_4344_);
v___x_4349_ = v_reuseFailAlloc_4350_;
goto v_reusejp_4348_;
}
v_reusejp_4348_:
{
return v___x_4349_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg___boxed(lean_object* v_x_4352_, lean_object* v___y_4353_, lean_object* v___y_4354_, lean_object* v___y_4355_){
_start:
{
lean_object* v_res_4356_; 
v_res_4356_ = l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg(v_x_4352_, v___y_4353_, v___y_4354_);
lean_dec(v___y_4354_);
lean_dec_ref(v___y_4353_);
return v_res_4356_;
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_add(lean_object* v_declName_4357_, lean_object* v_attrName_4358_, lean_object* v_stx_4359_, uint8_t v_kind_4360_, lean_object* v_a_4361_, lean_object* v_a_4362_){
_start:
{
lean_object* v___x_4364_; lean_object* v_env_4365_; lean_object* v___x_4366_; lean_object* v___x_4367_; 
v___x_4364_ = lean_st_ref_get(v_a_4362_);
v_env_4365_ = lean_ctor_get(v___x_4364_, 0);
lean_inc_ref(v_env_4365_);
lean_dec(v___x_4364_);
v___x_4366_ = l_Lean_getAttributeImpl(v_env_4365_, v_attrName_4358_);
v___x_4367_ = l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg(v___x_4366_, v_a_4361_, v_a_4362_);
if (lean_obj_tag(v___x_4367_) == 0)
{
lean_object* v_a_4368_; lean_object* v_add_4369_; lean_object* v___x_4370_; lean_object* v___x_4371_; 
v_a_4368_ = lean_ctor_get(v___x_4367_, 0);
lean_inc(v_a_4368_);
lean_dec_ref(v___x_4367_);
v_add_4369_ = lean_ctor_get(v_a_4368_, 1);
lean_inc_ref(v_add_4369_);
lean_dec(v_a_4368_);
v___x_4370_ = lean_box(v_kind_4360_);
lean_inc(v_a_4362_);
lean_inc_ref(v_a_4361_);
v___x_4371_ = lean_apply_6(v_add_4369_, v_declName_4357_, v_stx_4359_, v___x_4370_, v_a_4361_, v_a_4362_, lean_box(0));
return v___x_4371_;
}
else
{
lean_object* v_a_4372_; lean_object* v___x_4374_; uint8_t v_isShared_4375_; uint8_t v_isSharedCheck_4379_; 
lean_dec(v_stx_4359_);
lean_dec(v_declName_4357_);
v_a_4372_ = lean_ctor_get(v___x_4367_, 0);
v_isSharedCheck_4379_ = !lean_is_exclusive(v___x_4367_);
if (v_isSharedCheck_4379_ == 0)
{
v___x_4374_ = v___x_4367_;
v_isShared_4375_ = v_isSharedCheck_4379_;
goto v_resetjp_4373_;
}
else
{
lean_inc(v_a_4372_);
lean_dec(v___x_4367_);
v___x_4374_ = lean_box(0);
v_isShared_4375_ = v_isSharedCheck_4379_;
goto v_resetjp_4373_;
}
v_resetjp_4373_:
{
lean_object* v___x_4377_; 
if (v_isShared_4375_ == 0)
{
v___x_4377_ = v___x_4374_;
goto v_reusejp_4376_;
}
else
{
lean_object* v_reuseFailAlloc_4378_; 
v_reuseFailAlloc_4378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4378_, 0, v_a_4372_);
v___x_4377_ = v_reuseFailAlloc_4378_;
goto v_reusejp_4376_;
}
v_reusejp_4376_:
{
return v___x_4377_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_add___boxed(lean_object* v_declName_4380_, lean_object* v_attrName_4381_, lean_object* v_stx_4382_, lean_object* v_kind_4383_, lean_object* v_a_4384_, lean_object* v_a_4385_, lean_object* v_a_4386_){
_start:
{
uint8_t v_kind_boxed_4387_; lean_object* v_res_4388_; 
v_kind_boxed_4387_ = lean_unbox(v_kind_4383_);
v_res_4388_ = l_Lean_Attribute_add(v_declName_4380_, v_attrName_4381_, v_stx_4382_, v_kind_boxed_4387_, v_a_4384_, v_a_4385_);
lean_dec(v_a_4385_);
lean_dec_ref(v_a_4384_);
return v_res_4388_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0(lean_object* v_00_u03b1_4389_, lean_object* v_x_4390_, lean_object* v___y_4391_, lean_object* v___y_4392_){
_start:
{
lean_object* v___x_4394_; 
v___x_4394_ = l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg(v_x_4390_, v___y_4391_, v___y_4392_);
return v___x_4394_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___boxed(lean_object* v_00_u03b1_4395_, lean_object* v_x_4396_, lean_object* v___y_4397_, lean_object* v___y_4398_, lean_object* v___y_4399_){
_start:
{
lean_object* v_res_4400_; 
v_res_4400_ = l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0(v_00_u03b1_4395_, v_x_4396_, v___y_4397_, v___y_4398_);
lean_dec(v___y_4398_);
lean_dec_ref(v___y_4397_);
return v_res_4400_;
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_erase(lean_object* v_declName_4401_, lean_object* v_attrName_4402_, lean_object* v_a_4403_, lean_object* v_a_4404_){
_start:
{
lean_object* v___x_4406_; lean_object* v_env_4407_; lean_object* v___x_4408_; lean_object* v___x_4409_; 
v___x_4406_ = lean_st_ref_get(v_a_4404_);
v_env_4407_ = lean_ctor_get(v___x_4406_, 0);
lean_inc_ref(v_env_4407_);
lean_dec(v___x_4406_);
v___x_4408_ = l_Lean_getAttributeImpl(v_env_4407_, v_attrName_4402_);
v___x_4409_ = l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg(v___x_4408_, v_a_4403_, v_a_4404_);
if (lean_obj_tag(v___x_4409_) == 0)
{
lean_object* v_a_4410_; lean_object* v_erase_4411_; lean_object* v___x_4412_; 
v_a_4410_ = lean_ctor_get(v___x_4409_, 0);
lean_inc(v_a_4410_);
lean_dec_ref(v___x_4409_);
v_erase_4411_ = lean_ctor_get(v_a_4410_, 2);
lean_inc_ref(v_erase_4411_);
lean_dec(v_a_4410_);
lean_inc(v_a_4404_);
lean_inc_ref(v_a_4403_);
v___x_4412_ = lean_apply_4(v_erase_4411_, v_declName_4401_, v_a_4403_, v_a_4404_, lean_box(0));
return v___x_4412_;
}
else
{
lean_object* v_a_4413_; lean_object* v___x_4415_; uint8_t v_isShared_4416_; uint8_t v_isSharedCheck_4420_; 
lean_dec(v_declName_4401_);
v_a_4413_ = lean_ctor_get(v___x_4409_, 0);
v_isSharedCheck_4420_ = !lean_is_exclusive(v___x_4409_);
if (v_isSharedCheck_4420_ == 0)
{
v___x_4415_ = v___x_4409_;
v_isShared_4416_ = v_isSharedCheck_4420_;
goto v_resetjp_4414_;
}
else
{
lean_inc(v_a_4413_);
lean_dec(v___x_4409_);
v___x_4415_ = lean_box(0);
v_isShared_4416_ = v_isSharedCheck_4420_;
goto v_resetjp_4414_;
}
v_resetjp_4414_:
{
lean_object* v___x_4418_; 
if (v_isShared_4416_ == 0)
{
v___x_4418_ = v___x_4415_;
goto v_reusejp_4417_;
}
else
{
lean_object* v_reuseFailAlloc_4419_; 
v_reuseFailAlloc_4419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4419_, 0, v_a_4413_);
v___x_4418_ = v_reuseFailAlloc_4419_;
goto v_reusejp_4417_;
}
v_reusejp_4417_:
{
return v___x_4418_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_erase___boxed(lean_object* v_declName_4421_, lean_object* v_attrName_4422_, lean_object* v_a_4423_, lean_object* v_a_4424_, lean_object* v_a_4425_){
_start:
{
lean_object* v_res_4426_; 
v_res_4426_ = l_Lean_Attribute_erase(v_declName_4421_, v_attrName_4422_, v_a_4423_, v_a_4424_);
lean_dec(v_a_4424_);
lean_dec_ref(v_a_4423_);
return v_res_4426_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_updateEnvAttributesImpl_spec__0(lean_object* v_x_4427_, lean_object* v_x_4428_){
_start:
{
if (lean_obj_tag(v_x_4428_) == 0)
{
return v_x_4427_;
}
else
{
lean_object* v_key_4429_; lean_object* v_value_4430_; lean_object* v_tail_4431_; lean_object* v_newEntries_4432_; lean_object* v_map_4433_; uint8_t v___x_4434_; 
v_key_4429_ = lean_ctor_get(v_x_4428_, 0);
lean_inc(v_key_4429_);
v_value_4430_ = lean_ctor_get(v_x_4428_, 1);
lean_inc(v_value_4430_);
v_tail_4431_ = lean_ctor_get(v_x_4428_, 2);
lean_inc(v_tail_4431_);
lean_dec_ref(v_x_4428_);
v_newEntries_4432_ = lean_ctor_get(v_x_4427_, 0);
v_map_4433_ = lean_ctor_get(v_x_4427_, 1);
v___x_4434_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(v_map_4433_, v_key_4429_);
if (v___x_4434_ == 0)
{
lean_object* v___x_4436_; uint8_t v_isShared_4437_; uint8_t v_isSharedCheck_4443_; 
lean_inc_ref(v_map_4433_);
lean_inc(v_newEntries_4432_);
v_isSharedCheck_4443_ = !lean_is_exclusive(v_x_4427_);
if (v_isSharedCheck_4443_ == 0)
{
lean_object* v_unused_4444_; lean_object* v_unused_4445_; 
v_unused_4444_ = lean_ctor_get(v_x_4427_, 1);
lean_dec(v_unused_4444_);
v_unused_4445_ = lean_ctor_get(v_x_4427_, 0);
lean_dec(v_unused_4445_);
v___x_4436_ = v_x_4427_;
v_isShared_4437_ = v_isSharedCheck_4443_;
goto v_resetjp_4435_;
}
else
{
lean_dec(v_x_4427_);
v___x_4436_ = lean_box(0);
v_isShared_4437_ = v_isSharedCheck_4443_;
goto v_resetjp_4435_;
}
v_resetjp_4435_:
{
lean_object* v___x_4438_; lean_object* v___x_4440_; 
v___x_4438_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1___redArg(v_map_4433_, v_key_4429_, v_value_4430_);
if (v_isShared_4437_ == 0)
{
lean_ctor_set(v___x_4436_, 1, v___x_4438_);
v___x_4440_ = v___x_4436_;
goto v_reusejp_4439_;
}
else
{
lean_object* v_reuseFailAlloc_4442_; 
v_reuseFailAlloc_4442_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4442_, 0, v_newEntries_4432_);
lean_ctor_set(v_reuseFailAlloc_4442_, 1, v___x_4438_);
v___x_4440_ = v_reuseFailAlloc_4442_;
goto v_reusejp_4439_;
}
v_reusejp_4439_:
{
v_x_4427_ = v___x_4440_;
v_x_4428_ = v_tail_4431_;
goto _start;
}
}
}
else
{
lean_dec(v_value_4430_);
lean_dec(v_key_4429_);
v_x_4428_ = v_tail_4431_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_updateEnvAttributesImpl_spec__1(lean_object* v_as_4447_, size_t v_i_4448_, size_t v_stop_4449_, lean_object* v_b_4450_){
_start:
{
uint8_t v___x_4451_; 
v___x_4451_ = lean_usize_dec_eq(v_i_4448_, v_stop_4449_);
if (v___x_4451_ == 0)
{
lean_object* v___x_4452_; lean_object* v___x_4453_; size_t v___x_4454_; size_t v___x_4455_; 
v___x_4452_ = lean_array_uget_borrowed(v_as_4447_, v_i_4448_);
lean_inc(v___x_4452_);
v___x_4453_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_updateEnvAttributesImpl_spec__0(v_b_4450_, v___x_4452_);
v___x_4454_ = ((size_t)1ULL);
v___x_4455_ = lean_usize_add(v_i_4448_, v___x_4454_);
v_i_4448_ = v___x_4455_;
v_b_4450_ = v___x_4453_;
goto _start;
}
else
{
return v_b_4450_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_updateEnvAttributesImpl_spec__1___boxed(lean_object* v_as_4457_, lean_object* v_i_4458_, lean_object* v_stop_4459_, lean_object* v_b_4460_){
_start:
{
size_t v_i_boxed_4461_; size_t v_stop_boxed_4462_; lean_object* v_res_4463_; 
v_i_boxed_4461_ = lean_unbox_usize(v_i_4458_);
lean_dec(v_i_4458_);
v_stop_boxed_4462_ = lean_unbox_usize(v_stop_4459_);
lean_dec(v_stop_4459_);
v_res_4463_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_updateEnvAttributesImpl_spec__1(v_as_4457_, v_i_boxed_4461_, v_stop_boxed_4462_, v_b_4460_);
lean_dec_ref(v_as_4457_);
return v_res_4463_;
}
}
LEAN_EXPORT lean_object* lean_update_env_attributes(lean_object* v_env_4464_){
_start:
{
lean_object* v___x_4466_; lean_object* v___x_4467_; lean_object* v___x_4468_; lean_object* v___y_4470_; lean_object* v_toEnvExtension_4473_; lean_object* v_asyncMode_4474_; lean_object* v_buckets_4475_; lean_object* v___x_4476_; lean_object* v___x_4477_; lean_object* v___x_4478_; lean_object* v___x_4479_; lean_object* v___x_4480_; uint8_t v___x_4481_; 
v___x_4466_ = l_Lean_attributeMapRef;
v___x_4467_ = lean_st_ref_get(v___x_4466_);
v___x_4468_ = l_Lean_attributeExtension;
v_toEnvExtension_4473_ = lean_ctor_get(v___x_4468_, 0);
v_asyncMode_4474_ = lean_ctor_get(v_toEnvExtension_4473_, 2);
v_buckets_4475_ = lean_ctor_get(v___x_4467_, 1);
lean_inc_ref(v_buckets_4475_);
lean_dec(v___x_4467_);
v___x_4476_ = l_Lean_instInhabitedAttributeExtensionState_default;
v___x_4477_ = lean_box(0);
lean_inc_ref(v_env_4464_);
v___x_4478_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_4476_, v___x_4468_, v_env_4464_, v_asyncMode_4474_, v___x_4477_);
v___x_4479_ = lean_unsigned_to_nat(0u);
v___x_4480_ = lean_array_get_size(v_buckets_4475_);
v___x_4481_ = lean_nat_dec_lt(v___x_4479_, v___x_4480_);
if (v___x_4481_ == 0)
{
lean_dec_ref(v_buckets_4475_);
v___y_4470_ = v___x_4478_;
goto v___jp_4469_;
}
else
{
uint8_t v___x_4482_; 
v___x_4482_ = lean_nat_dec_le(v___x_4480_, v___x_4480_);
if (v___x_4482_ == 0)
{
if (v___x_4481_ == 0)
{
lean_dec_ref(v_buckets_4475_);
v___y_4470_ = v___x_4478_;
goto v___jp_4469_;
}
else
{
size_t v___x_4483_; size_t v___x_4484_; lean_object* v___x_4485_; 
v___x_4483_ = ((size_t)0ULL);
v___x_4484_ = lean_usize_of_nat(v___x_4480_);
v___x_4485_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_updateEnvAttributesImpl_spec__1(v_buckets_4475_, v___x_4483_, v___x_4484_, v___x_4478_);
lean_dec_ref(v_buckets_4475_);
v___y_4470_ = v___x_4485_;
goto v___jp_4469_;
}
}
else
{
size_t v___x_4486_; size_t v___x_4487_; lean_object* v___x_4488_; 
v___x_4486_ = ((size_t)0ULL);
v___x_4487_ = lean_usize_of_nat(v___x_4480_);
v___x_4488_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_updateEnvAttributesImpl_spec__1(v_buckets_4475_, v___x_4486_, v___x_4487_, v___x_4478_);
lean_dec_ref(v_buckets_4475_);
v___y_4470_ = v___x_4488_;
goto v___jp_4469_;
}
}
v___jp_4469_:
{
lean_object* v___x_4471_; lean_object* v___x_4472_; 
v___x_4471_ = l_Lean_PersistentEnvExtension_setState___redArg(v___x_4468_, v_env_4464_, v___y_4470_);
v___x_4472_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4472_, 0, v___x_4471_);
return v___x_4472_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_updateEnvAttributesImpl___boxed(lean_object* v_env_4489_, lean_object* v_a_4490_){
_start:
{
lean_object* v_res_4491_; 
v_res_4491_ = lean_update_env_attributes(v_env_4489_);
return v_res_4491_;
}
}
LEAN_EXPORT lean_object* lean_get_num_attributes(){
_start:
{
lean_object* v___x_4493_; lean_object* v___x_4494_; lean_object* v_size_4495_; lean_object* v___x_4496_; 
v___x_4493_ = l_Lean_attributeMapRef;
v___x_4494_ = lean_st_ref_get(v___x_4493_);
v_size_4495_ = lean_ctor_get(v___x_4494_, 0);
lean_inc(v_size_4495_);
lean_dec(v___x_4494_);
v___x_4496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4496_, 0, v_size_4495_);
return v___x_4496_;
}
}
LEAN_EXPORT lean_object* l_Lean_getNumBuiltinAttributesImpl___boxed(lean_object* v_a_4497_){
_start:
{
lean_object* v_res_4498_; 
v_res_4498_ = lean_get_num_attributes();
return v_res_4498_;
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
