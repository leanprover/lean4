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
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t l_Lean_Name_quickLt(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_initializing();
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
extern lean_object* l_Lean_instInhabitedMessageData_default;
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Environment_evalConst___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Array_reverse___redArg(lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_instInhabitedEnvExtension_default(lean_object*);
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
extern lean_object* l_Lean_ResolveName_backward_privateInPublic_warn;
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_Lean_Syntax_isNatLit_x3f(lean_object*);
uint8_t l_Lean_isMarkedMeta(lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_addParenHeuristic(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
uint8_t v___x_607_; 
v___x_607_ = l_Lean_initializing();
if (v___x_607_ == 0)
{
lean_object* v___x_608_; lean_object* v___x_609_; 
lean_dec(v_name_605_);
lean_dec_ref(v_attr_600_);
v___x_608_ = lean_obj_once(&l_Lean_registerBuiltinAttribute___closed__1, &l_Lean_registerBuiltinAttribute___closed__1_once, _init_l_Lean_registerBuiltinAttribute___closed__1);
v___x_609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_609_, 0, v___x_608_);
return v___x_609_;
}
else
{
lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; 
v___x_610_ = lean_st_ref_take(v___x_602_);
v___x_611_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1___redArg(v___x_610_, v_name_605_, v_attr_600_);
v___x_612_ = lean_st_ref_set(v___x_602_, v___x_611_);
v___x_613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_613_, 0, v___x_612_);
return v___x_613_;
}
}
else
{
lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; 
lean_dec_ref(v_attr_600_);
v___x_614_ = ((lean_object*)(l_Lean_registerBuiltinAttribute___closed__2));
v___x_615_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_605_, v___x_606_);
v___x_616_ = lean_string_append(v___x_614_, v___x_615_);
lean_dec_ref(v___x_615_);
v___x_617_ = ((lean_object*)(l_Lean_registerBuiltinAttribute___closed__3));
v___x_618_ = lean_string_append(v___x_616_, v___x_617_);
v___x_619_ = lean_mk_io_user_error(v___x_618_);
v___x_620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_620_, 0, v___x_619_);
return v___x_620_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerBuiltinAttribute___boxed(lean_object* v_attr_621_, lean_object* v_a_622_){
_start:
{
lean_object* v_res_623_; 
v_res_623_ = l_Lean_registerBuiltinAttribute(v_attr_621_);
return v_res_623_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0(lean_object* v_00_u03b2_624_, lean_object* v_m_625_, lean_object* v_a_626_){
_start:
{
uint8_t v___x_627_; 
v___x_627_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(v_m_625_, v_a_626_);
return v___x_627_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___boxed(lean_object* v_00_u03b2_628_, lean_object* v_m_629_, lean_object* v_a_630_){
_start:
{
uint8_t v_res_631_; lean_object* v_r_632_; 
v_res_631_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0(v_00_u03b2_628_, v_m_629_, v_a_630_);
lean_dec(v_a_630_);
lean_dec_ref(v_m_629_);
v_r_632_ = lean_box(v_res_631_);
return v_r_632_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1(lean_object* v_00_u03b2_633_, lean_object* v_m_634_, lean_object* v_a_635_, lean_object* v_b_636_){
_start:
{
lean_object* v___x_637_; 
v___x_637_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1___redArg(v_m_634_, v_a_635_, v_b_636_);
return v___x_637_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0_spec__0(lean_object* v_00_u03b2_638_, lean_object* v_a_639_, lean_object* v_x_640_){
_start:
{
uint8_t v___x_641_; 
v___x_641_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0_spec__0___redArg(v_a_639_, v_x_640_);
return v___x_641_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0_spec__0___boxed(lean_object* v_00_u03b2_642_, lean_object* v_a_643_, lean_object* v_x_644_){
_start:
{
uint8_t v_res_645_; lean_object* v_r_646_; 
v_res_645_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0_spec__0(v_00_u03b2_642_, v_a_643_, v_x_644_);
lean_dec(v_x_644_);
lean_dec(v_a_643_);
v_r_646_ = lean_box(v_res_645_);
return v_r_646_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2(lean_object* v_00_u03b2_647_, lean_object* v_data_648_){
_start:
{
lean_object* v___x_649_; 
v___x_649_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2___redArg(v_data_648_);
return v___x_649_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__3(lean_object* v_00_u03b2_650_, lean_object* v_a_651_, lean_object* v_b_652_, lean_object* v_x_653_){
_start:
{
lean_object* v___x_654_; 
v___x_654_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__3___redArg(v_a_651_, v_b_652_, v_x_653_);
return v___x_654_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_655_, lean_object* v_i_656_, lean_object* v_source_657_, lean_object* v_target_658_){
_start:
{
lean_object* v___x_659_; 
v___x_659_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2_spec__3___redArg(v_i_656_, v_source_657_, v_target_658_);
return v___x_659_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_660_, lean_object* v_x_661_, lean_object* v_x_662_){
_start:
{
lean_object* v___x_663_; 
v___x_663_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2_spec__3_spec__4___redArg(v_x_661_, v_x_662_);
return v___x_663_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg(lean_object* v_ref_664_, lean_object* v_msg_665_, lean_object* v___y_666_, lean_object* v___y_667_){
_start:
{
lean_object* v_fileName_669_; lean_object* v_fileMap_670_; lean_object* v_options_671_; lean_object* v_currRecDepth_672_; lean_object* v_maxRecDepth_673_; lean_object* v_ref_674_; lean_object* v_currNamespace_675_; lean_object* v_openDecls_676_; lean_object* v_initHeartbeats_677_; lean_object* v_maxHeartbeats_678_; lean_object* v_quotContext_679_; lean_object* v_currMacroScope_680_; uint8_t v_diag_681_; lean_object* v_cancelTk_x3f_682_; uint8_t v_suppressElabErrors_683_; lean_object* v_inheritedTraceOptions_684_; lean_object* v_ref_685_; lean_object* v___x_686_; lean_object* v___x_687_; 
v_fileName_669_ = lean_ctor_get(v___y_666_, 0);
v_fileMap_670_ = lean_ctor_get(v___y_666_, 1);
v_options_671_ = lean_ctor_get(v___y_666_, 2);
v_currRecDepth_672_ = lean_ctor_get(v___y_666_, 3);
v_maxRecDepth_673_ = lean_ctor_get(v___y_666_, 4);
v_ref_674_ = lean_ctor_get(v___y_666_, 5);
v_currNamespace_675_ = lean_ctor_get(v___y_666_, 6);
v_openDecls_676_ = lean_ctor_get(v___y_666_, 7);
v_initHeartbeats_677_ = lean_ctor_get(v___y_666_, 8);
v_maxHeartbeats_678_ = lean_ctor_get(v___y_666_, 9);
v_quotContext_679_ = lean_ctor_get(v___y_666_, 10);
v_currMacroScope_680_ = lean_ctor_get(v___y_666_, 11);
v_diag_681_ = lean_ctor_get_uint8(v___y_666_, sizeof(void*)*14);
v_cancelTk_x3f_682_ = lean_ctor_get(v___y_666_, 12);
v_suppressElabErrors_683_ = lean_ctor_get_uint8(v___y_666_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_684_ = lean_ctor_get(v___y_666_, 13);
v_ref_685_ = l_Lean_replaceRef(v_ref_664_, v_ref_674_);
lean_inc_ref(v_inheritedTraceOptions_684_);
lean_inc(v_cancelTk_x3f_682_);
lean_inc(v_currMacroScope_680_);
lean_inc(v_quotContext_679_);
lean_inc(v_maxHeartbeats_678_);
lean_inc(v_initHeartbeats_677_);
lean_inc(v_openDecls_676_);
lean_inc(v_currNamespace_675_);
lean_inc(v_maxRecDepth_673_);
lean_inc(v_currRecDepth_672_);
lean_inc_ref(v_options_671_);
lean_inc_ref(v_fileMap_670_);
lean_inc_ref(v_fileName_669_);
v___x_686_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_686_, 0, v_fileName_669_);
lean_ctor_set(v___x_686_, 1, v_fileMap_670_);
lean_ctor_set(v___x_686_, 2, v_options_671_);
lean_ctor_set(v___x_686_, 3, v_currRecDepth_672_);
lean_ctor_set(v___x_686_, 4, v_maxRecDepth_673_);
lean_ctor_set(v___x_686_, 5, v_ref_685_);
lean_ctor_set(v___x_686_, 6, v_currNamespace_675_);
lean_ctor_set(v___x_686_, 7, v_openDecls_676_);
lean_ctor_set(v___x_686_, 8, v_initHeartbeats_677_);
lean_ctor_set(v___x_686_, 9, v_maxHeartbeats_678_);
lean_ctor_set(v___x_686_, 10, v_quotContext_679_);
lean_ctor_set(v___x_686_, 11, v_currMacroScope_680_);
lean_ctor_set(v___x_686_, 12, v_cancelTk_x3f_682_);
lean_ctor_set(v___x_686_, 13, v_inheritedTraceOptions_684_);
lean_ctor_set_uint8(v___x_686_, sizeof(void*)*14, v_diag_681_);
lean_ctor_set_uint8(v___x_686_, sizeof(void*)*14 + 1, v_suppressElabErrors_683_);
v___x_687_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v_msg_665_, v___x_686_, v___y_667_);
lean_dec_ref_known(v___x_686_, 14);
return v___x_687_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg___boxed(lean_object* v_ref_688_, lean_object* v_msg_689_, lean_object* v___y_690_, lean_object* v___y_691_, lean_object* v___y_692_){
_start:
{
lean_object* v_res_693_; 
v_res_693_ = l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg(v_ref_688_, v_msg_689_, v___y_690_, v___y_691_);
lean_dec(v___y_691_);
lean_dec_ref(v___y_690_);
lean_dec(v_ref_688_);
return v_res_693_;
}
}
static lean_object* _init_l_Lean_Attribute_Builtin_ensureNoArgs___closed__4(void){
_start:
{
lean_object* v___x_702_; lean_object* v___x_703_; 
v___x_702_ = ((lean_object*)(l_Lean_Attribute_Builtin_ensureNoArgs___closed__3));
v___x_703_ = l_Lean_stringToMessageData(v___x_702_);
return v___x_703_;
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_ensureNoArgs(lean_object* v_stx_710_, lean_object* v_a_711_, lean_object* v_a_712_){
_start:
{
lean_object* v___x_714_; uint8_t v___y_725_; lean_object* v___x_731_; uint8_t v___x_732_; 
lean_inc(v_stx_710_);
v___x_714_ = l_Lean_Syntax_getKind(v_stx_710_);
v___x_731_ = ((lean_object*)(l_Lean_Attribute_Builtin_ensureNoArgs___closed__6));
v___x_732_ = lean_name_eq(v___x_714_, v___x_731_);
if (v___x_732_ == 0)
{
v___y_725_ = v___x_732_;
goto v___jp_724_;
}
else
{
lean_object* v___x_733_; lean_object* v___x_734_; uint8_t v___x_735_; 
v___x_733_ = lean_unsigned_to_nat(1u);
v___x_734_ = l_Lean_Syntax_getArg(v_stx_710_, v___x_733_);
v___x_735_ = l_Lean_Syntax_isNone(v___x_734_);
lean_dec(v___x_734_);
v___y_725_ = v___x_735_;
goto v___jp_724_;
}
v___jp_715_:
{
lean_object* v___x_716_; uint8_t v___x_717_; 
v___x_716_ = ((lean_object*)(l_Lean_Attribute_Builtin_ensureNoArgs___closed__2));
v___x_717_ = lean_name_eq(v___x_714_, v___x_716_);
lean_dec(v___x_714_);
if (v___x_717_ == 0)
{
if (lean_obj_tag(v_stx_710_) == 0)
{
lean_object* v___x_718_; lean_object* v___x_719_; 
v___x_718_ = lean_box(0);
v___x_719_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_719_, 0, v___x_718_);
return v___x_719_;
}
else
{
lean_object* v___x_720_; lean_object* v___x_721_; 
v___x_720_ = lean_obj_once(&l_Lean_Attribute_Builtin_ensureNoArgs___closed__4, &l_Lean_Attribute_Builtin_ensureNoArgs___closed__4_once, _init_l_Lean_Attribute_Builtin_ensureNoArgs___closed__4);
v___x_721_ = l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg(v_stx_710_, v___x_720_, v_a_711_, v_a_712_);
lean_dec(v_stx_710_);
return v___x_721_;
}
}
else
{
lean_object* v___x_722_; lean_object* v___x_723_; 
lean_dec(v_stx_710_);
v___x_722_ = lean_box(0);
v___x_723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_723_, 0, v___x_722_);
return v___x_723_;
}
}
v___jp_724_:
{
if (v___y_725_ == 0)
{
goto v___jp_715_;
}
else
{
lean_object* v___x_726_; lean_object* v___x_727_; uint8_t v___x_728_; 
v___x_726_ = lean_unsigned_to_nat(2u);
v___x_727_ = l_Lean_Syntax_getArg(v_stx_710_, v___x_726_);
v___x_728_ = l_Lean_Syntax_isNone(v___x_727_);
lean_dec(v___x_727_);
if (v___x_728_ == 0)
{
goto v___jp_715_;
}
else
{
lean_object* v___x_729_; lean_object* v___x_730_; 
lean_dec(v___x_714_);
lean_dec(v_stx_710_);
v___x_729_ = lean_box(0);
v___x_730_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_730_, 0, v___x_729_);
return v___x_730_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_ensureNoArgs___boxed(lean_object* v_stx_736_, lean_object* v_a_737_, lean_object* v_a_738_, lean_object* v_a_739_){
_start:
{
lean_object* v_res_740_; 
v_res_740_ = l_Lean_Attribute_Builtin_ensureNoArgs(v_stx_736_, v_a_737_, v_a_738_);
lean_dec(v_a_738_);
lean_dec_ref(v_a_737_);
return v_res_740_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0(lean_object* v_00_u03b1_741_, lean_object* v_ref_742_, lean_object* v_msg_743_, lean_object* v___y_744_, lean_object* v___y_745_){
_start:
{
lean_object* v___x_747_; 
v___x_747_ = l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg(v_ref_742_, v_msg_743_, v___y_744_, v___y_745_);
return v___x_747_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___boxed(lean_object* v_00_u03b1_748_, lean_object* v_ref_749_, lean_object* v_msg_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_){
_start:
{
lean_object* v_res_754_; 
v_res_754_ = l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0(v_00_u03b1_748_, v_ref_749_, v_msg_750_, v___y_751_, v___y_752_);
lean_dec(v___y_752_);
lean_dec_ref(v___y_751_);
lean_dec(v_ref_749_);
return v_res_754_;
}
}
static lean_object* _init_l_Lean_Attribute_Builtin_getIdent_x3f___closed__5(void){
_start:
{
lean_object* v___x_768_; lean_object* v___x_769_; 
v___x_768_ = ((lean_object*)(l_Lean_Attribute_Builtin_getIdent_x3f___closed__4));
v___x_769_ = l_Lean_stringToMessageData(v___x_768_);
return v___x_769_;
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getIdent_x3f(lean_object* v_stx_770_, lean_object* v_a_771_, lean_object* v_a_772_){
_start:
{
lean_object* v___x_782_; lean_object* v___x_783_; uint8_t v___x_784_; 
lean_inc(v_stx_770_);
v___x_782_ = l_Lean_Syntax_getKind(v_stx_770_);
v___x_783_ = ((lean_object*)(l_Lean_Attribute_Builtin_ensureNoArgs___closed__6));
v___x_784_ = lean_name_eq(v___x_782_, v___x_783_);
if (v___x_784_ == 0)
{
lean_object* v___x_785_; uint8_t v___x_786_; 
v___x_785_ = ((lean_object*)(l_Lean_Attribute_Builtin_getIdent_x3f___closed__1));
v___x_786_ = lean_name_eq(v___x_782_, v___x_785_);
if (v___x_786_ == 0)
{
lean_object* v___x_787_; uint8_t v___x_788_; 
v___x_787_ = ((lean_object*)(l_Lean_Attribute_Builtin_getIdent_x3f___closed__3));
v___x_788_ = lean_name_eq(v___x_782_, v___x_787_);
lean_dec(v___x_782_);
if (v___x_788_ == 0)
{
lean_object* v___x_789_; lean_object* v___x_790_; 
v___x_789_ = lean_obj_once(&l_Lean_Attribute_Builtin_getIdent_x3f___closed__5, &l_Lean_Attribute_Builtin_getIdent_x3f___closed__5_once, _init_l_Lean_Attribute_Builtin_getIdent_x3f___closed__5);
v___x_790_ = l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg(v_stx_770_, v___x_789_, v_a_771_, v_a_772_);
lean_dec(v_stx_770_);
return v___x_790_;
}
else
{
goto v___jp_774_;
}
}
else
{
lean_dec(v___x_782_);
goto v___jp_774_;
}
}
else
{
lean_object* v___x_791_; lean_object* v___x_792_; uint8_t v___x_793_; 
lean_dec(v___x_782_);
v___x_791_ = lean_unsigned_to_nat(1u);
v___x_792_ = l_Lean_Syntax_getArg(v_stx_770_, v___x_791_);
lean_dec(v_stx_770_);
v___x_793_ = l_Lean_Syntax_isNone(v___x_792_);
if (v___x_793_ == 0)
{
if (v___x_784_ == 0)
{
lean_dec(v___x_792_);
goto v___jp_779_;
}
else
{
lean_object* v___x_794_; lean_object* v___x_795_; uint8_t v___x_796_; 
v___x_794_ = lean_unsigned_to_nat(0u);
v___x_795_ = l_Lean_Syntax_getArg(v___x_792_, v___x_794_);
lean_dec(v___x_792_);
v___x_796_ = l_Lean_Syntax_isIdent(v___x_795_);
if (v___x_796_ == 0)
{
lean_dec(v___x_795_);
goto v___jp_779_;
}
else
{
lean_object* v___x_797_; lean_object* v___x_798_; 
v___x_797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_797_, 0, v___x_795_);
v___x_798_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_798_, 0, v___x_797_);
return v___x_798_;
}
}
}
else
{
lean_dec(v___x_792_);
goto v___jp_779_;
}
}
v___jp_774_:
{
lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; 
v___x_775_ = lean_unsigned_to_nat(1u);
v___x_776_ = l_Lean_Syntax_getArg(v_stx_770_, v___x_775_);
lean_dec(v_stx_770_);
v___x_777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_777_, 0, v___x_776_);
v___x_778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_778_, 0, v___x_777_);
return v___x_778_;
}
v___jp_779_:
{
lean_object* v___x_780_; lean_object* v___x_781_; 
v___x_780_ = lean_box(0);
v___x_781_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_781_, 0, v___x_780_);
return v___x_781_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getIdent_x3f___boxed(lean_object* v_stx_799_, lean_object* v_a_800_, lean_object* v_a_801_, lean_object* v_a_802_){
_start:
{
lean_object* v_res_803_; 
v_res_803_ = l_Lean_Attribute_Builtin_getIdent_x3f(v_stx_799_, v_a_800_, v_a_801_);
lean_dec(v_a_801_);
lean_dec_ref(v_a_800_);
return v_res_803_;
}
}
static lean_object* _init_l_Lean_Attribute_Builtin_getIdent___closed__1(void){
_start:
{
lean_object* v___x_805_; lean_object* v___x_806_; 
v___x_805_ = ((lean_object*)(l_Lean_Attribute_Builtin_getIdent___closed__0));
v___x_806_ = l_Lean_stringToMessageData(v___x_805_);
return v___x_806_;
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getIdent(lean_object* v_stx_807_, lean_object* v_a_808_, lean_object* v_a_809_){
_start:
{
lean_object* v___x_811_; 
lean_inc(v_stx_807_);
v___x_811_ = l_Lean_Attribute_Builtin_getIdent_x3f(v_stx_807_, v_a_808_, v_a_809_);
if (lean_obj_tag(v___x_811_) == 0)
{
lean_object* v_a_812_; lean_object* v___x_814_; uint8_t v_isShared_815_; uint8_t v_isSharedCheck_825_; 
v_a_812_ = lean_ctor_get(v___x_811_, 0);
v_isSharedCheck_825_ = !lean_is_exclusive(v___x_811_);
if (v_isSharedCheck_825_ == 0)
{
v___x_814_ = v___x_811_;
v_isShared_815_ = v_isSharedCheck_825_;
goto v_resetjp_813_;
}
else
{
lean_inc(v_a_812_);
lean_dec(v___x_811_);
v___x_814_ = lean_box(0);
v_isShared_815_ = v_isSharedCheck_825_;
goto v_resetjp_813_;
}
v_resetjp_813_:
{
if (lean_obj_tag(v_a_812_) == 0)
{
lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; 
lean_del_object(v___x_814_);
v___x_816_ = lean_obj_once(&l_Lean_Attribute_Builtin_getIdent___closed__1, &l_Lean_Attribute_Builtin_getIdent___closed__1_once, _init_l_Lean_Attribute_Builtin_getIdent___closed__1);
lean_inc(v_stx_807_);
v___x_817_ = l_Lean_MessageData_ofSyntax(v_stx_807_);
v___x_818_ = l_Lean_indentD(v___x_817_);
v___x_819_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_819_, 0, v___x_816_);
lean_ctor_set(v___x_819_, 1, v___x_818_);
v___x_820_ = l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg(v_stx_807_, v___x_819_, v_a_808_, v_a_809_);
lean_dec(v_stx_807_);
return v___x_820_;
}
else
{
lean_object* v_val_821_; lean_object* v___x_823_; 
lean_dec(v_stx_807_);
v_val_821_ = lean_ctor_get(v_a_812_, 0);
lean_inc(v_val_821_);
lean_dec_ref_known(v_a_812_, 1);
if (v_isShared_815_ == 0)
{
lean_ctor_set(v___x_814_, 0, v_val_821_);
v___x_823_ = v___x_814_;
goto v_reusejp_822_;
}
else
{
lean_object* v_reuseFailAlloc_824_; 
v_reuseFailAlloc_824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_824_, 0, v_val_821_);
v___x_823_ = v_reuseFailAlloc_824_;
goto v_reusejp_822_;
}
v_reusejp_822_:
{
return v___x_823_;
}
}
}
}
else
{
lean_object* v_a_826_; lean_object* v___x_828_; uint8_t v_isShared_829_; uint8_t v_isSharedCheck_833_; 
lean_dec(v_stx_807_);
v_a_826_ = lean_ctor_get(v___x_811_, 0);
v_isSharedCheck_833_ = !lean_is_exclusive(v___x_811_);
if (v_isSharedCheck_833_ == 0)
{
v___x_828_ = v___x_811_;
v_isShared_829_ = v_isSharedCheck_833_;
goto v_resetjp_827_;
}
else
{
lean_inc(v_a_826_);
lean_dec(v___x_811_);
v___x_828_ = lean_box(0);
v_isShared_829_ = v_isSharedCheck_833_;
goto v_resetjp_827_;
}
v_resetjp_827_:
{
lean_object* v___x_831_; 
if (v_isShared_829_ == 0)
{
v___x_831_ = v___x_828_;
goto v_reusejp_830_;
}
else
{
lean_object* v_reuseFailAlloc_832_; 
v_reuseFailAlloc_832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_832_, 0, v_a_826_);
v___x_831_ = v_reuseFailAlloc_832_;
goto v_reusejp_830_;
}
v_reusejp_830_:
{
return v___x_831_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getIdent___boxed(lean_object* v_stx_834_, lean_object* v_a_835_, lean_object* v_a_836_, lean_object* v_a_837_){
_start:
{
lean_object* v_res_838_; 
v_res_838_ = l_Lean_Attribute_Builtin_getIdent(v_stx_834_, v_a_835_, v_a_836_);
lean_dec(v_a_836_);
lean_dec_ref(v_a_835_);
return v_res_838_;
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getId_x3f(lean_object* v_stx_839_, lean_object* v_a_840_, lean_object* v_a_841_){
_start:
{
lean_object* v___x_843_; 
v___x_843_ = l_Lean_Attribute_Builtin_getIdent_x3f(v_stx_839_, v_a_840_, v_a_841_);
if (lean_obj_tag(v___x_843_) == 0)
{
lean_object* v_a_844_; lean_object* v___x_846_; uint8_t v_isShared_847_; uint8_t v_isSharedCheck_864_; 
v_a_844_ = lean_ctor_get(v___x_843_, 0);
v_isSharedCheck_864_ = !lean_is_exclusive(v___x_843_);
if (v_isSharedCheck_864_ == 0)
{
v___x_846_ = v___x_843_;
v_isShared_847_ = v_isSharedCheck_864_;
goto v_resetjp_845_;
}
else
{
lean_inc(v_a_844_);
lean_dec(v___x_843_);
v___x_846_ = lean_box(0);
v_isShared_847_ = v_isSharedCheck_864_;
goto v_resetjp_845_;
}
v_resetjp_845_:
{
if (lean_obj_tag(v_a_844_) == 0)
{
lean_object* v___x_848_; lean_object* v___x_850_; 
v___x_848_ = lean_box(0);
if (v_isShared_847_ == 0)
{
lean_ctor_set(v___x_846_, 0, v___x_848_);
v___x_850_ = v___x_846_;
goto v_reusejp_849_;
}
else
{
lean_object* v_reuseFailAlloc_851_; 
v_reuseFailAlloc_851_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_851_, 0, v___x_848_);
v___x_850_ = v_reuseFailAlloc_851_;
goto v_reusejp_849_;
}
v_reusejp_849_:
{
return v___x_850_;
}
}
else
{
lean_object* v_val_852_; lean_object* v___x_854_; uint8_t v_isShared_855_; uint8_t v_isSharedCheck_863_; 
v_val_852_ = lean_ctor_get(v_a_844_, 0);
v_isSharedCheck_863_ = !lean_is_exclusive(v_a_844_);
if (v_isSharedCheck_863_ == 0)
{
v___x_854_ = v_a_844_;
v_isShared_855_ = v_isSharedCheck_863_;
goto v_resetjp_853_;
}
else
{
lean_inc(v_val_852_);
lean_dec(v_a_844_);
v___x_854_ = lean_box(0);
v_isShared_855_ = v_isSharedCheck_863_;
goto v_resetjp_853_;
}
v_resetjp_853_:
{
lean_object* v___x_856_; lean_object* v___x_858_; 
v___x_856_ = l_Lean_Syntax_getId(v_val_852_);
lean_dec(v_val_852_);
if (v_isShared_855_ == 0)
{
lean_ctor_set(v___x_854_, 0, v___x_856_);
v___x_858_ = v___x_854_;
goto v_reusejp_857_;
}
else
{
lean_object* v_reuseFailAlloc_862_; 
v_reuseFailAlloc_862_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_862_, 0, v___x_856_);
v___x_858_ = v_reuseFailAlloc_862_;
goto v_reusejp_857_;
}
v_reusejp_857_:
{
lean_object* v___x_860_; 
if (v_isShared_847_ == 0)
{
lean_ctor_set(v___x_846_, 0, v___x_858_);
v___x_860_ = v___x_846_;
goto v_reusejp_859_;
}
else
{
lean_object* v_reuseFailAlloc_861_; 
v_reuseFailAlloc_861_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_861_, 0, v___x_858_);
v___x_860_ = v_reuseFailAlloc_861_;
goto v_reusejp_859_;
}
v_reusejp_859_:
{
return v___x_860_;
}
}
}
}
}
}
else
{
lean_object* v_a_865_; lean_object* v___x_867_; uint8_t v_isShared_868_; uint8_t v_isSharedCheck_872_; 
v_a_865_ = lean_ctor_get(v___x_843_, 0);
v_isSharedCheck_872_ = !lean_is_exclusive(v___x_843_);
if (v_isSharedCheck_872_ == 0)
{
v___x_867_ = v___x_843_;
v_isShared_868_ = v_isSharedCheck_872_;
goto v_resetjp_866_;
}
else
{
lean_inc(v_a_865_);
lean_dec(v___x_843_);
v___x_867_ = lean_box(0);
v_isShared_868_ = v_isSharedCheck_872_;
goto v_resetjp_866_;
}
v_resetjp_866_:
{
lean_object* v___x_870_; 
if (v_isShared_868_ == 0)
{
v___x_870_ = v___x_867_;
goto v_reusejp_869_;
}
else
{
lean_object* v_reuseFailAlloc_871_; 
v_reuseFailAlloc_871_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_871_, 0, v_a_865_);
v___x_870_ = v_reuseFailAlloc_871_;
goto v_reusejp_869_;
}
v_reusejp_869_:
{
return v___x_870_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getId_x3f___boxed(lean_object* v_stx_873_, lean_object* v_a_874_, lean_object* v_a_875_, lean_object* v_a_876_){
_start:
{
lean_object* v_res_877_; 
v_res_877_ = l_Lean_Attribute_Builtin_getId_x3f(v_stx_873_, v_a_874_, v_a_875_);
lean_dec(v_a_875_);
lean_dec_ref(v_a_874_);
return v_res_877_;
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getId(lean_object* v_stx_878_, lean_object* v_a_879_, lean_object* v_a_880_){
_start:
{
lean_object* v___x_882_; 
v___x_882_ = l_Lean_Attribute_Builtin_getIdent(v_stx_878_, v_a_879_, v_a_880_);
if (lean_obj_tag(v___x_882_) == 0)
{
lean_object* v_a_883_; lean_object* v___x_885_; uint8_t v_isShared_886_; uint8_t v_isSharedCheck_891_; 
v_a_883_ = lean_ctor_get(v___x_882_, 0);
v_isSharedCheck_891_ = !lean_is_exclusive(v___x_882_);
if (v_isSharedCheck_891_ == 0)
{
v___x_885_ = v___x_882_;
v_isShared_886_ = v_isSharedCheck_891_;
goto v_resetjp_884_;
}
else
{
lean_inc(v_a_883_);
lean_dec(v___x_882_);
v___x_885_ = lean_box(0);
v_isShared_886_ = v_isSharedCheck_891_;
goto v_resetjp_884_;
}
v_resetjp_884_:
{
lean_object* v___x_887_; lean_object* v___x_889_; 
v___x_887_ = l_Lean_Syntax_getId(v_a_883_);
lean_dec(v_a_883_);
if (v_isShared_886_ == 0)
{
lean_ctor_set(v___x_885_, 0, v___x_887_);
v___x_889_ = v___x_885_;
goto v_reusejp_888_;
}
else
{
lean_object* v_reuseFailAlloc_890_; 
v_reuseFailAlloc_890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_890_, 0, v___x_887_);
v___x_889_ = v_reuseFailAlloc_890_;
goto v_reusejp_888_;
}
v_reusejp_888_:
{
return v___x_889_;
}
}
}
else
{
lean_object* v_a_892_; lean_object* v___x_894_; uint8_t v_isShared_895_; uint8_t v_isSharedCheck_899_; 
v_a_892_ = lean_ctor_get(v___x_882_, 0);
v_isSharedCheck_899_ = !lean_is_exclusive(v___x_882_);
if (v_isSharedCheck_899_ == 0)
{
v___x_894_ = v___x_882_;
v_isShared_895_ = v_isSharedCheck_899_;
goto v_resetjp_893_;
}
else
{
lean_inc(v_a_892_);
lean_dec(v___x_882_);
v___x_894_ = lean_box(0);
v_isShared_895_ = v_isSharedCheck_899_;
goto v_resetjp_893_;
}
v_resetjp_893_:
{
lean_object* v___x_897_; 
if (v_isShared_895_ == 0)
{
v___x_897_ = v___x_894_;
goto v_reusejp_896_;
}
else
{
lean_object* v_reuseFailAlloc_898_; 
v_reuseFailAlloc_898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_898_, 0, v_a_892_);
v___x_897_ = v_reuseFailAlloc_898_;
goto v_reusejp_896_;
}
v_reusejp_896_:
{
return v___x_897_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getId___boxed(lean_object* v_stx_900_, lean_object* v_a_901_, lean_object* v_a_902_, lean_object* v_a_903_){
_start:
{
lean_object* v_res_904_; 
v_res_904_ = l_Lean_Attribute_Builtin_getId(v_stx_900_, v_a_901_, v_a_902_);
lean_dec(v_a_902_);
lean_dec_ref(v_a_901_);
return v_res_904_;
}
}
static lean_object* _init_l_Lean_getAttrParamOptPrio___closed__1(void){
_start:
{
lean_object* v___x_906_; lean_object* v___x_907_; 
v___x_906_ = ((lean_object*)(l_Lean_getAttrParamOptPrio___closed__0));
v___x_907_ = l_Lean_stringToMessageData(v___x_906_);
return v___x_907_;
}
}
LEAN_EXPORT lean_object* l_Lean_getAttrParamOptPrio(lean_object* v_optPrioStx_908_, lean_object* v_a_909_, lean_object* v_a_910_){
_start:
{
uint8_t v___x_912_; 
v___x_912_ = l_Lean_Syntax_isNone(v_optPrioStx_908_);
if (v___x_912_ == 0)
{
lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; 
v___x_913_ = lean_unsigned_to_nat(0u);
v___x_914_ = l_Lean_Syntax_getArg(v_optPrioStx_908_, v___x_913_);
v___x_915_ = l_Lean_Syntax_isNatLit_x3f(v___x_914_);
lean_dec(v___x_914_);
if (lean_obj_tag(v___x_915_) == 0)
{
lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; 
v___x_916_ = lean_obj_once(&l_Lean_getAttrParamOptPrio___closed__1, &l_Lean_getAttrParamOptPrio___closed__1_once, _init_l_Lean_getAttrParamOptPrio___closed__1);
lean_inc(v_optPrioStx_908_);
v___x_917_ = l_Lean_MessageData_ofSyntax(v_optPrioStx_908_);
v___x_918_ = l_Lean_indentD(v___x_917_);
v___x_919_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_919_, 0, v___x_916_);
lean_ctor_set(v___x_919_, 1, v___x_918_);
v___x_920_ = l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg(v_optPrioStx_908_, v___x_919_, v_a_909_, v_a_910_);
lean_dec(v_optPrioStx_908_);
return v___x_920_;
}
else
{
lean_object* v_val_921_; lean_object* v___x_923_; uint8_t v_isShared_924_; uint8_t v_isSharedCheck_928_; 
lean_dec(v_optPrioStx_908_);
v_val_921_ = lean_ctor_get(v___x_915_, 0);
v_isSharedCheck_928_ = !lean_is_exclusive(v___x_915_);
if (v_isSharedCheck_928_ == 0)
{
v___x_923_ = v___x_915_;
v_isShared_924_ = v_isSharedCheck_928_;
goto v_resetjp_922_;
}
else
{
lean_inc(v_val_921_);
lean_dec(v___x_915_);
v___x_923_ = lean_box(0);
v_isShared_924_ = v_isSharedCheck_928_;
goto v_resetjp_922_;
}
v_resetjp_922_:
{
lean_object* v___x_926_; 
if (v_isShared_924_ == 0)
{
lean_ctor_set_tag(v___x_923_, 0);
v___x_926_ = v___x_923_;
goto v_reusejp_925_;
}
else
{
lean_object* v_reuseFailAlloc_927_; 
v_reuseFailAlloc_927_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_927_, 0, v_val_921_);
v___x_926_ = v_reuseFailAlloc_927_;
goto v_reusejp_925_;
}
v_reusejp_925_:
{
return v___x_926_;
}
}
}
}
else
{
lean_object* v___x_929_; lean_object* v___x_930_; 
lean_dec(v_optPrioStx_908_);
v___x_929_ = lean_unsigned_to_nat(1000u);
v___x_930_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_930_, 0, v___x_929_);
return v___x_930_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getAttrParamOptPrio___boxed(lean_object* v_optPrioStx_931_, lean_object* v_a_932_, lean_object* v_a_933_, lean_object* v_a_934_){
_start:
{
lean_object* v_res_935_; 
v_res_935_ = l_Lean_getAttrParamOptPrio(v_optPrioStx_931_, v_a_932_, v_a_933_);
lean_dec(v_a_933_);
lean_dec_ref(v_a_932_);
return v_res_935_;
}
}
static lean_object* _init_l_Lean_Attribute_Builtin_getPrio___closed__1(void){
_start:
{
lean_object* v___x_937_; lean_object* v___x_938_; 
v___x_937_ = ((lean_object*)(l_Lean_Attribute_Builtin_getPrio___closed__0));
v___x_938_ = l_Lean_stringToMessageData(v___x_937_);
return v___x_938_;
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getPrio(lean_object* v_stx_939_, lean_object* v_a_940_, lean_object* v_a_941_){
_start:
{
lean_object* v___x_943_; lean_object* v___x_944_; uint8_t v___x_945_; 
lean_inc(v_stx_939_);
v___x_943_ = l_Lean_Syntax_getKind(v_stx_939_);
v___x_944_ = ((lean_object*)(l_Lean_Attribute_Builtin_ensureNoArgs___closed__6));
v___x_945_ = lean_name_eq(v___x_943_, v___x_944_);
lean_dec(v___x_943_);
if (v___x_945_ == 0)
{
lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; 
v___x_946_ = lean_obj_once(&l_Lean_Attribute_Builtin_getPrio___closed__1, &l_Lean_Attribute_Builtin_getPrio___closed__1_once, _init_l_Lean_Attribute_Builtin_getPrio___closed__1);
lean_inc(v_stx_939_);
v___x_947_ = l_Lean_MessageData_ofSyntax(v_stx_939_);
v___x_948_ = l_Lean_indentD(v___x_947_);
v___x_949_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_949_, 0, v___x_946_);
lean_ctor_set(v___x_949_, 1, v___x_948_);
v___x_950_ = l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg(v_stx_939_, v___x_949_, v_a_940_, v_a_941_);
lean_dec(v_stx_939_);
return v___x_950_;
}
else
{
lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; 
v___x_951_ = lean_unsigned_to_nat(1u);
v___x_952_ = l_Lean_Syntax_getArg(v_stx_939_, v___x_951_);
lean_dec(v_stx_939_);
v___x_953_ = l_Lean_getAttrParamOptPrio(v___x_952_, v_a_940_, v_a_941_);
return v___x_953_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getPrio___boxed(lean_object* v_stx_954_, lean_object* v_a_955_, lean_object* v_a_956_, lean_object* v_a_957_){
_start:
{
lean_object* v_res_958_; 
v_res_958_ = l_Lean_Attribute_Builtin_getPrio(v_stx_954_, v_a_955_, v_a_956_);
lean_dec(v_a_956_);
lean_dec_ref(v_a_955_);
return v_res_958_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__1(void){
_start:
{
lean_object* v___x_960_; lean_object* v___x_961_; 
v___x_960_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__0));
v___x_961_ = l_Lean_stringToMessageData(v___x_960_);
return v___x_961_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__3(void){
_start:
{
lean_object* v___x_963_; lean_object* v___x_964_; 
v___x_963_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__2));
v___x_964_ = l_Lean_stringToMessageData(v___x_963_);
return v___x_964_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__5(void){
_start:
{
lean_object* v___x_966_; lean_object* v___x_967_; 
v___x_966_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__4));
v___x_967_ = l_Lean_stringToMessageData(v___x_966_);
return v___x_967_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___redArg(lean_object* v_inst_968_, lean_object* v_inst_969_, lean_object* v_name_970_, uint8_t v_kind_971_){
_start:
{
lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___y_978_; 
v___x_972_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__1, &l_Lean_throwAttrMustBeGlobal___redArg___closed__1_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__1);
v___x_973_ = l_Lean_MessageData_ofName(v_name_970_);
v___x_974_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_974_, 0, v___x_972_);
lean_ctor_set(v___x_974_, 1, v___x_973_);
v___x_975_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__3, &l_Lean_throwAttrMustBeGlobal___redArg___closed__3_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__3);
v___x_976_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_976_, 0, v___x_974_);
lean_ctor_set(v___x_976_, 1, v___x_975_);
switch(v_kind_971_)
{
case 0:
{
lean_object* v___x_985_; 
v___x_985_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__0));
v___y_978_ = v___x_985_;
goto v___jp_977_;
}
case 1:
{
lean_object* v___x_986_; 
v___x_986_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__1));
v___y_978_ = v___x_986_;
goto v___jp_977_;
}
default: 
{
lean_object* v___x_987_; 
v___x_987_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__2));
v___y_978_ = v___x_987_;
goto v___jp_977_;
}
}
v___jp_977_:
{
lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; 
lean_inc_ref(v___y_978_);
v___x_979_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_979_, 0, v___y_978_);
v___x_980_ = l_Lean_MessageData_ofFormat(v___x_979_);
v___x_981_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_981_, 0, v___x_976_);
lean_ctor_set(v___x_981_, 1, v___x_980_);
v___x_982_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__5, &l_Lean_throwAttrMustBeGlobal___redArg___closed__5_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__5);
v___x_983_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_983_, 0, v___x_981_);
lean_ctor_set(v___x_983_, 1, v___x_982_);
v___x_984_ = l_Lean_throwError___redArg(v_inst_968_, v_inst_969_, v___x_983_);
return v___x_984_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___redArg___boxed(lean_object* v_inst_988_, lean_object* v_inst_989_, lean_object* v_name_990_, lean_object* v_kind_991_){
_start:
{
uint8_t v_kind_boxed_992_; lean_object* v_res_993_; 
v_kind_boxed_992_ = lean_unbox(v_kind_991_);
v_res_993_ = l_Lean_throwAttrMustBeGlobal___redArg(v_inst_988_, v_inst_989_, v_name_990_, v_kind_boxed_992_);
return v_res_993_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal(lean_object* v_m_994_, lean_object* v_inst_995_, lean_object* v_inst_996_, lean_object* v_00_u03b1_997_, lean_object* v_name_998_, uint8_t v_kind_999_){
_start:
{
lean_object* v___x_1000_; 
v___x_1000_ = l_Lean_throwAttrMustBeGlobal___redArg(v_inst_995_, v_inst_996_, v_name_998_, v_kind_999_);
return v___x_1000_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___boxed(lean_object* v_m_1001_, lean_object* v_inst_1002_, lean_object* v_inst_1003_, lean_object* v_00_u03b1_1004_, lean_object* v_name_1005_, lean_object* v_kind_1006_){
_start:
{
uint8_t v_kind_boxed_1007_; lean_object* v_res_1008_; 
v_kind_boxed_1007_ = lean_unbox(v_kind_1006_);
v_res_1008_ = l_Lean_throwAttrMustBeGlobal(v_m_1001_, v_inst_1002_, v_inst_1003_, v_00_u03b1_1004_, v_name_1005_, v_kind_boxed_1007_);
return v_res_1008_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1(void){
_start:
{
lean_object* v___x_1010_; lean_object* v___x_1011_; 
v___x_1010_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___redArg___closed__0));
v___x_1011_ = l_Lean_stringToMessageData(v___x_1010_);
return v___x_1011_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__3(void){
_start:
{
lean_object* v___x_1013_; lean_object* v___x_1014_; 
v___x_1013_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___redArg___closed__2));
v___x_1014_ = l_Lean_stringToMessageData(v___x_1013_);
return v___x_1014_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__5(void){
_start:
{
lean_object* v___x_1016_; lean_object* v___x_1017_; 
v___x_1016_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___redArg___closed__4));
v___x_1017_ = l_Lean_stringToMessageData(v___x_1016_);
return v___x_1017_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___redArg(lean_object* v_inst_1018_, lean_object* v_inst_1019_, lean_object* v_attrName_1020_, lean_object* v_declName_1021_){
_start:
{
lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; uint8_t v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; 
v___x_1022_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1);
v___x_1023_ = l_Lean_MessageData_ofName(v_attrName_1020_);
v___x_1024_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1024_, 0, v___x_1022_);
lean_ctor_set(v___x_1024_, 1, v___x_1023_);
v___x_1025_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__3, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__3_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__3);
v___x_1026_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1026_, 0, v___x_1024_);
lean_ctor_set(v___x_1026_, 1, v___x_1025_);
v___x_1027_ = 0;
v___x_1028_ = l_Lean_MessageData_ofConstName(v_declName_1021_, v___x_1027_);
v___x_1029_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1029_, 0, v___x_1026_);
lean_ctor_set(v___x_1029_, 1, v___x_1028_);
v___x_1030_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__5, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__5_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__5);
v___x_1031_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1031_, 0, v___x_1029_);
lean_ctor_set(v___x_1031_, 1, v___x_1030_);
v___x_1032_ = l_Lean_throwError___redArg(v_inst_1018_, v_inst_1019_, v___x_1031_);
return v___x_1032_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule(lean_object* v_m_1033_, lean_object* v_inst_1034_, lean_object* v_inst_1035_, lean_object* v_00_u03b1_1036_, lean_object* v_attrName_1037_, lean_object* v_declName_1038_){
_start:
{
lean_object* v___x_1039_; 
v___x_1039_ = l_Lean_throwAttrDeclInImportedModule___redArg(v_inst_1034_, v_inst_1035_, v_attrName_1037_, v_declName_1038_);
return v___x_1039_;
}
}
static lean_object* _init_l_Lean_throwAttrNotInAsyncCtx___redArg___closed__1(void){
_start:
{
lean_object* v___x_1041_; lean_object* v___x_1042_; 
v___x_1041_ = ((lean_object*)(l_Lean_throwAttrNotInAsyncCtx___redArg___closed__0));
v___x_1042_ = l_Lean_stringToMessageData(v___x_1041_);
return v___x_1042_;
}
}
static lean_object* _init_l_Lean_throwAttrNotInAsyncCtx___redArg___closed__3(void){
_start:
{
lean_object* v___x_1044_; lean_object* v___x_1045_; 
v___x_1044_ = ((lean_object*)(l_Lean_throwAttrNotInAsyncCtx___redArg___closed__2));
v___x_1045_ = l_Lean_stringToMessageData(v___x_1044_);
return v___x_1045_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___redArg(lean_object* v_inst_1046_, lean_object* v_inst_1047_, lean_object* v_attrName_1048_, lean_object* v_declName_1049_, lean_object* v_asyncPrefix_x3f_1050_){
_start:
{
lean_object* v___y_1052_; 
if (lean_obj_tag(v_asyncPrefix_x3f_1050_) == 0)
{
lean_object* v___x_1065_; 
v___x_1065_ = l_Lean_MessageData_nil;
v___y_1052_ = v___x_1065_;
goto v___jp_1051_;
}
else
{
lean_object* v_val_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; 
v_val_1066_ = lean_ctor_get(v_asyncPrefix_x3f_1050_, 0);
lean_inc(v_val_1066_);
lean_dec_ref_known(v_asyncPrefix_x3f_1050_, 1);
v___x_1067_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___redArg___closed__3, &l_Lean_throwAttrNotInAsyncCtx___redArg___closed__3_once, _init_l_Lean_throwAttrNotInAsyncCtx___redArg___closed__3);
v___x_1068_ = l_Lean_MessageData_ofName(v_val_1066_);
v___x_1069_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1069_, 0, v___x_1067_);
lean_ctor_set(v___x_1069_, 1, v___x_1068_);
v___x_1070_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__5, &l_Lean_throwAttrMustBeGlobal___redArg___closed__5_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__5);
v___x_1071_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1071_, 0, v___x_1069_);
lean_ctor_set(v___x_1071_, 1, v___x_1070_);
v___y_1052_ = v___x_1071_;
goto v___jp_1051_;
}
v___jp_1051_:
{
lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; uint8_t v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; 
v___x_1053_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1);
v___x_1054_ = l_Lean_MessageData_ofName(v_attrName_1048_);
v___x_1055_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1055_, 0, v___x_1053_);
lean_ctor_set(v___x_1055_, 1, v___x_1054_);
v___x_1056_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__3, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__3_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__3);
v___x_1057_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1057_, 0, v___x_1055_);
lean_ctor_set(v___x_1057_, 1, v___x_1056_);
v___x_1058_ = 0;
v___x_1059_ = l_Lean_MessageData_ofConstName(v_declName_1049_, v___x_1058_);
v___x_1060_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1060_, 0, v___x_1057_);
lean_ctor_set(v___x_1060_, 1, v___x_1059_);
v___x_1061_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___redArg___closed__1, &l_Lean_throwAttrNotInAsyncCtx___redArg___closed__1_once, _init_l_Lean_throwAttrNotInAsyncCtx___redArg___closed__1);
v___x_1062_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1062_, 0, v___x_1060_);
lean_ctor_set(v___x_1062_, 1, v___x_1061_);
v___x_1063_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1063_, 0, v___x_1062_);
lean_ctor_set(v___x_1063_, 1, v___y_1052_);
v___x_1064_ = l_Lean_throwError___redArg(v_inst_1046_, v_inst_1047_, v___x_1063_);
return v___x_1064_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx(lean_object* v_m_1072_, lean_object* v_inst_1073_, lean_object* v_inst_1074_, lean_object* v_00_u03b1_1075_, lean_object* v_attrName_1076_, lean_object* v_declName_1077_, lean_object* v_asyncPrefix_x3f_1078_){
_start:
{
lean_object* v___x_1079_; 
v___x_1079_ = l_Lean_throwAttrNotInAsyncCtx___redArg(v_inst_1073_, v_inst_1074_, v_attrName_1076_, v_declName_1077_, v_asyncPrefix_x3f_1078_);
return v___x_1079_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1(void){
_start:
{
lean_object* v___x_1081_; lean_object* v___x_1082_; 
v___x_1081_ = ((lean_object*)(l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__0));
v___x_1082_ = l_Lean_stringToMessageData(v___x_1081_);
return v___x_1082_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__3(void){
_start:
{
lean_object* v___x_1084_; lean_object* v___x_1085_; 
v___x_1084_ = ((lean_object*)(l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__2));
v___x_1085_ = l_Lean_stringToMessageData(v___x_1084_);
return v___x_1085_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__5(void){
_start:
{
lean_object* v___x_1087_; lean_object* v___x_1088_; 
v___x_1087_ = ((lean_object*)(l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__4));
v___x_1088_ = l_Lean_stringToMessageData(v___x_1087_);
return v___x_1088_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__7(void){
_start:
{
lean_object* v___x_1090_; lean_object* v___x_1091_; 
v___x_1090_ = ((lean_object*)(l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__6));
v___x_1091_ = l_Lean_stringToMessageData(v___x_1090_);
return v___x_1091_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclNotOfExpectedType___redArg(lean_object* v_inst_1092_, lean_object* v_inst_1093_, lean_object* v_attrName_1094_, lean_object* v_declName_1095_, lean_object* v_givenType_1096_, lean_object* v_expectedType_1097_){
_start:
{
lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; uint8_t v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; 
v___x_1098_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1);
v___x_1099_ = l_Lean_MessageData_ofName(v_attrName_1094_);
lean_inc_ref(v___x_1099_);
v___x_1100_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1100_, 0, v___x_1098_);
lean_ctor_set(v___x_1100_, 1, v___x_1099_);
v___x_1101_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1, &l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1);
v___x_1102_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1102_, 0, v___x_1100_);
lean_ctor_set(v___x_1102_, 1, v___x_1101_);
v___x_1103_ = 0;
v___x_1104_ = l_Lean_MessageData_ofConstName(v_declName_1095_, v___x_1103_);
v___x_1105_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1105_, 0, v___x_1102_);
lean_ctor_set(v___x_1105_, 1, v___x_1104_);
v___x_1106_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__3, &l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__3_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__3);
v___x_1107_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1107_, 0, v___x_1105_);
lean_ctor_set(v___x_1107_, 1, v___x_1106_);
v___x_1108_ = l_Lean_indentExpr(v_givenType_1096_);
v___x_1109_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1109_, 0, v___x_1107_);
lean_ctor_set(v___x_1109_, 1, v___x_1108_);
v___x_1110_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__5, &l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__5_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__5);
v___x_1111_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1111_, 0, v___x_1109_);
lean_ctor_set(v___x_1111_, 1, v___x_1110_);
v___x_1112_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1112_, 0, v___x_1111_);
lean_ctor_set(v___x_1112_, 1, v___x_1099_);
v___x_1113_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__7, &l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__7_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__7);
v___x_1114_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1114_, 0, v___x_1112_);
lean_ctor_set(v___x_1114_, 1, v___x_1113_);
v___x_1115_ = l_Lean_indentExpr(v_expectedType_1097_);
v___x_1116_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1116_, 0, v___x_1114_);
lean_ctor_set(v___x_1116_, 1, v___x_1115_);
v___x_1117_ = l_Lean_throwError___redArg(v_inst_1092_, v_inst_1093_, v___x_1116_);
return v___x_1117_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclNotOfExpectedType(lean_object* v_m_1118_, lean_object* v_inst_1119_, lean_object* v_inst_1120_, lean_object* v_00_u03b1_1121_, lean_object* v_attrName_1122_, lean_object* v_declName_1123_, lean_object* v_givenType_1124_, lean_object* v_expectedType_1125_){
_start:
{
lean_object* v___x_1126_; 
v___x_1126_ = l_Lean_throwAttrDeclNotOfExpectedType___redArg(v_inst_1119_, v_inst_1120_, v_attrName_1122_, v_declName_1123_, v_givenType_1124_, v_expectedType_1125_);
return v___x_1126_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1___redArg(lean_object* v_constName_1127_, uint8_t v_skipRealize_1128_, lean_object* v___y_1129_){
_start:
{
lean_object* v___x_1131_; lean_object* v_env_1132_; uint8_t v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; 
v___x_1131_ = lean_st_ref_get(v___y_1129_);
v_env_1132_ = lean_ctor_get(v___x_1131_, 0);
lean_inc_ref(v_env_1132_);
lean_dec(v___x_1131_);
v___x_1133_ = l_Lean_Environment_contains(v_env_1132_, v_constName_1127_, v_skipRealize_1128_);
v___x_1134_ = lean_box(v___x_1133_);
v___x_1135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1135_, 0, v___x_1134_);
return v___x_1135_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1___redArg___boxed(lean_object* v_constName_1136_, lean_object* v_skipRealize_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_){
_start:
{
uint8_t v_skipRealize_boxed_1140_; lean_object* v_res_1141_; 
v_skipRealize_boxed_1140_ = lean_unbox(v_skipRealize_1137_);
v_res_1141_ = l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1___redArg(v_constName_1136_, v_skipRealize_boxed_1140_, v___y_1138_);
lean_dec(v___y_1138_);
return v_res_1141_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1(lean_object* v_constName_1142_, uint8_t v_skipRealize_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_){
_start:
{
lean_object* v___x_1147_; 
v___x_1147_ = l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1___redArg(v_constName_1142_, v_skipRealize_1143_, v___y_1145_);
return v___x_1147_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1___boxed(lean_object* v_constName_1148_, lean_object* v_skipRealize_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_){
_start:
{
uint8_t v_skipRealize_boxed_1153_; lean_object* v_res_1154_; 
v_skipRealize_boxed_1153_ = lean_unbox(v_skipRealize_1149_);
v_res_1154_ = l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1(v_constName_1148_, v_skipRealize_boxed_1153_, v___y_1150_, v___y_1151_);
lean_dec(v___y_1151_);
lean_dec_ref(v___y_1150_);
return v_res_1154_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___lam__0(lean_object* v___y_1155_, uint8_t v_isExporting_1156_, lean_object* v___x_1157_, lean_object* v_a_x3f_1158_){
_start:
{
lean_object* v___x_1160_; lean_object* v_env_1161_; lean_object* v_nextMacroScope_1162_; lean_object* v_ngen_1163_; lean_object* v_auxDeclNGen_1164_; lean_object* v_traceState_1165_; lean_object* v_messages_1166_; lean_object* v_infoState_1167_; lean_object* v_snapshotTasks_1168_; lean_object* v___x_1170_; uint8_t v_isShared_1171_; uint8_t v_isSharedCheck_1179_; 
v___x_1160_ = lean_st_ref_take(v___y_1155_);
v_env_1161_ = lean_ctor_get(v___x_1160_, 0);
v_nextMacroScope_1162_ = lean_ctor_get(v___x_1160_, 1);
v_ngen_1163_ = lean_ctor_get(v___x_1160_, 2);
v_auxDeclNGen_1164_ = lean_ctor_get(v___x_1160_, 3);
v_traceState_1165_ = lean_ctor_get(v___x_1160_, 4);
v_messages_1166_ = lean_ctor_get(v___x_1160_, 6);
v_infoState_1167_ = lean_ctor_get(v___x_1160_, 7);
v_snapshotTasks_1168_ = lean_ctor_get(v___x_1160_, 8);
v_isSharedCheck_1179_ = !lean_is_exclusive(v___x_1160_);
if (v_isSharedCheck_1179_ == 0)
{
lean_object* v_unused_1180_; 
v_unused_1180_ = lean_ctor_get(v___x_1160_, 5);
lean_dec(v_unused_1180_);
v___x_1170_ = v___x_1160_;
v_isShared_1171_ = v_isSharedCheck_1179_;
goto v_resetjp_1169_;
}
else
{
lean_inc(v_snapshotTasks_1168_);
lean_inc(v_infoState_1167_);
lean_inc(v_messages_1166_);
lean_inc(v_traceState_1165_);
lean_inc(v_auxDeclNGen_1164_);
lean_inc(v_ngen_1163_);
lean_inc(v_nextMacroScope_1162_);
lean_inc(v_env_1161_);
lean_dec(v___x_1160_);
v___x_1170_ = lean_box(0);
v_isShared_1171_ = v_isSharedCheck_1179_;
goto v_resetjp_1169_;
}
v_resetjp_1169_:
{
lean_object* v___x_1172_; lean_object* v___x_1174_; 
v___x_1172_ = l_Lean_Environment_setExporting(v_env_1161_, v_isExporting_1156_);
if (v_isShared_1171_ == 0)
{
lean_ctor_set(v___x_1170_, 5, v___x_1157_);
lean_ctor_set(v___x_1170_, 0, v___x_1172_);
v___x_1174_ = v___x_1170_;
goto v_reusejp_1173_;
}
else
{
lean_object* v_reuseFailAlloc_1178_; 
v_reuseFailAlloc_1178_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1178_, 0, v___x_1172_);
lean_ctor_set(v_reuseFailAlloc_1178_, 1, v_nextMacroScope_1162_);
lean_ctor_set(v_reuseFailAlloc_1178_, 2, v_ngen_1163_);
lean_ctor_set(v_reuseFailAlloc_1178_, 3, v_auxDeclNGen_1164_);
lean_ctor_set(v_reuseFailAlloc_1178_, 4, v_traceState_1165_);
lean_ctor_set(v_reuseFailAlloc_1178_, 5, v___x_1157_);
lean_ctor_set(v_reuseFailAlloc_1178_, 6, v_messages_1166_);
lean_ctor_set(v_reuseFailAlloc_1178_, 7, v_infoState_1167_);
lean_ctor_set(v_reuseFailAlloc_1178_, 8, v_snapshotTasks_1168_);
v___x_1174_ = v_reuseFailAlloc_1178_;
goto v_reusejp_1173_;
}
v_reusejp_1173_:
{
lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; 
v___x_1175_ = lean_st_ref_set(v___y_1155_, v___x_1174_);
v___x_1176_ = lean_box(0);
v___x_1177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1177_, 0, v___x_1176_);
return v___x_1177_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___lam__0___boxed(lean_object* v___y_1181_, lean_object* v_isExporting_1182_, lean_object* v___x_1183_, lean_object* v_a_x3f_1184_, lean_object* v___y_1185_){
_start:
{
uint8_t v_isExporting_boxed_1186_; lean_object* v_res_1187_; 
v_isExporting_boxed_1186_ = lean_unbox(v_isExporting_1182_);
v_res_1187_ = l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___lam__0(v___y_1181_, v_isExporting_boxed_1186_, v___x_1183_, v_a_x3f_1184_);
lean_dec(v_a_x3f_1184_);
lean_dec(v___y_1181_);
return v_res_1187_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_1188_; 
v___x_1188_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1188_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_1189_; lean_object* v___x_1190_; 
v___x_1189_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__0, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__0);
v___x_1190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1190_, 0, v___x_1189_);
return v___x_1190_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_1191_; lean_object* v___x_1192_; 
v___x_1191_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1);
v___x_1192_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1192_, 0, v___x_1191_);
lean_ctor_set(v___x_1192_, 1, v___x_1191_);
return v___x_1192_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg(lean_object* v_x_1193_, uint8_t v_isExporting_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_){
_start:
{
lean_object* v___x_1198_; lean_object* v_env_1199_; uint8_t v_isExporting_1200_; lean_object* v___x_1251_; uint8_t v_isModule_1252_; 
v___x_1198_ = lean_st_ref_get(v___y_1196_);
v_env_1199_ = lean_ctor_get(v___x_1198_, 0);
lean_inc_ref(v_env_1199_);
lean_dec(v___x_1198_);
v_isExporting_1200_ = lean_ctor_get_uint8(v_env_1199_, sizeof(void*)*8);
v___x_1251_ = l_Lean_Environment_header(v_env_1199_);
lean_dec_ref(v_env_1199_);
v_isModule_1252_ = lean_ctor_get_uint8(v___x_1251_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_1251_);
if (v_isModule_1252_ == 0)
{
lean_object* v___x_1253_; 
lean_inc(v___y_1196_);
lean_inc_ref(v___y_1195_);
v___x_1253_ = lean_apply_3(v_x_1193_, v___y_1195_, v___y_1196_, lean_box(0));
return v___x_1253_;
}
else
{
if (v_isExporting_1200_ == 0)
{
if (v_isExporting_1194_ == 0)
{
lean_object* v___x_1254_; 
lean_inc(v___y_1196_);
lean_inc_ref(v___y_1195_);
v___x_1254_ = lean_apply_3(v_x_1193_, v___y_1195_, v___y_1196_, lean_box(0));
return v___x_1254_;
}
else
{
goto v___jp_1201_;
}
}
else
{
if (v_isExporting_1194_ == 0)
{
goto v___jp_1201_;
}
else
{
lean_object* v___x_1255_; 
lean_inc(v___y_1196_);
lean_inc_ref(v___y_1195_);
v___x_1255_ = lean_apply_3(v_x_1193_, v___y_1195_, v___y_1196_, lean_box(0));
return v___x_1255_;
}
}
}
v___jp_1201_:
{
lean_object* v___x_1202_; lean_object* v_env_1203_; lean_object* v_nextMacroScope_1204_; lean_object* v_ngen_1205_; lean_object* v_auxDeclNGen_1206_; lean_object* v_traceState_1207_; lean_object* v_messages_1208_; lean_object* v_infoState_1209_; lean_object* v_snapshotTasks_1210_; lean_object* v___x_1212_; uint8_t v_isShared_1213_; uint8_t v_isSharedCheck_1249_; 
v___x_1202_ = lean_st_ref_take(v___y_1196_);
v_env_1203_ = lean_ctor_get(v___x_1202_, 0);
v_nextMacroScope_1204_ = lean_ctor_get(v___x_1202_, 1);
v_ngen_1205_ = lean_ctor_get(v___x_1202_, 2);
v_auxDeclNGen_1206_ = lean_ctor_get(v___x_1202_, 3);
v_traceState_1207_ = lean_ctor_get(v___x_1202_, 4);
v_messages_1208_ = lean_ctor_get(v___x_1202_, 6);
v_infoState_1209_ = lean_ctor_get(v___x_1202_, 7);
v_snapshotTasks_1210_ = lean_ctor_get(v___x_1202_, 8);
v_isSharedCheck_1249_ = !lean_is_exclusive(v___x_1202_);
if (v_isSharedCheck_1249_ == 0)
{
lean_object* v_unused_1250_; 
v_unused_1250_ = lean_ctor_get(v___x_1202_, 5);
lean_dec(v_unused_1250_);
v___x_1212_ = v___x_1202_;
v_isShared_1213_ = v_isSharedCheck_1249_;
goto v_resetjp_1211_;
}
else
{
lean_inc(v_snapshotTasks_1210_);
lean_inc(v_infoState_1209_);
lean_inc(v_messages_1208_);
lean_inc(v_traceState_1207_);
lean_inc(v_auxDeclNGen_1206_);
lean_inc(v_ngen_1205_);
lean_inc(v_nextMacroScope_1204_);
lean_inc(v_env_1203_);
lean_dec(v___x_1202_);
v___x_1212_ = lean_box(0);
v_isShared_1213_ = v_isSharedCheck_1249_;
goto v_resetjp_1211_;
}
v_resetjp_1211_:
{
lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1217_; 
v___x_1214_ = l_Lean_Environment_setExporting(v_env_1203_, v_isExporting_1194_);
v___x_1215_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2);
if (v_isShared_1213_ == 0)
{
lean_ctor_set(v___x_1212_, 5, v___x_1215_);
lean_ctor_set(v___x_1212_, 0, v___x_1214_);
v___x_1217_ = v___x_1212_;
goto v_reusejp_1216_;
}
else
{
lean_object* v_reuseFailAlloc_1248_; 
v_reuseFailAlloc_1248_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1248_, 0, v___x_1214_);
lean_ctor_set(v_reuseFailAlloc_1248_, 1, v_nextMacroScope_1204_);
lean_ctor_set(v_reuseFailAlloc_1248_, 2, v_ngen_1205_);
lean_ctor_set(v_reuseFailAlloc_1248_, 3, v_auxDeclNGen_1206_);
lean_ctor_set(v_reuseFailAlloc_1248_, 4, v_traceState_1207_);
lean_ctor_set(v_reuseFailAlloc_1248_, 5, v___x_1215_);
lean_ctor_set(v_reuseFailAlloc_1248_, 6, v_messages_1208_);
lean_ctor_set(v_reuseFailAlloc_1248_, 7, v_infoState_1209_);
lean_ctor_set(v_reuseFailAlloc_1248_, 8, v_snapshotTasks_1210_);
v___x_1217_ = v_reuseFailAlloc_1248_;
goto v_reusejp_1216_;
}
v_reusejp_1216_:
{
lean_object* v___x_1218_; lean_object* v_r_1219_; 
v___x_1218_ = lean_st_ref_set(v___y_1196_, v___x_1217_);
lean_inc(v___y_1196_);
lean_inc_ref(v___y_1195_);
v_r_1219_ = lean_apply_3(v_x_1193_, v___y_1195_, v___y_1196_, lean_box(0));
if (lean_obj_tag(v_r_1219_) == 0)
{
lean_object* v_a_1220_; lean_object* v___x_1222_; uint8_t v_isShared_1223_; uint8_t v_isSharedCheck_1236_; 
v_a_1220_ = lean_ctor_get(v_r_1219_, 0);
v_isSharedCheck_1236_ = !lean_is_exclusive(v_r_1219_);
if (v_isSharedCheck_1236_ == 0)
{
v___x_1222_ = v_r_1219_;
v_isShared_1223_ = v_isSharedCheck_1236_;
goto v_resetjp_1221_;
}
else
{
lean_inc(v_a_1220_);
lean_dec(v_r_1219_);
v___x_1222_ = lean_box(0);
v_isShared_1223_ = v_isSharedCheck_1236_;
goto v_resetjp_1221_;
}
v_resetjp_1221_:
{
lean_object* v___x_1225_; 
lean_inc(v_a_1220_);
if (v_isShared_1223_ == 0)
{
lean_ctor_set_tag(v___x_1222_, 1);
v___x_1225_ = v___x_1222_;
goto v_reusejp_1224_;
}
else
{
lean_object* v_reuseFailAlloc_1235_; 
v_reuseFailAlloc_1235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1235_, 0, v_a_1220_);
v___x_1225_ = v_reuseFailAlloc_1235_;
goto v_reusejp_1224_;
}
v_reusejp_1224_:
{
lean_object* v___x_1226_; lean_object* v___x_1228_; uint8_t v_isShared_1229_; uint8_t v_isSharedCheck_1233_; 
v___x_1226_ = l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___lam__0(v___y_1196_, v_isExporting_1200_, v___x_1215_, v___x_1225_);
lean_dec_ref(v___x_1225_);
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
lean_ctor_set(v___x_1228_, 0, v_a_1220_);
v___x_1231_ = v___x_1228_;
goto v_reusejp_1230_;
}
else
{
lean_object* v_reuseFailAlloc_1232_; 
v_reuseFailAlloc_1232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1232_, 0, v_a_1220_);
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
else
{
lean_object* v_a_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1241_; uint8_t v_isShared_1242_; uint8_t v_isSharedCheck_1246_; 
v_a_1237_ = lean_ctor_get(v_r_1219_, 0);
lean_inc(v_a_1237_);
lean_dec_ref_known(v_r_1219_, 1);
v___x_1238_ = lean_box(0);
v___x_1239_ = l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___lam__0(v___y_1196_, v_isExporting_1200_, v___x_1215_, v___x_1238_);
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
lean_ctor_set_tag(v___x_1241_, 1);
lean_ctor_set(v___x_1241_, 0, v_a_1237_);
v___x_1244_ = v___x_1241_;
goto v_reusejp_1243_;
}
else
{
lean_object* v_reuseFailAlloc_1245_; 
v_reuseFailAlloc_1245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1245_, 0, v_a_1237_);
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
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___boxed(lean_object* v_x_1256_, lean_object* v_isExporting_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_){
_start:
{
uint8_t v_isExporting_boxed_1261_; lean_object* v_res_1262_; 
v_isExporting_boxed_1261_ = lean_unbox(v_isExporting_1257_);
v_res_1262_ = l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg(v_x_1256_, v_isExporting_boxed_1261_, v___y_1258_, v___y_1259_);
lean_dec(v___y_1259_);
lean_dec_ref(v___y_1258_);
return v_res_1262_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2(lean_object* v_00_u03b1_1263_, lean_object* v_x_1264_, uint8_t v_isExporting_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_){
_start:
{
lean_object* v___x_1269_; 
v___x_1269_ = l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg(v_x_1264_, v_isExporting_1265_, v___y_1266_, v___y_1267_);
return v___x_1269_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___boxed(lean_object* v_00_u03b1_1270_, lean_object* v_x_1271_, lean_object* v_isExporting_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_){
_start:
{
uint8_t v_isExporting_boxed_1276_; lean_object* v_res_1277_; 
v_isExporting_boxed_1276_ = lean_unbox(v_isExporting_1272_);
v_res_1277_ = l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2(v_00_u03b1_1270_, v_x_1271_, v_isExporting_boxed_1276_, v___y_1273_, v___y_1274_);
lean_dec(v___y_1274_);
lean_dec_ref(v___y_1273_);
return v_res_1277_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0_spec__3(lean_object* v_opts_1278_, lean_object* v_opt_1279_){
_start:
{
lean_object* v_name_1280_; lean_object* v_defValue_1281_; lean_object* v_map_1282_; lean_object* v___x_1283_; 
v_name_1280_ = lean_ctor_get(v_opt_1279_, 0);
v_defValue_1281_ = lean_ctor_get(v_opt_1279_, 1);
v_map_1282_ = lean_ctor_get(v_opts_1278_, 0);
v___x_1283_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1282_, v_name_1280_);
if (lean_obj_tag(v___x_1283_) == 0)
{
uint8_t v___x_1284_; 
v___x_1284_ = lean_unbox(v_defValue_1281_);
return v___x_1284_;
}
else
{
lean_object* v_val_1285_; 
v_val_1285_ = lean_ctor_get(v___x_1283_, 0);
lean_inc(v_val_1285_);
lean_dec_ref_known(v___x_1283_, 1);
if (lean_obj_tag(v_val_1285_) == 1)
{
uint8_t v_v_1286_; 
v_v_1286_ = lean_ctor_get_uint8(v_val_1285_, 0);
lean_dec_ref_known(v_val_1285_, 0);
return v_v_1286_;
}
else
{
uint8_t v___x_1287_; 
lean_dec(v_val_1285_);
v___x_1287_ = lean_unbox(v_defValue_1281_);
return v___x_1287_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0_spec__3___boxed(lean_object* v_opts_1288_, lean_object* v_opt_1289_){
_start:
{
uint8_t v_res_1290_; lean_object* v_r_1291_; 
v_res_1290_ = l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0_spec__3(v_opts_1288_, v_opt_1289_);
lean_dec_ref(v_opt_1289_);
lean_dec_ref(v_opts_1288_);
v_r_1291_ = lean_box(v_res_1290_);
return v_r_1291_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0(uint8_t v___y_1299_, uint8_t v_suppressElabErrors_1300_, lean_object* v_x_1301_){
_start:
{
if (lean_obj_tag(v_x_1301_) == 1)
{
lean_object* v_pre_1302_; 
v_pre_1302_ = lean_ctor_get(v_x_1301_, 0);
switch(lean_obj_tag(v_pre_1302_))
{
case 1:
{
lean_object* v_pre_1303_; 
v_pre_1303_ = lean_ctor_get(v_pre_1302_, 0);
switch(lean_obj_tag(v_pre_1303_))
{
case 0:
{
lean_object* v_str_1304_; lean_object* v_str_1305_; lean_object* v___x_1306_; uint8_t v___x_1307_; 
v_str_1304_ = lean_ctor_get(v_x_1301_, 1);
v_str_1305_ = lean_ctor_get(v_pre_1302_, 1);
v___x_1306_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__0));
v___x_1307_ = lean_string_dec_eq(v_str_1305_, v___x_1306_);
if (v___x_1307_ == 0)
{
lean_object* v___x_1308_; uint8_t v___x_1309_; 
v___x_1308_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__2));
v___x_1309_ = lean_string_dec_eq(v_str_1305_, v___x_1308_);
if (v___x_1309_ == 0)
{
return v___y_1299_;
}
else
{
lean_object* v___x_1310_; uint8_t v___x_1311_; 
v___x_1310_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__1));
v___x_1311_ = lean_string_dec_eq(v_str_1304_, v___x_1310_);
if (v___x_1311_ == 0)
{
return v___y_1299_;
}
else
{
return v_suppressElabErrors_1300_;
}
}
}
else
{
lean_object* v___x_1312_; uint8_t v___x_1313_; 
v___x_1312_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__2));
v___x_1313_ = lean_string_dec_eq(v_str_1304_, v___x_1312_);
if (v___x_1313_ == 0)
{
return v___y_1299_;
}
else
{
return v_suppressElabErrors_1300_;
}
}
}
case 1:
{
lean_object* v_pre_1314_; 
v_pre_1314_ = lean_ctor_get(v_pre_1303_, 0);
if (lean_obj_tag(v_pre_1314_) == 0)
{
lean_object* v_str_1315_; lean_object* v_str_1316_; lean_object* v_str_1317_; lean_object* v___x_1318_; uint8_t v___x_1319_; 
v_str_1315_ = lean_ctor_get(v_x_1301_, 1);
v_str_1316_ = lean_ctor_get(v_pre_1302_, 1);
v_str_1317_ = lean_ctor_get(v_pre_1303_, 1);
v___x_1318_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__3));
v___x_1319_ = lean_string_dec_eq(v_str_1317_, v___x_1318_);
if (v___x_1319_ == 0)
{
return v___y_1299_;
}
else
{
lean_object* v___x_1320_; uint8_t v___x_1321_; 
v___x_1320_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__4));
v___x_1321_ = lean_string_dec_eq(v_str_1316_, v___x_1320_);
if (v___x_1321_ == 0)
{
return v___y_1299_;
}
else
{
lean_object* v___x_1322_; uint8_t v___x_1323_; 
v___x_1322_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__5));
v___x_1323_ = lean_string_dec_eq(v_str_1315_, v___x_1322_);
if (v___x_1323_ == 0)
{
return v___y_1299_;
}
else
{
return v_suppressElabErrors_1300_;
}
}
}
}
else
{
return v___y_1299_;
}
}
default: 
{
return v___y_1299_;
}
}
}
case 0:
{
lean_object* v_str_1324_; lean_object* v___x_1325_; uint8_t v___x_1326_; 
v_str_1324_ = lean_ctor_get(v_x_1301_, 1);
v___x_1325_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__6));
v___x_1326_ = lean_string_dec_eq(v_str_1324_, v___x_1325_);
if (v___x_1326_ == 0)
{
return v___y_1299_;
}
else
{
return v_suppressElabErrors_1300_;
}
}
default: 
{
return v___y_1299_;
}
}
}
else
{
return v___y_1299_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___boxed(lean_object* v___y_1327_, lean_object* v_suppressElabErrors_1328_, lean_object* v_x_1329_){
_start:
{
uint8_t v___y_4996__boxed_1330_; uint8_t v_suppressElabErrors_boxed_1331_; uint8_t v_res_1332_; lean_object* v_r_1333_; 
v___y_4996__boxed_1330_ = lean_unbox(v___y_1327_);
v_suppressElabErrors_boxed_1331_ = lean_unbox(v_suppressElabErrors_1328_);
v_res_1332_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0(v___y_4996__boxed_1330_, v_suppressElabErrors_boxed_1331_, v_x_1329_);
lean_dec(v_x_1329_);
v_r_1333_ = lean_box(v_res_1332_);
return v_r_1333_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6(lean_object* v_ref_1334_, lean_object* v_msgData_1335_, uint8_t v_severity_1336_, uint8_t v_isSilent_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_){
_start:
{
lean_object* v___y_1342_; lean_object* v___y_1343_; lean_object* v___y_1344_; lean_object* v___y_1345_; lean_object* v___y_1346_; uint8_t v___y_1347_; uint8_t v___y_1348_; lean_object* v___y_1349_; lean_object* v___y_1350_; lean_object* v___y_1378_; lean_object* v___y_1379_; lean_object* v___y_1380_; lean_object* v___y_1381_; uint8_t v___y_1382_; uint8_t v___y_1383_; uint8_t v___y_1384_; lean_object* v___y_1385_; lean_object* v___y_1403_; lean_object* v___y_1404_; lean_object* v___y_1405_; uint8_t v___y_1406_; uint8_t v___y_1407_; uint8_t v___y_1408_; lean_object* v___y_1409_; lean_object* v___y_1410_; lean_object* v___y_1414_; lean_object* v___y_1415_; lean_object* v___y_1416_; uint8_t v___y_1417_; lean_object* v___y_1418_; uint8_t v___y_1419_; uint8_t v___y_1420_; uint8_t v___x_1425_; lean_object* v___y_1427_; lean_object* v___y_1428_; uint8_t v___y_1429_; lean_object* v___y_1430_; lean_object* v___y_1431_; uint8_t v___y_1432_; uint8_t v___y_1433_; uint8_t v___y_1435_; uint8_t v___x_1450_; 
v___x_1425_ = 2;
v___x_1450_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1336_, v___x_1425_);
if (v___x_1450_ == 0)
{
v___y_1435_ = v___x_1450_;
goto v___jp_1434_;
}
else
{
uint8_t v___x_1451_; 
lean_inc_ref(v_msgData_1335_);
v___x_1451_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_1335_);
v___y_1435_ = v___x_1451_;
goto v___jp_1434_;
}
v___jp_1341_:
{
lean_object* v___x_1351_; lean_object* v_currNamespace_1352_; lean_object* v_openDecls_1353_; lean_object* v_env_1354_; lean_object* v_nextMacroScope_1355_; lean_object* v_ngen_1356_; lean_object* v_auxDeclNGen_1357_; lean_object* v_traceState_1358_; lean_object* v_cache_1359_; lean_object* v_messages_1360_; lean_object* v_infoState_1361_; lean_object* v_snapshotTasks_1362_; lean_object* v___x_1364_; uint8_t v_isShared_1365_; uint8_t v_isSharedCheck_1376_; 
v___x_1351_ = lean_st_ref_take(v___y_1350_);
v_currNamespace_1352_ = lean_ctor_get(v___y_1349_, 6);
v_openDecls_1353_ = lean_ctor_get(v___y_1349_, 7);
v_env_1354_ = lean_ctor_get(v___x_1351_, 0);
v_nextMacroScope_1355_ = lean_ctor_get(v___x_1351_, 1);
v_ngen_1356_ = lean_ctor_get(v___x_1351_, 2);
v_auxDeclNGen_1357_ = lean_ctor_get(v___x_1351_, 3);
v_traceState_1358_ = lean_ctor_get(v___x_1351_, 4);
v_cache_1359_ = lean_ctor_get(v___x_1351_, 5);
v_messages_1360_ = lean_ctor_get(v___x_1351_, 6);
v_infoState_1361_ = lean_ctor_get(v___x_1351_, 7);
v_snapshotTasks_1362_ = lean_ctor_get(v___x_1351_, 8);
v_isSharedCheck_1376_ = !lean_is_exclusive(v___x_1351_);
if (v_isSharedCheck_1376_ == 0)
{
v___x_1364_ = v___x_1351_;
v_isShared_1365_ = v_isSharedCheck_1376_;
goto v_resetjp_1363_;
}
else
{
lean_inc(v_snapshotTasks_1362_);
lean_inc(v_infoState_1361_);
lean_inc(v_messages_1360_);
lean_inc(v_cache_1359_);
lean_inc(v_traceState_1358_);
lean_inc(v_auxDeclNGen_1357_);
lean_inc(v_ngen_1356_);
lean_inc(v_nextMacroScope_1355_);
lean_inc(v_env_1354_);
lean_dec(v___x_1351_);
v___x_1364_ = lean_box(0);
v_isShared_1365_ = v_isSharedCheck_1376_;
goto v_resetjp_1363_;
}
v_resetjp_1363_:
{
lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1371_; 
lean_inc(v_openDecls_1353_);
lean_inc(v_currNamespace_1352_);
v___x_1366_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1366_, 0, v_currNamespace_1352_);
lean_ctor_set(v___x_1366_, 1, v_openDecls_1353_);
v___x_1367_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1367_, 0, v___x_1366_);
lean_ctor_set(v___x_1367_, 1, v___y_1345_);
lean_inc_ref(v___y_1344_);
lean_inc_ref(v___y_1343_);
v___x_1368_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1368_, 0, v___y_1343_);
lean_ctor_set(v___x_1368_, 1, v___y_1342_);
lean_ctor_set(v___x_1368_, 2, v___y_1346_);
lean_ctor_set(v___x_1368_, 3, v___y_1344_);
lean_ctor_set(v___x_1368_, 4, v___x_1367_);
lean_ctor_set_uint8(v___x_1368_, sizeof(void*)*5, v___y_1348_);
lean_ctor_set_uint8(v___x_1368_, sizeof(void*)*5 + 1, v___y_1347_);
lean_ctor_set_uint8(v___x_1368_, sizeof(void*)*5 + 2, v_isSilent_1337_);
v___x_1369_ = l_Lean_MessageLog_add(v___x_1368_, v_messages_1360_);
if (v_isShared_1365_ == 0)
{
lean_ctor_set(v___x_1364_, 6, v___x_1369_);
v___x_1371_ = v___x_1364_;
goto v_reusejp_1370_;
}
else
{
lean_object* v_reuseFailAlloc_1375_; 
v_reuseFailAlloc_1375_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1375_, 0, v_env_1354_);
lean_ctor_set(v_reuseFailAlloc_1375_, 1, v_nextMacroScope_1355_);
lean_ctor_set(v_reuseFailAlloc_1375_, 2, v_ngen_1356_);
lean_ctor_set(v_reuseFailAlloc_1375_, 3, v_auxDeclNGen_1357_);
lean_ctor_set(v_reuseFailAlloc_1375_, 4, v_traceState_1358_);
lean_ctor_set(v_reuseFailAlloc_1375_, 5, v_cache_1359_);
lean_ctor_set(v_reuseFailAlloc_1375_, 6, v___x_1369_);
lean_ctor_set(v_reuseFailAlloc_1375_, 7, v_infoState_1361_);
lean_ctor_set(v_reuseFailAlloc_1375_, 8, v_snapshotTasks_1362_);
v___x_1371_ = v_reuseFailAlloc_1375_;
goto v_reusejp_1370_;
}
v_reusejp_1370_:
{
lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; 
v___x_1372_ = lean_st_ref_set(v___y_1350_, v___x_1371_);
v___x_1373_ = lean_box(0);
v___x_1374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1374_, 0, v___x_1373_);
return v___x_1374_;
}
}
}
v___jp_1377_:
{
lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v_a_1388_; lean_object* v___x_1390_; uint8_t v_isShared_1391_; uint8_t v_isSharedCheck_1401_; 
v___x_1386_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_1335_);
v___x_1387_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0(v___x_1386_, v___y_1338_, v___y_1339_);
v_a_1388_ = lean_ctor_get(v___x_1387_, 0);
v_isSharedCheck_1401_ = !lean_is_exclusive(v___x_1387_);
if (v_isSharedCheck_1401_ == 0)
{
v___x_1390_ = v___x_1387_;
v_isShared_1391_ = v_isSharedCheck_1401_;
goto v_resetjp_1389_;
}
else
{
lean_inc(v_a_1388_);
lean_dec(v___x_1387_);
v___x_1390_ = lean_box(0);
v_isShared_1391_ = v_isSharedCheck_1401_;
goto v_resetjp_1389_;
}
v_resetjp_1389_:
{
lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; 
lean_inc_ref_n(v___y_1381_, 2);
v___x_1392_ = l_Lean_FileMap_toPosition(v___y_1381_, v___y_1380_);
lean_dec(v___y_1380_);
v___x_1393_ = l_Lean_FileMap_toPosition(v___y_1381_, v___y_1385_);
lean_dec(v___y_1385_);
v___x_1394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1394_, 0, v___x_1393_);
v___x_1395_ = ((lean_object*)(l_Lean_instInhabitedAttributeImplCore_default___closed__3));
if (v___y_1382_ == 0)
{
lean_del_object(v___x_1390_);
lean_dec_ref(v___y_1378_);
v___y_1342_ = v___x_1392_;
v___y_1343_ = v___y_1379_;
v___y_1344_ = v___x_1395_;
v___y_1345_ = v_a_1388_;
v___y_1346_ = v___x_1394_;
v___y_1347_ = v___y_1384_;
v___y_1348_ = v___y_1383_;
v___y_1349_ = v___y_1338_;
v___y_1350_ = v___y_1339_;
goto v___jp_1341_;
}
else
{
uint8_t v___x_1396_; 
lean_inc(v_a_1388_);
v___x_1396_ = l_Lean_MessageData_hasTag(v___y_1378_, v_a_1388_);
if (v___x_1396_ == 0)
{
lean_object* v___x_1397_; lean_object* v___x_1399_; 
lean_dec_ref_known(v___x_1394_, 1);
lean_dec_ref(v___x_1392_);
lean_dec(v_a_1388_);
v___x_1397_ = lean_box(0);
if (v_isShared_1391_ == 0)
{
lean_ctor_set(v___x_1390_, 0, v___x_1397_);
v___x_1399_ = v___x_1390_;
goto v_reusejp_1398_;
}
else
{
lean_object* v_reuseFailAlloc_1400_; 
v_reuseFailAlloc_1400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1400_, 0, v___x_1397_);
v___x_1399_ = v_reuseFailAlloc_1400_;
goto v_reusejp_1398_;
}
v_reusejp_1398_:
{
return v___x_1399_;
}
}
else
{
lean_del_object(v___x_1390_);
v___y_1342_ = v___x_1392_;
v___y_1343_ = v___y_1379_;
v___y_1344_ = v___x_1395_;
v___y_1345_ = v_a_1388_;
v___y_1346_ = v___x_1394_;
v___y_1347_ = v___y_1384_;
v___y_1348_ = v___y_1383_;
v___y_1349_ = v___y_1338_;
v___y_1350_ = v___y_1339_;
goto v___jp_1341_;
}
}
}
}
v___jp_1402_:
{
lean_object* v___x_1411_; 
v___x_1411_ = l_Lean_Syntax_getTailPos_x3f(v___y_1409_, v___y_1408_);
lean_dec(v___y_1409_);
if (lean_obj_tag(v___x_1411_) == 0)
{
lean_inc(v___y_1410_);
v___y_1378_ = v___y_1403_;
v___y_1379_ = v___y_1404_;
v___y_1380_ = v___y_1410_;
v___y_1381_ = v___y_1405_;
v___y_1382_ = v___y_1406_;
v___y_1383_ = v___y_1408_;
v___y_1384_ = v___y_1407_;
v___y_1385_ = v___y_1410_;
goto v___jp_1377_;
}
else
{
lean_object* v_val_1412_; 
v_val_1412_ = lean_ctor_get(v___x_1411_, 0);
lean_inc(v_val_1412_);
lean_dec_ref_known(v___x_1411_, 1);
v___y_1378_ = v___y_1403_;
v___y_1379_ = v___y_1404_;
v___y_1380_ = v___y_1410_;
v___y_1381_ = v___y_1405_;
v___y_1382_ = v___y_1406_;
v___y_1383_ = v___y_1408_;
v___y_1384_ = v___y_1407_;
v___y_1385_ = v_val_1412_;
goto v___jp_1377_;
}
}
v___jp_1413_:
{
lean_object* v_ref_1421_; lean_object* v___x_1422_; 
v_ref_1421_ = l_Lean_replaceRef(v_ref_1334_, v___y_1418_);
v___x_1422_ = l_Lean_Syntax_getPos_x3f(v_ref_1421_, v___y_1419_);
if (lean_obj_tag(v___x_1422_) == 0)
{
lean_object* v___x_1423_; 
v___x_1423_ = lean_unsigned_to_nat(0u);
v___y_1403_ = v___y_1414_;
v___y_1404_ = v___y_1415_;
v___y_1405_ = v___y_1416_;
v___y_1406_ = v___y_1417_;
v___y_1407_ = v___y_1420_;
v___y_1408_ = v___y_1419_;
v___y_1409_ = v_ref_1421_;
v___y_1410_ = v___x_1423_;
goto v___jp_1402_;
}
else
{
lean_object* v_val_1424_; 
v_val_1424_ = lean_ctor_get(v___x_1422_, 0);
lean_inc(v_val_1424_);
lean_dec_ref_known(v___x_1422_, 1);
v___y_1403_ = v___y_1414_;
v___y_1404_ = v___y_1415_;
v___y_1405_ = v___y_1416_;
v___y_1406_ = v___y_1417_;
v___y_1407_ = v___y_1420_;
v___y_1408_ = v___y_1419_;
v___y_1409_ = v_ref_1421_;
v___y_1410_ = v_val_1424_;
goto v___jp_1402_;
}
}
v___jp_1426_:
{
if (v___y_1433_ == 0)
{
v___y_1414_ = v___y_1431_;
v___y_1415_ = v___y_1427_;
v___y_1416_ = v___y_1428_;
v___y_1417_ = v___y_1429_;
v___y_1418_ = v___y_1430_;
v___y_1419_ = v___y_1432_;
v___y_1420_ = v_severity_1336_;
goto v___jp_1413_;
}
else
{
v___y_1414_ = v___y_1431_;
v___y_1415_ = v___y_1427_;
v___y_1416_ = v___y_1428_;
v___y_1417_ = v___y_1429_;
v___y_1418_ = v___y_1430_;
v___y_1419_ = v___y_1432_;
v___y_1420_ = v___x_1425_;
goto v___jp_1413_;
}
}
v___jp_1434_:
{
if (v___y_1435_ == 0)
{
lean_object* v_fileName_1436_; lean_object* v_fileMap_1437_; lean_object* v_options_1438_; lean_object* v_ref_1439_; uint8_t v_suppressElabErrors_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___f_1443_; uint8_t v___x_1444_; uint8_t v___x_1445_; 
v_fileName_1436_ = lean_ctor_get(v___y_1338_, 0);
v_fileMap_1437_ = lean_ctor_get(v___y_1338_, 1);
v_options_1438_ = lean_ctor_get(v___y_1338_, 2);
v_ref_1439_ = lean_ctor_get(v___y_1338_, 5);
v_suppressElabErrors_1440_ = lean_ctor_get_uint8(v___y_1338_, sizeof(void*)*14 + 1);
v___x_1441_ = lean_box(v___y_1435_);
v___x_1442_ = lean_box(v_suppressElabErrors_1440_);
v___f_1443_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1443_, 0, v___x_1441_);
lean_closure_set(v___f_1443_, 1, v___x_1442_);
v___x_1444_ = 1;
v___x_1445_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1336_, v___x_1444_);
if (v___x_1445_ == 0)
{
v___y_1427_ = v_fileName_1436_;
v___y_1428_ = v_fileMap_1437_;
v___y_1429_ = v_suppressElabErrors_1440_;
v___y_1430_ = v_ref_1439_;
v___y_1431_ = v___f_1443_;
v___y_1432_ = v___y_1435_;
v___y_1433_ = v___x_1445_;
goto v___jp_1426_;
}
else
{
lean_object* v___x_1446_; uint8_t v___x_1447_; 
v___x_1446_ = l_Lean_warningAsError;
v___x_1447_ = l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0_spec__3(v_options_1438_, v___x_1446_);
v___y_1427_ = v_fileName_1436_;
v___y_1428_ = v_fileMap_1437_;
v___y_1429_ = v_suppressElabErrors_1440_;
v___y_1430_ = v_ref_1439_;
v___y_1431_ = v___f_1443_;
v___y_1432_ = v___y_1435_;
v___y_1433_ = v___x_1447_;
goto v___jp_1426_;
}
}
else
{
lean_object* v___x_1448_; lean_object* v___x_1449_; 
lean_dec_ref(v_msgData_1335_);
v___x_1448_ = lean_box(0);
v___x_1449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1449_, 0, v___x_1448_);
return v___x_1449_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___boxed(lean_object* v_ref_1452_, lean_object* v_msgData_1453_, lean_object* v_severity_1454_, lean_object* v_isSilent_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_){
_start:
{
uint8_t v_severity_boxed_1459_; uint8_t v_isSilent_boxed_1460_; lean_object* v_res_1461_; 
v_severity_boxed_1459_ = lean_unbox(v_severity_1454_);
v_isSilent_boxed_1460_ = lean_unbox(v_isSilent_1455_);
v_res_1461_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6(v_ref_1452_, v_msgData_1453_, v_severity_boxed_1459_, v_isSilent_boxed_1460_, v___y_1456_, v___y_1457_);
lean_dec(v___y_1457_);
lean_dec_ref(v___y_1456_);
lean_dec(v_ref_1452_);
return v_res_1461_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5(lean_object* v_msgData_1462_, uint8_t v_severity_1463_, uint8_t v_isSilent_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_){
_start:
{
lean_object* v_ref_1468_; lean_object* v___x_1469_; 
v_ref_1468_ = lean_ctor_get(v___y_1465_, 5);
v___x_1469_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6(v_ref_1468_, v_msgData_1462_, v_severity_1463_, v_isSilent_1464_, v___y_1465_, v___y_1466_);
return v___x_1469_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5___boxed(lean_object* v_msgData_1470_, lean_object* v_severity_1471_, lean_object* v_isSilent_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_){
_start:
{
uint8_t v_severity_boxed_1476_; uint8_t v_isSilent_boxed_1477_; lean_object* v_res_1478_; 
v_severity_boxed_1476_ = lean_unbox(v_severity_1471_);
v_isSilent_boxed_1477_ = lean_unbox(v_isSilent_1472_);
v_res_1478_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5(v_msgData_1470_, v_severity_boxed_1476_, v_isSilent_boxed_1477_, v___y_1473_, v___y_1474_);
lean_dec(v___y_1474_);
lean_dec_ref(v___y_1473_);
return v_res_1478_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1(lean_object* v_msgData_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_){
_start:
{
uint8_t v___x_1483_; uint8_t v___x_1484_; lean_object* v___x_1485_; 
v___x_1483_ = 1;
v___x_1484_ = 0;
v___x_1485_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5(v_msgData_1479_, v___x_1483_, v___x_1484_, v___y_1480_, v___y_1481_);
return v___x_1485_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1___boxed(lean_object* v_msgData_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_){
_start:
{
lean_object* v_res_1490_; 
v_res_1490_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1(v_msgData_1486_, v___y_1487_, v___y_1488_);
lean_dec(v___y_1488_);
lean_dec_ref(v___y_1487_);
return v_res_1490_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0___redArg(lean_object* v_opt_1491_, lean_object* v___y_1492_){
_start:
{
lean_object* v_options_1494_; uint8_t v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; 
v_options_1494_ = lean_ctor_get(v___y_1492_, 2);
v___x_1495_ = l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0_spec__3(v_options_1494_, v_opt_1491_);
v___x_1496_ = lean_box(v___x_1495_);
v___x_1497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1497_, 0, v___x_1496_);
return v___x_1497_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0___redArg___boxed(lean_object* v_opt_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_){
_start:
{
lean_object* v_res_1501_; 
v_res_1501_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0___redArg(v_opt_1498_, v___y_1499_);
lean_dec_ref(v___y_1499_);
lean_dec_ref(v_opt_1498_);
return v_res_1501_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1503_; lean_object* v___x_1504_; 
v___x_1503_ = ((lean_object*)(l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__0));
v___x_1504_ = l_Lean_stringToMessageData(v___x_1503_);
return v___x_1504_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__3(void){
_start:
{
lean_object* v___x_1506_; lean_object* v___x_1507_; 
v___x_1506_ = ((lean_object*)(l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__2));
v___x_1507_ = l_Lean_stringToMessageData(v___x_1506_);
return v___x_1507_;
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0(lean_object* v_id_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_){
_start:
{
lean_object* v___x_1512_; lean_object* v_env_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v_a_1516_; lean_object* v___x_1518_; uint8_t v_isShared_1519_; uint8_t v_isSharedCheck_1535_; 
v___x_1512_ = lean_st_ref_get(v___y_1510_);
v_env_1513_ = lean_ctor_get(v___x_1512_, 0);
lean_inc_ref(v_env_1513_);
lean_dec(v___x_1512_);
v___x_1514_ = l_Lean_ResolveName_backward_privateInPublic_warn;
v___x_1515_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0___redArg(v___x_1514_, v___y_1509_);
v_a_1516_ = lean_ctor_get(v___x_1515_, 0);
v_isSharedCheck_1535_ = !lean_is_exclusive(v___x_1515_);
if (v_isSharedCheck_1535_ == 0)
{
v___x_1518_ = v___x_1515_;
v_isShared_1519_ = v_isSharedCheck_1535_;
goto v_resetjp_1517_;
}
else
{
lean_inc(v_a_1516_);
lean_dec(v___x_1515_);
v___x_1518_ = lean_box(0);
v_isShared_1519_ = v_isSharedCheck_1535_;
goto v_resetjp_1517_;
}
v_resetjp_1517_:
{
uint8_t v_isExporting_1525_; 
v_isExporting_1525_ = lean_ctor_get_uint8(v_env_1513_, sizeof(void*)*8);
lean_dec_ref(v_env_1513_);
if (v_isExporting_1525_ == 0)
{
lean_dec(v_a_1516_);
lean_dec(v_id_1508_);
goto v___jp_1520_;
}
else
{
uint8_t v___x_1526_; 
v___x_1526_ = l_Lean_isPrivateName(v_id_1508_);
if (v___x_1526_ == 0)
{
lean_dec(v_a_1516_);
lean_dec(v_id_1508_);
goto v___jp_1520_;
}
else
{
uint8_t v___x_1527_; 
v___x_1527_ = lean_unbox(v_a_1516_);
lean_dec(v_a_1516_);
if (v___x_1527_ == 0)
{
lean_dec(v_id_1508_);
goto v___jp_1520_;
}
else
{
lean_object* v___x_1528_; uint8_t v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; 
lean_del_object(v___x_1518_);
v___x_1528_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__1, &l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__1_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__1);
v___x_1529_ = 0;
v___x_1530_ = l_Lean_MessageData_ofConstName(v_id_1508_, v___x_1529_);
v___x_1531_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1531_, 0, v___x_1528_);
lean_ctor_set(v___x_1531_, 1, v___x_1530_);
v___x_1532_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__3, &l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__3_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__3);
v___x_1533_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1533_, 0, v___x_1531_);
lean_ctor_set(v___x_1533_, 1, v___x_1532_);
v___x_1534_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1(v___x_1533_, v___y_1509_, v___y_1510_);
return v___x_1534_;
}
}
}
v___jp_1520_:
{
lean_object* v___x_1521_; lean_object* v___x_1523_; 
v___x_1521_ = lean_box(0);
if (v_isShared_1519_ == 0)
{
lean_ctor_set(v___x_1518_, 0, v___x_1521_);
v___x_1523_ = v___x_1518_;
goto v_reusejp_1522_;
}
else
{
lean_object* v_reuseFailAlloc_1524_; 
v_reuseFailAlloc_1524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1524_, 0, v___x_1521_);
v___x_1523_ = v_reuseFailAlloc_1524_;
goto v_reusejp_1522_;
}
v_reusejp_1522_:
{
return v___x_1523_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___boxed(lean_object* v_id_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_){
_start:
{
lean_object* v_res_1540_; 
v_res_1540_ = l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0(v_id_1536_, v___y_1537_, v___y_1538_);
lean_dec(v___y_1538_);
lean_dec_ref(v___y_1537_);
return v_res_1540_;
}
}
static lean_object* _init_l_Lean_ensureAttrDeclIsPublic___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1542_; lean_object* v___x_1543_; 
v___x_1542_ = ((lean_object*)(l_Lean_ensureAttrDeclIsPublic___lam__0___closed__0));
v___x_1543_ = l_Lean_stringToMessageData(v___x_1542_);
return v___x_1543_;
}
}
LEAN_EXPORT lean_object* l_Lean_ensureAttrDeclIsPublic___lam__0(lean_object* v_declName_1544_, uint8_t v_isModule_1545_, lean_object* v_attrName_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_){
_start:
{
lean_object* v___x_1550_; 
lean_inc(v_declName_1544_);
v___x_1550_ = l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0(v_declName_1544_, v___y_1547_, v___y_1548_);
if (lean_obj_tag(v___x_1550_) == 0)
{
lean_object* v___x_1551_; lean_object* v_a_1552_; lean_object* v___x_1554_; uint8_t v_isShared_1555_; uint8_t v_isSharedCheck_1572_; 
lean_dec_ref_known(v___x_1550_, 1);
lean_inc(v_declName_1544_);
v___x_1551_ = l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1___redArg(v_declName_1544_, v_isModule_1545_, v___y_1548_);
v_a_1552_ = lean_ctor_get(v___x_1551_, 0);
v_isSharedCheck_1572_ = !lean_is_exclusive(v___x_1551_);
if (v_isSharedCheck_1572_ == 0)
{
v___x_1554_ = v___x_1551_;
v_isShared_1555_ = v_isSharedCheck_1572_;
goto v_resetjp_1553_;
}
else
{
lean_inc(v_a_1552_);
lean_dec(v___x_1551_);
v___x_1554_ = lean_box(0);
v_isShared_1555_ = v_isSharedCheck_1572_;
goto v_resetjp_1553_;
}
v_resetjp_1553_:
{
uint8_t v___x_1556_; 
v___x_1556_ = lean_unbox(v_a_1552_);
if (v___x_1556_ == 0)
{
lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; uint8_t v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; 
lean_del_object(v___x_1554_);
v___x_1557_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1);
v___x_1558_ = l_Lean_MessageData_ofName(v_attrName_1546_);
v___x_1559_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1559_, 0, v___x_1557_);
lean_ctor_set(v___x_1559_, 1, v___x_1558_);
v___x_1560_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1, &l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1);
v___x_1561_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1561_, 0, v___x_1559_);
lean_ctor_set(v___x_1561_, 1, v___x_1560_);
v___x_1562_ = lean_unbox(v_a_1552_);
lean_dec(v_a_1552_);
v___x_1563_ = l_Lean_MessageData_ofConstName(v_declName_1544_, v___x_1562_);
v___x_1564_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1564_, 0, v___x_1561_);
lean_ctor_set(v___x_1564_, 1, v___x_1563_);
v___x_1565_ = lean_obj_once(&l_Lean_ensureAttrDeclIsPublic___lam__0___closed__1, &l_Lean_ensureAttrDeclIsPublic___lam__0___closed__1_once, _init_l_Lean_ensureAttrDeclIsPublic___lam__0___closed__1);
v___x_1566_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1566_, 0, v___x_1564_);
lean_ctor_set(v___x_1566_, 1, v___x_1565_);
v___x_1567_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_1566_, v___y_1547_, v___y_1548_);
return v___x_1567_;
}
else
{
lean_object* v___x_1568_; lean_object* v___x_1570_; 
lean_dec(v_a_1552_);
lean_dec(v_attrName_1546_);
lean_dec(v_declName_1544_);
v___x_1568_ = lean_box(0);
if (v_isShared_1555_ == 0)
{
lean_ctor_set(v___x_1554_, 0, v___x_1568_);
v___x_1570_ = v___x_1554_;
goto v_reusejp_1569_;
}
else
{
lean_object* v_reuseFailAlloc_1571_; 
v_reuseFailAlloc_1571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1571_, 0, v___x_1568_);
v___x_1570_ = v_reuseFailAlloc_1571_;
goto v_reusejp_1569_;
}
v_reusejp_1569_:
{
return v___x_1570_;
}
}
}
}
else
{
lean_dec(v_attrName_1546_);
lean_dec(v_declName_1544_);
return v___x_1550_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ensureAttrDeclIsPublic___lam__0___boxed(lean_object* v_declName_1573_, lean_object* v_isModule_1574_, lean_object* v_attrName_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_){
_start:
{
uint8_t v_isModule_boxed_1579_; lean_object* v_res_1580_; 
v_isModule_boxed_1579_ = lean_unbox(v_isModule_1574_);
v_res_1580_ = l_Lean_ensureAttrDeclIsPublic___lam__0(v_declName_1573_, v_isModule_boxed_1579_, v_attrName_1575_, v___y_1576_, v___y_1577_);
lean_dec(v___y_1577_);
lean_dec_ref(v___y_1576_);
return v_res_1580_;
}
}
LEAN_EXPORT lean_object* l_Lean_ensureAttrDeclIsPublic(lean_object* v_attrName_1581_, lean_object* v_declName_1582_, uint8_t v_attrKind_1583_, lean_object* v_a_1584_, lean_object* v_a_1585_){
_start:
{
lean_object* v___x_1587_; lean_object* v_env_1591_; lean_object* v___x_1592_; uint8_t v_isModule_1593_; 
v___x_1587_ = lean_st_ref_get(v_a_1585_);
v_env_1591_ = lean_ctor_get(v___x_1587_, 0);
lean_inc_ref(v_env_1591_);
lean_dec(v___x_1587_);
v___x_1592_ = l_Lean_Environment_header(v_env_1591_);
lean_dec_ref(v_env_1591_);
v_isModule_1593_ = lean_ctor_get_uint8(v___x_1592_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_1592_);
if (v_isModule_1593_ == 0)
{
lean_dec(v_declName_1582_);
lean_dec(v_attrName_1581_);
goto v___jp_1588_;
}
else
{
uint8_t v___x_1594_; uint8_t v___x_1595_; 
v___x_1594_ = 1;
v___x_1595_ = l_Lean_instBEqAttributeKind_beq(v_attrKind_1583_, v___x_1594_);
if (v___x_1595_ == 0)
{
lean_object* v___x_1596_; lean_object* v___f_1597_; lean_object* v___x_1598_; 
v___x_1596_ = lean_box(v_isModule_1593_);
v___f_1597_ = lean_alloc_closure((void*)(l_Lean_ensureAttrDeclIsPublic___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1597_, 0, v_declName_1582_);
lean_closure_set(v___f_1597_, 1, v___x_1596_);
lean_closure_set(v___f_1597_, 2, v_attrName_1581_);
v___x_1598_ = l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg(v___f_1597_, v_isModule_1593_, v_a_1584_, v_a_1585_);
return v___x_1598_;
}
else
{
lean_dec(v_declName_1582_);
lean_dec(v_attrName_1581_);
goto v___jp_1588_;
}
}
v___jp_1588_:
{
lean_object* v___x_1589_; lean_object* v___x_1590_; 
v___x_1589_ = lean_box(0);
v___x_1590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1590_, 0, v___x_1589_);
return v___x_1590_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ensureAttrDeclIsPublic___boxed(lean_object* v_attrName_1599_, lean_object* v_declName_1600_, lean_object* v_attrKind_1601_, lean_object* v_a_1602_, lean_object* v_a_1603_, lean_object* v_a_1604_){
_start:
{
uint8_t v_attrKind_boxed_1605_; lean_object* v_res_1606_; 
v_attrKind_boxed_1605_ = lean_unbox(v_attrKind_1601_);
v_res_1606_ = l_Lean_ensureAttrDeclIsPublic(v_attrName_1599_, v_declName_1600_, v_attrKind_boxed_1605_, v_a_1602_, v_a_1603_);
lean_dec(v_a_1603_);
lean_dec_ref(v_a_1602_);
return v_res_1606_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0(lean_object* v_opt_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_){
_start:
{
lean_object* v___x_1611_; 
v___x_1611_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0___redArg(v_opt_1607_, v___y_1608_);
return v___x_1611_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0___boxed(lean_object* v_opt_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_){
_start:
{
lean_object* v_res_1616_; 
v_res_1616_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0(v_opt_1612_, v___y_1613_, v___y_1614_);
lean_dec(v___y_1614_);
lean_dec_ref(v___y_1613_);
lean_dec_ref(v_opt_1612_);
return v_res_1616_;
}
}
static lean_object* _init_l_Lean_ensureAttrDeclIsMeta___closed__1(void){
_start:
{
lean_object* v___x_1618_; lean_object* v___x_1619_; 
v___x_1618_ = ((lean_object*)(l_Lean_ensureAttrDeclIsMeta___closed__0));
v___x_1619_ = l_Lean_stringToMessageData(v___x_1618_);
return v___x_1619_;
}
}
LEAN_EXPORT lean_object* l_Lean_ensureAttrDeclIsMeta(lean_object* v_attrName_1620_, lean_object* v_declName_1621_, uint8_t v_attrKind_1622_, lean_object* v_a_1623_, lean_object* v_a_1624_){
_start:
{
lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v_env_1628_; lean_object* v___x_1629_; uint8_t v_isModule_1630_; 
v___x_1626_ = lean_st_ref_get(v_a_1624_);
v___x_1627_ = lean_st_ref_get(v_a_1624_);
v_env_1628_ = lean_ctor_get(v___x_1626_, 0);
lean_inc_ref(v_env_1628_);
lean_dec(v___x_1626_);
v___x_1629_ = l_Lean_Environment_header(v_env_1628_);
lean_dec_ref(v_env_1628_);
v_isModule_1630_ = lean_ctor_get_uint8(v___x_1629_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_1629_);
if (v_isModule_1630_ == 0)
{
lean_object* v___x_1631_; 
lean_dec(v___x_1627_);
v___x_1631_ = l_Lean_ensureAttrDeclIsPublic(v_attrName_1620_, v_declName_1621_, v_attrKind_1622_, v_a_1623_, v_a_1624_);
return v___x_1631_;
}
else
{
lean_object* v_env_1632_; uint8_t v___x_1633_; 
v_env_1632_ = lean_ctor_get(v___x_1627_, 0);
lean_inc_ref(v_env_1632_);
lean_dec(v___x_1627_);
lean_inc(v_declName_1621_);
v___x_1633_ = l_Lean_isMarkedMeta(v_env_1632_, v_declName_1621_);
if (v___x_1633_ == 0)
{
lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; 
v___x_1634_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1);
v___x_1635_ = l_Lean_MessageData_ofName(v_attrName_1620_);
v___x_1636_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1636_, 0, v___x_1634_);
lean_ctor_set(v___x_1636_, 1, v___x_1635_);
v___x_1637_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1, &l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1);
v___x_1638_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1638_, 0, v___x_1636_);
lean_ctor_set(v___x_1638_, 1, v___x_1637_);
v___x_1639_ = l_Lean_MessageData_ofConstName(v_declName_1621_, v___x_1633_);
v___x_1640_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1640_, 0, v___x_1638_);
lean_ctor_set(v___x_1640_, 1, v___x_1639_);
v___x_1641_ = lean_obj_once(&l_Lean_ensureAttrDeclIsMeta___closed__1, &l_Lean_ensureAttrDeclIsMeta___closed__1_once, _init_l_Lean_ensureAttrDeclIsMeta___closed__1);
v___x_1642_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1642_, 0, v___x_1640_);
lean_ctor_set(v___x_1642_, 1, v___x_1641_);
v___x_1643_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_1642_, v_a_1623_, v_a_1624_);
return v___x_1643_;
}
else
{
lean_object* v___x_1644_; 
v___x_1644_ = l_Lean_ensureAttrDeclIsPublic(v_attrName_1620_, v_declName_1621_, v_attrKind_1622_, v_a_1623_, v_a_1624_);
return v___x_1644_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ensureAttrDeclIsMeta___boxed(lean_object* v_attrName_1645_, lean_object* v_declName_1646_, lean_object* v_attrKind_1647_, lean_object* v_a_1648_, lean_object* v_a_1649_, lean_object* v_a_1650_){
_start:
{
uint8_t v_attrKind_boxed_1651_; lean_object* v_res_1652_; 
v_attrKind_boxed_1651_ = lean_unbox(v_attrKind_1647_);
v_res_1652_ = l_Lean_ensureAttrDeclIsMeta(v_attrName_1645_, v_declName_1646_, v_attrKind_boxed_1651_, v_a_1648_, v_a_1649_);
lean_dec(v_a_1649_);
lean_dec_ref(v_a_1648_);
return v_res_1652_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__0(lean_object* v_x_1656_, lean_object* v___y_1657_){
_start:
{
lean_object* v___x_1659_; lean_object* v___x_1660_; 
v___x_1659_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___lam__0___closed__1));
v___x_1660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1660_, 0, v___x_1659_);
return v___x_1660_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__0___boxed(lean_object* v_x_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_){
_start:
{
lean_object* v_res_1664_; 
v_res_1664_ = l_Lean_instInhabitedTagAttribute_default___lam__0(v_x_1661_, v___y_1662_);
lean_dec_ref(v___y_1662_);
lean_dec_ref(v_x_1661_);
return v_res_1664_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__1(lean_object* v_s_1665_, lean_object* v_x_1666_){
_start:
{
lean_inc(v_s_1665_);
return v_s_1665_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__1___boxed(lean_object* v_s_1667_, lean_object* v_x_1668_){
_start:
{
lean_object* v_res_1669_; 
v_res_1669_ = l_Lean_instInhabitedTagAttribute_default___lam__1(v_s_1667_, v_x_1668_);
lean_dec(v_x_1668_);
lean_dec(v_s_1667_);
return v_res_1669_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__2(lean_object* v_x_1674_, lean_object* v_x_1675_){
_start:
{
lean_object* v___x_1676_; 
v___x_1676_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___lam__2___closed__1));
return v___x_1676_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__2___boxed(lean_object* v_x_1677_, lean_object* v_x_1678_){
_start:
{
lean_object* v_res_1679_; 
v_res_1679_ = l_Lean_instInhabitedTagAttribute_default___lam__2(v_x_1677_, v_x_1678_);
lean_dec(v_x_1678_);
lean_dec_ref(v_x_1677_);
return v_res_1679_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__3(lean_object* v_x_1680_){
_start:
{
lean_object* v___x_1681_; 
v___x_1681_ = lean_box(0);
return v___x_1681_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__3___boxed(lean_object* v_x_1682_){
_start:
{
lean_object* v_res_1683_; 
v_res_1683_ = l_Lean_instInhabitedTagAttribute_default___lam__3(v_x_1682_);
lean_dec(v_x_1682_);
return v_res_1683_;
}
}
static lean_object* _init_l_Lean_instInhabitedTagAttribute_default___closed__4(void){
_start:
{
lean_object* v___x_1688_; 
v___x_1688_ = l_Lean_instInhabitedEnvExtension_default(lean_box(0));
return v___x_1688_;
}
}
static lean_object* _init_l_Lean_instInhabitedTagAttribute_default___closed__5(void){
_start:
{
lean_object* v___f_1689_; lean_object* v___f_1690_; lean_object* v___f_1691_; lean_object* v___f_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; 
v___f_1689_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___closed__3));
v___f_1690_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___closed__2));
v___f_1691_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___closed__1));
v___f_1692_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___closed__0));
v___x_1693_ = lean_box(0);
v___x_1694_ = lean_obj_once(&l_Lean_instInhabitedTagAttribute_default___closed__4, &l_Lean_instInhabitedTagAttribute_default___closed__4_once, _init_l_Lean_instInhabitedTagAttribute_default___closed__4);
v___x_1695_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1695_, 0, v___x_1694_);
lean_ctor_set(v___x_1695_, 1, v___x_1693_);
lean_ctor_set(v___x_1695_, 2, v___f_1692_);
lean_ctor_set(v___x_1695_, 3, v___f_1691_);
lean_ctor_set(v___x_1695_, 4, v___f_1690_);
lean_ctor_set(v___x_1695_, 5, v___f_1689_);
return v___x_1695_;
}
}
static lean_object* _init_l_Lean_instInhabitedTagAttribute_default___closed__6(void){
_start:
{
lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; 
v___x_1696_ = lean_obj_once(&l_Lean_instInhabitedTagAttribute_default___closed__5, &l_Lean_instInhabitedTagAttribute_default___closed__5_once, _init_l_Lean_instInhabitedTagAttribute_default___closed__5);
v___x_1697_ = ((lean_object*)(l_Lean_instInhabitedAttributeImpl_default));
v___x_1698_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1698_, 0, v___x_1697_);
lean_ctor_set(v___x_1698_, 1, v___x_1696_);
return v___x_1698_;
}
}
static lean_object* _init_l_Lean_instInhabitedTagAttribute_default(void){
_start:
{
lean_object* v___x_1699_; 
v___x_1699_ = lean_obj_once(&l_Lean_instInhabitedTagAttribute_default___closed__6, &l_Lean_instInhabitedTagAttribute_default___closed__6_once, _init_l_Lean_instInhabitedTagAttribute_default___closed__6);
return v___x_1699_;
}
}
static lean_object* _init_l_Lean_instInhabitedTagAttribute(void){
_start:
{
lean_object* v___x_1700_; 
v___x_1700_ = l_Lean_instInhabitedTagAttribute_default;
return v___x_1700_;
}
}
static lean_object* _init_l_Lean_registerTagAttribute___auto__1(void){
_start:
{
lean_object* v___x_1701_; 
v___x_1701_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__28, &l_Lean_AttributeImplCore_ref___autoParam___closed__28_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__28);
return v___x_1701_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__0(lean_object* v_x_1702_){
_start:
{
lean_object* v___x_1703_; 
v___x_1703_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___lam__2___closed__0));
return v___x_1703_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__0___boxed(lean_object* v_x_1704_){
_start:
{
lean_object* v_res_1705_; 
v_res_1705_ = l_Lean_registerTagAttribute___lam__0(v_x_1704_);
lean_dec(v_x_1704_);
return v_res_1705_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerTagAttribute_spec__0(lean_object* v_newState_1706_, lean_object* v_x_1707_, lean_object* v_x_1708_){
_start:
{
if (lean_obj_tag(v_x_1708_) == 0)
{
return v_x_1707_;
}
else
{
lean_object* v_head_1709_; lean_object* v_tail_1710_; uint8_t v___x_1711_; 
v_head_1709_ = lean_ctor_get(v_x_1708_, 0);
lean_inc(v_head_1709_);
v_tail_1710_ = lean_ctor_get(v_x_1708_, 1);
lean_inc(v_tail_1710_);
lean_dec_ref_known(v_x_1708_, 2);
v___x_1711_ = l_Lean_NameSet_contains(v_newState_1706_, v_head_1709_);
if (v___x_1711_ == 0)
{
lean_dec(v_head_1709_);
v_x_1708_ = v_tail_1710_;
goto _start;
}
else
{
lean_object* v___x_1713_; 
v___x_1713_ = l_Lean_NameSet_insert(v_x_1707_, v_head_1709_);
v_x_1707_ = v___x_1713_;
v_x_1708_ = v_tail_1710_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerTagAttribute_spec__0___boxed(lean_object* v_newState_1715_, lean_object* v_x_1716_, lean_object* v_x_1717_){
_start:
{
lean_object* v_res_1718_; 
v_res_1718_ = l_List_foldl___at___00Lean_registerTagAttribute_spec__0(v_newState_1715_, v_x_1716_, v_x_1717_);
lean_dec(v_newState_1715_);
return v_res_1718_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__1(lean_object* v_x_1719_, lean_object* v_newState_1720_, lean_object* v_newConsts_1721_, lean_object* v_s_1722_){
_start:
{
lean_object* v___x_1723_; 
v___x_1723_ = l_List_foldl___at___00Lean_registerTagAttribute_spec__0(v_newState_1720_, v_s_1722_, v_newConsts_1721_);
return v___x_1723_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__1___boxed(lean_object* v_x_1724_, lean_object* v_newState_1725_, lean_object* v_newConsts_1726_, lean_object* v_s_1727_){
_start:
{
lean_object* v_res_1728_; 
v_res_1728_ = l_Lean_registerTagAttribute___lam__1(v_x_1724_, v_newState_1725_, v_newConsts_1726_, v_s_1727_);
lean_dec(v_newState_1725_);
lean_dec(v_x_1724_);
return v_res_1728_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__2(lean_object* v_s_1741_){
_start:
{
lean_object* v___x_1742_; lean_object* v___y_1744_; 
v___x_1742_ = ((lean_object*)(l_Lean_registerTagAttribute___lam__2___closed__5));
if (lean_obj_tag(v_s_1741_) == 0)
{
lean_object* v_size_1748_; 
v_size_1748_ = lean_ctor_get(v_s_1741_, 0);
lean_inc(v_size_1748_);
lean_dec_ref_known(v_s_1741_, 5);
v___y_1744_ = v_size_1748_;
goto v___jp_1743_;
}
else
{
lean_object* v___x_1749_; 
v___x_1749_ = lean_unsigned_to_nat(0u);
v___y_1744_ = v___x_1749_;
goto v___jp_1743_;
}
v___jp_1743_:
{
lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; 
v___x_1745_ = l_Nat_reprFast(v___y_1744_);
v___x_1746_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1746_, 0, v___x_1745_);
v___x_1747_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1747_, 0, v___x_1742_);
lean_ctor_set(v___x_1747_, 1, v___x_1746_);
return v___x_1747_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4___redArg(lean_object* v_hi_1750_, lean_object* v_pivot_1751_, lean_object* v_as_1752_, lean_object* v_i_1753_, lean_object* v_k_1754_){
_start:
{
uint8_t v___x_1755_; 
v___x_1755_ = lean_nat_dec_lt(v_k_1754_, v_hi_1750_);
if (v___x_1755_ == 0)
{
lean_object* v___x_1756_; lean_object* v___x_1757_; 
lean_dec(v_k_1754_);
v___x_1756_ = lean_array_fswap(v_as_1752_, v_i_1753_, v_hi_1750_);
v___x_1757_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1757_, 0, v_i_1753_);
lean_ctor_set(v___x_1757_, 1, v___x_1756_);
return v___x_1757_;
}
else
{
lean_object* v___x_1758_; uint8_t v___x_1759_; 
v___x_1758_ = lean_array_fget_borrowed(v_as_1752_, v_k_1754_);
v___x_1759_ = l_Lean_Name_quickLt(v___x_1758_, v_pivot_1751_);
if (v___x_1759_ == 0)
{
lean_object* v___x_1760_; lean_object* v___x_1761_; 
v___x_1760_ = lean_unsigned_to_nat(1u);
v___x_1761_ = lean_nat_add(v_k_1754_, v___x_1760_);
lean_dec(v_k_1754_);
v_k_1754_ = v___x_1761_;
goto _start;
}
else
{
lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; 
v___x_1763_ = lean_array_fswap(v_as_1752_, v_i_1753_, v_k_1754_);
v___x_1764_ = lean_unsigned_to_nat(1u);
v___x_1765_ = lean_nat_add(v_i_1753_, v___x_1764_);
lean_dec(v_i_1753_);
v___x_1766_ = lean_nat_add(v_k_1754_, v___x_1764_);
lean_dec(v_k_1754_);
v_as_1752_ = v___x_1763_;
v_i_1753_ = v___x_1765_;
v_k_1754_ = v___x_1766_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4___redArg___boxed(lean_object* v_hi_1768_, lean_object* v_pivot_1769_, lean_object* v_as_1770_, lean_object* v_i_1771_, lean_object* v_k_1772_){
_start:
{
lean_object* v_res_1773_; 
v_res_1773_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4___redArg(v_hi_1768_, v_pivot_1769_, v_as_1770_, v_i_1771_, v_k_1772_);
lean_dec(v_pivot_1769_);
lean_dec(v_hi_1768_);
return v_res_1773_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___redArg(lean_object* v_n_1774_, lean_object* v_as_1775_, lean_object* v_lo_1776_, lean_object* v_hi_1777_){
_start:
{
lean_object* v___y_1779_; uint8_t v___x_1789_; 
v___x_1789_ = lean_nat_dec_lt(v_lo_1776_, v_hi_1777_);
if (v___x_1789_ == 0)
{
lean_dec(v_lo_1776_);
return v_as_1775_;
}
else
{
lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v_mid_1792_; lean_object* v___y_1794_; lean_object* v___y_1800_; lean_object* v___x_1805_; lean_object* v___x_1806_; uint8_t v___x_1807_; 
v___x_1790_ = lean_nat_add(v_lo_1776_, v_hi_1777_);
v___x_1791_ = lean_unsigned_to_nat(1u);
v_mid_1792_ = lean_nat_shiftr(v___x_1790_, v___x_1791_);
lean_dec(v___x_1790_);
v___x_1805_ = lean_array_fget_borrowed(v_as_1775_, v_mid_1792_);
v___x_1806_ = lean_array_fget_borrowed(v_as_1775_, v_lo_1776_);
v___x_1807_ = l_Lean_Name_quickLt(v___x_1805_, v___x_1806_);
if (v___x_1807_ == 0)
{
v___y_1800_ = v_as_1775_;
goto v___jp_1799_;
}
else
{
lean_object* v___x_1808_; 
v___x_1808_ = lean_array_fswap(v_as_1775_, v_lo_1776_, v_mid_1792_);
v___y_1800_ = v___x_1808_;
goto v___jp_1799_;
}
v___jp_1793_:
{
lean_object* v___x_1795_; lean_object* v___x_1796_; uint8_t v___x_1797_; 
v___x_1795_ = lean_array_fget_borrowed(v___y_1794_, v_mid_1792_);
v___x_1796_ = lean_array_fget_borrowed(v___y_1794_, v_hi_1777_);
v___x_1797_ = l_Lean_Name_quickLt(v___x_1795_, v___x_1796_);
if (v___x_1797_ == 0)
{
lean_dec(v_mid_1792_);
v___y_1779_ = v___y_1794_;
goto v___jp_1778_;
}
else
{
lean_object* v___x_1798_; 
v___x_1798_ = lean_array_fswap(v___y_1794_, v_mid_1792_, v_hi_1777_);
lean_dec(v_mid_1792_);
v___y_1779_ = v___x_1798_;
goto v___jp_1778_;
}
}
v___jp_1799_:
{
lean_object* v___x_1801_; lean_object* v___x_1802_; uint8_t v___x_1803_; 
v___x_1801_ = lean_array_fget_borrowed(v___y_1800_, v_hi_1777_);
v___x_1802_ = lean_array_fget_borrowed(v___y_1800_, v_lo_1776_);
v___x_1803_ = l_Lean_Name_quickLt(v___x_1801_, v___x_1802_);
if (v___x_1803_ == 0)
{
v___y_1794_ = v___y_1800_;
goto v___jp_1793_;
}
else
{
lean_object* v___x_1804_; 
v___x_1804_ = lean_array_fswap(v___y_1800_, v_lo_1776_, v_hi_1777_);
v___y_1794_ = v___x_1804_;
goto v___jp_1793_;
}
}
}
v___jp_1778_:
{
lean_object* v_pivot_1780_; lean_object* v___x_1781_; lean_object* v_fst_1782_; lean_object* v_snd_1783_; uint8_t v___x_1784_; 
v_pivot_1780_ = lean_array_fget(v___y_1779_, v_hi_1777_);
lean_inc_n(v_lo_1776_, 2);
v___x_1781_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4___redArg(v_hi_1777_, v_pivot_1780_, v___y_1779_, v_lo_1776_, v_lo_1776_);
lean_dec(v_pivot_1780_);
v_fst_1782_ = lean_ctor_get(v___x_1781_, 0);
lean_inc(v_fst_1782_);
v_snd_1783_ = lean_ctor_get(v___x_1781_, 1);
lean_inc(v_snd_1783_);
lean_dec_ref(v___x_1781_);
v___x_1784_ = lean_nat_dec_le(v_hi_1777_, v_fst_1782_);
if (v___x_1784_ == 0)
{
lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; 
v___x_1785_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___redArg(v_n_1774_, v_snd_1783_, v_lo_1776_, v_fst_1782_);
v___x_1786_ = lean_unsigned_to_nat(1u);
v___x_1787_ = lean_nat_add(v_fst_1782_, v___x_1786_);
lean_dec(v_fst_1782_);
v_as_1775_ = v___x_1785_;
v_lo_1776_ = v___x_1787_;
goto _start;
}
else
{
lean_dec(v_fst_1782_);
lean_dec(v_lo_1776_);
return v_snd_1783_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___redArg___boxed(lean_object* v_n_1809_, lean_object* v_as_1810_, lean_object* v_lo_1811_, lean_object* v_hi_1812_){
_start:
{
lean_object* v_res_1813_; 
v_res_1813_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___redArg(v_n_1809_, v_as_1810_, v_lo_1811_, v_hi_1812_);
lean_dec(v_hi_1812_);
lean_dec(v_n_1809_);
return v_res_1813_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerTagAttribute_spec__2(lean_object* v_env_1814_, lean_object* v_as_1815_, size_t v_i_1816_, size_t v_stop_1817_, lean_object* v_b_1818_){
_start:
{
lean_object* v___y_1820_; uint8_t v___x_1824_; 
v___x_1824_ = lean_usize_dec_eq(v_i_1816_, v_stop_1817_);
if (v___x_1824_ == 0)
{
lean_object* v___x_1825_; uint8_t v___x_1826_; lean_object* v___x_1827_; uint8_t v___x_1828_; 
v___x_1825_ = lean_array_uget_borrowed(v_as_1815_, v_i_1816_);
v___x_1826_ = 1;
lean_inc_ref(v_env_1814_);
v___x_1827_ = l_Lean_Environment_setExporting(v_env_1814_, v___x_1826_);
lean_inc(v___x_1825_);
v___x_1828_ = l_Lean_Environment_contains(v___x_1827_, v___x_1825_, v___x_1824_);
if (v___x_1828_ == 0)
{
v___y_1820_ = v_b_1818_;
goto v___jp_1819_;
}
else
{
lean_object* v___x_1829_; 
lean_inc(v___x_1825_);
v___x_1829_ = lean_array_push(v_b_1818_, v___x_1825_);
v___y_1820_ = v___x_1829_;
goto v___jp_1819_;
}
}
else
{
lean_dec_ref(v_env_1814_);
return v_b_1818_;
}
v___jp_1819_:
{
size_t v___x_1821_; size_t v___x_1822_; 
v___x_1821_ = ((size_t)1ULL);
v___x_1822_ = lean_usize_add(v_i_1816_, v___x_1821_);
v_i_1816_ = v___x_1822_;
v_b_1818_ = v___y_1820_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerTagAttribute_spec__2___boxed(lean_object* v_env_1830_, lean_object* v_as_1831_, lean_object* v_i_1832_, lean_object* v_stop_1833_, lean_object* v_b_1834_){
_start:
{
size_t v_i_boxed_1835_; size_t v_stop_boxed_1836_; lean_object* v_res_1837_; 
v_i_boxed_1835_ = lean_unbox_usize(v_i_1832_);
lean_dec(v_i_1832_);
v_stop_boxed_1836_ = lean_unbox_usize(v_stop_1833_);
lean_dec(v_stop_1833_);
v_res_1837_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerTagAttribute_spec__2(v_env_1830_, v_as_1831_, v_i_boxed_1835_, v_stop_boxed_1836_, v_b_1834_);
lean_dec_ref(v_as_1831_);
return v_res_1837_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerTagAttribute_spec__1_spec__1(lean_object* v_init_1838_, lean_object* v_x_1839_){
_start:
{
if (lean_obj_tag(v_x_1839_) == 0)
{
lean_object* v_k_1840_; lean_object* v_l_1841_; lean_object* v_r_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; 
v_k_1840_ = lean_ctor_get(v_x_1839_, 1);
lean_inc(v_k_1840_);
v_l_1841_ = lean_ctor_get(v_x_1839_, 3);
lean_inc(v_l_1841_);
v_r_1842_ = lean_ctor_get(v_x_1839_, 4);
lean_inc(v_r_1842_);
lean_dec_ref_known(v_x_1839_, 5);
v___x_1843_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerTagAttribute_spec__1_spec__1(v_init_1838_, v_l_1841_);
v___x_1844_ = lean_array_push(v___x_1843_, v_k_1840_);
v_init_1838_ = v___x_1844_;
v_x_1839_ = v_r_1842_;
goto _start;
}
else
{
return v_init_1838_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__3(lean_object* v_env_1846_, lean_object* v_es_1847_){
_start:
{
lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v___y_1851_; lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___y_1868_; lean_object* v___y_1869_; uint8_t v___x_1871_; 
v___x_1848_ = lean_unsigned_to_nat(0u);
v___x_1849_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___lam__2___closed__0));
v___x_1865_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerTagAttribute_spec__1_spec__1(v___x_1849_, v_es_1847_);
v___x_1866_ = lean_array_get_size(v___x_1865_);
v___x_1871_ = lean_nat_dec_eq(v___x_1866_, v___x_1848_);
if (v___x_1871_ == 0)
{
lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___y_1875_; uint8_t v___x_1877_; 
v___x_1872_ = lean_unsigned_to_nat(1u);
v___x_1873_ = lean_nat_sub(v___x_1866_, v___x_1872_);
v___x_1877_ = lean_nat_dec_le(v___x_1848_, v___x_1873_);
if (v___x_1877_ == 0)
{
lean_inc(v___x_1873_);
v___y_1875_ = v___x_1873_;
goto v___jp_1874_;
}
else
{
v___y_1875_ = v___x_1848_;
goto v___jp_1874_;
}
v___jp_1874_:
{
uint8_t v___x_1876_; 
v___x_1876_ = lean_nat_dec_le(v___y_1875_, v___x_1873_);
if (v___x_1876_ == 0)
{
lean_dec(v___x_1873_);
lean_inc(v___y_1875_);
v___y_1868_ = v___y_1875_;
v___y_1869_ = v___y_1875_;
goto v___jp_1867_;
}
else
{
v___y_1868_ = v___y_1875_;
v___y_1869_ = v___x_1873_;
goto v___jp_1867_;
}
}
}
else
{
v___y_1851_ = v___x_1865_;
goto v___jp_1850_;
}
v___jp_1850_:
{
lean_object* v___x_1852_; uint8_t v___x_1853_; 
v___x_1852_ = lean_array_get_size(v___y_1851_);
v___x_1853_ = lean_nat_dec_lt(v___x_1848_, v___x_1852_);
if (v___x_1853_ == 0)
{
lean_object* v___x_1854_; 
lean_dec_ref(v_env_1846_);
v___x_1854_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1854_, 0, v___x_1849_);
lean_ctor_set(v___x_1854_, 1, v___x_1849_);
lean_ctor_set(v___x_1854_, 2, v___y_1851_);
return v___x_1854_;
}
else
{
uint8_t v___x_1855_; 
v___x_1855_ = lean_nat_dec_le(v___x_1852_, v___x_1852_);
if (v___x_1855_ == 0)
{
if (v___x_1853_ == 0)
{
lean_object* v___x_1856_; 
lean_dec_ref(v_env_1846_);
v___x_1856_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1856_, 0, v___x_1849_);
lean_ctor_set(v___x_1856_, 1, v___x_1849_);
lean_ctor_set(v___x_1856_, 2, v___y_1851_);
return v___x_1856_;
}
else
{
size_t v___x_1857_; size_t v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; 
v___x_1857_ = ((size_t)0ULL);
v___x_1858_ = lean_usize_of_nat(v___x_1852_);
v___x_1859_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerTagAttribute_spec__2(v_env_1846_, v___y_1851_, v___x_1857_, v___x_1858_, v___x_1849_);
lean_inc_ref(v___x_1859_);
v___x_1860_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1860_, 0, v___x_1859_);
lean_ctor_set(v___x_1860_, 1, v___x_1859_);
lean_ctor_set(v___x_1860_, 2, v___y_1851_);
return v___x_1860_;
}
}
else
{
size_t v___x_1861_; size_t v___x_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; 
v___x_1861_ = ((size_t)0ULL);
v___x_1862_ = lean_usize_of_nat(v___x_1852_);
v___x_1863_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerTagAttribute_spec__2(v_env_1846_, v___y_1851_, v___x_1861_, v___x_1862_, v___x_1849_);
lean_inc_ref(v___x_1863_);
v___x_1864_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1864_, 0, v___x_1863_);
lean_ctor_set(v___x_1864_, 1, v___x_1863_);
lean_ctor_set(v___x_1864_, 2, v___y_1851_);
return v___x_1864_;
}
}
}
v___jp_1867_:
{
lean_object* v___x_1870_; 
v___x_1870_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___redArg(v___x_1866_, v___x_1865_, v___y_1868_, v___y_1869_);
lean_dec(v___y_1869_);
v___y_1851_ = v___x_1870_;
goto v___jp_1850_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__4(lean_object* v___x_1878_, lean_object* v_x_1879_, lean_object* v_x_1880_){
_start:
{
lean_object* v___x_1882_; 
v___x_1882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1882_, 0, v___x_1878_);
return v___x_1882_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__4___boxed(lean_object* v___x_1883_, lean_object* v_x_1884_, lean_object* v_x_1885_, lean_object* v___y_1886_){
_start:
{
lean_object* v_res_1887_; 
v_res_1887_ = l_Lean_registerTagAttribute___lam__4(v___x_1883_, v_x_1884_, v_x_1885_);
lean_dec_ref(v_x_1885_);
lean_dec_ref(v_x_1884_);
return v_res_1887_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__5(lean_object* v___x_1888_){
_start:
{
lean_object* v___x_1890_; 
v___x_1890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1890_, 0, v___x_1888_);
return v___x_1890_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__5___boxed(lean_object* v___x_1891_, lean_object* v___y_1892_){
_start:
{
lean_object* v_res_1893_; 
v_res_1893_ = l_Lean_registerTagAttribute___lam__5(v___x_1891_);
return v_res_1893_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__6(lean_object* v_name_1894_, lean_object* v_decl_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_){
_start:
{
lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; 
v___x_1899_ = lean_obj_once(&l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1, &l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1_once, _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1);
v___x_1900_ = l_Lean_MessageData_ofName(v_name_1894_);
v___x_1901_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1901_, 0, v___x_1899_);
lean_ctor_set(v___x_1901_, 1, v___x_1900_);
v___x_1902_ = lean_obj_once(&l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3, &l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3_once, _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3);
v___x_1903_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1903_, 0, v___x_1901_);
lean_ctor_set(v___x_1903_, 1, v___x_1902_);
v___x_1904_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_1903_, v___y_1896_, v___y_1897_);
return v___x_1904_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__6___boxed(lean_object* v_name_1905_, lean_object* v_decl_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_){
_start:
{
lean_object* v_res_1910_; 
v_res_1910_ = l_Lean_registerTagAttribute___lam__6(v_name_1905_, v_decl_1906_, v___y_1907_, v___y_1908_);
lean_dec(v___y_1908_);
lean_dec_ref(v___y_1907_);
lean_dec(v_decl_1906_);
return v_res_1910_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg(lean_object* v_attrName_1911_, lean_object* v_declName_1912_, lean_object* v___y_1913_, lean_object* v___y_1914_){
_start:
{
lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; uint8_t v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; 
v___x_1916_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1);
v___x_1917_ = l_Lean_MessageData_ofName(v_attrName_1911_);
v___x_1918_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1918_, 0, v___x_1916_);
lean_ctor_set(v___x_1918_, 1, v___x_1917_);
v___x_1919_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__3, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__3_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__3);
v___x_1920_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1920_, 0, v___x_1918_);
lean_ctor_set(v___x_1920_, 1, v___x_1919_);
v___x_1921_ = 0;
v___x_1922_ = l_Lean_MessageData_ofConstName(v_declName_1912_, v___x_1921_);
v___x_1923_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1923_, 0, v___x_1920_);
lean_ctor_set(v___x_1923_, 1, v___x_1922_);
v___x_1924_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__5, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__5_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__5);
v___x_1925_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1925_, 0, v___x_1923_);
lean_ctor_set(v___x_1925_, 1, v___x_1924_);
v___x_1926_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_1925_, v___y_1913_, v___y_1914_);
return v___x_1926_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg___boxed(lean_object* v_attrName_1927_, lean_object* v_declName_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_, lean_object* v___y_1931_){
_start:
{
lean_object* v_res_1932_; 
v_res_1932_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg(v_attrName_1927_, v_declName_1928_, v___y_1929_, v___y_1930_);
lean_dec(v___y_1930_);
lean_dec_ref(v___y_1929_);
return v_res_1932_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___redArg(lean_object* v_attrName_1933_, lean_object* v_declName_1934_, lean_object* v_asyncPrefix_x3f_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_){
_start:
{
lean_object* v___y_1940_; 
if (lean_obj_tag(v_asyncPrefix_x3f_1935_) == 0)
{
lean_object* v___x_1953_; 
v___x_1953_ = l_Lean_MessageData_nil;
v___y_1940_ = v___x_1953_;
goto v___jp_1939_;
}
else
{
lean_object* v_val_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; 
v_val_1954_ = lean_ctor_get(v_asyncPrefix_x3f_1935_, 0);
lean_inc(v_val_1954_);
lean_dec_ref_known(v_asyncPrefix_x3f_1935_, 1);
v___x_1955_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___redArg___closed__3, &l_Lean_throwAttrNotInAsyncCtx___redArg___closed__3_once, _init_l_Lean_throwAttrNotInAsyncCtx___redArg___closed__3);
v___x_1956_ = l_Lean_MessageData_ofName(v_val_1954_);
v___x_1957_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1957_, 0, v___x_1955_);
lean_ctor_set(v___x_1957_, 1, v___x_1956_);
v___x_1958_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__5, &l_Lean_throwAttrMustBeGlobal___redArg___closed__5_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__5);
v___x_1959_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1959_, 0, v___x_1957_);
lean_ctor_set(v___x_1959_, 1, v___x_1958_);
v___y_1940_ = v___x_1959_;
goto v___jp_1939_;
}
v___jp_1939_:
{
lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; uint8_t v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; 
v___x_1941_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1);
v___x_1942_ = l_Lean_MessageData_ofName(v_attrName_1933_);
v___x_1943_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1943_, 0, v___x_1941_);
lean_ctor_set(v___x_1943_, 1, v___x_1942_);
v___x_1944_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__3, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__3_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__3);
v___x_1945_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1945_, 0, v___x_1943_);
lean_ctor_set(v___x_1945_, 1, v___x_1944_);
v___x_1946_ = 0;
v___x_1947_ = l_Lean_MessageData_ofConstName(v_declName_1934_, v___x_1946_);
v___x_1948_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1948_, 0, v___x_1945_);
lean_ctor_set(v___x_1948_, 1, v___x_1947_);
v___x_1949_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___redArg___closed__1, &l_Lean_throwAttrNotInAsyncCtx___redArg___closed__1_once, _init_l_Lean_throwAttrNotInAsyncCtx___redArg___closed__1);
v___x_1950_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1950_, 0, v___x_1948_);
lean_ctor_set(v___x_1950_, 1, v___x_1949_);
v___x_1951_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1951_, 0, v___x_1950_);
lean_ctor_set(v___x_1951_, 1, v___y_1940_);
v___x_1952_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_1951_, v___y_1936_, v___y_1937_);
return v___x_1952_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___redArg___boxed(lean_object* v_attrName_1960_, lean_object* v_declName_1961_, lean_object* v_asyncPrefix_x3f_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_){
_start:
{
lean_object* v_res_1966_; 
v_res_1966_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___redArg(v_attrName_1960_, v_declName_1961_, v_asyncPrefix_x3f_1962_, v___y_1963_, v___y_1964_);
lean_dec(v___y_1964_);
lean_dec_ref(v___y_1963_);
return v_res_1966_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg(lean_object* v_name_1967_, uint8_t v_kind_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_){
_start:
{
lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___y_1978_; 
v___x_1972_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__1, &l_Lean_throwAttrMustBeGlobal___redArg___closed__1_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__1);
v___x_1973_ = l_Lean_MessageData_ofName(v_name_1967_);
v___x_1974_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1974_, 0, v___x_1972_);
lean_ctor_set(v___x_1974_, 1, v___x_1973_);
v___x_1975_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__3, &l_Lean_throwAttrMustBeGlobal___redArg___closed__3_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__3);
v___x_1976_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1976_, 0, v___x_1974_);
lean_ctor_set(v___x_1976_, 1, v___x_1975_);
switch(v_kind_1968_)
{
case 0:
{
lean_object* v___x_1985_; 
v___x_1985_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__0));
v___y_1978_ = v___x_1985_;
goto v___jp_1977_;
}
case 1:
{
lean_object* v___x_1986_; 
v___x_1986_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__1));
v___y_1978_ = v___x_1986_;
goto v___jp_1977_;
}
default: 
{
lean_object* v___x_1987_; 
v___x_1987_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__2));
v___y_1978_ = v___x_1987_;
goto v___jp_1977_;
}
}
v___jp_1977_:
{
lean_object* v___x_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; 
lean_inc_ref(v___y_1978_);
v___x_1979_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1979_, 0, v___y_1978_);
v___x_1980_ = l_Lean_MessageData_ofFormat(v___x_1979_);
v___x_1981_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1981_, 0, v___x_1976_);
lean_ctor_set(v___x_1981_, 1, v___x_1980_);
v___x_1982_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__5, &l_Lean_throwAttrMustBeGlobal___redArg___closed__5_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__5);
v___x_1983_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1983_, 0, v___x_1981_);
lean_ctor_set(v___x_1983_, 1, v___x_1982_);
v___x_1984_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_1983_, v___y_1969_, v___y_1970_);
return v___x_1984_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg___boxed(lean_object* v_name_1988_, lean_object* v_kind_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_){
_start:
{
uint8_t v_kind_boxed_1993_; lean_object* v_res_1994_; 
v_kind_boxed_1993_ = lean_unbox(v_kind_1989_);
v_res_1994_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg(v_name_1988_, v_kind_boxed_1993_, v___y_1990_, v___y_1991_);
lean_dec(v___y_1991_);
lean_dec_ref(v___y_1990_);
return v_res_1994_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__7(lean_object* v_validate_1995_, lean_object* v_a_1996_, lean_object* v_name_1997_, lean_object* v_decl_1998_, lean_object* v_stx_1999_, uint8_t v_kind_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_){
_start:
{
lean_object* v___y_2005_; lean_object* v___y_2006_; lean_object* v___y_2040_; lean_object* v___y_2041_; lean_object* v___y_2042_; lean_object* v___y_2049_; lean_object* v___y_2050_; lean_object* v___x_2055_; 
v___x_2055_ = l_Lean_Attribute_Builtin_ensureNoArgs(v_stx_1999_, v___y_2001_, v___y_2002_);
if (lean_obj_tag(v___x_2055_) == 0)
{
uint8_t v___x_2056_; uint8_t v___x_2057_; 
lean_dec_ref_known(v___x_2055_, 1);
v___x_2056_ = 0;
v___x_2057_ = l_Lean_instBEqAttributeKind_beq(v_kind_2000_, v___x_2056_);
if (v___x_2057_ == 0)
{
lean_object* v___x_2058_; 
lean_dec(v_decl_1998_);
lean_dec_ref(v_a_1996_);
lean_dec_ref(v_validate_1995_);
v___x_2058_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg(v_name_1997_, v_kind_2000_, v___y_2001_, v___y_2002_);
return v___x_2058_;
}
else
{
v___y_2049_ = v___y_2001_;
v___y_2050_ = v___y_2002_;
goto v___jp_2048_;
}
}
else
{
lean_dec(v_decl_1998_);
lean_dec(v_name_1997_);
lean_dec_ref(v_a_1996_);
lean_dec_ref(v_validate_1995_);
return v___x_2055_;
}
v___jp_2004_:
{
lean_object* v___x_2007_; 
lean_inc(v___y_2006_);
lean_inc_ref(v___y_2005_);
lean_inc(v_decl_1998_);
v___x_2007_ = lean_apply_4(v_validate_1995_, v_decl_1998_, v___y_2005_, v___y_2006_, lean_box(0));
if (lean_obj_tag(v___x_2007_) == 0)
{
lean_object* v___x_2009_; uint8_t v_isShared_2010_; uint8_t v_isSharedCheck_2037_; 
v_isSharedCheck_2037_ = !lean_is_exclusive(v___x_2007_);
if (v_isSharedCheck_2037_ == 0)
{
lean_object* v_unused_2038_; 
v_unused_2038_ = lean_ctor_get(v___x_2007_, 0);
lean_dec(v_unused_2038_);
v___x_2009_ = v___x_2007_;
v_isShared_2010_ = v_isSharedCheck_2037_;
goto v_resetjp_2008_;
}
else
{
lean_dec(v___x_2007_);
v___x_2009_ = lean_box(0);
v_isShared_2010_ = v_isSharedCheck_2037_;
goto v_resetjp_2008_;
}
v_resetjp_2008_:
{
lean_object* v___x_2011_; lean_object* v_toEnvExtension_2012_; lean_object* v_env_2013_; lean_object* v_nextMacroScope_2014_; lean_object* v_ngen_2015_; lean_object* v_auxDeclNGen_2016_; lean_object* v_traceState_2017_; lean_object* v_messages_2018_; lean_object* v_infoState_2019_; lean_object* v_snapshotTasks_2020_; lean_object* v___x_2022_; uint8_t v_isShared_2023_; uint8_t v_isSharedCheck_2035_; 
v___x_2011_ = lean_st_ref_take(v___y_2006_);
v_toEnvExtension_2012_ = lean_ctor_get(v_a_1996_, 0);
v_env_2013_ = lean_ctor_get(v___x_2011_, 0);
v_nextMacroScope_2014_ = lean_ctor_get(v___x_2011_, 1);
v_ngen_2015_ = lean_ctor_get(v___x_2011_, 2);
v_auxDeclNGen_2016_ = lean_ctor_get(v___x_2011_, 3);
v_traceState_2017_ = lean_ctor_get(v___x_2011_, 4);
v_messages_2018_ = lean_ctor_get(v___x_2011_, 6);
v_infoState_2019_ = lean_ctor_get(v___x_2011_, 7);
v_snapshotTasks_2020_ = lean_ctor_get(v___x_2011_, 8);
v_isSharedCheck_2035_ = !lean_is_exclusive(v___x_2011_);
if (v_isSharedCheck_2035_ == 0)
{
lean_object* v_unused_2036_; 
v_unused_2036_ = lean_ctor_get(v___x_2011_, 5);
lean_dec(v_unused_2036_);
v___x_2022_ = v___x_2011_;
v_isShared_2023_ = v_isSharedCheck_2035_;
goto v_resetjp_2021_;
}
else
{
lean_inc(v_snapshotTasks_2020_);
lean_inc(v_infoState_2019_);
lean_inc(v_messages_2018_);
lean_inc(v_traceState_2017_);
lean_inc(v_auxDeclNGen_2016_);
lean_inc(v_ngen_2015_);
lean_inc(v_nextMacroScope_2014_);
lean_inc(v_env_2013_);
lean_dec(v___x_2011_);
v___x_2022_ = lean_box(0);
v_isShared_2023_ = v_isSharedCheck_2035_;
goto v_resetjp_2021_;
}
v_resetjp_2021_:
{
lean_object* v_asyncMode_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2028_; 
v_asyncMode_2024_ = lean_ctor_get(v_toEnvExtension_2012_, 2);
lean_inc(v_asyncMode_2024_);
lean_inc(v_decl_1998_);
v___x_2025_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_a_1996_, v_env_2013_, v_decl_1998_, v_asyncMode_2024_, v_decl_1998_);
lean_dec(v_asyncMode_2024_);
v___x_2026_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2);
if (v_isShared_2023_ == 0)
{
lean_ctor_set(v___x_2022_, 5, v___x_2026_);
lean_ctor_set(v___x_2022_, 0, v___x_2025_);
v___x_2028_ = v___x_2022_;
goto v_reusejp_2027_;
}
else
{
lean_object* v_reuseFailAlloc_2034_; 
v_reuseFailAlloc_2034_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2034_, 0, v___x_2025_);
lean_ctor_set(v_reuseFailAlloc_2034_, 1, v_nextMacroScope_2014_);
lean_ctor_set(v_reuseFailAlloc_2034_, 2, v_ngen_2015_);
lean_ctor_set(v_reuseFailAlloc_2034_, 3, v_auxDeclNGen_2016_);
lean_ctor_set(v_reuseFailAlloc_2034_, 4, v_traceState_2017_);
lean_ctor_set(v_reuseFailAlloc_2034_, 5, v___x_2026_);
lean_ctor_set(v_reuseFailAlloc_2034_, 6, v_messages_2018_);
lean_ctor_set(v_reuseFailAlloc_2034_, 7, v_infoState_2019_);
lean_ctor_set(v_reuseFailAlloc_2034_, 8, v_snapshotTasks_2020_);
v___x_2028_ = v_reuseFailAlloc_2034_;
goto v_reusejp_2027_;
}
v_reusejp_2027_:
{
lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2032_; 
v___x_2029_ = lean_st_ref_set(v___y_2006_, v___x_2028_);
v___x_2030_ = lean_box(0);
if (v_isShared_2010_ == 0)
{
lean_ctor_set(v___x_2009_, 0, v___x_2030_);
v___x_2032_ = v___x_2009_;
goto v_reusejp_2031_;
}
else
{
lean_object* v_reuseFailAlloc_2033_; 
v_reuseFailAlloc_2033_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2033_, 0, v___x_2030_);
v___x_2032_ = v_reuseFailAlloc_2033_;
goto v_reusejp_2031_;
}
v_reusejp_2031_:
{
return v___x_2032_;
}
}
}
}
}
else
{
lean_dec(v_decl_1998_);
lean_dec_ref(v_a_1996_);
return v___x_2007_;
}
}
v___jp_2039_:
{
lean_object* v_toEnvExtension_2043_; lean_object* v_asyncMode_2044_; uint8_t v___x_2045_; 
v_toEnvExtension_2043_ = lean_ctor_get(v_a_1996_, 0);
v_asyncMode_2044_ = lean_ctor_get(v_toEnvExtension_2043_, 2);
lean_inc(v_decl_1998_);
lean_inc_ref(v___y_2040_);
v___x_2045_ = l_Lean_EnvExtension_asyncMayModify___redArg(v___y_2040_, v_decl_1998_, v_asyncMode_2044_);
if (v___x_2045_ == 0)
{
lean_object* v___x_2046_; lean_object* v___x_2047_; 
lean_dec_ref(v_a_1996_);
lean_dec_ref(v_validate_1995_);
v___x_2046_ = l_Lean_Environment_asyncPrefix_x3f(v___y_2040_);
v___x_2047_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___redArg(v_name_1997_, v_decl_1998_, v___x_2046_, v___y_2041_, v___y_2042_);
return v___x_2047_;
}
else
{
lean_dec_ref(v___y_2040_);
lean_dec(v_name_1997_);
v___y_2005_ = v___y_2041_;
v___y_2006_ = v___y_2042_;
goto v___jp_2004_;
}
}
v___jp_2048_:
{
lean_object* v___x_2051_; lean_object* v_env_2052_; lean_object* v___x_2053_; 
v___x_2051_ = lean_st_ref_get(v___y_2050_);
v_env_2052_ = lean_ctor_get(v___x_2051_, 0);
lean_inc_ref(v_env_2052_);
lean_dec(v___x_2051_);
v___x_2053_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2052_, v_decl_1998_);
if (lean_obj_tag(v___x_2053_) == 0)
{
v___y_2040_ = v_env_2052_;
v___y_2041_ = v___y_2049_;
v___y_2042_ = v___y_2050_;
goto v___jp_2039_;
}
else
{
lean_object* v___x_2054_; 
lean_dec_ref_known(v___x_2053_, 1);
lean_dec_ref(v_env_2052_);
lean_dec_ref(v_a_1996_);
lean_dec_ref(v_validate_1995_);
v___x_2054_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg(v_name_1997_, v_decl_1998_, v___y_2049_, v___y_2050_);
return v___x_2054_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__7___boxed(lean_object* v_validate_2059_, lean_object* v_a_2060_, lean_object* v_name_2061_, lean_object* v_decl_2062_, lean_object* v_stx_2063_, lean_object* v_kind_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_, lean_object* v___y_2067_){
_start:
{
uint8_t v_kind_boxed_2068_; lean_object* v_res_2069_; 
v_kind_boxed_2068_ = lean_unbox(v_kind_2064_);
v_res_2069_ = l_Lean_registerTagAttribute___lam__7(v_validate_2059_, v_a_2060_, v_name_2061_, v_decl_2062_, v_stx_2063_, v_kind_boxed_2068_, v___y_2065_, v___y_2066_);
lean_dec(v___y_2066_);
lean_dec_ref(v___y_2065_);
return v_res_2069_;
}
}
static lean_object* _init_l_Lean_registerTagAttribute___closed__5(void){
_start:
{
lean_object* v___x_2075_; lean_object* v___f_2076_; 
v___x_2075_ = l_Lean_NameSet_empty;
v___f_2076_ = lean_alloc_closure((void*)(l_Lean_registerTagAttribute___lam__4___boxed), 4, 1);
lean_closure_set(v___f_2076_, 0, v___x_2075_);
return v___f_2076_;
}
}
static lean_object* _init_l_Lean_registerTagAttribute___closed__6(void){
_start:
{
lean_object* v___x_2077_; lean_object* v___f_2078_; 
v___x_2077_ = l_Lean_NameSet_empty;
v___f_2078_ = lean_alloc_closure((void*)(l_Lean_registerTagAttribute___lam__5___boxed), 2, 1);
lean_closure_set(v___f_2078_, 0, v___x_2077_);
return v___f_2078_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute(lean_object* v_name_2081_, lean_object* v_descr_2082_, lean_object* v_validate_2083_, lean_object* v_ref_2084_, uint8_t v_applicationTime_2085_, lean_object* v_asyncMode_2086_){
_start:
{
lean_object* v___f_2088_; lean_object* v___f_2089_; lean_object* v___f_2090_; lean_object* v___f_2091_; lean_object* v___f_2092_; lean_object* v___f_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; 
v___f_2088_ = ((lean_object*)(l_Lean_registerTagAttribute___closed__0));
v___f_2089_ = ((lean_object*)(l_Lean_registerTagAttribute___closed__2));
v___f_2090_ = ((lean_object*)(l_Lean_registerTagAttribute___closed__3));
v___f_2091_ = ((lean_object*)(l_Lean_registerTagAttribute___closed__4));
v___f_2092_ = lean_obj_once(&l_Lean_registerTagAttribute___closed__5, &l_Lean_registerTagAttribute___closed__5_once, _init_l_Lean_registerTagAttribute___closed__5);
v___f_2093_ = lean_obj_once(&l_Lean_registerTagAttribute___closed__6, &l_Lean_registerTagAttribute___closed__6_once, _init_l_Lean_registerTagAttribute___closed__6);
v___x_2094_ = ((lean_object*)(l_Lean_registerTagAttribute___closed__7));
lean_inc(v_ref_2084_);
v___x_2095_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_2095_, 0, v_ref_2084_);
lean_ctor_set(v___x_2095_, 1, v___f_2093_);
lean_ctor_set(v___x_2095_, 2, v___f_2092_);
lean_ctor_set(v___x_2095_, 3, v___f_2091_);
lean_ctor_set(v___x_2095_, 4, v___f_2090_);
lean_ctor_set(v___x_2095_, 5, v___f_2089_);
lean_ctor_set(v___x_2095_, 6, v_asyncMode_2086_);
lean_ctor_set(v___x_2095_, 7, v___x_2094_);
v___x_2096_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2096_, 0, v___x_2095_);
lean_ctor_set(v___x_2096_, 1, v___f_2088_);
v___x_2097_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_2096_);
if (lean_obj_tag(v___x_2097_) == 0)
{
lean_object* v_a_2098_; lean_object* v___f_2099_; lean_object* v___f_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; 
v_a_2098_ = lean_ctor_get(v___x_2097_, 0);
lean_inc_n(v_a_2098_, 2);
lean_dec_ref_known(v___x_2097_, 1);
lean_inc_n(v_name_2081_, 2);
v___f_2099_ = lean_alloc_closure((void*)(l_Lean_registerTagAttribute___lam__6___boxed), 5, 1);
lean_closure_set(v___f_2099_, 0, v_name_2081_);
v___f_2100_ = lean_alloc_closure((void*)(l_Lean_registerTagAttribute___lam__7___boxed), 9, 3);
lean_closure_set(v___f_2100_, 0, v_validate_2083_);
lean_closure_set(v___f_2100_, 1, v_a_2098_);
lean_closure_set(v___f_2100_, 2, v_name_2081_);
v___x_2101_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2101_, 0, v_ref_2084_);
lean_ctor_set(v___x_2101_, 1, v_name_2081_);
lean_ctor_set(v___x_2101_, 2, v_descr_2082_);
lean_ctor_set_uint8(v___x_2101_, sizeof(void*)*3, v_applicationTime_2085_);
v___x_2102_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2102_, 0, v___x_2101_);
lean_ctor_set(v___x_2102_, 1, v___f_2100_);
lean_ctor_set(v___x_2102_, 2, v___f_2099_);
lean_inc_ref(v___x_2102_);
v___x_2103_ = l_Lean_registerBuiltinAttribute(v___x_2102_);
if (lean_obj_tag(v___x_2103_) == 0)
{
lean_object* v___x_2105_; uint8_t v_isShared_2106_; uint8_t v_isSharedCheck_2111_; 
v_isSharedCheck_2111_ = !lean_is_exclusive(v___x_2103_);
if (v_isSharedCheck_2111_ == 0)
{
lean_object* v_unused_2112_; 
v_unused_2112_ = lean_ctor_get(v___x_2103_, 0);
lean_dec(v_unused_2112_);
v___x_2105_ = v___x_2103_;
v_isShared_2106_ = v_isSharedCheck_2111_;
goto v_resetjp_2104_;
}
else
{
lean_dec(v___x_2103_);
v___x_2105_ = lean_box(0);
v_isShared_2106_ = v_isSharedCheck_2111_;
goto v_resetjp_2104_;
}
v_resetjp_2104_:
{
lean_object* v___x_2107_; lean_object* v___x_2109_; 
v___x_2107_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2107_, 0, v___x_2102_);
lean_ctor_set(v___x_2107_, 1, v_a_2098_);
if (v_isShared_2106_ == 0)
{
lean_ctor_set(v___x_2105_, 0, v___x_2107_);
v___x_2109_ = v___x_2105_;
goto v_reusejp_2108_;
}
else
{
lean_object* v_reuseFailAlloc_2110_; 
v_reuseFailAlloc_2110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2110_, 0, v___x_2107_);
v___x_2109_ = v_reuseFailAlloc_2110_;
goto v_reusejp_2108_;
}
v_reusejp_2108_:
{
return v___x_2109_;
}
}
}
else
{
lean_object* v_a_2113_; lean_object* v___x_2115_; uint8_t v_isShared_2116_; uint8_t v_isSharedCheck_2120_; 
lean_dec_ref_known(v___x_2102_, 3);
lean_dec(v_a_2098_);
v_a_2113_ = lean_ctor_get(v___x_2103_, 0);
v_isSharedCheck_2120_ = !lean_is_exclusive(v___x_2103_);
if (v_isSharedCheck_2120_ == 0)
{
v___x_2115_ = v___x_2103_;
v_isShared_2116_ = v_isSharedCheck_2120_;
goto v_resetjp_2114_;
}
else
{
lean_inc(v_a_2113_);
lean_dec(v___x_2103_);
v___x_2115_ = lean_box(0);
v_isShared_2116_ = v_isSharedCheck_2120_;
goto v_resetjp_2114_;
}
v_resetjp_2114_:
{
lean_object* v___x_2118_; 
if (v_isShared_2116_ == 0)
{
v___x_2118_ = v___x_2115_;
goto v_reusejp_2117_;
}
else
{
lean_object* v_reuseFailAlloc_2119_; 
v_reuseFailAlloc_2119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2119_, 0, v_a_2113_);
v___x_2118_ = v_reuseFailAlloc_2119_;
goto v_reusejp_2117_;
}
v_reusejp_2117_:
{
return v___x_2118_;
}
}
}
}
else
{
lean_object* v_a_2121_; lean_object* v___x_2123_; uint8_t v_isShared_2124_; uint8_t v_isSharedCheck_2128_; 
lean_dec(v_ref_2084_);
lean_dec_ref(v_validate_2083_);
lean_dec_ref(v_descr_2082_);
lean_dec(v_name_2081_);
v_a_2121_ = lean_ctor_get(v___x_2097_, 0);
v_isSharedCheck_2128_ = !lean_is_exclusive(v___x_2097_);
if (v_isSharedCheck_2128_ == 0)
{
v___x_2123_ = v___x_2097_;
v_isShared_2124_ = v_isSharedCheck_2128_;
goto v_resetjp_2122_;
}
else
{
lean_inc(v_a_2121_);
lean_dec(v___x_2097_);
v___x_2123_ = lean_box(0);
v_isShared_2124_ = v_isSharedCheck_2128_;
goto v_resetjp_2122_;
}
v_resetjp_2122_:
{
lean_object* v___x_2126_; 
if (v_isShared_2124_ == 0)
{
v___x_2126_ = v___x_2123_;
goto v_reusejp_2125_;
}
else
{
lean_object* v_reuseFailAlloc_2127_; 
v_reuseFailAlloc_2127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2127_, 0, v_a_2121_);
v___x_2126_ = v_reuseFailAlloc_2127_;
goto v_reusejp_2125_;
}
v_reusejp_2125_:
{
return v___x_2126_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___boxed(lean_object* v_name_2129_, lean_object* v_descr_2130_, lean_object* v_validate_2131_, lean_object* v_ref_2132_, lean_object* v_applicationTime_2133_, lean_object* v_asyncMode_2134_, lean_object* v_a_2135_){
_start:
{
uint8_t v_applicationTime_boxed_2136_; lean_object* v_res_2137_; 
v_applicationTime_boxed_2136_ = lean_unbox(v_applicationTime_2133_);
v_res_2137_ = l_Lean_registerTagAttribute(v_name_2129_, v_descr_2130_, v_validate_2131_, v_ref_2132_, v_applicationTime_boxed_2136_, v_asyncMode_2134_);
return v_res_2137_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerTagAttribute_spec__1(lean_object* v_init_2138_, lean_object* v_t_2139_){
_start:
{
lean_object* v___x_2140_; 
v___x_2140_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerTagAttribute_spec__1_spec__1(v_init_2138_, v_t_2139_);
return v___x_2140_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3(lean_object* v_n_2141_, lean_object* v_as_2142_, lean_object* v_lo_2143_, lean_object* v_hi_2144_, lean_object* v_w_2145_, lean_object* v_hlo_2146_, lean_object* v_hhi_2147_){
_start:
{
lean_object* v___x_2148_; 
v___x_2148_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___redArg(v_n_2141_, v_as_2142_, v_lo_2143_, v_hi_2144_);
return v___x_2148_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___boxed(lean_object* v_n_2149_, lean_object* v_as_2150_, lean_object* v_lo_2151_, lean_object* v_hi_2152_, lean_object* v_w_2153_, lean_object* v_hlo_2154_, lean_object* v_hhi_2155_){
_start:
{
lean_object* v_res_2156_; 
v_res_2156_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3(v_n_2149_, v_as_2150_, v_lo_2151_, v_hi_2152_, v_w_2153_, v_hlo_2154_, v_hhi_2155_);
lean_dec(v_hi_2152_);
lean_dec(v_n_2149_);
return v_res_2156_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4(lean_object* v_00_u03b1_2157_, lean_object* v_attrName_2158_, lean_object* v_declName_2159_, lean_object* v_asyncPrefix_x3f_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_){
_start:
{
lean_object* v___x_2164_; 
v___x_2164_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___redArg(v_attrName_2158_, v_declName_2159_, v_asyncPrefix_x3f_2160_, v___y_2161_, v___y_2162_);
return v___x_2164_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___boxed(lean_object* v_00_u03b1_2165_, lean_object* v_attrName_2166_, lean_object* v_declName_2167_, lean_object* v_asyncPrefix_x3f_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_){
_start:
{
lean_object* v_res_2172_; 
v_res_2172_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4(v_00_u03b1_2165_, v_attrName_2166_, v_declName_2167_, v_asyncPrefix_x3f_2168_, v___y_2169_, v___y_2170_);
lean_dec(v___y_2170_);
lean_dec_ref(v___y_2169_);
return v_res_2172_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5(lean_object* v_00_u03b1_2173_, lean_object* v_attrName_2174_, lean_object* v_declName_2175_, lean_object* v___y_2176_, lean_object* v___y_2177_){
_start:
{
lean_object* v___x_2179_; 
v___x_2179_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg(v_attrName_2174_, v_declName_2175_, v___y_2176_, v___y_2177_);
return v___x_2179_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___boxed(lean_object* v_00_u03b1_2180_, lean_object* v_attrName_2181_, lean_object* v_declName_2182_, lean_object* v___y_2183_, lean_object* v___y_2184_, lean_object* v___y_2185_){
_start:
{
lean_object* v_res_2186_; 
v_res_2186_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5(v_00_u03b1_2180_, v_attrName_2181_, v_declName_2182_, v___y_2183_, v___y_2184_);
lean_dec(v___y_2184_);
lean_dec_ref(v___y_2183_);
return v_res_2186_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6(lean_object* v_00_u03b1_2187_, lean_object* v_name_2188_, uint8_t v_kind_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_){
_start:
{
lean_object* v___x_2193_; 
v___x_2193_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg(v_name_2188_, v_kind_2189_, v___y_2190_, v___y_2191_);
return v___x_2193_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___boxed(lean_object* v_00_u03b1_2194_, lean_object* v_name_2195_, lean_object* v_kind_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_){
_start:
{
uint8_t v_kind_boxed_2200_; lean_object* v_res_2201_; 
v_kind_boxed_2200_ = lean_unbox(v_kind_2196_);
v_res_2201_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6(v_00_u03b1_2194_, v_name_2195_, v_kind_boxed_2200_, v___y_2197_, v___y_2198_);
lean_dec(v___y_2198_);
lean_dec_ref(v___y_2197_);
return v_res_2201_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4(lean_object* v_n_2202_, lean_object* v_lo_2203_, lean_object* v_hi_2204_, lean_object* v_hhi_2205_, lean_object* v_pivot_2206_, lean_object* v_as_2207_, lean_object* v_i_2208_, lean_object* v_k_2209_, lean_object* v_ilo_2210_, lean_object* v_ik_2211_, lean_object* v_w_2212_){
_start:
{
lean_object* v___x_2213_; 
v___x_2213_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4___redArg(v_hi_2204_, v_pivot_2206_, v_as_2207_, v_i_2208_, v_k_2209_);
return v___x_2213_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4___boxed(lean_object* v_n_2214_, lean_object* v_lo_2215_, lean_object* v_hi_2216_, lean_object* v_hhi_2217_, lean_object* v_pivot_2218_, lean_object* v_as_2219_, lean_object* v_i_2220_, lean_object* v_k_2221_, lean_object* v_ilo_2222_, lean_object* v_ik_2223_, lean_object* v_w_2224_){
_start:
{
lean_object* v_res_2225_; 
v_res_2225_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4(v_n_2214_, v_lo_2215_, v_hi_2216_, v_hhi_2217_, v_pivot_2218_, v_as_2219_, v_i_2220_, v_k_2221_, v_ilo_2222_, v_ik_2223_, v_w_2224_);
lean_dec(v_pivot_2218_);
lean_dec(v_hi_2216_);
lean_dec(v_lo_2215_);
lean_dec(v_n_2214_);
return v_res_2225_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg___lam__0(lean_object* v_attr_2226_, lean_object* v_decl_2227_, lean_object* v_env_2228_){
_start:
{
lean_object* v_ext_2229_; lean_object* v_toEnvExtension_2230_; lean_object* v_asyncMode_2231_; lean_object* v___x_2232_; 
v_ext_2229_ = lean_ctor_get(v_attr_2226_, 1);
lean_inc_ref(v_ext_2229_);
lean_dec_ref(v_attr_2226_);
v_toEnvExtension_2230_ = lean_ctor_get(v_ext_2229_, 0);
v_asyncMode_2231_ = lean_ctor_get(v_toEnvExtension_2230_, 2);
lean_inc(v_asyncMode_2231_);
lean_inc(v_decl_2227_);
v___x_2232_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_ext_2229_, v_env_2228_, v_decl_2227_, v_asyncMode_2231_, v_decl_2227_);
lean_dec(v_asyncMode_2231_);
return v___x_2232_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg___lam__1(lean_object* v_modifyEnv_2233_, lean_object* v___f_2234_, lean_object* v_____r_2235_){
_start:
{
lean_object* v___x_2236_; 
v___x_2236_ = lean_apply_1(v_modifyEnv_2233_, v___f_2234_);
return v___x_2236_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg___lam__2(lean_object* v_attr_2237_, lean_object* v_env_2238_, lean_object* v_decl_2239_, lean_object* v_inst_2240_, lean_object* v_inst_2241_, lean_object* v_toBind_2242_, lean_object* v___f_2243_, lean_object* v_modifyEnv_2244_, lean_object* v___f_2245_, lean_object* v_____r_2246_){
_start:
{
lean_object* v_ext_2247_; lean_object* v_toEnvExtension_2248_; lean_object* v_attr_2249_; lean_object* v_asyncMode_2250_; uint8_t v___x_2251_; 
v_ext_2247_ = lean_ctor_get(v_attr_2237_, 1);
v_toEnvExtension_2248_ = lean_ctor_get(v_ext_2247_, 0);
lean_inc_ref(v_toEnvExtension_2248_);
v_attr_2249_ = lean_ctor_get(v_attr_2237_, 0);
lean_inc_ref(v_attr_2249_);
lean_dec_ref(v_attr_2237_);
v_asyncMode_2250_ = lean_ctor_get(v_toEnvExtension_2248_, 2);
lean_inc(v_asyncMode_2250_);
lean_dec_ref(v_toEnvExtension_2248_);
lean_inc(v_decl_2239_);
lean_inc_ref(v_env_2238_);
v___x_2251_ = l_Lean_EnvExtension_asyncMayModify___redArg(v_env_2238_, v_decl_2239_, v_asyncMode_2250_);
lean_dec(v_asyncMode_2250_);
if (v___x_2251_ == 0)
{
lean_object* v_toAttributeImplCore_2252_; lean_object* v_name_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; 
lean_dec_ref(v___f_2245_);
lean_dec(v_modifyEnv_2244_);
v_toAttributeImplCore_2252_ = lean_ctor_get(v_attr_2249_, 0);
lean_inc_ref(v_toAttributeImplCore_2252_);
lean_dec_ref(v_attr_2249_);
v_name_2253_ = lean_ctor_get(v_toAttributeImplCore_2252_, 1);
lean_inc(v_name_2253_);
lean_dec_ref(v_toAttributeImplCore_2252_);
v___x_2254_ = l_Lean_Environment_asyncPrefix_x3f(v_env_2238_);
v___x_2255_ = l_Lean_throwAttrNotInAsyncCtx___redArg(v_inst_2240_, v_inst_2241_, v_name_2253_, v_decl_2239_, v___x_2254_);
v___x_2256_ = lean_apply_4(v_toBind_2242_, lean_box(0), lean_box(0), v___x_2255_, v___f_2243_);
return v___x_2256_;
}
else
{
lean_object* v___x_2257_; 
lean_dec_ref(v_attr_2249_);
lean_dec(v___f_2243_);
lean_dec(v_toBind_2242_);
lean_dec_ref(v_inst_2241_);
lean_dec_ref(v_inst_2240_);
lean_dec(v_decl_2239_);
lean_dec_ref(v_env_2238_);
v___x_2257_ = lean_apply_1(v_modifyEnv_2244_, v___f_2245_);
return v___x_2257_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg___lam__3(lean_object* v___f_2258_, lean_object* v_____r_2259_){
_start:
{
lean_object* v___x_2260_; 
v___x_2260_ = lean_apply_1(v___f_2258_, v_____r_2259_);
return v___x_2260_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg___lam__4(lean_object* v_attr_2261_, lean_object* v_decl_2262_, lean_object* v_inst_2263_, lean_object* v_inst_2264_, lean_object* v_toBind_2265_, lean_object* v___f_2266_, lean_object* v_modifyEnv_2267_, lean_object* v___f_2268_, lean_object* v_env_2269_){
_start:
{
lean_object* v___f_2270_; lean_object* v___x_2271_; 
lean_inc_ref(v___f_2268_);
lean_inc(v_modifyEnv_2267_);
lean_inc(v___f_2266_);
lean_inc(v_toBind_2265_);
lean_inc_ref(v_inst_2264_);
lean_inc_ref(v_inst_2263_);
lean_inc(v_decl_2262_);
lean_inc_ref(v_env_2269_);
lean_inc_ref(v_attr_2261_);
v___f_2270_ = lean_alloc_closure((void*)(l_Lean_TagAttribute_setTag___redArg___lam__2), 10, 9);
lean_closure_set(v___f_2270_, 0, v_attr_2261_);
lean_closure_set(v___f_2270_, 1, v_env_2269_);
lean_closure_set(v___f_2270_, 2, v_decl_2262_);
lean_closure_set(v___f_2270_, 3, v_inst_2263_);
lean_closure_set(v___f_2270_, 4, v_inst_2264_);
lean_closure_set(v___f_2270_, 5, v_toBind_2265_);
lean_closure_set(v___f_2270_, 6, v___f_2266_);
lean_closure_set(v___f_2270_, 7, v_modifyEnv_2267_);
lean_closure_set(v___f_2270_, 8, v___f_2268_);
v___x_2271_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2269_, v_decl_2262_);
if (lean_obj_tag(v___x_2271_) == 0)
{
lean_object* v___x_2272_; lean_object* v___x_2273_; 
lean_dec_ref(v___f_2270_);
v___x_2272_ = lean_box(0);
v___x_2273_ = l_Lean_TagAttribute_setTag___redArg___lam__2(v_attr_2261_, v_env_2269_, v_decl_2262_, v_inst_2263_, v_inst_2264_, v_toBind_2265_, v___f_2266_, v_modifyEnv_2267_, v___f_2268_, v___x_2272_);
return v___x_2273_;
}
else
{
lean_object* v_attr_2274_; lean_object* v_toAttributeImplCore_2275_; lean_object* v_name_2276_; lean_object* v___f_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; 
lean_dec_ref_known(v___x_2271_, 1);
lean_dec_ref(v_env_2269_);
lean_dec_ref(v___f_2268_);
lean_dec(v_modifyEnv_2267_);
lean_dec(v___f_2266_);
v_attr_2274_ = lean_ctor_get(v_attr_2261_, 0);
lean_inc_ref(v_attr_2274_);
lean_dec_ref(v_attr_2261_);
v_toAttributeImplCore_2275_ = lean_ctor_get(v_attr_2274_, 0);
lean_inc_ref(v_toAttributeImplCore_2275_);
lean_dec_ref(v_attr_2274_);
v_name_2276_ = lean_ctor_get(v_toAttributeImplCore_2275_, 1);
lean_inc(v_name_2276_);
lean_dec_ref(v_toAttributeImplCore_2275_);
v___f_2277_ = lean_alloc_closure((void*)(l_Lean_TagAttribute_setTag___redArg___lam__3), 2, 1);
lean_closure_set(v___f_2277_, 0, v___f_2270_);
v___x_2278_ = l_Lean_throwAttrDeclInImportedModule___redArg(v_inst_2263_, v_inst_2264_, v_name_2276_, v_decl_2262_);
v___x_2279_ = lean_apply_4(v_toBind_2265_, lean_box(0), lean_box(0), v___x_2278_, v___f_2277_);
return v___x_2279_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg(lean_object* v_inst_2280_, lean_object* v_inst_2281_, lean_object* v_inst_2282_, lean_object* v_attr_2283_, lean_object* v_decl_2284_){
_start:
{
lean_object* v_toBind_2285_; lean_object* v_getEnv_2286_; lean_object* v_modifyEnv_2287_; lean_object* v___f_2288_; lean_object* v___f_2289_; lean_object* v___f_2290_; lean_object* v___x_2291_; 
v_toBind_2285_ = lean_ctor_get(v_inst_2280_, 1);
lean_inc_n(v_toBind_2285_, 2);
v_getEnv_2286_ = lean_ctor_get(v_inst_2282_, 0);
lean_inc(v_getEnv_2286_);
v_modifyEnv_2287_ = lean_ctor_get(v_inst_2282_, 1);
lean_inc_n(v_modifyEnv_2287_, 2);
lean_dec_ref(v_inst_2282_);
lean_inc(v_decl_2284_);
lean_inc_ref(v_attr_2283_);
v___f_2288_ = lean_alloc_closure((void*)(l_Lean_TagAttribute_setTag___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2288_, 0, v_attr_2283_);
lean_closure_set(v___f_2288_, 1, v_decl_2284_);
lean_inc_ref(v___f_2288_);
v___f_2289_ = lean_alloc_closure((void*)(l_Lean_TagAttribute_setTag___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2289_, 0, v_modifyEnv_2287_);
lean_closure_set(v___f_2289_, 1, v___f_2288_);
v___f_2290_ = lean_alloc_closure((void*)(l_Lean_TagAttribute_setTag___redArg___lam__4), 9, 8);
lean_closure_set(v___f_2290_, 0, v_attr_2283_);
lean_closure_set(v___f_2290_, 1, v_decl_2284_);
lean_closure_set(v___f_2290_, 2, v_inst_2280_);
lean_closure_set(v___f_2290_, 3, v_inst_2281_);
lean_closure_set(v___f_2290_, 4, v_toBind_2285_);
lean_closure_set(v___f_2290_, 5, v___f_2289_);
lean_closure_set(v___f_2290_, 6, v_modifyEnv_2287_);
lean_closure_set(v___f_2290_, 7, v___f_2288_);
v___x_2291_ = lean_apply_4(v_toBind_2285_, lean_box(0), lean_box(0), v_getEnv_2286_, v___f_2290_);
return v___x_2291_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag(lean_object* v_m_2292_, lean_object* v_inst_2293_, lean_object* v_inst_2294_, lean_object* v_inst_2295_, lean_object* v_attr_2296_, lean_object* v_decl_2297_){
_start:
{
lean_object* v___x_2298_; 
v___x_2298_ = l_Lean_TagAttribute_setTag___redArg(v_inst_2293_, v_inst_2294_, v_inst_2295_, v_attr_2296_, v_decl_2297_);
return v___x_2298_;
}
}
LEAN_EXPORT uint8_t l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___redArg(lean_object* v_as_2299_, lean_object* v_k_2300_, lean_object* v_x_2301_, lean_object* v_x_2302_){
_start:
{
lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v_m_2305_; lean_object* v_a_2306_; uint8_t v___x_2307_; 
v___x_2303_ = lean_nat_add(v_x_2301_, v_x_2302_);
v___x_2304_ = lean_unsigned_to_nat(1u);
v_m_2305_ = lean_nat_shiftr(v___x_2303_, v___x_2304_);
lean_dec(v___x_2303_);
v_a_2306_ = lean_array_fget_borrowed(v_as_2299_, v_m_2305_);
v___x_2307_ = l_Lean_Name_quickLt(v_a_2306_, v_k_2300_);
if (v___x_2307_ == 0)
{
uint8_t v___x_2308_; 
lean_dec(v_x_2302_);
v___x_2308_ = l_Lean_Name_quickLt(v_k_2300_, v_a_2306_);
if (v___x_2308_ == 0)
{
uint8_t v___x_2309_; 
lean_dec(v_m_2305_);
lean_dec(v_x_2301_);
v___x_2309_ = 1;
return v___x_2309_;
}
else
{
lean_object* v___x_2310_; uint8_t v___x_2311_; 
v___x_2310_ = lean_unsigned_to_nat(0u);
v___x_2311_ = lean_nat_dec_eq(v_m_2305_, v___x_2310_);
if (v___x_2311_ == 0)
{
lean_object* v___x_2312_; uint8_t v___x_2313_; 
v___x_2312_ = lean_nat_sub(v_m_2305_, v___x_2304_);
lean_dec(v_m_2305_);
v___x_2313_ = lean_nat_dec_lt(v___x_2312_, v_x_2301_);
if (v___x_2313_ == 0)
{
v_x_2302_ = v___x_2312_;
goto _start;
}
else
{
lean_dec(v___x_2312_);
lean_dec(v_x_2301_);
return v___x_2307_;
}
}
else
{
lean_dec(v_m_2305_);
lean_dec(v_x_2301_);
return v___x_2307_;
}
}
}
else
{
lean_object* v___x_2315_; uint8_t v___x_2316_; 
lean_dec(v_x_2301_);
v___x_2315_ = lean_nat_add(v_m_2305_, v___x_2304_);
lean_dec(v_m_2305_);
v___x_2316_ = lean_nat_dec_le(v___x_2315_, v_x_2302_);
if (v___x_2316_ == 0)
{
lean_dec(v___x_2315_);
lean_dec(v_x_2302_);
return v___x_2316_;
}
else
{
v_x_2301_ = v___x_2315_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___redArg___boxed(lean_object* v_as_2318_, lean_object* v_k_2319_, lean_object* v_x_2320_, lean_object* v_x_2321_){
_start:
{
uint8_t v_res_2322_; lean_object* v_r_2323_; 
v_res_2322_ = l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___redArg(v_as_2318_, v_k_2319_, v_x_2320_, v_x_2321_);
lean_dec(v_k_2319_);
lean_dec_ref(v_as_2318_);
v_r_2323_ = lean_box(v_res_2322_);
return v_r_2323_;
}
}
LEAN_EXPORT uint8_t l_Lean_TagAttribute_hasTag(lean_object* v_attr_2324_, lean_object* v_env_2325_, lean_object* v_decl_2326_){
_start:
{
lean_object* v___x_2327_; lean_object* v___x_2328_; 
v___x_2327_ = lean_box(1);
v___x_2328_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2325_, v_decl_2326_);
if (lean_obj_tag(v___x_2328_) == 0)
{
lean_object* v_ext_2329_; lean_object* v_toEnvExtension_2330_; lean_object* v_asyncMode_2331_; lean_object* v___x_2332_; uint8_t v___x_2333_; 
v_ext_2329_ = lean_ctor_get(v_attr_2324_, 1);
v_toEnvExtension_2330_ = lean_ctor_get(v_ext_2329_, 0);
v_asyncMode_2331_ = lean_ctor_get(v_toEnvExtension_2330_, 2);
lean_inc(v_decl_2326_);
v___x_2332_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2327_, v_ext_2329_, v_env_2325_, v_asyncMode_2331_, v_decl_2326_);
v___x_2333_ = l_Lean_NameSet_contains(v___x_2332_, v_decl_2326_);
lean_dec(v_decl_2326_);
lean_dec(v___x_2332_);
return v___x_2333_;
}
else
{
lean_object* v_val_2334_; lean_object* v_ext_2335_; uint8_t v___x_2336_; lean_object* v___x_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; uint8_t v___x_2340_; 
v_val_2334_ = lean_ctor_get(v___x_2328_, 0);
lean_inc(v_val_2334_);
lean_dec_ref_known(v___x_2328_, 1);
v_ext_2335_ = lean_ctor_get(v_attr_2324_, 1);
v___x_2336_ = 0;
v___x_2337_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_2327_, v_ext_2335_, v_env_2325_, v_val_2334_, v___x_2336_);
lean_dec(v_val_2334_);
lean_dec_ref(v_env_2325_);
v___x_2338_ = lean_unsigned_to_nat(0u);
v___x_2339_ = lean_array_get_size(v___x_2337_);
v___x_2340_ = lean_nat_dec_lt(v___x_2338_, v___x_2339_);
if (v___x_2340_ == 0)
{
lean_dec_ref(v___x_2337_);
lean_dec(v_decl_2326_);
return v___x_2340_;
}
else
{
lean_object* v___x_2341_; lean_object* v___x_2342_; uint8_t v___x_2343_; 
v___x_2341_ = lean_unsigned_to_nat(1u);
v___x_2342_ = lean_nat_sub(v___x_2339_, v___x_2341_);
v___x_2343_ = lean_nat_dec_le(v___x_2338_, v___x_2342_);
if (v___x_2343_ == 0)
{
lean_dec(v___x_2342_);
lean_dec_ref(v___x_2337_);
lean_dec(v_decl_2326_);
return v___x_2343_;
}
else
{
uint8_t v___x_2344_; 
v___x_2344_ = l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___redArg(v___x_2337_, v_decl_2326_, v___x_2338_, v___x_2342_);
lean_dec(v_decl_2326_);
lean_dec_ref(v___x_2337_);
return v___x_2344_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_hasTag___boxed(lean_object* v_attr_2345_, lean_object* v_env_2346_, lean_object* v_decl_2347_){
_start:
{
uint8_t v_res_2348_; lean_object* v_r_2349_; 
v_res_2348_ = l_Lean_TagAttribute_hasTag(v_attr_2345_, v_env_2346_, v_decl_2347_);
lean_dec_ref(v_attr_2345_);
v_r_2349_ = lean_box(v_res_2348_);
return v_r_2349_;
}
}
LEAN_EXPORT uint8_t l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0(lean_object* v_as_2350_, lean_object* v_k_2351_, lean_object* v_x_2352_, lean_object* v_x_2353_, lean_object* v_x_2354_){
_start:
{
uint8_t v___x_2355_; 
v___x_2355_ = l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___redArg(v_as_2350_, v_k_2351_, v_x_2352_, v_x_2353_);
return v___x_2355_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___boxed(lean_object* v_as_2356_, lean_object* v_k_2357_, lean_object* v_x_2358_, lean_object* v_x_2359_, lean_object* v_x_2360_){
_start:
{
uint8_t v_res_2361_; lean_object* v_r_2362_; 
v_res_2361_ = l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0(v_as_2356_, v_k_2357_, v_x_2358_, v_x_2359_, v_x_2360_);
lean_dec(v_k_2357_);
lean_dec_ref(v_as_2356_);
v_r_2362_ = lean_box(v_res_2361_);
return v_r_2362_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__0(lean_object* v_x_2363_, lean_object* v___y_2364_){
_start:
{
lean_object* v___x_2366_; lean_object* v___x_2367_; 
v___x_2366_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___lam__0___closed__1));
v___x_2367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2367_, 0, v___x_2366_);
return v___x_2367_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__0___boxed(lean_object* v_x_2368_, lean_object* v___y_2369_, lean_object* v___y_2370_){
_start:
{
lean_object* v_res_2371_; 
v_res_2371_ = l_Lean_instInhabitedParametricAttribute_default___lam__0(v_x_2368_, v___y_2369_);
lean_dec_ref(v___y_2369_);
lean_dec_ref(v_x_2368_);
return v_res_2371_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__1(lean_object* v_s_2372_, lean_object* v_x_2373_){
_start:
{
lean_inc_ref(v_s_2372_);
return v_s_2372_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__1___boxed(lean_object* v_s_2374_, lean_object* v_x_2375_){
_start:
{
lean_object* v_res_2376_; 
v_res_2376_ = l_Lean_instInhabitedParametricAttribute_default___lam__1(v_s_2374_, v_x_2375_);
lean_dec_ref(v_x_2375_);
lean_dec_ref(v_s_2374_);
return v_res_2376_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__2(lean_object* v_x_2381_, lean_object* v_x_2382_){
_start:
{
lean_object* v___x_2383_; 
v___x_2383_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___lam__2___closed__1));
return v___x_2383_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__2___boxed(lean_object* v_x_2384_, lean_object* v_x_2385_){
_start:
{
lean_object* v_res_2386_; 
v_res_2386_ = l_Lean_instInhabitedParametricAttribute_default___lam__2(v_x_2384_, v_x_2385_);
lean_dec_ref(v_x_2385_);
lean_dec_ref(v_x_2384_);
return v_res_2386_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__3(lean_object* v_x_2387_){
_start:
{
lean_object* v___x_2388_; 
v___x_2388_ = lean_box(0);
return v___x_2388_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__3___boxed(lean_object* v_x_2389_){
_start:
{
lean_object* v_res_2390_; 
v_res_2390_ = l_Lean_instInhabitedParametricAttribute_default___lam__3(v_x_2389_);
lean_dec_ref(v_x_2389_);
return v_res_2390_;
}
}
static lean_object* _init_l_Lean_instInhabitedParametricAttribute_default___closed__4(void){
_start:
{
lean_object* v___x_2395_; 
v___x_2395_ = l_Lean_instInhabitedEnvExtension_default(lean_box(0));
return v___x_2395_;
}
}
static lean_object* _init_l_Lean_instInhabitedParametricAttribute_default___closed__5(void){
_start:
{
lean_object* v___f_2396_; lean_object* v___f_2397_; lean_object* v___f_2398_; lean_object* v___f_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; 
v___f_2396_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___closed__3));
v___f_2397_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___closed__2));
v___f_2398_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___closed__1));
v___f_2399_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___closed__0));
v___x_2400_ = lean_box(0);
v___x_2401_ = lean_obj_once(&l_Lean_instInhabitedParametricAttribute_default___closed__4, &l_Lean_instInhabitedParametricAttribute_default___closed__4_once, _init_l_Lean_instInhabitedParametricAttribute_default___closed__4);
v___x_2402_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2402_, 0, v___x_2401_);
lean_ctor_set(v___x_2402_, 1, v___x_2400_);
lean_ctor_set(v___x_2402_, 2, v___f_2399_);
lean_ctor_set(v___x_2402_, 3, v___f_2398_);
lean_ctor_set(v___x_2402_, 4, v___f_2397_);
lean_ctor_set(v___x_2402_, 5, v___f_2396_);
return v___x_2402_;
}
}
static lean_object* _init_l_Lean_instInhabitedParametricAttribute_default___closed__6(void){
_start:
{
uint8_t v___x_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; 
v___x_2403_ = 0;
v___x_2404_ = lean_obj_once(&l_Lean_instInhabitedParametricAttribute_default___closed__5, &l_Lean_instInhabitedParametricAttribute_default___closed__5_once, _init_l_Lean_instInhabitedParametricAttribute_default___closed__5);
v___x_2405_ = ((lean_object*)(l_Lean_instInhabitedAttributeImpl_default));
v___x_2406_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2406_, 0, v___x_2405_);
lean_ctor_set(v___x_2406_, 1, v___x_2404_);
lean_ctor_set_uint8(v___x_2406_, sizeof(void*)*2, v___x_2403_);
return v___x_2406_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default(lean_object* v_00_u03b1_2407_){
_start:
{
lean_object* v___x_2408_; 
v___x_2408_ = lean_obj_once(&l_Lean_instInhabitedParametricAttribute_default___closed__6, &l_Lean_instInhabitedParametricAttribute_default___closed__6_once, _init_l_Lean_instInhabitedParametricAttribute_default___closed__6);
return v___x_2408_;
}
}
static lean_object* _init_l_Lean_instInhabitedParametricAttribute___closed__0(void){
_start:
{
lean_object* v___x_2409_; 
v___x_2409_ = l_Lean_instInhabitedParametricAttribute_default(lean_box(0));
return v___x_2409_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute(lean_object* v_a_2410_){
_start:
{
lean_object* v___x_2411_; 
v___x_2411_ = lean_obj_once(&l_Lean_instInhabitedParametricAttribute___closed__0, &l_Lean_instInhabitedParametricAttribute___closed__0_once, _init_l_Lean_instInhabitedParametricAttribute___closed__0);
return v___x_2411_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__0(lean_object* v_x_2412_, lean_object* v_p_2413_){
_start:
{
lean_object* v_fst_2414_; lean_object* v_snd_2415_; lean_object* v___x_2417_; uint8_t v_isShared_2418_; uint8_t v_isSharedCheck_2432_; 
v_fst_2414_ = lean_ctor_get(v_x_2412_, 0);
v_snd_2415_ = lean_ctor_get(v_x_2412_, 1);
v_isSharedCheck_2432_ = !lean_is_exclusive(v_x_2412_);
if (v_isSharedCheck_2432_ == 0)
{
v___x_2417_ = v_x_2412_;
v_isShared_2418_ = v_isSharedCheck_2432_;
goto v_resetjp_2416_;
}
else
{
lean_inc(v_snd_2415_);
lean_inc(v_fst_2414_);
lean_dec(v_x_2412_);
v___x_2417_ = lean_box(0);
v_isShared_2418_ = v_isSharedCheck_2432_;
goto v_resetjp_2416_;
}
v_resetjp_2416_:
{
lean_object* v_fst_2419_; lean_object* v_snd_2420_; lean_object* v___x_2422_; uint8_t v_isShared_2423_; uint8_t v_isSharedCheck_2431_; 
v_fst_2419_ = lean_ctor_get(v_p_2413_, 0);
v_snd_2420_ = lean_ctor_get(v_p_2413_, 1);
v_isSharedCheck_2431_ = !lean_is_exclusive(v_p_2413_);
if (v_isSharedCheck_2431_ == 0)
{
v___x_2422_ = v_p_2413_;
v_isShared_2423_ = v_isSharedCheck_2431_;
goto v_resetjp_2421_;
}
else
{
lean_inc(v_snd_2420_);
lean_inc(v_fst_2419_);
lean_dec(v_p_2413_);
v___x_2422_ = lean_box(0);
v_isShared_2423_ = v_isSharedCheck_2431_;
goto v_resetjp_2421_;
}
v_resetjp_2421_:
{
lean_object* v___x_2425_; 
lean_inc(v_fst_2419_);
if (v_isShared_2418_ == 0)
{
lean_ctor_set_tag(v___x_2417_, 1);
lean_ctor_set(v___x_2417_, 1, v_fst_2414_);
lean_ctor_set(v___x_2417_, 0, v_fst_2419_);
v___x_2425_ = v___x_2417_;
goto v_reusejp_2424_;
}
else
{
lean_object* v_reuseFailAlloc_2430_; 
v_reuseFailAlloc_2430_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2430_, 0, v_fst_2419_);
lean_ctor_set(v_reuseFailAlloc_2430_, 1, v_fst_2414_);
v___x_2425_ = v_reuseFailAlloc_2430_;
goto v_reusejp_2424_;
}
v_reusejp_2424_:
{
lean_object* v___x_2426_; lean_object* v___x_2428_; 
v___x_2426_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_2419_, v_snd_2420_, v_snd_2415_);
if (v_isShared_2423_ == 0)
{
lean_ctor_set(v___x_2422_, 1, v___x_2426_);
lean_ctor_set(v___x_2422_, 0, v___x_2425_);
v___x_2428_ = v___x_2422_;
goto v_reusejp_2427_;
}
else
{
lean_object* v_reuseFailAlloc_2429_; 
v_reuseFailAlloc_2429_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2429_, 0, v___x_2425_);
lean_ctor_set(v_reuseFailAlloc_2429_, 1, v___x_2426_);
v___x_2428_ = v_reuseFailAlloc_2429_;
goto v_reusejp_2427_;
}
v_reusejp_2427_:
{
return v___x_2428_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg(lean_object* v_init_2433_, lean_object* v_x_2434_){
_start:
{
if (lean_obj_tag(v_x_2434_) == 0)
{
lean_object* v_k_2435_; lean_object* v_v_2436_; lean_object* v_l_2437_; lean_object* v_r_2438_; lean_object* v___x_2439_; lean_object* v___x_2440_; lean_object* v___x_2441_; 
v_k_2435_ = lean_ctor_get(v_x_2434_, 1);
v_v_2436_ = lean_ctor_get(v_x_2434_, 2);
v_l_2437_ = lean_ctor_get(v_x_2434_, 3);
v_r_2438_ = lean_ctor_get(v_x_2434_, 4);
v___x_2439_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg(v_init_2433_, v_l_2437_);
lean_inc(v_v_2436_);
lean_inc(v_k_2435_);
v___x_2440_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2440_, 0, v_k_2435_);
lean_ctor_set(v___x_2440_, 1, v_v_2436_);
v___x_2441_ = lean_array_push(v___x_2439_, v___x_2440_);
v_init_2433_ = v___x_2441_;
v_x_2434_ = v_r_2438_;
goto _start;
}
else
{
return v_init_2433_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg___boxed(lean_object* v_init_2443_, lean_object* v_x_2444_){
_start:
{
lean_object* v_res_2445_; 
v_res_2445_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg(v_init_2443_, v_x_2444_);
lean_dec(v_x_2444_);
return v_res_2445_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5___redArg(lean_object* v_snd_2446_, lean_object* v_as_2447_, size_t v_i_2448_, size_t v_stop_2449_, lean_object* v_b_2450_){
_start:
{
lean_object* v___y_2452_; uint8_t v___x_2456_; 
v___x_2456_ = lean_usize_dec_eq(v_i_2448_, v_stop_2449_);
if (v___x_2456_ == 0)
{
lean_object* v___x_2457_; lean_object* v___x_2458_; 
v___x_2457_ = lean_array_uget_borrowed(v_as_2447_, v_i_2448_);
v___x_2458_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_snd_2446_, v___x_2457_);
if (lean_obj_tag(v___x_2458_) == 0)
{
v___y_2452_ = v_b_2450_;
goto v___jp_2451_;
}
else
{
lean_object* v_val_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; 
v_val_2459_ = lean_ctor_get(v___x_2458_, 0);
lean_inc(v_val_2459_);
lean_dec_ref_known(v___x_2458_, 1);
lean_inc(v___x_2457_);
v___x_2460_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2460_, 0, v___x_2457_);
lean_ctor_set(v___x_2460_, 1, v_val_2459_);
v___x_2461_ = lean_array_push(v_b_2450_, v___x_2460_);
v___y_2452_ = v___x_2461_;
goto v___jp_2451_;
}
}
else
{
return v_b_2450_;
}
v___jp_2451_:
{
size_t v___x_2453_; size_t v___x_2454_; 
v___x_2453_ = ((size_t)1ULL);
v___x_2454_ = lean_usize_add(v_i_2448_, v___x_2453_);
v_i_2448_ = v___x_2454_;
v_b_2450_ = v___y_2452_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5___redArg___boxed(lean_object* v_snd_2462_, lean_object* v_as_2463_, lean_object* v_i_2464_, lean_object* v_stop_2465_, lean_object* v_b_2466_){
_start:
{
size_t v_i_boxed_2467_; size_t v_stop_boxed_2468_; lean_object* v_res_2469_; 
v_i_boxed_2467_ = lean_unbox_usize(v_i_2464_);
lean_dec(v_i_2464_);
v_stop_boxed_2468_ = lean_unbox_usize(v_stop_2465_);
lean_dec(v_stop_2465_);
v_res_2469_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5___redArg(v_snd_2462_, v_as_2463_, v_i_boxed_2467_, v_stop_boxed_2468_, v_b_2466_);
lean_dec_ref(v_as_2463_);
lean_dec(v_snd_2462_);
return v_res_2469_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3___redArg(lean_object* v_snd_2470_, lean_object* v_as_2471_, lean_object* v_start_2472_, lean_object* v_stop_2473_){
_start:
{
lean_object* v___x_2474_; uint8_t v___x_2475_; 
v___x_2474_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___lam__2___closed__0));
v___x_2475_ = lean_nat_dec_lt(v_start_2472_, v_stop_2473_);
if (v___x_2475_ == 0)
{
return v___x_2474_;
}
else
{
lean_object* v___x_2476_; uint8_t v___x_2477_; 
v___x_2476_ = lean_array_get_size(v_as_2471_);
v___x_2477_ = lean_nat_dec_le(v_stop_2473_, v___x_2476_);
if (v___x_2477_ == 0)
{
uint8_t v___x_2478_; 
v___x_2478_ = lean_nat_dec_lt(v_start_2472_, v___x_2476_);
if (v___x_2478_ == 0)
{
return v___x_2474_;
}
else
{
size_t v___x_2479_; size_t v___x_2480_; lean_object* v___x_2481_; 
v___x_2479_ = lean_usize_of_nat(v_start_2472_);
v___x_2480_ = lean_usize_of_nat(v___x_2476_);
v___x_2481_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5___redArg(v_snd_2470_, v_as_2471_, v___x_2479_, v___x_2480_, v___x_2474_);
return v___x_2481_;
}
}
else
{
size_t v___x_2482_; size_t v___x_2483_; lean_object* v___x_2484_; 
v___x_2482_ = lean_usize_of_nat(v_start_2472_);
v___x_2483_ = lean_usize_of_nat(v_stop_2473_);
v___x_2484_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5___redArg(v_snd_2470_, v_as_2471_, v___x_2482_, v___x_2483_, v___x_2474_);
return v___x_2484_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3___redArg___boxed(lean_object* v_snd_2485_, lean_object* v_as_2486_, lean_object* v_start_2487_, lean_object* v_stop_2488_){
_start:
{
lean_object* v_res_2489_; 
v_res_2489_ = l_Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3___redArg(v_snd_2485_, v_as_2486_, v_start_2487_, v_stop_2488_);
lean_dec(v_stop_2488_);
lean_dec(v_start_2487_);
lean_dec_ref(v_as_2486_);
lean_dec(v_snd_2485_);
return v_res_2489_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2_spec__3___redArg(lean_object* v_hi_2490_, lean_object* v_pivot_2491_, lean_object* v_as_2492_, lean_object* v_i_2493_, lean_object* v_k_2494_){
_start:
{
uint8_t v___x_2495_; 
v___x_2495_ = lean_nat_dec_lt(v_k_2494_, v_hi_2490_);
if (v___x_2495_ == 0)
{
lean_object* v___x_2496_; lean_object* v___x_2497_; 
lean_dec(v_k_2494_);
v___x_2496_ = lean_array_fswap(v_as_2492_, v_i_2493_, v_hi_2490_);
v___x_2497_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2497_, 0, v_i_2493_);
lean_ctor_set(v___x_2497_, 1, v___x_2496_);
return v___x_2497_;
}
else
{
lean_object* v___x_2498_; lean_object* v_fst_2499_; lean_object* v_fst_2500_; uint8_t v___x_2501_; 
v___x_2498_ = lean_array_fget_borrowed(v_as_2492_, v_k_2494_);
v_fst_2499_ = lean_ctor_get(v___x_2498_, 0);
v_fst_2500_ = lean_ctor_get(v_pivot_2491_, 0);
v___x_2501_ = l_Lean_Name_quickLt(v_fst_2499_, v_fst_2500_);
if (v___x_2501_ == 0)
{
lean_object* v___x_2502_; lean_object* v___x_2503_; 
v___x_2502_ = lean_unsigned_to_nat(1u);
v___x_2503_ = lean_nat_add(v_k_2494_, v___x_2502_);
lean_dec(v_k_2494_);
v_k_2494_ = v___x_2503_;
goto _start;
}
else
{
lean_object* v___x_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; 
v___x_2505_ = lean_array_fswap(v_as_2492_, v_i_2493_, v_k_2494_);
v___x_2506_ = lean_unsigned_to_nat(1u);
v___x_2507_ = lean_nat_add(v_i_2493_, v___x_2506_);
lean_dec(v_i_2493_);
v___x_2508_ = lean_nat_add(v_k_2494_, v___x_2506_);
lean_dec(v_k_2494_);
v_as_2492_ = v___x_2505_;
v_i_2493_ = v___x_2507_;
v_k_2494_ = v___x_2508_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2_spec__3___redArg___boxed(lean_object* v_hi_2510_, lean_object* v_pivot_2511_, lean_object* v_as_2512_, lean_object* v_i_2513_, lean_object* v_k_2514_){
_start:
{
lean_object* v_res_2515_; 
v_res_2515_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2_spec__3___redArg(v_hi_2510_, v_pivot_2511_, v_as_2512_, v_i_2513_, v_k_2514_);
lean_dec_ref(v_pivot_2511_);
lean_dec(v_hi_2510_);
return v_res_2515_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg___lam__0(lean_object* v_a_2516_, lean_object* v_b_2517_){
_start:
{
lean_object* v_fst_2518_; lean_object* v_fst_2519_; uint8_t v___x_2520_; 
v_fst_2518_ = lean_ctor_get(v_a_2516_, 0);
v_fst_2519_ = lean_ctor_get(v_b_2517_, 0);
v___x_2520_ = l_Lean_Name_quickLt(v_fst_2518_, v_fst_2519_);
return v___x_2520_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg___lam__0___boxed(lean_object* v_a_2521_, lean_object* v_b_2522_){
_start:
{
uint8_t v_res_2523_; lean_object* v_r_2524_; 
v_res_2523_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg___lam__0(v_a_2521_, v_b_2522_);
lean_dec_ref(v_b_2522_);
lean_dec_ref(v_a_2521_);
v_r_2524_ = lean_box(v_res_2523_);
return v_r_2524_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg(lean_object* v_n_2525_, lean_object* v_as_2526_, lean_object* v_lo_2527_, lean_object* v_hi_2528_){
_start:
{
lean_object* v___y_2530_; uint8_t v___x_2540_; 
v___x_2540_ = lean_nat_dec_lt(v_lo_2527_, v_hi_2528_);
if (v___x_2540_ == 0)
{
lean_dec(v_lo_2527_);
return v_as_2526_;
}
else
{
lean_object* v___x_2541_; lean_object* v___x_2542_; lean_object* v_mid_2543_; lean_object* v___y_2545_; lean_object* v___y_2551_; lean_object* v___x_2556_; lean_object* v___x_2557_; uint8_t v___x_2558_; 
v___x_2541_ = lean_nat_add(v_lo_2527_, v_hi_2528_);
v___x_2542_ = lean_unsigned_to_nat(1u);
v_mid_2543_ = lean_nat_shiftr(v___x_2541_, v___x_2542_);
lean_dec(v___x_2541_);
v___x_2556_ = lean_array_fget_borrowed(v_as_2526_, v_mid_2543_);
v___x_2557_ = lean_array_fget_borrowed(v_as_2526_, v_lo_2527_);
v___x_2558_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg___lam__0(v___x_2556_, v___x_2557_);
if (v___x_2558_ == 0)
{
v___y_2551_ = v_as_2526_;
goto v___jp_2550_;
}
else
{
lean_object* v___x_2559_; 
v___x_2559_ = lean_array_fswap(v_as_2526_, v_lo_2527_, v_mid_2543_);
v___y_2551_ = v___x_2559_;
goto v___jp_2550_;
}
v___jp_2544_:
{
lean_object* v___x_2546_; lean_object* v___x_2547_; uint8_t v___x_2548_; 
v___x_2546_ = lean_array_fget_borrowed(v___y_2545_, v_mid_2543_);
v___x_2547_ = lean_array_fget_borrowed(v___y_2545_, v_hi_2528_);
v___x_2548_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg___lam__0(v___x_2546_, v___x_2547_);
if (v___x_2548_ == 0)
{
lean_dec(v_mid_2543_);
v___y_2530_ = v___y_2545_;
goto v___jp_2529_;
}
else
{
lean_object* v___x_2549_; 
v___x_2549_ = lean_array_fswap(v___y_2545_, v_mid_2543_, v_hi_2528_);
lean_dec(v_mid_2543_);
v___y_2530_ = v___x_2549_;
goto v___jp_2529_;
}
}
v___jp_2550_:
{
lean_object* v___x_2552_; lean_object* v___x_2553_; uint8_t v___x_2554_; 
v___x_2552_ = lean_array_fget_borrowed(v___y_2551_, v_hi_2528_);
v___x_2553_ = lean_array_fget_borrowed(v___y_2551_, v_lo_2527_);
v___x_2554_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg___lam__0(v___x_2552_, v___x_2553_);
if (v___x_2554_ == 0)
{
v___y_2545_ = v___y_2551_;
goto v___jp_2544_;
}
else
{
lean_object* v___x_2555_; 
v___x_2555_ = lean_array_fswap(v___y_2551_, v_lo_2527_, v_hi_2528_);
v___y_2545_ = v___x_2555_;
goto v___jp_2544_;
}
}
}
v___jp_2529_:
{
lean_object* v_pivot_2531_; lean_object* v___x_2532_; lean_object* v_fst_2533_; lean_object* v_snd_2534_; uint8_t v___x_2535_; 
v_pivot_2531_ = lean_array_fget(v___y_2530_, v_hi_2528_);
lean_inc_n(v_lo_2527_, 2);
v___x_2532_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2_spec__3___redArg(v_hi_2528_, v_pivot_2531_, v___y_2530_, v_lo_2527_, v_lo_2527_);
lean_dec(v_pivot_2531_);
v_fst_2533_ = lean_ctor_get(v___x_2532_, 0);
lean_inc(v_fst_2533_);
v_snd_2534_ = lean_ctor_get(v___x_2532_, 1);
lean_inc(v_snd_2534_);
lean_dec_ref(v___x_2532_);
v___x_2535_ = lean_nat_dec_le(v_hi_2528_, v_fst_2533_);
if (v___x_2535_ == 0)
{
lean_object* v___x_2536_; lean_object* v___x_2537_; lean_object* v___x_2538_; 
v___x_2536_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg(v_n_2525_, v_snd_2534_, v_lo_2527_, v_fst_2533_);
v___x_2537_ = lean_unsigned_to_nat(1u);
v___x_2538_ = lean_nat_add(v_fst_2533_, v___x_2537_);
lean_dec(v_fst_2533_);
v_as_2526_ = v___x_2536_;
v_lo_2527_ = v___x_2538_;
goto _start;
}
else
{
lean_dec(v_fst_2533_);
lean_dec(v_lo_2527_);
return v_snd_2534_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg___boxed(lean_object* v_n_2560_, lean_object* v_as_2561_, lean_object* v_lo_2562_, lean_object* v_hi_2563_){
_start:
{
lean_object* v_res_2564_; 
v_res_2564_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg(v_n_2560_, v_as_2561_, v_lo_2562_, v_hi_2563_);
lean_dec(v_hi_2563_);
lean_dec(v_n_2560_);
return v_res_2564_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0___redArg(lean_object* v_filterExport_2565_, lean_object* v_env_2566_, lean_object* v_as_2567_, size_t v_i_2568_, size_t v_stop_2569_, lean_object* v_b_2570_){
_start:
{
lean_object* v___y_2572_; uint8_t v___x_2576_; 
v___x_2576_ = lean_usize_dec_eq(v_i_2568_, v_stop_2569_);
if (v___x_2576_ == 0)
{
lean_object* v___x_2577_; lean_object* v_fst_2578_; lean_object* v_snd_2579_; lean_object* v___x_2580_; uint8_t v___x_2581_; 
v___x_2577_ = lean_array_uget_borrowed(v_as_2567_, v_i_2568_);
v_fst_2578_ = lean_ctor_get(v___x_2577_, 0);
v_snd_2579_ = lean_ctor_get(v___x_2577_, 1);
lean_inc_ref(v_filterExport_2565_);
lean_inc(v_snd_2579_);
lean_inc(v_fst_2578_);
lean_inc_ref(v_env_2566_);
v___x_2580_ = lean_apply_3(v_filterExport_2565_, v_env_2566_, v_fst_2578_, v_snd_2579_);
v___x_2581_ = lean_unbox(v___x_2580_);
if (v___x_2581_ == 0)
{
v___y_2572_ = v_b_2570_;
goto v___jp_2571_;
}
else
{
lean_object* v___x_2582_; 
lean_inc(v___x_2577_);
v___x_2582_ = lean_array_push(v_b_2570_, v___x_2577_);
v___y_2572_ = v___x_2582_;
goto v___jp_2571_;
}
}
else
{
lean_dec_ref(v_env_2566_);
lean_dec_ref(v_filterExport_2565_);
return v_b_2570_;
}
v___jp_2571_:
{
size_t v___x_2573_; size_t v___x_2574_; 
v___x_2573_ = ((size_t)1ULL);
v___x_2574_ = lean_usize_add(v_i_2568_, v___x_2573_);
v_i_2568_ = v___x_2574_;
v_b_2570_ = v___y_2572_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0___redArg___boxed(lean_object* v_filterExport_2583_, lean_object* v_env_2584_, lean_object* v_as_2585_, lean_object* v_i_2586_, lean_object* v_stop_2587_, lean_object* v_b_2588_){
_start:
{
size_t v_i_boxed_2589_; size_t v_stop_boxed_2590_; lean_object* v_res_2591_; 
v_i_boxed_2589_ = lean_unbox_usize(v_i_2586_);
lean_dec(v_i_2586_);
v_stop_boxed_2590_ = lean_unbox_usize(v_stop_2587_);
lean_dec(v_stop_2587_);
v_res_2591_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0___redArg(v_filterExport_2583_, v_env_2584_, v_as_2585_, v_i_boxed_2589_, v_stop_boxed_2590_, v_b_2588_);
lean_dec_ref(v_as_2585_);
return v_res_2591_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__1(lean_object* v_filterExport_2592_, uint8_t v_preserveOrder_2593_, lean_object* v_env_2594_, lean_object* v_x_2595_){
_start:
{
lean_object* v___y_2597_; 
if (v_preserveOrder_2593_ == 0)
{
lean_object* v_snd_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; lean_object* v_r_2616_; lean_object* v___x_2617_; lean_object* v___y_2619_; lean_object* v___y_2620_; uint8_t v___x_2622_; 
v_snd_2613_ = lean_ctor_get(v_x_2595_, 1);
lean_inc(v_snd_2613_);
lean_dec_ref(v_x_2595_);
v___x_2614_ = lean_unsigned_to_nat(0u);
v___x_2615_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___lam__2___closed__0));
v_r_2616_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg(v___x_2615_, v_snd_2613_);
lean_dec(v_snd_2613_);
v___x_2617_ = lean_array_get_size(v_r_2616_);
v___x_2622_ = lean_nat_dec_eq(v___x_2617_, v___x_2614_);
if (v___x_2622_ == 0)
{
lean_object* v___x_2623_; lean_object* v___x_2624_; lean_object* v___y_2626_; uint8_t v___x_2628_; 
v___x_2623_ = lean_unsigned_to_nat(1u);
v___x_2624_ = lean_nat_sub(v___x_2617_, v___x_2623_);
v___x_2628_ = lean_nat_dec_le(v___x_2614_, v___x_2624_);
if (v___x_2628_ == 0)
{
lean_inc(v___x_2624_);
v___y_2626_ = v___x_2624_;
goto v___jp_2625_;
}
else
{
v___y_2626_ = v___x_2614_;
goto v___jp_2625_;
}
v___jp_2625_:
{
uint8_t v___x_2627_; 
v___x_2627_ = lean_nat_dec_le(v___y_2626_, v___x_2624_);
if (v___x_2627_ == 0)
{
lean_dec(v___x_2624_);
lean_inc(v___y_2626_);
v___y_2619_ = v___y_2626_;
v___y_2620_ = v___y_2626_;
goto v___jp_2618_;
}
else
{
v___y_2619_ = v___y_2626_;
v___y_2620_ = v___x_2624_;
goto v___jp_2618_;
}
}
}
else
{
v___y_2597_ = v_r_2616_;
goto v___jp_2596_;
}
v___jp_2618_:
{
lean_object* v___x_2621_; 
v___x_2621_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg(v___x_2617_, v_r_2616_, v___y_2619_, v___y_2620_);
lean_dec(v___y_2620_);
v___y_2597_ = v___x_2621_;
goto v___jp_2596_;
}
}
else
{
lean_object* v_fst_2629_; lean_object* v_snd_2630_; lean_object* v___x_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; 
v_fst_2629_ = lean_ctor_get(v_x_2595_, 0);
lean_inc(v_fst_2629_);
v_snd_2630_ = lean_ctor_get(v_x_2595_, 1);
lean_inc(v_snd_2630_);
lean_dec_ref(v_x_2595_);
v___x_2631_ = lean_array_mk(v_fst_2629_);
v___x_2632_ = l_Array_reverse___redArg(v___x_2631_);
v___x_2633_ = lean_unsigned_to_nat(0u);
v___x_2634_ = lean_array_get_size(v___x_2632_);
v___x_2635_ = l_Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3___redArg(v_snd_2630_, v___x_2632_, v___x_2633_, v___x_2634_);
lean_dec_ref(v___x_2632_);
lean_dec(v_snd_2630_);
v___y_2597_ = v___x_2635_;
goto v___jp_2596_;
}
v___jp_2596_:
{
lean_object* v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; uint8_t v___x_2601_; 
v___x_2598_ = lean_unsigned_to_nat(0u);
v___x_2599_ = lean_array_get_size(v___y_2597_);
v___x_2600_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___lam__2___closed__0));
v___x_2601_ = lean_nat_dec_lt(v___x_2598_, v___x_2599_);
if (v___x_2601_ == 0)
{
lean_object* v___x_2602_; 
lean_dec_ref(v_env_2594_);
lean_dec_ref(v_filterExport_2592_);
v___x_2602_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2602_, 0, v___x_2600_);
lean_ctor_set(v___x_2602_, 1, v___x_2600_);
lean_ctor_set(v___x_2602_, 2, v___y_2597_);
return v___x_2602_;
}
else
{
uint8_t v___x_2603_; 
v___x_2603_ = lean_nat_dec_le(v___x_2599_, v___x_2599_);
if (v___x_2603_ == 0)
{
if (v___x_2601_ == 0)
{
lean_object* v___x_2604_; 
lean_dec_ref(v_env_2594_);
lean_dec_ref(v_filterExport_2592_);
v___x_2604_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2604_, 0, v___x_2600_);
lean_ctor_set(v___x_2604_, 1, v___x_2600_);
lean_ctor_set(v___x_2604_, 2, v___y_2597_);
return v___x_2604_;
}
else
{
size_t v___x_2605_; size_t v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; 
v___x_2605_ = ((size_t)0ULL);
v___x_2606_ = lean_usize_of_nat(v___x_2599_);
v___x_2607_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0___redArg(v_filterExport_2592_, v_env_2594_, v___y_2597_, v___x_2605_, v___x_2606_, v___x_2600_);
lean_inc_ref(v___x_2607_);
v___x_2608_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2608_, 0, v___x_2607_);
lean_ctor_set(v___x_2608_, 1, v___x_2607_);
lean_ctor_set(v___x_2608_, 2, v___y_2597_);
return v___x_2608_;
}
}
else
{
size_t v___x_2609_; size_t v___x_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; 
v___x_2609_ = ((size_t)0ULL);
v___x_2610_ = lean_usize_of_nat(v___x_2599_);
v___x_2611_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0___redArg(v_filterExport_2592_, v_env_2594_, v___y_2597_, v___x_2609_, v___x_2610_, v___x_2600_);
lean_inc_ref(v___x_2611_);
v___x_2612_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2612_, 0, v___x_2611_);
lean_ctor_set(v___x_2612_, 1, v___x_2611_);
lean_ctor_set(v___x_2612_, 2, v___y_2597_);
return v___x_2612_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__1___boxed(lean_object* v_filterExport_2636_, lean_object* v_preserveOrder_2637_, lean_object* v_env_2638_, lean_object* v_x_2639_){
_start:
{
uint8_t v_preserveOrder_boxed_2640_; lean_object* v_res_2641_; 
v_preserveOrder_boxed_2640_ = lean_unbox(v_preserveOrder_2637_);
v_res_2641_ = l_Lean_registerParametricAttributeExt___redArg___lam__1(v_filterExport_2636_, v_preserveOrder_boxed_2640_, v_env_2638_, v_x_2639_);
return v_res_2641_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__2(lean_object* v_x_2651_){
_start:
{
lean_object* v_snd_2652_; lean_object* v___x_2654_; uint8_t v_isShared_2655_; uint8_t v_isSharedCheck_2666_; 
v_snd_2652_ = lean_ctor_get(v_x_2651_, 1);
v_isSharedCheck_2666_ = !lean_is_exclusive(v_x_2651_);
if (v_isSharedCheck_2666_ == 0)
{
lean_object* v_unused_2667_; 
v_unused_2667_ = lean_ctor_get(v_x_2651_, 0);
lean_dec(v_unused_2667_);
v___x_2654_ = v_x_2651_;
v_isShared_2655_ = v_isSharedCheck_2666_;
goto v_resetjp_2653_;
}
else
{
lean_inc(v_snd_2652_);
lean_dec(v_x_2651_);
v___x_2654_ = lean_box(0);
v_isShared_2655_ = v_isSharedCheck_2666_;
goto v_resetjp_2653_;
}
v_resetjp_2653_:
{
lean_object* v___x_2656_; lean_object* v___y_2658_; 
v___x_2656_ = ((lean_object*)(l_Lean_registerParametricAttributeExt___redArg___lam__2___closed__3));
if (lean_obj_tag(v_snd_2652_) == 0)
{
lean_object* v_size_2664_; 
v_size_2664_ = lean_ctor_get(v_snd_2652_, 0);
lean_inc(v_size_2664_);
lean_dec_ref_known(v_snd_2652_, 5);
v___y_2658_ = v_size_2664_;
goto v___jp_2657_;
}
else
{
lean_object* v___x_2665_; 
v___x_2665_ = lean_unsigned_to_nat(0u);
v___y_2658_ = v___x_2665_;
goto v___jp_2657_;
}
v___jp_2657_:
{
lean_object* v___x_2659_; lean_object* v___x_2660_; lean_object* v___x_2662_; 
v___x_2659_ = l_Nat_reprFast(v___y_2658_);
v___x_2660_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2660_, 0, v___x_2659_);
if (v_isShared_2655_ == 0)
{
lean_ctor_set_tag(v___x_2654_, 5);
lean_ctor_set(v___x_2654_, 1, v___x_2660_);
lean_ctor_set(v___x_2654_, 0, v___x_2656_);
v___x_2662_ = v___x_2654_;
goto v_reusejp_2661_;
}
else
{
lean_object* v_reuseFailAlloc_2663_; 
v_reuseFailAlloc_2663_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2663_, 0, v___x_2656_);
lean_ctor_set(v_reuseFailAlloc_2663_, 1, v___x_2660_);
v___x_2662_ = v_reuseFailAlloc_2663_;
goto v_reusejp_2661_;
}
v_reusejp_2661_:
{
return v___x_2662_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__3(lean_object* v_x_2668_){
_start:
{
lean_object* v___x_2669_; 
v___x_2669_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___lam__2___closed__0));
return v___x_2669_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__3___boxed(lean_object* v_x_2670_){
_start:
{
lean_object* v_res_2671_; 
v_res_2671_ = l_Lean_registerParametricAttributeExt___redArg___lam__3(v_x_2670_);
lean_dec_ref(v_x_2670_);
return v_res_2671_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__4(lean_object* v___x_2672_){
_start:
{
lean_object* v___x_2674_; 
v___x_2674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2674_, 0, v___x_2672_);
return v___x_2674_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__4___boxed(lean_object* v___x_2675_, lean_object* v___y_2676_){
_start:
{
lean_object* v_res_2677_; 
v_res_2677_ = l_Lean_registerParametricAttributeExt___redArg___lam__4(v___x_2675_);
return v_res_2677_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__5(lean_object* v___x_2678_, lean_object* v_x_2679_, lean_object* v___y_2680_){
_start:
{
lean_object* v___x_2682_; 
v___x_2682_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2682_, 0, v___x_2678_);
return v___x_2682_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__5___boxed(lean_object* v___x_2683_, lean_object* v_x_2684_, lean_object* v___y_2685_, lean_object* v___y_2686_){
_start:
{
lean_object* v_res_2687_; 
v_res_2687_ = l_Lean_registerParametricAttributeExt___redArg___lam__5(v___x_2683_, v_x_2684_, v___y_2685_);
lean_dec_ref(v___y_2685_);
lean_dec_ref(v_x_2684_);
return v_res_2687_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg(lean_object* v_ref_2698_, uint8_t v_preserveOrder_2699_, lean_object* v_filterExport_2700_){
_start:
{
lean_object* v___f_2702_; lean_object* v___x_2703_; lean_object* v___f_2704_; lean_object* v___f_2705_; lean_object* v___f_2706_; lean_object* v___f_2707_; lean_object* v___f_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; lean_object* v___x_2711_; lean_object* v___x_2712_; lean_object* v___x_2713_; 
v___f_2702_ = ((lean_object*)(l_Lean_registerParametricAttributeExt___redArg___closed__0));
v___x_2703_ = lean_box(v_preserveOrder_2699_);
v___f_2704_ = lean_alloc_closure((void*)(l_Lean_registerParametricAttributeExt___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_2704_, 0, v_filterExport_2700_);
lean_closure_set(v___f_2704_, 1, v___x_2703_);
v___f_2705_ = ((lean_object*)(l_Lean_registerParametricAttributeExt___redArg___closed__1));
v___f_2706_ = ((lean_object*)(l_Lean_registerParametricAttributeExt___redArg___closed__2));
v___f_2707_ = ((lean_object*)(l_Lean_registerParametricAttributeExt___redArg___closed__4));
v___f_2708_ = ((lean_object*)(l_Lean_registerParametricAttributeExt___redArg___closed__5));
v___x_2709_ = lean_box(2);
v___x_2710_ = lean_box(0);
v___x_2711_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_2711_, 0, v_ref_2698_);
lean_ctor_set(v___x_2711_, 1, v___f_2707_);
lean_ctor_set(v___x_2711_, 2, v___f_2708_);
lean_ctor_set(v___x_2711_, 3, v___f_2702_);
lean_ctor_set(v___x_2711_, 4, v___f_2704_);
lean_ctor_set(v___x_2711_, 5, v___f_2705_);
lean_ctor_set(v___x_2711_, 6, v___x_2709_);
lean_ctor_set(v___x_2711_, 7, v___x_2710_);
v___x_2712_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2712_, 0, v___x_2711_);
lean_ctor_set(v___x_2712_, 1, v___f_2706_);
v___x_2713_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_2712_);
return v___x_2713_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___boxed(lean_object* v_ref_2714_, lean_object* v_preserveOrder_2715_, lean_object* v_filterExport_2716_, lean_object* v_a_2717_){
_start:
{
uint8_t v_preserveOrder_boxed_2718_; lean_object* v_res_2719_; 
v_preserveOrder_boxed_2718_ = lean_unbox(v_preserveOrder_2715_);
v_res_2719_ = l_Lean_registerParametricAttributeExt___redArg(v_ref_2714_, v_preserveOrder_boxed_2718_, v_filterExport_2716_);
return v_res_2719_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt(lean_object* v_00_u03b1_2720_, lean_object* v_ref_2721_, uint8_t v_preserveOrder_2722_, lean_object* v_filterExport_2723_){
_start:
{
lean_object* v___x_2725_; 
v___x_2725_ = l_Lean_registerParametricAttributeExt___redArg(v_ref_2721_, v_preserveOrder_2722_, v_filterExport_2723_);
return v___x_2725_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___boxed(lean_object* v_00_u03b1_2726_, lean_object* v_ref_2727_, lean_object* v_preserveOrder_2728_, lean_object* v_filterExport_2729_, lean_object* v_a_2730_){
_start:
{
uint8_t v_preserveOrder_boxed_2731_; lean_object* v_res_2732_; 
v_preserveOrder_boxed_2731_ = lean_unbox(v_preserveOrder_2728_);
v_res_2732_ = l_Lean_registerParametricAttributeExt(v_00_u03b1_2726_, v_ref_2727_, v_preserveOrder_boxed_2731_, v_filterExport_2729_);
return v_res_2732_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0(lean_object* v_00_u03b1_2733_, lean_object* v_filterExport_2734_, lean_object* v_env_2735_, lean_object* v_as_2736_, size_t v_i_2737_, size_t v_stop_2738_, lean_object* v_b_2739_){
_start:
{
lean_object* v___x_2740_; 
v___x_2740_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0___redArg(v_filterExport_2734_, v_env_2735_, v_as_2736_, v_i_2737_, v_stop_2738_, v_b_2739_);
return v___x_2740_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0___boxed(lean_object* v_00_u03b1_2741_, lean_object* v_filterExport_2742_, lean_object* v_env_2743_, lean_object* v_as_2744_, lean_object* v_i_2745_, lean_object* v_stop_2746_, lean_object* v_b_2747_){
_start:
{
size_t v_i_boxed_2748_; size_t v_stop_boxed_2749_; lean_object* v_res_2750_; 
v_i_boxed_2748_ = lean_unbox_usize(v_i_2745_);
lean_dec(v_i_2745_);
v_stop_boxed_2749_ = lean_unbox_usize(v_stop_2746_);
lean_dec(v_stop_2746_);
v_res_2750_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0(v_00_u03b1_2741_, v_filterExport_2742_, v_env_2743_, v_as_2744_, v_i_boxed_2748_, v_stop_boxed_2749_, v_b_2747_);
lean_dec_ref(v_as_2744_);
return v_res_2750_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1___redArg(lean_object* v_init_2751_, lean_object* v_t_2752_){
_start:
{
lean_object* v___x_2753_; 
v___x_2753_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg(v_init_2751_, v_t_2752_);
return v___x_2753_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1___redArg___boxed(lean_object* v_init_2754_, lean_object* v_t_2755_){
_start:
{
lean_object* v_res_2756_; 
v_res_2756_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1___redArg(v_init_2754_, v_t_2755_);
lean_dec(v_t_2755_);
return v_res_2756_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1(lean_object* v_00_u03b1_2757_, lean_object* v_init_2758_, lean_object* v_t_2759_){
_start:
{
lean_object* v___x_2760_; 
v___x_2760_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg(v_init_2758_, v_t_2759_);
return v___x_2760_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1___boxed(lean_object* v_00_u03b1_2761_, lean_object* v_init_2762_, lean_object* v_t_2763_){
_start:
{
lean_object* v_res_2764_; 
v_res_2764_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1(v_00_u03b1_2761_, v_init_2762_, v_t_2763_);
lean_dec(v_t_2763_);
return v_res_2764_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2(lean_object* v_00_u03b1_2765_, lean_object* v_n_2766_, lean_object* v_as_2767_, lean_object* v_lo_2768_, lean_object* v_hi_2769_, lean_object* v_w_2770_, lean_object* v_hlo_2771_, lean_object* v_hhi_2772_){
_start:
{
lean_object* v___x_2773_; 
v___x_2773_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg(v_n_2766_, v_as_2767_, v_lo_2768_, v_hi_2769_);
return v___x_2773_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___boxed(lean_object* v_00_u03b1_2774_, lean_object* v_n_2775_, lean_object* v_as_2776_, lean_object* v_lo_2777_, lean_object* v_hi_2778_, lean_object* v_w_2779_, lean_object* v_hlo_2780_, lean_object* v_hhi_2781_){
_start:
{
lean_object* v_res_2782_; 
v_res_2782_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2(v_00_u03b1_2774_, v_n_2775_, v_as_2776_, v_lo_2777_, v_hi_2778_, v_w_2779_, v_hlo_2780_, v_hhi_2781_);
lean_dec(v_hi_2778_);
lean_dec(v_n_2775_);
return v_res_2782_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3(lean_object* v_00_u03b1_2783_, lean_object* v_snd_2784_, lean_object* v_as_2785_, lean_object* v_start_2786_, lean_object* v_stop_2787_){
_start:
{
lean_object* v___x_2788_; 
v___x_2788_ = l_Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3___redArg(v_snd_2784_, v_as_2785_, v_start_2786_, v_stop_2787_);
return v___x_2788_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3___boxed(lean_object* v_00_u03b1_2789_, lean_object* v_snd_2790_, lean_object* v_as_2791_, lean_object* v_start_2792_, lean_object* v_stop_2793_){
_start:
{
lean_object* v_res_2794_; 
v_res_2794_ = l_Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3(v_00_u03b1_2789_, v_snd_2790_, v_as_2791_, v_start_2792_, v_stop_2793_);
lean_dec(v_stop_2793_);
lean_dec(v_start_2792_);
lean_dec_ref(v_as_2791_);
lean_dec(v_snd_2790_);
return v_res_2794_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1(lean_object* v_00_u03b1_2795_, lean_object* v_init_2796_, lean_object* v_x_2797_){
_start:
{
lean_object* v___x_2798_; 
v___x_2798_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg(v_init_2796_, v_x_2797_);
return v___x_2798_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___boxed(lean_object* v_00_u03b1_2799_, lean_object* v_init_2800_, lean_object* v_x_2801_){
_start:
{
lean_object* v_res_2802_; 
v_res_2802_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1(v_00_u03b1_2799_, v_init_2800_, v_x_2801_);
lean_dec(v_x_2801_);
return v_res_2802_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2_spec__3(lean_object* v_00_u03b1_2803_, lean_object* v_n_2804_, lean_object* v_lo_2805_, lean_object* v_hi_2806_, lean_object* v_hhi_2807_, lean_object* v_pivot_2808_, lean_object* v_as_2809_, lean_object* v_i_2810_, lean_object* v_k_2811_, lean_object* v_ilo_2812_, lean_object* v_ik_2813_, lean_object* v_w_2814_){
_start:
{
lean_object* v___x_2815_; 
v___x_2815_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2_spec__3___redArg(v_hi_2806_, v_pivot_2808_, v_as_2809_, v_i_2810_, v_k_2811_);
return v___x_2815_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2_spec__3___boxed(lean_object* v_00_u03b1_2816_, lean_object* v_n_2817_, lean_object* v_lo_2818_, lean_object* v_hi_2819_, lean_object* v_hhi_2820_, lean_object* v_pivot_2821_, lean_object* v_as_2822_, lean_object* v_i_2823_, lean_object* v_k_2824_, lean_object* v_ilo_2825_, lean_object* v_ik_2826_, lean_object* v_w_2827_){
_start:
{
lean_object* v_res_2828_; 
v_res_2828_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2_spec__3(v_00_u03b1_2816_, v_n_2817_, v_lo_2818_, v_hi_2819_, v_hhi_2820_, v_pivot_2821_, v_as_2822_, v_i_2823_, v_k_2824_, v_ilo_2825_, v_ik_2826_, v_w_2827_);
lean_dec_ref(v_pivot_2821_);
lean_dec(v_hi_2819_);
lean_dec(v_lo_2818_);
lean_dec(v_n_2817_);
return v_res_2828_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5(lean_object* v_00_u03b1_2829_, lean_object* v_snd_2830_, lean_object* v_as_2831_, size_t v_i_2832_, size_t v_stop_2833_, lean_object* v_b_2834_){
_start:
{
lean_object* v___x_2835_; 
v___x_2835_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5___redArg(v_snd_2830_, v_as_2831_, v_i_2832_, v_stop_2833_, v_b_2834_);
return v___x_2835_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5___boxed(lean_object* v_00_u03b1_2836_, lean_object* v_snd_2837_, lean_object* v_as_2838_, lean_object* v_i_2839_, lean_object* v_stop_2840_, lean_object* v_b_2841_){
_start:
{
size_t v_i_boxed_2842_; size_t v_stop_boxed_2843_; lean_object* v_res_2844_; 
v_i_boxed_2842_ = lean_unbox_usize(v_i_2839_);
lean_dec(v_i_2839_);
v_stop_boxed_2843_ = lean_unbox_usize(v_stop_2840_);
lean_dec(v_stop_2840_);
v_res_2844_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5(v_00_u03b1_2836_, v_snd_2837_, v_as_2838_, v_i_boxed_2842_, v_stop_boxed_2843_, v_b_2841_);
lean_dec_ref(v_as_2838_);
lean_dec(v_snd_2837_);
return v_res_2844_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_registerParametricAttributeForExt_spec__0___redArg(lean_object* v_env_2845_, lean_object* v___y_2846_){
_start:
{
lean_object* v___x_2848_; lean_object* v_nextMacroScope_2849_; lean_object* v_ngen_2850_; lean_object* v_auxDeclNGen_2851_; lean_object* v_traceState_2852_; lean_object* v_messages_2853_; lean_object* v_infoState_2854_; lean_object* v_snapshotTasks_2855_; lean_object* v___x_2857_; uint8_t v_isShared_2858_; uint8_t v_isSharedCheck_2866_; 
v___x_2848_ = lean_st_ref_take(v___y_2846_);
v_nextMacroScope_2849_ = lean_ctor_get(v___x_2848_, 1);
v_ngen_2850_ = lean_ctor_get(v___x_2848_, 2);
v_auxDeclNGen_2851_ = lean_ctor_get(v___x_2848_, 3);
v_traceState_2852_ = lean_ctor_get(v___x_2848_, 4);
v_messages_2853_ = lean_ctor_get(v___x_2848_, 6);
v_infoState_2854_ = lean_ctor_get(v___x_2848_, 7);
v_snapshotTasks_2855_ = lean_ctor_get(v___x_2848_, 8);
v_isSharedCheck_2866_ = !lean_is_exclusive(v___x_2848_);
if (v_isSharedCheck_2866_ == 0)
{
lean_object* v_unused_2867_; lean_object* v_unused_2868_; 
v_unused_2867_ = lean_ctor_get(v___x_2848_, 5);
lean_dec(v_unused_2867_);
v_unused_2868_ = lean_ctor_get(v___x_2848_, 0);
lean_dec(v_unused_2868_);
v___x_2857_ = v___x_2848_;
v_isShared_2858_ = v_isSharedCheck_2866_;
goto v_resetjp_2856_;
}
else
{
lean_inc(v_snapshotTasks_2855_);
lean_inc(v_infoState_2854_);
lean_inc(v_messages_2853_);
lean_inc(v_traceState_2852_);
lean_inc(v_auxDeclNGen_2851_);
lean_inc(v_ngen_2850_);
lean_inc(v_nextMacroScope_2849_);
lean_dec(v___x_2848_);
v___x_2857_ = lean_box(0);
v_isShared_2858_ = v_isSharedCheck_2866_;
goto v_resetjp_2856_;
}
v_resetjp_2856_:
{
lean_object* v___x_2859_; lean_object* v___x_2861_; 
v___x_2859_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2);
if (v_isShared_2858_ == 0)
{
lean_ctor_set(v___x_2857_, 5, v___x_2859_);
lean_ctor_set(v___x_2857_, 0, v_env_2845_);
v___x_2861_ = v___x_2857_;
goto v_reusejp_2860_;
}
else
{
lean_object* v_reuseFailAlloc_2865_; 
v_reuseFailAlloc_2865_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2865_, 0, v_env_2845_);
lean_ctor_set(v_reuseFailAlloc_2865_, 1, v_nextMacroScope_2849_);
lean_ctor_set(v_reuseFailAlloc_2865_, 2, v_ngen_2850_);
lean_ctor_set(v_reuseFailAlloc_2865_, 3, v_auxDeclNGen_2851_);
lean_ctor_set(v_reuseFailAlloc_2865_, 4, v_traceState_2852_);
lean_ctor_set(v_reuseFailAlloc_2865_, 5, v___x_2859_);
lean_ctor_set(v_reuseFailAlloc_2865_, 6, v_messages_2853_);
lean_ctor_set(v_reuseFailAlloc_2865_, 7, v_infoState_2854_);
lean_ctor_set(v_reuseFailAlloc_2865_, 8, v_snapshotTasks_2855_);
v___x_2861_ = v_reuseFailAlloc_2865_;
goto v_reusejp_2860_;
}
v_reusejp_2860_:
{
lean_object* v___x_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; 
v___x_2862_ = lean_st_ref_set(v___y_2846_, v___x_2861_);
v___x_2863_ = lean_box(0);
v___x_2864_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2864_, 0, v___x_2863_);
return v___x_2864_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_registerParametricAttributeForExt_spec__0___redArg___boxed(lean_object* v_env_2869_, lean_object* v___y_2870_, lean_object* v___y_2871_){
_start:
{
lean_object* v_res_2872_; 
v_res_2872_ = l_Lean_setEnv___at___00Lean_registerParametricAttributeForExt_spec__0___redArg(v_env_2869_, v___y_2870_);
lean_dec(v___y_2870_);
return v_res_2872_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_registerParametricAttributeForExt_spec__0(lean_object* v_env_2873_, lean_object* v___y_2874_, lean_object* v___y_2875_){
_start:
{
lean_object* v___x_2877_; 
v___x_2877_ = l_Lean_setEnv___at___00Lean_registerParametricAttributeForExt_spec__0___redArg(v_env_2873_, v___y_2875_);
return v___x_2877_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_registerParametricAttributeForExt_spec__0___boxed(lean_object* v_env_2878_, lean_object* v___y_2879_, lean_object* v___y_2880_, lean_object* v___y_2881_){
_start:
{
lean_object* v_res_2882_; 
v_res_2882_ = l_Lean_setEnv___at___00Lean_registerParametricAttributeForExt_spec__0(v_env_2878_, v___y_2879_, v___y_2880_);
lean_dec(v___y_2880_);
lean_dec_ref(v___y_2879_);
return v_res_2882_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___redArg___lam__0(lean_object* v_getParam_2883_, lean_object* v_ext_2884_, lean_object* v_afterSet_2885_, lean_object* v_toAttributeImplCore_2886_, lean_object* v_decl_2887_, lean_object* v_stx_2888_, uint8_t v_kind_2889_, lean_object* v___y_2890_, lean_object* v___y_2891_){
_start:
{
lean_object* v___y_2894_; lean_object* v___y_2895_; lean_object* v___y_2896_; lean_object* v___y_2897_; uint8_t v___y_2898_; lean_object* v___y_2901_; lean_object* v___y_2902_; lean_object* v___y_2903_; uint8_t v___x_2947_; uint8_t v___x_2948_; 
v___x_2947_ = 0;
v___x_2948_ = l_Lean_instBEqAttributeKind_beq(v_kind_2889_, v___x_2947_);
if (v___x_2948_ == 0)
{
lean_object* v_name_2949_; lean_object* v___x_2950_; 
lean_dec(v_stx_2888_);
lean_dec(v_decl_2887_);
lean_dec_ref(v_afterSet_2885_);
lean_dec_ref(v_ext_2884_);
lean_dec_ref(v_getParam_2883_);
v_name_2949_ = lean_ctor_get(v_toAttributeImplCore_2886_, 1);
lean_inc(v_name_2949_);
lean_dec_ref(v_toAttributeImplCore_2886_);
v___x_2950_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg(v_name_2949_, v_kind_2889_, v___y_2890_, v___y_2891_);
return v___x_2950_;
}
else
{
goto v___jp_2941_;
}
v___jp_2893_:
{
if (v___y_2898_ == 0)
{
lean_object* v___x_2899_; 
lean_dec_ref(v___y_2894_);
v___x_2899_ = l_Lean_setEnv___at___00Lean_registerParametricAttributeForExt_spec__0___redArg(v___y_2897_, v___y_2895_);
return v___x_2899_;
}
else
{
lean_dec_ref(v___y_2897_);
return v___y_2894_;
}
}
v___jp_2900_:
{
lean_object* v___x_2904_; 
lean_inc(v___y_2903_);
lean_inc_ref(v___y_2902_);
lean_inc(v_decl_2887_);
v___x_2904_ = lean_apply_5(v_getParam_2883_, v_decl_2887_, v_stx_2888_, v___y_2902_, v___y_2903_, lean_box(0));
if (lean_obj_tag(v___x_2904_) == 0)
{
lean_object* v_a_2905_; lean_object* v___x_2906_; lean_object* v_toEnvExtension_2907_; lean_object* v_env_2908_; lean_object* v_nextMacroScope_2909_; lean_object* v_ngen_2910_; lean_object* v_auxDeclNGen_2911_; lean_object* v_traceState_2912_; lean_object* v_messages_2913_; lean_object* v_infoState_2914_; lean_object* v_snapshotTasks_2915_; lean_object* v___x_2917_; uint8_t v_isShared_2918_; uint8_t v_isSharedCheck_2931_; 
v_a_2905_ = lean_ctor_get(v___x_2904_, 0);
lean_inc(v_a_2905_);
lean_dec_ref_known(v___x_2904_, 1);
v___x_2906_ = lean_st_ref_take(v___y_2903_);
v_toEnvExtension_2907_ = lean_ctor_get(v_ext_2884_, 0);
v_env_2908_ = lean_ctor_get(v___x_2906_, 0);
v_nextMacroScope_2909_ = lean_ctor_get(v___x_2906_, 1);
v_ngen_2910_ = lean_ctor_get(v___x_2906_, 2);
v_auxDeclNGen_2911_ = lean_ctor_get(v___x_2906_, 3);
v_traceState_2912_ = lean_ctor_get(v___x_2906_, 4);
v_messages_2913_ = lean_ctor_get(v___x_2906_, 6);
v_infoState_2914_ = lean_ctor_get(v___x_2906_, 7);
v_snapshotTasks_2915_ = lean_ctor_get(v___x_2906_, 8);
v_isSharedCheck_2931_ = !lean_is_exclusive(v___x_2906_);
if (v_isSharedCheck_2931_ == 0)
{
lean_object* v_unused_2932_; 
v_unused_2932_ = lean_ctor_get(v___x_2906_, 5);
lean_dec(v_unused_2932_);
v___x_2917_ = v___x_2906_;
v_isShared_2918_ = v_isSharedCheck_2931_;
goto v_resetjp_2916_;
}
else
{
lean_inc(v_snapshotTasks_2915_);
lean_inc(v_infoState_2914_);
lean_inc(v_messages_2913_);
lean_inc(v_traceState_2912_);
lean_inc(v_auxDeclNGen_2911_);
lean_inc(v_ngen_2910_);
lean_inc(v_nextMacroScope_2909_);
lean_inc(v_env_2908_);
lean_dec(v___x_2906_);
v___x_2917_ = lean_box(0);
v_isShared_2918_ = v_isSharedCheck_2931_;
goto v_resetjp_2916_;
}
v_resetjp_2916_:
{
lean_object* v_asyncMode_2919_; lean_object* v___x_2920_; lean_object* v___x_2921_; lean_object* v___x_2922_; lean_object* v___x_2924_; 
v_asyncMode_2919_ = lean_ctor_get(v_toEnvExtension_2907_, 2);
lean_inc(v_asyncMode_2919_);
lean_inc(v_a_2905_);
lean_inc_n(v_decl_2887_, 2);
v___x_2920_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2920_, 0, v_decl_2887_);
lean_ctor_set(v___x_2920_, 1, v_a_2905_);
v___x_2921_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_ext_2884_, v_env_2908_, v___x_2920_, v_asyncMode_2919_, v_decl_2887_);
lean_dec(v_asyncMode_2919_);
v___x_2922_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2);
if (v_isShared_2918_ == 0)
{
lean_ctor_set(v___x_2917_, 5, v___x_2922_);
lean_ctor_set(v___x_2917_, 0, v___x_2921_);
v___x_2924_ = v___x_2917_;
goto v_reusejp_2923_;
}
else
{
lean_object* v_reuseFailAlloc_2930_; 
v_reuseFailAlloc_2930_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2930_, 0, v___x_2921_);
lean_ctor_set(v_reuseFailAlloc_2930_, 1, v_nextMacroScope_2909_);
lean_ctor_set(v_reuseFailAlloc_2930_, 2, v_ngen_2910_);
lean_ctor_set(v_reuseFailAlloc_2930_, 3, v_auxDeclNGen_2911_);
lean_ctor_set(v_reuseFailAlloc_2930_, 4, v_traceState_2912_);
lean_ctor_set(v_reuseFailAlloc_2930_, 5, v___x_2922_);
lean_ctor_set(v_reuseFailAlloc_2930_, 6, v_messages_2913_);
lean_ctor_set(v_reuseFailAlloc_2930_, 7, v_infoState_2914_);
lean_ctor_set(v_reuseFailAlloc_2930_, 8, v_snapshotTasks_2915_);
v___x_2924_ = v_reuseFailAlloc_2930_;
goto v_reusejp_2923_;
}
v_reusejp_2923_:
{
lean_object* v___x_2925_; lean_object* v___x_2926_; 
v___x_2925_ = lean_st_ref_set(v___y_2903_, v___x_2924_);
lean_inc(v___y_2903_);
lean_inc_ref(v___y_2902_);
v___x_2926_ = lean_apply_5(v_afterSet_2885_, v_decl_2887_, v_a_2905_, v___y_2902_, v___y_2903_, lean_box(0));
if (lean_obj_tag(v___x_2926_) == 0)
{
lean_dec_ref(v___y_2901_);
return v___x_2926_;
}
else
{
lean_object* v_a_2927_; uint8_t v___x_2928_; 
v_a_2927_ = lean_ctor_get(v___x_2926_, 0);
lean_inc(v_a_2927_);
v___x_2928_ = l_Lean_Exception_isInterrupt(v_a_2927_);
if (v___x_2928_ == 0)
{
uint8_t v___x_2929_; 
v___x_2929_ = l_Lean_Exception_isRuntime(v_a_2927_);
v___y_2894_ = v___x_2926_;
v___y_2895_ = v___y_2903_;
v___y_2896_ = v___y_2902_;
v___y_2897_ = v___y_2901_;
v___y_2898_ = v___x_2929_;
goto v___jp_2893_;
}
else
{
lean_dec(v_a_2927_);
v___y_2894_ = v___x_2926_;
v___y_2895_ = v___y_2903_;
v___y_2896_ = v___y_2902_;
v___y_2897_ = v___y_2901_;
v___y_2898_ = v___x_2928_;
goto v___jp_2893_;
}
}
}
}
}
else
{
lean_object* v_a_2933_; lean_object* v___x_2935_; uint8_t v_isShared_2936_; uint8_t v_isSharedCheck_2940_; 
lean_dec_ref(v___y_2901_);
lean_dec(v_decl_2887_);
lean_dec_ref(v_afterSet_2885_);
lean_dec_ref(v_ext_2884_);
v_a_2933_ = lean_ctor_get(v___x_2904_, 0);
v_isSharedCheck_2940_ = !lean_is_exclusive(v___x_2904_);
if (v_isSharedCheck_2940_ == 0)
{
v___x_2935_ = v___x_2904_;
v_isShared_2936_ = v_isSharedCheck_2940_;
goto v_resetjp_2934_;
}
else
{
lean_inc(v_a_2933_);
lean_dec(v___x_2904_);
v___x_2935_ = lean_box(0);
v_isShared_2936_ = v_isSharedCheck_2940_;
goto v_resetjp_2934_;
}
v_resetjp_2934_:
{
lean_object* v___x_2938_; 
if (v_isShared_2936_ == 0)
{
v___x_2938_ = v___x_2935_;
goto v_reusejp_2937_;
}
else
{
lean_object* v_reuseFailAlloc_2939_; 
v_reuseFailAlloc_2939_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2939_, 0, v_a_2933_);
v___x_2938_ = v_reuseFailAlloc_2939_;
goto v_reusejp_2937_;
}
v_reusejp_2937_:
{
return v___x_2938_;
}
}
}
}
v___jp_2941_:
{
lean_object* v___x_2942_; lean_object* v_env_2943_; lean_object* v___x_2944_; 
v___x_2942_ = lean_st_ref_get(v___y_2891_);
v_env_2943_ = lean_ctor_get(v___x_2942_, 0);
lean_inc_ref(v_env_2943_);
lean_dec(v___x_2942_);
v___x_2944_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2943_, v_decl_2887_);
if (lean_obj_tag(v___x_2944_) == 0)
{
lean_dec_ref(v_toAttributeImplCore_2886_);
v___y_2901_ = v_env_2943_;
v___y_2902_ = v___y_2890_;
v___y_2903_ = v___y_2891_;
goto v___jp_2900_;
}
else
{
lean_object* v_name_2945_; lean_object* v___x_2946_; 
lean_dec_ref_known(v___x_2944_, 1);
lean_dec_ref(v_env_2943_);
lean_dec(v_stx_2888_);
lean_dec_ref(v_afterSet_2885_);
lean_dec_ref(v_ext_2884_);
lean_dec_ref(v_getParam_2883_);
v_name_2945_ = lean_ctor_get(v_toAttributeImplCore_2886_, 1);
lean_inc(v_name_2945_);
lean_dec_ref(v_toAttributeImplCore_2886_);
v___x_2946_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg(v_name_2945_, v_decl_2887_, v___y_2890_, v___y_2891_);
return v___x_2946_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___redArg___lam__0___boxed(lean_object* v_getParam_2951_, lean_object* v_ext_2952_, lean_object* v_afterSet_2953_, lean_object* v_toAttributeImplCore_2954_, lean_object* v_decl_2955_, lean_object* v_stx_2956_, lean_object* v_kind_2957_, lean_object* v___y_2958_, lean_object* v___y_2959_, lean_object* v___y_2960_){
_start:
{
uint8_t v_kind_boxed_2961_; lean_object* v_res_2962_; 
v_kind_boxed_2961_ = lean_unbox(v_kind_2957_);
v_res_2962_ = l_Lean_registerParametricAttributeForExt___redArg___lam__0(v_getParam_2951_, v_ext_2952_, v_afterSet_2953_, v_toAttributeImplCore_2954_, v_decl_2955_, v_stx_2956_, v_kind_boxed_2961_, v___y_2958_, v___y_2959_);
lean_dec(v___y_2959_);
lean_dec_ref(v___y_2958_);
return v_res_2962_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___redArg___lam__1(lean_object* v_toAttributeImplCore_2963_, lean_object* v_decl_2964_, lean_object* v___y_2965_, lean_object* v___y_2966_){
_start:
{
lean_object* v_name_2968_; lean_object* v___x_2969_; lean_object* v___x_2970_; lean_object* v___x_2971_; lean_object* v___x_2972_; lean_object* v___x_2973_; lean_object* v___x_2974_; 
v_name_2968_ = lean_ctor_get(v_toAttributeImplCore_2963_, 1);
lean_inc(v_name_2968_);
lean_dec_ref(v_toAttributeImplCore_2963_);
v___x_2969_ = lean_obj_once(&l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1, &l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1_once, _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1);
v___x_2970_ = l_Lean_MessageData_ofName(v_name_2968_);
v___x_2971_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2971_, 0, v___x_2969_);
lean_ctor_set(v___x_2971_, 1, v___x_2970_);
v___x_2972_ = lean_obj_once(&l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3, &l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3_once, _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3);
v___x_2973_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2973_, 0, v___x_2971_);
lean_ctor_set(v___x_2973_, 1, v___x_2972_);
v___x_2974_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_2973_, v___y_2965_, v___y_2966_);
return v___x_2974_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___redArg___lam__1___boxed(lean_object* v_toAttributeImplCore_2975_, lean_object* v_decl_2976_, lean_object* v___y_2977_, lean_object* v___y_2978_, lean_object* v___y_2979_){
_start:
{
lean_object* v_res_2980_; 
v_res_2980_ = l_Lean_registerParametricAttributeForExt___redArg___lam__1(v_toAttributeImplCore_2975_, v_decl_2976_, v___y_2977_, v___y_2978_);
lean_dec(v___y_2978_);
lean_dec_ref(v___y_2977_);
lean_dec(v_decl_2976_);
return v_res_2980_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___redArg(lean_object* v_impl_2981_, lean_object* v_ext_2982_){
_start:
{
lean_object* v_toAttributeImplCore_2984_; lean_object* v_getParam_2985_; lean_object* v_afterSet_2986_; uint8_t v_preserveOrder_2987_; lean_object* v___f_2988_; lean_object* v___f_2989_; lean_object* v_attrImpl_2990_; lean_object* v___x_2991_; 
v_toAttributeImplCore_2984_ = lean_ctor_get(v_impl_2981_, 0);
lean_inc_ref_n(v_toAttributeImplCore_2984_, 3);
v_getParam_2985_ = lean_ctor_get(v_impl_2981_, 1);
lean_inc_ref(v_getParam_2985_);
v_afterSet_2986_ = lean_ctor_get(v_impl_2981_, 2);
lean_inc_ref(v_afterSet_2986_);
v_preserveOrder_2987_ = lean_ctor_get_uint8(v_impl_2981_, sizeof(void*)*4);
lean_dec_ref(v_impl_2981_);
lean_inc_ref(v_ext_2982_);
v___f_2988_ = lean_alloc_closure((void*)(l_Lean_registerParametricAttributeForExt___redArg___lam__0___boxed), 10, 4);
lean_closure_set(v___f_2988_, 0, v_getParam_2985_);
lean_closure_set(v___f_2988_, 1, v_ext_2982_);
lean_closure_set(v___f_2988_, 2, v_afterSet_2986_);
lean_closure_set(v___f_2988_, 3, v_toAttributeImplCore_2984_);
v___f_2989_ = lean_alloc_closure((void*)(l_Lean_registerParametricAttributeForExt___redArg___lam__1___boxed), 5, 1);
lean_closure_set(v___f_2989_, 0, v_toAttributeImplCore_2984_);
v_attrImpl_2990_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_attrImpl_2990_, 0, v_toAttributeImplCore_2984_);
lean_ctor_set(v_attrImpl_2990_, 1, v___f_2988_);
lean_ctor_set(v_attrImpl_2990_, 2, v___f_2989_);
lean_inc_ref(v_attrImpl_2990_);
v___x_2991_ = l_Lean_registerBuiltinAttribute(v_attrImpl_2990_);
if (lean_obj_tag(v___x_2991_) == 0)
{
lean_object* v___x_2993_; uint8_t v_isShared_2994_; uint8_t v_isSharedCheck_2999_; 
v_isSharedCheck_2999_ = !lean_is_exclusive(v___x_2991_);
if (v_isSharedCheck_2999_ == 0)
{
lean_object* v_unused_3000_; 
v_unused_3000_ = lean_ctor_get(v___x_2991_, 0);
lean_dec(v_unused_3000_);
v___x_2993_ = v___x_2991_;
v_isShared_2994_ = v_isSharedCheck_2999_;
goto v_resetjp_2992_;
}
else
{
lean_dec(v___x_2991_);
v___x_2993_ = lean_box(0);
v_isShared_2994_ = v_isSharedCheck_2999_;
goto v_resetjp_2992_;
}
v_resetjp_2992_:
{
lean_object* v___x_2995_; lean_object* v___x_2997_; 
v___x_2995_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2995_, 0, v_attrImpl_2990_);
lean_ctor_set(v___x_2995_, 1, v_ext_2982_);
lean_ctor_set_uint8(v___x_2995_, sizeof(void*)*2, v_preserveOrder_2987_);
if (v_isShared_2994_ == 0)
{
lean_ctor_set(v___x_2993_, 0, v___x_2995_);
v___x_2997_ = v___x_2993_;
goto v_reusejp_2996_;
}
else
{
lean_object* v_reuseFailAlloc_2998_; 
v_reuseFailAlloc_2998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2998_, 0, v___x_2995_);
v___x_2997_ = v_reuseFailAlloc_2998_;
goto v_reusejp_2996_;
}
v_reusejp_2996_:
{
return v___x_2997_;
}
}
}
else
{
lean_object* v_a_3001_; lean_object* v___x_3003_; uint8_t v_isShared_3004_; uint8_t v_isSharedCheck_3008_; 
lean_dec_ref_known(v_attrImpl_2990_, 3);
lean_dec_ref(v_ext_2982_);
v_a_3001_ = lean_ctor_get(v___x_2991_, 0);
v_isSharedCheck_3008_ = !lean_is_exclusive(v___x_2991_);
if (v_isSharedCheck_3008_ == 0)
{
v___x_3003_ = v___x_2991_;
v_isShared_3004_ = v_isSharedCheck_3008_;
goto v_resetjp_3002_;
}
else
{
lean_inc(v_a_3001_);
lean_dec(v___x_2991_);
v___x_3003_ = lean_box(0);
v_isShared_3004_ = v_isSharedCheck_3008_;
goto v_resetjp_3002_;
}
v_resetjp_3002_:
{
lean_object* v___x_3006_; 
if (v_isShared_3004_ == 0)
{
v___x_3006_ = v___x_3003_;
goto v_reusejp_3005_;
}
else
{
lean_object* v_reuseFailAlloc_3007_; 
v_reuseFailAlloc_3007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3007_, 0, v_a_3001_);
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
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___redArg___boxed(lean_object* v_impl_3009_, lean_object* v_ext_3010_, lean_object* v_a_3011_){
_start:
{
lean_object* v_res_3012_; 
v_res_3012_ = l_Lean_registerParametricAttributeForExt___redArg(v_impl_3009_, v_ext_3010_);
return v_res_3012_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt(lean_object* v_00_u03b1_3013_, lean_object* v_impl_3014_, lean_object* v_ext_3015_){
_start:
{
lean_object* v___x_3017_; 
v___x_3017_ = l_Lean_registerParametricAttributeForExt___redArg(v_impl_3014_, v_ext_3015_);
return v___x_3017_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___boxed(lean_object* v_00_u03b1_3018_, lean_object* v_impl_3019_, lean_object* v_ext_3020_, lean_object* v_a_3021_){
_start:
{
lean_object* v_res_3022_; 
v_res_3022_ = l_Lean_registerParametricAttributeForExt(v_00_u03b1_3018_, v_impl_3019_, v_ext_3020_);
return v_res_3022_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg(lean_object* v_impl_3023_){
_start:
{
lean_object* v_toAttributeImplCore_3025_; uint8_t v_preserveOrder_3026_; lean_object* v_filterExport_3027_; lean_object* v_ref_3028_; lean_object* v___x_3029_; 
v_toAttributeImplCore_3025_ = lean_ctor_get(v_impl_3023_, 0);
v_preserveOrder_3026_ = lean_ctor_get_uint8(v_impl_3023_, sizeof(void*)*4);
v_filterExport_3027_ = lean_ctor_get(v_impl_3023_, 3);
v_ref_3028_ = lean_ctor_get(v_toAttributeImplCore_3025_, 0);
lean_inc_ref(v_filterExport_3027_);
lean_inc(v_ref_3028_);
v___x_3029_ = l_Lean_registerParametricAttributeExt___redArg(v_ref_3028_, v_preserveOrder_3026_, v_filterExport_3027_);
if (lean_obj_tag(v___x_3029_) == 0)
{
lean_object* v_a_3030_; lean_object* v___x_3031_; 
v_a_3030_ = lean_ctor_get(v___x_3029_, 0);
lean_inc(v_a_3030_);
lean_dec_ref_known(v___x_3029_, 1);
v___x_3031_ = l_Lean_registerParametricAttributeForExt___redArg(v_impl_3023_, v_a_3030_);
return v___x_3031_;
}
else
{
lean_object* v_a_3032_; lean_object* v___x_3034_; uint8_t v_isShared_3035_; uint8_t v_isSharedCheck_3039_; 
lean_dec_ref(v_impl_3023_);
v_a_3032_ = lean_ctor_get(v___x_3029_, 0);
v_isSharedCheck_3039_ = !lean_is_exclusive(v___x_3029_);
if (v_isSharedCheck_3039_ == 0)
{
v___x_3034_ = v___x_3029_;
v_isShared_3035_ = v_isSharedCheck_3039_;
goto v_resetjp_3033_;
}
else
{
lean_inc(v_a_3032_);
lean_dec(v___x_3029_);
v___x_3034_ = lean_box(0);
v_isShared_3035_ = v_isSharedCheck_3039_;
goto v_resetjp_3033_;
}
v_resetjp_3033_:
{
lean_object* v___x_3037_; 
if (v_isShared_3035_ == 0)
{
v___x_3037_ = v___x_3034_;
goto v_reusejp_3036_;
}
else
{
lean_object* v_reuseFailAlloc_3038_; 
v_reuseFailAlloc_3038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3038_, 0, v_a_3032_);
v___x_3037_ = v_reuseFailAlloc_3038_;
goto v_reusejp_3036_;
}
v_reusejp_3036_:
{
return v___x_3037_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___boxed(lean_object* v_impl_3040_, lean_object* v_a_3041_){
_start:
{
lean_object* v_res_3042_; 
v_res_3042_ = l_Lean_registerParametricAttribute___redArg(v_impl_3040_);
return v_res_3042_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute(lean_object* v_00_u03b1_3043_, lean_object* v_impl_3044_){
_start:
{
lean_object* v___x_3046_; 
v___x_3046_ = l_Lean_registerParametricAttribute___redArg(v_impl_3044_);
return v___x_3046_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___boxed(lean_object* v_00_u03b1_3047_, lean_object* v_impl_3048_, lean_object* v_a_3049_){
_start:
{
lean_object* v_res_3050_; 
v_res_3050_ = l_Lean_registerParametricAttribute(v_00_u03b1_3047_, v_impl_3048_);
return v_res_3050_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___lam__1(lean_object* v_decl_3051_, lean_object* v___x_3052_, lean_object* v___x_3053_, lean_object* v_a_3054_, lean_object* v_x_3055_, lean_object* v___y_3056_){
_start:
{
lean_object* v_fst_3057_; uint8_t v___x_3058_; 
v_fst_3057_ = lean_ctor_get(v_a_3054_, 0);
v___x_3058_ = lean_name_eq(v_fst_3057_, v_decl_3051_);
if (v___x_3058_ == 0)
{
lean_object* v___x_3059_; 
lean_dec_ref(v_a_3054_);
v___x_3059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3059_, 0, v___x_3052_);
return v___x_3059_;
}
else
{
lean_object* v___x_3060_; lean_object* v___x_3061_; lean_object* v___x_3062_; lean_object* v___x_3063_; 
lean_dec_ref(v___x_3052_);
v___x_3060_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3060_, 0, v_a_3054_);
v___x_3061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3061_, 0, v___x_3060_);
v___x_3062_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3062_, 0, v___x_3061_);
lean_ctor_set(v___x_3062_, 1, v___x_3053_);
v___x_3063_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3063_, 0, v___x_3062_);
return v___x_3063_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___lam__1___boxed(lean_object* v_decl_3064_, lean_object* v___x_3065_, lean_object* v___x_3066_, lean_object* v_a_3067_, lean_object* v_x_3068_, lean_object* v___y_3069_){
_start:
{
lean_object* v_res_3070_; 
v_res_3070_ = l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___lam__1(v_decl_3064_, v___x_3065_, v___x_3066_, v_a_3067_, v_x_3068_, v___y_3069_);
lean_dec_ref(v___y_3069_);
lean_dec(v_decl_3064_);
return v_res_3070_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg(lean_object* v_inst_3098_, lean_object* v_ext_3099_, uint8_t v_preserveOrder_3100_, lean_object* v_env_3101_, lean_object* v_decl_3102_){
_start:
{
lean_object* v___y_3104_; lean_object* v___x_3115_; lean_object* v___x_3116_; 
v___x_3115_ = ((lean_object*)(l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__0));
v___x_3116_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3101_, v_decl_3102_);
if (lean_obj_tag(v___x_3116_) == 0)
{
lean_object* v_toEnvExtension_3117_; lean_object* v_asyncMode_3118_; lean_object* v___x_3119_; lean_object* v___x_3120_; lean_object* v_snd_3121_; lean_object* v___x_3122_; 
lean_dec(v_inst_3098_);
v_toEnvExtension_3117_ = lean_ctor_get(v_ext_3099_, 0);
v_asyncMode_3118_ = lean_ctor_get(v_toEnvExtension_3117_, 2);
v___x_3119_ = lean_box(0);
v___x_3120_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3115_, v_ext_3099_, v_env_3101_, v_asyncMode_3118_, v___x_3119_);
v_snd_3121_ = lean_ctor_get(v___x_3120_, 1);
lean_inc(v_snd_3121_);
lean_dec(v___x_3120_);
v___x_3122_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_snd_3121_, v_decl_3102_);
lean_dec(v_decl_3102_);
lean_dec(v_snd_3121_);
return v___x_3122_;
}
else
{
if (v_preserveOrder_3100_ == 0)
{
lean_object* v_val_3123_; uint8_t v___x_3124_; lean_object* v___x_3125_; lean_object* v___x_3126_; lean_object* v___x_3127_; uint8_t v___x_3128_; 
v_val_3123_ = lean_ctor_get(v___x_3116_, 0);
lean_inc(v_val_3123_);
lean_dec_ref_known(v___x_3116_, 1);
v___x_3124_ = 0;
v___x_3125_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_3115_, v_ext_3099_, v_env_3101_, v_val_3123_, v___x_3124_);
lean_dec(v_val_3123_);
lean_dec_ref(v_env_3101_);
v___x_3126_ = lean_unsigned_to_nat(0u);
v___x_3127_ = lean_array_get_size(v___x_3125_);
v___x_3128_ = lean_nat_dec_lt(v___x_3126_, v___x_3127_);
if (v___x_3128_ == 0)
{
lean_object* v___x_3129_; 
lean_dec_ref(v___x_3125_);
lean_dec(v_decl_3102_);
lean_dec(v_inst_3098_);
v___x_3129_ = lean_box(0);
return v___x_3129_;
}
else
{
lean_object* v___x_3130_; lean_object* v___x_3131_; uint8_t v___x_3132_; 
v___x_3130_ = lean_unsigned_to_nat(1u);
v___x_3131_ = lean_nat_sub(v___x_3127_, v___x_3130_);
v___x_3132_ = lean_nat_dec_le(v___x_3126_, v___x_3131_);
if (v___x_3132_ == 0)
{
lean_object* v___x_3133_; 
lean_dec(v___x_3131_);
lean_dec_ref(v___x_3125_);
lean_dec(v_decl_3102_);
lean_dec(v_inst_3098_);
v___x_3133_ = lean_box(0);
return v___x_3133_;
}
else
{
lean_object* v___f_3134_; lean_object* v___x_3135_; lean_object* v___x_3136_; lean_object* v___x_3137_; 
v___f_3134_ = ((lean_object*)(l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__1));
v___x_3135_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3135_, 0, v_decl_3102_);
lean_ctor_set(v___x_3135_, 1, v_inst_3098_);
v___x_3136_ = ((lean_object*)(l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__2));
v___x_3137_ = l_Array_binSearchAux___redArg(v___f_3134_, v___x_3136_, v___x_3125_, v___x_3135_, v___x_3126_, v___x_3131_);
lean_dec_ref(v___x_3125_);
v___y_3104_ = v___x_3137_;
goto v___jp_3103_;
}
}
}
else
{
lean_object* v_val_3138_; uint8_t v___x_3139_; lean_object* v___x_3140_; lean_object* v___x_3141_; lean_object* v___x_3142_; lean_object* v___x_3143_; lean_object* v___x_3144_; lean_object* v___f_3145_; size_t v_sz_3146_; size_t v___x_3147_; lean_object* v___x_3148_; lean_object* v_fst_3149_; 
lean_dec(v_inst_3098_);
v_val_3138_ = lean_ctor_get(v___x_3116_, 0);
lean_inc(v_val_3138_);
lean_dec_ref_known(v___x_3116_, 1);
v___x_3139_ = 0;
v___x_3140_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_3115_, v_ext_3099_, v_env_3101_, v_val_3138_, v___x_3139_);
lean_dec(v_val_3138_);
lean_dec_ref(v_env_3101_);
v___x_3141_ = ((lean_object*)(l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__12));
v___x_3142_ = lean_box(0);
v___x_3143_ = lean_box(0);
v___x_3144_ = ((lean_object*)(l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__13));
v___f_3145_ = lean_alloc_closure((void*)(l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___lam__1___boxed), 6, 3);
lean_closure_set(v___f_3145_, 0, v_decl_3102_);
lean_closure_set(v___f_3145_, 1, v___x_3144_);
lean_closure_set(v___f_3145_, 2, v___x_3143_);
v_sz_3146_ = lean_array_size(v___x_3140_);
v___x_3147_ = ((size_t)0ULL);
v___x_3148_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_3141_, v___x_3140_, v___f_3145_, v_sz_3146_, v___x_3147_, v___x_3144_);
v_fst_3149_ = lean_ctor_get(v___x_3148_, 0);
lean_inc(v_fst_3149_);
lean_dec(v___x_3148_);
if (lean_obj_tag(v_fst_3149_) == 0)
{
return v___x_3142_;
}
else
{
lean_object* v_val_3150_; 
v_val_3150_ = lean_ctor_get(v_fst_3149_, 0);
lean_inc(v_val_3150_);
lean_dec_ref_known(v_fst_3149_, 1);
v___y_3104_ = v_val_3150_;
goto v___jp_3103_;
}
}
}
v___jp_3103_:
{
if (lean_obj_tag(v___y_3104_) == 0)
{
lean_object* v___x_3105_; 
v___x_3105_ = lean_box(0);
return v___x_3105_;
}
else
{
lean_object* v_val_3106_; lean_object* v___x_3108_; uint8_t v_isShared_3109_; uint8_t v_isSharedCheck_3114_; 
v_val_3106_ = lean_ctor_get(v___y_3104_, 0);
v_isSharedCheck_3114_ = !lean_is_exclusive(v___y_3104_);
if (v_isSharedCheck_3114_ == 0)
{
v___x_3108_ = v___y_3104_;
v_isShared_3109_ = v_isSharedCheck_3114_;
goto v_resetjp_3107_;
}
else
{
lean_inc(v_val_3106_);
lean_dec(v___y_3104_);
v___x_3108_ = lean_box(0);
v_isShared_3109_ = v_isSharedCheck_3114_;
goto v_resetjp_3107_;
}
v_resetjp_3107_:
{
lean_object* v_snd_3110_; lean_object* v___x_3112_; 
v_snd_3110_ = lean_ctor_get(v_val_3106_, 1);
lean_inc(v_snd_3110_);
lean_dec(v_val_3106_);
if (v_isShared_3109_ == 0)
{
lean_ctor_set(v___x_3108_, 0, v_snd_3110_);
v___x_3112_ = v___x_3108_;
goto v_reusejp_3111_;
}
else
{
lean_object* v_reuseFailAlloc_3113_; 
v_reuseFailAlloc_3113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3113_, 0, v_snd_3110_);
v___x_3112_ = v_reuseFailAlloc_3113_;
goto v_reusejp_3111_;
}
v_reusejp_3111_:
{
return v___x_3112_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___boxed(lean_object* v_inst_3151_, lean_object* v_ext_3152_, lean_object* v_preserveOrder_3153_, lean_object* v_env_3154_, lean_object* v_decl_3155_){
_start:
{
uint8_t v_preserveOrder_boxed_3156_; lean_object* v_res_3157_; 
v_preserveOrder_boxed_3156_ = lean_unbox(v_preserveOrder_3153_);
v_res_3157_ = l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg(v_inst_3151_, v_ext_3152_, v_preserveOrder_boxed_3156_, v_env_3154_, v_decl_3155_);
lean_dec_ref(v_ext_3152_);
return v_res_3157_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f(lean_object* v_00_u03b1_3158_, lean_object* v_inst_3159_, lean_object* v_ext_3160_, uint8_t v_preserveOrder_3161_, lean_object* v_env_3162_, lean_object* v_decl_3163_){
_start:
{
lean_object* v___x_3164_; 
v___x_3164_ = l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg(v_inst_3159_, v_ext_3160_, v_preserveOrder_3161_, v_env_3162_, v_decl_3163_);
return v___x_3164_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f___boxed(lean_object* v_00_u03b1_3165_, lean_object* v_inst_3166_, lean_object* v_ext_3167_, lean_object* v_preserveOrder_3168_, lean_object* v_env_3169_, lean_object* v_decl_3170_){
_start:
{
uint8_t v_preserveOrder_boxed_3171_; lean_object* v_res_3172_; 
v_preserveOrder_boxed_3171_ = lean_unbox(v_preserveOrder_3168_);
v_res_3172_ = l_Lean_ParametricAttribute_getParamFromExt_x3f(v_00_u03b1_3165_, v_inst_3166_, v_ext_3167_, v_preserveOrder_boxed_3171_, v_env_3169_, v_decl_3170_);
lean_dec_ref(v_ext_3167_);
return v_res_3172_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParam_x3f___redArg(lean_object* v_inst_3173_, lean_object* v_attr_3174_, lean_object* v_env_3175_, lean_object* v_decl_3176_){
_start:
{
lean_object* v_ext_3177_; uint8_t v_preserveOrder_3178_; lean_object* v___x_3179_; 
v_ext_3177_ = lean_ctor_get(v_attr_3174_, 1);
v_preserveOrder_3178_ = lean_ctor_get_uint8(v_attr_3174_, sizeof(void*)*2);
v___x_3179_ = l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg(v_inst_3173_, v_ext_3177_, v_preserveOrder_3178_, v_env_3175_, v_decl_3176_);
return v___x_3179_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParam_x3f___redArg___boxed(lean_object* v_inst_3180_, lean_object* v_attr_3181_, lean_object* v_env_3182_, lean_object* v_decl_3183_){
_start:
{
lean_object* v_res_3184_; 
v_res_3184_ = l_Lean_ParametricAttribute_getParam_x3f___redArg(v_inst_3180_, v_attr_3181_, v_env_3182_, v_decl_3183_);
lean_dec_ref(v_attr_3181_);
return v_res_3184_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParam_x3f(lean_object* v_00_u03b1_3185_, lean_object* v_inst_3186_, lean_object* v_attr_3187_, lean_object* v_env_3188_, lean_object* v_decl_3189_){
_start:
{
lean_object* v___x_3190_; 
v___x_3190_ = l_Lean_ParametricAttribute_getParam_x3f___redArg(v_inst_3186_, v_attr_3187_, v_env_3188_, v_decl_3189_);
return v___x_3190_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParam_x3f___boxed(lean_object* v_00_u03b1_3191_, lean_object* v_inst_3192_, lean_object* v_attr_3193_, lean_object* v_env_3194_, lean_object* v_decl_3195_){
_start:
{
lean_object* v_res_3196_; 
v_res_3196_ = l_Lean_ParametricAttribute_getParam_x3f(v_00_u03b1_3191_, v_inst_3192_, v_attr_3193_, v_env_3194_, v_decl_3195_);
lean_dec_ref(v_attr_3193_);
return v_res_3196_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_setParamFromExt___redArg(lean_object* v_ext_3201_, lean_object* v_attr_3202_, lean_object* v_env_3203_, lean_object* v_decl_3204_, lean_object* v_param_3205_){
_start:
{
lean_object* v___x_3206_; 
v___x_3206_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3203_, v_decl_3204_);
if (lean_obj_tag(v___x_3206_) == 0)
{
lean_object* v_toEnvExtension_3207_; lean_object* v_asyncMode_3208_; lean_object* v___x_3209_; lean_object* v___x_3210_; lean_object* v___x_3211_; lean_object* v_snd_3212_; lean_object* v___x_3214_; uint8_t v_isShared_3215_; uint8_t v_isSharedCheck_3242_; 
v_toEnvExtension_3207_ = lean_ctor_get(v_ext_3201_, 0);
v_asyncMode_3208_ = lean_ctor_get(v_toEnvExtension_3207_, 2);
lean_inc(v_asyncMode_3208_);
v___x_3209_ = ((lean_object*)(l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__0));
v___x_3210_ = lean_box(0);
lean_inc_ref(v_env_3203_);
v___x_3211_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3209_, v_ext_3201_, v_env_3203_, v_asyncMode_3208_, v___x_3210_);
v_snd_3212_ = lean_ctor_get(v___x_3211_, 1);
v_isSharedCheck_3242_ = !lean_is_exclusive(v___x_3211_);
if (v_isSharedCheck_3242_ == 0)
{
lean_object* v_unused_3243_; 
v_unused_3243_ = lean_ctor_get(v___x_3211_, 0);
lean_dec(v_unused_3243_);
v___x_3214_ = v___x_3211_;
v_isShared_3215_ = v_isSharedCheck_3242_;
goto v_resetjp_3213_;
}
else
{
lean_inc(v_snd_3212_);
lean_dec(v___x_3211_);
v___x_3214_ = lean_box(0);
v_isShared_3215_ = v_isSharedCheck_3242_;
goto v_resetjp_3213_;
}
v_resetjp_3213_:
{
lean_object* v___x_3216_; 
v___x_3216_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_snd_3212_, v_decl_3204_);
lean_dec(v_snd_3212_);
if (lean_obj_tag(v___x_3216_) == 0)
{
lean_object* v___x_3218_; 
lean_dec_ref(v_attr_3202_);
if (v_isShared_3215_ == 0)
{
lean_ctor_set(v___x_3214_, 1, v_param_3205_);
lean_ctor_set(v___x_3214_, 0, v_decl_3204_);
v___x_3218_ = v___x_3214_;
goto v_reusejp_3217_;
}
else
{
lean_object* v_reuseFailAlloc_3221_; 
v_reuseFailAlloc_3221_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3221_, 0, v_decl_3204_);
lean_ctor_set(v_reuseFailAlloc_3221_, 1, v_param_3205_);
v___x_3218_ = v_reuseFailAlloc_3221_;
goto v_reusejp_3217_;
}
v_reusejp_3217_:
{
lean_object* v___x_3219_; lean_object* v___x_3220_; 
v___x_3219_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_ext_3201_, v_env_3203_, v___x_3218_, v_asyncMode_3208_, v___x_3210_);
lean_dec(v_asyncMode_3208_);
v___x_3220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3220_, 0, v___x_3219_);
return v___x_3220_;
}
}
else
{
lean_object* v___x_3223_; uint8_t v_isShared_3224_; uint8_t v_isSharedCheck_3240_; 
lean_del_object(v___x_3214_);
lean_dec(v_asyncMode_3208_);
lean_dec(v_param_3205_);
lean_dec_ref(v_env_3203_);
lean_dec_ref(v_ext_3201_);
v_isSharedCheck_3240_ = !lean_is_exclusive(v___x_3216_);
if (v_isSharedCheck_3240_ == 0)
{
lean_object* v_unused_3241_; 
v_unused_3241_ = lean_ctor_get(v___x_3216_, 0);
lean_dec(v_unused_3241_);
v___x_3223_ = v___x_3216_;
v_isShared_3224_ = v_isSharedCheck_3240_;
goto v_resetjp_3222_;
}
else
{
lean_dec(v___x_3216_);
v___x_3223_ = lean_box(0);
v_isShared_3224_ = v_isSharedCheck_3240_;
goto v_resetjp_3222_;
}
v_resetjp_3222_:
{
lean_object* v_toAttributeImplCore_3225_; lean_object* v_name_3226_; uint8_t v___x_3227_; lean_object* v___x_3228_; lean_object* v___x_3229_; lean_object* v___x_3230_; lean_object* v___x_3231_; lean_object* v___x_3232_; lean_object* v___x_3233_; lean_object* v___x_3234_; lean_object* v___x_3235_; lean_object* v___x_3236_; lean_object* v___x_3238_; 
v_toAttributeImplCore_3225_ = lean_ctor_get(v_attr_3202_, 0);
lean_inc_ref(v_toAttributeImplCore_3225_);
lean_dec_ref(v_attr_3202_);
v_name_3226_ = lean_ctor_get(v_toAttributeImplCore_3225_, 1);
lean_inc(v_name_3226_);
lean_dec_ref(v_toAttributeImplCore_3225_);
v___x_3227_ = 1;
v___x_3228_ = ((lean_object*)(l_Lean_ParametricAttribute_setParamFromExt___redArg___closed__0));
v___x_3229_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_3226_, v___x_3227_);
v___x_3230_ = lean_string_append(v___x_3228_, v___x_3229_);
lean_dec_ref(v___x_3229_);
v___x_3231_ = ((lean_object*)(l_Lean_ParametricAttribute_setParamFromExt___redArg___closed__1));
v___x_3232_ = lean_string_append(v___x_3230_, v___x_3231_);
v___x_3233_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_decl_3204_, v___x_3227_);
v___x_3234_ = lean_string_append(v___x_3232_, v___x_3233_);
lean_dec_ref(v___x_3233_);
v___x_3235_ = ((lean_object*)(l_Lean_ParametricAttribute_setParamFromExt___redArg___closed__2));
v___x_3236_ = lean_string_append(v___x_3234_, v___x_3235_);
if (v_isShared_3224_ == 0)
{
lean_ctor_set_tag(v___x_3223_, 0);
lean_ctor_set(v___x_3223_, 0, v___x_3236_);
v___x_3238_ = v___x_3223_;
goto v_reusejp_3237_;
}
else
{
lean_object* v_reuseFailAlloc_3239_; 
v_reuseFailAlloc_3239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3239_, 0, v___x_3236_);
v___x_3238_ = v_reuseFailAlloc_3239_;
goto v_reusejp_3237_;
}
v_reusejp_3237_:
{
return v___x_3238_;
}
}
}
}
}
else
{
lean_object* v___x_3245_; uint8_t v_isShared_3246_; uint8_t v_isSharedCheck_3262_; 
lean_dec(v_param_3205_);
lean_dec_ref(v_env_3203_);
lean_dec_ref(v_ext_3201_);
v_isSharedCheck_3262_ = !lean_is_exclusive(v___x_3206_);
if (v_isSharedCheck_3262_ == 0)
{
lean_object* v_unused_3263_; 
v_unused_3263_ = lean_ctor_get(v___x_3206_, 0);
lean_dec(v_unused_3263_);
v___x_3245_ = v___x_3206_;
v_isShared_3246_ = v_isSharedCheck_3262_;
goto v_resetjp_3244_;
}
else
{
lean_dec(v___x_3206_);
v___x_3245_ = lean_box(0);
v_isShared_3246_ = v_isSharedCheck_3262_;
goto v_resetjp_3244_;
}
v_resetjp_3244_:
{
lean_object* v_toAttributeImplCore_3247_; lean_object* v_name_3248_; uint8_t v___x_3249_; lean_object* v___x_3250_; lean_object* v___x_3251_; lean_object* v___x_3252_; lean_object* v___x_3253_; lean_object* v___x_3254_; lean_object* v___x_3255_; lean_object* v___x_3256_; lean_object* v___x_3257_; lean_object* v___x_3258_; lean_object* v___x_3260_; 
v_toAttributeImplCore_3247_ = lean_ctor_get(v_attr_3202_, 0);
lean_inc_ref(v_toAttributeImplCore_3247_);
lean_dec_ref(v_attr_3202_);
v_name_3248_ = lean_ctor_get(v_toAttributeImplCore_3247_, 1);
lean_inc(v_name_3248_);
lean_dec_ref(v_toAttributeImplCore_3247_);
v___x_3249_ = 1;
v___x_3250_ = ((lean_object*)(l_Lean_ParametricAttribute_setParamFromExt___redArg___closed__0));
v___x_3251_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_3248_, v___x_3249_);
v___x_3252_ = lean_string_append(v___x_3250_, v___x_3251_);
lean_dec_ref(v___x_3251_);
v___x_3253_ = ((lean_object*)(l_Lean_ParametricAttribute_setParamFromExt___redArg___closed__1));
v___x_3254_ = lean_string_append(v___x_3252_, v___x_3253_);
v___x_3255_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_decl_3204_, v___x_3249_);
v___x_3256_ = lean_string_append(v___x_3254_, v___x_3255_);
lean_dec_ref(v___x_3255_);
v___x_3257_ = ((lean_object*)(l_Lean_ParametricAttribute_setParamFromExt___redArg___closed__3));
v___x_3258_ = lean_string_append(v___x_3256_, v___x_3257_);
if (v_isShared_3246_ == 0)
{
lean_ctor_set_tag(v___x_3245_, 0);
lean_ctor_set(v___x_3245_, 0, v___x_3258_);
v___x_3260_ = v___x_3245_;
goto v_reusejp_3259_;
}
else
{
lean_object* v_reuseFailAlloc_3261_; 
v_reuseFailAlloc_3261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3261_, 0, v___x_3258_);
v___x_3260_ = v_reuseFailAlloc_3261_;
goto v_reusejp_3259_;
}
v_reusejp_3259_:
{
return v___x_3260_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_setParamFromExt(lean_object* v_00_u03b1_3264_, lean_object* v_ext_3265_, lean_object* v_attr_3266_, lean_object* v_env_3267_, lean_object* v_decl_3268_, lean_object* v_param_3269_){
_start:
{
lean_object* v___x_3270_; 
v___x_3270_ = l_Lean_ParametricAttribute_setParamFromExt___redArg(v_ext_3265_, v_attr_3266_, v_env_3267_, v_decl_3268_, v_param_3269_);
return v___x_3270_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_setParam___redArg(lean_object* v_attr_3271_, lean_object* v_env_3272_, lean_object* v_decl_3273_, lean_object* v_param_3274_){
_start:
{
lean_object* v_attr_3275_; lean_object* v_ext_3276_; lean_object* v___x_3277_; 
v_attr_3275_ = lean_ctor_get(v_attr_3271_, 0);
lean_inc_ref(v_attr_3275_);
v_ext_3276_ = lean_ctor_get(v_attr_3271_, 1);
lean_inc_ref(v_ext_3276_);
lean_dec_ref(v_attr_3271_);
v___x_3277_ = l_Lean_ParametricAttribute_setParamFromExt___redArg(v_ext_3276_, v_attr_3275_, v_env_3272_, v_decl_3273_, v_param_3274_);
return v___x_3277_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_setParam(lean_object* v_00_u03b1_3278_, lean_object* v_attr_3279_, lean_object* v_env_3280_, lean_object* v_decl_3281_, lean_object* v_param_3282_){
_start:
{
lean_object* v___x_3283_; 
v___x_3283_ = l_Lean_ParametricAttribute_setParam___redArg(v_attr_3279_, v_env_3280_, v_decl_3281_, v_param_3282_);
return v___x_3283_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___lam__0(lean_object* v_x_3284_, lean_object* v___y_3285_){
_start:
{
lean_object* v___x_3287_; lean_object* v___x_3288_; 
v___x_3287_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___lam__0___closed__1));
v___x_3288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3288_, 0, v___x_3287_);
return v___x_3288_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___lam__0___boxed(lean_object* v_x_3289_, lean_object* v___y_3290_, lean_object* v___y_3291_){
_start:
{
lean_object* v_res_3292_; 
v_res_3292_ = l_Lean_instInhabitedEnumAttributes_default___lam__0(v_x_3289_, v___y_3290_);
lean_dec_ref(v___y_3290_);
lean_dec_ref(v_x_3289_);
return v_res_3292_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___lam__1(lean_object* v_s_3293_, lean_object* v_x_3294_){
_start:
{
lean_inc(v_s_3293_);
return v_s_3293_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___lam__1___boxed(lean_object* v_s_3295_, lean_object* v_x_3296_){
_start:
{
lean_object* v_res_3297_; 
v_res_3297_ = l_Lean_instInhabitedEnumAttributes_default___lam__1(v_s_3295_, v_x_3296_);
lean_dec_ref(v_x_3296_);
lean_dec(v_s_3295_);
return v_res_3297_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___lam__2(lean_object* v_x_3298_, lean_object* v_x_3299_){
_start:
{
lean_object* v___x_3300_; 
v___x_3300_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___lam__2___closed__1));
return v___x_3300_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___lam__2___boxed(lean_object* v_x_3301_, lean_object* v_x_3302_){
_start:
{
lean_object* v_res_3303_; 
v_res_3303_ = l_Lean_instInhabitedEnumAttributes_default___lam__2(v_x_3301_, v_x_3302_);
lean_dec(v_x_3302_);
lean_dec_ref(v_x_3301_);
return v_res_3303_;
}
}
static lean_object* _init_l_Lean_instInhabitedEnumAttributes_default___closed__3(void){
_start:
{
lean_object* v___x_3307_; 
v___x_3307_ = l_Lean_instInhabitedEnvExtension_default(lean_box(0));
return v___x_3307_;
}
}
static lean_object* _init_l_Lean_instInhabitedEnumAttributes_default___closed__4(void){
_start:
{
lean_object* v___f_3308_; lean_object* v___f_3309_; lean_object* v___f_3310_; lean_object* v___f_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; 
v___f_3308_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___closed__3));
v___f_3309_ = ((lean_object*)(l_Lean_instInhabitedEnumAttributes_default___closed__2));
v___f_3310_ = ((lean_object*)(l_Lean_instInhabitedEnumAttributes_default___closed__1));
v___f_3311_ = ((lean_object*)(l_Lean_instInhabitedEnumAttributes_default___closed__0));
v___x_3312_ = lean_box(0);
v___x_3313_ = lean_obj_once(&l_Lean_instInhabitedEnumAttributes_default___closed__3, &l_Lean_instInhabitedEnumAttributes_default___closed__3_once, _init_l_Lean_instInhabitedEnumAttributes_default___closed__3);
v___x_3314_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3314_, 0, v___x_3313_);
lean_ctor_set(v___x_3314_, 1, v___x_3312_);
lean_ctor_set(v___x_3314_, 2, v___f_3311_);
lean_ctor_set(v___x_3314_, 3, v___f_3310_);
lean_ctor_set(v___x_3314_, 4, v___f_3309_);
lean_ctor_set(v___x_3314_, 5, v___f_3308_);
return v___x_3314_;
}
}
static lean_object* _init_l_Lean_instInhabitedEnumAttributes_default___closed__5(void){
_start:
{
lean_object* v___x_3315_; lean_object* v___x_3316_; lean_object* v___x_3317_; 
v___x_3315_ = lean_obj_once(&l_Lean_instInhabitedEnumAttributes_default___closed__4, &l_Lean_instInhabitedEnumAttributes_default___closed__4_once, _init_l_Lean_instInhabitedEnumAttributes_default___closed__4);
v___x_3316_ = lean_box(0);
v___x_3317_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3317_, 0, v___x_3316_);
lean_ctor_set(v___x_3317_, 1, v___x_3315_);
return v___x_3317_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default(lean_object* v_00_u03b1_3318_){
_start:
{
lean_object* v___x_3319_; 
v___x_3319_ = lean_obj_once(&l_Lean_instInhabitedEnumAttributes_default___closed__5, &l_Lean_instInhabitedEnumAttributes_default___closed__5_once, _init_l_Lean_instInhabitedEnumAttributes_default___closed__5);
return v___x_3319_;
}
}
static lean_object* _init_l_Lean_instInhabitedEnumAttributes___closed__0(void){
_start:
{
lean_object* v___x_3320_; 
v___x_3320_ = l_Lean_instInhabitedEnumAttributes_default(lean_box(0));
return v___x_3320_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes(lean_object* v_a_3321_){
_start:
{
lean_object* v___x_3322_; 
v___x_3322_ = lean_obj_once(&l_Lean_instInhabitedEnumAttributes___closed__0, &l_Lean_instInhabitedEnumAttributes___closed__0_once, _init_l_Lean_instInhabitedEnumAttributes___closed__0);
return v___x_3322_;
}
}
static lean_object* _init_l_Lean_registerEnumAttributes___auto__1(void){
_start:
{
lean_object* v___x_3323_; 
v___x_3323_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__28, &l_Lean_AttributeImplCore_ref___autoParam___closed__28_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__28);
return v___x_3323_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__0(lean_object* v_x_3324_){
_start:
{
lean_object* v___x_3325_; 
v___x_3325_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___lam__2___closed__0));
return v___x_3325_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__0___boxed(lean_object* v_x_3326_){
_start:
{
lean_object* v_res_3327_; 
v_res_3327_ = l_Lean_registerEnumAttributes___redArg___lam__0(v_x_3326_);
lean_dec(v_x_3326_);
return v_res_3327_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___redArg(lean_object* v_newState_3328_, lean_object* v_x_3329_, lean_object* v_x_3330_){
_start:
{
if (lean_obj_tag(v_x_3330_) == 0)
{
return v_x_3329_;
}
else
{
lean_object* v_head_3331_; lean_object* v_tail_3332_; lean_object* v___x_3333_; 
v_head_3331_ = lean_ctor_get(v_x_3330_, 0);
lean_inc(v_head_3331_);
v_tail_3332_ = lean_ctor_get(v_x_3330_, 1);
lean_inc(v_tail_3332_);
lean_dec_ref_known(v_x_3330_, 2);
v___x_3333_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_newState_3328_, v_head_3331_);
if (lean_obj_tag(v___x_3333_) == 1)
{
lean_object* v_val_3334_; lean_object* v___x_3335_; 
v_val_3334_ = lean_ctor_get(v___x_3333_, 0);
lean_inc(v_val_3334_);
lean_dec_ref_known(v___x_3333_, 1);
v___x_3335_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_head_3331_, v_val_3334_, v_x_3329_);
v_x_3329_ = v___x_3335_;
v_x_3330_ = v_tail_3332_;
goto _start;
}
else
{
lean_dec(v___x_3333_);
lean_dec(v_head_3331_);
v_x_3330_ = v_tail_3332_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___redArg___boxed(lean_object* v_newState_3338_, lean_object* v_x_3339_, lean_object* v_x_3340_){
_start:
{
lean_object* v_res_3341_; 
v_res_3341_ = l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___redArg(v_newState_3338_, v_x_3339_, v_x_3340_);
lean_dec(v_newState_3338_);
return v_res_3341_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__1(lean_object* v_x_3342_, lean_object* v_newState_3343_, lean_object* v_consts_3344_, lean_object* v_st_3345_){
_start:
{
lean_object* v___x_3346_; 
v___x_3346_ = l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___redArg(v_newState_3343_, v_st_3345_, v_consts_3344_);
return v___x_3346_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__1___boxed(lean_object* v_x_3347_, lean_object* v_newState_3348_, lean_object* v_consts_3349_, lean_object* v_st_3350_){
_start:
{
lean_object* v_res_3351_; 
v_res_3351_ = l_Lean_registerEnumAttributes___redArg___lam__1(v_x_3347_, v_newState_3348_, v_consts_3349_, v_st_3350_);
lean_dec(v_newState_3348_);
lean_dec(v_x_3347_);
return v_res_3351_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__2(lean_object* v_s_3361_){
_start:
{
lean_object* v___x_3362_; lean_object* v___y_3364_; 
v___x_3362_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___lam__2___closed__3));
if (lean_obj_tag(v_s_3361_) == 0)
{
lean_object* v_size_3368_; 
v_size_3368_ = lean_ctor_get(v_s_3361_, 0);
lean_inc(v_size_3368_);
lean_dec_ref_known(v_s_3361_, 5);
v___y_3364_ = v_size_3368_;
goto v___jp_3363_;
}
else
{
lean_object* v___x_3369_; 
v___x_3369_ = lean_unsigned_to_nat(0u);
v___y_3364_ = v___x_3369_;
goto v___jp_3363_;
}
v___jp_3363_:
{
lean_object* v___x_3365_; lean_object* v___x_3366_; lean_object* v___x_3367_; 
v___x_3365_ = l_Nat_reprFast(v___y_3364_);
v___x_3366_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3366_, 0, v___x_3365_);
v___x_3367_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3367_, 0, v___x_3362_);
lean_ctor_set(v___x_3367_, 1, v___x_3366_);
return v___x_3367_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg(lean_object* v_env_3370_, lean_object* v_as_3371_, size_t v_i_3372_, size_t v_stop_3373_, lean_object* v_b_3374_){
_start:
{
lean_object* v___y_3376_; uint8_t v___x_3380_; 
v___x_3380_ = lean_usize_dec_eq(v_i_3372_, v_stop_3373_);
if (v___x_3380_ == 0)
{
lean_object* v___x_3381_; lean_object* v_fst_3382_; uint8_t v___x_3383_; lean_object* v___x_3384_; uint8_t v___x_3385_; 
v___x_3381_ = lean_array_uget_borrowed(v_as_3371_, v_i_3372_);
v_fst_3382_ = lean_ctor_get(v___x_3381_, 0);
v___x_3383_ = 1;
lean_inc_ref(v_env_3370_);
v___x_3384_ = l_Lean_Environment_setExporting(v_env_3370_, v___x_3383_);
lean_inc(v_fst_3382_);
v___x_3385_ = l_Lean_Environment_contains(v___x_3384_, v_fst_3382_, v___x_3380_);
if (v___x_3385_ == 0)
{
v___y_3376_ = v_b_3374_;
goto v___jp_3375_;
}
else
{
lean_object* v___x_3386_; 
lean_inc(v___x_3381_);
v___x_3386_ = lean_array_push(v_b_3374_, v___x_3381_);
v___y_3376_ = v___x_3386_;
goto v___jp_3375_;
}
}
else
{
lean_dec_ref(v_env_3370_);
return v_b_3374_;
}
v___jp_3375_:
{
size_t v___x_3377_; size_t v___x_3378_; 
v___x_3377_ = ((size_t)1ULL);
v___x_3378_ = lean_usize_add(v_i_3372_, v___x_3377_);
v_i_3372_ = v___x_3378_;
v_b_3374_ = v___y_3376_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg___boxed(lean_object* v_env_3387_, lean_object* v_as_3388_, lean_object* v_i_3389_, lean_object* v_stop_3390_, lean_object* v_b_3391_){
_start:
{
size_t v_i_boxed_3392_; size_t v_stop_boxed_3393_; lean_object* v_res_3394_; 
v_i_boxed_3392_ = lean_unbox_usize(v_i_3389_);
lean_dec(v_i_3389_);
v_stop_boxed_3393_ = lean_unbox_usize(v_stop_3390_);
lean_dec(v_stop_3390_);
v_res_3394_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg(v_env_3387_, v_as_3388_, v_i_boxed_3392_, v_stop_boxed_3393_, v_b_3391_);
lean_dec_ref(v_as_3388_);
return v_res_3394_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__3(lean_object* v_env_3395_, lean_object* v_m_3396_){
_start:
{
lean_object* v___x_3397_; lean_object* v___x_3398_; lean_object* v___y_3400_; lean_object* v___x_3414_; lean_object* v___x_3415_; lean_object* v___y_3417_; lean_object* v___y_3418_; uint8_t v___x_3420_; 
v___x_3397_ = lean_unsigned_to_nat(0u);
v___x_3398_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___lam__2___closed__0));
v___x_3414_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg(v___x_3398_, v_m_3396_);
v___x_3415_ = lean_array_get_size(v___x_3414_);
v___x_3420_ = lean_nat_dec_eq(v___x_3415_, v___x_3397_);
if (v___x_3420_ == 0)
{
lean_object* v___x_3421_; lean_object* v___x_3422_; lean_object* v___y_3424_; uint8_t v___x_3426_; 
v___x_3421_ = lean_unsigned_to_nat(1u);
v___x_3422_ = lean_nat_sub(v___x_3415_, v___x_3421_);
v___x_3426_ = lean_nat_dec_le(v___x_3397_, v___x_3422_);
if (v___x_3426_ == 0)
{
lean_inc(v___x_3422_);
v___y_3424_ = v___x_3422_;
goto v___jp_3423_;
}
else
{
v___y_3424_ = v___x_3397_;
goto v___jp_3423_;
}
v___jp_3423_:
{
uint8_t v___x_3425_; 
v___x_3425_ = lean_nat_dec_le(v___y_3424_, v___x_3422_);
if (v___x_3425_ == 0)
{
lean_dec(v___x_3422_);
lean_inc(v___y_3424_);
v___y_3417_ = v___y_3424_;
v___y_3418_ = v___y_3424_;
goto v___jp_3416_;
}
else
{
v___y_3417_ = v___y_3424_;
v___y_3418_ = v___x_3422_;
goto v___jp_3416_;
}
}
}
else
{
v___y_3400_ = v___x_3414_;
goto v___jp_3399_;
}
v___jp_3399_:
{
lean_object* v___x_3401_; uint8_t v___x_3402_; 
v___x_3401_ = lean_array_get_size(v___y_3400_);
v___x_3402_ = lean_nat_dec_lt(v___x_3397_, v___x_3401_);
if (v___x_3402_ == 0)
{
lean_object* v___x_3403_; 
lean_dec_ref(v_env_3395_);
v___x_3403_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3403_, 0, v___x_3398_);
lean_ctor_set(v___x_3403_, 1, v___x_3398_);
lean_ctor_set(v___x_3403_, 2, v___y_3400_);
return v___x_3403_;
}
else
{
uint8_t v___x_3404_; 
v___x_3404_ = lean_nat_dec_le(v___x_3401_, v___x_3401_);
if (v___x_3404_ == 0)
{
if (v___x_3402_ == 0)
{
lean_object* v___x_3405_; 
lean_dec_ref(v_env_3395_);
v___x_3405_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3405_, 0, v___x_3398_);
lean_ctor_set(v___x_3405_, 1, v___x_3398_);
lean_ctor_set(v___x_3405_, 2, v___y_3400_);
return v___x_3405_;
}
else
{
size_t v___x_3406_; size_t v___x_3407_; lean_object* v___x_3408_; lean_object* v___x_3409_; 
v___x_3406_ = ((size_t)0ULL);
v___x_3407_ = lean_usize_of_nat(v___x_3401_);
v___x_3408_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg(v_env_3395_, v___y_3400_, v___x_3406_, v___x_3407_, v___x_3398_);
lean_inc_ref(v___x_3408_);
v___x_3409_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3409_, 0, v___x_3408_);
lean_ctor_set(v___x_3409_, 1, v___x_3408_);
lean_ctor_set(v___x_3409_, 2, v___y_3400_);
return v___x_3409_;
}
}
else
{
size_t v___x_3410_; size_t v___x_3411_; lean_object* v___x_3412_; lean_object* v___x_3413_; 
v___x_3410_ = ((size_t)0ULL);
v___x_3411_ = lean_usize_of_nat(v___x_3401_);
v___x_3412_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg(v_env_3395_, v___y_3400_, v___x_3410_, v___x_3411_, v___x_3398_);
lean_inc_ref(v___x_3412_);
v___x_3413_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3413_, 0, v___x_3412_);
lean_ctor_set(v___x_3413_, 1, v___x_3412_);
lean_ctor_set(v___x_3413_, 2, v___y_3400_);
return v___x_3413_;
}
}
}
v___jp_3416_:
{
lean_object* v___x_3419_; 
v___x_3419_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg(v___x_3415_, v___x_3414_, v___y_3417_, v___y_3418_);
lean_dec(v___y_3418_);
v___y_3400_ = v___x_3419_;
goto v___jp_3399_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__3___boxed(lean_object* v_env_3427_, lean_object* v_m_3428_){
_start:
{
lean_object* v_res_3429_; 
v_res_3429_ = l_Lean_registerEnumAttributes___redArg___lam__3(v_env_3427_, v_m_3428_);
lean_dec(v_m_3428_);
return v_res_3429_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__4(lean_object* v_s_3430_, lean_object* v_p_3431_){
_start:
{
lean_object* v_fst_3432_; lean_object* v_snd_3433_; lean_object* v___x_3434_; 
v_fst_3432_ = lean_ctor_get(v_p_3431_, 0);
lean_inc(v_fst_3432_);
v_snd_3433_ = lean_ctor_get(v_p_3431_, 1);
lean_inc(v_snd_3433_);
lean_dec_ref(v_p_3431_);
v___x_3434_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_3432_, v_snd_3433_, v_s_3430_);
return v___x_3434_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__6(lean_object* v___x_3435_, lean_object* v_x_3436_, lean_object* v_x_3437_){
_start:
{
lean_object* v___x_3439_; 
v___x_3439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3439_, 0, v___x_3435_);
return v___x_3439_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__6___boxed(lean_object* v___x_3440_, lean_object* v_x_3441_, lean_object* v_x_3442_, lean_object* v___y_3443_){
_start:
{
lean_object* v_res_3444_; 
v_res_3444_ = l_Lean_registerEnumAttributes___redArg___lam__6(v___x_3440_, v_x_3441_, v_x_3442_);
lean_dec_ref(v_x_3442_);
lean_dec_ref(v_x_3441_);
return v_res_3444_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_registerEnumAttributes_spec__3(lean_object* v_as_3445_){
_start:
{
if (lean_obj_tag(v_as_3445_) == 0)
{
lean_object* v___x_3447_; lean_object* v___x_3448_; 
v___x_3447_ = lean_box(0);
v___x_3448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3448_, 0, v___x_3447_);
return v___x_3448_;
}
else
{
lean_object* v_head_3449_; lean_object* v_tail_3450_; lean_object* v___x_3451_; 
v_head_3449_ = lean_ctor_get(v_as_3445_, 0);
lean_inc(v_head_3449_);
v_tail_3450_ = lean_ctor_get(v_as_3445_, 1);
lean_inc(v_tail_3450_);
lean_dec_ref_known(v_as_3445_, 2);
v___x_3451_ = l_Lean_registerBuiltinAttribute(v_head_3449_);
if (lean_obj_tag(v___x_3451_) == 0)
{
lean_dec_ref_known(v___x_3451_, 1);
v_as_3445_ = v_tail_3450_;
goto _start;
}
else
{
lean_dec(v_tail_3450_);
return v___x_3451_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_registerEnumAttributes_spec__3___boxed(lean_object* v_as_3453_, lean_object* v___y_3454_){
_start:
{
lean_object* v_res_3455_; 
v_res_3455_ = l_List_forM___at___00Lean_registerEnumAttributes_spec__3(v_as_3453_);
return v_res_3455_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__1(lean_object* v_validate_3456_, lean_object* v_snd_3457_, lean_object* v_a_3458_, lean_object* v_fst_3459_, lean_object* v_decl_3460_, lean_object* v_stx_3461_, uint8_t v_kind_3462_, lean_object* v___y_3463_, lean_object* v___y_3464_){
_start:
{
lean_object* v___y_3467_; lean_object* v___y_3468_; lean_object* v___y_3503_; lean_object* v___y_3504_; lean_object* v___x_3509_; 
v___x_3509_ = l_Lean_Attribute_Builtin_ensureNoArgs(v_stx_3461_, v___y_3463_, v___y_3464_);
if (lean_obj_tag(v___x_3509_) == 0)
{
uint8_t v___x_3510_; uint8_t v___x_3511_; 
lean_dec_ref_known(v___x_3509_, 1);
v___x_3510_ = 0;
v___x_3511_ = l_Lean_instBEqAttributeKind_beq(v_kind_3462_, v___x_3510_);
if (v___x_3511_ == 0)
{
lean_object* v___x_3512_; 
lean_dec(v_decl_3460_);
lean_dec_ref(v_a_3458_);
lean_dec(v_snd_3457_);
lean_dec_ref(v_validate_3456_);
v___x_3512_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg(v_fst_3459_, v_kind_3462_, v___y_3463_, v___y_3464_);
return v___x_3512_;
}
else
{
v___y_3503_ = v___y_3463_;
v___y_3504_ = v___y_3464_;
goto v___jp_3502_;
}
}
else
{
lean_dec(v_decl_3460_);
lean_dec(v_fst_3459_);
lean_dec_ref(v_a_3458_);
lean_dec(v_snd_3457_);
lean_dec_ref(v_validate_3456_);
return v___x_3509_;
}
v___jp_3466_:
{
lean_object* v___x_3469_; 
lean_inc(v___y_3468_);
lean_inc_ref(v___y_3467_);
lean_inc(v_snd_3457_);
lean_inc(v_decl_3460_);
v___x_3469_ = lean_apply_5(v_validate_3456_, v_decl_3460_, v_snd_3457_, v___y_3467_, v___y_3468_, lean_box(0));
if (lean_obj_tag(v___x_3469_) == 0)
{
lean_object* v___x_3471_; uint8_t v_isShared_3472_; uint8_t v_isSharedCheck_3500_; 
v_isSharedCheck_3500_ = !lean_is_exclusive(v___x_3469_);
if (v_isSharedCheck_3500_ == 0)
{
lean_object* v_unused_3501_; 
v_unused_3501_ = lean_ctor_get(v___x_3469_, 0);
lean_dec(v_unused_3501_);
v___x_3471_ = v___x_3469_;
v_isShared_3472_ = v_isSharedCheck_3500_;
goto v_resetjp_3470_;
}
else
{
lean_dec(v___x_3469_);
v___x_3471_ = lean_box(0);
v_isShared_3472_ = v_isSharedCheck_3500_;
goto v_resetjp_3470_;
}
v_resetjp_3470_:
{
lean_object* v___x_3473_; lean_object* v_toEnvExtension_3474_; lean_object* v_env_3475_; lean_object* v_nextMacroScope_3476_; lean_object* v_ngen_3477_; lean_object* v_auxDeclNGen_3478_; lean_object* v_traceState_3479_; lean_object* v_messages_3480_; lean_object* v_infoState_3481_; lean_object* v_snapshotTasks_3482_; lean_object* v___x_3484_; uint8_t v_isShared_3485_; uint8_t v_isSharedCheck_3498_; 
v___x_3473_ = lean_st_ref_take(v___y_3468_);
v_toEnvExtension_3474_ = lean_ctor_get(v_a_3458_, 0);
v_env_3475_ = lean_ctor_get(v___x_3473_, 0);
v_nextMacroScope_3476_ = lean_ctor_get(v___x_3473_, 1);
v_ngen_3477_ = lean_ctor_get(v___x_3473_, 2);
v_auxDeclNGen_3478_ = lean_ctor_get(v___x_3473_, 3);
v_traceState_3479_ = lean_ctor_get(v___x_3473_, 4);
v_messages_3480_ = lean_ctor_get(v___x_3473_, 6);
v_infoState_3481_ = lean_ctor_get(v___x_3473_, 7);
v_snapshotTasks_3482_ = lean_ctor_get(v___x_3473_, 8);
v_isSharedCheck_3498_ = !lean_is_exclusive(v___x_3473_);
if (v_isSharedCheck_3498_ == 0)
{
lean_object* v_unused_3499_; 
v_unused_3499_ = lean_ctor_get(v___x_3473_, 5);
lean_dec(v_unused_3499_);
v___x_3484_ = v___x_3473_;
v_isShared_3485_ = v_isSharedCheck_3498_;
goto v_resetjp_3483_;
}
else
{
lean_inc(v_snapshotTasks_3482_);
lean_inc(v_infoState_3481_);
lean_inc(v_messages_3480_);
lean_inc(v_traceState_3479_);
lean_inc(v_auxDeclNGen_3478_);
lean_inc(v_ngen_3477_);
lean_inc(v_nextMacroScope_3476_);
lean_inc(v_env_3475_);
lean_dec(v___x_3473_);
v___x_3484_ = lean_box(0);
v_isShared_3485_ = v_isSharedCheck_3498_;
goto v_resetjp_3483_;
}
v_resetjp_3483_:
{
lean_object* v_asyncMode_3486_; lean_object* v___x_3487_; lean_object* v___x_3488_; lean_object* v___x_3489_; lean_object* v___x_3491_; 
v_asyncMode_3486_ = lean_ctor_get(v_toEnvExtension_3474_, 2);
lean_inc(v_asyncMode_3486_);
lean_inc(v_decl_3460_);
v___x_3487_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3487_, 0, v_decl_3460_);
lean_ctor_set(v___x_3487_, 1, v_snd_3457_);
v___x_3488_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_a_3458_, v_env_3475_, v___x_3487_, v_asyncMode_3486_, v_decl_3460_);
lean_dec(v_asyncMode_3486_);
v___x_3489_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2);
if (v_isShared_3485_ == 0)
{
lean_ctor_set(v___x_3484_, 5, v___x_3489_);
lean_ctor_set(v___x_3484_, 0, v___x_3488_);
v___x_3491_ = v___x_3484_;
goto v_reusejp_3490_;
}
else
{
lean_object* v_reuseFailAlloc_3497_; 
v_reuseFailAlloc_3497_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3497_, 0, v___x_3488_);
lean_ctor_set(v_reuseFailAlloc_3497_, 1, v_nextMacroScope_3476_);
lean_ctor_set(v_reuseFailAlloc_3497_, 2, v_ngen_3477_);
lean_ctor_set(v_reuseFailAlloc_3497_, 3, v_auxDeclNGen_3478_);
lean_ctor_set(v_reuseFailAlloc_3497_, 4, v_traceState_3479_);
lean_ctor_set(v_reuseFailAlloc_3497_, 5, v___x_3489_);
lean_ctor_set(v_reuseFailAlloc_3497_, 6, v_messages_3480_);
lean_ctor_set(v_reuseFailAlloc_3497_, 7, v_infoState_3481_);
lean_ctor_set(v_reuseFailAlloc_3497_, 8, v_snapshotTasks_3482_);
v___x_3491_ = v_reuseFailAlloc_3497_;
goto v_reusejp_3490_;
}
v_reusejp_3490_:
{
lean_object* v___x_3492_; lean_object* v___x_3493_; lean_object* v___x_3495_; 
v___x_3492_ = lean_st_ref_set(v___y_3468_, v___x_3491_);
v___x_3493_ = lean_box(0);
if (v_isShared_3472_ == 0)
{
lean_ctor_set(v___x_3471_, 0, v___x_3493_);
v___x_3495_ = v___x_3471_;
goto v_reusejp_3494_;
}
else
{
lean_object* v_reuseFailAlloc_3496_; 
v_reuseFailAlloc_3496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3496_, 0, v___x_3493_);
v___x_3495_ = v_reuseFailAlloc_3496_;
goto v_reusejp_3494_;
}
v_reusejp_3494_:
{
return v___x_3495_;
}
}
}
}
}
else
{
lean_dec(v_decl_3460_);
lean_dec_ref(v_a_3458_);
lean_dec(v_snd_3457_);
return v___x_3469_;
}
}
v___jp_3502_:
{
lean_object* v___x_3505_; lean_object* v_env_3506_; lean_object* v___x_3507_; 
v___x_3505_ = lean_st_ref_get(v___y_3504_);
v_env_3506_ = lean_ctor_get(v___x_3505_, 0);
lean_inc_ref(v_env_3506_);
lean_dec(v___x_3505_);
v___x_3507_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3506_, v_decl_3460_);
lean_dec_ref(v_env_3506_);
if (lean_obj_tag(v___x_3507_) == 0)
{
lean_dec(v_fst_3459_);
v___y_3467_ = v___y_3503_;
v___y_3468_ = v___y_3504_;
goto v___jp_3466_;
}
else
{
lean_object* v___x_3508_; 
lean_dec_ref_known(v___x_3507_, 1);
lean_dec_ref(v_a_3458_);
lean_dec(v_snd_3457_);
lean_dec_ref(v_validate_3456_);
v___x_3508_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg(v_fst_3459_, v_decl_3460_, v___y_3503_, v___y_3504_);
return v___x_3508_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__1___boxed(lean_object* v_validate_3513_, lean_object* v_snd_3514_, lean_object* v_a_3515_, lean_object* v_fst_3516_, lean_object* v_decl_3517_, lean_object* v_stx_3518_, lean_object* v_kind_3519_, lean_object* v___y_3520_, lean_object* v___y_3521_, lean_object* v___y_3522_){
_start:
{
uint8_t v_kind_boxed_3523_; lean_object* v_res_3524_; 
v_kind_boxed_3523_ = lean_unbox(v_kind_3519_);
v_res_3524_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__1(v_validate_3513_, v_snd_3514_, v_a_3515_, v_fst_3516_, v_decl_3517_, v_stx_3518_, v_kind_boxed_3523_, v___y_3520_, v___y_3521_);
lean_dec(v___y_3521_);
lean_dec_ref(v___y_3520_);
return v_res_3524_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__0(lean_object* v_fst_3525_, lean_object* v_decl_3526_, lean_object* v___y_3527_, lean_object* v___y_3528_){
_start:
{
lean_object* v___x_3530_; lean_object* v___x_3531_; lean_object* v___x_3532_; lean_object* v___x_3533_; lean_object* v___x_3534_; lean_object* v___x_3535_; 
v___x_3530_ = lean_obj_once(&l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1, &l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1_once, _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1);
v___x_3531_ = l_Lean_MessageData_ofName(v_fst_3525_);
v___x_3532_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3532_, 0, v___x_3530_);
lean_ctor_set(v___x_3532_, 1, v___x_3531_);
v___x_3533_ = lean_obj_once(&l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3, &l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3_once, _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3);
v___x_3534_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3534_, 0, v___x_3532_);
lean_ctor_set(v___x_3534_, 1, v___x_3533_);
v___x_3535_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_3534_, v___y_3527_, v___y_3528_);
return v___x_3535_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__0___boxed(lean_object* v_fst_3536_, lean_object* v_decl_3537_, lean_object* v___y_3538_, lean_object* v___y_3539_, lean_object* v___y_3540_){
_start:
{
lean_object* v_res_3541_; 
v_res_3541_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__0(v_fst_3536_, v_decl_3537_, v___y_3538_, v___y_3539_);
lean_dec(v___y_3539_);
lean_dec_ref(v___y_3538_);
lean_dec(v_decl_3537_);
return v_res_3541_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg(lean_object* v_validate_3542_, lean_object* v_a_3543_, lean_object* v_ref_3544_, uint8_t v_applicationTime_3545_, lean_object* v_a_3546_, lean_object* v_a_3547_){
_start:
{
if (lean_obj_tag(v_a_3546_) == 0)
{
lean_object* v___x_3548_; 
lean_dec(v_ref_3544_);
lean_dec_ref(v_a_3543_);
lean_dec_ref(v_validate_3542_);
v___x_3548_ = l_List_reverse___redArg(v_a_3547_);
return v___x_3548_;
}
else
{
lean_object* v_head_3549_; lean_object* v_snd_3550_; lean_object* v_tail_3551_; lean_object* v___x_3553_; uint8_t v_isShared_3554_; uint8_t v_isSharedCheck_3566_; 
v_head_3549_ = lean_ctor_get(v_a_3546_, 0);
lean_inc(v_head_3549_);
v_snd_3550_ = lean_ctor_get(v_head_3549_, 1);
lean_inc(v_snd_3550_);
v_tail_3551_ = lean_ctor_get(v_a_3546_, 1);
v_isSharedCheck_3566_ = !lean_is_exclusive(v_a_3546_);
if (v_isSharedCheck_3566_ == 0)
{
lean_object* v_unused_3567_; 
v_unused_3567_ = lean_ctor_get(v_a_3546_, 0);
lean_dec(v_unused_3567_);
v___x_3553_ = v_a_3546_;
v_isShared_3554_ = v_isSharedCheck_3566_;
goto v_resetjp_3552_;
}
else
{
lean_inc(v_tail_3551_);
lean_dec(v_a_3546_);
v___x_3553_ = lean_box(0);
v_isShared_3554_ = v_isSharedCheck_3566_;
goto v_resetjp_3552_;
}
v_resetjp_3552_:
{
lean_object* v_fst_3555_; lean_object* v_fst_3556_; lean_object* v_snd_3557_; lean_object* v___f_3558_; lean_object* v___f_3559_; lean_object* v___x_3560_; lean_object* v___x_3561_; lean_object* v___x_3563_; 
v_fst_3555_ = lean_ctor_get(v_head_3549_, 0);
lean_inc_n(v_fst_3555_, 3);
lean_dec(v_head_3549_);
v_fst_3556_ = lean_ctor_get(v_snd_3550_, 0);
lean_inc(v_fst_3556_);
v_snd_3557_ = lean_ctor_get(v_snd_3550_, 1);
lean_inc(v_snd_3557_);
lean_dec(v_snd_3550_);
v___f_3558_ = lean_alloc_closure((void*)(l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__0___boxed), 5, 1);
lean_closure_set(v___f_3558_, 0, v_fst_3555_);
lean_inc_ref(v_a_3543_);
lean_inc_ref(v_validate_3542_);
v___f_3559_ = lean_alloc_closure((void*)(l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__1___boxed), 10, 4);
lean_closure_set(v___f_3559_, 0, v_validate_3542_);
lean_closure_set(v___f_3559_, 1, v_snd_3557_);
lean_closure_set(v___f_3559_, 2, v_a_3543_);
lean_closure_set(v___f_3559_, 3, v_fst_3555_);
lean_inc(v_ref_3544_);
v___x_3560_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_3560_, 0, v_ref_3544_);
lean_ctor_set(v___x_3560_, 1, v_fst_3555_);
lean_ctor_set(v___x_3560_, 2, v_fst_3556_);
lean_ctor_set_uint8(v___x_3560_, sizeof(void*)*3, v_applicationTime_3545_);
v___x_3561_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3561_, 0, v___x_3560_);
lean_ctor_set(v___x_3561_, 1, v___f_3559_);
lean_ctor_set(v___x_3561_, 2, v___f_3558_);
if (v_isShared_3554_ == 0)
{
lean_ctor_set(v___x_3553_, 1, v_a_3547_);
lean_ctor_set(v___x_3553_, 0, v___x_3561_);
v___x_3563_ = v___x_3553_;
goto v_reusejp_3562_;
}
else
{
lean_object* v_reuseFailAlloc_3565_; 
v_reuseFailAlloc_3565_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3565_, 0, v___x_3561_);
lean_ctor_set(v_reuseFailAlloc_3565_, 1, v_a_3547_);
v___x_3563_ = v_reuseFailAlloc_3565_;
goto v_reusejp_3562_;
}
v_reusejp_3562_:
{
v_a_3546_ = v_tail_3551_;
v_a_3547_ = v___x_3563_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___boxed(lean_object* v_validate_3568_, lean_object* v_a_3569_, lean_object* v_ref_3570_, lean_object* v_applicationTime_3571_, lean_object* v_a_3572_, lean_object* v_a_3573_){
_start:
{
uint8_t v_applicationTime_boxed_3574_; lean_object* v_res_3575_; 
v_applicationTime_boxed_3574_ = lean_unbox(v_applicationTime_3571_);
v_res_3575_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg(v_validate_3568_, v_a_3569_, v_ref_3570_, v_applicationTime_boxed_3574_, v_a_3572_, v_a_3573_);
return v_res_3575_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg(lean_object* v_attrDescrs_3589_, lean_object* v_validate_3590_, uint8_t v_applicationTime_3591_, lean_object* v_ref_3592_){
_start:
{
lean_object* v___f_3594_; lean_object* v___f_3595_; lean_object* v___f_3596_; lean_object* v___f_3597_; lean_object* v___f_3598_; lean_object* v___f_3599_; lean_object* v___x_3600_; lean_object* v___x_3601_; lean_object* v___x_3602_; lean_object* v___x_3603_; lean_object* v___x_3604_; 
v___f_3594_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__0));
v___f_3595_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__2));
v___f_3596_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__3));
v___f_3597_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__4));
v___f_3598_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__5));
v___f_3599_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__6));
v___x_3600_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__7));
v___x_3601_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__8));
lean_inc(v_ref_3592_);
v___x_3602_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_3602_, 0, v_ref_3592_);
lean_ctor_set(v___x_3602_, 1, v___f_3598_);
lean_ctor_set(v___x_3602_, 2, v___f_3599_);
lean_ctor_set(v___x_3602_, 3, v___f_3597_);
lean_ctor_set(v___x_3602_, 4, v___f_3596_);
lean_ctor_set(v___x_3602_, 5, v___f_3595_);
lean_ctor_set(v___x_3602_, 6, v___x_3600_);
lean_ctor_set(v___x_3602_, 7, v___x_3601_);
v___x_3603_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3603_, 0, v___x_3602_);
lean_ctor_set(v___x_3603_, 1, v___f_3594_);
v___x_3604_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_3603_);
if (lean_obj_tag(v___x_3604_) == 0)
{
lean_object* v_a_3605_; lean_object* v___x_3606_; lean_object* v___x_3607_; lean_object* v___x_3608_; 
v_a_3605_ = lean_ctor_get(v___x_3604_, 0);
lean_inc_n(v_a_3605_, 2);
lean_dec_ref_known(v___x_3604_, 1);
v___x_3606_ = lean_box(0);
v___x_3607_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg(v_validate_3590_, v_a_3605_, v_ref_3592_, v_applicationTime_3591_, v_attrDescrs_3589_, v___x_3606_);
lean_inc(v___x_3607_);
v___x_3608_ = l_List_forM___at___00Lean_registerEnumAttributes_spec__3(v___x_3607_);
if (lean_obj_tag(v___x_3608_) == 0)
{
lean_object* v___x_3610_; uint8_t v_isShared_3611_; uint8_t v_isSharedCheck_3616_; 
v_isSharedCheck_3616_ = !lean_is_exclusive(v___x_3608_);
if (v_isSharedCheck_3616_ == 0)
{
lean_object* v_unused_3617_; 
v_unused_3617_ = lean_ctor_get(v___x_3608_, 0);
lean_dec(v_unused_3617_);
v___x_3610_ = v___x_3608_;
v_isShared_3611_ = v_isSharedCheck_3616_;
goto v_resetjp_3609_;
}
else
{
lean_dec(v___x_3608_);
v___x_3610_ = lean_box(0);
v_isShared_3611_ = v_isSharedCheck_3616_;
goto v_resetjp_3609_;
}
v_resetjp_3609_:
{
lean_object* v___x_3612_; lean_object* v___x_3614_; 
v___x_3612_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3612_, 0, v___x_3607_);
lean_ctor_set(v___x_3612_, 1, v_a_3605_);
if (v_isShared_3611_ == 0)
{
lean_ctor_set(v___x_3610_, 0, v___x_3612_);
v___x_3614_ = v___x_3610_;
goto v_reusejp_3613_;
}
else
{
lean_object* v_reuseFailAlloc_3615_; 
v_reuseFailAlloc_3615_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3615_, 0, v___x_3612_);
v___x_3614_ = v_reuseFailAlloc_3615_;
goto v_reusejp_3613_;
}
v_reusejp_3613_:
{
return v___x_3614_;
}
}
}
else
{
lean_object* v_a_3618_; lean_object* v___x_3620_; uint8_t v_isShared_3621_; uint8_t v_isSharedCheck_3625_; 
lean_dec(v___x_3607_);
lean_dec(v_a_3605_);
v_a_3618_ = lean_ctor_get(v___x_3608_, 0);
v_isSharedCheck_3625_ = !lean_is_exclusive(v___x_3608_);
if (v_isSharedCheck_3625_ == 0)
{
v___x_3620_ = v___x_3608_;
v_isShared_3621_ = v_isSharedCheck_3625_;
goto v_resetjp_3619_;
}
else
{
lean_inc(v_a_3618_);
lean_dec(v___x_3608_);
v___x_3620_ = lean_box(0);
v_isShared_3621_ = v_isSharedCheck_3625_;
goto v_resetjp_3619_;
}
v_resetjp_3619_:
{
lean_object* v___x_3623_; 
if (v_isShared_3621_ == 0)
{
v___x_3623_ = v___x_3620_;
goto v_reusejp_3622_;
}
else
{
lean_object* v_reuseFailAlloc_3624_; 
v_reuseFailAlloc_3624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3624_, 0, v_a_3618_);
v___x_3623_ = v_reuseFailAlloc_3624_;
goto v_reusejp_3622_;
}
v_reusejp_3622_:
{
return v___x_3623_;
}
}
}
}
else
{
lean_object* v_a_3626_; lean_object* v___x_3628_; uint8_t v_isShared_3629_; uint8_t v_isSharedCheck_3633_; 
lean_dec(v_ref_3592_);
lean_dec_ref(v_validate_3590_);
lean_dec(v_attrDescrs_3589_);
v_a_3626_ = lean_ctor_get(v___x_3604_, 0);
v_isSharedCheck_3633_ = !lean_is_exclusive(v___x_3604_);
if (v_isSharedCheck_3633_ == 0)
{
v___x_3628_ = v___x_3604_;
v_isShared_3629_ = v_isSharedCheck_3633_;
goto v_resetjp_3627_;
}
else
{
lean_inc(v_a_3626_);
lean_dec(v___x_3604_);
v___x_3628_ = lean_box(0);
v_isShared_3629_ = v_isSharedCheck_3633_;
goto v_resetjp_3627_;
}
v_resetjp_3627_:
{
lean_object* v___x_3631_; 
if (v_isShared_3629_ == 0)
{
v___x_3631_ = v___x_3628_;
goto v_reusejp_3630_;
}
else
{
lean_object* v_reuseFailAlloc_3632_; 
v_reuseFailAlloc_3632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3632_, 0, v_a_3626_);
v___x_3631_ = v_reuseFailAlloc_3632_;
goto v_reusejp_3630_;
}
v_reusejp_3630_:
{
return v___x_3631_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___boxed(lean_object* v_attrDescrs_3634_, lean_object* v_validate_3635_, lean_object* v_applicationTime_3636_, lean_object* v_ref_3637_, lean_object* v_a_3638_){
_start:
{
uint8_t v_applicationTime_boxed_3639_; lean_object* v_res_3640_; 
v_applicationTime_boxed_3639_ = lean_unbox(v_applicationTime_3636_);
v_res_3640_ = l_Lean_registerEnumAttributes___redArg(v_attrDescrs_3634_, v_validate_3635_, v_applicationTime_boxed_3639_, v_ref_3637_);
return v_res_3640_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes(lean_object* v_00_u03b1_3641_, lean_object* v_attrDescrs_3642_, lean_object* v_validate_3643_, uint8_t v_applicationTime_3644_, lean_object* v_ref_3645_){
_start:
{
lean_object* v___x_3647_; 
v___x_3647_ = l_Lean_registerEnumAttributes___redArg(v_attrDescrs_3642_, v_validate_3643_, v_applicationTime_3644_, v_ref_3645_);
return v___x_3647_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___boxed(lean_object* v_00_u03b1_3648_, lean_object* v_attrDescrs_3649_, lean_object* v_validate_3650_, lean_object* v_applicationTime_3651_, lean_object* v_ref_3652_, lean_object* v_a_3653_){
_start:
{
uint8_t v_applicationTime_boxed_3654_; lean_object* v_res_3655_; 
v_applicationTime_boxed_3654_ = lean_unbox(v_applicationTime_3651_);
v_res_3655_ = l_Lean_registerEnumAttributes(v_00_u03b1_3648_, v_attrDescrs_3649_, v_validate_3650_, v_applicationTime_boxed_3654_, v_ref_3652_);
return v_res_3655_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0(lean_object* v_00_u03b1_3656_, lean_object* v_env_3657_, lean_object* v_as_3658_, size_t v_i_3659_, size_t v_stop_3660_, lean_object* v_b_3661_){
_start:
{
lean_object* v___x_3662_; 
v___x_3662_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg(v_env_3657_, v_as_3658_, v_i_3659_, v_stop_3660_, v_b_3661_);
return v___x_3662_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___boxed(lean_object* v_00_u03b1_3663_, lean_object* v_env_3664_, lean_object* v_as_3665_, lean_object* v_i_3666_, lean_object* v_stop_3667_, lean_object* v_b_3668_){
_start:
{
size_t v_i_boxed_3669_; size_t v_stop_boxed_3670_; lean_object* v_res_3671_; 
v_i_boxed_3669_ = lean_unbox_usize(v_i_3666_);
lean_dec(v_i_3666_);
v_stop_boxed_3670_ = lean_unbox_usize(v_stop_3667_);
lean_dec(v_stop_3667_);
v_res_3671_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0(v_00_u03b1_3663_, v_env_3664_, v_as_3665_, v_i_boxed_3669_, v_stop_boxed_3670_, v_b_3668_);
lean_dec_ref(v_as_3665_);
return v_res_3671_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerEnumAttributes_spec__1(lean_object* v_00_u03b1_3672_, lean_object* v_newState_3673_, lean_object* v_x_3674_, lean_object* v_x_3675_){
_start:
{
lean_object* v___x_3676_; 
v___x_3676_ = l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___redArg(v_newState_3673_, v_x_3674_, v_x_3675_);
return v___x_3676_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___boxed(lean_object* v_00_u03b1_3677_, lean_object* v_newState_3678_, lean_object* v_x_3679_, lean_object* v_x_3680_){
_start:
{
lean_object* v_res_3681_; 
v_res_3681_ = l_List_foldl___at___00Lean_registerEnumAttributes_spec__1(v_00_u03b1_3677_, v_newState_3678_, v_x_3679_, v_x_3680_);
lean_dec(v_newState_3678_);
return v_res_3681_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2(lean_object* v_00_u03b1_3682_, lean_object* v_validate_3683_, lean_object* v_a_3684_, lean_object* v_ref_3685_, uint8_t v_applicationTime_3686_, lean_object* v_a_3687_, lean_object* v_a_3688_){
_start:
{
lean_object* v___x_3689_; 
v___x_3689_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg(v_validate_3683_, v_a_3684_, v_ref_3685_, v_applicationTime_3686_, v_a_3687_, v_a_3688_);
return v___x_3689_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___boxed(lean_object* v_00_u03b1_3690_, lean_object* v_validate_3691_, lean_object* v_a_3692_, lean_object* v_ref_3693_, lean_object* v_applicationTime_3694_, lean_object* v_a_3695_, lean_object* v_a_3696_){
_start:
{
uint8_t v_applicationTime_boxed_3697_; lean_object* v_res_3698_; 
v_applicationTime_boxed_3697_ = lean_unbox(v_applicationTime_3694_);
v_res_3698_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2(v_00_u03b1_3690_, v_validate_3691_, v_a_3692_, v_ref_3693_, v_applicationTime_boxed_3697_, v_a_3695_, v_a_3696_);
return v_res_3698_;
}
}
LEAN_EXPORT lean_object* l_Lean_EnumAttributes_getValue___redArg(lean_object* v_inst_3699_, lean_object* v_attr_3700_, lean_object* v_env_3701_, lean_object* v_decl_3702_){
_start:
{
lean_object* v___x_3703_; lean_object* v___x_3704_; 
v___x_3703_ = lean_box(1);
v___x_3704_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3701_, v_decl_3702_);
if (lean_obj_tag(v___x_3704_) == 0)
{
lean_object* v_ext_3705_; lean_object* v_toEnvExtension_3706_; lean_object* v_asyncMode_3707_; lean_object* v___x_3708_; lean_object* v___x_3709_; 
lean_dec(v_inst_3699_);
v_ext_3705_ = lean_ctor_get(v_attr_3700_, 1);
lean_inc_ref(v_ext_3705_);
lean_dec_ref(v_attr_3700_);
v_toEnvExtension_3706_ = lean_ctor_get(v_ext_3705_, 0);
v_asyncMode_3707_ = lean_ctor_get(v_toEnvExtension_3706_, 2);
lean_inc(v_asyncMode_3707_);
lean_inc(v_decl_3702_);
v___x_3708_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3703_, v_ext_3705_, v_env_3701_, v_asyncMode_3707_, v_decl_3702_);
lean_dec(v_asyncMode_3707_);
lean_dec_ref(v_ext_3705_);
v___x_3709_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_3708_, v_decl_3702_);
lean_dec(v_decl_3702_);
lean_dec(v___x_3708_);
return v___x_3709_;
}
else
{
lean_object* v_val_3710_; lean_object* v_ext_3711_; lean_object* v___x_3713_; uint8_t v_isShared_3714_; uint8_t v_isSharedCheck_3741_; 
v_val_3710_ = lean_ctor_get(v___x_3704_, 0);
lean_inc(v_val_3710_);
lean_dec_ref_known(v___x_3704_, 1);
v_ext_3711_ = lean_ctor_get(v_attr_3700_, 1);
v_isSharedCheck_3741_ = !lean_is_exclusive(v_attr_3700_);
if (v_isSharedCheck_3741_ == 0)
{
lean_object* v_unused_3742_; 
v_unused_3742_ = lean_ctor_get(v_attr_3700_, 0);
lean_dec(v_unused_3742_);
v___x_3713_ = v_attr_3700_;
v_isShared_3714_ = v_isSharedCheck_3741_;
goto v_resetjp_3712_;
}
else
{
lean_inc(v_ext_3711_);
lean_dec(v_attr_3700_);
v___x_3713_ = lean_box(0);
v_isShared_3714_ = v_isSharedCheck_3741_;
goto v_resetjp_3712_;
}
v_resetjp_3712_:
{
uint8_t v___x_3715_; lean_object* v___x_3716_; lean_object* v___x_3717_; lean_object* v___x_3718_; uint8_t v___x_3719_; 
v___x_3715_ = 0;
v___x_3716_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_3703_, v_ext_3711_, v_env_3701_, v_val_3710_, v___x_3715_);
lean_dec(v_val_3710_);
lean_dec_ref(v_env_3701_);
lean_dec_ref(v_ext_3711_);
v___x_3717_ = lean_unsigned_to_nat(0u);
v___x_3718_ = lean_array_get_size(v___x_3716_);
v___x_3719_ = lean_nat_dec_lt(v___x_3717_, v___x_3718_);
if (v___x_3719_ == 0)
{
lean_object* v___x_3720_; 
lean_dec_ref(v___x_3716_);
lean_del_object(v___x_3713_);
lean_dec(v_decl_3702_);
lean_dec(v_inst_3699_);
v___x_3720_ = lean_box(0);
return v___x_3720_;
}
else
{
lean_object* v___x_3721_; lean_object* v___x_3722_; uint8_t v___x_3723_; 
v___x_3721_ = lean_unsigned_to_nat(1u);
v___x_3722_ = lean_nat_sub(v___x_3718_, v___x_3721_);
v___x_3723_ = lean_nat_dec_le(v___x_3717_, v___x_3722_);
if (v___x_3723_ == 0)
{
lean_object* v___x_3724_; 
lean_dec(v___x_3722_);
lean_dec_ref(v___x_3716_);
lean_del_object(v___x_3713_);
lean_dec(v_decl_3702_);
lean_dec(v_inst_3699_);
v___x_3724_ = lean_box(0);
return v___x_3724_;
}
else
{
lean_object* v___f_3725_; lean_object* v___x_3727_; 
v___f_3725_ = ((lean_object*)(l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__1));
if (v_isShared_3714_ == 0)
{
lean_ctor_set(v___x_3713_, 1, v_inst_3699_);
lean_ctor_set(v___x_3713_, 0, v_decl_3702_);
v___x_3727_ = v___x_3713_;
goto v_reusejp_3726_;
}
else
{
lean_object* v_reuseFailAlloc_3740_; 
v_reuseFailAlloc_3740_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3740_, 0, v_decl_3702_);
lean_ctor_set(v_reuseFailAlloc_3740_, 1, v_inst_3699_);
v___x_3727_ = v_reuseFailAlloc_3740_;
goto v_reusejp_3726_;
}
v_reusejp_3726_:
{
lean_object* v___x_3728_; lean_object* v___x_3729_; 
v___x_3728_ = ((lean_object*)(l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__2));
v___x_3729_ = l_Array_binSearchAux___redArg(v___f_3725_, v___x_3728_, v___x_3716_, v___x_3727_, v___x_3717_, v___x_3722_);
lean_dec_ref(v___x_3716_);
if (lean_obj_tag(v___x_3729_) == 0)
{
lean_object* v___x_3730_; 
v___x_3730_ = lean_box(0);
return v___x_3730_;
}
else
{
lean_object* v_val_3731_; lean_object* v___x_3733_; uint8_t v_isShared_3734_; uint8_t v_isSharedCheck_3739_; 
v_val_3731_ = lean_ctor_get(v___x_3729_, 0);
v_isSharedCheck_3739_ = !lean_is_exclusive(v___x_3729_);
if (v_isSharedCheck_3739_ == 0)
{
v___x_3733_ = v___x_3729_;
v_isShared_3734_ = v_isSharedCheck_3739_;
goto v_resetjp_3732_;
}
else
{
lean_inc(v_val_3731_);
lean_dec(v___x_3729_);
v___x_3733_ = lean_box(0);
v_isShared_3734_ = v_isSharedCheck_3739_;
goto v_resetjp_3732_;
}
v_resetjp_3732_:
{
lean_object* v_snd_3735_; lean_object* v___x_3737_; 
v_snd_3735_ = lean_ctor_get(v_val_3731_, 1);
lean_inc(v_snd_3735_);
lean_dec(v_val_3731_);
if (v_isShared_3734_ == 0)
{
lean_ctor_set(v___x_3733_, 0, v_snd_3735_);
v___x_3737_ = v___x_3733_;
goto v_reusejp_3736_;
}
else
{
lean_object* v_reuseFailAlloc_3738_; 
v_reuseFailAlloc_3738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3738_, 0, v_snd_3735_);
v___x_3737_ = v_reuseFailAlloc_3738_;
goto v_reusejp_3736_;
}
v_reusejp_3736_:
{
return v___x_3737_;
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
LEAN_EXPORT lean_object* l_Lean_EnumAttributes_getValue(lean_object* v_00_u03b1_3743_, lean_object* v_inst_3744_, lean_object* v_attr_3745_, lean_object* v_env_3746_, lean_object* v_decl_3747_){
_start:
{
lean_object* v___x_3748_; 
v___x_3748_ = l_Lean_EnumAttributes_getValue___redArg(v_inst_3744_, v_attr_3745_, v_env_3746_, v_decl_3747_);
return v___x_3748_;
}
}
LEAN_EXPORT lean_object* l_Lean_EnumAttributes_setValue___redArg(lean_object* v_attrs_3757_, lean_object* v_env_3758_, lean_object* v_decl_3759_, lean_object* v_val_3760_){
_start:
{
lean_object* v_ext_3761_; lean_object* v___x_3763_; uint8_t v_isShared_3764_; uint8_t v_isSharedCheck_3825_; 
v_ext_3761_ = lean_ctor_get(v_attrs_3757_, 1);
v_isSharedCheck_3825_ = !lean_is_exclusive(v_attrs_3757_);
if (v_isSharedCheck_3825_ == 0)
{
lean_object* v_unused_3826_; 
v_unused_3826_ = lean_ctor_get(v_attrs_3757_, 0);
lean_dec(v_unused_3826_);
v___x_3763_ = v_attrs_3757_;
v_isShared_3764_ = v_isSharedCheck_3825_;
goto v_resetjp_3762_;
}
else
{
lean_inc(v_ext_3761_);
lean_dec(v_attrs_3757_);
v___x_3763_ = lean_box(0);
v_isShared_3764_ = v_isSharedCheck_3825_;
goto v_resetjp_3762_;
}
v_resetjp_3762_:
{
lean_object* v_toEnvExtension_3765_; lean_object* v_name_3766_; lean_object* v___x_3767_; uint8_t v___x_3768_; lean_object* v___x_3769_; lean_object* v___x_3770_; lean_object* v___x_3771_; lean_object* v___x_3772_; lean_object* v___x_3773_; lean_object* v___x_3774_; lean_object* v___x_3775_; lean_object* v_pfx_3776_; lean_object* v___x_3777_; 
v_toEnvExtension_3765_ = lean_ctor_get(v_ext_3761_, 0);
v_name_3766_ = lean_ctor_get(v_ext_3761_, 1);
v___x_3767_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__0));
v___x_3768_ = 1;
lean_inc(v_name_3766_);
v___x_3769_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_3766_, v___x_3768_);
v___x_3770_ = lean_string_append(v___x_3767_, v___x_3769_);
lean_dec_ref(v___x_3769_);
v___x_3771_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__1));
v___x_3772_ = lean_string_append(v___x_3770_, v___x_3771_);
lean_inc(v_decl_3759_);
v___x_3773_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_decl_3759_, v___x_3768_);
v___x_3774_ = lean_string_append(v___x_3772_, v___x_3773_);
lean_dec_ref(v___x_3773_);
v___x_3775_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__4));
v_pfx_3776_ = lean_string_append(v___x_3774_, v___x_3775_);
v___x_3777_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3758_, v_decl_3759_);
if (lean_obj_tag(v___x_3777_) == 0)
{
lean_object* v_asyncMode_3778_; uint8_t v___x_3785_; 
v_asyncMode_3778_ = lean_ctor_get(v_toEnvExtension_3765_, 2);
lean_inc(v_asyncMode_3778_);
lean_inc(v_decl_3759_);
lean_inc_ref(v_env_3758_);
v___x_3785_ = l_Lean_EnvExtension_asyncMayModify___redArg(v_env_3758_, v_decl_3759_, v_asyncMode_3778_);
if (v___x_3785_ == 0)
{
lean_object* v___x_3786_; lean_object* v___x_3787_; lean_object* v___y_3789_; lean_object* v___x_3793_; 
lean_dec(v_asyncMode_3778_);
lean_del_object(v___x_3763_);
lean_dec_ref(v_ext_3761_);
lean_dec(v_val_3760_);
lean_dec(v_decl_3759_);
v___x_3786_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__2));
v___x_3787_ = lean_string_append(v_pfx_3776_, v___x_3786_);
v___x_3793_ = l_Lean_Environment_asyncPrefix_x3f(v_env_3758_);
if (lean_obj_tag(v___x_3793_) == 0)
{
lean_object* v___x_3794_; 
v___x_3794_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__3));
v___y_3789_ = v___x_3794_;
goto v___jp_3788_;
}
else
{
lean_object* v_val_3795_; lean_object* v___x_3796_; lean_object* v___x_3797_; lean_object* v___x_3798_; lean_object* v___x_3799_; lean_object* v___x_3800_; lean_object* v___x_3801_; 
v_val_3795_ = lean_ctor_get(v___x_3793_, 0);
lean_inc(v_val_3795_);
lean_dec_ref_known(v___x_3793_, 1);
v___x_3796_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__4));
v___x_3797_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_val_3795_, v___x_3768_);
v___x_3798_ = l_addParenHeuristic(v___x_3797_);
v___x_3799_ = lean_string_append(v___x_3796_, v___x_3798_);
lean_dec_ref(v___x_3798_);
v___x_3800_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__5));
v___x_3801_ = lean_string_append(v___x_3799_, v___x_3800_);
v___y_3789_ = v___x_3801_;
goto v___jp_3788_;
}
v___jp_3788_:
{
lean_object* v___x_3790_; lean_object* v___x_3791_; lean_object* v___x_3792_; 
v___x_3790_ = lean_string_append(v___x_3787_, v___y_3789_);
lean_dec_ref(v___y_3789_);
v___x_3791_ = lean_string_append(v___x_3790_, v___x_3775_);
v___x_3792_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3792_, 0, v___x_3791_);
return v___x_3792_;
}
}
else
{
lean_object* v___x_3802_; lean_object* v___x_3803_; lean_object* v___x_3804_; 
v___x_3802_ = lean_box(1);
lean_inc(v_decl_3759_);
lean_inc_ref(v_env_3758_);
v___x_3803_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3802_, v_ext_3761_, v_env_3758_, v_asyncMode_3778_, v_decl_3759_);
v___x_3804_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_3803_, v_decl_3759_);
lean_dec(v___x_3803_);
if (lean_obj_tag(v___x_3804_) == 0)
{
lean_dec_ref(v_pfx_3776_);
goto v___jp_3779_;
}
else
{
lean_object* v___x_3806_; uint8_t v_isShared_3807_; uint8_t v_isSharedCheck_3813_; 
v_isSharedCheck_3813_ = !lean_is_exclusive(v___x_3804_);
if (v_isSharedCheck_3813_ == 0)
{
lean_object* v_unused_3814_; 
v_unused_3814_ = lean_ctor_get(v___x_3804_, 0);
lean_dec(v_unused_3814_);
v___x_3806_ = v___x_3804_;
v_isShared_3807_ = v_isSharedCheck_3813_;
goto v_resetjp_3805_;
}
else
{
lean_dec(v___x_3804_);
v___x_3806_ = lean_box(0);
v_isShared_3807_ = v_isSharedCheck_3813_;
goto v_resetjp_3805_;
}
v_resetjp_3805_:
{
if (v___x_3785_ == 0)
{
lean_del_object(v___x_3806_);
lean_dec_ref(v_pfx_3776_);
goto v___jp_3779_;
}
else
{
lean_object* v___x_3808_; lean_object* v___x_3809_; lean_object* v___x_3811_; 
lean_dec(v_asyncMode_3778_);
lean_del_object(v___x_3763_);
lean_dec_ref(v_ext_3761_);
lean_dec(v_val_3760_);
lean_dec(v_decl_3759_);
lean_dec_ref(v_env_3758_);
v___x_3808_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__6));
v___x_3809_ = lean_string_append(v_pfx_3776_, v___x_3808_);
if (v_isShared_3807_ == 0)
{
lean_ctor_set_tag(v___x_3806_, 0);
lean_ctor_set(v___x_3806_, 0, v___x_3809_);
v___x_3811_ = v___x_3806_;
goto v_reusejp_3810_;
}
else
{
lean_object* v_reuseFailAlloc_3812_; 
v_reuseFailAlloc_3812_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3812_, 0, v___x_3809_);
v___x_3811_ = v_reuseFailAlloc_3812_;
goto v_reusejp_3810_;
}
v_reusejp_3810_:
{
return v___x_3811_;
}
}
}
}
}
v___jp_3779_:
{
lean_object* v___x_3781_; 
lean_inc(v_decl_3759_);
if (v_isShared_3764_ == 0)
{
lean_ctor_set(v___x_3763_, 1, v_val_3760_);
lean_ctor_set(v___x_3763_, 0, v_decl_3759_);
v___x_3781_ = v___x_3763_;
goto v_reusejp_3780_;
}
else
{
lean_object* v_reuseFailAlloc_3784_; 
v_reuseFailAlloc_3784_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3784_, 0, v_decl_3759_);
lean_ctor_set(v_reuseFailAlloc_3784_, 1, v_val_3760_);
v___x_3781_ = v_reuseFailAlloc_3784_;
goto v_reusejp_3780_;
}
v_reusejp_3780_:
{
lean_object* v___x_3782_; lean_object* v___x_3783_; 
v___x_3782_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_ext_3761_, v_env_3758_, v___x_3781_, v_asyncMode_3778_, v_decl_3759_);
lean_dec(v_asyncMode_3778_);
v___x_3783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3783_, 0, v___x_3782_);
return v___x_3783_;
}
}
}
else
{
lean_object* v___x_3816_; uint8_t v_isShared_3817_; uint8_t v_isSharedCheck_3823_; 
lean_del_object(v___x_3763_);
lean_dec_ref(v_ext_3761_);
lean_dec(v_val_3760_);
lean_dec(v_decl_3759_);
lean_dec_ref(v_env_3758_);
v_isSharedCheck_3823_ = !lean_is_exclusive(v___x_3777_);
if (v_isSharedCheck_3823_ == 0)
{
lean_object* v_unused_3824_; 
v_unused_3824_ = lean_ctor_get(v___x_3777_, 0);
lean_dec(v_unused_3824_);
v___x_3816_ = v___x_3777_;
v_isShared_3817_ = v_isSharedCheck_3823_;
goto v_resetjp_3815_;
}
else
{
lean_dec(v___x_3777_);
v___x_3816_ = lean_box(0);
v_isShared_3817_ = v_isSharedCheck_3823_;
goto v_resetjp_3815_;
}
v_resetjp_3815_:
{
lean_object* v___x_3818_; lean_object* v___x_3819_; lean_object* v___x_3821_; 
v___x_3818_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__7));
v___x_3819_ = lean_string_append(v_pfx_3776_, v___x_3818_);
if (v_isShared_3817_ == 0)
{
lean_ctor_set_tag(v___x_3816_, 0);
lean_ctor_set(v___x_3816_, 0, v___x_3819_);
v___x_3821_ = v___x_3816_;
goto v_reusejp_3820_;
}
else
{
lean_object* v_reuseFailAlloc_3822_; 
v_reuseFailAlloc_3822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3822_, 0, v___x_3819_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_EnumAttributes_setValue(lean_object* v_00_u03b1_3827_, lean_object* v_attrs_3828_, lean_object* v_env_3829_, lean_object* v_decl_3830_, lean_object* v_val_3831_){
_start:
{
lean_object* v___x_3832_; 
v___x_3832_ = l_Lean_EnumAttributes_setValue___redArg(v_attrs_3828_, v_env_3829_, v_decl_3830_, v_val_3831_);
return v___x_3832_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_2990505691____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3834_; lean_object* v___x_3835_; lean_object* v___x_3836_; 
v___x_3834_ = lean_obj_once(&l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_, &l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2__once, _init_l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_);
v___x_3835_ = lean_st_mk_ref(v___x_3834_);
v___x_3836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3836_, 0, v___x_3835_);
return v___x_3836_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_2990505691____hygCtx___hyg_2____boxed(lean_object* v_a_3837_){
_start:
{
lean_object* v_res_3838_; 
v_res_3838_ = l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_2990505691____hygCtx___hyg_2_();
return v_res_3838_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerAttributeImplBuilder(lean_object* v_builderId_3841_, lean_object* v_builder_3842_){
_start:
{
lean_object* v___x_3844_; lean_object* v___x_3845_; uint8_t v___x_3846_; 
v___x_3844_ = l_Lean_attributeImplBuilderTableRef;
v___x_3845_ = lean_st_ref_get(v___x_3844_);
v___x_3846_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(v___x_3845_, v_builderId_3841_);
lean_dec(v___x_3845_);
if (v___x_3846_ == 0)
{
lean_object* v___x_3847_; lean_object* v___x_3848_; lean_object* v___x_3849_; lean_object* v___x_3850_; 
v___x_3847_ = lean_st_ref_take(v___x_3844_);
v___x_3848_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1___redArg(v___x_3847_, v_builderId_3841_, v_builder_3842_);
v___x_3849_ = lean_st_ref_set(v___x_3844_, v___x_3848_);
v___x_3850_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3850_, 0, v___x_3849_);
return v___x_3850_;
}
else
{
lean_object* v___x_3851_; lean_object* v___x_3852_; lean_object* v___x_3853_; lean_object* v___x_3854_; lean_object* v___x_3855_; lean_object* v___x_3856_; lean_object* v___x_3857_; 
lean_dec_ref(v_builder_3842_);
v___x_3851_ = ((lean_object*)(l_Lean_registerAttributeImplBuilder___closed__0));
v___x_3852_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_builderId_3841_, v___x_3846_);
v___x_3853_ = lean_string_append(v___x_3851_, v___x_3852_);
lean_dec_ref(v___x_3852_);
v___x_3854_ = ((lean_object*)(l_Lean_registerAttributeImplBuilder___closed__1));
v___x_3855_ = lean_string_append(v___x_3853_, v___x_3854_);
v___x_3856_ = lean_mk_io_user_error(v___x_3855_);
v___x_3857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3857_, 0, v___x_3856_);
return v___x_3857_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerAttributeImplBuilder___boxed(lean_object* v_builderId_3858_, lean_object* v_builder_3859_, lean_object* v_a_3860_){
_start:
{
lean_object* v_res_3861_; 
v_res_3861_ = l_Lean_registerAttributeImplBuilder(v_builderId_3858_, v_builder_3859_);
return v_res_3861_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___redArg(lean_object* v_e_3862_){
_start:
{
if (lean_obj_tag(v_e_3862_) == 0)
{
lean_object* v_a_3864_; lean_object* v___x_3866_; uint8_t v_isShared_3867_; uint8_t v_isSharedCheck_3872_; 
v_a_3864_ = lean_ctor_get(v_e_3862_, 0);
v_isSharedCheck_3872_ = !lean_is_exclusive(v_e_3862_);
if (v_isSharedCheck_3872_ == 0)
{
v___x_3866_ = v_e_3862_;
v_isShared_3867_ = v_isSharedCheck_3872_;
goto v_resetjp_3865_;
}
else
{
lean_inc(v_a_3864_);
lean_dec(v_e_3862_);
v___x_3866_ = lean_box(0);
v_isShared_3867_ = v_isSharedCheck_3872_;
goto v_resetjp_3865_;
}
v_resetjp_3865_:
{
lean_object* v___x_3868_; lean_object* v___x_3870_; 
v___x_3868_ = lean_mk_io_user_error(v_a_3864_);
if (v_isShared_3867_ == 0)
{
lean_ctor_set_tag(v___x_3866_, 1);
lean_ctor_set(v___x_3866_, 0, v___x_3868_);
v___x_3870_ = v___x_3866_;
goto v_reusejp_3869_;
}
else
{
lean_object* v_reuseFailAlloc_3871_; 
v_reuseFailAlloc_3871_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3871_, 0, v___x_3868_);
v___x_3870_ = v_reuseFailAlloc_3871_;
goto v_reusejp_3869_;
}
v_reusejp_3869_:
{
return v___x_3870_;
}
}
}
else
{
lean_object* v_a_3873_; lean_object* v___x_3875_; uint8_t v_isShared_3876_; uint8_t v_isSharedCheck_3880_; 
v_a_3873_ = lean_ctor_get(v_e_3862_, 0);
v_isSharedCheck_3880_ = !lean_is_exclusive(v_e_3862_);
if (v_isSharedCheck_3880_ == 0)
{
v___x_3875_ = v_e_3862_;
v_isShared_3876_ = v_isSharedCheck_3880_;
goto v_resetjp_3874_;
}
else
{
lean_inc(v_a_3873_);
lean_dec(v_e_3862_);
v___x_3875_ = lean_box(0);
v_isShared_3876_ = v_isSharedCheck_3880_;
goto v_resetjp_3874_;
}
v_resetjp_3874_:
{
lean_object* v___x_3878_; 
if (v_isShared_3876_ == 0)
{
lean_ctor_set_tag(v___x_3875_, 0);
v___x_3878_ = v___x_3875_;
goto v_reusejp_3877_;
}
else
{
lean_object* v_reuseFailAlloc_3879_; 
v_reuseFailAlloc_3879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3879_, 0, v_a_3873_);
v___x_3878_ = v_reuseFailAlloc_3879_;
goto v_reusejp_3877_;
}
v_reusejp_3877_:
{
return v___x_3878_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___redArg___boxed(lean_object* v_e_3881_, lean_object* v_a_3882_){
_start:
{
lean_object* v_res_3883_; 
v_res_3883_ = l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___redArg(v_e_3881_);
return v_res_3883_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1(lean_object* v_00_u03b1_3884_, lean_object* v_e_3885_){
_start:
{
lean_object* v___x_3887_; 
v___x_3887_ = l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___redArg(v_e_3885_);
return v___x_3887_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___boxed(lean_object* v_00_u03b1_3888_, lean_object* v_e_3889_, lean_object* v_a_3890_){
_start:
{
lean_object* v_res_3891_; 
v_res_3891_ = l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1(v_00_u03b1_3888_, v_e_3889_);
return v_res_3891_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___redArg(lean_object* v_a_3892_, lean_object* v_x_3893_){
_start:
{
if (lean_obj_tag(v_x_3893_) == 0)
{
lean_object* v___x_3894_; 
v___x_3894_ = lean_box(0);
return v___x_3894_;
}
else
{
lean_object* v_key_3895_; lean_object* v_value_3896_; lean_object* v_tail_3897_; uint8_t v___x_3898_; 
v_key_3895_ = lean_ctor_get(v_x_3893_, 0);
v_value_3896_ = lean_ctor_get(v_x_3893_, 1);
v_tail_3897_ = lean_ctor_get(v_x_3893_, 2);
v___x_3898_ = lean_name_eq(v_key_3895_, v_a_3892_);
if (v___x_3898_ == 0)
{
v_x_3893_ = v_tail_3897_;
goto _start;
}
else
{
lean_object* v___x_3900_; 
lean_inc(v_value_3896_);
v___x_3900_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3900_, 0, v_value_3896_);
return v___x_3900_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___redArg___boxed(lean_object* v_a_3901_, lean_object* v_x_3902_){
_start:
{
lean_object* v_res_3903_; 
v_res_3903_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___redArg(v_a_3901_, v_x_3902_);
lean_dec(v_x_3902_);
lean_dec(v_a_3901_);
return v_res_3903_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(lean_object* v_m_3904_, lean_object* v_a_3905_){
_start:
{
lean_object* v_buckets_3906_; lean_object* v___x_3907_; uint64_t v___y_3909_; 
v_buckets_3906_ = lean_ctor_get(v_m_3904_, 1);
v___x_3907_ = lean_array_get_size(v_buckets_3906_);
if (lean_obj_tag(v_a_3905_) == 0)
{
uint64_t v___x_3923_; 
v___x_3923_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg___closed__0);
v___y_3909_ = v___x_3923_;
goto v___jp_3908_;
}
else
{
uint64_t v_hash_3924_; 
v_hash_3924_ = lean_ctor_get_uint64(v_a_3905_, sizeof(void*)*2);
v___y_3909_ = v_hash_3924_;
goto v___jp_3908_;
}
v___jp_3908_:
{
uint64_t v___x_3910_; uint64_t v___x_3911_; uint64_t v_fold_3912_; uint64_t v___x_3913_; uint64_t v___x_3914_; uint64_t v___x_3915_; size_t v___x_3916_; size_t v___x_3917_; size_t v___x_3918_; size_t v___x_3919_; size_t v___x_3920_; lean_object* v___x_3921_; lean_object* v___x_3922_; 
v___x_3910_ = 32ULL;
v___x_3911_ = lean_uint64_shift_right(v___y_3909_, v___x_3910_);
v_fold_3912_ = lean_uint64_xor(v___y_3909_, v___x_3911_);
v___x_3913_ = 16ULL;
v___x_3914_ = lean_uint64_shift_right(v_fold_3912_, v___x_3913_);
v___x_3915_ = lean_uint64_xor(v_fold_3912_, v___x_3914_);
v___x_3916_ = lean_uint64_to_usize(v___x_3915_);
v___x_3917_ = lean_usize_of_nat(v___x_3907_);
v___x_3918_ = ((size_t)1ULL);
v___x_3919_ = lean_usize_sub(v___x_3917_, v___x_3918_);
v___x_3920_ = lean_usize_land(v___x_3916_, v___x_3919_);
v___x_3921_ = lean_array_uget_borrowed(v_buckets_3906_, v___x_3920_);
v___x_3922_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___redArg(v_a_3905_, v___x_3921_);
return v___x_3922_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg___boxed(lean_object* v_m_3925_, lean_object* v_a_3926_){
_start:
{
lean_object* v_res_3927_; 
v_res_3927_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(v_m_3925_, v_a_3926_);
lean_dec(v_a_3926_);
lean_dec_ref(v_m_3925_);
return v_res_3927_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAttributeImplOfEntry(lean_object* v_e_3929_){
_start:
{
lean_object* v___x_3931_; lean_object* v___x_3932_; lean_object* v_builderId_3933_; lean_object* v_ref_3934_; lean_object* v_args_3935_; lean_object* v___x_3936_; 
v___x_3931_ = l_Lean_attributeImplBuilderTableRef;
v___x_3932_ = lean_st_ref_get(v___x_3931_);
v_builderId_3933_ = lean_ctor_get(v_e_3929_, 0);
lean_inc(v_builderId_3933_);
v_ref_3934_ = lean_ctor_get(v_e_3929_, 1);
lean_inc(v_ref_3934_);
v_args_3935_ = lean_ctor_get(v_e_3929_, 2);
lean_inc(v_args_3935_);
lean_dec_ref(v_e_3929_);
v___x_3936_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(v___x_3932_, v_builderId_3933_);
lean_dec(v___x_3932_);
if (lean_obj_tag(v___x_3936_) == 0)
{
lean_object* v___x_3937_; uint8_t v___x_3938_; lean_object* v___x_3939_; lean_object* v___x_3940_; lean_object* v___x_3941_; lean_object* v___x_3942_; lean_object* v___x_3943_; lean_object* v___x_3944_; 
lean_dec(v_args_3935_);
lean_dec(v_ref_3934_);
v___x_3937_ = ((lean_object*)(l_Lean_mkAttributeImplOfEntry___closed__0));
v___x_3938_ = 1;
v___x_3939_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_builderId_3933_, v___x_3938_);
v___x_3940_ = lean_string_append(v___x_3937_, v___x_3939_);
lean_dec_ref(v___x_3939_);
v___x_3941_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__4));
v___x_3942_ = lean_string_append(v___x_3940_, v___x_3941_);
v___x_3943_ = lean_mk_io_user_error(v___x_3942_);
v___x_3944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3944_, 0, v___x_3943_);
return v___x_3944_;
}
else
{
lean_object* v_val_3945_; lean_object* v___x_3946_; lean_object* v___x_3947_; 
lean_dec(v_builderId_3933_);
v_val_3945_ = lean_ctor_get(v___x_3936_, 0);
lean_inc(v_val_3945_);
lean_dec_ref_known(v___x_3936_, 1);
v___x_3946_ = lean_apply_2(v_val_3945_, v_ref_3934_, v_args_3935_);
v___x_3947_ = l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___redArg(v___x_3946_);
return v___x_3947_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkAttributeImplOfEntry___boxed(lean_object* v_e_3948_, lean_object* v_a_3949_){
_start:
{
lean_object* v_res_3950_; 
v_res_3950_ = l_Lean_mkAttributeImplOfEntry(v_e_3948_);
return v_res_3950_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0(lean_object* v_00_u03b2_3951_, lean_object* v_m_3952_, lean_object* v_a_3953_){
_start:
{
lean_object* v___x_3954_; 
v___x_3954_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(v_m_3952_, v_a_3953_);
return v___x_3954_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___boxed(lean_object* v_00_u03b2_3955_, lean_object* v_m_3956_, lean_object* v_a_3957_){
_start:
{
lean_object* v_res_3958_; 
v_res_3958_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0(v_00_u03b2_3955_, v_m_3956_, v_a_3957_);
lean_dec(v_a_3957_);
lean_dec_ref(v_m_3956_);
return v_res_3958_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0(lean_object* v_00_u03b2_3959_, lean_object* v_a_3960_, lean_object* v_x_3961_){
_start:
{
lean_object* v___x_3962_; 
v___x_3962_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___redArg(v_a_3960_, v_x_3961_);
return v___x_3962_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3963_, lean_object* v_a_3964_, lean_object* v_x_3965_){
_start:
{
lean_object* v_res_3966_; 
v_res_3966_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0(v_00_u03b2_3963_, v_a_3964_, v_x_3965_);
lean_dec(v_x_3965_);
lean_dec(v_a_3964_);
return v_res_3966_;
}
}
static lean_object* _init_l_Lean_instInhabitedAttributeExtensionState_default___closed__0(void){
_start:
{
lean_object* v___x_3967_; lean_object* v___x_3968_; lean_object* v___x_3969_; 
v___x_3967_ = lean_obj_once(&l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_, &l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2__once, _init_l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_);
v___x_3968_ = lean_box(0);
v___x_3969_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3969_, 0, v___x_3968_);
lean_ctor_set(v___x_3969_, 1, v___x_3967_);
return v___x_3969_;
}
}
static lean_object* _init_l_Lean_instInhabitedAttributeExtensionState_default(void){
_start:
{
lean_object* v___x_3970_; 
v___x_3970_ = lean_obj_once(&l_Lean_instInhabitedAttributeExtensionState_default___closed__0, &l_Lean_instInhabitedAttributeExtensionState_default___closed__0_once, _init_l_Lean_instInhabitedAttributeExtensionState_default___closed__0);
return v___x_3970_;
}
}
static lean_object* _init_l_Lean_instInhabitedAttributeExtensionState(void){
_start:
{
lean_object* v___x_3971_; 
v___x_3971_ = l_Lean_instInhabitedAttributeExtensionState_default;
return v___x_3971_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_AttributeExtension_mkInitial(){
_start:
{
lean_object* v___x_3973_; lean_object* v___x_3974_; lean_object* v___x_3975_; lean_object* v___x_3976_; lean_object* v___x_3977_; 
v___x_3973_ = l_Lean_attributeMapRef;
v___x_3974_ = lean_st_ref_get(v___x_3973_);
v___x_3975_ = lean_box(0);
v___x_3976_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3976_, 0, v___x_3975_);
lean_ctor_set(v___x_3976_, 1, v___x_3974_);
v___x_3977_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3977_, 0, v___x_3976_);
return v___x_3977_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_AttributeExtension_mkInitial___boxed(lean_object* v_a_3978_){
_start:
{
lean_object* v_res_3979_; 
v_res_3979_ = l___private_Lean_Attributes_0__Lean_AttributeExtension_mkInitial();
return v_res_3979_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAttributeImplOfConstantUnsafe(lean_object* v_env_3985_, lean_object* v_opts_3986_, lean_object* v_declName_3987_){
_start:
{
uint8_t v___x_3990_; lean_object* v___x_3991_; 
v___x_3990_ = 0;
lean_inc(v_declName_3987_);
lean_inc_ref(v_env_3985_);
v___x_3991_ = l_Lean_Environment_find_x3f(v_env_3985_, v_declName_3987_, v___x_3990_);
if (lean_obj_tag(v___x_3991_) == 0)
{
lean_object* v___x_3992_; uint8_t v___x_3993_; lean_object* v___x_3994_; lean_object* v___x_3995_; lean_object* v___x_3996_; lean_object* v___x_3997_; lean_object* v___x_3998_; 
lean_dec_ref(v_env_3985_);
v___x_3992_ = ((lean_object*)(l_Lean_mkAttributeImplOfConstantUnsafe___closed__2));
v___x_3993_ = 1;
v___x_3994_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_declName_3987_, v___x_3993_);
v___x_3995_ = lean_string_append(v___x_3992_, v___x_3994_);
lean_dec_ref(v___x_3994_);
v___x_3996_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__4));
v___x_3997_ = lean_string_append(v___x_3995_, v___x_3996_);
v___x_3998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3998_, 0, v___x_3997_);
return v___x_3998_;
}
else
{
lean_object* v_val_3999_; lean_object* v___x_4000_; 
v_val_3999_ = lean_ctor_get(v___x_3991_, 0);
lean_inc(v_val_3999_);
lean_dec_ref_known(v___x_3991_, 1);
v___x_4000_ = l_Lean_ConstantInfo_type(v_val_3999_);
lean_dec(v_val_3999_);
if (lean_obj_tag(v___x_4000_) == 4)
{
lean_object* v_declName_4001_; 
v_declName_4001_ = lean_ctor_get(v___x_4000_, 0);
lean_inc(v_declName_4001_);
lean_dec_ref_known(v___x_4000_, 2);
if (lean_obj_tag(v_declName_4001_) == 1)
{
lean_object* v_pre_4002_; 
v_pre_4002_ = lean_ctor_get(v_declName_4001_, 0);
lean_inc(v_pre_4002_);
if (lean_obj_tag(v_pre_4002_) == 1)
{
lean_object* v_pre_4003_; 
v_pre_4003_ = lean_ctor_get(v_pre_4002_, 0);
if (lean_obj_tag(v_pre_4003_) == 0)
{
lean_object* v_str_4004_; lean_object* v_str_4005_; lean_object* v___x_4006_; uint8_t v___x_4007_; 
v_str_4004_ = lean_ctor_get(v_declName_4001_, 1);
lean_inc_ref(v_str_4004_);
lean_dec_ref_known(v_declName_4001_, 2);
v_str_4005_ = lean_ctor_get(v_pre_4002_, 1);
lean_inc_ref(v_str_4005_);
lean_dec_ref_known(v_pre_4002_, 2);
v___x_4006_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__0));
v___x_4007_ = lean_string_dec_eq(v_str_4005_, v___x_4006_);
lean_dec_ref(v_str_4005_);
if (v___x_4007_ == 0)
{
lean_dec_ref(v_str_4004_);
lean_dec(v_declName_3987_);
lean_dec_ref(v_env_3985_);
goto v___jp_3988_;
}
else
{
lean_object* v___x_4008_; uint8_t v___x_4009_; 
v___x_4008_ = ((lean_object*)(l_Lean_mkAttributeImplOfConstantUnsafe___closed__3));
v___x_4009_ = lean_string_dec_eq(v_str_4004_, v___x_4008_);
lean_dec_ref(v_str_4004_);
if (v___x_4009_ == 0)
{
lean_dec(v_declName_3987_);
lean_dec_ref(v_env_3985_);
goto v___jp_3988_;
}
else
{
lean_object* v___x_4010_; 
v___x_4010_ = l_Lean_Environment_evalConst___redArg(v_env_3985_, v_opts_3986_, v_declName_3987_, v___x_4009_);
lean_dec(v_declName_3987_);
lean_dec_ref(v_env_3985_);
return v___x_4010_;
}
}
}
else
{
lean_dec_ref_known(v_pre_4002_, 2);
lean_dec_ref_known(v_declName_4001_, 2);
lean_dec(v_declName_3987_);
lean_dec_ref(v_env_3985_);
goto v___jp_3988_;
}
}
else
{
lean_dec_ref_known(v_declName_4001_, 2);
lean_dec(v_pre_4002_);
lean_dec(v_declName_3987_);
lean_dec_ref(v_env_3985_);
goto v___jp_3988_;
}
}
else
{
lean_dec(v_declName_4001_);
lean_dec(v_declName_3987_);
lean_dec_ref(v_env_3985_);
goto v___jp_3988_;
}
}
else
{
lean_dec_ref(v___x_4000_);
lean_dec(v_declName_3987_);
lean_dec_ref(v_env_3985_);
goto v___jp_3988_;
}
}
v___jp_3988_:
{
lean_object* v___x_3989_; 
v___x_3989_ = ((lean_object*)(l_Lean_mkAttributeImplOfConstantUnsafe___closed__1));
return v___x_3989_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkAttributeImplOfConstantUnsafe___boxed(lean_object* v_env_4011_, lean_object* v_opts_4012_, lean_object* v_declName_4013_){
_start:
{
lean_object* v_res_4014_; 
v_res_4014_ = l_Lean_mkAttributeImplOfConstantUnsafe(v_env_4011_, v_opts_4012_, v_declName_4013_);
lean_dec_ref(v_opts_4012_);
return v_res_4014_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg(lean_object* v_as_4015_, size_t v_i_4016_, size_t v_stop_4017_, lean_object* v_b_4018_){
_start:
{
uint8_t v___x_4020_; 
v___x_4020_ = lean_usize_dec_eq(v_i_4016_, v_stop_4017_);
if (v___x_4020_ == 0)
{
lean_object* v___x_4021_; lean_object* v___x_4022_; 
v___x_4021_ = lean_array_uget_borrowed(v_as_4015_, v_i_4016_);
lean_inc(v___x_4021_);
v___x_4022_ = l_Lean_mkAttributeImplOfEntry(v___x_4021_);
if (lean_obj_tag(v___x_4022_) == 0)
{
lean_object* v_a_4023_; lean_object* v_toAttributeImplCore_4024_; lean_object* v_name_4025_; lean_object* v___x_4026_; size_t v___x_4027_; size_t v___x_4028_; 
v_a_4023_ = lean_ctor_get(v___x_4022_, 0);
lean_inc(v_a_4023_);
lean_dec_ref_known(v___x_4022_, 1);
v_toAttributeImplCore_4024_ = lean_ctor_get(v_a_4023_, 0);
v_name_4025_ = lean_ctor_get(v_toAttributeImplCore_4024_, 1);
lean_inc(v_name_4025_);
v___x_4026_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1___redArg(v_b_4018_, v_name_4025_, v_a_4023_);
v___x_4027_ = ((size_t)1ULL);
v___x_4028_ = lean_usize_add(v_i_4016_, v___x_4027_);
v_i_4016_ = v___x_4028_;
v_b_4018_ = v___x_4026_;
goto _start;
}
else
{
lean_object* v_a_4030_; lean_object* v___x_4032_; uint8_t v_isShared_4033_; uint8_t v_isSharedCheck_4037_; 
lean_dec_ref(v_b_4018_);
v_a_4030_ = lean_ctor_get(v___x_4022_, 0);
v_isSharedCheck_4037_ = !lean_is_exclusive(v___x_4022_);
if (v_isSharedCheck_4037_ == 0)
{
v___x_4032_ = v___x_4022_;
v_isShared_4033_ = v_isSharedCheck_4037_;
goto v_resetjp_4031_;
}
else
{
lean_inc(v_a_4030_);
lean_dec(v___x_4022_);
v___x_4032_ = lean_box(0);
v_isShared_4033_ = v_isSharedCheck_4037_;
goto v_resetjp_4031_;
}
v_resetjp_4031_:
{
lean_object* v___x_4035_; 
if (v_isShared_4033_ == 0)
{
v___x_4035_ = v___x_4032_;
goto v_reusejp_4034_;
}
else
{
lean_object* v_reuseFailAlloc_4036_; 
v_reuseFailAlloc_4036_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4036_, 0, v_a_4030_);
v___x_4035_ = v_reuseFailAlloc_4036_;
goto v_reusejp_4034_;
}
v_reusejp_4034_:
{
return v___x_4035_;
}
}
}
}
else
{
lean_object* v___x_4038_; 
v___x_4038_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4038_, 0, v_b_4018_);
return v___x_4038_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg___boxed(lean_object* v_as_4039_, lean_object* v_i_4040_, lean_object* v_stop_4041_, lean_object* v_b_4042_, lean_object* v___y_4043_){
_start:
{
size_t v_i_boxed_4044_; size_t v_stop_boxed_4045_; lean_object* v_res_4046_; 
v_i_boxed_4044_ = lean_unbox_usize(v_i_4040_);
lean_dec(v_i_4040_);
v_stop_boxed_4045_ = lean_unbox_usize(v_stop_4041_);
lean_dec(v_stop_4041_);
v_res_4046_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg(v_as_4039_, v_i_boxed_4044_, v_stop_boxed_4045_, v_b_4042_);
lean_dec_ref(v_as_4039_);
return v_res_4046_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__1(lean_object* v_as_4047_, size_t v_i_4048_, size_t v_stop_4049_, lean_object* v_b_4050_, lean_object* v___y_4051_){
_start:
{
lean_object* v_a_4054_; lean_object* v___y_4059_; uint8_t v___x_4061_; 
v___x_4061_ = lean_usize_dec_eq(v_i_4048_, v_stop_4049_);
if (v___x_4061_ == 0)
{
lean_object* v___x_4062_; lean_object* v___x_4063_; lean_object* v___x_4064_; uint8_t v___x_4065_; 
v___x_4062_ = lean_array_uget_borrowed(v_as_4047_, v_i_4048_);
v___x_4063_ = lean_unsigned_to_nat(0u);
v___x_4064_ = lean_array_get_size(v___x_4062_);
v___x_4065_ = lean_nat_dec_lt(v___x_4063_, v___x_4064_);
if (v___x_4065_ == 0)
{
v_a_4054_ = v_b_4050_;
goto v___jp_4053_;
}
else
{
uint8_t v___x_4066_; 
v___x_4066_ = lean_nat_dec_le(v___x_4064_, v___x_4064_);
if (v___x_4066_ == 0)
{
if (v___x_4065_ == 0)
{
v_a_4054_ = v_b_4050_;
goto v___jp_4053_;
}
else
{
size_t v___x_4067_; size_t v___x_4068_; lean_object* v___x_4069_; 
v___x_4067_ = ((size_t)0ULL);
v___x_4068_ = lean_usize_of_nat(v___x_4064_);
v___x_4069_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg(v___x_4062_, v___x_4067_, v___x_4068_, v_b_4050_);
v___y_4059_ = v___x_4069_;
goto v___jp_4058_;
}
}
else
{
size_t v___x_4070_; size_t v___x_4071_; lean_object* v___x_4072_; 
v___x_4070_ = ((size_t)0ULL);
v___x_4071_ = lean_usize_of_nat(v___x_4064_);
v___x_4072_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg(v___x_4062_, v___x_4070_, v___x_4071_, v_b_4050_);
v___y_4059_ = v___x_4072_;
goto v___jp_4058_;
}
}
}
else
{
lean_object* v___x_4073_; 
v___x_4073_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4073_, 0, v_b_4050_);
return v___x_4073_;
}
v___jp_4053_:
{
size_t v___x_4055_; size_t v___x_4056_; 
v___x_4055_ = ((size_t)1ULL);
v___x_4056_ = lean_usize_add(v_i_4048_, v___x_4055_);
v_i_4048_ = v___x_4056_;
v_b_4050_ = v_a_4054_;
goto _start;
}
v___jp_4058_:
{
if (lean_obj_tag(v___y_4059_) == 0)
{
lean_object* v_a_4060_; 
v_a_4060_ = lean_ctor_get(v___y_4059_, 0);
lean_inc(v_a_4060_);
lean_dec_ref_known(v___y_4059_, 1);
v_a_4054_ = v_a_4060_;
goto v___jp_4053_;
}
else
{
return v___y_4059_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__1___boxed(lean_object* v_as_4074_, lean_object* v_i_4075_, lean_object* v_stop_4076_, lean_object* v_b_4077_, lean_object* v___y_4078_, lean_object* v___y_4079_){
_start:
{
size_t v_i_boxed_4080_; size_t v_stop_boxed_4081_; lean_object* v_res_4082_; 
v_i_boxed_4080_ = lean_unbox_usize(v_i_4075_);
lean_dec(v_i_4075_);
v_stop_boxed_4081_ = lean_unbox_usize(v_stop_4076_);
lean_dec(v_stop_4076_);
v_res_4082_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__1(v_as_4074_, v_i_boxed_4080_, v_stop_boxed_4081_, v_b_4077_, v___y_4078_);
lean_dec_ref(v___y_4078_);
lean_dec_ref(v_as_4074_);
return v_res_4082_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_AttributeExtension_addImported(lean_object* v_es_4083_, lean_object* v_a_4084_){
_start:
{
lean_object* v_a_4087_; lean_object* v___y_4092_; lean_object* v___x_4102_; lean_object* v___x_4103_; lean_object* v___x_4104_; lean_object* v___x_4105_; uint8_t v___x_4106_; 
v___x_4102_ = l_Lean_attributeMapRef;
v___x_4103_ = lean_st_ref_get(v___x_4102_);
v___x_4104_ = lean_unsigned_to_nat(0u);
v___x_4105_ = lean_array_get_size(v_es_4083_);
v___x_4106_ = lean_nat_dec_lt(v___x_4104_, v___x_4105_);
if (v___x_4106_ == 0)
{
v_a_4087_ = v___x_4103_;
goto v___jp_4086_;
}
else
{
uint8_t v___x_4107_; 
v___x_4107_ = lean_nat_dec_le(v___x_4105_, v___x_4105_);
if (v___x_4107_ == 0)
{
if (v___x_4106_ == 0)
{
v_a_4087_ = v___x_4103_;
goto v___jp_4086_;
}
else
{
size_t v___x_4108_; size_t v___x_4109_; lean_object* v___x_4110_; 
v___x_4108_ = ((size_t)0ULL);
v___x_4109_ = lean_usize_of_nat(v___x_4105_);
v___x_4110_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__1(v_es_4083_, v___x_4108_, v___x_4109_, v___x_4103_, v_a_4084_);
v___y_4092_ = v___x_4110_;
goto v___jp_4091_;
}
}
else
{
size_t v___x_4111_; size_t v___x_4112_; lean_object* v___x_4113_; 
v___x_4111_ = ((size_t)0ULL);
v___x_4112_ = lean_usize_of_nat(v___x_4105_);
v___x_4113_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__1(v_es_4083_, v___x_4111_, v___x_4112_, v___x_4103_, v_a_4084_);
v___y_4092_ = v___x_4113_;
goto v___jp_4091_;
}
}
v___jp_4086_:
{
lean_object* v___x_4088_; lean_object* v___x_4089_; lean_object* v___x_4090_; 
v___x_4088_ = lean_box(0);
v___x_4089_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4089_, 0, v___x_4088_);
lean_ctor_set(v___x_4089_, 1, v_a_4087_);
v___x_4090_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4090_, 0, v___x_4089_);
return v___x_4090_;
}
v___jp_4091_:
{
if (lean_obj_tag(v___y_4092_) == 0)
{
lean_object* v_a_4093_; 
v_a_4093_ = lean_ctor_get(v___y_4092_, 0);
lean_inc(v_a_4093_);
lean_dec_ref_known(v___y_4092_, 1);
v_a_4087_ = v_a_4093_;
goto v___jp_4086_;
}
else
{
lean_object* v_a_4094_; lean_object* v___x_4096_; uint8_t v_isShared_4097_; uint8_t v_isSharedCheck_4101_; 
v_a_4094_ = lean_ctor_get(v___y_4092_, 0);
v_isSharedCheck_4101_ = !lean_is_exclusive(v___y_4092_);
if (v_isSharedCheck_4101_ == 0)
{
v___x_4096_ = v___y_4092_;
v_isShared_4097_ = v_isSharedCheck_4101_;
goto v_resetjp_4095_;
}
else
{
lean_inc(v_a_4094_);
lean_dec(v___y_4092_);
v___x_4096_ = lean_box(0);
v_isShared_4097_ = v_isSharedCheck_4101_;
goto v_resetjp_4095_;
}
v_resetjp_4095_:
{
lean_object* v___x_4099_; 
if (v_isShared_4097_ == 0)
{
v___x_4099_ = v___x_4096_;
goto v_reusejp_4098_;
}
else
{
lean_object* v_reuseFailAlloc_4100_; 
v_reuseFailAlloc_4100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4100_, 0, v_a_4094_);
v___x_4099_ = v_reuseFailAlloc_4100_;
goto v_reusejp_4098_;
}
v_reusejp_4098_:
{
return v___x_4099_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_AttributeExtension_addImported___boxed(lean_object* v_es_4114_, lean_object* v_a_4115_, lean_object* v_a_4116_){
_start:
{
lean_object* v_res_4117_; 
v_res_4117_ = l___private_Lean_Attributes_0__Lean_AttributeExtension_addImported(v_es_4114_, v_a_4115_);
lean_dec_ref(v_a_4115_);
lean_dec_ref(v_es_4114_);
return v_res_4117_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0(lean_object* v_as_4118_, size_t v_i_4119_, size_t v_stop_4120_, lean_object* v_b_4121_, lean_object* v___y_4122_){
_start:
{
lean_object* v___x_4124_; 
v___x_4124_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg(v_as_4118_, v_i_4119_, v_stop_4120_, v_b_4121_);
return v___x_4124_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___boxed(lean_object* v_as_4125_, lean_object* v_i_4126_, lean_object* v_stop_4127_, lean_object* v_b_4128_, lean_object* v___y_4129_, lean_object* v___y_4130_){
_start:
{
size_t v_i_boxed_4131_; size_t v_stop_boxed_4132_; lean_object* v_res_4133_; 
v_i_boxed_4131_ = lean_unbox_usize(v_i_4126_);
lean_dec(v_i_4126_);
v_stop_boxed_4132_ = lean_unbox_usize(v_stop_4127_);
lean_dec(v_stop_4127_);
v_res_4133_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0(v_as_4125_, v_i_boxed_4131_, v_stop_boxed_4132_, v_b_4128_, v___y_4129_);
lean_dec_ref(v___y_4129_);
lean_dec_ref(v_as_4125_);
return v_res_4133_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_addAttrEntry(lean_object* v_s_4134_, lean_object* v_e_4135_){
_start:
{
lean_object* v_snd_4136_; lean_object* v_toAttributeImplCore_4137_; lean_object* v_fst_4138_; lean_object* v___x_4140_; uint8_t v_isShared_4141_; uint8_t v_isSharedCheck_4156_; 
v_snd_4136_ = lean_ctor_get(v_e_4135_, 1);
lean_inc(v_snd_4136_);
v_toAttributeImplCore_4137_ = lean_ctor_get(v_snd_4136_, 0);
v_fst_4138_ = lean_ctor_get(v_e_4135_, 0);
v_isSharedCheck_4156_ = !lean_is_exclusive(v_e_4135_);
if (v_isSharedCheck_4156_ == 0)
{
lean_object* v_unused_4157_; 
v_unused_4157_ = lean_ctor_get(v_e_4135_, 1);
lean_dec(v_unused_4157_);
v___x_4140_ = v_e_4135_;
v_isShared_4141_ = v_isSharedCheck_4156_;
goto v_resetjp_4139_;
}
else
{
lean_inc(v_fst_4138_);
lean_dec(v_e_4135_);
v___x_4140_ = lean_box(0);
v_isShared_4141_ = v_isSharedCheck_4156_;
goto v_resetjp_4139_;
}
v_resetjp_4139_:
{
lean_object* v_newEntries_4142_; lean_object* v_map_4143_; lean_object* v___x_4145_; uint8_t v_isShared_4146_; uint8_t v_isSharedCheck_4155_; 
v_newEntries_4142_ = lean_ctor_get(v_s_4134_, 0);
v_map_4143_ = lean_ctor_get(v_s_4134_, 1);
v_isSharedCheck_4155_ = !lean_is_exclusive(v_s_4134_);
if (v_isSharedCheck_4155_ == 0)
{
v___x_4145_ = v_s_4134_;
v_isShared_4146_ = v_isSharedCheck_4155_;
goto v_resetjp_4144_;
}
else
{
lean_inc(v_map_4143_);
lean_inc(v_newEntries_4142_);
lean_dec(v_s_4134_);
v___x_4145_ = lean_box(0);
v_isShared_4146_ = v_isSharedCheck_4155_;
goto v_resetjp_4144_;
}
v_resetjp_4144_:
{
lean_object* v_name_4147_; lean_object* v___x_4149_; 
v_name_4147_ = lean_ctor_get(v_toAttributeImplCore_4137_, 1);
lean_inc(v_name_4147_);
if (v_isShared_4141_ == 0)
{
lean_ctor_set_tag(v___x_4140_, 1);
lean_ctor_set(v___x_4140_, 1, v_newEntries_4142_);
v___x_4149_ = v___x_4140_;
goto v_reusejp_4148_;
}
else
{
lean_object* v_reuseFailAlloc_4154_; 
v_reuseFailAlloc_4154_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4154_, 0, v_fst_4138_);
lean_ctor_set(v_reuseFailAlloc_4154_, 1, v_newEntries_4142_);
v___x_4149_ = v_reuseFailAlloc_4154_;
goto v_reusejp_4148_;
}
v_reusejp_4148_:
{
lean_object* v___x_4150_; lean_object* v___x_4152_; 
v___x_4150_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1___redArg(v_map_4143_, v_name_4147_, v_snd_4136_);
if (v_isShared_4146_ == 0)
{
lean_ctor_set(v___x_4145_, 1, v___x_4150_);
lean_ctor_set(v___x_4145_, 0, v___x_4149_);
v___x_4152_ = v___x_4145_;
goto v_reusejp_4151_;
}
else
{
lean_object* v_reuseFailAlloc_4153_; 
v_reuseFailAlloc_4153_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4153_, 0, v___x_4149_);
lean_ctor_set(v_reuseFailAlloc_4153_, 1, v___x_4150_);
v___x_4152_ = v_reuseFailAlloc_4153_;
goto v_reusejp_4151_;
}
v_reusejp_4151_:
{
return v___x_4152_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn___lam__0_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(lean_object* v_x_4158_, lean_object* v_s_4159_){
_start:
{
lean_object* v_newEntries_4160_; lean_object* v___x_4161_; lean_object* v___x_4162_; lean_object* v___x_4163_; 
v_newEntries_4160_ = lean_ctor_get(v_s_4159_, 0);
lean_inc(v_newEntries_4160_);
lean_dec_ref(v_s_4159_);
v___x_4161_ = l_List_reverse___redArg(v_newEntries_4160_);
v___x_4162_ = lean_array_mk(v___x_4161_);
lean_inc_ref_n(v___x_4162_, 2);
v___x_4163_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4163_, 0, v___x_4162_);
lean_ctor_set(v___x_4163_, 1, v___x_4162_);
lean_ctor_set(v___x_4163_, 2, v___x_4162_);
return v___x_4163_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn___lam__0_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2____boxed(lean_object* v_x_4164_, lean_object* v_s_4165_){
_start:
{
lean_object* v_res_4166_; 
v_res_4166_ = l___private_Lean_Attributes_0__Lean_initFn___lam__0_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(v_x_4164_, v_s_4165_);
lean_dec_ref(v_x_4164_);
return v_res_4166_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn___lam__1_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(lean_object* v_s_4167_){
_start:
{
lean_object* v_newEntries_4168_; lean_object* v___x_4170_; uint8_t v_isShared_4171_; uint8_t v_isSharedCheck_4179_; 
v_newEntries_4168_ = lean_ctor_get(v_s_4167_, 0);
v_isSharedCheck_4179_ = !lean_is_exclusive(v_s_4167_);
if (v_isSharedCheck_4179_ == 0)
{
lean_object* v_unused_4180_; 
v_unused_4180_ = lean_ctor_get(v_s_4167_, 1);
lean_dec(v_unused_4180_);
v___x_4170_ = v_s_4167_;
v_isShared_4171_ = v_isSharedCheck_4179_;
goto v_resetjp_4169_;
}
else
{
lean_inc(v_newEntries_4168_);
lean_dec(v_s_4167_);
v___x_4170_ = lean_box(0);
v_isShared_4171_ = v_isSharedCheck_4179_;
goto v_resetjp_4169_;
}
v_resetjp_4169_:
{
lean_object* v___x_4172_; lean_object* v___x_4173_; lean_object* v___x_4174_; lean_object* v___x_4175_; lean_object* v___x_4177_; 
v___x_4172_ = ((lean_object*)(l_Lean_registerTagAttribute___lam__2___closed__4));
v___x_4173_ = l_List_lengthTR___redArg(v_newEntries_4168_);
lean_dec(v_newEntries_4168_);
v___x_4174_ = l_Nat_reprFast(v___x_4173_);
v___x_4175_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4175_, 0, v___x_4174_);
if (v_isShared_4171_ == 0)
{
lean_ctor_set_tag(v___x_4170_, 5);
lean_ctor_set(v___x_4170_, 1, v___x_4175_);
lean_ctor_set(v___x_4170_, 0, v___x_4172_);
v___x_4177_ = v___x_4170_;
goto v_reusejp_4176_;
}
else
{
lean_object* v_reuseFailAlloc_4178_; 
v_reuseFailAlloc_4178_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4178_, 0, v___x_4172_);
lean_ctor_set(v_reuseFailAlloc_4178_, 1, v___x_4175_);
v___x_4177_ = v_reuseFailAlloc_4178_;
goto v_reusejp_4176_;
}
v_reusejp_4176_:
{
return v___x_4177_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn___lam__2_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(lean_object* v_s_4181_){
_start:
{
lean_object* v_newEntries_4182_; lean_object* v___x_4183_; lean_object* v___x_4184_; 
v_newEntries_4182_ = lean_ctor_get(v_s_4181_, 0);
lean_inc(v_newEntries_4182_);
lean_dec_ref(v_s_4181_);
v___x_4183_ = l_List_reverse___redArg(v_newEntries_4182_);
v___x_4184_ = lean_array_mk(v___x_4183_);
return v___x_4184_;
}
}
static lean_object* _init_l___private_Lean_Attributes_0__Lean_initFn___closed__7_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4194_; lean_object* v___x_4195_; lean_object* v___f_4196_; lean_object* v___f_4197_; lean_object* v___x_4198_; lean_object* v___x_4199_; lean_object* v___x_4200_; lean_object* v___x_4201_; lean_object* v___x_4202_; 
v___x_4194_ = lean_box(0);
v___x_4195_ = lean_box(2);
v___f_4196_ = ((lean_object*)(l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___f_4197_ = ((lean_object*)(l___private_Lean_Attributes_0__Lean_initFn___closed__0_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___x_4198_ = ((lean_object*)(l___private_Lean_Attributes_0__Lean_initFn___closed__6_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___x_4199_ = ((lean_object*)(l___private_Lean_Attributes_0__Lean_initFn___closed__5_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___x_4200_ = lean_alloc_closure((void*)(l___private_Lean_Attributes_0__Lean_AttributeExtension_mkInitial___boxed), 1, 0);
v___x_4201_ = ((lean_object*)(l___private_Lean_Attributes_0__Lean_initFn___closed__4_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___x_4202_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_4202_, 0, v___x_4201_);
lean_ctor_set(v___x_4202_, 1, v___x_4200_);
lean_ctor_set(v___x_4202_, 2, v___x_4199_);
lean_ctor_set(v___x_4202_, 3, v___x_4198_);
lean_ctor_set(v___x_4202_, 4, v___f_4197_);
lean_ctor_set(v___x_4202_, 5, v___f_4196_);
lean_ctor_set(v___x_4202_, 6, v___x_4195_);
lean_ctor_set(v___x_4202_, 7, v___x_4194_);
return v___x_4202_;
}
}
static lean_object* _init_l___private_Lean_Attributes_0__Lean_initFn___closed__8_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_4203_; lean_object* v___x_4204_; lean_object* v___x_4205_; 
v___f_4203_ = ((lean_object*)(l___private_Lean_Attributes_0__Lean_initFn___closed__2_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___x_4204_ = lean_obj_once(&l___private_Lean_Attributes_0__Lean_initFn___closed__7_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_, &l___private_Lean_Attributes_0__Lean_initFn___closed__7_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2__once, _init_l___private_Lean_Attributes_0__Lean_initFn___closed__7_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_);
v___x_4205_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4205_, 0, v___x_4204_);
lean_ctor_set(v___x_4205_, 1, v___f_4203_);
return v___x_4205_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4207_; lean_object* v___x_4208_; 
v___x_4207_ = lean_obj_once(&l___private_Lean_Attributes_0__Lean_initFn___closed__8_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_, &l___private_Lean_Attributes_0__Lean_initFn___closed__8_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2__once, _init_l___private_Lean_Attributes_0__Lean_initFn___closed__8_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_);
v___x_4208_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_4207_);
return v___x_4208_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2____boxed(lean_object* v_a_4209_){
_start:
{
lean_object* v_res_4210_; 
v_res_4210_ = l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_();
return v_res_4210_;
}
}
LEAN_EXPORT lean_object* l_Lean_isBuiltinAttribute(lean_object* v_n_4211_){
_start:
{
lean_object* v___x_4213_; lean_object* v___x_4214_; uint8_t v___x_4215_; lean_object* v___x_4216_; lean_object* v___x_4217_; 
v___x_4213_ = l_Lean_attributeMapRef;
v___x_4214_ = lean_st_ref_get(v___x_4213_);
v___x_4215_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(v___x_4214_, v_n_4211_);
lean_dec(v___x_4214_);
v___x_4216_ = lean_box(v___x_4215_);
v___x_4217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4217_, 0, v___x_4216_);
return v___x_4217_;
}
}
LEAN_EXPORT lean_object* l_Lean_isBuiltinAttribute___boxed(lean_object* v_n_4218_, lean_object* v_a_4219_){
_start:
{
lean_object* v_res_4220_; 
v_res_4220_ = l_Lean_isBuiltinAttribute(v_n_4218_);
lean_dec(v_n_4218_);
return v_res_4220_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_getBuiltinAttributeNames_spec__0(lean_object* v_x_4221_, lean_object* v_x_4222_){
_start:
{
if (lean_obj_tag(v_x_4222_) == 0)
{
return v_x_4221_;
}
else
{
lean_object* v_key_4223_; lean_object* v_tail_4224_; lean_object* v___x_4225_; 
v_key_4223_ = lean_ctor_get(v_x_4222_, 0);
v_tail_4224_ = lean_ctor_get(v_x_4222_, 2);
lean_inc(v_key_4223_);
v___x_4225_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4225_, 0, v_key_4223_);
lean_ctor_set(v___x_4225_, 1, v_x_4221_);
v_x_4221_ = v___x_4225_;
v_x_4222_ = v_tail_4224_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_getBuiltinAttributeNames_spec__0___boxed(lean_object* v_x_4227_, lean_object* v_x_4228_){
_start:
{
lean_object* v_res_4229_; 
v_res_4229_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_getBuiltinAttributeNames_spec__0(v_x_4227_, v_x_4228_);
lean_dec(v_x_4228_);
return v_res_4229_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1(lean_object* v_as_4230_, size_t v_i_4231_, size_t v_stop_4232_, lean_object* v_b_4233_){
_start:
{
uint8_t v___x_4234_; 
v___x_4234_ = lean_usize_dec_eq(v_i_4231_, v_stop_4232_);
if (v___x_4234_ == 0)
{
lean_object* v___x_4235_; lean_object* v___x_4236_; size_t v___x_4237_; size_t v___x_4238_; 
v___x_4235_ = lean_array_uget_borrowed(v_as_4230_, v_i_4231_);
v___x_4236_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_getBuiltinAttributeNames_spec__0(v_b_4233_, v___x_4235_);
v___x_4237_ = ((size_t)1ULL);
v___x_4238_ = lean_usize_add(v_i_4231_, v___x_4237_);
v_i_4231_ = v___x_4238_;
v_b_4233_ = v___x_4236_;
goto _start;
}
else
{
return v_b_4233_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1___boxed(lean_object* v_as_4240_, lean_object* v_i_4241_, lean_object* v_stop_4242_, lean_object* v_b_4243_){
_start:
{
size_t v_i_boxed_4244_; size_t v_stop_boxed_4245_; lean_object* v_res_4246_; 
v_i_boxed_4244_ = lean_unbox_usize(v_i_4241_);
lean_dec(v_i_4241_);
v_stop_boxed_4245_ = lean_unbox_usize(v_stop_4242_);
lean_dec(v_stop_4242_);
v_res_4246_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1(v_as_4240_, v_i_boxed_4244_, v_stop_boxed_4245_, v_b_4243_);
lean_dec_ref(v_as_4240_);
return v_res_4246_;
}
}
LEAN_EXPORT lean_object* l_Lean_getBuiltinAttributeNames(){
_start:
{
lean_object* v___x_4248_; lean_object* v___x_4249_; lean_object* v_buckets_4250_; lean_object* v___x_4251_; lean_object* v___x_4252_; lean_object* v___x_4253_; uint8_t v___x_4254_; 
v___x_4248_ = l_Lean_attributeMapRef;
v___x_4249_ = lean_st_ref_get(v___x_4248_);
v_buckets_4250_ = lean_ctor_get(v___x_4249_, 1);
lean_inc_ref(v_buckets_4250_);
lean_dec(v___x_4249_);
v___x_4251_ = lean_box(0);
v___x_4252_ = lean_unsigned_to_nat(0u);
v___x_4253_ = lean_array_get_size(v_buckets_4250_);
v___x_4254_ = lean_nat_dec_lt(v___x_4252_, v___x_4253_);
if (v___x_4254_ == 0)
{
lean_object* v___x_4255_; 
lean_dec_ref(v_buckets_4250_);
v___x_4255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4255_, 0, v___x_4251_);
return v___x_4255_;
}
else
{
uint8_t v___x_4256_; 
v___x_4256_ = lean_nat_dec_le(v___x_4253_, v___x_4253_);
if (v___x_4256_ == 0)
{
if (v___x_4254_ == 0)
{
lean_object* v___x_4257_; 
lean_dec_ref(v_buckets_4250_);
v___x_4257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4257_, 0, v___x_4251_);
return v___x_4257_;
}
else
{
size_t v___x_4258_; size_t v___x_4259_; lean_object* v___x_4260_; lean_object* v___x_4261_; 
v___x_4258_ = ((size_t)0ULL);
v___x_4259_ = lean_usize_of_nat(v___x_4253_);
v___x_4260_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1(v_buckets_4250_, v___x_4258_, v___x_4259_, v___x_4251_);
lean_dec_ref(v_buckets_4250_);
v___x_4261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4261_, 0, v___x_4260_);
return v___x_4261_;
}
}
else
{
size_t v___x_4262_; size_t v___x_4263_; lean_object* v___x_4264_; lean_object* v___x_4265_; 
v___x_4262_ = ((size_t)0ULL);
v___x_4263_ = lean_usize_of_nat(v___x_4253_);
v___x_4264_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1(v_buckets_4250_, v___x_4262_, v___x_4263_, v___x_4251_);
lean_dec_ref(v_buckets_4250_);
v___x_4265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4265_, 0, v___x_4264_);
return v___x_4265_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getBuiltinAttributeNames___boxed(lean_object* v_a_4266_){
_start:
{
lean_object* v_res_4267_; 
v_res_4267_ = l_Lean_getBuiltinAttributeNames();
return v_res_4267_;
}
}
LEAN_EXPORT lean_object* l_Lean_getBuiltinAttributeImpl(lean_object* v_attrName_4269_){
_start:
{
lean_object* v___x_4271_; lean_object* v___x_4272_; lean_object* v___x_4273_; 
v___x_4271_ = l_Lean_attributeMapRef;
v___x_4272_ = lean_st_ref_get(v___x_4271_);
v___x_4273_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(v___x_4272_, v_attrName_4269_);
lean_dec(v___x_4272_);
if (lean_obj_tag(v___x_4273_) == 0)
{
lean_object* v___x_4274_; uint8_t v___x_4275_; lean_object* v___x_4276_; lean_object* v___x_4277_; lean_object* v___x_4278_; lean_object* v___x_4279_; lean_object* v___x_4280_; lean_object* v___x_4281_; 
v___x_4274_ = ((lean_object*)(l_Lean_getBuiltinAttributeImpl___closed__0));
v___x_4275_ = 1;
v___x_4276_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_attrName_4269_, v___x_4275_);
v___x_4277_ = lean_string_append(v___x_4274_, v___x_4276_);
lean_dec_ref(v___x_4276_);
v___x_4278_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__4));
v___x_4279_ = lean_string_append(v___x_4277_, v___x_4278_);
v___x_4280_ = lean_mk_io_user_error(v___x_4279_);
v___x_4281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4281_, 0, v___x_4280_);
return v___x_4281_;
}
else
{
lean_object* v_val_4282_; lean_object* v___x_4284_; uint8_t v_isShared_4285_; uint8_t v_isSharedCheck_4289_; 
lean_dec(v_attrName_4269_);
v_val_4282_ = lean_ctor_get(v___x_4273_, 0);
v_isSharedCheck_4289_ = !lean_is_exclusive(v___x_4273_);
if (v_isSharedCheck_4289_ == 0)
{
v___x_4284_ = v___x_4273_;
v_isShared_4285_ = v_isSharedCheck_4289_;
goto v_resetjp_4283_;
}
else
{
lean_inc(v_val_4282_);
lean_dec(v___x_4273_);
v___x_4284_ = lean_box(0);
v_isShared_4285_ = v_isSharedCheck_4289_;
goto v_resetjp_4283_;
}
v_resetjp_4283_:
{
lean_object* v___x_4287_; 
if (v_isShared_4285_ == 0)
{
lean_ctor_set_tag(v___x_4284_, 0);
v___x_4287_ = v___x_4284_;
goto v_reusejp_4286_;
}
else
{
lean_object* v_reuseFailAlloc_4288_; 
v_reuseFailAlloc_4288_ = lean_alloc_ctor(0, 1, 0);
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
LEAN_EXPORT lean_object* l_Lean_getBuiltinAttributeImpl___boxed(lean_object* v_attrName_4290_, lean_object* v_a_4291_){
_start:
{
lean_object* v_res_4292_; 
v_res_4292_ = l_Lean_getBuiltinAttributeImpl(v_attrName_4290_);
return v_res_4292_;
}
}
LEAN_EXPORT uint8_t l_Lean_isAttribute(lean_object* v_env_4293_, lean_object* v_attrName_4294_){
_start:
{
lean_object* v___x_4295_; lean_object* v_toEnvExtension_4296_; lean_object* v_asyncMode_4297_; lean_object* v___x_4298_; lean_object* v___x_4299_; lean_object* v___x_4300_; lean_object* v_map_4301_; uint8_t v___x_4302_; 
v___x_4295_ = l_Lean_attributeExtension;
v_toEnvExtension_4296_ = lean_ctor_get(v___x_4295_, 0);
v_asyncMode_4297_ = lean_ctor_get(v_toEnvExtension_4296_, 2);
v___x_4298_ = l_Lean_instInhabitedAttributeExtensionState_default;
v___x_4299_ = lean_box(0);
v___x_4300_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_4298_, v___x_4295_, v_env_4293_, v_asyncMode_4297_, v___x_4299_);
v_map_4301_ = lean_ctor_get(v___x_4300_, 1);
lean_inc_ref(v_map_4301_);
lean_dec(v___x_4300_);
v___x_4302_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(v_map_4301_, v_attrName_4294_);
lean_dec_ref(v_map_4301_);
return v___x_4302_;
}
}
LEAN_EXPORT lean_object* l_Lean_isAttribute___boxed(lean_object* v_env_4303_, lean_object* v_attrName_4304_){
_start:
{
uint8_t v_res_4305_; lean_object* v_r_4306_; 
v_res_4305_ = l_Lean_isAttribute(v_env_4303_, v_attrName_4304_);
lean_dec(v_attrName_4304_);
v_r_4306_ = lean_box(v_res_4305_);
return v_r_4306_;
}
}
LEAN_EXPORT lean_object* l_Lean_getAttributeNames(lean_object* v_env_4307_){
_start:
{
lean_object* v___x_4308_; lean_object* v_toEnvExtension_4309_; lean_object* v_asyncMode_4310_; lean_object* v___x_4311_; lean_object* v___x_4312_; lean_object* v___x_4313_; lean_object* v_map_4314_; lean_object* v_buckets_4315_; lean_object* v___x_4316_; lean_object* v___x_4317_; lean_object* v___x_4318_; uint8_t v___x_4319_; 
v___x_4308_ = l_Lean_attributeExtension;
v_toEnvExtension_4309_ = lean_ctor_get(v___x_4308_, 0);
v_asyncMode_4310_ = lean_ctor_get(v_toEnvExtension_4309_, 2);
v___x_4311_ = l_Lean_instInhabitedAttributeExtensionState_default;
v___x_4312_ = lean_box(0);
v___x_4313_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_4311_, v___x_4308_, v_env_4307_, v_asyncMode_4310_, v___x_4312_);
v_map_4314_ = lean_ctor_get(v___x_4313_, 1);
lean_inc_ref(v_map_4314_);
lean_dec(v___x_4313_);
v_buckets_4315_ = lean_ctor_get(v_map_4314_, 1);
lean_inc_ref(v_buckets_4315_);
lean_dec_ref(v_map_4314_);
v___x_4316_ = lean_box(0);
v___x_4317_ = lean_unsigned_to_nat(0u);
v___x_4318_ = lean_array_get_size(v_buckets_4315_);
v___x_4319_ = lean_nat_dec_lt(v___x_4317_, v___x_4318_);
if (v___x_4319_ == 0)
{
lean_dec_ref(v_buckets_4315_);
return v___x_4316_;
}
else
{
uint8_t v___x_4320_; 
v___x_4320_ = lean_nat_dec_le(v___x_4318_, v___x_4318_);
if (v___x_4320_ == 0)
{
if (v___x_4319_ == 0)
{
lean_dec_ref(v_buckets_4315_);
return v___x_4316_;
}
else
{
size_t v___x_4321_; size_t v___x_4322_; lean_object* v___x_4323_; 
v___x_4321_ = ((size_t)0ULL);
v___x_4322_ = lean_usize_of_nat(v___x_4318_);
v___x_4323_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1(v_buckets_4315_, v___x_4321_, v___x_4322_, v___x_4316_);
lean_dec_ref(v_buckets_4315_);
return v___x_4323_;
}
}
else
{
size_t v___x_4324_; size_t v___x_4325_; lean_object* v___x_4326_; 
v___x_4324_ = ((size_t)0ULL);
v___x_4325_ = lean_usize_of_nat(v___x_4318_);
v___x_4326_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1(v_buckets_4315_, v___x_4324_, v___x_4325_, v___x_4316_);
lean_dec_ref(v_buckets_4315_);
return v___x_4326_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getAttributeImpl(lean_object* v_env_4327_, lean_object* v_attrName_4328_){
_start:
{
lean_object* v___x_4329_; lean_object* v_toEnvExtension_4330_; lean_object* v_asyncMode_4331_; lean_object* v___x_4332_; lean_object* v___x_4333_; lean_object* v___x_4334_; lean_object* v_map_4335_; lean_object* v___x_4336_; 
v___x_4329_ = l_Lean_attributeExtension;
v_toEnvExtension_4330_ = lean_ctor_get(v___x_4329_, 0);
v_asyncMode_4331_ = lean_ctor_get(v_toEnvExtension_4330_, 2);
v___x_4332_ = l_Lean_instInhabitedAttributeExtensionState_default;
v___x_4333_ = lean_box(0);
v___x_4334_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_4332_, v___x_4329_, v_env_4327_, v_asyncMode_4331_, v___x_4333_);
v_map_4335_ = lean_ctor_get(v___x_4334_, 1);
lean_inc_ref(v_map_4335_);
lean_dec(v___x_4334_);
v___x_4336_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(v_map_4335_, v_attrName_4328_);
lean_dec_ref(v_map_4335_);
if (lean_obj_tag(v___x_4336_) == 0)
{
lean_object* v___x_4337_; uint8_t v___x_4338_; lean_object* v___x_4339_; lean_object* v___x_4340_; lean_object* v___x_4341_; lean_object* v___x_4342_; lean_object* v___x_4343_; 
v___x_4337_ = ((lean_object*)(l_Lean_getBuiltinAttributeImpl___closed__0));
v___x_4338_ = 1;
v___x_4339_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_attrName_4328_, v___x_4338_);
v___x_4340_ = lean_string_append(v___x_4337_, v___x_4339_);
lean_dec_ref(v___x_4339_);
v___x_4341_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__4));
v___x_4342_ = lean_string_append(v___x_4340_, v___x_4341_);
v___x_4343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4343_, 0, v___x_4342_);
return v___x_4343_;
}
else
{
lean_object* v_val_4344_; lean_object* v___x_4346_; uint8_t v_isShared_4347_; uint8_t v_isSharedCheck_4351_; 
lean_dec(v_attrName_4328_);
v_val_4344_ = lean_ctor_get(v___x_4336_, 0);
v_isSharedCheck_4351_ = !lean_is_exclusive(v___x_4336_);
if (v_isSharedCheck_4351_ == 0)
{
v___x_4346_ = v___x_4336_;
v_isShared_4347_ = v_isSharedCheck_4351_;
goto v_resetjp_4345_;
}
else
{
lean_inc(v_val_4344_);
lean_dec(v___x_4336_);
v___x_4346_ = lean_box(0);
v_isShared_4347_ = v_isSharedCheck_4351_;
goto v_resetjp_4345_;
}
v_resetjp_4345_:
{
lean_object* v___x_4349_; 
if (v_isShared_4347_ == 0)
{
v___x_4349_ = v___x_4346_;
goto v_reusejp_4348_;
}
else
{
lean_object* v_reuseFailAlloc_4350_; 
v_reuseFailAlloc_4350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4350_, 0, v_val_4344_);
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
LEAN_EXPORT lean_object* l_Lean_registerAttributeOfBuilder(lean_object* v_env_4352_, lean_object* v_builderId_4353_, lean_object* v_ref_4354_, lean_object* v_args_4355_){
_start:
{
lean_object* v_entry_4357_; lean_object* v___x_4358_; 
v_entry_4357_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_entry_4357_, 0, v_builderId_4353_);
lean_ctor_set(v_entry_4357_, 1, v_ref_4354_);
lean_ctor_set(v_entry_4357_, 2, v_args_4355_);
lean_inc_ref(v_entry_4357_);
v___x_4358_ = l_Lean_mkAttributeImplOfEntry(v_entry_4357_);
if (lean_obj_tag(v___x_4358_) == 0)
{
lean_object* v_a_4359_; lean_object* v___x_4361_; uint8_t v_isShared_4362_; uint8_t v_isSharedCheck_4384_; 
v_a_4359_ = lean_ctor_get(v___x_4358_, 0);
v_isSharedCheck_4384_ = !lean_is_exclusive(v___x_4358_);
if (v_isSharedCheck_4384_ == 0)
{
v___x_4361_ = v___x_4358_;
v_isShared_4362_ = v_isSharedCheck_4384_;
goto v_resetjp_4360_;
}
else
{
lean_inc(v_a_4359_);
lean_dec(v___x_4358_);
v___x_4361_ = lean_box(0);
v_isShared_4362_ = v_isSharedCheck_4384_;
goto v_resetjp_4360_;
}
v_resetjp_4360_:
{
lean_object* v_toAttributeImplCore_4363_; lean_object* v_name_4364_; uint8_t v___x_4365_; 
v_toAttributeImplCore_4363_ = lean_ctor_get(v_a_4359_, 0);
v_name_4364_ = lean_ctor_get(v_toAttributeImplCore_4363_, 1);
lean_inc_ref(v_env_4352_);
v___x_4365_ = l_Lean_isAttribute(v_env_4352_, v_name_4364_);
if (v___x_4365_ == 0)
{
lean_object* v___x_4366_; lean_object* v_toEnvExtension_4367_; lean_object* v_asyncMode_4368_; lean_object* v___x_4369_; lean_object* v___x_4370_; lean_object* v___x_4371_; lean_object* v___x_4373_; 
v___x_4366_ = l_Lean_attributeExtension;
v_toEnvExtension_4367_ = lean_ctor_get(v___x_4366_, 0);
v_asyncMode_4368_ = lean_ctor_get(v_toEnvExtension_4367_, 2);
v___x_4369_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4369_, 0, v_entry_4357_);
lean_ctor_set(v___x_4369_, 1, v_a_4359_);
v___x_4370_ = lean_box(0);
v___x_4371_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_4366_, v_env_4352_, v___x_4369_, v_asyncMode_4368_, v___x_4370_);
if (v_isShared_4362_ == 0)
{
lean_ctor_set(v___x_4361_, 0, v___x_4371_);
v___x_4373_ = v___x_4361_;
goto v_reusejp_4372_;
}
else
{
lean_object* v_reuseFailAlloc_4374_; 
v_reuseFailAlloc_4374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4374_, 0, v___x_4371_);
v___x_4373_ = v_reuseFailAlloc_4374_;
goto v_reusejp_4372_;
}
v_reusejp_4372_:
{
return v___x_4373_;
}
}
else
{
lean_object* v___x_4375_; lean_object* v___x_4376_; lean_object* v___x_4377_; lean_object* v___x_4378_; lean_object* v___x_4379_; lean_object* v___x_4380_; lean_object* v___x_4382_; 
lean_inc(v_name_4364_);
lean_dec(v_a_4359_);
lean_dec_ref_known(v_entry_4357_, 3);
lean_dec_ref(v_env_4352_);
v___x_4375_ = ((lean_object*)(l_Lean_registerBuiltinAttribute___closed__2));
v___x_4376_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_4364_, v___x_4365_);
v___x_4377_ = lean_string_append(v___x_4375_, v___x_4376_);
lean_dec_ref(v___x_4376_);
v___x_4378_ = ((lean_object*)(l_Lean_registerBuiltinAttribute___closed__3));
v___x_4379_ = lean_string_append(v___x_4377_, v___x_4378_);
v___x_4380_ = lean_mk_io_user_error(v___x_4379_);
if (v_isShared_4362_ == 0)
{
lean_ctor_set_tag(v___x_4361_, 1);
lean_ctor_set(v___x_4361_, 0, v___x_4380_);
v___x_4382_ = v___x_4361_;
goto v_reusejp_4381_;
}
else
{
lean_object* v_reuseFailAlloc_4383_; 
v_reuseFailAlloc_4383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4383_, 0, v___x_4380_);
v___x_4382_ = v_reuseFailAlloc_4383_;
goto v_reusejp_4381_;
}
v_reusejp_4381_:
{
return v___x_4382_;
}
}
}
}
else
{
lean_object* v_a_4385_; lean_object* v___x_4387_; uint8_t v_isShared_4388_; uint8_t v_isSharedCheck_4392_; 
lean_dec_ref_known(v_entry_4357_, 3);
lean_dec_ref(v_env_4352_);
v_a_4385_ = lean_ctor_get(v___x_4358_, 0);
v_isSharedCheck_4392_ = !lean_is_exclusive(v___x_4358_);
if (v_isSharedCheck_4392_ == 0)
{
v___x_4387_ = v___x_4358_;
v_isShared_4388_ = v_isSharedCheck_4392_;
goto v_resetjp_4386_;
}
else
{
lean_inc(v_a_4385_);
lean_dec(v___x_4358_);
v___x_4387_ = lean_box(0);
v_isShared_4388_ = v_isSharedCheck_4392_;
goto v_resetjp_4386_;
}
v_resetjp_4386_:
{
lean_object* v___x_4390_; 
if (v_isShared_4388_ == 0)
{
v___x_4390_ = v___x_4387_;
goto v_reusejp_4389_;
}
else
{
lean_object* v_reuseFailAlloc_4391_; 
v_reuseFailAlloc_4391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4391_, 0, v_a_4385_);
v___x_4390_ = v_reuseFailAlloc_4391_;
goto v_reusejp_4389_;
}
v_reusejp_4389_:
{
return v___x_4390_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerAttributeOfBuilder___boxed(lean_object* v_env_4393_, lean_object* v_builderId_4394_, lean_object* v_ref_4395_, lean_object* v_args_4396_, lean_object* v_a_4397_){
_start:
{
lean_object* v_res_4398_; 
v_res_4398_ = l_Lean_registerAttributeOfBuilder(v_env_4393_, v_builderId_4394_, v_ref_4395_, v_args_4396_);
return v_res_4398_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg(lean_object* v_x_4399_, lean_object* v___y_4400_, lean_object* v___y_4401_){
_start:
{
if (lean_obj_tag(v_x_4399_) == 0)
{
lean_object* v_a_4403_; lean_object* v___x_4404_; lean_object* v___x_4405_; 
v_a_4403_ = lean_ctor_get(v_x_4399_, 0);
lean_inc(v_a_4403_);
lean_dec_ref_known(v_x_4399_, 1);
v___x_4404_ = l_Lean_stringToMessageData(v_a_4403_);
v___x_4405_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_4404_, v___y_4400_, v___y_4401_);
return v___x_4405_;
}
else
{
lean_object* v_a_4406_; lean_object* v___x_4408_; uint8_t v_isShared_4409_; uint8_t v_isSharedCheck_4413_; 
v_a_4406_ = lean_ctor_get(v_x_4399_, 0);
v_isSharedCheck_4413_ = !lean_is_exclusive(v_x_4399_);
if (v_isSharedCheck_4413_ == 0)
{
v___x_4408_ = v_x_4399_;
v_isShared_4409_ = v_isSharedCheck_4413_;
goto v_resetjp_4407_;
}
else
{
lean_inc(v_a_4406_);
lean_dec(v_x_4399_);
v___x_4408_ = lean_box(0);
v_isShared_4409_ = v_isSharedCheck_4413_;
goto v_resetjp_4407_;
}
v_resetjp_4407_:
{
lean_object* v___x_4411_; 
if (v_isShared_4409_ == 0)
{
lean_ctor_set_tag(v___x_4408_, 0);
v___x_4411_ = v___x_4408_;
goto v_reusejp_4410_;
}
else
{
lean_object* v_reuseFailAlloc_4412_; 
v_reuseFailAlloc_4412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4412_, 0, v_a_4406_);
v___x_4411_ = v_reuseFailAlloc_4412_;
goto v_reusejp_4410_;
}
v_reusejp_4410_:
{
return v___x_4411_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg___boxed(lean_object* v_x_4414_, lean_object* v___y_4415_, lean_object* v___y_4416_, lean_object* v___y_4417_){
_start:
{
lean_object* v_res_4418_; 
v_res_4418_ = l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg(v_x_4414_, v___y_4415_, v___y_4416_);
lean_dec(v___y_4416_);
lean_dec_ref(v___y_4415_);
return v_res_4418_;
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_add(lean_object* v_declName_4419_, lean_object* v_attrName_4420_, lean_object* v_stx_4421_, uint8_t v_kind_4422_, lean_object* v_a_4423_, lean_object* v_a_4424_){
_start:
{
lean_object* v___x_4426_; lean_object* v_env_4427_; lean_object* v___x_4428_; lean_object* v___x_4429_; 
v___x_4426_ = lean_st_ref_get(v_a_4424_);
v_env_4427_ = lean_ctor_get(v___x_4426_, 0);
lean_inc_ref(v_env_4427_);
lean_dec(v___x_4426_);
v___x_4428_ = l_Lean_getAttributeImpl(v_env_4427_, v_attrName_4420_);
v___x_4429_ = l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg(v___x_4428_, v_a_4423_, v_a_4424_);
if (lean_obj_tag(v___x_4429_) == 0)
{
lean_object* v_a_4430_; lean_object* v_add_4431_; lean_object* v___x_4432_; lean_object* v___x_4433_; 
v_a_4430_ = lean_ctor_get(v___x_4429_, 0);
lean_inc(v_a_4430_);
lean_dec_ref_known(v___x_4429_, 1);
v_add_4431_ = lean_ctor_get(v_a_4430_, 1);
lean_inc_ref(v_add_4431_);
lean_dec(v_a_4430_);
v___x_4432_ = lean_box(v_kind_4422_);
lean_inc(v_a_4424_);
lean_inc_ref(v_a_4423_);
v___x_4433_ = lean_apply_6(v_add_4431_, v_declName_4419_, v_stx_4421_, v___x_4432_, v_a_4423_, v_a_4424_, lean_box(0));
return v___x_4433_;
}
else
{
lean_object* v_a_4434_; lean_object* v___x_4436_; uint8_t v_isShared_4437_; uint8_t v_isSharedCheck_4441_; 
lean_dec(v_stx_4421_);
lean_dec(v_declName_4419_);
v_a_4434_ = lean_ctor_get(v___x_4429_, 0);
v_isSharedCheck_4441_ = !lean_is_exclusive(v___x_4429_);
if (v_isSharedCheck_4441_ == 0)
{
v___x_4436_ = v___x_4429_;
v_isShared_4437_ = v_isSharedCheck_4441_;
goto v_resetjp_4435_;
}
else
{
lean_inc(v_a_4434_);
lean_dec(v___x_4429_);
v___x_4436_ = lean_box(0);
v_isShared_4437_ = v_isSharedCheck_4441_;
goto v_resetjp_4435_;
}
v_resetjp_4435_:
{
lean_object* v___x_4439_; 
if (v_isShared_4437_ == 0)
{
v___x_4439_ = v___x_4436_;
goto v_reusejp_4438_;
}
else
{
lean_object* v_reuseFailAlloc_4440_; 
v_reuseFailAlloc_4440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4440_, 0, v_a_4434_);
v___x_4439_ = v_reuseFailAlloc_4440_;
goto v_reusejp_4438_;
}
v_reusejp_4438_:
{
return v___x_4439_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_add___boxed(lean_object* v_declName_4442_, lean_object* v_attrName_4443_, lean_object* v_stx_4444_, lean_object* v_kind_4445_, lean_object* v_a_4446_, lean_object* v_a_4447_, lean_object* v_a_4448_){
_start:
{
uint8_t v_kind_boxed_4449_; lean_object* v_res_4450_; 
v_kind_boxed_4449_ = lean_unbox(v_kind_4445_);
v_res_4450_ = l_Lean_Attribute_add(v_declName_4442_, v_attrName_4443_, v_stx_4444_, v_kind_boxed_4449_, v_a_4446_, v_a_4447_);
lean_dec(v_a_4447_);
lean_dec_ref(v_a_4446_);
return v_res_4450_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0(lean_object* v_00_u03b1_4451_, lean_object* v_x_4452_, lean_object* v___y_4453_, lean_object* v___y_4454_){
_start:
{
lean_object* v___x_4456_; 
v___x_4456_ = l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg(v_x_4452_, v___y_4453_, v___y_4454_);
return v___x_4456_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___boxed(lean_object* v_00_u03b1_4457_, lean_object* v_x_4458_, lean_object* v___y_4459_, lean_object* v___y_4460_, lean_object* v___y_4461_){
_start:
{
lean_object* v_res_4462_; 
v_res_4462_ = l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0(v_00_u03b1_4457_, v_x_4458_, v___y_4459_, v___y_4460_);
lean_dec(v___y_4460_);
lean_dec_ref(v___y_4459_);
return v_res_4462_;
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_erase(lean_object* v_declName_4463_, lean_object* v_attrName_4464_, lean_object* v_a_4465_, lean_object* v_a_4466_){
_start:
{
lean_object* v___x_4468_; lean_object* v_env_4469_; lean_object* v___x_4470_; lean_object* v___x_4471_; 
v___x_4468_ = lean_st_ref_get(v_a_4466_);
v_env_4469_ = lean_ctor_get(v___x_4468_, 0);
lean_inc_ref(v_env_4469_);
lean_dec(v___x_4468_);
v___x_4470_ = l_Lean_getAttributeImpl(v_env_4469_, v_attrName_4464_);
v___x_4471_ = l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg(v___x_4470_, v_a_4465_, v_a_4466_);
if (lean_obj_tag(v___x_4471_) == 0)
{
lean_object* v_a_4472_; lean_object* v_erase_4473_; lean_object* v___x_4474_; 
v_a_4472_ = lean_ctor_get(v___x_4471_, 0);
lean_inc(v_a_4472_);
lean_dec_ref_known(v___x_4471_, 1);
v_erase_4473_ = lean_ctor_get(v_a_4472_, 2);
lean_inc_ref(v_erase_4473_);
lean_dec(v_a_4472_);
lean_inc(v_a_4466_);
lean_inc_ref(v_a_4465_);
v___x_4474_ = lean_apply_4(v_erase_4473_, v_declName_4463_, v_a_4465_, v_a_4466_, lean_box(0));
return v___x_4474_;
}
else
{
lean_object* v_a_4475_; lean_object* v___x_4477_; uint8_t v_isShared_4478_; uint8_t v_isSharedCheck_4482_; 
lean_dec(v_declName_4463_);
v_a_4475_ = lean_ctor_get(v___x_4471_, 0);
v_isSharedCheck_4482_ = !lean_is_exclusive(v___x_4471_);
if (v_isSharedCheck_4482_ == 0)
{
v___x_4477_ = v___x_4471_;
v_isShared_4478_ = v_isSharedCheck_4482_;
goto v_resetjp_4476_;
}
else
{
lean_inc(v_a_4475_);
lean_dec(v___x_4471_);
v___x_4477_ = lean_box(0);
v_isShared_4478_ = v_isSharedCheck_4482_;
goto v_resetjp_4476_;
}
v_resetjp_4476_:
{
lean_object* v___x_4480_; 
if (v_isShared_4478_ == 0)
{
v___x_4480_ = v___x_4477_;
goto v_reusejp_4479_;
}
else
{
lean_object* v_reuseFailAlloc_4481_; 
v_reuseFailAlloc_4481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4481_, 0, v_a_4475_);
v___x_4480_ = v_reuseFailAlloc_4481_;
goto v_reusejp_4479_;
}
v_reusejp_4479_:
{
return v___x_4480_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_erase___boxed(lean_object* v_declName_4483_, lean_object* v_attrName_4484_, lean_object* v_a_4485_, lean_object* v_a_4486_, lean_object* v_a_4487_){
_start:
{
lean_object* v_res_4488_; 
v_res_4488_ = l_Lean_Attribute_erase(v_declName_4483_, v_attrName_4484_, v_a_4485_, v_a_4486_);
lean_dec(v_a_4486_);
lean_dec_ref(v_a_4485_);
return v_res_4488_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_updateEnvAttributesImpl_spec__0(lean_object* v_x_4489_, lean_object* v_x_4490_){
_start:
{
if (lean_obj_tag(v_x_4490_) == 0)
{
return v_x_4489_;
}
else
{
lean_object* v_key_4491_; lean_object* v_value_4492_; lean_object* v_tail_4493_; lean_object* v_newEntries_4494_; lean_object* v_map_4495_; uint8_t v___x_4496_; 
v_key_4491_ = lean_ctor_get(v_x_4490_, 0);
lean_inc(v_key_4491_);
v_value_4492_ = lean_ctor_get(v_x_4490_, 1);
lean_inc(v_value_4492_);
v_tail_4493_ = lean_ctor_get(v_x_4490_, 2);
lean_inc(v_tail_4493_);
lean_dec_ref_known(v_x_4490_, 3);
v_newEntries_4494_ = lean_ctor_get(v_x_4489_, 0);
v_map_4495_ = lean_ctor_get(v_x_4489_, 1);
v___x_4496_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(v_map_4495_, v_key_4491_);
if (v___x_4496_ == 0)
{
lean_object* v___x_4498_; uint8_t v_isShared_4499_; uint8_t v_isSharedCheck_4505_; 
lean_inc_ref(v_map_4495_);
lean_inc(v_newEntries_4494_);
v_isSharedCheck_4505_ = !lean_is_exclusive(v_x_4489_);
if (v_isSharedCheck_4505_ == 0)
{
lean_object* v_unused_4506_; lean_object* v_unused_4507_; 
v_unused_4506_ = lean_ctor_get(v_x_4489_, 1);
lean_dec(v_unused_4506_);
v_unused_4507_ = lean_ctor_get(v_x_4489_, 0);
lean_dec(v_unused_4507_);
v___x_4498_ = v_x_4489_;
v_isShared_4499_ = v_isSharedCheck_4505_;
goto v_resetjp_4497_;
}
else
{
lean_dec(v_x_4489_);
v___x_4498_ = lean_box(0);
v_isShared_4499_ = v_isSharedCheck_4505_;
goto v_resetjp_4497_;
}
v_resetjp_4497_:
{
lean_object* v___x_4500_; lean_object* v___x_4502_; 
v___x_4500_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1___redArg(v_map_4495_, v_key_4491_, v_value_4492_);
if (v_isShared_4499_ == 0)
{
lean_ctor_set(v___x_4498_, 1, v___x_4500_);
v___x_4502_ = v___x_4498_;
goto v_reusejp_4501_;
}
else
{
lean_object* v_reuseFailAlloc_4504_; 
v_reuseFailAlloc_4504_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4504_, 0, v_newEntries_4494_);
lean_ctor_set(v_reuseFailAlloc_4504_, 1, v___x_4500_);
v___x_4502_ = v_reuseFailAlloc_4504_;
goto v_reusejp_4501_;
}
v_reusejp_4501_:
{
v_x_4489_ = v___x_4502_;
v_x_4490_ = v_tail_4493_;
goto _start;
}
}
}
else
{
lean_dec(v_value_4492_);
lean_dec(v_key_4491_);
v_x_4490_ = v_tail_4493_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_updateEnvAttributesImpl_spec__1(lean_object* v_as_4509_, size_t v_i_4510_, size_t v_stop_4511_, lean_object* v_b_4512_){
_start:
{
uint8_t v___x_4513_; 
v___x_4513_ = lean_usize_dec_eq(v_i_4510_, v_stop_4511_);
if (v___x_4513_ == 0)
{
lean_object* v___x_4514_; lean_object* v___x_4515_; size_t v___x_4516_; size_t v___x_4517_; 
v___x_4514_ = lean_array_uget_borrowed(v_as_4509_, v_i_4510_);
lean_inc(v___x_4514_);
v___x_4515_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_updateEnvAttributesImpl_spec__0(v_b_4512_, v___x_4514_);
v___x_4516_ = ((size_t)1ULL);
v___x_4517_ = lean_usize_add(v_i_4510_, v___x_4516_);
v_i_4510_ = v___x_4517_;
v_b_4512_ = v___x_4515_;
goto _start;
}
else
{
return v_b_4512_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_updateEnvAttributesImpl_spec__1___boxed(lean_object* v_as_4519_, lean_object* v_i_4520_, lean_object* v_stop_4521_, lean_object* v_b_4522_){
_start:
{
size_t v_i_boxed_4523_; size_t v_stop_boxed_4524_; lean_object* v_res_4525_; 
v_i_boxed_4523_ = lean_unbox_usize(v_i_4520_);
lean_dec(v_i_4520_);
v_stop_boxed_4524_ = lean_unbox_usize(v_stop_4521_);
lean_dec(v_stop_4521_);
v_res_4525_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_updateEnvAttributesImpl_spec__1(v_as_4519_, v_i_boxed_4523_, v_stop_boxed_4524_, v_b_4522_);
lean_dec_ref(v_as_4519_);
return v_res_4525_;
}
}
LEAN_EXPORT lean_object* lean_update_env_attributes(lean_object* v_env_4526_){
_start:
{
lean_object* v___x_4528_; lean_object* v___x_4529_; lean_object* v___x_4530_; lean_object* v___y_4532_; lean_object* v_toEnvExtension_4535_; lean_object* v_asyncMode_4536_; lean_object* v_buckets_4537_; lean_object* v___x_4538_; lean_object* v___x_4539_; lean_object* v___x_4540_; lean_object* v___x_4541_; lean_object* v___x_4542_; uint8_t v___x_4543_; 
v___x_4528_ = l_Lean_attributeMapRef;
v___x_4529_ = lean_st_ref_get(v___x_4528_);
v___x_4530_ = l_Lean_attributeExtension;
v_toEnvExtension_4535_ = lean_ctor_get(v___x_4530_, 0);
v_asyncMode_4536_ = lean_ctor_get(v_toEnvExtension_4535_, 2);
v_buckets_4537_ = lean_ctor_get(v___x_4529_, 1);
lean_inc_ref(v_buckets_4537_);
lean_dec(v___x_4529_);
v___x_4538_ = l_Lean_instInhabitedAttributeExtensionState_default;
v___x_4539_ = lean_box(0);
lean_inc_ref(v_env_4526_);
v___x_4540_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_4538_, v___x_4530_, v_env_4526_, v_asyncMode_4536_, v___x_4539_);
v___x_4541_ = lean_unsigned_to_nat(0u);
v___x_4542_ = lean_array_get_size(v_buckets_4537_);
v___x_4543_ = lean_nat_dec_lt(v___x_4541_, v___x_4542_);
if (v___x_4543_ == 0)
{
lean_dec_ref(v_buckets_4537_);
v___y_4532_ = v___x_4540_;
goto v___jp_4531_;
}
else
{
uint8_t v___x_4544_; 
v___x_4544_ = lean_nat_dec_le(v___x_4542_, v___x_4542_);
if (v___x_4544_ == 0)
{
if (v___x_4543_ == 0)
{
lean_dec_ref(v_buckets_4537_);
v___y_4532_ = v___x_4540_;
goto v___jp_4531_;
}
else
{
size_t v___x_4545_; size_t v___x_4546_; lean_object* v___x_4547_; 
v___x_4545_ = ((size_t)0ULL);
v___x_4546_ = lean_usize_of_nat(v___x_4542_);
v___x_4547_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_updateEnvAttributesImpl_spec__1(v_buckets_4537_, v___x_4545_, v___x_4546_, v___x_4540_);
lean_dec_ref(v_buckets_4537_);
v___y_4532_ = v___x_4547_;
goto v___jp_4531_;
}
}
else
{
size_t v___x_4548_; size_t v___x_4549_; lean_object* v___x_4550_; 
v___x_4548_ = ((size_t)0ULL);
v___x_4549_ = lean_usize_of_nat(v___x_4542_);
v___x_4550_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_updateEnvAttributesImpl_spec__1(v_buckets_4537_, v___x_4548_, v___x_4549_, v___x_4540_);
lean_dec_ref(v_buckets_4537_);
v___y_4532_ = v___x_4550_;
goto v___jp_4531_;
}
}
v___jp_4531_:
{
lean_object* v___x_4533_; lean_object* v___x_4534_; 
v___x_4533_ = l_Lean_PersistentEnvExtension_setState___redArg(v___x_4530_, v_env_4526_, v___y_4532_);
v___x_4534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4534_, 0, v___x_4533_);
return v___x_4534_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_updateEnvAttributesImpl___boxed(lean_object* v_env_4551_, lean_object* v_a_4552_){
_start:
{
lean_object* v_res_4553_; 
v_res_4553_ = lean_update_env_attributes(v_env_4551_);
return v_res_4553_;
}
}
LEAN_EXPORT lean_object* lean_get_num_attributes(){
_start:
{
lean_object* v___x_4555_; lean_object* v___x_4556_; lean_object* v_size_4557_; lean_object* v___x_4558_; 
v___x_4555_ = l_Lean_attributeMapRef;
v___x_4556_ = lean_st_ref_get(v___x_4555_);
v_size_4557_ = lean_ctor_get(v___x_4556_, 0);
lean_inc(v_size_4557_);
lean_dec(v___x_4556_);
v___x_4558_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4558_, 0, v_size_4557_);
return v___x_4558_;
}
}
LEAN_EXPORT lean_object* l_Lean_getNumBuiltinAttributesImpl___boxed(lean_object* v_a_4559_){
_start:
{
lean_object* v_res_4560_; 
v_res_4560_ = lean_get_num_attributes();
return v_res_4560_;
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
