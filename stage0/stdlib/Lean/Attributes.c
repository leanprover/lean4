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
uint8_t v___y_995__boxed_322_; lean_object* v_res_323_; 
v___y_995__boxed_322_ = lean_unbox(v___y_318_);
v_res_323_ = l_Lean_instInhabitedAttributeImpl_default___lam__0(v_x_316_, v___y_317_, v___y_995__boxed_322_, v___y_319_, v___y_320_);
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
lean_dec_ref(v___x_704_);
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
lean_object* v___x_800_; lean_object* v___x_801_; uint8_t v___x_802_; 
lean_inc(v_stx_788_);
v___x_800_ = l_Lean_Syntax_getKind(v_stx_788_);
v___x_801_ = ((lean_object*)(l_Lean_Attribute_Builtin_ensureNoArgs___closed__6));
v___x_802_ = lean_name_eq(v___x_800_, v___x_801_);
if (v___x_802_ == 0)
{
lean_object* v___x_803_; uint8_t v___x_804_; 
v___x_803_ = ((lean_object*)(l_Lean_Attribute_Builtin_getIdent_x3f___closed__1));
v___x_804_ = lean_name_eq(v___x_800_, v___x_803_);
if (v___x_804_ == 0)
{
lean_object* v___x_805_; uint8_t v___x_806_; 
v___x_805_ = ((lean_object*)(l_Lean_Attribute_Builtin_getIdent_x3f___closed__3));
v___x_806_ = lean_name_eq(v___x_800_, v___x_805_);
lean_dec(v___x_800_);
if (v___x_806_ == 0)
{
lean_object* v___x_807_; lean_object* v___x_808_; 
v___x_807_ = lean_obj_once(&l_Lean_Attribute_Builtin_getIdent_x3f___closed__5, &l_Lean_Attribute_Builtin_getIdent_x3f___closed__5_once, _init_l_Lean_Attribute_Builtin_getIdent_x3f___closed__5);
v___x_808_ = l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg(v_stx_788_, v___x_807_, v_a_789_, v_a_790_);
lean_dec(v_stx_788_);
return v___x_808_;
}
else
{
goto v___jp_792_;
}
}
else
{
lean_dec(v___x_800_);
goto v___jp_792_;
}
}
else
{
lean_object* v___x_809_; lean_object* v___x_810_; uint8_t v___x_811_; 
lean_dec(v___x_800_);
v___x_809_ = lean_unsigned_to_nat(1u);
v___x_810_ = l_Lean_Syntax_getArg(v_stx_788_, v___x_809_);
lean_dec(v_stx_788_);
v___x_811_ = l_Lean_Syntax_isNone(v___x_810_);
if (v___x_811_ == 0)
{
if (v___x_802_ == 0)
{
lean_dec(v___x_810_);
goto v___jp_797_;
}
else
{
lean_object* v___x_812_; lean_object* v___x_813_; uint8_t v___x_814_; 
v___x_812_ = lean_unsigned_to_nat(0u);
v___x_813_ = l_Lean_Syntax_getArg(v___x_810_, v___x_812_);
lean_dec(v___x_810_);
v___x_814_ = l_Lean_Syntax_isIdent(v___x_813_);
if (v___x_814_ == 0)
{
lean_dec(v___x_813_);
goto v___jp_797_;
}
else
{
lean_object* v___x_815_; lean_object* v___x_816_; 
v___x_815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_815_, 0, v___x_813_);
v___x_816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_816_, 0, v___x_815_);
return v___x_816_;
}
}
}
else
{
lean_dec(v___x_810_);
goto v___jp_797_;
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
v___jp_797_:
{
lean_object* v___x_798_; lean_object* v___x_799_; 
v___x_798_ = lean_box(0);
v___x_799_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_799_, 0, v___x_798_);
return v___x_799_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getIdent_x3f___boxed(lean_object* v_stx_817_, lean_object* v_a_818_, lean_object* v_a_819_, lean_object* v_a_820_){
_start:
{
lean_object* v_res_821_; 
v_res_821_ = l_Lean_Attribute_Builtin_getIdent_x3f(v_stx_817_, v_a_818_, v_a_819_);
lean_dec(v_a_819_);
lean_dec_ref(v_a_818_);
return v_res_821_;
}
}
static lean_object* _init_l_Lean_Attribute_Builtin_getIdent___closed__1(void){
_start:
{
lean_object* v___x_823_; lean_object* v___x_824_; 
v___x_823_ = ((lean_object*)(l_Lean_Attribute_Builtin_getIdent___closed__0));
v___x_824_ = l_Lean_stringToMessageData(v___x_823_);
return v___x_824_;
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getIdent(lean_object* v_stx_825_, lean_object* v_a_826_, lean_object* v_a_827_){
_start:
{
lean_object* v___x_829_; 
lean_inc(v_stx_825_);
v___x_829_ = l_Lean_Attribute_Builtin_getIdent_x3f(v_stx_825_, v_a_826_, v_a_827_);
if (lean_obj_tag(v___x_829_) == 0)
{
lean_object* v_a_830_; lean_object* v___x_832_; uint8_t v_isShared_833_; uint8_t v_isSharedCheck_843_; 
v_a_830_ = lean_ctor_get(v___x_829_, 0);
v_isSharedCheck_843_ = !lean_is_exclusive(v___x_829_);
if (v_isSharedCheck_843_ == 0)
{
v___x_832_ = v___x_829_;
v_isShared_833_ = v_isSharedCheck_843_;
goto v_resetjp_831_;
}
else
{
lean_inc(v_a_830_);
lean_dec(v___x_829_);
v___x_832_ = lean_box(0);
v_isShared_833_ = v_isSharedCheck_843_;
goto v_resetjp_831_;
}
v_resetjp_831_:
{
if (lean_obj_tag(v_a_830_) == 0)
{
lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; 
lean_del_object(v___x_832_);
v___x_834_ = lean_obj_once(&l_Lean_Attribute_Builtin_getIdent___closed__1, &l_Lean_Attribute_Builtin_getIdent___closed__1_once, _init_l_Lean_Attribute_Builtin_getIdent___closed__1);
lean_inc(v_stx_825_);
v___x_835_ = l_Lean_MessageData_ofSyntax(v_stx_825_);
v___x_836_ = l_Lean_indentD(v___x_835_);
v___x_837_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_837_, 0, v___x_834_);
lean_ctor_set(v___x_837_, 1, v___x_836_);
v___x_838_ = l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg(v_stx_825_, v___x_837_, v_a_826_, v_a_827_);
lean_dec(v_stx_825_);
return v___x_838_;
}
else
{
lean_object* v_val_839_; lean_object* v___x_841_; 
lean_dec(v_stx_825_);
v_val_839_ = lean_ctor_get(v_a_830_, 0);
lean_inc(v_val_839_);
lean_dec_ref(v_a_830_);
if (v_isShared_833_ == 0)
{
lean_ctor_set(v___x_832_, 0, v_val_839_);
v___x_841_ = v___x_832_;
goto v_reusejp_840_;
}
else
{
lean_object* v_reuseFailAlloc_842_; 
v_reuseFailAlloc_842_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_842_, 0, v_val_839_);
v___x_841_ = v_reuseFailAlloc_842_;
goto v_reusejp_840_;
}
v_reusejp_840_:
{
return v___x_841_;
}
}
}
}
else
{
lean_object* v_a_844_; lean_object* v___x_846_; uint8_t v_isShared_847_; uint8_t v_isSharedCheck_851_; 
lean_dec(v_stx_825_);
v_a_844_ = lean_ctor_get(v___x_829_, 0);
v_isSharedCheck_851_ = !lean_is_exclusive(v___x_829_);
if (v_isSharedCheck_851_ == 0)
{
v___x_846_ = v___x_829_;
v_isShared_847_ = v_isSharedCheck_851_;
goto v_resetjp_845_;
}
else
{
lean_inc(v_a_844_);
lean_dec(v___x_829_);
v___x_846_ = lean_box(0);
v_isShared_847_ = v_isSharedCheck_851_;
goto v_resetjp_845_;
}
v_resetjp_845_:
{
lean_object* v___x_849_; 
if (v_isShared_847_ == 0)
{
v___x_849_ = v___x_846_;
goto v_reusejp_848_;
}
else
{
lean_object* v_reuseFailAlloc_850_; 
v_reuseFailAlloc_850_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_850_, 0, v_a_844_);
v___x_849_ = v_reuseFailAlloc_850_;
goto v_reusejp_848_;
}
v_reusejp_848_:
{
return v___x_849_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getIdent___boxed(lean_object* v_stx_852_, lean_object* v_a_853_, lean_object* v_a_854_, lean_object* v_a_855_){
_start:
{
lean_object* v_res_856_; 
v_res_856_ = l_Lean_Attribute_Builtin_getIdent(v_stx_852_, v_a_853_, v_a_854_);
lean_dec(v_a_854_);
lean_dec_ref(v_a_853_);
return v_res_856_;
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getId_x3f(lean_object* v_stx_857_, lean_object* v_a_858_, lean_object* v_a_859_){
_start:
{
lean_object* v___x_861_; 
v___x_861_ = l_Lean_Attribute_Builtin_getIdent_x3f(v_stx_857_, v_a_858_, v_a_859_);
if (lean_obj_tag(v___x_861_) == 0)
{
lean_object* v_a_862_; lean_object* v___x_864_; uint8_t v_isShared_865_; uint8_t v_isSharedCheck_882_; 
v_a_862_ = lean_ctor_get(v___x_861_, 0);
v_isSharedCheck_882_ = !lean_is_exclusive(v___x_861_);
if (v_isSharedCheck_882_ == 0)
{
v___x_864_ = v___x_861_;
v_isShared_865_ = v_isSharedCheck_882_;
goto v_resetjp_863_;
}
else
{
lean_inc(v_a_862_);
lean_dec(v___x_861_);
v___x_864_ = lean_box(0);
v_isShared_865_ = v_isSharedCheck_882_;
goto v_resetjp_863_;
}
v_resetjp_863_:
{
if (lean_obj_tag(v_a_862_) == 0)
{
lean_object* v___x_866_; lean_object* v___x_868_; 
v___x_866_ = lean_box(0);
if (v_isShared_865_ == 0)
{
lean_ctor_set(v___x_864_, 0, v___x_866_);
v___x_868_ = v___x_864_;
goto v_reusejp_867_;
}
else
{
lean_object* v_reuseFailAlloc_869_; 
v_reuseFailAlloc_869_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_869_, 0, v___x_866_);
v___x_868_ = v_reuseFailAlloc_869_;
goto v_reusejp_867_;
}
v_reusejp_867_:
{
return v___x_868_;
}
}
else
{
lean_object* v_val_870_; lean_object* v___x_872_; uint8_t v_isShared_873_; uint8_t v_isSharedCheck_881_; 
v_val_870_ = lean_ctor_get(v_a_862_, 0);
v_isSharedCheck_881_ = !lean_is_exclusive(v_a_862_);
if (v_isSharedCheck_881_ == 0)
{
v___x_872_ = v_a_862_;
v_isShared_873_ = v_isSharedCheck_881_;
goto v_resetjp_871_;
}
else
{
lean_inc(v_val_870_);
lean_dec(v_a_862_);
v___x_872_ = lean_box(0);
v_isShared_873_ = v_isSharedCheck_881_;
goto v_resetjp_871_;
}
v_resetjp_871_:
{
lean_object* v___x_874_; lean_object* v___x_876_; 
v___x_874_ = l_Lean_Syntax_getId(v_val_870_);
lean_dec(v_val_870_);
if (v_isShared_873_ == 0)
{
lean_ctor_set(v___x_872_, 0, v___x_874_);
v___x_876_ = v___x_872_;
goto v_reusejp_875_;
}
else
{
lean_object* v_reuseFailAlloc_880_; 
v_reuseFailAlloc_880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_880_, 0, v___x_874_);
v___x_876_ = v_reuseFailAlloc_880_;
goto v_reusejp_875_;
}
v_reusejp_875_:
{
lean_object* v___x_878_; 
if (v_isShared_865_ == 0)
{
lean_ctor_set(v___x_864_, 0, v___x_876_);
v___x_878_ = v___x_864_;
goto v_reusejp_877_;
}
else
{
lean_object* v_reuseFailAlloc_879_; 
v_reuseFailAlloc_879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_879_, 0, v___x_876_);
v___x_878_ = v_reuseFailAlloc_879_;
goto v_reusejp_877_;
}
v_reusejp_877_:
{
return v___x_878_;
}
}
}
}
}
}
else
{
lean_object* v_a_883_; lean_object* v___x_885_; uint8_t v_isShared_886_; uint8_t v_isSharedCheck_890_; 
v_a_883_ = lean_ctor_get(v___x_861_, 0);
v_isSharedCheck_890_ = !lean_is_exclusive(v___x_861_);
if (v_isSharedCheck_890_ == 0)
{
v___x_885_ = v___x_861_;
v_isShared_886_ = v_isSharedCheck_890_;
goto v_resetjp_884_;
}
else
{
lean_inc(v_a_883_);
lean_dec(v___x_861_);
v___x_885_ = lean_box(0);
v_isShared_886_ = v_isSharedCheck_890_;
goto v_resetjp_884_;
}
v_resetjp_884_:
{
lean_object* v___x_888_; 
if (v_isShared_886_ == 0)
{
v___x_888_ = v___x_885_;
goto v_reusejp_887_;
}
else
{
lean_object* v_reuseFailAlloc_889_; 
v_reuseFailAlloc_889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_889_, 0, v_a_883_);
v___x_888_ = v_reuseFailAlloc_889_;
goto v_reusejp_887_;
}
v_reusejp_887_:
{
return v___x_888_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getId_x3f___boxed(lean_object* v_stx_891_, lean_object* v_a_892_, lean_object* v_a_893_, lean_object* v_a_894_){
_start:
{
lean_object* v_res_895_; 
v_res_895_ = l_Lean_Attribute_Builtin_getId_x3f(v_stx_891_, v_a_892_, v_a_893_);
lean_dec(v_a_893_);
lean_dec_ref(v_a_892_);
return v_res_895_;
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getId(lean_object* v_stx_896_, lean_object* v_a_897_, lean_object* v_a_898_){
_start:
{
lean_object* v___x_900_; 
v___x_900_ = l_Lean_Attribute_Builtin_getIdent(v_stx_896_, v_a_897_, v_a_898_);
if (lean_obj_tag(v___x_900_) == 0)
{
lean_object* v_a_901_; lean_object* v___x_903_; uint8_t v_isShared_904_; uint8_t v_isSharedCheck_909_; 
v_a_901_ = lean_ctor_get(v___x_900_, 0);
v_isSharedCheck_909_ = !lean_is_exclusive(v___x_900_);
if (v_isSharedCheck_909_ == 0)
{
v___x_903_ = v___x_900_;
v_isShared_904_ = v_isSharedCheck_909_;
goto v_resetjp_902_;
}
else
{
lean_inc(v_a_901_);
lean_dec(v___x_900_);
v___x_903_ = lean_box(0);
v_isShared_904_ = v_isSharedCheck_909_;
goto v_resetjp_902_;
}
v_resetjp_902_:
{
lean_object* v___x_905_; lean_object* v___x_907_; 
v___x_905_ = l_Lean_Syntax_getId(v_a_901_);
lean_dec(v_a_901_);
if (v_isShared_904_ == 0)
{
lean_ctor_set(v___x_903_, 0, v___x_905_);
v___x_907_ = v___x_903_;
goto v_reusejp_906_;
}
else
{
lean_object* v_reuseFailAlloc_908_; 
v_reuseFailAlloc_908_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_908_, 0, v___x_905_);
v___x_907_ = v_reuseFailAlloc_908_;
goto v_reusejp_906_;
}
v_reusejp_906_:
{
return v___x_907_;
}
}
}
else
{
lean_object* v_a_910_; lean_object* v___x_912_; uint8_t v_isShared_913_; uint8_t v_isSharedCheck_917_; 
v_a_910_ = lean_ctor_get(v___x_900_, 0);
v_isSharedCheck_917_ = !lean_is_exclusive(v___x_900_);
if (v_isSharedCheck_917_ == 0)
{
v___x_912_ = v___x_900_;
v_isShared_913_ = v_isSharedCheck_917_;
goto v_resetjp_911_;
}
else
{
lean_inc(v_a_910_);
lean_dec(v___x_900_);
v___x_912_ = lean_box(0);
v_isShared_913_ = v_isSharedCheck_917_;
goto v_resetjp_911_;
}
v_resetjp_911_:
{
lean_object* v___x_915_; 
if (v_isShared_913_ == 0)
{
v___x_915_ = v___x_912_;
goto v_reusejp_914_;
}
else
{
lean_object* v_reuseFailAlloc_916_; 
v_reuseFailAlloc_916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_916_, 0, v_a_910_);
v___x_915_ = v_reuseFailAlloc_916_;
goto v_reusejp_914_;
}
v_reusejp_914_:
{
return v___x_915_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getId___boxed(lean_object* v_stx_918_, lean_object* v_a_919_, lean_object* v_a_920_, lean_object* v_a_921_){
_start:
{
lean_object* v_res_922_; 
v_res_922_ = l_Lean_Attribute_Builtin_getId(v_stx_918_, v_a_919_, v_a_920_);
lean_dec(v_a_920_);
lean_dec_ref(v_a_919_);
return v_res_922_;
}
}
static lean_object* _init_l_Lean_getAttrParamOptPrio___closed__1(void){
_start:
{
lean_object* v___x_924_; lean_object* v___x_925_; 
v___x_924_ = ((lean_object*)(l_Lean_getAttrParamOptPrio___closed__0));
v___x_925_ = l_Lean_stringToMessageData(v___x_924_);
return v___x_925_;
}
}
LEAN_EXPORT lean_object* l_Lean_getAttrParamOptPrio(lean_object* v_optPrioStx_926_, lean_object* v_a_927_, lean_object* v_a_928_){
_start:
{
uint8_t v___x_930_; 
v___x_930_ = l_Lean_Syntax_isNone(v_optPrioStx_926_);
if (v___x_930_ == 0)
{
lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; 
v___x_931_ = lean_unsigned_to_nat(0u);
v___x_932_ = l_Lean_Syntax_getArg(v_optPrioStx_926_, v___x_931_);
v___x_933_ = l_Lean_Syntax_isNatLit_x3f(v___x_932_);
lean_dec(v___x_932_);
if (lean_obj_tag(v___x_933_) == 0)
{
lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; 
v___x_934_ = lean_obj_once(&l_Lean_getAttrParamOptPrio___closed__1, &l_Lean_getAttrParamOptPrio___closed__1_once, _init_l_Lean_getAttrParamOptPrio___closed__1);
lean_inc(v_optPrioStx_926_);
v___x_935_ = l_Lean_MessageData_ofSyntax(v_optPrioStx_926_);
v___x_936_ = l_Lean_indentD(v___x_935_);
v___x_937_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_937_, 0, v___x_934_);
lean_ctor_set(v___x_937_, 1, v___x_936_);
v___x_938_ = l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg(v_optPrioStx_926_, v___x_937_, v_a_927_, v_a_928_);
lean_dec(v_optPrioStx_926_);
return v___x_938_;
}
else
{
lean_object* v_val_939_; lean_object* v___x_941_; uint8_t v_isShared_942_; uint8_t v_isSharedCheck_946_; 
lean_dec(v_optPrioStx_926_);
v_val_939_ = lean_ctor_get(v___x_933_, 0);
v_isSharedCheck_946_ = !lean_is_exclusive(v___x_933_);
if (v_isSharedCheck_946_ == 0)
{
v___x_941_ = v___x_933_;
v_isShared_942_ = v_isSharedCheck_946_;
goto v_resetjp_940_;
}
else
{
lean_inc(v_val_939_);
lean_dec(v___x_933_);
v___x_941_ = lean_box(0);
v_isShared_942_ = v_isSharedCheck_946_;
goto v_resetjp_940_;
}
v_resetjp_940_:
{
lean_object* v___x_944_; 
if (v_isShared_942_ == 0)
{
lean_ctor_set_tag(v___x_941_, 0);
v___x_944_ = v___x_941_;
goto v_reusejp_943_;
}
else
{
lean_object* v_reuseFailAlloc_945_; 
v_reuseFailAlloc_945_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_945_, 0, v_val_939_);
v___x_944_ = v_reuseFailAlloc_945_;
goto v_reusejp_943_;
}
v_reusejp_943_:
{
return v___x_944_;
}
}
}
}
else
{
lean_object* v___x_947_; lean_object* v___x_948_; 
lean_dec(v_optPrioStx_926_);
v___x_947_ = lean_unsigned_to_nat(1000u);
v___x_948_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_948_, 0, v___x_947_);
return v___x_948_;
}
}
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
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getPrio(lean_object* v_stx_957_, lean_object* v_a_958_, lean_object* v_a_959_){
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
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getPrio___boxed(lean_object* v_stx_972_, lean_object* v_a_973_, lean_object* v_a_974_, lean_object* v_a_975_){
_start:
{
lean_object* v_res_976_; 
v_res_976_ = l_Lean_Attribute_Builtin_getPrio(v_stx_972_, v_a_973_, v_a_974_);
lean_dec(v_a_974_);
lean_dec_ref(v_a_973_);
return v_res_976_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__1(void){
_start:
{
lean_object* v___x_978_; lean_object* v___x_979_; 
v___x_978_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__0));
v___x_979_ = l_Lean_stringToMessageData(v___x_978_);
return v___x_979_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__3(void){
_start:
{
lean_object* v___x_981_; lean_object* v___x_982_; 
v___x_981_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__2));
v___x_982_ = l_Lean_stringToMessageData(v___x_981_);
return v___x_982_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__5(void){
_start:
{
lean_object* v___x_984_; lean_object* v___x_985_; 
v___x_984_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__4));
v___x_985_ = l_Lean_stringToMessageData(v___x_984_);
return v___x_985_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___redArg(lean_object* v_inst_986_, lean_object* v_inst_987_, lean_object* v_name_988_, uint8_t v_kind_989_){
_start:
{
lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___y_996_; 
v___x_990_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__1, &l_Lean_throwAttrMustBeGlobal___redArg___closed__1_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__1);
v___x_991_ = l_Lean_MessageData_ofName(v_name_988_);
v___x_992_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_992_, 0, v___x_990_);
lean_ctor_set(v___x_992_, 1, v___x_991_);
v___x_993_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__3, &l_Lean_throwAttrMustBeGlobal___redArg___closed__3_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__3);
v___x_994_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_994_, 0, v___x_992_);
lean_ctor_set(v___x_994_, 1, v___x_993_);
switch(v_kind_989_)
{
case 0:
{
lean_object* v___x_1003_; 
v___x_1003_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__0));
v___y_996_ = v___x_1003_;
goto v___jp_995_;
}
case 1:
{
lean_object* v___x_1004_; 
v___x_1004_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__1));
v___y_996_ = v___x_1004_;
goto v___jp_995_;
}
default: 
{
lean_object* v___x_1005_; 
v___x_1005_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__2));
v___y_996_ = v___x_1005_;
goto v___jp_995_;
}
}
v___jp_995_:
{
lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; 
lean_inc_ref(v___y_996_);
v___x_997_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_997_, 0, v___y_996_);
v___x_998_ = l_Lean_MessageData_ofFormat(v___x_997_);
v___x_999_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_999_, 0, v___x_994_);
lean_ctor_set(v___x_999_, 1, v___x_998_);
v___x_1000_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__5, &l_Lean_throwAttrMustBeGlobal___redArg___closed__5_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__5);
v___x_1001_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1001_, 0, v___x_999_);
lean_ctor_set(v___x_1001_, 1, v___x_1000_);
v___x_1002_ = l_Lean_throwError___redArg(v_inst_986_, v_inst_987_, v___x_1001_);
return v___x_1002_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___redArg___boxed(lean_object* v_inst_1006_, lean_object* v_inst_1007_, lean_object* v_name_1008_, lean_object* v_kind_1009_){
_start:
{
uint8_t v_kind_boxed_1010_; lean_object* v_res_1011_; 
v_kind_boxed_1010_ = lean_unbox(v_kind_1009_);
v_res_1011_ = l_Lean_throwAttrMustBeGlobal___redArg(v_inst_1006_, v_inst_1007_, v_name_1008_, v_kind_boxed_1010_);
return v_res_1011_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal(lean_object* v_m_1012_, lean_object* v_inst_1013_, lean_object* v_inst_1014_, lean_object* v_00_u03b1_1015_, lean_object* v_name_1016_, uint8_t v_kind_1017_){
_start:
{
lean_object* v___x_1018_; 
v___x_1018_ = l_Lean_throwAttrMustBeGlobal___redArg(v_inst_1013_, v_inst_1014_, v_name_1016_, v_kind_1017_);
return v___x_1018_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___boxed(lean_object* v_m_1019_, lean_object* v_inst_1020_, lean_object* v_inst_1021_, lean_object* v_00_u03b1_1022_, lean_object* v_name_1023_, lean_object* v_kind_1024_){
_start:
{
uint8_t v_kind_boxed_1025_; lean_object* v_res_1026_; 
v_kind_boxed_1025_ = lean_unbox(v_kind_1024_);
v_res_1026_ = l_Lean_throwAttrMustBeGlobal(v_m_1019_, v_inst_1020_, v_inst_1021_, v_00_u03b1_1022_, v_name_1023_, v_kind_boxed_1025_);
return v_res_1026_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1(void){
_start:
{
lean_object* v___x_1028_; lean_object* v___x_1029_; 
v___x_1028_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___redArg___closed__0));
v___x_1029_ = l_Lean_stringToMessageData(v___x_1028_);
return v___x_1029_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__3(void){
_start:
{
lean_object* v___x_1031_; lean_object* v___x_1032_; 
v___x_1031_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___redArg___closed__2));
v___x_1032_ = l_Lean_stringToMessageData(v___x_1031_);
return v___x_1032_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__5(void){
_start:
{
lean_object* v___x_1034_; lean_object* v___x_1035_; 
v___x_1034_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___redArg___closed__4));
v___x_1035_ = l_Lean_stringToMessageData(v___x_1034_);
return v___x_1035_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___redArg(lean_object* v_inst_1036_, lean_object* v_inst_1037_, lean_object* v_attrName_1038_, lean_object* v_declName_1039_){
_start:
{
lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; uint8_t v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; 
v___x_1040_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1);
v___x_1041_ = l_Lean_MessageData_ofName(v_attrName_1038_);
v___x_1042_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1042_, 0, v___x_1040_);
lean_ctor_set(v___x_1042_, 1, v___x_1041_);
v___x_1043_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__3, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__3_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__3);
v___x_1044_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1044_, 0, v___x_1042_);
lean_ctor_set(v___x_1044_, 1, v___x_1043_);
v___x_1045_ = 0;
v___x_1046_ = l_Lean_MessageData_ofConstName(v_declName_1039_, v___x_1045_);
v___x_1047_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1047_, 0, v___x_1044_);
lean_ctor_set(v___x_1047_, 1, v___x_1046_);
v___x_1048_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__5, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__5_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__5);
v___x_1049_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1049_, 0, v___x_1047_);
lean_ctor_set(v___x_1049_, 1, v___x_1048_);
v___x_1050_ = l_Lean_throwError___redArg(v_inst_1036_, v_inst_1037_, v___x_1049_);
return v___x_1050_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule(lean_object* v_m_1051_, lean_object* v_inst_1052_, lean_object* v_inst_1053_, lean_object* v_00_u03b1_1054_, lean_object* v_attrName_1055_, lean_object* v_declName_1056_){
_start:
{
lean_object* v___x_1057_; 
v___x_1057_ = l_Lean_throwAttrDeclInImportedModule___redArg(v_inst_1052_, v_inst_1053_, v_attrName_1055_, v_declName_1056_);
return v___x_1057_;
}
}
static lean_object* _init_l_Lean_throwAttrNotInAsyncCtx___redArg___closed__1(void){
_start:
{
lean_object* v___x_1059_; lean_object* v___x_1060_; 
v___x_1059_ = ((lean_object*)(l_Lean_throwAttrNotInAsyncCtx___redArg___closed__0));
v___x_1060_ = l_Lean_stringToMessageData(v___x_1059_);
return v___x_1060_;
}
}
static lean_object* _init_l_Lean_throwAttrNotInAsyncCtx___redArg___closed__3(void){
_start:
{
lean_object* v___x_1062_; lean_object* v___x_1063_; 
v___x_1062_ = ((lean_object*)(l_Lean_throwAttrNotInAsyncCtx___redArg___closed__2));
v___x_1063_ = l_Lean_stringToMessageData(v___x_1062_);
return v___x_1063_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___redArg(lean_object* v_inst_1064_, lean_object* v_inst_1065_, lean_object* v_attrName_1066_, lean_object* v_declName_1067_, lean_object* v_asyncPrefix_x3f_1068_){
_start:
{
lean_object* v___y_1070_; 
if (lean_obj_tag(v_asyncPrefix_x3f_1068_) == 0)
{
lean_object* v___x_1083_; 
v___x_1083_ = l_Lean_MessageData_nil;
v___y_1070_ = v___x_1083_;
goto v___jp_1069_;
}
else
{
lean_object* v_val_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; 
v_val_1084_ = lean_ctor_get(v_asyncPrefix_x3f_1068_, 0);
lean_inc(v_val_1084_);
lean_dec_ref(v_asyncPrefix_x3f_1068_);
v___x_1085_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___redArg___closed__3, &l_Lean_throwAttrNotInAsyncCtx___redArg___closed__3_once, _init_l_Lean_throwAttrNotInAsyncCtx___redArg___closed__3);
v___x_1086_ = l_Lean_MessageData_ofName(v_val_1084_);
v___x_1087_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1087_, 0, v___x_1085_);
lean_ctor_set(v___x_1087_, 1, v___x_1086_);
v___x_1088_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__5, &l_Lean_throwAttrMustBeGlobal___redArg___closed__5_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__5);
v___x_1089_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1089_, 0, v___x_1087_);
lean_ctor_set(v___x_1089_, 1, v___x_1088_);
v___y_1070_ = v___x_1089_;
goto v___jp_1069_;
}
v___jp_1069_:
{
lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; uint8_t v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; 
v___x_1071_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1);
v___x_1072_ = l_Lean_MessageData_ofName(v_attrName_1066_);
v___x_1073_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1073_, 0, v___x_1071_);
lean_ctor_set(v___x_1073_, 1, v___x_1072_);
v___x_1074_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__3, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__3_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__3);
v___x_1075_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1075_, 0, v___x_1073_);
lean_ctor_set(v___x_1075_, 1, v___x_1074_);
v___x_1076_ = 0;
v___x_1077_ = l_Lean_MessageData_ofConstName(v_declName_1067_, v___x_1076_);
v___x_1078_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1078_, 0, v___x_1075_);
lean_ctor_set(v___x_1078_, 1, v___x_1077_);
v___x_1079_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___redArg___closed__1, &l_Lean_throwAttrNotInAsyncCtx___redArg___closed__1_once, _init_l_Lean_throwAttrNotInAsyncCtx___redArg___closed__1);
v___x_1080_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1080_, 0, v___x_1078_);
lean_ctor_set(v___x_1080_, 1, v___x_1079_);
v___x_1081_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1081_, 0, v___x_1080_);
lean_ctor_set(v___x_1081_, 1, v___y_1070_);
v___x_1082_ = l_Lean_throwError___redArg(v_inst_1064_, v_inst_1065_, v___x_1081_);
return v___x_1082_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx(lean_object* v_m_1090_, lean_object* v_inst_1091_, lean_object* v_inst_1092_, lean_object* v_00_u03b1_1093_, lean_object* v_attrName_1094_, lean_object* v_declName_1095_, lean_object* v_asyncPrefix_x3f_1096_){
_start:
{
lean_object* v___x_1097_; 
v___x_1097_ = l_Lean_throwAttrNotInAsyncCtx___redArg(v_inst_1091_, v_inst_1092_, v_attrName_1094_, v_declName_1095_, v_asyncPrefix_x3f_1096_);
return v___x_1097_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1(void){
_start:
{
lean_object* v___x_1099_; lean_object* v___x_1100_; 
v___x_1099_ = ((lean_object*)(l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__0));
v___x_1100_ = l_Lean_stringToMessageData(v___x_1099_);
return v___x_1100_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__3(void){
_start:
{
lean_object* v___x_1102_; lean_object* v___x_1103_; 
v___x_1102_ = ((lean_object*)(l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__2));
v___x_1103_ = l_Lean_stringToMessageData(v___x_1102_);
return v___x_1103_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__5(void){
_start:
{
lean_object* v___x_1105_; lean_object* v___x_1106_; 
v___x_1105_ = ((lean_object*)(l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__4));
v___x_1106_ = l_Lean_stringToMessageData(v___x_1105_);
return v___x_1106_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__7(void){
_start:
{
lean_object* v___x_1108_; lean_object* v___x_1109_; 
v___x_1108_ = ((lean_object*)(l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__6));
v___x_1109_ = l_Lean_stringToMessageData(v___x_1108_);
return v___x_1109_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclNotOfExpectedType___redArg(lean_object* v_inst_1110_, lean_object* v_inst_1111_, lean_object* v_attrName_1112_, lean_object* v_declName_1113_, lean_object* v_givenType_1114_, lean_object* v_expectedType_1115_){
_start:
{
lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; uint8_t v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; 
v___x_1116_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1);
v___x_1117_ = l_Lean_MessageData_ofName(v_attrName_1112_);
lean_inc_ref(v___x_1117_);
v___x_1118_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1118_, 0, v___x_1116_);
lean_ctor_set(v___x_1118_, 1, v___x_1117_);
v___x_1119_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1, &l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1);
v___x_1120_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1120_, 0, v___x_1118_);
lean_ctor_set(v___x_1120_, 1, v___x_1119_);
v___x_1121_ = 0;
v___x_1122_ = l_Lean_MessageData_ofConstName(v_declName_1113_, v___x_1121_);
v___x_1123_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1123_, 0, v___x_1120_);
lean_ctor_set(v___x_1123_, 1, v___x_1122_);
v___x_1124_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__3, &l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__3_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__3);
v___x_1125_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1125_, 0, v___x_1123_);
lean_ctor_set(v___x_1125_, 1, v___x_1124_);
v___x_1126_ = l_Lean_indentExpr(v_givenType_1114_);
v___x_1127_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1127_, 0, v___x_1125_);
lean_ctor_set(v___x_1127_, 1, v___x_1126_);
v___x_1128_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__5, &l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__5_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__5);
v___x_1129_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1129_, 0, v___x_1127_);
lean_ctor_set(v___x_1129_, 1, v___x_1128_);
v___x_1130_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1130_, 0, v___x_1129_);
lean_ctor_set(v___x_1130_, 1, v___x_1117_);
v___x_1131_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__7, &l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__7_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__7);
v___x_1132_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1132_, 0, v___x_1130_);
lean_ctor_set(v___x_1132_, 1, v___x_1131_);
v___x_1133_ = l_Lean_indentExpr(v_expectedType_1115_);
v___x_1134_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1134_, 0, v___x_1132_);
lean_ctor_set(v___x_1134_, 1, v___x_1133_);
v___x_1135_ = l_Lean_throwError___redArg(v_inst_1110_, v_inst_1111_, v___x_1134_);
return v___x_1135_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclNotOfExpectedType(lean_object* v_m_1136_, lean_object* v_inst_1137_, lean_object* v_inst_1138_, lean_object* v_00_u03b1_1139_, lean_object* v_attrName_1140_, lean_object* v_declName_1141_, lean_object* v_givenType_1142_, lean_object* v_expectedType_1143_){
_start:
{
lean_object* v___x_1144_; 
v___x_1144_ = l_Lean_throwAttrDeclNotOfExpectedType___redArg(v_inst_1137_, v_inst_1138_, v_attrName_1140_, v_declName_1141_, v_givenType_1142_, v_expectedType_1143_);
return v___x_1144_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1___redArg(lean_object* v_constName_1145_, uint8_t v_skipRealize_1146_, lean_object* v___y_1147_){
_start:
{
lean_object* v___x_1149_; lean_object* v_env_1150_; uint8_t v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; 
v___x_1149_ = lean_st_ref_get(v___y_1147_);
v_env_1150_ = lean_ctor_get(v___x_1149_, 0);
lean_inc_ref(v_env_1150_);
lean_dec(v___x_1149_);
v___x_1151_ = l_Lean_Environment_contains(v_env_1150_, v_constName_1145_, v_skipRealize_1146_);
v___x_1152_ = lean_box(v___x_1151_);
v___x_1153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1153_, 0, v___x_1152_);
return v___x_1153_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1___redArg___boxed(lean_object* v_constName_1154_, lean_object* v_skipRealize_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_){
_start:
{
uint8_t v_skipRealize_boxed_1158_; lean_object* v_res_1159_; 
v_skipRealize_boxed_1158_ = lean_unbox(v_skipRealize_1155_);
v_res_1159_ = l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1___redArg(v_constName_1154_, v_skipRealize_boxed_1158_, v___y_1156_);
lean_dec(v___y_1156_);
return v_res_1159_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1(lean_object* v_constName_1160_, uint8_t v_skipRealize_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_){
_start:
{
lean_object* v___x_1165_; 
v___x_1165_ = l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1___redArg(v_constName_1160_, v_skipRealize_1161_, v___y_1163_);
return v___x_1165_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1___boxed(lean_object* v_constName_1166_, lean_object* v_skipRealize_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_){
_start:
{
uint8_t v_skipRealize_boxed_1171_; lean_object* v_res_1172_; 
v_skipRealize_boxed_1171_ = lean_unbox(v_skipRealize_1167_);
v_res_1172_ = l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1(v_constName_1166_, v_skipRealize_boxed_1171_, v___y_1168_, v___y_1169_);
lean_dec(v___y_1169_);
lean_dec_ref(v___y_1168_);
return v_res_1172_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___lam__0(lean_object* v___y_1173_, uint8_t v_isExporting_1174_, lean_object* v___x_1175_, lean_object* v_a_x3f_1176_){
_start:
{
lean_object* v___x_1178_; lean_object* v_env_1179_; lean_object* v_nextMacroScope_1180_; lean_object* v_ngen_1181_; lean_object* v_auxDeclNGen_1182_; lean_object* v_traceState_1183_; lean_object* v_messages_1184_; lean_object* v_infoState_1185_; lean_object* v_snapshotTasks_1186_; lean_object* v_newDecls_1187_; lean_object* v___x_1189_; uint8_t v_isShared_1190_; uint8_t v_isSharedCheck_1198_; 
v___x_1178_ = lean_st_ref_take(v___y_1173_);
v_env_1179_ = lean_ctor_get(v___x_1178_, 0);
v_nextMacroScope_1180_ = lean_ctor_get(v___x_1178_, 1);
v_ngen_1181_ = lean_ctor_get(v___x_1178_, 2);
v_auxDeclNGen_1182_ = lean_ctor_get(v___x_1178_, 3);
v_traceState_1183_ = lean_ctor_get(v___x_1178_, 4);
v_messages_1184_ = lean_ctor_get(v___x_1178_, 6);
v_infoState_1185_ = lean_ctor_get(v___x_1178_, 7);
v_snapshotTasks_1186_ = lean_ctor_get(v___x_1178_, 8);
v_newDecls_1187_ = lean_ctor_get(v___x_1178_, 9);
v_isSharedCheck_1198_ = !lean_is_exclusive(v___x_1178_);
if (v_isSharedCheck_1198_ == 0)
{
lean_object* v_unused_1199_; 
v_unused_1199_ = lean_ctor_get(v___x_1178_, 5);
lean_dec(v_unused_1199_);
v___x_1189_ = v___x_1178_;
v_isShared_1190_ = v_isSharedCheck_1198_;
goto v_resetjp_1188_;
}
else
{
lean_inc(v_newDecls_1187_);
lean_inc(v_snapshotTasks_1186_);
lean_inc(v_infoState_1185_);
lean_inc(v_messages_1184_);
lean_inc(v_traceState_1183_);
lean_inc(v_auxDeclNGen_1182_);
lean_inc(v_ngen_1181_);
lean_inc(v_nextMacroScope_1180_);
lean_inc(v_env_1179_);
lean_dec(v___x_1178_);
v___x_1189_ = lean_box(0);
v_isShared_1190_ = v_isSharedCheck_1198_;
goto v_resetjp_1188_;
}
v_resetjp_1188_:
{
lean_object* v___x_1191_; lean_object* v___x_1193_; 
v___x_1191_ = l_Lean_Environment_setExporting(v_env_1179_, v_isExporting_1174_);
if (v_isShared_1190_ == 0)
{
lean_ctor_set(v___x_1189_, 5, v___x_1175_);
lean_ctor_set(v___x_1189_, 0, v___x_1191_);
v___x_1193_ = v___x_1189_;
goto v_reusejp_1192_;
}
else
{
lean_object* v_reuseFailAlloc_1197_; 
v_reuseFailAlloc_1197_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1197_, 0, v___x_1191_);
lean_ctor_set(v_reuseFailAlloc_1197_, 1, v_nextMacroScope_1180_);
lean_ctor_set(v_reuseFailAlloc_1197_, 2, v_ngen_1181_);
lean_ctor_set(v_reuseFailAlloc_1197_, 3, v_auxDeclNGen_1182_);
lean_ctor_set(v_reuseFailAlloc_1197_, 4, v_traceState_1183_);
lean_ctor_set(v_reuseFailAlloc_1197_, 5, v___x_1175_);
lean_ctor_set(v_reuseFailAlloc_1197_, 6, v_messages_1184_);
lean_ctor_set(v_reuseFailAlloc_1197_, 7, v_infoState_1185_);
lean_ctor_set(v_reuseFailAlloc_1197_, 8, v_snapshotTasks_1186_);
lean_ctor_set(v_reuseFailAlloc_1197_, 9, v_newDecls_1187_);
v___x_1193_ = v_reuseFailAlloc_1197_;
goto v_reusejp_1192_;
}
v_reusejp_1192_:
{
lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; 
v___x_1194_ = lean_st_ref_set(v___y_1173_, v___x_1193_);
v___x_1195_ = lean_box(0);
v___x_1196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1196_, 0, v___x_1195_);
return v___x_1196_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___lam__0___boxed(lean_object* v___y_1200_, lean_object* v_isExporting_1201_, lean_object* v___x_1202_, lean_object* v_a_x3f_1203_, lean_object* v___y_1204_){
_start:
{
uint8_t v_isExporting_boxed_1205_; lean_object* v_res_1206_; 
v_isExporting_boxed_1205_ = lean_unbox(v_isExporting_1201_);
v_res_1206_ = l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___lam__0(v___y_1200_, v_isExporting_boxed_1205_, v___x_1202_, v_a_x3f_1203_);
lean_dec(v_a_x3f_1203_);
lean_dec(v___y_1200_);
return v_res_1206_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_1207_; 
v___x_1207_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1207_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_1208_; lean_object* v___x_1209_; 
v___x_1208_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__0, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__0);
v___x_1209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1209_, 0, v___x_1208_);
return v___x_1209_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_1210_; lean_object* v___x_1211_; 
v___x_1210_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1);
v___x_1211_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1211_, 0, v___x_1210_);
lean_ctor_set(v___x_1211_, 1, v___x_1210_);
return v___x_1211_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg(lean_object* v_x_1212_, uint8_t v_isExporting_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_){
_start:
{
lean_object* v___x_1217_; lean_object* v_env_1218_; uint8_t v_isExporting_1219_; lean_object* v___x_1220_; lean_object* v_env_1221_; lean_object* v_nextMacroScope_1222_; lean_object* v_ngen_1223_; lean_object* v_auxDeclNGen_1224_; lean_object* v_traceState_1225_; lean_object* v_messages_1226_; lean_object* v_infoState_1227_; lean_object* v_snapshotTasks_1228_; lean_object* v_newDecls_1229_; lean_object* v___x_1231_; uint8_t v_isShared_1232_; uint8_t v_isSharedCheck_1268_; 
v___x_1217_ = lean_st_ref_get(v___y_1215_);
v_env_1218_ = lean_ctor_get(v___x_1217_, 0);
lean_inc_ref(v_env_1218_);
lean_dec(v___x_1217_);
v_isExporting_1219_ = lean_ctor_get_uint8(v_env_1218_, sizeof(void*)*8);
lean_dec_ref(v_env_1218_);
v___x_1220_ = lean_st_ref_take(v___y_1215_);
v_env_1221_ = lean_ctor_get(v___x_1220_, 0);
v_nextMacroScope_1222_ = lean_ctor_get(v___x_1220_, 1);
v_ngen_1223_ = lean_ctor_get(v___x_1220_, 2);
v_auxDeclNGen_1224_ = lean_ctor_get(v___x_1220_, 3);
v_traceState_1225_ = lean_ctor_get(v___x_1220_, 4);
v_messages_1226_ = lean_ctor_get(v___x_1220_, 6);
v_infoState_1227_ = lean_ctor_get(v___x_1220_, 7);
v_snapshotTasks_1228_ = lean_ctor_get(v___x_1220_, 8);
v_newDecls_1229_ = lean_ctor_get(v___x_1220_, 9);
v_isSharedCheck_1268_ = !lean_is_exclusive(v___x_1220_);
if (v_isSharedCheck_1268_ == 0)
{
lean_object* v_unused_1269_; 
v_unused_1269_ = lean_ctor_get(v___x_1220_, 5);
lean_dec(v_unused_1269_);
v___x_1231_ = v___x_1220_;
v_isShared_1232_ = v_isSharedCheck_1268_;
goto v_resetjp_1230_;
}
else
{
lean_inc(v_newDecls_1229_);
lean_inc(v_snapshotTasks_1228_);
lean_inc(v_infoState_1227_);
lean_inc(v_messages_1226_);
lean_inc(v_traceState_1225_);
lean_inc(v_auxDeclNGen_1224_);
lean_inc(v_ngen_1223_);
lean_inc(v_nextMacroScope_1222_);
lean_inc(v_env_1221_);
lean_dec(v___x_1220_);
v___x_1231_ = lean_box(0);
v_isShared_1232_ = v_isSharedCheck_1268_;
goto v_resetjp_1230_;
}
v_resetjp_1230_:
{
lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1236_; 
v___x_1233_ = l_Lean_Environment_setExporting(v_env_1221_, v_isExporting_1213_);
v___x_1234_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2);
if (v_isShared_1232_ == 0)
{
lean_ctor_set(v___x_1231_, 5, v___x_1234_);
lean_ctor_set(v___x_1231_, 0, v___x_1233_);
v___x_1236_ = v___x_1231_;
goto v_reusejp_1235_;
}
else
{
lean_object* v_reuseFailAlloc_1267_; 
v_reuseFailAlloc_1267_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1267_, 0, v___x_1233_);
lean_ctor_set(v_reuseFailAlloc_1267_, 1, v_nextMacroScope_1222_);
lean_ctor_set(v_reuseFailAlloc_1267_, 2, v_ngen_1223_);
lean_ctor_set(v_reuseFailAlloc_1267_, 3, v_auxDeclNGen_1224_);
lean_ctor_set(v_reuseFailAlloc_1267_, 4, v_traceState_1225_);
lean_ctor_set(v_reuseFailAlloc_1267_, 5, v___x_1234_);
lean_ctor_set(v_reuseFailAlloc_1267_, 6, v_messages_1226_);
lean_ctor_set(v_reuseFailAlloc_1267_, 7, v_infoState_1227_);
lean_ctor_set(v_reuseFailAlloc_1267_, 8, v_snapshotTasks_1228_);
lean_ctor_set(v_reuseFailAlloc_1267_, 9, v_newDecls_1229_);
v___x_1236_ = v_reuseFailAlloc_1267_;
goto v_reusejp_1235_;
}
v_reusejp_1235_:
{
lean_object* v___x_1237_; lean_object* v_r_1238_; 
v___x_1237_ = lean_st_ref_set(v___y_1215_, v___x_1236_);
lean_inc(v___y_1215_);
lean_inc_ref(v___y_1214_);
v_r_1238_ = lean_apply_3(v_x_1212_, v___y_1214_, v___y_1215_, lean_box(0));
if (lean_obj_tag(v_r_1238_) == 0)
{
lean_object* v_a_1239_; lean_object* v___x_1241_; uint8_t v_isShared_1242_; uint8_t v_isSharedCheck_1255_; 
v_a_1239_ = lean_ctor_get(v_r_1238_, 0);
v_isSharedCheck_1255_ = !lean_is_exclusive(v_r_1238_);
if (v_isSharedCheck_1255_ == 0)
{
v___x_1241_ = v_r_1238_;
v_isShared_1242_ = v_isSharedCheck_1255_;
goto v_resetjp_1240_;
}
else
{
lean_inc(v_a_1239_);
lean_dec(v_r_1238_);
v___x_1241_ = lean_box(0);
v_isShared_1242_ = v_isSharedCheck_1255_;
goto v_resetjp_1240_;
}
v_resetjp_1240_:
{
lean_object* v___x_1244_; 
lean_inc(v_a_1239_);
if (v_isShared_1242_ == 0)
{
lean_ctor_set_tag(v___x_1241_, 1);
v___x_1244_ = v___x_1241_;
goto v_reusejp_1243_;
}
else
{
lean_object* v_reuseFailAlloc_1254_; 
v_reuseFailAlloc_1254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1254_, 0, v_a_1239_);
v___x_1244_ = v_reuseFailAlloc_1254_;
goto v_reusejp_1243_;
}
v_reusejp_1243_:
{
lean_object* v___x_1245_; lean_object* v___x_1247_; uint8_t v_isShared_1248_; uint8_t v_isSharedCheck_1252_; 
v___x_1245_ = l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___lam__0(v___y_1215_, v_isExporting_1219_, v___x_1234_, v___x_1244_);
lean_dec_ref(v___x_1244_);
v_isSharedCheck_1252_ = !lean_is_exclusive(v___x_1245_);
if (v_isSharedCheck_1252_ == 0)
{
lean_object* v_unused_1253_; 
v_unused_1253_ = lean_ctor_get(v___x_1245_, 0);
lean_dec(v_unused_1253_);
v___x_1247_ = v___x_1245_;
v_isShared_1248_ = v_isSharedCheck_1252_;
goto v_resetjp_1246_;
}
else
{
lean_dec(v___x_1245_);
v___x_1247_ = lean_box(0);
v_isShared_1248_ = v_isSharedCheck_1252_;
goto v_resetjp_1246_;
}
v_resetjp_1246_:
{
lean_object* v___x_1250_; 
if (v_isShared_1248_ == 0)
{
lean_ctor_set(v___x_1247_, 0, v_a_1239_);
v___x_1250_ = v___x_1247_;
goto v_reusejp_1249_;
}
else
{
lean_object* v_reuseFailAlloc_1251_; 
v_reuseFailAlloc_1251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1251_, 0, v_a_1239_);
v___x_1250_ = v_reuseFailAlloc_1251_;
goto v_reusejp_1249_;
}
v_reusejp_1249_:
{
return v___x_1250_;
}
}
}
}
}
else
{
lean_object* v_a_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1260_; uint8_t v_isShared_1261_; uint8_t v_isSharedCheck_1265_; 
v_a_1256_ = lean_ctor_get(v_r_1238_, 0);
lean_inc(v_a_1256_);
lean_dec_ref(v_r_1238_);
v___x_1257_ = lean_box(0);
v___x_1258_ = l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___lam__0(v___y_1215_, v_isExporting_1219_, v___x_1234_, v___x_1257_);
v_isSharedCheck_1265_ = !lean_is_exclusive(v___x_1258_);
if (v_isSharedCheck_1265_ == 0)
{
lean_object* v_unused_1266_; 
v_unused_1266_ = lean_ctor_get(v___x_1258_, 0);
lean_dec(v_unused_1266_);
v___x_1260_ = v___x_1258_;
v_isShared_1261_ = v_isSharedCheck_1265_;
goto v_resetjp_1259_;
}
else
{
lean_dec(v___x_1258_);
v___x_1260_ = lean_box(0);
v_isShared_1261_ = v_isSharedCheck_1265_;
goto v_resetjp_1259_;
}
v_resetjp_1259_:
{
lean_object* v___x_1263_; 
if (v_isShared_1261_ == 0)
{
lean_ctor_set_tag(v___x_1260_, 1);
lean_ctor_set(v___x_1260_, 0, v_a_1256_);
v___x_1263_ = v___x_1260_;
goto v_reusejp_1262_;
}
else
{
lean_object* v_reuseFailAlloc_1264_; 
v_reuseFailAlloc_1264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1264_, 0, v_a_1256_);
v___x_1263_ = v_reuseFailAlloc_1264_;
goto v_reusejp_1262_;
}
v_reusejp_1262_:
{
return v___x_1263_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___boxed(lean_object* v_x_1270_, lean_object* v_isExporting_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_){
_start:
{
uint8_t v_isExporting_boxed_1275_; lean_object* v_res_1276_; 
v_isExporting_boxed_1275_ = lean_unbox(v_isExporting_1271_);
v_res_1276_ = l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg(v_x_1270_, v_isExporting_boxed_1275_, v___y_1272_, v___y_1273_);
lean_dec(v___y_1273_);
lean_dec_ref(v___y_1272_);
return v_res_1276_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2(lean_object* v_00_u03b1_1277_, lean_object* v_x_1278_, uint8_t v_isExporting_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_){
_start:
{
lean_object* v___x_1283_; 
v___x_1283_ = l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg(v_x_1278_, v_isExporting_1279_, v___y_1280_, v___y_1281_);
return v___x_1283_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___boxed(lean_object* v_00_u03b1_1284_, lean_object* v_x_1285_, lean_object* v_isExporting_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_){
_start:
{
uint8_t v_isExporting_boxed_1290_; lean_object* v_res_1291_; 
v_isExporting_boxed_1290_ = lean_unbox(v_isExporting_1286_);
v_res_1291_ = l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2(v_00_u03b1_1284_, v_x_1285_, v_isExporting_boxed_1290_, v___y_1287_, v___y_1288_);
lean_dec(v___y_1288_);
lean_dec_ref(v___y_1287_);
return v_res_1291_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0_spec__3(lean_object* v_opts_1292_, lean_object* v_opt_1293_){
_start:
{
lean_object* v_name_1294_; lean_object* v_defValue_1295_; lean_object* v_map_1296_; lean_object* v___x_1297_; 
v_name_1294_ = lean_ctor_get(v_opt_1293_, 0);
v_defValue_1295_ = lean_ctor_get(v_opt_1293_, 1);
v_map_1296_ = lean_ctor_get(v_opts_1292_, 0);
v___x_1297_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1296_, v_name_1294_);
if (lean_obj_tag(v___x_1297_) == 0)
{
uint8_t v___x_1298_; 
v___x_1298_ = lean_unbox(v_defValue_1295_);
return v___x_1298_;
}
else
{
lean_object* v_val_1299_; 
v_val_1299_ = lean_ctor_get(v___x_1297_, 0);
lean_inc(v_val_1299_);
lean_dec_ref(v___x_1297_);
if (lean_obj_tag(v_val_1299_) == 1)
{
uint8_t v_v_1300_; 
v_v_1300_ = lean_ctor_get_uint8(v_val_1299_, 0);
lean_dec_ref(v_val_1299_);
return v_v_1300_;
}
else
{
uint8_t v___x_1301_; 
lean_dec(v_val_1299_);
v___x_1301_ = lean_unbox(v_defValue_1295_);
return v___x_1301_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0_spec__3___boxed(lean_object* v_opts_1302_, lean_object* v_opt_1303_){
_start:
{
uint8_t v_res_1304_; lean_object* v_r_1305_; 
v_res_1304_ = l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0_spec__3(v_opts_1302_, v_opt_1303_);
lean_dec_ref(v_opt_1303_);
lean_dec_ref(v_opts_1302_);
v_r_1305_ = lean_box(v_res_1304_);
return v_r_1305_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0(uint8_t v___y_1313_, uint8_t v_suppressElabErrors_1314_, lean_object* v_x_1315_){
_start:
{
if (lean_obj_tag(v_x_1315_) == 1)
{
lean_object* v_pre_1316_; 
v_pre_1316_ = lean_ctor_get(v_x_1315_, 0);
switch(lean_obj_tag(v_pre_1316_))
{
case 1:
{
lean_object* v_pre_1317_; 
v_pre_1317_ = lean_ctor_get(v_pre_1316_, 0);
switch(lean_obj_tag(v_pre_1317_))
{
case 0:
{
lean_object* v_str_1318_; lean_object* v_str_1319_; lean_object* v___x_1320_; uint8_t v___x_1321_; 
v_str_1318_ = lean_ctor_get(v_x_1315_, 1);
v_str_1319_ = lean_ctor_get(v_pre_1316_, 1);
v___x_1320_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__0));
v___x_1321_ = lean_string_dec_eq(v_str_1319_, v___x_1320_);
if (v___x_1321_ == 0)
{
lean_object* v___x_1322_; uint8_t v___x_1323_; 
v___x_1322_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__2));
v___x_1323_ = lean_string_dec_eq(v_str_1319_, v___x_1322_);
if (v___x_1323_ == 0)
{
return v___y_1313_;
}
else
{
lean_object* v___x_1324_; uint8_t v___x_1325_; 
v___x_1324_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__1));
v___x_1325_ = lean_string_dec_eq(v_str_1318_, v___x_1324_);
if (v___x_1325_ == 0)
{
return v___y_1313_;
}
else
{
return v_suppressElabErrors_1314_;
}
}
}
else
{
lean_object* v___x_1326_; uint8_t v___x_1327_; 
v___x_1326_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__2));
v___x_1327_ = lean_string_dec_eq(v_str_1318_, v___x_1326_);
if (v___x_1327_ == 0)
{
return v___y_1313_;
}
else
{
return v_suppressElabErrors_1314_;
}
}
}
case 1:
{
lean_object* v_pre_1328_; 
v_pre_1328_ = lean_ctor_get(v_pre_1317_, 0);
if (lean_obj_tag(v_pre_1328_) == 0)
{
lean_object* v_str_1329_; lean_object* v_str_1330_; lean_object* v_str_1331_; lean_object* v___x_1332_; uint8_t v___x_1333_; 
v_str_1329_ = lean_ctor_get(v_x_1315_, 1);
v_str_1330_ = lean_ctor_get(v_pre_1316_, 1);
v_str_1331_ = lean_ctor_get(v_pre_1317_, 1);
v___x_1332_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__3));
v___x_1333_ = lean_string_dec_eq(v_str_1331_, v___x_1332_);
if (v___x_1333_ == 0)
{
return v___y_1313_;
}
else
{
lean_object* v___x_1334_; uint8_t v___x_1335_; 
v___x_1334_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__4));
v___x_1335_ = lean_string_dec_eq(v_str_1330_, v___x_1334_);
if (v___x_1335_ == 0)
{
return v___y_1313_;
}
else
{
lean_object* v___x_1336_; uint8_t v___x_1337_; 
v___x_1336_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__5));
v___x_1337_ = lean_string_dec_eq(v_str_1329_, v___x_1336_);
if (v___x_1337_ == 0)
{
return v___y_1313_;
}
else
{
return v_suppressElabErrors_1314_;
}
}
}
}
else
{
return v___y_1313_;
}
}
default: 
{
return v___y_1313_;
}
}
}
case 0:
{
lean_object* v_str_1338_; lean_object* v___x_1339_; uint8_t v___x_1340_; 
v_str_1338_ = lean_ctor_get(v_x_1315_, 1);
v___x_1339_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__6));
v___x_1340_ = lean_string_dec_eq(v_str_1338_, v___x_1339_);
if (v___x_1340_ == 0)
{
return v___y_1313_;
}
else
{
return v_suppressElabErrors_1314_;
}
}
default: 
{
return v___y_1313_;
}
}
}
else
{
return v___y_1313_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___boxed(lean_object* v___y_1341_, lean_object* v_suppressElabErrors_1342_, lean_object* v_x_1343_){
_start:
{
uint8_t v___y_5010__boxed_1344_; uint8_t v_suppressElabErrors_boxed_1345_; uint8_t v_res_1346_; lean_object* v_r_1347_; 
v___y_5010__boxed_1344_ = lean_unbox(v___y_1341_);
v_suppressElabErrors_boxed_1345_ = lean_unbox(v_suppressElabErrors_1342_);
v_res_1346_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0(v___y_5010__boxed_1344_, v_suppressElabErrors_boxed_1345_, v_x_1343_);
lean_dec(v_x_1343_);
v_r_1347_ = lean_box(v_res_1346_);
return v_r_1347_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6(lean_object* v_ref_1348_, lean_object* v_msgData_1349_, uint8_t v_severity_1350_, uint8_t v_isSilent_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_){
_start:
{
lean_object* v___y_1356_; lean_object* v___y_1357_; lean_object* v___y_1358_; lean_object* v___y_1359_; lean_object* v___y_1360_; uint8_t v___y_1361_; uint8_t v___y_1362_; lean_object* v___y_1363_; lean_object* v___y_1364_; lean_object* v___y_1393_; lean_object* v___y_1394_; lean_object* v___y_1395_; uint8_t v___y_1396_; uint8_t v___y_1397_; lean_object* v___y_1398_; uint8_t v___y_1399_; lean_object* v___y_1400_; lean_object* v___y_1418_; lean_object* v___y_1419_; lean_object* v___y_1420_; uint8_t v___y_1421_; lean_object* v___y_1422_; uint8_t v___y_1423_; uint8_t v___y_1424_; lean_object* v___y_1425_; lean_object* v___y_1429_; lean_object* v___y_1430_; lean_object* v___y_1431_; uint8_t v___y_1432_; lean_object* v___y_1433_; uint8_t v___y_1434_; uint8_t v___y_1435_; uint8_t v___x_1440_; lean_object* v___y_1442_; lean_object* v___y_1443_; lean_object* v___y_1444_; lean_object* v___y_1445_; uint8_t v___y_1446_; uint8_t v___y_1447_; uint8_t v___y_1448_; uint8_t v___y_1450_; uint8_t v___x_1465_; 
v___x_1440_ = 2;
v___x_1465_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1350_, v___x_1440_);
if (v___x_1465_ == 0)
{
v___y_1450_ = v___x_1465_;
goto v___jp_1449_;
}
else
{
uint8_t v___x_1466_; 
lean_inc_ref(v_msgData_1349_);
v___x_1466_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_1349_);
v___y_1450_ = v___x_1466_;
goto v___jp_1449_;
}
v___jp_1355_:
{
lean_object* v___x_1365_; lean_object* v_currNamespace_1366_; lean_object* v_openDecls_1367_; lean_object* v_env_1368_; lean_object* v_nextMacroScope_1369_; lean_object* v_ngen_1370_; lean_object* v_auxDeclNGen_1371_; lean_object* v_traceState_1372_; lean_object* v_cache_1373_; lean_object* v_messages_1374_; lean_object* v_infoState_1375_; lean_object* v_snapshotTasks_1376_; lean_object* v_newDecls_1377_; lean_object* v___x_1379_; uint8_t v_isShared_1380_; uint8_t v_isSharedCheck_1391_; 
v___x_1365_ = lean_st_ref_take(v___y_1364_);
v_currNamespace_1366_ = lean_ctor_get(v___y_1363_, 6);
v_openDecls_1367_ = lean_ctor_get(v___y_1363_, 7);
v_env_1368_ = lean_ctor_get(v___x_1365_, 0);
v_nextMacroScope_1369_ = lean_ctor_get(v___x_1365_, 1);
v_ngen_1370_ = lean_ctor_get(v___x_1365_, 2);
v_auxDeclNGen_1371_ = lean_ctor_get(v___x_1365_, 3);
v_traceState_1372_ = lean_ctor_get(v___x_1365_, 4);
v_cache_1373_ = lean_ctor_get(v___x_1365_, 5);
v_messages_1374_ = lean_ctor_get(v___x_1365_, 6);
v_infoState_1375_ = lean_ctor_get(v___x_1365_, 7);
v_snapshotTasks_1376_ = lean_ctor_get(v___x_1365_, 8);
v_newDecls_1377_ = lean_ctor_get(v___x_1365_, 9);
v_isSharedCheck_1391_ = !lean_is_exclusive(v___x_1365_);
if (v_isSharedCheck_1391_ == 0)
{
v___x_1379_ = v___x_1365_;
v_isShared_1380_ = v_isSharedCheck_1391_;
goto v_resetjp_1378_;
}
else
{
lean_inc(v_newDecls_1377_);
lean_inc(v_snapshotTasks_1376_);
lean_inc(v_infoState_1375_);
lean_inc(v_messages_1374_);
lean_inc(v_cache_1373_);
lean_inc(v_traceState_1372_);
lean_inc(v_auxDeclNGen_1371_);
lean_inc(v_ngen_1370_);
lean_inc(v_nextMacroScope_1369_);
lean_inc(v_env_1368_);
lean_dec(v___x_1365_);
v___x_1379_ = lean_box(0);
v_isShared_1380_ = v_isSharedCheck_1391_;
goto v_resetjp_1378_;
}
v_resetjp_1378_:
{
lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1386_; 
lean_inc(v_openDecls_1367_);
lean_inc(v_currNamespace_1366_);
v___x_1381_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1381_, 0, v_currNamespace_1366_);
lean_ctor_set(v___x_1381_, 1, v_openDecls_1367_);
v___x_1382_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1382_, 0, v___x_1381_);
lean_ctor_set(v___x_1382_, 1, v___y_1360_);
lean_inc_ref(v___y_1356_);
lean_inc_ref(v___y_1359_);
v___x_1383_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1383_, 0, v___y_1359_);
lean_ctor_set(v___x_1383_, 1, v___y_1357_);
lean_ctor_set(v___x_1383_, 2, v___y_1358_);
lean_ctor_set(v___x_1383_, 3, v___y_1356_);
lean_ctor_set(v___x_1383_, 4, v___x_1382_);
lean_ctor_set_uint8(v___x_1383_, sizeof(void*)*5, v___y_1361_);
lean_ctor_set_uint8(v___x_1383_, sizeof(void*)*5 + 1, v___y_1362_);
lean_ctor_set_uint8(v___x_1383_, sizeof(void*)*5 + 2, v_isSilent_1351_);
v___x_1384_ = l_Lean_MessageLog_add(v___x_1383_, v_messages_1374_);
if (v_isShared_1380_ == 0)
{
lean_ctor_set(v___x_1379_, 6, v___x_1384_);
v___x_1386_ = v___x_1379_;
goto v_reusejp_1385_;
}
else
{
lean_object* v_reuseFailAlloc_1390_; 
v_reuseFailAlloc_1390_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1390_, 0, v_env_1368_);
lean_ctor_set(v_reuseFailAlloc_1390_, 1, v_nextMacroScope_1369_);
lean_ctor_set(v_reuseFailAlloc_1390_, 2, v_ngen_1370_);
lean_ctor_set(v_reuseFailAlloc_1390_, 3, v_auxDeclNGen_1371_);
lean_ctor_set(v_reuseFailAlloc_1390_, 4, v_traceState_1372_);
lean_ctor_set(v_reuseFailAlloc_1390_, 5, v_cache_1373_);
lean_ctor_set(v_reuseFailAlloc_1390_, 6, v___x_1384_);
lean_ctor_set(v_reuseFailAlloc_1390_, 7, v_infoState_1375_);
lean_ctor_set(v_reuseFailAlloc_1390_, 8, v_snapshotTasks_1376_);
lean_ctor_set(v_reuseFailAlloc_1390_, 9, v_newDecls_1377_);
v___x_1386_ = v_reuseFailAlloc_1390_;
goto v_reusejp_1385_;
}
v_reusejp_1385_:
{
lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; 
v___x_1387_ = lean_st_ref_set(v___y_1364_, v___x_1386_);
v___x_1388_ = lean_box(0);
v___x_1389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1389_, 0, v___x_1388_);
return v___x_1389_;
}
}
}
v___jp_1392_:
{
lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v_a_1403_; lean_object* v___x_1405_; uint8_t v_isShared_1406_; uint8_t v_isSharedCheck_1416_; 
v___x_1401_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_1349_);
v___x_1402_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0(v___x_1401_, v___y_1352_, v___y_1353_);
v_a_1403_ = lean_ctor_get(v___x_1402_, 0);
v_isSharedCheck_1416_ = !lean_is_exclusive(v___x_1402_);
if (v_isSharedCheck_1416_ == 0)
{
v___x_1405_ = v___x_1402_;
v_isShared_1406_ = v_isSharedCheck_1416_;
goto v_resetjp_1404_;
}
else
{
lean_inc(v_a_1403_);
lean_dec(v___x_1402_);
v___x_1405_ = lean_box(0);
v_isShared_1406_ = v_isSharedCheck_1416_;
goto v_resetjp_1404_;
}
v_resetjp_1404_:
{
lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; 
lean_inc_ref_n(v___y_1394_, 2);
v___x_1407_ = l_Lean_FileMap_toPosition(v___y_1394_, v___y_1398_);
lean_dec(v___y_1398_);
v___x_1408_ = l_Lean_FileMap_toPosition(v___y_1394_, v___y_1400_);
lean_dec(v___y_1400_);
v___x_1409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1409_, 0, v___x_1408_);
v___x_1410_ = ((lean_object*)(l_Lean_instInhabitedAttributeImplCore_default___closed__3));
if (v___y_1397_ == 0)
{
lean_del_object(v___x_1405_);
lean_dec_ref(v___y_1393_);
v___y_1356_ = v___x_1410_;
v___y_1357_ = v___x_1407_;
v___y_1358_ = v___x_1409_;
v___y_1359_ = v___y_1395_;
v___y_1360_ = v_a_1403_;
v___y_1361_ = v___y_1396_;
v___y_1362_ = v___y_1399_;
v___y_1363_ = v___y_1352_;
v___y_1364_ = v___y_1353_;
goto v___jp_1355_;
}
else
{
uint8_t v___x_1411_; 
lean_inc(v_a_1403_);
v___x_1411_ = l_Lean_MessageData_hasTag(v___y_1393_, v_a_1403_);
if (v___x_1411_ == 0)
{
lean_object* v___x_1412_; lean_object* v___x_1414_; 
lean_dec_ref(v___x_1409_);
lean_dec_ref(v___x_1407_);
lean_dec(v_a_1403_);
v___x_1412_ = lean_box(0);
if (v_isShared_1406_ == 0)
{
lean_ctor_set(v___x_1405_, 0, v___x_1412_);
v___x_1414_ = v___x_1405_;
goto v_reusejp_1413_;
}
else
{
lean_object* v_reuseFailAlloc_1415_; 
v_reuseFailAlloc_1415_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1415_, 0, v___x_1412_);
v___x_1414_ = v_reuseFailAlloc_1415_;
goto v_reusejp_1413_;
}
v_reusejp_1413_:
{
return v___x_1414_;
}
}
else
{
lean_del_object(v___x_1405_);
v___y_1356_ = v___x_1410_;
v___y_1357_ = v___x_1407_;
v___y_1358_ = v___x_1409_;
v___y_1359_ = v___y_1395_;
v___y_1360_ = v_a_1403_;
v___y_1361_ = v___y_1396_;
v___y_1362_ = v___y_1399_;
v___y_1363_ = v___y_1352_;
v___y_1364_ = v___y_1353_;
goto v___jp_1355_;
}
}
}
}
v___jp_1417_:
{
lean_object* v___x_1426_; 
v___x_1426_ = l_Lean_Syntax_getTailPos_x3f(v___y_1422_, v___y_1421_);
lean_dec(v___y_1422_);
if (lean_obj_tag(v___x_1426_) == 0)
{
lean_inc(v___y_1425_);
v___y_1393_ = v___y_1418_;
v___y_1394_ = v___y_1419_;
v___y_1395_ = v___y_1420_;
v___y_1396_ = v___y_1421_;
v___y_1397_ = v___y_1423_;
v___y_1398_ = v___y_1425_;
v___y_1399_ = v___y_1424_;
v___y_1400_ = v___y_1425_;
goto v___jp_1392_;
}
else
{
lean_object* v_val_1427_; 
v_val_1427_ = lean_ctor_get(v___x_1426_, 0);
lean_inc(v_val_1427_);
lean_dec_ref(v___x_1426_);
v___y_1393_ = v___y_1418_;
v___y_1394_ = v___y_1419_;
v___y_1395_ = v___y_1420_;
v___y_1396_ = v___y_1421_;
v___y_1397_ = v___y_1423_;
v___y_1398_ = v___y_1425_;
v___y_1399_ = v___y_1424_;
v___y_1400_ = v_val_1427_;
goto v___jp_1392_;
}
}
v___jp_1428_:
{
lean_object* v_ref_1436_; lean_object* v___x_1437_; 
v_ref_1436_ = l_Lean_replaceRef(v_ref_1348_, v___y_1433_);
v___x_1437_ = l_Lean_Syntax_getPos_x3f(v_ref_1436_, v___y_1432_);
if (lean_obj_tag(v___x_1437_) == 0)
{
lean_object* v___x_1438_; 
v___x_1438_ = lean_unsigned_to_nat(0u);
v___y_1418_ = v___y_1429_;
v___y_1419_ = v___y_1430_;
v___y_1420_ = v___y_1431_;
v___y_1421_ = v___y_1432_;
v___y_1422_ = v_ref_1436_;
v___y_1423_ = v___y_1434_;
v___y_1424_ = v___y_1435_;
v___y_1425_ = v___x_1438_;
goto v___jp_1417_;
}
else
{
lean_object* v_val_1439_; 
v_val_1439_ = lean_ctor_get(v___x_1437_, 0);
lean_inc(v_val_1439_);
lean_dec_ref(v___x_1437_);
v___y_1418_ = v___y_1429_;
v___y_1419_ = v___y_1430_;
v___y_1420_ = v___y_1431_;
v___y_1421_ = v___y_1432_;
v___y_1422_ = v_ref_1436_;
v___y_1423_ = v___y_1434_;
v___y_1424_ = v___y_1435_;
v___y_1425_ = v_val_1439_;
goto v___jp_1417_;
}
}
v___jp_1441_:
{
if (v___y_1448_ == 0)
{
v___y_1429_ = v___y_1442_;
v___y_1430_ = v___y_1443_;
v___y_1431_ = v___y_1444_;
v___y_1432_ = v___y_1447_;
v___y_1433_ = v___y_1445_;
v___y_1434_ = v___y_1446_;
v___y_1435_ = v_severity_1350_;
goto v___jp_1428_;
}
else
{
v___y_1429_ = v___y_1442_;
v___y_1430_ = v___y_1443_;
v___y_1431_ = v___y_1444_;
v___y_1432_ = v___y_1447_;
v___y_1433_ = v___y_1445_;
v___y_1434_ = v___y_1446_;
v___y_1435_ = v___x_1440_;
goto v___jp_1428_;
}
}
v___jp_1449_:
{
if (v___y_1450_ == 0)
{
lean_object* v_fileName_1451_; lean_object* v_fileMap_1452_; lean_object* v_options_1453_; lean_object* v_ref_1454_; uint8_t v_suppressElabErrors_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___f_1458_; uint8_t v___x_1459_; uint8_t v___x_1460_; 
v_fileName_1451_ = lean_ctor_get(v___y_1352_, 0);
v_fileMap_1452_ = lean_ctor_get(v___y_1352_, 1);
v_options_1453_ = lean_ctor_get(v___y_1352_, 2);
v_ref_1454_ = lean_ctor_get(v___y_1352_, 5);
v_suppressElabErrors_1455_ = lean_ctor_get_uint8(v___y_1352_, sizeof(void*)*14 + 1);
v___x_1456_ = lean_box(v___y_1450_);
v___x_1457_ = lean_box(v_suppressElabErrors_1455_);
v___f_1458_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1458_, 0, v___x_1456_);
lean_closure_set(v___f_1458_, 1, v___x_1457_);
v___x_1459_ = 1;
v___x_1460_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1350_, v___x_1459_);
if (v___x_1460_ == 0)
{
v___y_1442_ = v___f_1458_;
v___y_1443_ = v_fileMap_1452_;
v___y_1444_ = v_fileName_1451_;
v___y_1445_ = v_ref_1454_;
v___y_1446_ = v_suppressElabErrors_1455_;
v___y_1447_ = v___y_1450_;
v___y_1448_ = v___x_1460_;
goto v___jp_1441_;
}
else
{
lean_object* v___x_1461_; uint8_t v___x_1462_; 
v___x_1461_ = l_Lean_warningAsError;
v___x_1462_ = l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0_spec__3(v_options_1453_, v___x_1461_);
v___y_1442_ = v___f_1458_;
v___y_1443_ = v_fileMap_1452_;
v___y_1444_ = v_fileName_1451_;
v___y_1445_ = v_ref_1454_;
v___y_1446_ = v_suppressElabErrors_1455_;
v___y_1447_ = v___y_1450_;
v___y_1448_ = v___x_1462_;
goto v___jp_1441_;
}
}
else
{
lean_object* v___x_1463_; lean_object* v___x_1464_; 
lean_dec_ref(v_msgData_1349_);
v___x_1463_ = lean_box(0);
v___x_1464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1464_, 0, v___x_1463_);
return v___x_1464_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___boxed(lean_object* v_ref_1467_, lean_object* v_msgData_1468_, lean_object* v_severity_1469_, lean_object* v_isSilent_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_){
_start:
{
uint8_t v_severity_boxed_1474_; uint8_t v_isSilent_boxed_1475_; lean_object* v_res_1476_; 
v_severity_boxed_1474_ = lean_unbox(v_severity_1469_);
v_isSilent_boxed_1475_ = lean_unbox(v_isSilent_1470_);
v_res_1476_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6(v_ref_1467_, v_msgData_1468_, v_severity_boxed_1474_, v_isSilent_boxed_1475_, v___y_1471_, v___y_1472_);
lean_dec(v___y_1472_);
lean_dec_ref(v___y_1471_);
lean_dec(v_ref_1467_);
return v_res_1476_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5(lean_object* v_msgData_1477_, uint8_t v_severity_1478_, uint8_t v_isSilent_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_){
_start:
{
lean_object* v_ref_1483_; lean_object* v___x_1484_; 
v_ref_1483_ = lean_ctor_get(v___y_1480_, 5);
v___x_1484_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6(v_ref_1483_, v_msgData_1477_, v_severity_1478_, v_isSilent_1479_, v___y_1480_, v___y_1481_);
return v___x_1484_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5___boxed(lean_object* v_msgData_1485_, lean_object* v_severity_1486_, lean_object* v_isSilent_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_){
_start:
{
uint8_t v_severity_boxed_1491_; uint8_t v_isSilent_boxed_1492_; lean_object* v_res_1493_; 
v_severity_boxed_1491_ = lean_unbox(v_severity_1486_);
v_isSilent_boxed_1492_ = lean_unbox(v_isSilent_1487_);
v_res_1493_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5(v_msgData_1485_, v_severity_boxed_1491_, v_isSilent_boxed_1492_, v___y_1488_, v___y_1489_);
lean_dec(v___y_1489_);
lean_dec_ref(v___y_1488_);
return v_res_1493_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1(lean_object* v_msgData_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_){
_start:
{
uint8_t v___x_1498_; uint8_t v___x_1499_; lean_object* v___x_1500_; 
v___x_1498_ = 1;
v___x_1499_ = 0;
v___x_1500_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5(v_msgData_1494_, v___x_1498_, v___x_1499_, v___y_1495_, v___y_1496_);
return v___x_1500_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1___boxed(lean_object* v_msgData_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_){
_start:
{
lean_object* v_res_1505_; 
v_res_1505_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1(v_msgData_1501_, v___y_1502_, v___y_1503_);
lean_dec(v___y_1503_);
lean_dec_ref(v___y_1502_);
return v_res_1505_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0___redArg(lean_object* v_opt_1506_, lean_object* v___y_1507_){
_start:
{
lean_object* v_options_1509_; uint8_t v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; 
v_options_1509_ = lean_ctor_get(v___y_1507_, 2);
v___x_1510_ = l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0_spec__3(v_options_1509_, v_opt_1506_);
v___x_1511_ = lean_box(v___x_1510_);
v___x_1512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1512_, 0, v___x_1511_);
return v___x_1512_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0___redArg___boxed(lean_object* v_opt_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_){
_start:
{
lean_object* v_res_1516_; 
v_res_1516_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0___redArg(v_opt_1513_, v___y_1514_);
lean_dec_ref(v___y_1514_);
lean_dec_ref(v_opt_1513_);
return v_res_1516_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1518_; lean_object* v___x_1519_; 
v___x_1518_ = ((lean_object*)(l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__0));
v___x_1519_ = l_Lean_stringToMessageData(v___x_1518_);
return v___x_1519_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__3(void){
_start:
{
lean_object* v___x_1521_; lean_object* v___x_1522_; 
v___x_1521_ = ((lean_object*)(l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__2));
v___x_1522_ = l_Lean_stringToMessageData(v___x_1521_);
return v___x_1522_;
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0(lean_object* v_id_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_){
_start:
{
lean_object* v___x_1527_; lean_object* v_env_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v_a_1531_; lean_object* v___x_1533_; uint8_t v_isShared_1534_; uint8_t v_isSharedCheck_1550_; 
v___x_1527_ = lean_st_ref_get(v___y_1525_);
v_env_1528_ = lean_ctor_get(v___x_1527_, 0);
lean_inc_ref(v_env_1528_);
lean_dec(v___x_1527_);
v___x_1529_ = l_Lean_ResolveName_backward_privateInPublic_warn;
v___x_1530_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0___redArg(v___x_1529_, v___y_1524_);
v_a_1531_ = lean_ctor_get(v___x_1530_, 0);
v_isSharedCheck_1550_ = !lean_is_exclusive(v___x_1530_);
if (v_isSharedCheck_1550_ == 0)
{
v___x_1533_ = v___x_1530_;
v_isShared_1534_ = v_isSharedCheck_1550_;
goto v_resetjp_1532_;
}
else
{
lean_inc(v_a_1531_);
lean_dec(v___x_1530_);
v___x_1533_ = lean_box(0);
v_isShared_1534_ = v_isSharedCheck_1550_;
goto v_resetjp_1532_;
}
v_resetjp_1532_:
{
uint8_t v_isExporting_1540_; 
v_isExporting_1540_ = lean_ctor_get_uint8(v_env_1528_, sizeof(void*)*8);
lean_dec_ref(v_env_1528_);
if (v_isExporting_1540_ == 0)
{
lean_dec(v_a_1531_);
lean_dec(v_id_1523_);
goto v___jp_1535_;
}
else
{
uint8_t v___x_1541_; 
v___x_1541_ = l_Lean_isPrivateName(v_id_1523_);
if (v___x_1541_ == 0)
{
lean_dec(v_a_1531_);
lean_dec(v_id_1523_);
goto v___jp_1535_;
}
else
{
uint8_t v___x_1542_; 
v___x_1542_ = lean_unbox(v_a_1531_);
lean_dec(v_a_1531_);
if (v___x_1542_ == 0)
{
lean_dec(v_id_1523_);
goto v___jp_1535_;
}
else
{
lean_object* v___x_1543_; uint8_t v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; 
lean_del_object(v___x_1533_);
v___x_1543_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__1, &l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__1_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__1);
v___x_1544_ = 0;
v___x_1545_ = l_Lean_MessageData_ofConstName(v_id_1523_, v___x_1544_);
v___x_1546_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1546_, 0, v___x_1543_);
lean_ctor_set(v___x_1546_, 1, v___x_1545_);
v___x_1547_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__3, &l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__3_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__3);
v___x_1548_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1548_, 0, v___x_1546_);
lean_ctor_set(v___x_1548_, 1, v___x_1547_);
v___x_1549_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1(v___x_1548_, v___y_1524_, v___y_1525_);
return v___x_1549_;
}
}
}
v___jp_1535_:
{
lean_object* v___x_1536_; lean_object* v___x_1538_; 
v___x_1536_ = lean_box(0);
if (v_isShared_1534_ == 0)
{
lean_ctor_set(v___x_1533_, 0, v___x_1536_);
v___x_1538_ = v___x_1533_;
goto v_reusejp_1537_;
}
else
{
lean_object* v_reuseFailAlloc_1539_; 
v_reuseFailAlloc_1539_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1539_, 0, v___x_1536_);
v___x_1538_ = v_reuseFailAlloc_1539_;
goto v_reusejp_1537_;
}
v_reusejp_1537_:
{
return v___x_1538_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___boxed(lean_object* v_id_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_){
_start:
{
lean_object* v_res_1555_; 
v_res_1555_ = l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0(v_id_1551_, v___y_1552_, v___y_1553_);
lean_dec(v___y_1553_);
lean_dec_ref(v___y_1552_);
return v_res_1555_;
}
}
static lean_object* _init_l_Lean_ensureAttrDeclIsPublic___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1557_; lean_object* v___x_1558_; 
v___x_1557_ = ((lean_object*)(l_Lean_ensureAttrDeclIsPublic___lam__0___closed__0));
v___x_1558_ = l_Lean_stringToMessageData(v___x_1557_);
return v___x_1558_;
}
}
LEAN_EXPORT lean_object* l_Lean_ensureAttrDeclIsPublic___lam__0(lean_object* v_declName_1559_, uint8_t v_isModule_1560_, lean_object* v_attrName_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_){
_start:
{
lean_object* v___x_1565_; 
lean_inc(v_declName_1559_);
v___x_1565_ = l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0(v_declName_1559_, v___y_1562_, v___y_1563_);
if (lean_obj_tag(v___x_1565_) == 0)
{
lean_object* v___x_1566_; lean_object* v_a_1567_; lean_object* v___x_1569_; uint8_t v_isShared_1570_; uint8_t v_isSharedCheck_1587_; 
lean_dec_ref(v___x_1565_);
lean_inc(v_declName_1559_);
v___x_1566_ = l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1___redArg(v_declName_1559_, v_isModule_1560_, v___y_1563_);
v_a_1567_ = lean_ctor_get(v___x_1566_, 0);
v_isSharedCheck_1587_ = !lean_is_exclusive(v___x_1566_);
if (v_isSharedCheck_1587_ == 0)
{
v___x_1569_ = v___x_1566_;
v_isShared_1570_ = v_isSharedCheck_1587_;
goto v_resetjp_1568_;
}
else
{
lean_inc(v_a_1567_);
lean_dec(v___x_1566_);
v___x_1569_ = lean_box(0);
v_isShared_1570_ = v_isSharedCheck_1587_;
goto v_resetjp_1568_;
}
v_resetjp_1568_:
{
uint8_t v___x_1571_; 
v___x_1571_ = lean_unbox(v_a_1567_);
if (v___x_1571_ == 0)
{
lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; uint8_t v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; 
lean_del_object(v___x_1569_);
v___x_1572_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1);
v___x_1573_ = l_Lean_MessageData_ofName(v_attrName_1561_);
v___x_1574_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1574_, 0, v___x_1572_);
lean_ctor_set(v___x_1574_, 1, v___x_1573_);
v___x_1575_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1, &l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1);
v___x_1576_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1576_, 0, v___x_1574_);
lean_ctor_set(v___x_1576_, 1, v___x_1575_);
v___x_1577_ = lean_unbox(v_a_1567_);
lean_dec(v_a_1567_);
v___x_1578_ = l_Lean_MessageData_ofConstName(v_declName_1559_, v___x_1577_);
v___x_1579_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1579_, 0, v___x_1576_);
lean_ctor_set(v___x_1579_, 1, v___x_1578_);
v___x_1580_ = lean_obj_once(&l_Lean_ensureAttrDeclIsPublic___lam__0___closed__1, &l_Lean_ensureAttrDeclIsPublic___lam__0___closed__1_once, _init_l_Lean_ensureAttrDeclIsPublic___lam__0___closed__1);
v___x_1581_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1581_, 0, v___x_1579_);
lean_ctor_set(v___x_1581_, 1, v___x_1580_);
v___x_1582_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_1581_, v___y_1562_, v___y_1563_);
return v___x_1582_;
}
else
{
lean_object* v___x_1583_; lean_object* v___x_1585_; 
lean_dec(v_a_1567_);
lean_dec(v_attrName_1561_);
lean_dec(v_declName_1559_);
v___x_1583_ = lean_box(0);
if (v_isShared_1570_ == 0)
{
lean_ctor_set(v___x_1569_, 0, v___x_1583_);
v___x_1585_ = v___x_1569_;
goto v_reusejp_1584_;
}
else
{
lean_object* v_reuseFailAlloc_1586_; 
v_reuseFailAlloc_1586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1586_, 0, v___x_1583_);
v___x_1585_ = v_reuseFailAlloc_1586_;
goto v_reusejp_1584_;
}
v_reusejp_1584_:
{
return v___x_1585_;
}
}
}
}
else
{
lean_dec(v_attrName_1561_);
lean_dec(v_declName_1559_);
return v___x_1565_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ensureAttrDeclIsPublic___lam__0___boxed(lean_object* v_declName_1588_, lean_object* v_isModule_1589_, lean_object* v_attrName_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_){
_start:
{
uint8_t v_isModule_boxed_1594_; lean_object* v_res_1595_; 
v_isModule_boxed_1594_ = lean_unbox(v_isModule_1589_);
v_res_1595_ = l_Lean_ensureAttrDeclIsPublic___lam__0(v_declName_1588_, v_isModule_boxed_1594_, v_attrName_1590_, v___y_1591_, v___y_1592_);
lean_dec(v___y_1592_);
lean_dec_ref(v___y_1591_);
return v_res_1595_;
}
}
LEAN_EXPORT lean_object* l_Lean_ensureAttrDeclIsPublic(lean_object* v_attrName_1596_, lean_object* v_declName_1597_, uint8_t v_attrKind_1598_, lean_object* v_a_1599_, lean_object* v_a_1600_){
_start:
{
lean_object* v___x_1602_; lean_object* v_env_1606_; lean_object* v___x_1607_; uint8_t v_isModule_1608_; 
v___x_1602_ = lean_st_ref_get(v_a_1600_);
v_env_1606_ = lean_ctor_get(v___x_1602_, 0);
lean_inc_ref(v_env_1606_);
lean_dec(v___x_1602_);
v___x_1607_ = l_Lean_Environment_header(v_env_1606_);
lean_dec_ref(v_env_1606_);
v_isModule_1608_ = lean_ctor_get_uint8(v___x_1607_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_1607_);
if (v_isModule_1608_ == 0)
{
lean_dec(v_declName_1597_);
lean_dec(v_attrName_1596_);
goto v___jp_1603_;
}
else
{
uint8_t v___x_1609_; uint8_t v___x_1610_; 
v___x_1609_ = 1;
v___x_1610_ = l_Lean_instBEqAttributeKind_beq(v_attrKind_1598_, v___x_1609_);
if (v___x_1610_ == 0)
{
lean_object* v___x_1611_; lean_object* v___f_1612_; lean_object* v___x_1613_; 
v___x_1611_ = lean_box(v_isModule_1608_);
v___f_1612_ = lean_alloc_closure((void*)(l_Lean_ensureAttrDeclIsPublic___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1612_, 0, v_declName_1597_);
lean_closure_set(v___f_1612_, 1, v___x_1611_);
lean_closure_set(v___f_1612_, 2, v_attrName_1596_);
v___x_1613_ = l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg(v___f_1612_, v_isModule_1608_, v_a_1599_, v_a_1600_);
return v___x_1613_;
}
else
{
lean_dec(v_declName_1597_);
lean_dec(v_attrName_1596_);
goto v___jp_1603_;
}
}
v___jp_1603_:
{
lean_object* v___x_1604_; lean_object* v___x_1605_; 
v___x_1604_ = lean_box(0);
v___x_1605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1605_, 0, v___x_1604_);
return v___x_1605_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ensureAttrDeclIsPublic___boxed(lean_object* v_attrName_1614_, lean_object* v_declName_1615_, lean_object* v_attrKind_1616_, lean_object* v_a_1617_, lean_object* v_a_1618_, lean_object* v_a_1619_){
_start:
{
uint8_t v_attrKind_boxed_1620_; lean_object* v_res_1621_; 
v_attrKind_boxed_1620_ = lean_unbox(v_attrKind_1616_);
v_res_1621_ = l_Lean_ensureAttrDeclIsPublic(v_attrName_1614_, v_declName_1615_, v_attrKind_boxed_1620_, v_a_1617_, v_a_1618_);
lean_dec(v_a_1618_);
lean_dec_ref(v_a_1617_);
return v_res_1621_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0(lean_object* v_opt_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_){
_start:
{
lean_object* v___x_1626_; 
v___x_1626_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0___redArg(v_opt_1622_, v___y_1623_);
return v___x_1626_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0___boxed(lean_object* v_opt_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_){
_start:
{
lean_object* v_res_1631_; 
v_res_1631_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0(v_opt_1627_, v___y_1628_, v___y_1629_);
lean_dec(v___y_1629_);
lean_dec_ref(v___y_1628_);
lean_dec_ref(v_opt_1627_);
return v_res_1631_;
}
}
static lean_object* _init_l_Lean_ensureAttrDeclIsMeta___closed__1(void){
_start:
{
lean_object* v___x_1633_; lean_object* v___x_1634_; 
v___x_1633_ = ((lean_object*)(l_Lean_ensureAttrDeclIsMeta___closed__0));
v___x_1634_ = l_Lean_stringToMessageData(v___x_1633_);
return v___x_1634_;
}
}
LEAN_EXPORT lean_object* l_Lean_ensureAttrDeclIsMeta(lean_object* v_attrName_1635_, lean_object* v_declName_1636_, uint8_t v_attrKind_1637_, lean_object* v_a_1638_, lean_object* v_a_1639_){
_start:
{
lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v_env_1643_; lean_object* v___x_1644_; uint8_t v_isModule_1645_; 
v___x_1641_ = lean_st_ref_get(v_a_1639_);
v___x_1642_ = lean_st_ref_get(v_a_1639_);
v_env_1643_ = lean_ctor_get(v___x_1641_, 0);
lean_inc_ref(v_env_1643_);
lean_dec(v___x_1641_);
v___x_1644_ = l_Lean_Environment_header(v_env_1643_);
lean_dec_ref(v_env_1643_);
v_isModule_1645_ = lean_ctor_get_uint8(v___x_1644_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_1644_);
if (v_isModule_1645_ == 0)
{
lean_object* v___x_1646_; 
lean_dec(v___x_1642_);
v___x_1646_ = l_Lean_ensureAttrDeclIsPublic(v_attrName_1635_, v_declName_1636_, v_attrKind_1637_, v_a_1638_, v_a_1639_);
return v___x_1646_;
}
else
{
lean_object* v_env_1647_; uint8_t v___x_1648_; 
v_env_1647_ = lean_ctor_get(v___x_1642_, 0);
lean_inc_ref(v_env_1647_);
lean_dec(v___x_1642_);
lean_inc(v_declName_1636_);
v___x_1648_ = l_Lean_isMarkedMeta(v_env_1647_, v_declName_1636_);
if (v___x_1648_ == 0)
{
lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; 
v___x_1649_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1);
v___x_1650_ = l_Lean_MessageData_ofName(v_attrName_1635_);
v___x_1651_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1651_, 0, v___x_1649_);
lean_ctor_set(v___x_1651_, 1, v___x_1650_);
v___x_1652_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1, &l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1);
v___x_1653_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1653_, 0, v___x_1651_);
lean_ctor_set(v___x_1653_, 1, v___x_1652_);
v___x_1654_ = l_Lean_MessageData_ofConstName(v_declName_1636_, v___x_1648_);
v___x_1655_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1655_, 0, v___x_1653_);
lean_ctor_set(v___x_1655_, 1, v___x_1654_);
v___x_1656_ = lean_obj_once(&l_Lean_ensureAttrDeclIsMeta___closed__1, &l_Lean_ensureAttrDeclIsMeta___closed__1_once, _init_l_Lean_ensureAttrDeclIsMeta___closed__1);
v___x_1657_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1657_, 0, v___x_1655_);
lean_ctor_set(v___x_1657_, 1, v___x_1656_);
v___x_1658_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_1657_, v_a_1638_, v_a_1639_);
return v___x_1658_;
}
else
{
lean_object* v___x_1659_; 
v___x_1659_ = l_Lean_ensureAttrDeclIsPublic(v_attrName_1635_, v_declName_1636_, v_attrKind_1637_, v_a_1638_, v_a_1639_);
return v___x_1659_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ensureAttrDeclIsMeta___boxed(lean_object* v_attrName_1660_, lean_object* v_declName_1661_, lean_object* v_attrKind_1662_, lean_object* v_a_1663_, lean_object* v_a_1664_, lean_object* v_a_1665_){
_start:
{
uint8_t v_attrKind_boxed_1666_; lean_object* v_res_1667_; 
v_attrKind_boxed_1666_ = lean_unbox(v_attrKind_1662_);
v_res_1667_ = l_Lean_ensureAttrDeclIsMeta(v_attrName_1660_, v_declName_1661_, v_attrKind_boxed_1666_, v_a_1663_, v_a_1664_);
lean_dec(v_a_1664_);
lean_dec_ref(v_a_1663_);
return v_res_1667_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__0(lean_object* v_x_1671_, lean_object* v___y_1672_){
_start:
{
lean_object* v___x_1674_; lean_object* v___x_1675_; 
v___x_1674_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___lam__0___closed__1));
v___x_1675_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1675_, 0, v___x_1674_);
return v___x_1675_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__0___boxed(lean_object* v_x_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_){
_start:
{
lean_object* v_res_1679_; 
v_res_1679_ = l_Lean_instInhabitedTagAttribute_default___lam__0(v_x_1676_, v___y_1677_);
lean_dec_ref(v___y_1677_);
lean_dec_ref(v_x_1676_);
return v_res_1679_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__1(lean_object* v_s_1680_, lean_object* v_x_1681_){
_start:
{
lean_inc(v_s_1680_);
return v_s_1680_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__1___boxed(lean_object* v_s_1682_, lean_object* v_x_1683_){
_start:
{
lean_object* v_res_1684_; 
v_res_1684_ = l_Lean_instInhabitedTagAttribute_default___lam__1(v_s_1682_, v_x_1683_);
lean_dec(v_x_1683_);
lean_dec(v_s_1682_);
return v_res_1684_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__2(lean_object* v_x_1689_, lean_object* v_x_1690_){
_start:
{
lean_object* v___x_1691_; 
v___x_1691_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___lam__2___closed__1));
return v___x_1691_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__2___boxed(lean_object* v_x_1692_, lean_object* v_x_1693_){
_start:
{
lean_object* v_res_1694_; 
v_res_1694_ = l_Lean_instInhabitedTagAttribute_default___lam__2(v_x_1692_, v_x_1693_);
lean_dec(v_x_1693_);
lean_dec_ref(v_x_1692_);
return v_res_1694_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__3(lean_object* v_x_1695_){
_start:
{
lean_object* v___x_1696_; 
v___x_1696_ = lean_box(0);
return v___x_1696_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__3___boxed(lean_object* v_x_1697_){
_start:
{
lean_object* v_res_1698_; 
v_res_1698_ = l_Lean_instInhabitedTagAttribute_default___lam__3(v_x_1697_);
lean_dec(v_x_1697_);
return v_res_1698_;
}
}
static lean_object* _init_l_Lean_instInhabitedTagAttribute_default___closed__4(void){
_start:
{
lean_object* v___x_1703_; 
v___x_1703_ = l_Lean_instInhabitedEnvExtension_default(lean_box(0));
return v___x_1703_;
}
}
static lean_object* _init_l_Lean_instInhabitedTagAttribute_default___closed__5(void){
_start:
{
lean_object* v___f_1704_; lean_object* v___f_1705_; lean_object* v___f_1706_; lean_object* v___f_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; 
v___f_1704_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___closed__3));
v___f_1705_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___closed__2));
v___f_1706_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___closed__1));
v___f_1707_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___closed__0));
v___x_1708_ = lean_box(0);
v___x_1709_ = lean_obj_once(&l_Lean_instInhabitedTagAttribute_default___closed__4, &l_Lean_instInhabitedTagAttribute_default___closed__4_once, _init_l_Lean_instInhabitedTagAttribute_default___closed__4);
v___x_1710_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1710_, 0, v___x_1709_);
lean_ctor_set(v___x_1710_, 1, v___x_1708_);
lean_ctor_set(v___x_1710_, 2, v___f_1707_);
lean_ctor_set(v___x_1710_, 3, v___f_1706_);
lean_ctor_set(v___x_1710_, 4, v___f_1705_);
lean_ctor_set(v___x_1710_, 5, v___f_1704_);
return v___x_1710_;
}
}
static lean_object* _init_l_Lean_instInhabitedTagAttribute_default___closed__6(void){
_start:
{
lean_object* v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; 
v___x_1711_ = lean_obj_once(&l_Lean_instInhabitedTagAttribute_default___closed__5, &l_Lean_instInhabitedTagAttribute_default___closed__5_once, _init_l_Lean_instInhabitedTagAttribute_default___closed__5);
v___x_1712_ = ((lean_object*)(l_Lean_instInhabitedAttributeImpl_default));
v___x_1713_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1713_, 0, v___x_1712_);
lean_ctor_set(v___x_1713_, 1, v___x_1711_);
return v___x_1713_;
}
}
static lean_object* _init_l_Lean_instInhabitedTagAttribute_default(void){
_start:
{
lean_object* v___x_1714_; 
v___x_1714_ = lean_obj_once(&l_Lean_instInhabitedTagAttribute_default___closed__6, &l_Lean_instInhabitedTagAttribute_default___closed__6_once, _init_l_Lean_instInhabitedTagAttribute_default___closed__6);
return v___x_1714_;
}
}
static lean_object* _init_l_Lean_instInhabitedTagAttribute(void){
_start:
{
lean_object* v___x_1715_; 
v___x_1715_ = l_Lean_instInhabitedTagAttribute_default;
return v___x_1715_;
}
}
static lean_object* _init_l_Lean_registerTagAttribute___auto__1(void){
_start:
{
lean_object* v___x_1716_; 
v___x_1716_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__28, &l_Lean_AttributeImplCore_ref___autoParam___closed__28_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__28);
return v___x_1716_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__0(lean_object* v_x_1717_){
_start:
{
lean_object* v___x_1718_; 
v___x_1718_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___lam__2___closed__0));
return v___x_1718_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__0___boxed(lean_object* v_x_1719_){
_start:
{
lean_object* v_res_1720_; 
v_res_1720_ = l_Lean_registerTagAttribute___lam__0(v_x_1719_);
lean_dec(v_x_1719_);
return v_res_1720_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerTagAttribute_spec__0(lean_object* v_newState_1721_, lean_object* v_x_1722_, lean_object* v_x_1723_){
_start:
{
if (lean_obj_tag(v_x_1723_) == 0)
{
return v_x_1722_;
}
else
{
lean_object* v_head_1724_; lean_object* v_tail_1725_; uint8_t v___x_1726_; 
v_head_1724_ = lean_ctor_get(v_x_1723_, 0);
lean_inc(v_head_1724_);
v_tail_1725_ = lean_ctor_get(v_x_1723_, 1);
lean_inc(v_tail_1725_);
lean_dec_ref(v_x_1723_);
v___x_1726_ = l_Lean_NameSet_contains(v_newState_1721_, v_head_1724_);
if (v___x_1726_ == 0)
{
lean_dec(v_head_1724_);
v_x_1723_ = v_tail_1725_;
goto _start;
}
else
{
lean_object* v___x_1728_; 
v___x_1728_ = l_Lean_NameSet_insert(v_x_1722_, v_head_1724_);
v_x_1722_ = v___x_1728_;
v_x_1723_ = v_tail_1725_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerTagAttribute_spec__0___boxed(lean_object* v_newState_1730_, lean_object* v_x_1731_, lean_object* v_x_1732_){
_start:
{
lean_object* v_res_1733_; 
v_res_1733_ = l_List_foldl___at___00Lean_registerTagAttribute_spec__0(v_newState_1730_, v_x_1731_, v_x_1732_);
lean_dec(v_newState_1730_);
return v_res_1733_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__1(lean_object* v_x_1734_, lean_object* v_newState_1735_, lean_object* v_newConsts_1736_, lean_object* v_s_1737_){
_start:
{
lean_object* v___x_1738_; 
v___x_1738_ = l_List_foldl___at___00Lean_registerTagAttribute_spec__0(v_newState_1735_, v_s_1737_, v_newConsts_1736_);
return v___x_1738_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__1___boxed(lean_object* v_x_1739_, lean_object* v_newState_1740_, lean_object* v_newConsts_1741_, lean_object* v_s_1742_){
_start:
{
lean_object* v_res_1743_; 
v_res_1743_ = l_Lean_registerTagAttribute___lam__1(v_x_1739_, v_newState_1740_, v_newConsts_1741_, v_s_1742_);
lean_dec(v_newState_1740_);
lean_dec(v_x_1739_);
return v_res_1743_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__2(lean_object* v_s_1756_){
_start:
{
lean_object* v___x_1757_; lean_object* v___y_1759_; 
v___x_1757_ = ((lean_object*)(l_Lean_registerTagAttribute___lam__2___closed__5));
if (lean_obj_tag(v_s_1756_) == 0)
{
lean_object* v_size_1763_; 
v_size_1763_ = lean_ctor_get(v_s_1756_, 0);
lean_inc(v_size_1763_);
lean_dec_ref(v_s_1756_);
v___y_1759_ = v_size_1763_;
goto v___jp_1758_;
}
else
{
lean_object* v___x_1764_; 
v___x_1764_ = lean_unsigned_to_nat(0u);
v___y_1759_ = v___x_1764_;
goto v___jp_1758_;
}
v___jp_1758_:
{
lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; 
v___x_1760_ = l_Nat_reprFast(v___y_1759_);
v___x_1761_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1761_, 0, v___x_1760_);
v___x_1762_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1762_, 0, v___x_1757_);
lean_ctor_set(v___x_1762_, 1, v___x_1761_);
return v___x_1762_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4___redArg(lean_object* v_hi_1765_, lean_object* v_pivot_1766_, lean_object* v_as_1767_, lean_object* v_i_1768_, lean_object* v_k_1769_){
_start:
{
uint8_t v___x_1770_; 
v___x_1770_ = lean_nat_dec_lt(v_k_1769_, v_hi_1765_);
if (v___x_1770_ == 0)
{
lean_object* v___x_1771_; lean_object* v___x_1772_; 
lean_dec(v_k_1769_);
v___x_1771_ = lean_array_fswap(v_as_1767_, v_i_1768_, v_hi_1765_);
v___x_1772_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1772_, 0, v_i_1768_);
lean_ctor_set(v___x_1772_, 1, v___x_1771_);
return v___x_1772_;
}
else
{
lean_object* v___x_1773_; uint8_t v___x_1774_; 
v___x_1773_ = lean_array_fget_borrowed(v_as_1767_, v_k_1769_);
v___x_1774_ = l_Lean_Name_quickLt(v___x_1773_, v_pivot_1766_);
if (v___x_1774_ == 0)
{
lean_object* v___x_1775_; lean_object* v___x_1776_; 
v___x_1775_ = lean_unsigned_to_nat(1u);
v___x_1776_ = lean_nat_add(v_k_1769_, v___x_1775_);
lean_dec(v_k_1769_);
v_k_1769_ = v___x_1776_;
goto _start;
}
else
{
lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; 
v___x_1778_ = lean_array_fswap(v_as_1767_, v_i_1768_, v_k_1769_);
v___x_1779_ = lean_unsigned_to_nat(1u);
v___x_1780_ = lean_nat_add(v_i_1768_, v___x_1779_);
lean_dec(v_i_1768_);
v___x_1781_ = lean_nat_add(v_k_1769_, v___x_1779_);
lean_dec(v_k_1769_);
v_as_1767_ = v___x_1778_;
v_i_1768_ = v___x_1780_;
v_k_1769_ = v___x_1781_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4___redArg___boxed(lean_object* v_hi_1783_, lean_object* v_pivot_1784_, lean_object* v_as_1785_, lean_object* v_i_1786_, lean_object* v_k_1787_){
_start:
{
lean_object* v_res_1788_; 
v_res_1788_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4___redArg(v_hi_1783_, v_pivot_1784_, v_as_1785_, v_i_1786_, v_k_1787_);
lean_dec(v_pivot_1784_);
lean_dec(v_hi_1783_);
return v_res_1788_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___redArg(lean_object* v_n_1789_, lean_object* v_as_1790_, lean_object* v_lo_1791_, lean_object* v_hi_1792_){
_start:
{
lean_object* v___y_1794_; uint8_t v___x_1804_; 
v___x_1804_ = lean_nat_dec_lt(v_lo_1791_, v_hi_1792_);
if (v___x_1804_ == 0)
{
lean_dec(v_lo_1791_);
return v_as_1790_;
}
else
{
lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v_mid_1807_; lean_object* v___y_1809_; lean_object* v___y_1815_; lean_object* v___x_1820_; lean_object* v___x_1821_; uint8_t v___x_1822_; 
v___x_1805_ = lean_nat_add(v_lo_1791_, v_hi_1792_);
v___x_1806_ = lean_unsigned_to_nat(1u);
v_mid_1807_ = lean_nat_shiftr(v___x_1805_, v___x_1806_);
lean_dec(v___x_1805_);
v___x_1820_ = lean_array_fget_borrowed(v_as_1790_, v_mid_1807_);
v___x_1821_ = lean_array_fget_borrowed(v_as_1790_, v_lo_1791_);
v___x_1822_ = l_Lean_Name_quickLt(v___x_1820_, v___x_1821_);
if (v___x_1822_ == 0)
{
v___y_1815_ = v_as_1790_;
goto v___jp_1814_;
}
else
{
lean_object* v___x_1823_; 
v___x_1823_ = lean_array_fswap(v_as_1790_, v_lo_1791_, v_mid_1807_);
v___y_1815_ = v___x_1823_;
goto v___jp_1814_;
}
v___jp_1808_:
{
lean_object* v___x_1810_; lean_object* v___x_1811_; uint8_t v___x_1812_; 
v___x_1810_ = lean_array_fget_borrowed(v___y_1809_, v_mid_1807_);
v___x_1811_ = lean_array_fget_borrowed(v___y_1809_, v_hi_1792_);
v___x_1812_ = l_Lean_Name_quickLt(v___x_1810_, v___x_1811_);
if (v___x_1812_ == 0)
{
lean_dec(v_mid_1807_);
v___y_1794_ = v___y_1809_;
goto v___jp_1793_;
}
else
{
lean_object* v___x_1813_; 
v___x_1813_ = lean_array_fswap(v___y_1809_, v_mid_1807_, v_hi_1792_);
lean_dec(v_mid_1807_);
v___y_1794_ = v___x_1813_;
goto v___jp_1793_;
}
}
v___jp_1814_:
{
lean_object* v___x_1816_; lean_object* v___x_1817_; uint8_t v___x_1818_; 
v___x_1816_ = lean_array_fget_borrowed(v___y_1815_, v_hi_1792_);
v___x_1817_ = lean_array_fget_borrowed(v___y_1815_, v_lo_1791_);
v___x_1818_ = l_Lean_Name_quickLt(v___x_1816_, v___x_1817_);
if (v___x_1818_ == 0)
{
v___y_1809_ = v___y_1815_;
goto v___jp_1808_;
}
else
{
lean_object* v___x_1819_; 
v___x_1819_ = lean_array_fswap(v___y_1815_, v_lo_1791_, v_hi_1792_);
v___y_1809_ = v___x_1819_;
goto v___jp_1808_;
}
}
}
v___jp_1793_:
{
lean_object* v_pivot_1795_; lean_object* v___x_1796_; lean_object* v_fst_1797_; lean_object* v_snd_1798_; uint8_t v___x_1799_; 
v_pivot_1795_ = lean_array_fget(v___y_1794_, v_hi_1792_);
lean_inc_n(v_lo_1791_, 2);
v___x_1796_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4___redArg(v_hi_1792_, v_pivot_1795_, v___y_1794_, v_lo_1791_, v_lo_1791_);
lean_dec(v_pivot_1795_);
v_fst_1797_ = lean_ctor_get(v___x_1796_, 0);
lean_inc(v_fst_1797_);
v_snd_1798_ = lean_ctor_get(v___x_1796_, 1);
lean_inc(v_snd_1798_);
lean_dec_ref(v___x_1796_);
v___x_1799_ = lean_nat_dec_le(v_hi_1792_, v_fst_1797_);
if (v___x_1799_ == 0)
{
lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; 
v___x_1800_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___redArg(v_n_1789_, v_snd_1798_, v_lo_1791_, v_fst_1797_);
v___x_1801_ = lean_unsigned_to_nat(1u);
v___x_1802_ = lean_nat_add(v_fst_1797_, v___x_1801_);
lean_dec(v_fst_1797_);
v_as_1790_ = v___x_1800_;
v_lo_1791_ = v___x_1802_;
goto _start;
}
else
{
lean_dec(v_fst_1797_);
lean_dec(v_lo_1791_);
return v_snd_1798_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___redArg___boxed(lean_object* v_n_1824_, lean_object* v_as_1825_, lean_object* v_lo_1826_, lean_object* v_hi_1827_){
_start:
{
lean_object* v_res_1828_; 
v_res_1828_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___redArg(v_n_1824_, v_as_1825_, v_lo_1826_, v_hi_1827_);
lean_dec(v_hi_1827_);
lean_dec(v_n_1824_);
return v_res_1828_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerTagAttribute_spec__2(lean_object* v_env_1829_, lean_object* v_as_1830_, size_t v_i_1831_, size_t v_stop_1832_, lean_object* v_b_1833_){
_start:
{
lean_object* v___y_1835_; uint8_t v___x_1839_; 
v___x_1839_ = lean_usize_dec_eq(v_i_1831_, v_stop_1832_);
if (v___x_1839_ == 0)
{
lean_object* v___x_1840_; uint8_t v___x_1841_; lean_object* v___x_1842_; uint8_t v___x_1843_; 
v___x_1840_ = lean_array_uget_borrowed(v_as_1830_, v_i_1831_);
v___x_1841_ = 1;
lean_inc_ref(v_env_1829_);
v___x_1842_ = l_Lean_Environment_setExporting(v_env_1829_, v___x_1841_);
lean_inc(v___x_1840_);
v___x_1843_ = l_Lean_Environment_contains(v___x_1842_, v___x_1840_, v___x_1839_);
if (v___x_1843_ == 0)
{
v___y_1835_ = v_b_1833_;
goto v___jp_1834_;
}
else
{
lean_object* v___x_1844_; 
lean_inc(v___x_1840_);
v___x_1844_ = lean_array_push(v_b_1833_, v___x_1840_);
v___y_1835_ = v___x_1844_;
goto v___jp_1834_;
}
}
else
{
lean_dec_ref(v_env_1829_);
return v_b_1833_;
}
v___jp_1834_:
{
size_t v___x_1836_; size_t v___x_1837_; 
v___x_1836_ = ((size_t)1ULL);
v___x_1837_ = lean_usize_add(v_i_1831_, v___x_1836_);
v_i_1831_ = v___x_1837_;
v_b_1833_ = v___y_1835_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerTagAttribute_spec__2___boxed(lean_object* v_env_1845_, lean_object* v_as_1846_, lean_object* v_i_1847_, lean_object* v_stop_1848_, lean_object* v_b_1849_){
_start:
{
size_t v_i_boxed_1850_; size_t v_stop_boxed_1851_; lean_object* v_res_1852_; 
v_i_boxed_1850_ = lean_unbox_usize(v_i_1847_);
lean_dec(v_i_1847_);
v_stop_boxed_1851_ = lean_unbox_usize(v_stop_1848_);
lean_dec(v_stop_1848_);
v_res_1852_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerTagAttribute_spec__2(v_env_1845_, v_as_1846_, v_i_boxed_1850_, v_stop_boxed_1851_, v_b_1849_);
lean_dec_ref(v_as_1846_);
return v_res_1852_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerTagAttribute_spec__1_spec__1(lean_object* v_init_1853_, lean_object* v_x_1854_){
_start:
{
if (lean_obj_tag(v_x_1854_) == 0)
{
lean_object* v_k_1855_; lean_object* v_l_1856_; lean_object* v_r_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; 
v_k_1855_ = lean_ctor_get(v_x_1854_, 1);
lean_inc(v_k_1855_);
v_l_1856_ = lean_ctor_get(v_x_1854_, 3);
lean_inc(v_l_1856_);
v_r_1857_ = lean_ctor_get(v_x_1854_, 4);
lean_inc(v_r_1857_);
lean_dec_ref(v_x_1854_);
v___x_1858_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerTagAttribute_spec__1_spec__1(v_init_1853_, v_l_1856_);
v___x_1859_ = lean_array_push(v___x_1858_, v_k_1855_);
v_init_1853_ = v___x_1859_;
v_x_1854_ = v_r_1857_;
goto _start;
}
else
{
return v_init_1853_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__3(lean_object* v_env_1861_, lean_object* v_es_1862_){
_start:
{
lean_object* v___x_1863_; lean_object* v___x_1864_; lean_object* v___y_1866_; lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___y_1883_; lean_object* v___y_1884_; uint8_t v___x_1886_; 
v___x_1863_ = lean_unsigned_to_nat(0u);
v___x_1864_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___lam__2___closed__0));
v___x_1880_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerTagAttribute_spec__1_spec__1(v___x_1864_, v_es_1862_);
v___x_1881_ = lean_array_get_size(v___x_1880_);
v___x_1886_ = lean_nat_dec_eq(v___x_1881_, v___x_1863_);
if (v___x_1886_ == 0)
{
lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v___y_1890_; uint8_t v___x_1892_; 
v___x_1887_ = lean_unsigned_to_nat(1u);
v___x_1888_ = lean_nat_sub(v___x_1881_, v___x_1887_);
v___x_1892_ = lean_nat_dec_le(v___x_1863_, v___x_1888_);
if (v___x_1892_ == 0)
{
lean_inc(v___x_1888_);
v___y_1890_ = v___x_1888_;
goto v___jp_1889_;
}
else
{
v___y_1890_ = v___x_1863_;
goto v___jp_1889_;
}
v___jp_1889_:
{
uint8_t v___x_1891_; 
v___x_1891_ = lean_nat_dec_le(v___y_1890_, v___x_1888_);
if (v___x_1891_ == 0)
{
lean_dec(v___x_1888_);
lean_inc(v___y_1890_);
v___y_1883_ = v___y_1890_;
v___y_1884_ = v___y_1890_;
goto v___jp_1882_;
}
else
{
v___y_1883_ = v___y_1890_;
v___y_1884_ = v___x_1888_;
goto v___jp_1882_;
}
}
}
else
{
v___y_1866_ = v___x_1880_;
goto v___jp_1865_;
}
v___jp_1865_:
{
lean_object* v___x_1867_; uint8_t v___x_1868_; 
v___x_1867_ = lean_array_get_size(v___y_1866_);
v___x_1868_ = lean_nat_dec_lt(v___x_1863_, v___x_1867_);
if (v___x_1868_ == 0)
{
lean_object* v___x_1869_; 
lean_dec_ref(v_env_1861_);
v___x_1869_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1869_, 0, v___x_1864_);
lean_ctor_set(v___x_1869_, 1, v___x_1864_);
lean_ctor_set(v___x_1869_, 2, v___y_1866_);
return v___x_1869_;
}
else
{
uint8_t v___x_1870_; 
v___x_1870_ = lean_nat_dec_le(v___x_1867_, v___x_1867_);
if (v___x_1870_ == 0)
{
if (v___x_1868_ == 0)
{
lean_object* v___x_1871_; 
lean_dec_ref(v_env_1861_);
v___x_1871_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1871_, 0, v___x_1864_);
lean_ctor_set(v___x_1871_, 1, v___x_1864_);
lean_ctor_set(v___x_1871_, 2, v___y_1866_);
return v___x_1871_;
}
else
{
size_t v___x_1872_; size_t v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; 
v___x_1872_ = ((size_t)0ULL);
v___x_1873_ = lean_usize_of_nat(v___x_1867_);
v___x_1874_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerTagAttribute_spec__2(v_env_1861_, v___y_1866_, v___x_1872_, v___x_1873_, v___x_1864_);
lean_inc_ref(v___x_1874_);
v___x_1875_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1875_, 0, v___x_1874_);
lean_ctor_set(v___x_1875_, 1, v___x_1874_);
lean_ctor_set(v___x_1875_, 2, v___y_1866_);
return v___x_1875_;
}
}
else
{
size_t v___x_1876_; size_t v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; 
v___x_1876_ = ((size_t)0ULL);
v___x_1877_ = lean_usize_of_nat(v___x_1867_);
v___x_1878_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerTagAttribute_spec__2(v_env_1861_, v___y_1866_, v___x_1876_, v___x_1877_, v___x_1864_);
lean_inc_ref(v___x_1878_);
v___x_1879_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1879_, 0, v___x_1878_);
lean_ctor_set(v___x_1879_, 1, v___x_1878_);
lean_ctor_set(v___x_1879_, 2, v___y_1866_);
return v___x_1879_;
}
}
}
v___jp_1882_:
{
lean_object* v___x_1885_; 
v___x_1885_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___redArg(v___x_1881_, v___x_1880_, v___y_1883_, v___y_1884_);
lean_dec(v___y_1884_);
v___y_1866_ = v___x_1885_;
goto v___jp_1865_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__4(lean_object* v___x_1893_, lean_object* v_x_1894_, lean_object* v_x_1895_){
_start:
{
lean_object* v___x_1897_; 
v___x_1897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1897_, 0, v___x_1893_);
return v___x_1897_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__4___boxed(lean_object* v___x_1898_, lean_object* v_x_1899_, lean_object* v_x_1900_, lean_object* v___y_1901_){
_start:
{
lean_object* v_res_1902_; 
v_res_1902_ = l_Lean_registerTagAttribute___lam__4(v___x_1898_, v_x_1899_, v_x_1900_);
lean_dec_ref(v_x_1900_);
lean_dec_ref(v_x_1899_);
return v_res_1902_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__5(lean_object* v___x_1903_){
_start:
{
lean_object* v___x_1905_; 
v___x_1905_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1905_, 0, v___x_1903_);
return v___x_1905_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__5___boxed(lean_object* v___x_1906_, lean_object* v___y_1907_){
_start:
{
lean_object* v_res_1908_; 
v_res_1908_ = l_Lean_registerTagAttribute___lam__5(v___x_1906_);
return v_res_1908_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__6(lean_object* v_name_1909_, lean_object* v_decl_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_){
_start:
{
lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; 
v___x_1914_ = lean_obj_once(&l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1, &l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1_once, _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1);
v___x_1915_ = l_Lean_MessageData_ofName(v_name_1909_);
v___x_1916_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1916_, 0, v___x_1914_);
lean_ctor_set(v___x_1916_, 1, v___x_1915_);
v___x_1917_ = lean_obj_once(&l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3, &l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3_once, _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3);
v___x_1918_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1918_, 0, v___x_1916_);
lean_ctor_set(v___x_1918_, 1, v___x_1917_);
v___x_1919_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_1918_, v___y_1911_, v___y_1912_);
return v___x_1919_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__6___boxed(lean_object* v_name_1920_, lean_object* v_decl_1921_, lean_object* v___y_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_){
_start:
{
lean_object* v_res_1925_; 
v_res_1925_ = l_Lean_registerTagAttribute___lam__6(v_name_1920_, v_decl_1921_, v___y_1922_, v___y_1923_);
lean_dec(v___y_1923_);
lean_dec_ref(v___y_1922_);
lean_dec(v_decl_1921_);
return v_res_1925_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg(lean_object* v_attrName_1926_, lean_object* v_declName_1927_, lean_object* v___y_1928_, lean_object* v___y_1929_){
_start:
{
lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; uint8_t v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; 
v___x_1931_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1);
v___x_1932_ = l_Lean_MessageData_ofName(v_attrName_1926_);
v___x_1933_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1933_, 0, v___x_1931_);
lean_ctor_set(v___x_1933_, 1, v___x_1932_);
v___x_1934_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__3, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__3_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__3);
v___x_1935_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1935_, 0, v___x_1933_);
lean_ctor_set(v___x_1935_, 1, v___x_1934_);
v___x_1936_ = 0;
v___x_1937_ = l_Lean_MessageData_ofConstName(v_declName_1927_, v___x_1936_);
v___x_1938_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1938_, 0, v___x_1935_);
lean_ctor_set(v___x_1938_, 1, v___x_1937_);
v___x_1939_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__5, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__5_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__5);
v___x_1940_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1940_, 0, v___x_1938_);
lean_ctor_set(v___x_1940_, 1, v___x_1939_);
v___x_1941_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_1940_, v___y_1928_, v___y_1929_);
return v___x_1941_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg___boxed(lean_object* v_attrName_1942_, lean_object* v_declName_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_){
_start:
{
lean_object* v_res_1947_; 
v_res_1947_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg(v_attrName_1942_, v_declName_1943_, v___y_1944_, v___y_1945_);
lean_dec(v___y_1945_);
lean_dec_ref(v___y_1944_);
return v_res_1947_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___redArg(lean_object* v_attrName_1948_, lean_object* v_declName_1949_, lean_object* v_asyncPrefix_x3f_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_){
_start:
{
lean_object* v___y_1955_; 
if (lean_obj_tag(v_asyncPrefix_x3f_1950_) == 0)
{
lean_object* v___x_1968_; 
v___x_1968_ = l_Lean_MessageData_nil;
v___y_1955_ = v___x_1968_;
goto v___jp_1954_;
}
else
{
lean_object* v_val_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; 
v_val_1969_ = lean_ctor_get(v_asyncPrefix_x3f_1950_, 0);
lean_inc(v_val_1969_);
lean_dec_ref(v_asyncPrefix_x3f_1950_);
v___x_1970_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___redArg___closed__3, &l_Lean_throwAttrNotInAsyncCtx___redArg___closed__3_once, _init_l_Lean_throwAttrNotInAsyncCtx___redArg___closed__3);
v___x_1971_ = l_Lean_MessageData_ofName(v_val_1969_);
v___x_1972_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1972_, 0, v___x_1970_);
lean_ctor_set(v___x_1972_, 1, v___x_1971_);
v___x_1973_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__5, &l_Lean_throwAttrMustBeGlobal___redArg___closed__5_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__5);
v___x_1974_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1974_, 0, v___x_1972_);
lean_ctor_set(v___x_1974_, 1, v___x_1973_);
v___y_1955_ = v___x_1974_;
goto v___jp_1954_;
}
v___jp_1954_:
{
lean_object* v___x_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; lean_object* v___x_1960_; uint8_t v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; 
v___x_1956_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1);
v___x_1957_ = l_Lean_MessageData_ofName(v_attrName_1948_);
v___x_1958_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1958_, 0, v___x_1956_);
lean_ctor_set(v___x_1958_, 1, v___x_1957_);
v___x_1959_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__3, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__3_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__3);
v___x_1960_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1960_, 0, v___x_1958_);
lean_ctor_set(v___x_1960_, 1, v___x_1959_);
v___x_1961_ = 0;
v___x_1962_ = l_Lean_MessageData_ofConstName(v_declName_1949_, v___x_1961_);
v___x_1963_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1963_, 0, v___x_1960_);
lean_ctor_set(v___x_1963_, 1, v___x_1962_);
v___x_1964_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___redArg___closed__1, &l_Lean_throwAttrNotInAsyncCtx___redArg___closed__1_once, _init_l_Lean_throwAttrNotInAsyncCtx___redArg___closed__1);
v___x_1965_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1965_, 0, v___x_1963_);
lean_ctor_set(v___x_1965_, 1, v___x_1964_);
v___x_1966_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1966_, 0, v___x_1965_);
lean_ctor_set(v___x_1966_, 1, v___y_1955_);
v___x_1967_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_1966_, v___y_1951_, v___y_1952_);
return v___x_1967_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___redArg___boxed(lean_object* v_attrName_1975_, lean_object* v_declName_1976_, lean_object* v_asyncPrefix_x3f_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_){
_start:
{
lean_object* v_res_1981_; 
v_res_1981_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___redArg(v_attrName_1975_, v_declName_1976_, v_asyncPrefix_x3f_1977_, v___y_1978_, v___y_1979_);
lean_dec(v___y_1979_);
lean_dec_ref(v___y_1978_);
return v_res_1981_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg(lean_object* v_name_1982_, uint8_t v_kind_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_){
_start:
{
lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v___y_1993_; 
v___x_1987_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__1, &l_Lean_throwAttrMustBeGlobal___redArg___closed__1_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__1);
v___x_1988_ = l_Lean_MessageData_ofName(v_name_1982_);
v___x_1989_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1989_, 0, v___x_1987_);
lean_ctor_set(v___x_1989_, 1, v___x_1988_);
v___x_1990_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__3, &l_Lean_throwAttrMustBeGlobal___redArg___closed__3_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__3);
v___x_1991_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1991_, 0, v___x_1989_);
lean_ctor_set(v___x_1991_, 1, v___x_1990_);
switch(v_kind_1983_)
{
case 0:
{
lean_object* v___x_2000_; 
v___x_2000_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__0));
v___y_1993_ = v___x_2000_;
goto v___jp_1992_;
}
case 1:
{
lean_object* v___x_2001_; 
v___x_2001_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__1));
v___y_1993_ = v___x_2001_;
goto v___jp_1992_;
}
default: 
{
lean_object* v___x_2002_; 
v___x_2002_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__2));
v___y_1993_ = v___x_2002_;
goto v___jp_1992_;
}
}
v___jp_1992_:
{
lean_object* v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; 
lean_inc_ref(v___y_1993_);
v___x_1994_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1994_, 0, v___y_1993_);
v___x_1995_ = l_Lean_MessageData_ofFormat(v___x_1994_);
v___x_1996_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1996_, 0, v___x_1991_);
lean_ctor_set(v___x_1996_, 1, v___x_1995_);
v___x_1997_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__5, &l_Lean_throwAttrMustBeGlobal___redArg___closed__5_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__5);
v___x_1998_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1998_, 0, v___x_1996_);
lean_ctor_set(v___x_1998_, 1, v___x_1997_);
v___x_1999_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_1998_, v___y_1984_, v___y_1985_);
return v___x_1999_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg___boxed(lean_object* v_name_2003_, lean_object* v_kind_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_){
_start:
{
uint8_t v_kind_boxed_2008_; lean_object* v_res_2009_; 
v_kind_boxed_2008_ = lean_unbox(v_kind_2004_);
v_res_2009_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg(v_name_2003_, v_kind_boxed_2008_, v___y_2005_, v___y_2006_);
lean_dec(v___y_2006_);
lean_dec_ref(v___y_2005_);
return v_res_2009_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__7(lean_object* v_validate_2010_, lean_object* v_a_2011_, lean_object* v_name_2012_, lean_object* v_decl_2013_, lean_object* v_stx_2014_, uint8_t v_kind_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_){
_start:
{
lean_object* v___y_2020_; lean_object* v___y_2021_; lean_object* v___y_2056_; lean_object* v___y_2057_; lean_object* v___y_2058_; lean_object* v___y_2065_; lean_object* v___y_2066_; lean_object* v___x_2071_; 
v___x_2071_ = l_Lean_Attribute_Builtin_ensureNoArgs(v_stx_2014_, v___y_2016_, v___y_2017_);
if (lean_obj_tag(v___x_2071_) == 0)
{
uint8_t v___x_2072_; uint8_t v___x_2073_; 
lean_dec_ref(v___x_2071_);
v___x_2072_ = 0;
v___x_2073_ = l_Lean_instBEqAttributeKind_beq(v_kind_2015_, v___x_2072_);
if (v___x_2073_ == 0)
{
lean_object* v___x_2074_; 
lean_dec(v_decl_2013_);
lean_dec_ref(v_a_2011_);
lean_dec_ref(v_validate_2010_);
v___x_2074_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg(v_name_2012_, v_kind_2015_, v___y_2016_, v___y_2017_);
return v___x_2074_;
}
else
{
v___y_2065_ = v___y_2016_;
v___y_2066_ = v___y_2017_;
goto v___jp_2064_;
}
}
else
{
lean_dec(v_decl_2013_);
lean_dec(v_name_2012_);
lean_dec_ref(v_a_2011_);
lean_dec_ref(v_validate_2010_);
return v___x_2071_;
}
v___jp_2019_:
{
lean_object* v___x_2022_; 
lean_inc(v___y_2021_);
lean_inc_ref(v___y_2020_);
lean_inc(v_decl_2013_);
v___x_2022_ = lean_apply_4(v_validate_2010_, v_decl_2013_, v___y_2020_, v___y_2021_, lean_box(0));
if (lean_obj_tag(v___x_2022_) == 0)
{
lean_object* v___x_2024_; uint8_t v_isShared_2025_; uint8_t v_isSharedCheck_2053_; 
v_isSharedCheck_2053_ = !lean_is_exclusive(v___x_2022_);
if (v_isSharedCheck_2053_ == 0)
{
lean_object* v_unused_2054_; 
v_unused_2054_ = lean_ctor_get(v___x_2022_, 0);
lean_dec(v_unused_2054_);
v___x_2024_ = v___x_2022_;
v_isShared_2025_ = v_isSharedCheck_2053_;
goto v_resetjp_2023_;
}
else
{
lean_dec(v___x_2022_);
v___x_2024_ = lean_box(0);
v_isShared_2025_ = v_isSharedCheck_2053_;
goto v_resetjp_2023_;
}
v_resetjp_2023_:
{
lean_object* v___x_2026_; lean_object* v_toEnvExtension_2027_; lean_object* v_env_2028_; lean_object* v_nextMacroScope_2029_; lean_object* v_ngen_2030_; lean_object* v_auxDeclNGen_2031_; lean_object* v_traceState_2032_; lean_object* v_messages_2033_; lean_object* v_infoState_2034_; lean_object* v_snapshotTasks_2035_; lean_object* v_newDecls_2036_; lean_object* v___x_2038_; uint8_t v_isShared_2039_; uint8_t v_isSharedCheck_2051_; 
v___x_2026_ = lean_st_ref_take(v___y_2021_);
v_toEnvExtension_2027_ = lean_ctor_get(v_a_2011_, 0);
v_env_2028_ = lean_ctor_get(v___x_2026_, 0);
v_nextMacroScope_2029_ = lean_ctor_get(v___x_2026_, 1);
v_ngen_2030_ = lean_ctor_get(v___x_2026_, 2);
v_auxDeclNGen_2031_ = lean_ctor_get(v___x_2026_, 3);
v_traceState_2032_ = lean_ctor_get(v___x_2026_, 4);
v_messages_2033_ = lean_ctor_get(v___x_2026_, 6);
v_infoState_2034_ = lean_ctor_get(v___x_2026_, 7);
v_snapshotTasks_2035_ = lean_ctor_get(v___x_2026_, 8);
v_newDecls_2036_ = lean_ctor_get(v___x_2026_, 9);
v_isSharedCheck_2051_ = !lean_is_exclusive(v___x_2026_);
if (v_isSharedCheck_2051_ == 0)
{
lean_object* v_unused_2052_; 
v_unused_2052_ = lean_ctor_get(v___x_2026_, 5);
lean_dec(v_unused_2052_);
v___x_2038_ = v___x_2026_;
v_isShared_2039_ = v_isSharedCheck_2051_;
goto v_resetjp_2037_;
}
else
{
lean_inc(v_newDecls_2036_);
lean_inc(v_snapshotTasks_2035_);
lean_inc(v_infoState_2034_);
lean_inc(v_messages_2033_);
lean_inc(v_traceState_2032_);
lean_inc(v_auxDeclNGen_2031_);
lean_inc(v_ngen_2030_);
lean_inc(v_nextMacroScope_2029_);
lean_inc(v_env_2028_);
lean_dec(v___x_2026_);
v___x_2038_ = lean_box(0);
v_isShared_2039_ = v_isSharedCheck_2051_;
goto v_resetjp_2037_;
}
v_resetjp_2037_:
{
lean_object* v_asyncMode_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2044_; 
v_asyncMode_2040_ = lean_ctor_get(v_toEnvExtension_2027_, 2);
lean_inc(v_asyncMode_2040_);
lean_inc(v_decl_2013_);
v___x_2041_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_a_2011_, v_env_2028_, v_decl_2013_, v_asyncMode_2040_, v_decl_2013_);
lean_dec(v_asyncMode_2040_);
v___x_2042_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2);
if (v_isShared_2039_ == 0)
{
lean_ctor_set(v___x_2038_, 5, v___x_2042_);
lean_ctor_set(v___x_2038_, 0, v___x_2041_);
v___x_2044_ = v___x_2038_;
goto v_reusejp_2043_;
}
else
{
lean_object* v_reuseFailAlloc_2050_; 
v_reuseFailAlloc_2050_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2050_, 0, v___x_2041_);
lean_ctor_set(v_reuseFailAlloc_2050_, 1, v_nextMacroScope_2029_);
lean_ctor_set(v_reuseFailAlloc_2050_, 2, v_ngen_2030_);
lean_ctor_set(v_reuseFailAlloc_2050_, 3, v_auxDeclNGen_2031_);
lean_ctor_set(v_reuseFailAlloc_2050_, 4, v_traceState_2032_);
lean_ctor_set(v_reuseFailAlloc_2050_, 5, v___x_2042_);
lean_ctor_set(v_reuseFailAlloc_2050_, 6, v_messages_2033_);
lean_ctor_set(v_reuseFailAlloc_2050_, 7, v_infoState_2034_);
lean_ctor_set(v_reuseFailAlloc_2050_, 8, v_snapshotTasks_2035_);
lean_ctor_set(v_reuseFailAlloc_2050_, 9, v_newDecls_2036_);
v___x_2044_ = v_reuseFailAlloc_2050_;
goto v_reusejp_2043_;
}
v_reusejp_2043_:
{
lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2048_; 
v___x_2045_ = lean_st_ref_set(v___y_2021_, v___x_2044_);
v___x_2046_ = lean_box(0);
if (v_isShared_2025_ == 0)
{
lean_ctor_set(v___x_2024_, 0, v___x_2046_);
v___x_2048_ = v___x_2024_;
goto v_reusejp_2047_;
}
else
{
lean_object* v_reuseFailAlloc_2049_; 
v_reuseFailAlloc_2049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2049_, 0, v___x_2046_);
v___x_2048_ = v_reuseFailAlloc_2049_;
goto v_reusejp_2047_;
}
v_reusejp_2047_:
{
return v___x_2048_;
}
}
}
}
}
else
{
lean_dec(v_decl_2013_);
lean_dec_ref(v_a_2011_);
return v___x_2022_;
}
}
v___jp_2055_:
{
lean_object* v_toEnvExtension_2059_; lean_object* v_asyncMode_2060_; uint8_t v___x_2061_; 
v_toEnvExtension_2059_ = lean_ctor_get(v_a_2011_, 0);
v_asyncMode_2060_ = lean_ctor_get(v_toEnvExtension_2059_, 2);
lean_inc(v_decl_2013_);
lean_inc_ref(v___y_2056_);
v___x_2061_ = l_Lean_EnvExtension_asyncMayModify___redArg(v___y_2056_, v_decl_2013_, v_asyncMode_2060_);
if (v___x_2061_ == 0)
{
lean_object* v___x_2062_; lean_object* v___x_2063_; 
lean_dec_ref(v_a_2011_);
lean_dec_ref(v_validate_2010_);
v___x_2062_ = l_Lean_Environment_asyncPrefix_x3f(v___y_2056_);
v___x_2063_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___redArg(v_name_2012_, v_decl_2013_, v___x_2062_, v___y_2057_, v___y_2058_);
return v___x_2063_;
}
else
{
lean_dec_ref(v___y_2056_);
lean_dec(v_name_2012_);
v___y_2020_ = v___y_2057_;
v___y_2021_ = v___y_2058_;
goto v___jp_2019_;
}
}
v___jp_2064_:
{
lean_object* v___x_2067_; lean_object* v_env_2068_; lean_object* v___x_2069_; 
v___x_2067_ = lean_st_ref_get(v___y_2066_);
v_env_2068_ = lean_ctor_get(v___x_2067_, 0);
lean_inc_ref(v_env_2068_);
lean_dec(v___x_2067_);
v___x_2069_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2068_, v_decl_2013_);
if (lean_obj_tag(v___x_2069_) == 0)
{
v___y_2056_ = v_env_2068_;
v___y_2057_ = v___y_2065_;
v___y_2058_ = v___y_2066_;
goto v___jp_2055_;
}
else
{
lean_object* v___x_2070_; 
lean_dec_ref(v___x_2069_);
lean_dec_ref(v_env_2068_);
lean_dec_ref(v_a_2011_);
lean_dec_ref(v_validate_2010_);
v___x_2070_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg(v_name_2012_, v_decl_2013_, v___y_2065_, v___y_2066_);
return v___x_2070_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__7___boxed(lean_object* v_validate_2075_, lean_object* v_a_2076_, lean_object* v_name_2077_, lean_object* v_decl_2078_, lean_object* v_stx_2079_, lean_object* v_kind_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_, lean_object* v___y_2083_){
_start:
{
uint8_t v_kind_boxed_2084_; lean_object* v_res_2085_; 
v_kind_boxed_2084_ = lean_unbox(v_kind_2080_);
v_res_2085_ = l_Lean_registerTagAttribute___lam__7(v_validate_2075_, v_a_2076_, v_name_2077_, v_decl_2078_, v_stx_2079_, v_kind_boxed_2084_, v___y_2081_, v___y_2082_);
lean_dec(v___y_2082_);
lean_dec_ref(v___y_2081_);
return v_res_2085_;
}
}
static lean_object* _init_l_Lean_registerTagAttribute___closed__5(void){
_start:
{
lean_object* v___x_2091_; lean_object* v___f_2092_; 
v___x_2091_ = l_Lean_NameSet_empty;
v___f_2092_ = lean_alloc_closure((void*)(l_Lean_registerTagAttribute___lam__4___boxed), 4, 1);
lean_closure_set(v___f_2092_, 0, v___x_2091_);
return v___f_2092_;
}
}
static lean_object* _init_l_Lean_registerTagAttribute___closed__6(void){
_start:
{
lean_object* v___x_2093_; lean_object* v___f_2094_; 
v___x_2093_ = l_Lean_NameSet_empty;
v___f_2094_ = lean_alloc_closure((void*)(l_Lean_registerTagAttribute___lam__5___boxed), 2, 1);
lean_closure_set(v___f_2094_, 0, v___x_2093_);
return v___f_2094_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute(lean_object* v_name_2097_, lean_object* v_descr_2098_, lean_object* v_validate_2099_, lean_object* v_ref_2100_, uint8_t v_applicationTime_2101_, lean_object* v_asyncMode_2102_){
_start:
{
lean_object* v___f_2104_; lean_object* v___f_2105_; lean_object* v___f_2106_; lean_object* v___f_2107_; lean_object* v___f_2108_; lean_object* v___f_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; 
v___f_2104_ = ((lean_object*)(l_Lean_registerTagAttribute___closed__0));
v___f_2105_ = ((lean_object*)(l_Lean_registerTagAttribute___closed__2));
v___f_2106_ = ((lean_object*)(l_Lean_registerTagAttribute___closed__3));
v___f_2107_ = ((lean_object*)(l_Lean_registerTagAttribute___closed__4));
v___f_2108_ = lean_obj_once(&l_Lean_registerTagAttribute___closed__5, &l_Lean_registerTagAttribute___closed__5_once, _init_l_Lean_registerTagAttribute___closed__5);
v___f_2109_ = lean_obj_once(&l_Lean_registerTagAttribute___closed__6, &l_Lean_registerTagAttribute___closed__6_once, _init_l_Lean_registerTagAttribute___closed__6);
v___x_2110_ = ((lean_object*)(l_Lean_registerTagAttribute___closed__7));
lean_inc(v_ref_2100_);
v___x_2111_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_2111_, 0, v_ref_2100_);
lean_ctor_set(v___x_2111_, 1, v___f_2109_);
lean_ctor_set(v___x_2111_, 2, v___f_2108_);
lean_ctor_set(v___x_2111_, 3, v___f_2107_);
lean_ctor_set(v___x_2111_, 4, v___f_2106_);
lean_ctor_set(v___x_2111_, 5, v___f_2105_);
lean_ctor_set(v___x_2111_, 6, v_asyncMode_2102_);
lean_ctor_set(v___x_2111_, 7, v___x_2110_);
v___x_2112_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2112_, 0, v___x_2111_);
lean_ctor_set(v___x_2112_, 1, v___f_2104_);
v___x_2113_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_2112_);
if (lean_obj_tag(v___x_2113_) == 0)
{
lean_object* v_a_2114_; lean_object* v___f_2115_; lean_object* v___f_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; 
v_a_2114_ = lean_ctor_get(v___x_2113_, 0);
lean_inc_n(v_a_2114_, 2);
lean_dec_ref(v___x_2113_);
lean_inc_n(v_name_2097_, 2);
v___f_2115_ = lean_alloc_closure((void*)(l_Lean_registerTagAttribute___lam__6___boxed), 5, 1);
lean_closure_set(v___f_2115_, 0, v_name_2097_);
v___f_2116_ = lean_alloc_closure((void*)(l_Lean_registerTagAttribute___lam__7___boxed), 9, 3);
lean_closure_set(v___f_2116_, 0, v_validate_2099_);
lean_closure_set(v___f_2116_, 1, v_a_2114_);
lean_closure_set(v___f_2116_, 2, v_name_2097_);
v___x_2117_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2117_, 0, v_ref_2100_);
lean_ctor_set(v___x_2117_, 1, v_name_2097_);
lean_ctor_set(v___x_2117_, 2, v_descr_2098_);
lean_ctor_set_uint8(v___x_2117_, sizeof(void*)*3, v_applicationTime_2101_);
v___x_2118_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2118_, 0, v___x_2117_);
lean_ctor_set(v___x_2118_, 1, v___f_2116_);
lean_ctor_set(v___x_2118_, 2, v___f_2115_);
lean_inc_ref(v___x_2118_);
v___x_2119_ = l_Lean_registerBuiltinAttribute(v___x_2118_);
if (lean_obj_tag(v___x_2119_) == 0)
{
lean_object* v___x_2121_; uint8_t v_isShared_2122_; uint8_t v_isSharedCheck_2127_; 
v_isSharedCheck_2127_ = !lean_is_exclusive(v___x_2119_);
if (v_isSharedCheck_2127_ == 0)
{
lean_object* v_unused_2128_; 
v_unused_2128_ = lean_ctor_get(v___x_2119_, 0);
lean_dec(v_unused_2128_);
v___x_2121_ = v___x_2119_;
v_isShared_2122_ = v_isSharedCheck_2127_;
goto v_resetjp_2120_;
}
else
{
lean_dec(v___x_2119_);
v___x_2121_ = lean_box(0);
v_isShared_2122_ = v_isSharedCheck_2127_;
goto v_resetjp_2120_;
}
v_resetjp_2120_:
{
lean_object* v___x_2123_; lean_object* v___x_2125_; 
v___x_2123_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2123_, 0, v___x_2118_);
lean_ctor_set(v___x_2123_, 1, v_a_2114_);
if (v_isShared_2122_ == 0)
{
lean_ctor_set(v___x_2121_, 0, v___x_2123_);
v___x_2125_ = v___x_2121_;
goto v_reusejp_2124_;
}
else
{
lean_object* v_reuseFailAlloc_2126_; 
v_reuseFailAlloc_2126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2126_, 0, v___x_2123_);
v___x_2125_ = v_reuseFailAlloc_2126_;
goto v_reusejp_2124_;
}
v_reusejp_2124_:
{
return v___x_2125_;
}
}
}
else
{
lean_object* v_a_2129_; lean_object* v___x_2131_; uint8_t v_isShared_2132_; uint8_t v_isSharedCheck_2136_; 
lean_dec_ref(v___x_2118_);
lean_dec(v_a_2114_);
v_a_2129_ = lean_ctor_get(v___x_2119_, 0);
v_isSharedCheck_2136_ = !lean_is_exclusive(v___x_2119_);
if (v_isSharedCheck_2136_ == 0)
{
v___x_2131_ = v___x_2119_;
v_isShared_2132_ = v_isSharedCheck_2136_;
goto v_resetjp_2130_;
}
else
{
lean_inc(v_a_2129_);
lean_dec(v___x_2119_);
v___x_2131_ = lean_box(0);
v_isShared_2132_ = v_isSharedCheck_2136_;
goto v_resetjp_2130_;
}
v_resetjp_2130_:
{
lean_object* v___x_2134_; 
if (v_isShared_2132_ == 0)
{
v___x_2134_ = v___x_2131_;
goto v_reusejp_2133_;
}
else
{
lean_object* v_reuseFailAlloc_2135_; 
v_reuseFailAlloc_2135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2135_, 0, v_a_2129_);
v___x_2134_ = v_reuseFailAlloc_2135_;
goto v_reusejp_2133_;
}
v_reusejp_2133_:
{
return v___x_2134_;
}
}
}
}
else
{
lean_object* v_a_2137_; lean_object* v___x_2139_; uint8_t v_isShared_2140_; uint8_t v_isSharedCheck_2144_; 
lean_dec(v_ref_2100_);
lean_dec_ref(v_validate_2099_);
lean_dec_ref(v_descr_2098_);
lean_dec(v_name_2097_);
v_a_2137_ = lean_ctor_get(v___x_2113_, 0);
v_isSharedCheck_2144_ = !lean_is_exclusive(v___x_2113_);
if (v_isSharedCheck_2144_ == 0)
{
v___x_2139_ = v___x_2113_;
v_isShared_2140_ = v_isSharedCheck_2144_;
goto v_resetjp_2138_;
}
else
{
lean_inc(v_a_2137_);
lean_dec(v___x_2113_);
v___x_2139_ = lean_box(0);
v_isShared_2140_ = v_isSharedCheck_2144_;
goto v_resetjp_2138_;
}
v_resetjp_2138_:
{
lean_object* v___x_2142_; 
if (v_isShared_2140_ == 0)
{
v___x_2142_ = v___x_2139_;
goto v_reusejp_2141_;
}
else
{
lean_object* v_reuseFailAlloc_2143_; 
v_reuseFailAlloc_2143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2143_, 0, v_a_2137_);
v___x_2142_ = v_reuseFailAlloc_2143_;
goto v_reusejp_2141_;
}
v_reusejp_2141_:
{
return v___x_2142_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___boxed(lean_object* v_name_2145_, lean_object* v_descr_2146_, lean_object* v_validate_2147_, lean_object* v_ref_2148_, lean_object* v_applicationTime_2149_, lean_object* v_asyncMode_2150_, lean_object* v_a_2151_){
_start:
{
uint8_t v_applicationTime_boxed_2152_; lean_object* v_res_2153_; 
v_applicationTime_boxed_2152_ = lean_unbox(v_applicationTime_2149_);
v_res_2153_ = l_Lean_registerTagAttribute(v_name_2145_, v_descr_2146_, v_validate_2147_, v_ref_2148_, v_applicationTime_boxed_2152_, v_asyncMode_2150_);
return v_res_2153_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerTagAttribute_spec__1(lean_object* v_init_2154_, lean_object* v_t_2155_){
_start:
{
lean_object* v___x_2156_; 
v___x_2156_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerTagAttribute_spec__1_spec__1(v_init_2154_, v_t_2155_);
return v___x_2156_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3(lean_object* v_n_2157_, lean_object* v_as_2158_, lean_object* v_lo_2159_, lean_object* v_hi_2160_, lean_object* v_w_2161_, lean_object* v_hlo_2162_, lean_object* v_hhi_2163_){
_start:
{
lean_object* v___x_2164_; 
v___x_2164_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___redArg(v_n_2157_, v_as_2158_, v_lo_2159_, v_hi_2160_);
return v___x_2164_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___boxed(lean_object* v_n_2165_, lean_object* v_as_2166_, lean_object* v_lo_2167_, lean_object* v_hi_2168_, lean_object* v_w_2169_, lean_object* v_hlo_2170_, lean_object* v_hhi_2171_){
_start:
{
lean_object* v_res_2172_; 
v_res_2172_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3(v_n_2165_, v_as_2166_, v_lo_2167_, v_hi_2168_, v_w_2169_, v_hlo_2170_, v_hhi_2171_);
lean_dec(v_hi_2168_);
lean_dec(v_n_2165_);
return v_res_2172_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4(lean_object* v_00_u03b1_2173_, lean_object* v_attrName_2174_, lean_object* v_declName_2175_, lean_object* v_asyncPrefix_x3f_2176_, lean_object* v___y_2177_, lean_object* v___y_2178_){
_start:
{
lean_object* v___x_2180_; 
v___x_2180_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___redArg(v_attrName_2174_, v_declName_2175_, v_asyncPrefix_x3f_2176_, v___y_2177_, v___y_2178_);
return v___x_2180_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___boxed(lean_object* v_00_u03b1_2181_, lean_object* v_attrName_2182_, lean_object* v_declName_2183_, lean_object* v_asyncPrefix_x3f_2184_, lean_object* v___y_2185_, lean_object* v___y_2186_, lean_object* v___y_2187_){
_start:
{
lean_object* v_res_2188_; 
v_res_2188_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4(v_00_u03b1_2181_, v_attrName_2182_, v_declName_2183_, v_asyncPrefix_x3f_2184_, v___y_2185_, v___y_2186_);
lean_dec(v___y_2186_);
lean_dec_ref(v___y_2185_);
return v_res_2188_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5(lean_object* v_00_u03b1_2189_, lean_object* v_attrName_2190_, lean_object* v_declName_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_){
_start:
{
lean_object* v___x_2195_; 
v___x_2195_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg(v_attrName_2190_, v_declName_2191_, v___y_2192_, v___y_2193_);
return v___x_2195_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___boxed(lean_object* v_00_u03b1_2196_, lean_object* v_attrName_2197_, lean_object* v_declName_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_){
_start:
{
lean_object* v_res_2202_; 
v_res_2202_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5(v_00_u03b1_2196_, v_attrName_2197_, v_declName_2198_, v___y_2199_, v___y_2200_);
lean_dec(v___y_2200_);
lean_dec_ref(v___y_2199_);
return v_res_2202_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6(lean_object* v_00_u03b1_2203_, lean_object* v_name_2204_, uint8_t v_kind_2205_, lean_object* v___y_2206_, lean_object* v___y_2207_){
_start:
{
lean_object* v___x_2209_; 
v___x_2209_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg(v_name_2204_, v_kind_2205_, v___y_2206_, v___y_2207_);
return v___x_2209_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___boxed(lean_object* v_00_u03b1_2210_, lean_object* v_name_2211_, lean_object* v_kind_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_){
_start:
{
uint8_t v_kind_boxed_2216_; lean_object* v_res_2217_; 
v_kind_boxed_2216_ = lean_unbox(v_kind_2212_);
v_res_2217_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6(v_00_u03b1_2210_, v_name_2211_, v_kind_boxed_2216_, v___y_2213_, v___y_2214_);
lean_dec(v___y_2214_);
lean_dec_ref(v___y_2213_);
return v_res_2217_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4(lean_object* v_n_2218_, lean_object* v_lo_2219_, lean_object* v_hi_2220_, lean_object* v_hhi_2221_, lean_object* v_pivot_2222_, lean_object* v_as_2223_, lean_object* v_i_2224_, lean_object* v_k_2225_, lean_object* v_ilo_2226_, lean_object* v_ik_2227_, lean_object* v_w_2228_){
_start:
{
lean_object* v___x_2229_; 
v___x_2229_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4___redArg(v_hi_2220_, v_pivot_2222_, v_as_2223_, v_i_2224_, v_k_2225_);
return v___x_2229_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4___boxed(lean_object* v_n_2230_, lean_object* v_lo_2231_, lean_object* v_hi_2232_, lean_object* v_hhi_2233_, lean_object* v_pivot_2234_, lean_object* v_as_2235_, lean_object* v_i_2236_, lean_object* v_k_2237_, lean_object* v_ilo_2238_, lean_object* v_ik_2239_, lean_object* v_w_2240_){
_start:
{
lean_object* v_res_2241_; 
v_res_2241_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4(v_n_2230_, v_lo_2231_, v_hi_2232_, v_hhi_2233_, v_pivot_2234_, v_as_2235_, v_i_2236_, v_k_2237_, v_ilo_2238_, v_ik_2239_, v_w_2240_);
lean_dec(v_pivot_2234_);
lean_dec(v_hi_2232_);
lean_dec(v_lo_2231_);
lean_dec(v_n_2230_);
return v_res_2241_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg___lam__0(lean_object* v_attr_2242_, lean_object* v_decl_2243_, lean_object* v_env_2244_){
_start:
{
lean_object* v_ext_2245_; lean_object* v_toEnvExtension_2246_; lean_object* v_asyncMode_2247_; lean_object* v___x_2248_; 
v_ext_2245_ = lean_ctor_get(v_attr_2242_, 1);
lean_inc_ref(v_ext_2245_);
lean_dec_ref(v_attr_2242_);
v_toEnvExtension_2246_ = lean_ctor_get(v_ext_2245_, 0);
v_asyncMode_2247_ = lean_ctor_get(v_toEnvExtension_2246_, 2);
lean_inc(v_asyncMode_2247_);
lean_inc(v_decl_2243_);
v___x_2248_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_ext_2245_, v_env_2244_, v_decl_2243_, v_asyncMode_2247_, v_decl_2243_);
lean_dec(v_asyncMode_2247_);
return v___x_2248_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg___lam__1(lean_object* v_modifyEnv_2249_, lean_object* v___f_2250_, lean_object* v_____r_2251_){
_start:
{
lean_object* v___x_2252_; 
v___x_2252_ = lean_apply_1(v_modifyEnv_2249_, v___f_2250_);
return v___x_2252_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg___lam__2(lean_object* v_attr_2253_, lean_object* v_env_2254_, lean_object* v_decl_2255_, lean_object* v_inst_2256_, lean_object* v_inst_2257_, lean_object* v_toBind_2258_, lean_object* v___f_2259_, lean_object* v_modifyEnv_2260_, lean_object* v___f_2261_, lean_object* v_____r_2262_){
_start:
{
lean_object* v_ext_2263_; lean_object* v_toEnvExtension_2264_; lean_object* v_attr_2265_; lean_object* v_asyncMode_2266_; uint8_t v___x_2267_; 
v_ext_2263_ = lean_ctor_get(v_attr_2253_, 1);
v_toEnvExtension_2264_ = lean_ctor_get(v_ext_2263_, 0);
lean_inc_ref(v_toEnvExtension_2264_);
v_attr_2265_ = lean_ctor_get(v_attr_2253_, 0);
lean_inc_ref(v_attr_2265_);
lean_dec_ref(v_attr_2253_);
v_asyncMode_2266_ = lean_ctor_get(v_toEnvExtension_2264_, 2);
lean_inc(v_asyncMode_2266_);
lean_dec_ref(v_toEnvExtension_2264_);
lean_inc(v_decl_2255_);
lean_inc_ref(v_env_2254_);
v___x_2267_ = l_Lean_EnvExtension_asyncMayModify___redArg(v_env_2254_, v_decl_2255_, v_asyncMode_2266_);
lean_dec(v_asyncMode_2266_);
if (v___x_2267_ == 0)
{
lean_object* v_toAttributeImplCore_2268_; lean_object* v_name_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; 
lean_dec_ref(v___f_2261_);
lean_dec(v_modifyEnv_2260_);
v_toAttributeImplCore_2268_ = lean_ctor_get(v_attr_2265_, 0);
lean_inc_ref(v_toAttributeImplCore_2268_);
lean_dec_ref(v_attr_2265_);
v_name_2269_ = lean_ctor_get(v_toAttributeImplCore_2268_, 1);
lean_inc(v_name_2269_);
lean_dec_ref(v_toAttributeImplCore_2268_);
v___x_2270_ = l_Lean_Environment_asyncPrefix_x3f(v_env_2254_);
v___x_2271_ = l_Lean_throwAttrNotInAsyncCtx___redArg(v_inst_2256_, v_inst_2257_, v_name_2269_, v_decl_2255_, v___x_2270_);
v___x_2272_ = lean_apply_4(v_toBind_2258_, lean_box(0), lean_box(0), v___x_2271_, v___f_2259_);
return v___x_2272_;
}
else
{
lean_object* v___x_2273_; 
lean_dec_ref(v_attr_2265_);
lean_dec(v___f_2259_);
lean_dec(v_toBind_2258_);
lean_dec_ref(v_inst_2257_);
lean_dec_ref(v_inst_2256_);
lean_dec(v_decl_2255_);
lean_dec_ref(v_env_2254_);
v___x_2273_ = lean_apply_1(v_modifyEnv_2260_, v___f_2261_);
return v___x_2273_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg___lam__3(lean_object* v___f_2274_, lean_object* v_____r_2275_){
_start:
{
lean_object* v___x_2276_; 
v___x_2276_ = lean_apply_1(v___f_2274_, v_____r_2275_);
return v___x_2276_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg___lam__4(lean_object* v_attr_2277_, lean_object* v_decl_2278_, lean_object* v_inst_2279_, lean_object* v_inst_2280_, lean_object* v_toBind_2281_, lean_object* v___f_2282_, lean_object* v_modifyEnv_2283_, lean_object* v___f_2284_, lean_object* v_env_2285_){
_start:
{
lean_object* v___f_2286_; lean_object* v___x_2287_; 
lean_inc_ref(v___f_2284_);
lean_inc(v_modifyEnv_2283_);
lean_inc(v___f_2282_);
lean_inc(v_toBind_2281_);
lean_inc_ref(v_inst_2280_);
lean_inc_ref(v_inst_2279_);
lean_inc(v_decl_2278_);
lean_inc_ref(v_env_2285_);
lean_inc_ref(v_attr_2277_);
v___f_2286_ = lean_alloc_closure((void*)(l_Lean_TagAttribute_setTag___redArg___lam__2), 10, 9);
lean_closure_set(v___f_2286_, 0, v_attr_2277_);
lean_closure_set(v___f_2286_, 1, v_env_2285_);
lean_closure_set(v___f_2286_, 2, v_decl_2278_);
lean_closure_set(v___f_2286_, 3, v_inst_2279_);
lean_closure_set(v___f_2286_, 4, v_inst_2280_);
lean_closure_set(v___f_2286_, 5, v_toBind_2281_);
lean_closure_set(v___f_2286_, 6, v___f_2282_);
lean_closure_set(v___f_2286_, 7, v_modifyEnv_2283_);
lean_closure_set(v___f_2286_, 8, v___f_2284_);
v___x_2287_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2285_, v_decl_2278_);
if (lean_obj_tag(v___x_2287_) == 0)
{
lean_object* v___x_2288_; lean_object* v___x_2289_; 
lean_dec_ref(v___f_2286_);
v___x_2288_ = lean_box(0);
v___x_2289_ = l_Lean_TagAttribute_setTag___redArg___lam__2(v_attr_2277_, v_env_2285_, v_decl_2278_, v_inst_2279_, v_inst_2280_, v_toBind_2281_, v___f_2282_, v_modifyEnv_2283_, v___f_2284_, v___x_2288_);
return v___x_2289_;
}
else
{
lean_object* v_attr_2290_; lean_object* v_toAttributeImplCore_2291_; lean_object* v_name_2292_; lean_object* v___f_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; 
lean_dec_ref(v___x_2287_);
lean_dec_ref(v_env_2285_);
lean_dec_ref(v___f_2284_);
lean_dec(v_modifyEnv_2283_);
lean_dec(v___f_2282_);
v_attr_2290_ = lean_ctor_get(v_attr_2277_, 0);
lean_inc_ref(v_attr_2290_);
lean_dec_ref(v_attr_2277_);
v_toAttributeImplCore_2291_ = lean_ctor_get(v_attr_2290_, 0);
lean_inc_ref(v_toAttributeImplCore_2291_);
lean_dec_ref(v_attr_2290_);
v_name_2292_ = lean_ctor_get(v_toAttributeImplCore_2291_, 1);
lean_inc(v_name_2292_);
lean_dec_ref(v_toAttributeImplCore_2291_);
v___f_2293_ = lean_alloc_closure((void*)(l_Lean_TagAttribute_setTag___redArg___lam__3), 2, 1);
lean_closure_set(v___f_2293_, 0, v___f_2286_);
v___x_2294_ = l_Lean_throwAttrDeclInImportedModule___redArg(v_inst_2279_, v_inst_2280_, v_name_2292_, v_decl_2278_);
v___x_2295_ = lean_apply_4(v_toBind_2281_, lean_box(0), lean_box(0), v___x_2294_, v___f_2293_);
return v___x_2295_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg(lean_object* v_inst_2296_, lean_object* v_inst_2297_, lean_object* v_inst_2298_, lean_object* v_attr_2299_, lean_object* v_decl_2300_){
_start:
{
lean_object* v_toBind_2301_; lean_object* v_getEnv_2302_; lean_object* v_modifyEnv_2303_; lean_object* v___f_2304_; lean_object* v___f_2305_; lean_object* v___f_2306_; lean_object* v___x_2307_; 
v_toBind_2301_ = lean_ctor_get(v_inst_2296_, 1);
lean_inc_n(v_toBind_2301_, 2);
v_getEnv_2302_ = lean_ctor_get(v_inst_2298_, 0);
lean_inc(v_getEnv_2302_);
v_modifyEnv_2303_ = lean_ctor_get(v_inst_2298_, 1);
lean_inc_n(v_modifyEnv_2303_, 2);
lean_dec_ref(v_inst_2298_);
lean_inc(v_decl_2300_);
lean_inc_ref(v_attr_2299_);
v___f_2304_ = lean_alloc_closure((void*)(l_Lean_TagAttribute_setTag___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2304_, 0, v_attr_2299_);
lean_closure_set(v___f_2304_, 1, v_decl_2300_);
lean_inc_ref(v___f_2304_);
v___f_2305_ = lean_alloc_closure((void*)(l_Lean_TagAttribute_setTag___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2305_, 0, v_modifyEnv_2303_);
lean_closure_set(v___f_2305_, 1, v___f_2304_);
v___f_2306_ = lean_alloc_closure((void*)(l_Lean_TagAttribute_setTag___redArg___lam__4), 9, 8);
lean_closure_set(v___f_2306_, 0, v_attr_2299_);
lean_closure_set(v___f_2306_, 1, v_decl_2300_);
lean_closure_set(v___f_2306_, 2, v_inst_2296_);
lean_closure_set(v___f_2306_, 3, v_inst_2297_);
lean_closure_set(v___f_2306_, 4, v_toBind_2301_);
lean_closure_set(v___f_2306_, 5, v___f_2305_);
lean_closure_set(v___f_2306_, 6, v_modifyEnv_2303_);
lean_closure_set(v___f_2306_, 7, v___f_2304_);
v___x_2307_ = lean_apply_4(v_toBind_2301_, lean_box(0), lean_box(0), v_getEnv_2302_, v___f_2306_);
return v___x_2307_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag(lean_object* v_m_2308_, lean_object* v_inst_2309_, lean_object* v_inst_2310_, lean_object* v_inst_2311_, lean_object* v_attr_2312_, lean_object* v_decl_2313_){
_start:
{
lean_object* v___x_2314_; 
v___x_2314_ = l_Lean_TagAttribute_setTag___redArg(v_inst_2309_, v_inst_2310_, v_inst_2311_, v_attr_2312_, v_decl_2313_);
return v___x_2314_;
}
}
LEAN_EXPORT uint8_t l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___redArg(lean_object* v_as_2315_, lean_object* v_k_2316_, lean_object* v_x_2317_, lean_object* v_x_2318_){
_start:
{
lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v_m_2321_; lean_object* v_a_2322_; uint8_t v___x_2323_; 
v___x_2319_ = lean_nat_add(v_x_2317_, v_x_2318_);
v___x_2320_ = lean_unsigned_to_nat(1u);
v_m_2321_ = lean_nat_shiftr(v___x_2319_, v___x_2320_);
lean_dec(v___x_2319_);
v_a_2322_ = lean_array_fget_borrowed(v_as_2315_, v_m_2321_);
v___x_2323_ = l_Lean_Name_quickLt(v_a_2322_, v_k_2316_);
if (v___x_2323_ == 0)
{
uint8_t v___x_2324_; 
lean_dec(v_x_2318_);
v___x_2324_ = l_Lean_Name_quickLt(v_k_2316_, v_a_2322_);
if (v___x_2324_ == 0)
{
uint8_t v___x_2325_; 
lean_dec(v_m_2321_);
lean_dec(v_x_2317_);
v___x_2325_ = 1;
return v___x_2325_;
}
else
{
lean_object* v___x_2326_; uint8_t v___x_2327_; 
v___x_2326_ = lean_unsigned_to_nat(0u);
v___x_2327_ = lean_nat_dec_eq(v_m_2321_, v___x_2326_);
if (v___x_2327_ == 0)
{
lean_object* v___x_2328_; uint8_t v___x_2329_; 
v___x_2328_ = lean_nat_sub(v_m_2321_, v___x_2320_);
lean_dec(v_m_2321_);
v___x_2329_ = lean_nat_dec_lt(v___x_2328_, v_x_2317_);
if (v___x_2329_ == 0)
{
v_x_2318_ = v___x_2328_;
goto _start;
}
else
{
lean_dec(v___x_2328_);
lean_dec(v_x_2317_);
return v___x_2323_;
}
}
else
{
lean_dec(v_m_2321_);
lean_dec(v_x_2317_);
return v___x_2323_;
}
}
}
else
{
lean_object* v___x_2331_; uint8_t v___x_2332_; 
lean_dec(v_x_2317_);
v___x_2331_ = lean_nat_add(v_m_2321_, v___x_2320_);
lean_dec(v_m_2321_);
v___x_2332_ = lean_nat_dec_le(v___x_2331_, v_x_2318_);
if (v___x_2332_ == 0)
{
lean_dec(v___x_2331_);
lean_dec(v_x_2318_);
return v___x_2332_;
}
else
{
v_x_2317_ = v___x_2331_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___redArg___boxed(lean_object* v_as_2334_, lean_object* v_k_2335_, lean_object* v_x_2336_, lean_object* v_x_2337_){
_start:
{
uint8_t v_res_2338_; lean_object* v_r_2339_; 
v_res_2338_ = l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___redArg(v_as_2334_, v_k_2335_, v_x_2336_, v_x_2337_);
lean_dec(v_k_2335_);
lean_dec_ref(v_as_2334_);
v_r_2339_ = lean_box(v_res_2338_);
return v_r_2339_;
}
}
LEAN_EXPORT uint8_t l_Lean_TagAttribute_hasTag(lean_object* v_attr_2340_, lean_object* v_env_2341_, lean_object* v_decl_2342_){
_start:
{
lean_object* v___x_2343_; lean_object* v___x_2344_; 
v___x_2343_ = lean_box(1);
v___x_2344_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2341_, v_decl_2342_);
if (lean_obj_tag(v___x_2344_) == 0)
{
lean_object* v_ext_2345_; lean_object* v_toEnvExtension_2346_; lean_object* v_asyncMode_2347_; lean_object* v___x_2348_; uint8_t v___x_2349_; 
v_ext_2345_ = lean_ctor_get(v_attr_2340_, 1);
v_toEnvExtension_2346_ = lean_ctor_get(v_ext_2345_, 0);
v_asyncMode_2347_ = lean_ctor_get(v_toEnvExtension_2346_, 2);
lean_inc(v_decl_2342_);
v___x_2348_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2343_, v_ext_2345_, v_env_2341_, v_asyncMode_2347_, v_decl_2342_);
v___x_2349_ = l_Lean_NameSet_contains(v___x_2348_, v_decl_2342_);
lean_dec(v_decl_2342_);
lean_dec(v___x_2348_);
return v___x_2349_;
}
else
{
lean_object* v_val_2350_; lean_object* v_ext_2351_; uint8_t v___x_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; uint8_t v___x_2356_; 
v_val_2350_ = lean_ctor_get(v___x_2344_, 0);
lean_inc(v_val_2350_);
lean_dec_ref(v___x_2344_);
v_ext_2351_ = lean_ctor_get(v_attr_2340_, 1);
v___x_2352_ = 0;
v___x_2353_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_2343_, v_ext_2351_, v_env_2341_, v_val_2350_, v___x_2352_);
lean_dec(v_val_2350_);
lean_dec_ref(v_env_2341_);
v___x_2354_ = lean_unsigned_to_nat(0u);
v___x_2355_ = lean_array_get_size(v___x_2353_);
v___x_2356_ = lean_nat_dec_lt(v___x_2354_, v___x_2355_);
if (v___x_2356_ == 0)
{
lean_dec_ref(v___x_2353_);
lean_dec(v_decl_2342_);
return v___x_2356_;
}
else
{
lean_object* v___x_2357_; lean_object* v___x_2358_; uint8_t v___x_2359_; 
v___x_2357_ = lean_unsigned_to_nat(1u);
v___x_2358_ = lean_nat_sub(v___x_2355_, v___x_2357_);
v___x_2359_ = lean_nat_dec_le(v___x_2354_, v___x_2358_);
if (v___x_2359_ == 0)
{
lean_dec(v___x_2358_);
lean_dec_ref(v___x_2353_);
lean_dec(v_decl_2342_);
return v___x_2359_;
}
else
{
uint8_t v___x_2360_; 
v___x_2360_ = l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___redArg(v___x_2353_, v_decl_2342_, v___x_2354_, v___x_2358_);
lean_dec(v_decl_2342_);
lean_dec_ref(v___x_2353_);
return v___x_2360_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_hasTag___boxed(lean_object* v_attr_2361_, lean_object* v_env_2362_, lean_object* v_decl_2363_){
_start:
{
uint8_t v_res_2364_; lean_object* v_r_2365_; 
v_res_2364_ = l_Lean_TagAttribute_hasTag(v_attr_2361_, v_env_2362_, v_decl_2363_);
lean_dec_ref(v_attr_2361_);
v_r_2365_ = lean_box(v_res_2364_);
return v_r_2365_;
}
}
LEAN_EXPORT uint8_t l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0(lean_object* v_as_2366_, lean_object* v_k_2367_, lean_object* v_x_2368_, lean_object* v_x_2369_, lean_object* v_x_2370_){
_start:
{
uint8_t v___x_2371_; 
v___x_2371_ = l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___redArg(v_as_2366_, v_k_2367_, v_x_2368_, v_x_2369_);
return v___x_2371_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___boxed(lean_object* v_as_2372_, lean_object* v_k_2373_, lean_object* v_x_2374_, lean_object* v_x_2375_, lean_object* v_x_2376_){
_start:
{
uint8_t v_res_2377_; lean_object* v_r_2378_; 
v_res_2377_ = l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0(v_as_2372_, v_k_2373_, v_x_2374_, v_x_2375_, v_x_2376_);
lean_dec(v_k_2373_);
lean_dec_ref(v_as_2372_);
v_r_2378_ = lean_box(v_res_2377_);
return v_r_2378_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__0(lean_object* v_x_2379_, lean_object* v___y_2380_){
_start:
{
lean_object* v___x_2382_; lean_object* v___x_2383_; 
v___x_2382_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___lam__0___closed__1));
v___x_2383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2383_, 0, v___x_2382_);
return v___x_2383_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__0___boxed(lean_object* v_x_2384_, lean_object* v___y_2385_, lean_object* v___y_2386_){
_start:
{
lean_object* v_res_2387_; 
v_res_2387_ = l_Lean_instInhabitedParametricAttribute_default___lam__0(v_x_2384_, v___y_2385_);
lean_dec_ref(v___y_2385_);
lean_dec_ref(v_x_2384_);
return v_res_2387_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__1(lean_object* v_s_2388_, lean_object* v_x_2389_){
_start:
{
lean_inc_ref(v_s_2388_);
return v_s_2388_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__1___boxed(lean_object* v_s_2390_, lean_object* v_x_2391_){
_start:
{
lean_object* v_res_2392_; 
v_res_2392_ = l_Lean_instInhabitedParametricAttribute_default___lam__1(v_s_2390_, v_x_2391_);
lean_dec_ref(v_x_2391_);
lean_dec_ref(v_s_2390_);
return v_res_2392_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__2(lean_object* v_x_2397_, lean_object* v_x_2398_){
_start:
{
lean_object* v___x_2399_; 
v___x_2399_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___lam__2___closed__1));
return v___x_2399_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__2___boxed(lean_object* v_x_2400_, lean_object* v_x_2401_){
_start:
{
lean_object* v_res_2402_; 
v_res_2402_ = l_Lean_instInhabitedParametricAttribute_default___lam__2(v_x_2400_, v_x_2401_);
lean_dec_ref(v_x_2401_);
lean_dec_ref(v_x_2400_);
return v_res_2402_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__3(lean_object* v_x_2403_){
_start:
{
lean_object* v___x_2404_; 
v___x_2404_ = lean_box(0);
return v___x_2404_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__3___boxed(lean_object* v_x_2405_){
_start:
{
lean_object* v_res_2406_; 
v_res_2406_ = l_Lean_instInhabitedParametricAttribute_default___lam__3(v_x_2405_);
lean_dec_ref(v_x_2405_);
return v_res_2406_;
}
}
static lean_object* _init_l_Lean_instInhabitedParametricAttribute_default___closed__4(void){
_start:
{
lean_object* v___x_2411_; 
v___x_2411_ = l_Lean_instInhabitedEnvExtension_default(lean_box(0));
return v___x_2411_;
}
}
static lean_object* _init_l_Lean_instInhabitedParametricAttribute_default___closed__5(void){
_start:
{
lean_object* v___f_2412_; lean_object* v___f_2413_; lean_object* v___f_2414_; lean_object* v___f_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; 
v___f_2412_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___closed__3));
v___f_2413_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___closed__2));
v___f_2414_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___closed__1));
v___f_2415_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___closed__0));
v___x_2416_ = lean_box(0);
v___x_2417_ = lean_obj_once(&l_Lean_instInhabitedParametricAttribute_default___closed__4, &l_Lean_instInhabitedParametricAttribute_default___closed__4_once, _init_l_Lean_instInhabitedParametricAttribute_default___closed__4);
v___x_2418_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2418_, 0, v___x_2417_);
lean_ctor_set(v___x_2418_, 1, v___x_2416_);
lean_ctor_set(v___x_2418_, 2, v___f_2415_);
lean_ctor_set(v___x_2418_, 3, v___f_2414_);
lean_ctor_set(v___x_2418_, 4, v___f_2413_);
lean_ctor_set(v___x_2418_, 5, v___f_2412_);
return v___x_2418_;
}
}
static lean_object* _init_l_Lean_instInhabitedParametricAttribute_default___closed__6(void){
_start:
{
uint8_t v___x_2419_; lean_object* v___x_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; 
v___x_2419_ = 0;
v___x_2420_ = lean_obj_once(&l_Lean_instInhabitedParametricAttribute_default___closed__5, &l_Lean_instInhabitedParametricAttribute_default___closed__5_once, _init_l_Lean_instInhabitedParametricAttribute_default___closed__5);
v___x_2421_ = ((lean_object*)(l_Lean_instInhabitedAttributeImpl_default));
v___x_2422_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2422_, 0, v___x_2421_);
lean_ctor_set(v___x_2422_, 1, v___x_2420_);
lean_ctor_set_uint8(v___x_2422_, sizeof(void*)*2, v___x_2419_);
return v___x_2422_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default(lean_object* v_00_u03b1_2423_){
_start:
{
lean_object* v___x_2424_; 
v___x_2424_ = lean_obj_once(&l_Lean_instInhabitedParametricAttribute_default___closed__6, &l_Lean_instInhabitedParametricAttribute_default___closed__6_once, _init_l_Lean_instInhabitedParametricAttribute_default___closed__6);
return v___x_2424_;
}
}
static lean_object* _init_l_Lean_instInhabitedParametricAttribute___closed__0(void){
_start:
{
lean_object* v___x_2425_; 
v___x_2425_ = l_Lean_instInhabitedParametricAttribute_default(lean_box(0));
return v___x_2425_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute(lean_object* v_a_2426_){
_start:
{
lean_object* v___x_2427_; 
v___x_2427_ = lean_obj_once(&l_Lean_instInhabitedParametricAttribute___closed__0, &l_Lean_instInhabitedParametricAttribute___closed__0_once, _init_l_Lean_instInhabitedParametricAttribute___closed__0);
return v___x_2427_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_registerParametricAttribute_spec__4___redArg(lean_object* v_env_2428_, lean_object* v___y_2429_){
_start:
{
lean_object* v___x_2431_; lean_object* v_nextMacroScope_2432_; lean_object* v_ngen_2433_; lean_object* v_auxDeclNGen_2434_; lean_object* v_traceState_2435_; lean_object* v_messages_2436_; lean_object* v_infoState_2437_; lean_object* v_snapshotTasks_2438_; lean_object* v_newDecls_2439_; lean_object* v___x_2441_; uint8_t v_isShared_2442_; uint8_t v_isSharedCheck_2450_; 
v___x_2431_ = lean_st_ref_take(v___y_2429_);
v_nextMacroScope_2432_ = lean_ctor_get(v___x_2431_, 1);
v_ngen_2433_ = lean_ctor_get(v___x_2431_, 2);
v_auxDeclNGen_2434_ = lean_ctor_get(v___x_2431_, 3);
v_traceState_2435_ = lean_ctor_get(v___x_2431_, 4);
v_messages_2436_ = lean_ctor_get(v___x_2431_, 6);
v_infoState_2437_ = lean_ctor_get(v___x_2431_, 7);
v_snapshotTasks_2438_ = lean_ctor_get(v___x_2431_, 8);
v_newDecls_2439_ = lean_ctor_get(v___x_2431_, 9);
v_isSharedCheck_2450_ = !lean_is_exclusive(v___x_2431_);
if (v_isSharedCheck_2450_ == 0)
{
lean_object* v_unused_2451_; lean_object* v_unused_2452_; 
v_unused_2451_ = lean_ctor_get(v___x_2431_, 5);
lean_dec(v_unused_2451_);
v_unused_2452_ = lean_ctor_get(v___x_2431_, 0);
lean_dec(v_unused_2452_);
v___x_2441_ = v___x_2431_;
v_isShared_2442_ = v_isSharedCheck_2450_;
goto v_resetjp_2440_;
}
else
{
lean_inc(v_newDecls_2439_);
lean_inc(v_snapshotTasks_2438_);
lean_inc(v_infoState_2437_);
lean_inc(v_messages_2436_);
lean_inc(v_traceState_2435_);
lean_inc(v_auxDeclNGen_2434_);
lean_inc(v_ngen_2433_);
lean_inc(v_nextMacroScope_2432_);
lean_dec(v___x_2431_);
v___x_2441_ = lean_box(0);
v_isShared_2442_ = v_isSharedCheck_2450_;
goto v_resetjp_2440_;
}
v_resetjp_2440_:
{
lean_object* v___x_2443_; lean_object* v___x_2445_; 
v___x_2443_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2);
if (v_isShared_2442_ == 0)
{
lean_ctor_set(v___x_2441_, 5, v___x_2443_);
lean_ctor_set(v___x_2441_, 0, v_env_2428_);
v___x_2445_ = v___x_2441_;
goto v_reusejp_2444_;
}
else
{
lean_object* v_reuseFailAlloc_2449_; 
v_reuseFailAlloc_2449_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2449_, 0, v_env_2428_);
lean_ctor_set(v_reuseFailAlloc_2449_, 1, v_nextMacroScope_2432_);
lean_ctor_set(v_reuseFailAlloc_2449_, 2, v_ngen_2433_);
lean_ctor_set(v_reuseFailAlloc_2449_, 3, v_auxDeclNGen_2434_);
lean_ctor_set(v_reuseFailAlloc_2449_, 4, v_traceState_2435_);
lean_ctor_set(v_reuseFailAlloc_2449_, 5, v___x_2443_);
lean_ctor_set(v_reuseFailAlloc_2449_, 6, v_messages_2436_);
lean_ctor_set(v_reuseFailAlloc_2449_, 7, v_infoState_2437_);
lean_ctor_set(v_reuseFailAlloc_2449_, 8, v_snapshotTasks_2438_);
lean_ctor_set(v_reuseFailAlloc_2449_, 9, v_newDecls_2439_);
v___x_2445_ = v_reuseFailAlloc_2449_;
goto v_reusejp_2444_;
}
v_reusejp_2444_:
{
lean_object* v___x_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; 
v___x_2446_ = lean_st_ref_set(v___y_2429_, v___x_2445_);
v___x_2447_ = lean_box(0);
v___x_2448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2448_, 0, v___x_2447_);
return v___x_2448_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_registerParametricAttribute_spec__4___redArg___boxed(lean_object* v_env_2453_, lean_object* v___y_2454_, lean_object* v___y_2455_){
_start:
{
lean_object* v_res_2456_; 
v_res_2456_ = l_Lean_setEnv___at___00Lean_registerParametricAttribute_spec__4___redArg(v_env_2453_, v___y_2454_);
lean_dec(v___y_2454_);
return v_res_2456_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_registerParametricAttribute_spec__4(lean_object* v_env_2457_, lean_object* v___y_2458_, lean_object* v___y_2459_){
_start:
{
lean_object* v___x_2461_; 
v___x_2461_ = l_Lean_setEnv___at___00Lean_registerParametricAttribute_spec__4___redArg(v_env_2457_, v___y_2459_);
return v___x_2461_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_registerParametricAttribute_spec__4___boxed(lean_object* v_env_2462_, lean_object* v___y_2463_, lean_object* v___y_2464_, lean_object* v___y_2465_){
_start:
{
lean_object* v_res_2466_; 
v_res_2466_ = l_Lean_setEnv___at___00Lean_registerParametricAttribute_spec__4(v_env_2462_, v___y_2463_, v___y_2464_);
lean_dec(v___y_2464_);
lean_dec_ref(v___y_2463_);
return v_res_2466_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___lam__0(lean_object* v_x_2467_, lean_object* v_p_2468_){
_start:
{
lean_object* v_fst_2469_; lean_object* v_snd_2470_; lean_object* v___x_2472_; uint8_t v_isShared_2473_; uint8_t v_isSharedCheck_2487_; 
v_fst_2469_ = lean_ctor_get(v_x_2467_, 0);
v_snd_2470_ = lean_ctor_get(v_x_2467_, 1);
v_isSharedCheck_2487_ = !lean_is_exclusive(v_x_2467_);
if (v_isSharedCheck_2487_ == 0)
{
v___x_2472_ = v_x_2467_;
v_isShared_2473_ = v_isSharedCheck_2487_;
goto v_resetjp_2471_;
}
else
{
lean_inc(v_snd_2470_);
lean_inc(v_fst_2469_);
lean_dec(v_x_2467_);
v___x_2472_ = lean_box(0);
v_isShared_2473_ = v_isSharedCheck_2487_;
goto v_resetjp_2471_;
}
v_resetjp_2471_:
{
lean_object* v_fst_2474_; lean_object* v_snd_2475_; lean_object* v___x_2477_; uint8_t v_isShared_2478_; uint8_t v_isSharedCheck_2486_; 
v_fst_2474_ = lean_ctor_get(v_p_2468_, 0);
v_snd_2475_ = lean_ctor_get(v_p_2468_, 1);
v_isSharedCheck_2486_ = !lean_is_exclusive(v_p_2468_);
if (v_isSharedCheck_2486_ == 0)
{
v___x_2477_ = v_p_2468_;
v_isShared_2478_ = v_isSharedCheck_2486_;
goto v_resetjp_2476_;
}
else
{
lean_inc(v_snd_2475_);
lean_inc(v_fst_2474_);
lean_dec(v_p_2468_);
v___x_2477_ = lean_box(0);
v_isShared_2478_ = v_isSharedCheck_2486_;
goto v_resetjp_2476_;
}
v_resetjp_2476_:
{
lean_object* v___x_2480_; 
lean_inc(v_fst_2474_);
if (v_isShared_2473_ == 0)
{
lean_ctor_set_tag(v___x_2472_, 1);
lean_ctor_set(v___x_2472_, 1, v_fst_2469_);
lean_ctor_set(v___x_2472_, 0, v_fst_2474_);
v___x_2480_ = v___x_2472_;
goto v_reusejp_2479_;
}
else
{
lean_object* v_reuseFailAlloc_2485_; 
v_reuseFailAlloc_2485_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2485_, 0, v_fst_2474_);
lean_ctor_set(v_reuseFailAlloc_2485_, 1, v_fst_2469_);
v___x_2480_ = v_reuseFailAlloc_2485_;
goto v_reusejp_2479_;
}
v_reusejp_2479_:
{
lean_object* v___x_2481_; lean_object* v___x_2483_; 
v___x_2481_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_2474_, v_snd_2475_, v_snd_2470_);
if (v_isShared_2478_ == 0)
{
lean_ctor_set(v___x_2477_, 1, v___x_2481_);
lean_ctor_set(v___x_2477_, 0, v___x_2480_);
v___x_2483_ = v___x_2477_;
goto v_reusejp_2482_;
}
else
{
lean_object* v_reuseFailAlloc_2484_; 
v_reuseFailAlloc_2484_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2484_, 0, v___x_2480_);
lean_ctor_set(v_reuseFailAlloc_2484_, 1, v___x_2481_);
v___x_2483_ = v_reuseFailAlloc_2484_;
goto v_reusejp_2482_;
}
v_reusejp_2482_:
{
return v___x_2483_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1_spec__1___redArg(lean_object* v_init_2488_, lean_object* v_x_2489_){
_start:
{
if (lean_obj_tag(v_x_2489_) == 0)
{
lean_object* v_k_2490_; lean_object* v_v_2491_; lean_object* v_l_2492_; lean_object* v_r_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; lean_object* v___x_2496_; 
v_k_2490_ = lean_ctor_get(v_x_2489_, 1);
v_v_2491_ = lean_ctor_get(v_x_2489_, 2);
v_l_2492_ = lean_ctor_get(v_x_2489_, 3);
v_r_2493_ = lean_ctor_get(v_x_2489_, 4);
v___x_2494_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1_spec__1___redArg(v_init_2488_, v_l_2492_);
lean_inc(v_v_2491_);
lean_inc(v_k_2490_);
v___x_2495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2495_, 0, v_k_2490_);
lean_ctor_set(v___x_2495_, 1, v_v_2491_);
v___x_2496_ = lean_array_push(v___x_2494_, v___x_2495_);
v_init_2488_ = v___x_2496_;
v_x_2489_ = v_r_2493_;
goto _start;
}
else
{
return v_init_2488_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1_spec__1___redArg___boxed(lean_object* v_init_2498_, lean_object* v_x_2499_){
_start:
{
lean_object* v_res_2500_; 
v_res_2500_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1_spec__1___redArg(v_init_2498_, v_x_2499_);
lean_dec(v_x_2499_);
return v_res_2500_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2_spec__3___redArg(lean_object* v_hi_2501_, lean_object* v_pivot_2502_, lean_object* v_as_2503_, lean_object* v_i_2504_, lean_object* v_k_2505_){
_start:
{
uint8_t v___x_2506_; 
v___x_2506_ = lean_nat_dec_lt(v_k_2505_, v_hi_2501_);
if (v___x_2506_ == 0)
{
lean_object* v___x_2507_; lean_object* v___x_2508_; 
lean_dec(v_k_2505_);
v___x_2507_ = lean_array_fswap(v_as_2503_, v_i_2504_, v_hi_2501_);
v___x_2508_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2508_, 0, v_i_2504_);
lean_ctor_set(v___x_2508_, 1, v___x_2507_);
return v___x_2508_;
}
else
{
lean_object* v___x_2509_; lean_object* v_fst_2510_; lean_object* v_fst_2511_; uint8_t v___x_2512_; 
v___x_2509_ = lean_array_fget_borrowed(v_as_2503_, v_k_2505_);
v_fst_2510_ = lean_ctor_get(v___x_2509_, 0);
v_fst_2511_ = lean_ctor_get(v_pivot_2502_, 0);
v___x_2512_ = l_Lean_Name_quickLt(v_fst_2510_, v_fst_2511_);
if (v___x_2512_ == 0)
{
lean_object* v___x_2513_; lean_object* v___x_2514_; 
v___x_2513_ = lean_unsigned_to_nat(1u);
v___x_2514_ = lean_nat_add(v_k_2505_, v___x_2513_);
lean_dec(v_k_2505_);
v_k_2505_ = v___x_2514_;
goto _start;
}
else
{
lean_object* v___x_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; lean_object* v___x_2519_; 
v___x_2516_ = lean_array_fswap(v_as_2503_, v_i_2504_, v_k_2505_);
v___x_2517_ = lean_unsigned_to_nat(1u);
v___x_2518_ = lean_nat_add(v_i_2504_, v___x_2517_);
lean_dec(v_i_2504_);
v___x_2519_ = lean_nat_add(v_k_2505_, v___x_2517_);
lean_dec(v_k_2505_);
v_as_2503_ = v___x_2516_;
v_i_2504_ = v___x_2518_;
v_k_2505_ = v___x_2519_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2_spec__3___redArg___boxed(lean_object* v_hi_2521_, lean_object* v_pivot_2522_, lean_object* v_as_2523_, lean_object* v_i_2524_, lean_object* v_k_2525_){
_start:
{
lean_object* v_res_2526_; 
v_res_2526_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2_spec__3___redArg(v_hi_2521_, v_pivot_2522_, v_as_2523_, v_i_2524_, v_k_2525_);
lean_dec_ref(v_pivot_2522_);
lean_dec(v_hi_2521_);
return v_res_2526_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2___redArg___lam__0(lean_object* v_a_2527_, lean_object* v_b_2528_){
_start:
{
lean_object* v_fst_2529_; lean_object* v_fst_2530_; uint8_t v___x_2531_; 
v_fst_2529_ = lean_ctor_get(v_a_2527_, 0);
v_fst_2530_ = lean_ctor_get(v_b_2528_, 0);
v___x_2531_ = l_Lean_Name_quickLt(v_fst_2529_, v_fst_2530_);
return v___x_2531_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2___redArg___lam__0___boxed(lean_object* v_a_2532_, lean_object* v_b_2533_){
_start:
{
uint8_t v_res_2534_; lean_object* v_r_2535_; 
v_res_2534_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2___redArg___lam__0(v_a_2532_, v_b_2533_);
lean_dec_ref(v_b_2533_);
lean_dec_ref(v_a_2532_);
v_r_2535_ = lean_box(v_res_2534_);
return v_r_2535_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2___redArg(lean_object* v_n_2536_, lean_object* v_as_2537_, lean_object* v_lo_2538_, lean_object* v_hi_2539_){
_start:
{
lean_object* v___y_2541_; uint8_t v___x_2551_; 
v___x_2551_ = lean_nat_dec_lt(v_lo_2538_, v_hi_2539_);
if (v___x_2551_ == 0)
{
lean_dec(v_lo_2538_);
return v_as_2537_;
}
else
{
lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v_mid_2554_; lean_object* v___y_2556_; lean_object* v___y_2562_; lean_object* v___x_2567_; lean_object* v___x_2568_; uint8_t v___x_2569_; 
v___x_2552_ = lean_nat_add(v_lo_2538_, v_hi_2539_);
v___x_2553_ = lean_unsigned_to_nat(1u);
v_mid_2554_ = lean_nat_shiftr(v___x_2552_, v___x_2553_);
lean_dec(v___x_2552_);
v___x_2567_ = lean_array_fget_borrowed(v_as_2537_, v_mid_2554_);
v___x_2568_ = lean_array_fget_borrowed(v_as_2537_, v_lo_2538_);
v___x_2569_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2___redArg___lam__0(v___x_2567_, v___x_2568_);
if (v___x_2569_ == 0)
{
v___y_2562_ = v_as_2537_;
goto v___jp_2561_;
}
else
{
lean_object* v___x_2570_; 
v___x_2570_ = lean_array_fswap(v_as_2537_, v_lo_2538_, v_mid_2554_);
v___y_2562_ = v___x_2570_;
goto v___jp_2561_;
}
v___jp_2555_:
{
lean_object* v___x_2557_; lean_object* v___x_2558_; uint8_t v___x_2559_; 
v___x_2557_ = lean_array_fget_borrowed(v___y_2556_, v_mid_2554_);
v___x_2558_ = lean_array_fget_borrowed(v___y_2556_, v_hi_2539_);
v___x_2559_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2___redArg___lam__0(v___x_2557_, v___x_2558_);
if (v___x_2559_ == 0)
{
lean_dec(v_mid_2554_);
v___y_2541_ = v___y_2556_;
goto v___jp_2540_;
}
else
{
lean_object* v___x_2560_; 
v___x_2560_ = lean_array_fswap(v___y_2556_, v_mid_2554_, v_hi_2539_);
lean_dec(v_mid_2554_);
v___y_2541_ = v___x_2560_;
goto v___jp_2540_;
}
}
v___jp_2561_:
{
lean_object* v___x_2563_; lean_object* v___x_2564_; uint8_t v___x_2565_; 
v___x_2563_ = lean_array_fget_borrowed(v___y_2562_, v_hi_2539_);
v___x_2564_ = lean_array_fget_borrowed(v___y_2562_, v_lo_2538_);
v___x_2565_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2___redArg___lam__0(v___x_2563_, v___x_2564_);
if (v___x_2565_ == 0)
{
v___y_2556_ = v___y_2562_;
goto v___jp_2555_;
}
else
{
lean_object* v___x_2566_; 
v___x_2566_ = lean_array_fswap(v___y_2562_, v_lo_2538_, v_hi_2539_);
v___y_2556_ = v___x_2566_;
goto v___jp_2555_;
}
}
}
v___jp_2540_:
{
lean_object* v_pivot_2542_; lean_object* v___x_2543_; lean_object* v_fst_2544_; lean_object* v_snd_2545_; uint8_t v___x_2546_; 
v_pivot_2542_ = lean_array_fget(v___y_2541_, v_hi_2539_);
lean_inc_n(v_lo_2538_, 2);
v___x_2543_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2_spec__3___redArg(v_hi_2539_, v_pivot_2542_, v___y_2541_, v_lo_2538_, v_lo_2538_);
lean_dec(v_pivot_2542_);
v_fst_2544_ = lean_ctor_get(v___x_2543_, 0);
lean_inc(v_fst_2544_);
v_snd_2545_ = lean_ctor_get(v___x_2543_, 1);
lean_inc(v_snd_2545_);
lean_dec_ref(v___x_2543_);
v___x_2546_ = lean_nat_dec_le(v_hi_2539_, v_fst_2544_);
if (v___x_2546_ == 0)
{
lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; 
v___x_2547_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2___redArg(v_n_2536_, v_snd_2545_, v_lo_2538_, v_fst_2544_);
v___x_2548_ = lean_unsigned_to_nat(1u);
v___x_2549_ = lean_nat_add(v_fst_2544_, v___x_2548_);
lean_dec(v_fst_2544_);
v_as_2537_ = v___x_2547_;
v_lo_2538_ = v___x_2549_;
goto _start;
}
else
{
lean_dec(v_fst_2544_);
lean_dec(v_lo_2538_);
return v_snd_2545_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2___redArg___boxed(lean_object* v_n_2571_, lean_object* v_as_2572_, lean_object* v_lo_2573_, lean_object* v_hi_2574_){
_start:
{
lean_object* v_res_2575_; 
v_res_2575_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2___redArg(v_n_2571_, v_as_2572_, v_lo_2573_, v_hi_2574_);
lean_dec(v_hi_2574_);
lean_dec(v_n_2571_);
return v_res_2575_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3_spec__5___redArg(lean_object* v_snd_2576_, lean_object* v_as_2577_, size_t v_i_2578_, size_t v_stop_2579_, lean_object* v_b_2580_){
_start:
{
lean_object* v___y_2582_; uint8_t v___x_2586_; 
v___x_2586_ = lean_usize_dec_eq(v_i_2578_, v_stop_2579_);
if (v___x_2586_ == 0)
{
lean_object* v___x_2587_; lean_object* v___x_2588_; 
v___x_2587_ = lean_array_uget_borrowed(v_as_2577_, v_i_2578_);
v___x_2588_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_snd_2576_, v___x_2587_);
if (lean_obj_tag(v___x_2588_) == 0)
{
v___y_2582_ = v_b_2580_;
goto v___jp_2581_;
}
else
{
lean_object* v_val_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; 
v_val_2589_ = lean_ctor_get(v___x_2588_, 0);
lean_inc(v_val_2589_);
lean_dec_ref(v___x_2588_);
lean_inc(v___x_2587_);
v___x_2590_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2590_, 0, v___x_2587_);
lean_ctor_set(v___x_2590_, 1, v_val_2589_);
v___x_2591_ = lean_array_push(v_b_2580_, v___x_2590_);
v___y_2582_ = v___x_2591_;
goto v___jp_2581_;
}
}
else
{
return v_b_2580_;
}
v___jp_2581_:
{
size_t v___x_2583_; size_t v___x_2584_; 
v___x_2583_ = ((size_t)1ULL);
v___x_2584_ = lean_usize_add(v_i_2578_, v___x_2583_);
v_i_2578_ = v___x_2584_;
v_b_2580_ = v___y_2582_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3_spec__5___redArg___boxed(lean_object* v_snd_2592_, lean_object* v_as_2593_, lean_object* v_i_2594_, lean_object* v_stop_2595_, lean_object* v_b_2596_){
_start:
{
size_t v_i_boxed_2597_; size_t v_stop_boxed_2598_; lean_object* v_res_2599_; 
v_i_boxed_2597_ = lean_unbox_usize(v_i_2594_);
lean_dec(v_i_2594_);
v_stop_boxed_2598_ = lean_unbox_usize(v_stop_2595_);
lean_dec(v_stop_2595_);
v_res_2599_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3_spec__5___redArg(v_snd_2592_, v_as_2593_, v_i_boxed_2597_, v_stop_boxed_2598_, v_b_2596_);
lean_dec_ref(v_as_2593_);
lean_dec(v_snd_2592_);
return v_res_2599_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3___redArg(lean_object* v_snd_2600_, lean_object* v_as_2601_, lean_object* v_start_2602_, lean_object* v_stop_2603_){
_start:
{
lean_object* v___x_2604_; uint8_t v___x_2605_; 
v___x_2604_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___lam__2___closed__0));
v___x_2605_ = lean_nat_dec_lt(v_start_2602_, v_stop_2603_);
if (v___x_2605_ == 0)
{
return v___x_2604_;
}
else
{
lean_object* v___x_2606_; uint8_t v___x_2607_; 
v___x_2606_ = lean_array_get_size(v_as_2601_);
v___x_2607_ = lean_nat_dec_le(v_stop_2603_, v___x_2606_);
if (v___x_2607_ == 0)
{
uint8_t v___x_2608_; 
v___x_2608_ = lean_nat_dec_lt(v_start_2602_, v___x_2606_);
if (v___x_2608_ == 0)
{
return v___x_2604_;
}
else
{
size_t v___x_2609_; size_t v___x_2610_; lean_object* v___x_2611_; 
v___x_2609_ = lean_usize_of_nat(v_start_2602_);
v___x_2610_ = lean_usize_of_nat(v___x_2606_);
v___x_2611_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3_spec__5___redArg(v_snd_2600_, v_as_2601_, v___x_2609_, v___x_2610_, v___x_2604_);
return v___x_2611_;
}
}
else
{
size_t v___x_2612_; size_t v___x_2613_; lean_object* v___x_2614_; 
v___x_2612_ = lean_usize_of_nat(v_start_2602_);
v___x_2613_ = lean_usize_of_nat(v_stop_2603_);
v___x_2614_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3_spec__5___redArg(v_snd_2600_, v_as_2601_, v___x_2612_, v___x_2613_, v___x_2604_);
return v___x_2614_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3___redArg___boxed(lean_object* v_snd_2615_, lean_object* v_as_2616_, lean_object* v_start_2617_, lean_object* v_stop_2618_){
_start:
{
lean_object* v_res_2619_; 
v_res_2619_ = l_Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3___redArg(v_snd_2615_, v_as_2616_, v_start_2617_, v_stop_2618_);
lean_dec(v_stop_2618_);
lean_dec(v_start_2617_);
lean_dec_ref(v_as_2616_);
lean_dec(v_snd_2615_);
return v_res_2619_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttribute_spec__0___redArg(lean_object* v_impl_2620_, lean_object* v_env_2621_, lean_object* v_as_2622_, size_t v_i_2623_, size_t v_stop_2624_, lean_object* v_b_2625_){
_start:
{
lean_object* v___y_2627_; uint8_t v___x_2631_; 
v___x_2631_ = lean_usize_dec_eq(v_i_2623_, v_stop_2624_);
if (v___x_2631_ == 0)
{
lean_object* v___x_2632_; lean_object* v_fst_2633_; lean_object* v_snd_2634_; lean_object* v_filterExport_2635_; lean_object* v___x_2636_; uint8_t v___x_2637_; 
v___x_2632_ = lean_array_uget_borrowed(v_as_2622_, v_i_2623_);
v_fst_2633_ = lean_ctor_get(v___x_2632_, 0);
v_snd_2634_ = lean_ctor_get(v___x_2632_, 1);
v_filterExport_2635_ = lean_ctor_get(v_impl_2620_, 3);
lean_inc_ref(v_filterExport_2635_);
lean_inc(v_snd_2634_);
lean_inc(v_fst_2633_);
lean_inc_ref(v_env_2621_);
v___x_2636_ = lean_apply_3(v_filterExport_2635_, v_env_2621_, v_fst_2633_, v_snd_2634_);
v___x_2637_ = lean_unbox(v___x_2636_);
if (v___x_2637_ == 0)
{
v___y_2627_ = v_b_2625_;
goto v___jp_2626_;
}
else
{
lean_object* v___x_2638_; 
lean_inc(v___x_2632_);
v___x_2638_ = lean_array_push(v_b_2625_, v___x_2632_);
v___y_2627_ = v___x_2638_;
goto v___jp_2626_;
}
}
else
{
lean_dec_ref(v_env_2621_);
lean_dec_ref(v_impl_2620_);
return v_b_2625_;
}
v___jp_2626_:
{
size_t v___x_2628_; size_t v___x_2629_; 
v___x_2628_ = ((size_t)1ULL);
v___x_2629_ = lean_usize_add(v_i_2623_, v___x_2628_);
v_i_2623_ = v___x_2629_;
v_b_2625_ = v___y_2627_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttribute_spec__0___redArg___boxed(lean_object* v_impl_2639_, lean_object* v_env_2640_, lean_object* v_as_2641_, lean_object* v_i_2642_, lean_object* v_stop_2643_, lean_object* v_b_2644_){
_start:
{
size_t v_i_boxed_2645_; size_t v_stop_boxed_2646_; lean_object* v_res_2647_; 
v_i_boxed_2645_ = lean_unbox_usize(v_i_2642_);
lean_dec(v_i_2642_);
v_stop_boxed_2646_ = lean_unbox_usize(v_stop_2643_);
lean_dec(v_stop_2643_);
v_res_2647_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttribute_spec__0___redArg(v_impl_2639_, v_env_2640_, v_as_2641_, v_i_boxed_2645_, v_stop_boxed_2646_, v_b_2644_);
lean_dec_ref(v_as_2641_);
return v_res_2647_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___lam__1(lean_object* v_impl_2648_, uint8_t v_preserveOrder_2649_, lean_object* v_env_2650_, lean_object* v_x_2651_){
_start:
{
lean_object* v___y_2653_; 
if (v_preserveOrder_2649_ == 0)
{
lean_object* v_snd_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; lean_object* v_r_2672_; lean_object* v___x_2673_; lean_object* v___y_2675_; lean_object* v___y_2676_; uint8_t v___x_2678_; 
v_snd_2669_ = lean_ctor_get(v_x_2651_, 1);
lean_inc(v_snd_2669_);
lean_dec_ref(v_x_2651_);
v___x_2670_ = lean_unsigned_to_nat(0u);
v___x_2671_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___lam__2___closed__0));
v_r_2672_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1_spec__1___redArg(v___x_2671_, v_snd_2669_);
lean_dec(v_snd_2669_);
v___x_2673_ = lean_array_get_size(v_r_2672_);
v___x_2678_ = lean_nat_dec_eq(v___x_2673_, v___x_2670_);
if (v___x_2678_ == 0)
{
lean_object* v___x_2679_; lean_object* v___x_2680_; lean_object* v___y_2682_; uint8_t v___x_2684_; 
v___x_2679_ = lean_unsigned_to_nat(1u);
v___x_2680_ = lean_nat_sub(v___x_2673_, v___x_2679_);
v___x_2684_ = lean_nat_dec_le(v___x_2670_, v___x_2680_);
if (v___x_2684_ == 0)
{
lean_inc(v___x_2680_);
v___y_2682_ = v___x_2680_;
goto v___jp_2681_;
}
else
{
v___y_2682_ = v___x_2670_;
goto v___jp_2681_;
}
v___jp_2681_:
{
uint8_t v___x_2683_; 
v___x_2683_ = lean_nat_dec_le(v___y_2682_, v___x_2680_);
if (v___x_2683_ == 0)
{
lean_dec(v___x_2680_);
lean_inc(v___y_2682_);
v___y_2675_ = v___y_2682_;
v___y_2676_ = v___y_2682_;
goto v___jp_2674_;
}
else
{
v___y_2675_ = v___y_2682_;
v___y_2676_ = v___x_2680_;
goto v___jp_2674_;
}
}
}
else
{
v___y_2653_ = v_r_2672_;
goto v___jp_2652_;
}
v___jp_2674_:
{
lean_object* v___x_2677_; 
v___x_2677_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2___redArg(v___x_2673_, v_r_2672_, v___y_2675_, v___y_2676_);
lean_dec(v___y_2676_);
v___y_2653_ = v___x_2677_;
goto v___jp_2652_;
}
}
else
{
lean_object* v_fst_2685_; lean_object* v_snd_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; lean_object* v___x_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; 
v_fst_2685_ = lean_ctor_get(v_x_2651_, 0);
lean_inc(v_fst_2685_);
v_snd_2686_ = lean_ctor_get(v_x_2651_, 1);
lean_inc(v_snd_2686_);
lean_dec_ref(v_x_2651_);
v___x_2687_ = lean_array_mk(v_fst_2685_);
v___x_2688_ = l_Array_reverse___redArg(v___x_2687_);
v___x_2689_ = lean_unsigned_to_nat(0u);
v___x_2690_ = lean_array_get_size(v___x_2688_);
v___x_2691_ = l_Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3___redArg(v_snd_2686_, v___x_2688_, v___x_2689_, v___x_2690_);
lean_dec_ref(v___x_2688_);
lean_dec(v_snd_2686_);
v___y_2653_ = v___x_2691_;
goto v___jp_2652_;
}
v___jp_2652_:
{
lean_object* v___x_2654_; lean_object* v___x_2655_; lean_object* v___x_2656_; uint8_t v___x_2657_; 
v___x_2654_ = lean_unsigned_to_nat(0u);
v___x_2655_ = lean_array_get_size(v___y_2653_);
v___x_2656_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___lam__2___closed__0));
v___x_2657_ = lean_nat_dec_lt(v___x_2654_, v___x_2655_);
if (v___x_2657_ == 0)
{
lean_object* v___x_2658_; 
lean_dec_ref(v_env_2650_);
lean_dec_ref(v_impl_2648_);
v___x_2658_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2658_, 0, v___x_2656_);
lean_ctor_set(v___x_2658_, 1, v___x_2656_);
lean_ctor_set(v___x_2658_, 2, v___y_2653_);
return v___x_2658_;
}
else
{
uint8_t v___x_2659_; 
v___x_2659_ = lean_nat_dec_le(v___x_2655_, v___x_2655_);
if (v___x_2659_ == 0)
{
if (v___x_2657_ == 0)
{
lean_object* v___x_2660_; 
lean_dec_ref(v_env_2650_);
lean_dec_ref(v_impl_2648_);
v___x_2660_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2660_, 0, v___x_2656_);
lean_ctor_set(v___x_2660_, 1, v___x_2656_);
lean_ctor_set(v___x_2660_, 2, v___y_2653_);
return v___x_2660_;
}
else
{
size_t v___x_2661_; size_t v___x_2662_; lean_object* v___x_2663_; lean_object* v___x_2664_; 
v___x_2661_ = ((size_t)0ULL);
v___x_2662_ = lean_usize_of_nat(v___x_2655_);
v___x_2663_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttribute_spec__0___redArg(v_impl_2648_, v_env_2650_, v___y_2653_, v___x_2661_, v___x_2662_, v___x_2656_);
lean_inc_ref(v___x_2663_);
v___x_2664_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2664_, 0, v___x_2663_);
lean_ctor_set(v___x_2664_, 1, v___x_2663_);
lean_ctor_set(v___x_2664_, 2, v___y_2653_);
return v___x_2664_;
}
}
else
{
size_t v___x_2665_; size_t v___x_2666_; lean_object* v___x_2667_; lean_object* v___x_2668_; 
v___x_2665_ = ((size_t)0ULL);
v___x_2666_ = lean_usize_of_nat(v___x_2655_);
v___x_2667_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttribute_spec__0___redArg(v_impl_2648_, v_env_2650_, v___y_2653_, v___x_2665_, v___x_2666_, v___x_2656_);
lean_inc_ref(v___x_2667_);
v___x_2668_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2668_, 0, v___x_2667_);
lean_ctor_set(v___x_2668_, 1, v___x_2667_);
lean_ctor_set(v___x_2668_, 2, v___y_2653_);
return v___x_2668_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___lam__1___boxed(lean_object* v_impl_2692_, lean_object* v_preserveOrder_2693_, lean_object* v_env_2694_, lean_object* v_x_2695_){
_start:
{
uint8_t v_preserveOrder_boxed_2696_; lean_object* v_res_2697_; 
v_preserveOrder_boxed_2696_ = lean_unbox(v_preserveOrder_2693_);
v_res_2697_ = l_Lean_registerParametricAttribute___redArg___lam__1(v_impl_2692_, v_preserveOrder_boxed_2696_, v_env_2694_, v_x_2695_);
return v_res_2697_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___lam__2(lean_object* v_x_2707_){
_start:
{
lean_object* v_snd_2708_; lean_object* v___x_2710_; uint8_t v_isShared_2711_; uint8_t v_isSharedCheck_2722_; 
v_snd_2708_ = lean_ctor_get(v_x_2707_, 1);
v_isSharedCheck_2722_ = !lean_is_exclusive(v_x_2707_);
if (v_isSharedCheck_2722_ == 0)
{
lean_object* v_unused_2723_; 
v_unused_2723_ = lean_ctor_get(v_x_2707_, 0);
lean_dec(v_unused_2723_);
v___x_2710_ = v_x_2707_;
v_isShared_2711_ = v_isSharedCheck_2722_;
goto v_resetjp_2709_;
}
else
{
lean_inc(v_snd_2708_);
lean_dec(v_x_2707_);
v___x_2710_ = lean_box(0);
v_isShared_2711_ = v_isSharedCheck_2722_;
goto v_resetjp_2709_;
}
v_resetjp_2709_:
{
lean_object* v___x_2712_; lean_object* v___y_2714_; 
v___x_2712_ = ((lean_object*)(l_Lean_registerParametricAttribute___redArg___lam__2___closed__3));
if (lean_obj_tag(v_snd_2708_) == 0)
{
lean_object* v_size_2720_; 
v_size_2720_ = lean_ctor_get(v_snd_2708_, 0);
lean_inc(v_size_2720_);
lean_dec_ref(v_snd_2708_);
v___y_2714_ = v_size_2720_;
goto v___jp_2713_;
}
else
{
lean_object* v___x_2721_; 
v___x_2721_ = lean_unsigned_to_nat(0u);
v___y_2714_ = v___x_2721_;
goto v___jp_2713_;
}
v___jp_2713_:
{
lean_object* v___x_2715_; lean_object* v___x_2716_; lean_object* v___x_2718_; 
v___x_2715_ = l_Nat_reprFast(v___y_2714_);
v___x_2716_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2716_, 0, v___x_2715_);
if (v_isShared_2711_ == 0)
{
lean_ctor_set_tag(v___x_2710_, 5);
lean_ctor_set(v___x_2710_, 1, v___x_2716_);
lean_ctor_set(v___x_2710_, 0, v___x_2712_);
v___x_2718_ = v___x_2710_;
goto v_reusejp_2717_;
}
else
{
lean_object* v_reuseFailAlloc_2719_; 
v_reuseFailAlloc_2719_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2719_, 0, v___x_2712_);
lean_ctor_set(v_reuseFailAlloc_2719_, 1, v___x_2716_);
v___x_2718_ = v_reuseFailAlloc_2719_;
goto v_reusejp_2717_;
}
v_reusejp_2717_:
{
return v___x_2718_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___lam__3(lean_object* v_x_2724_){
_start:
{
lean_object* v___x_2725_; 
v___x_2725_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___lam__2___closed__0));
return v___x_2725_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___lam__3___boxed(lean_object* v_x_2726_){
_start:
{
lean_object* v_res_2727_; 
v_res_2727_ = l_Lean_registerParametricAttribute___redArg___lam__3(v_x_2726_);
lean_dec_ref(v_x_2726_);
return v_res_2727_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___lam__4(lean_object* v___x_2728_, lean_object* v_x_2729_, lean_object* v___y_2730_){
_start:
{
lean_object* v___x_2732_; 
v___x_2732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2732_, 0, v___x_2728_);
return v___x_2732_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___lam__4___boxed(lean_object* v___x_2733_, lean_object* v_x_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_){
_start:
{
lean_object* v_res_2737_; 
v_res_2737_ = l_Lean_registerParametricAttribute___redArg___lam__4(v___x_2733_, v_x_2734_, v___y_2735_);
lean_dec_ref(v___y_2735_);
lean_dec_ref(v_x_2734_);
return v_res_2737_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___lam__5(lean_object* v___x_2738_){
_start:
{
lean_object* v___x_2740_; 
v___x_2740_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2740_, 0, v___x_2738_);
return v___x_2740_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___lam__5___boxed(lean_object* v___x_2741_, lean_object* v___y_2742_){
_start:
{
lean_object* v_res_2743_; 
v_res_2743_ = l_Lean_registerParametricAttribute___redArg___lam__5(v___x_2741_);
return v_res_2743_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___lam__7(lean_object* v_getParam_2744_, lean_object* v_a_2745_, lean_object* v_afterSet_2746_, lean_object* v_name_2747_, lean_object* v_decl_2748_, lean_object* v_stx_2749_, uint8_t v_kind_2750_, lean_object* v___y_2751_, lean_object* v___y_2752_){
_start:
{
lean_object* v___y_2755_; lean_object* v___y_2756_; lean_object* v___y_2757_; lean_object* v___y_2758_; uint8_t v___y_2759_; lean_object* v___y_2762_; lean_object* v___y_2763_; lean_object* v___y_2764_; uint8_t v___x_2808_; uint8_t v___x_2809_; 
v___x_2808_ = 0;
v___x_2809_ = l_Lean_instBEqAttributeKind_beq(v_kind_2750_, v___x_2808_);
if (v___x_2809_ == 0)
{
lean_object* v___x_2810_; 
lean_dec(v_stx_2749_);
lean_dec(v_decl_2748_);
lean_dec_ref(v_afterSet_2746_);
lean_dec_ref(v_a_2745_);
lean_dec_ref(v_getParam_2744_);
v___x_2810_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg(v_name_2747_, v_kind_2750_, v___y_2751_, v___y_2752_);
return v___x_2810_;
}
else
{
goto v___jp_2803_;
}
v___jp_2754_:
{
if (v___y_2759_ == 0)
{
lean_object* v___x_2760_; 
lean_dec_ref(v___y_2758_);
v___x_2760_ = l_Lean_setEnv___at___00Lean_registerParametricAttribute_spec__4___redArg(v___y_2757_, v___y_2755_);
return v___x_2760_;
}
else
{
lean_dec_ref(v___y_2757_);
return v___y_2758_;
}
}
v___jp_2761_:
{
lean_object* v___x_2765_; 
lean_inc(v___y_2764_);
lean_inc_ref(v___y_2763_);
lean_inc(v_decl_2748_);
v___x_2765_ = lean_apply_5(v_getParam_2744_, v_decl_2748_, v_stx_2749_, v___y_2763_, v___y_2764_, lean_box(0));
if (lean_obj_tag(v___x_2765_) == 0)
{
lean_object* v_a_2766_; lean_object* v___x_2767_; lean_object* v_toEnvExtension_2768_; lean_object* v_env_2769_; lean_object* v_nextMacroScope_2770_; lean_object* v_ngen_2771_; lean_object* v_auxDeclNGen_2772_; lean_object* v_traceState_2773_; lean_object* v_messages_2774_; lean_object* v_infoState_2775_; lean_object* v_snapshotTasks_2776_; lean_object* v_newDecls_2777_; lean_object* v___x_2779_; uint8_t v_isShared_2780_; uint8_t v_isSharedCheck_2793_; 
v_a_2766_ = lean_ctor_get(v___x_2765_, 0);
lean_inc(v_a_2766_);
lean_dec_ref(v___x_2765_);
v___x_2767_ = lean_st_ref_take(v___y_2764_);
v_toEnvExtension_2768_ = lean_ctor_get(v_a_2745_, 0);
v_env_2769_ = lean_ctor_get(v___x_2767_, 0);
v_nextMacroScope_2770_ = lean_ctor_get(v___x_2767_, 1);
v_ngen_2771_ = lean_ctor_get(v___x_2767_, 2);
v_auxDeclNGen_2772_ = lean_ctor_get(v___x_2767_, 3);
v_traceState_2773_ = lean_ctor_get(v___x_2767_, 4);
v_messages_2774_ = lean_ctor_get(v___x_2767_, 6);
v_infoState_2775_ = lean_ctor_get(v___x_2767_, 7);
v_snapshotTasks_2776_ = lean_ctor_get(v___x_2767_, 8);
v_newDecls_2777_ = lean_ctor_get(v___x_2767_, 9);
v_isSharedCheck_2793_ = !lean_is_exclusive(v___x_2767_);
if (v_isSharedCheck_2793_ == 0)
{
lean_object* v_unused_2794_; 
v_unused_2794_ = lean_ctor_get(v___x_2767_, 5);
lean_dec(v_unused_2794_);
v___x_2779_ = v___x_2767_;
v_isShared_2780_ = v_isSharedCheck_2793_;
goto v_resetjp_2778_;
}
else
{
lean_inc(v_newDecls_2777_);
lean_inc(v_snapshotTasks_2776_);
lean_inc(v_infoState_2775_);
lean_inc(v_messages_2774_);
lean_inc(v_traceState_2773_);
lean_inc(v_auxDeclNGen_2772_);
lean_inc(v_ngen_2771_);
lean_inc(v_nextMacroScope_2770_);
lean_inc(v_env_2769_);
lean_dec(v___x_2767_);
v___x_2779_ = lean_box(0);
v_isShared_2780_ = v_isSharedCheck_2793_;
goto v_resetjp_2778_;
}
v_resetjp_2778_:
{
lean_object* v_asyncMode_2781_; lean_object* v___x_2782_; lean_object* v___x_2783_; lean_object* v___x_2784_; lean_object* v___x_2786_; 
v_asyncMode_2781_ = lean_ctor_get(v_toEnvExtension_2768_, 2);
lean_inc(v_asyncMode_2781_);
lean_inc(v_a_2766_);
lean_inc_n(v_decl_2748_, 2);
v___x_2782_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2782_, 0, v_decl_2748_);
lean_ctor_set(v___x_2782_, 1, v_a_2766_);
v___x_2783_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_a_2745_, v_env_2769_, v___x_2782_, v_asyncMode_2781_, v_decl_2748_);
lean_dec(v_asyncMode_2781_);
v___x_2784_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2);
if (v_isShared_2780_ == 0)
{
lean_ctor_set(v___x_2779_, 5, v___x_2784_);
lean_ctor_set(v___x_2779_, 0, v___x_2783_);
v___x_2786_ = v___x_2779_;
goto v_reusejp_2785_;
}
else
{
lean_object* v_reuseFailAlloc_2792_; 
v_reuseFailAlloc_2792_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2792_, 0, v___x_2783_);
lean_ctor_set(v_reuseFailAlloc_2792_, 1, v_nextMacroScope_2770_);
lean_ctor_set(v_reuseFailAlloc_2792_, 2, v_ngen_2771_);
lean_ctor_set(v_reuseFailAlloc_2792_, 3, v_auxDeclNGen_2772_);
lean_ctor_set(v_reuseFailAlloc_2792_, 4, v_traceState_2773_);
lean_ctor_set(v_reuseFailAlloc_2792_, 5, v___x_2784_);
lean_ctor_set(v_reuseFailAlloc_2792_, 6, v_messages_2774_);
lean_ctor_set(v_reuseFailAlloc_2792_, 7, v_infoState_2775_);
lean_ctor_set(v_reuseFailAlloc_2792_, 8, v_snapshotTasks_2776_);
lean_ctor_set(v_reuseFailAlloc_2792_, 9, v_newDecls_2777_);
v___x_2786_ = v_reuseFailAlloc_2792_;
goto v_reusejp_2785_;
}
v_reusejp_2785_:
{
lean_object* v___x_2787_; lean_object* v___x_2788_; 
v___x_2787_ = lean_st_ref_set(v___y_2764_, v___x_2786_);
lean_inc(v___y_2764_);
lean_inc_ref(v___y_2763_);
v___x_2788_ = lean_apply_5(v_afterSet_2746_, v_decl_2748_, v_a_2766_, v___y_2763_, v___y_2764_, lean_box(0));
if (lean_obj_tag(v___x_2788_) == 0)
{
lean_dec_ref(v___y_2762_);
return v___x_2788_;
}
else
{
lean_object* v_a_2789_; uint8_t v___x_2790_; 
v_a_2789_ = lean_ctor_get(v___x_2788_, 0);
lean_inc(v_a_2789_);
v___x_2790_ = l_Lean_Exception_isInterrupt(v_a_2789_);
if (v___x_2790_ == 0)
{
uint8_t v___x_2791_; 
v___x_2791_ = l_Lean_Exception_isRuntime(v_a_2789_);
v___y_2755_ = v___y_2764_;
v___y_2756_ = v___y_2763_;
v___y_2757_ = v___y_2762_;
v___y_2758_ = v___x_2788_;
v___y_2759_ = v___x_2791_;
goto v___jp_2754_;
}
else
{
lean_dec(v_a_2789_);
v___y_2755_ = v___y_2764_;
v___y_2756_ = v___y_2763_;
v___y_2757_ = v___y_2762_;
v___y_2758_ = v___x_2788_;
v___y_2759_ = v___x_2790_;
goto v___jp_2754_;
}
}
}
}
}
else
{
lean_object* v_a_2795_; lean_object* v___x_2797_; uint8_t v_isShared_2798_; uint8_t v_isSharedCheck_2802_; 
lean_dec_ref(v___y_2762_);
lean_dec(v_decl_2748_);
lean_dec_ref(v_afterSet_2746_);
lean_dec_ref(v_a_2745_);
v_a_2795_ = lean_ctor_get(v___x_2765_, 0);
v_isSharedCheck_2802_ = !lean_is_exclusive(v___x_2765_);
if (v_isSharedCheck_2802_ == 0)
{
v___x_2797_ = v___x_2765_;
v_isShared_2798_ = v_isSharedCheck_2802_;
goto v_resetjp_2796_;
}
else
{
lean_inc(v_a_2795_);
lean_dec(v___x_2765_);
v___x_2797_ = lean_box(0);
v_isShared_2798_ = v_isSharedCheck_2802_;
goto v_resetjp_2796_;
}
v_resetjp_2796_:
{
lean_object* v___x_2800_; 
if (v_isShared_2798_ == 0)
{
v___x_2800_ = v___x_2797_;
goto v_reusejp_2799_;
}
else
{
lean_object* v_reuseFailAlloc_2801_; 
v_reuseFailAlloc_2801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2801_, 0, v_a_2795_);
v___x_2800_ = v_reuseFailAlloc_2801_;
goto v_reusejp_2799_;
}
v_reusejp_2799_:
{
return v___x_2800_;
}
}
}
}
v___jp_2803_:
{
lean_object* v___x_2804_; lean_object* v_env_2805_; lean_object* v___x_2806_; 
v___x_2804_ = lean_st_ref_get(v___y_2752_);
v_env_2805_ = lean_ctor_get(v___x_2804_, 0);
lean_inc_ref(v_env_2805_);
lean_dec(v___x_2804_);
v___x_2806_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2805_, v_decl_2748_);
if (lean_obj_tag(v___x_2806_) == 0)
{
lean_dec(v_name_2747_);
v___y_2762_ = v_env_2805_;
v___y_2763_ = v___y_2751_;
v___y_2764_ = v___y_2752_;
goto v___jp_2761_;
}
else
{
lean_object* v___x_2807_; 
lean_dec_ref(v___x_2806_);
lean_dec_ref(v_env_2805_);
lean_dec(v_stx_2749_);
lean_dec_ref(v_afterSet_2746_);
lean_dec_ref(v_a_2745_);
lean_dec_ref(v_getParam_2744_);
v___x_2807_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg(v_name_2747_, v_decl_2748_, v___y_2751_, v___y_2752_);
return v___x_2807_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___lam__7___boxed(lean_object* v_getParam_2811_, lean_object* v_a_2812_, lean_object* v_afterSet_2813_, lean_object* v_name_2814_, lean_object* v_decl_2815_, lean_object* v_stx_2816_, lean_object* v_kind_2817_, lean_object* v___y_2818_, lean_object* v___y_2819_, lean_object* v___y_2820_){
_start:
{
uint8_t v_kind_boxed_2821_; lean_object* v_res_2822_; 
v_kind_boxed_2821_ = lean_unbox(v_kind_2817_);
v_res_2822_ = l_Lean_registerParametricAttribute___redArg___lam__7(v_getParam_2811_, v_a_2812_, v_afterSet_2813_, v_name_2814_, v_decl_2815_, v_stx_2816_, v_kind_boxed_2821_, v___y_2818_, v___y_2819_);
lean_dec(v___y_2819_);
lean_dec_ref(v___y_2818_);
return v_res_2822_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg(lean_object* v_impl_2833_){
_start:
{
lean_object* v_toAttributeImplCore_2835_; lean_object* v_getParam_2836_; lean_object* v_afterSet_2837_; uint8_t v_preserveOrder_2838_; lean_object* v_ref_2839_; lean_object* v_name_2840_; lean_object* v___f_2841_; lean_object* v___x_2842_; lean_object* v___f_2843_; lean_object* v___f_2844_; lean_object* v___f_2845_; lean_object* v___f_2846_; lean_object* v___f_2847_; lean_object* v___x_2848_; lean_object* v___x_2849_; lean_object* v___x_2850_; lean_object* v___x_2851_; lean_object* v___x_2852_; 
v_toAttributeImplCore_2835_ = lean_ctor_get(v_impl_2833_, 0);
lean_inc_ref(v_toAttributeImplCore_2835_);
v_getParam_2836_ = lean_ctor_get(v_impl_2833_, 1);
lean_inc_ref(v_getParam_2836_);
v_afterSet_2837_ = lean_ctor_get(v_impl_2833_, 2);
lean_inc_ref(v_afterSet_2837_);
v_preserveOrder_2838_ = lean_ctor_get_uint8(v_impl_2833_, sizeof(void*)*4);
v_ref_2839_ = lean_ctor_get(v_toAttributeImplCore_2835_, 0);
v_name_2840_ = lean_ctor_get(v_toAttributeImplCore_2835_, 1);
v___f_2841_ = ((lean_object*)(l_Lean_registerParametricAttribute___redArg___closed__0));
v___x_2842_ = lean_box(v_preserveOrder_2838_);
v___f_2843_ = lean_alloc_closure((void*)(l_Lean_registerParametricAttribute___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_2843_, 0, v_impl_2833_);
lean_closure_set(v___f_2843_, 1, v___x_2842_);
v___f_2844_ = ((lean_object*)(l_Lean_registerParametricAttribute___redArg___closed__1));
v___f_2845_ = ((lean_object*)(l_Lean_registerParametricAttribute___redArg___closed__2));
v___f_2846_ = ((lean_object*)(l_Lean_registerParametricAttribute___redArg___closed__4));
v___f_2847_ = ((lean_object*)(l_Lean_registerParametricAttribute___redArg___closed__5));
v___x_2848_ = lean_box(2);
v___x_2849_ = lean_box(0);
lean_inc(v_ref_2839_);
v___x_2850_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_2850_, 0, v_ref_2839_);
lean_ctor_set(v___x_2850_, 1, v___f_2847_);
lean_ctor_set(v___x_2850_, 2, v___f_2846_);
lean_ctor_set(v___x_2850_, 3, v___f_2841_);
lean_ctor_set(v___x_2850_, 4, v___f_2843_);
lean_ctor_set(v___x_2850_, 5, v___f_2844_);
lean_ctor_set(v___x_2850_, 6, v___x_2848_);
lean_ctor_set(v___x_2850_, 7, v___x_2849_);
v___x_2851_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2851_, 0, v___x_2850_);
lean_ctor_set(v___x_2851_, 1, v___f_2845_);
v___x_2852_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_2851_);
if (lean_obj_tag(v___x_2852_) == 0)
{
lean_object* v_a_2853_; lean_object* v___f_2854_; lean_object* v___f_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; 
v_a_2853_ = lean_ctor_get(v___x_2852_, 0);
lean_inc_n(v_a_2853_, 2);
lean_dec_ref(v___x_2852_);
lean_inc_n(v_name_2840_, 2);
v___f_2854_ = lean_alloc_closure((void*)(l_Lean_registerTagAttribute___lam__6___boxed), 5, 1);
lean_closure_set(v___f_2854_, 0, v_name_2840_);
v___f_2855_ = lean_alloc_closure((void*)(l_Lean_registerParametricAttribute___redArg___lam__7___boxed), 10, 4);
lean_closure_set(v___f_2855_, 0, v_getParam_2836_);
lean_closure_set(v___f_2855_, 1, v_a_2853_);
lean_closure_set(v___f_2855_, 2, v_afterSet_2837_);
lean_closure_set(v___f_2855_, 3, v_name_2840_);
v___x_2856_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2856_, 0, v_toAttributeImplCore_2835_);
lean_ctor_set(v___x_2856_, 1, v___f_2855_);
lean_ctor_set(v___x_2856_, 2, v___f_2854_);
lean_inc_ref(v___x_2856_);
v___x_2857_ = l_Lean_registerBuiltinAttribute(v___x_2856_);
if (lean_obj_tag(v___x_2857_) == 0)
{
lean_object* v___x_2859_; uint8_t v_isShared_2860_; uint8_t v_isSharedCheck_2865_; 
v_isSharedCheck_2865_ = !lean_is_exclusive(v___x_2857_);
if (v_isSharedCheck_2865_ == 0)
{
lean_object* v_unused_2866_; 
v_unused_2866_ = lean_ctor_get(v___x_2857_, 0);
lean_dec(v_unused_2866_);
v___x_2859_ = v___x_2857_;
v_isShared_2860_ = v_isSharedCheck_2865_;
goto v_resetjp_2858_;
}
else
{
lean_dec(v___x_2857_);
v___x_2859_ = lean_box(0);
v_isShared_2860_ = v_isSharedCheck_2865_;
goto v_resetjp_2858_;
}
v_resetjp_2858_:
{
lean_object* v___x_2861_; lean_object* v___x_2863_; 
v___x_2861_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2861_, 0, v___x_2856_);
lean_ctor_set(v___x_2861_, 1, v_a_2853_);
lean_ctor_set_uint8(v___x_2861_, sizeof(void*)*2, v_preserveOrder_2838_);
if (v_isShared_2860_ == 0)
{
lean_ctor_set(v___x_2859_, 0, v___x_2861_);
v___x_2863_ = v___x_2859_;
goto v_reusejp_2862_;
}
else
{
lean_object* v_reuseFailAlloc_2864_; 
v_reuseFailAlloc_2864_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2864_, 0, v___x_2861_);
v___x_2863_ = v_reuseFailAlloc_2864_;
goto v_reusejp_2862_;
}
v_reusejp_2862_:
{
return v___x_2863_;
}
}
}
else
{
lean_object* v_a_2867_; lean_object* v___x_2869_; uint8_t v_isShared_2870_; uint8_t v_isSharedCheck_2874_; 
lean_dec_ref(v___x_2856_);
lean_dec(v_a_2853_);
v_a_2867_ = lean_ctor_get(v___x_2857_, 0);
v_isSharedCheck_2874_ = !lean_is_exclusive(v___x_2857_);
if (v_isSharedCheck_2874_ == 0)
{
v___x_2869_ = v___x_2857_;
v_isShared_2870_ = v_isSharedCheck_2874_;
goto v_resetjp_2868_;
}
else
{
lean_inc(v_a_2867_);
lean_dec(v___x_2857_);
v___x_2869_ = lean_box(0);
v_isShared_2870_ = v_isSharedCheck_2874_;
goto v_resetjp_2868_;
}
v_resetjp_2868_:
{
lean_object* v___x_2872_; 
if (v_isShared_2870_ == 0)
{
v___x_2872_ = v___x_2869_;
goto v_reusejp_2871_;
}
else
{
lean_object* v_reuseFailAlloc_2873_; 
v_reuseFailAlloc_2873_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2873_, 0, v_a_2867_);
v___x_2872_ = v_reuseFailAlloc_2873_;
goto v_reusejp_2871_;
}
v_reusejp_2871_:
{
return v___x_2872_;
}
}
}
}
else
{
lean_object* v_a_2875_; lean_object* v___x_2877_; uint8_t v_isShared_2878_; uint8_t v_isSharedCheck_2882_; 
lean_dec_ref(v_afterSet_2837_);
lean_dec_ref(v_getParam_2836_);
lean_dec_ref(v_toAttributeImplCore_2835_);
v_a_2875_ = lean_ctor_get(v___x_2852_, 0);
v_isSharedCheck_2882_ = !lean_is_exclusive(v___x_2852_);
if (v_isSharedCheck_2882_ == 0)
{
v___x_2877_ = v___x_2852_;
v_isShared_2878_ = v_isSharedCheck_2882_;
goto v_resetjp_2876_;
}
else
{
lean_inc(v_a_2875_);
lean_dec(v___x_2852_);
v___x_2877_ = lean_box(0);
v_isShared_2878_ = v_isSharedCheck_2882_;
goto v_resetjp_2876_;
}
v_resetjp_2876_:
{
lean_object* v___x_2880_; 
if (v_isShared_2878_ == 0)
{
v___x_2880_ = v___x_2877_;
goto v_reusejp_2879_;
}
else
{
lean_object* v_reuseFailAlloc_2881_; 
v_reuseFailAlloc_2881_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2881_, 0, v_a_2875_);
v___x_2880_ = v_reuseFailAlloc_2881_;
goto v_reusejp_2879_;
}
v_reusejp_2879_:
{
return v___x_2880_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___boxed(lean_object* v_impl_2883_, lean_object* v_a_2884_){
_start:
{
lean_object* v_res_2885_; 
v_res_2885_ = l_Lean_registerParametricAttribute___redArg(v_impl_2883_);
return v_res_2885_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute(lean_object* v_00_u03b1_2886_, lean_object* v_impl_2887_){
_start:
{
lean_object* v___x_2889_; 
v___x_2889_ = l_Lean_registerParametricAttribute___redArg(v_impl_2887_);
return v___x_2889_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___boxed(lean_object* v_00_u03b1_2890_, lean_object* v_impl_2891_, lean_object* v_a_2892_){
_start:
{
lean_object* v_res_2893_; 
v_res_2893_ = l_Lean_registerParametricAttribute(v_00_u03b1_2890_, v_impl_2891_);
return v_res_2893_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttribute_spec__0(lean_object* v_00_u03b1_2894_, lean_object* v_impl_2895_, lean_object* v_env_2896_, lean_object* v_as_2897_, size_t v_i_2898_, size_t v_stop_2899_, lean_object* v_b_2900_){
_start:
{
lean_object* v___x_2901_; 
v___x_2901_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttribute_spec__0___redArg(v_impl_2895_, v_env_2896_, v_as_2897_, v_i_2898_, v_stop_2899_, v_b_2900_);
return v___x_2901_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttribute_spec__0___boxed(lean_object* v_00_u03b1_2902_, lean_object* v_impl_2903_, lean_object* v_env_2904_, lean_object* v_as_2905_, lean_object* v_i_2906_, lean_object* v_stop_2907_, lean_object* v_b_2908_){
_start:
{
size_t v_i_boxed_2909_; size_t v_stop_boxed_2910_; lean_object* v_res_2911_; 
v_i_boxed_2909_ = lean_unbox_usize(v_i_2906_);
lean_dec(v_i_2906_);
v_stop_boxed_2910_ = lean_unbox_usize(v_stop_2907_);
lean_dec(v_stop_2907_);
v_res_2911_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttribute_spec__0(v_00_u03b1_2902_, v_impl_2903_, v_env_2904_, v_as_2905_, v_i_boxed_2909_, v_stop_boxed_2910_, v_b_2908_);
lean_dec_ref(v_as_2905_);
return v_res_2911_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1___redArg(lean_object* v_init_2912_, lean_object* v_t_2913_){
_start:
{
lean_object* v___x_2914_; 
v___x_2914_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1_spec__1___redArg(v_init_2912_, v_t_2913_);
return v___x_2914_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1___redArg___boxed(lean_object* v_init_2915_, lean_object* v_t_2916_){
_start:
{
lean_object* v_res_2917_; 
v_res_2917_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1___redArg(v_init_2915_, v_t_2916_);
lean_dec(v_t_2916_);
return v_res_2917_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1(lean_object* v_00_u03b1_2918_, lean_object* v_init_2919_, lean_object* v_t_2920_){
_start:
{
lean_object* v___x_2921_; 
v___x_2921_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1_spec__1___redArg(v_init_2919_, v_t_2920_);
return v___x_2921_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1___boxed(lean_object* v_00_u03b1_2922_, lean_object* v_init_2923_, lean_object* v_t_2924_){
_start:
{
lean_object* v_res_2925_; 
v_res_2925_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1(v_00_u03b1_2922_, v_init_2923_, v_t_2924_);
lean_dec(v_t_2924_);
return v_res_2925_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2(lean_object* v_00_u03b1_2926_, lean_object* v_n_2927_, lean_object* v_as_2928_, lean_object* v_lo_2929_, lean_object* v_hi_2930_, lean_object* v_w_2931_, lean_object* v_hlo_2932_, lean_object* v_hhi_2933_){
_start:
{
lean_object* v___x_2934_; 
v___x_2934_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2___redArg(v_n_2927_, v_as_2928_, v_lo_2929_, v_hi_2930_);
return v___x_2934_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2___boxed(lean_object* v_00_u03b1_2935_, lean_object* v_n_2936_, lean_object* v_as_2937_, lean_object* v_lo_2938_, lean_object* v_hi_2939_, lean_object* v_w_2940_, lean_object* v_hlo_2941_, lean_object* v_hhi_2942_){
_start:
{
lean_object* v_res_2943_; 
v_res_2943_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2(v_00_u03b1_2935_, v_n_2936_, v_as_2937_, v_lo_2938_, v_hi_2939_, v_w_2940_, v_hlo_2941_, v_hhi_2942_);
lean_dec(v_hi_2939_);
lean_dec(v_n_2936_);
return v_res_2943_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3(lean_object* v_00_u03b1_2944_, lean_object* v_snd_2945_, lean_object* v_as_2946_, lean_object* v_start_2947_, lean_object* v_stop_2948_){
_start:
{
lean_object* v___x_2949_; 
v___x_2949_ = l_Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3___redArg(v_snd_2945_, v_as_2946_, v_start_2947_, v_stop_2948_);
return v___x_2949_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3___boxed(lean_object* v_00_u03b1_2950_, lean_object* v_snd_2951_, lean_object* v_as_2952_, lean_object* v_start_2953_, lean_object* v_stop_2954_){
_start:
{
lean_object* v_res_2955_; 
v_res_2955_ = l_Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3(v_00_u03b1_2950_, v_snd_2951_, v_as_2952_, v_start_2953_, v_stop_2954_);
lean_dec(v_stop_2954_);
lean_dec(v_start_2953_);
lean_dec_ref(v_as_2952_);
lean_dec(v_snd_2951_);
return v_res_2955_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1_spec__1(lean_object* v_00_u03b1_2956_, lean_object* v_init_2957_, lean_object* v_x_2958_){
_start:
{
lean_object* v___x_2959_; 
v___x_2959_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1_spec__1___redArg(v_init_2957_, v_x_2958_);
return v___x_2959_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1_spec__1___boxed(lean_object* v_00_u03b1_2960_, lean_object* v_init_2961_, lean_object* v_x_2962_){
_start:
{
lean_object* v_res_2963_; 
v_res_2963_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1_spec__1(v_00_u03b1_2960_, v_init_2961_, v_x_2962_);
lean_dec(v_x_2962_);
return v_res_2963_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2_spec__3(lean_object* v_00_u03b1_2964_, lean_object* v_n_2965_, lean_object* v_lo_2966_, lean_object* v_hi_2967_, lean_object* v_hhi_2968_, lean_object* v_pivot_2969_, lean_object* v_as_2970_, lean_object* v_i_2971_, lean_object* v_k_2972_, lean_object* v_ilo_2973_, lean_object* v_ik_2974_, lean_object* v_w_2975_){
_start:
{
lean_object* v___x_2976_; 
v___x_2976_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2_spec__3___redArg(v_hi_2967_, v_pivot_2969_, v_as_2970_, v_i_2971_, v_k_2972_);
return v___x_2976_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2_spec__3___boxed(lean_object* v_00_u03b1_2977_, lean_object* v_n_2978_, lean_object* v_lo_2979_, lean_object* v_hi_2980_, lean_object* v_hhi_2981_, lean_object* v_pivot_2982_, lean_object* v_as_2983_, lean_object* v_i_2984_, lean_object* v_k_2985_, lean_object* v_ilo_2986_, lean_object* v_ik_2987_, lean_object* v_w_2988_){
_start:
{
lean_object* v_res_2989_; 
v_res_2989_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2_spec__3(v_00_u03b1_2977_, v_n_2978_, v_lo_2979_, v_hi_2980_, v_hhi_2981_, v_pivot_2982_, v_as_2983_, v_i_2984_, v_k_2985_, v_ilo_2986_, v_ik_2987_, v_w_2988_);
lean_dec_ref(v_pivot_2982_);
lean_dec(v_hi_2980_);
lean_dec(v_lo_2979_);
lean_dec(v_n_2978_);
return v_res_2989_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3_spec__5(lean_object* v_00_u03b1_2990_, lean_object* v_snd_2991_, lean_object* v_as_2992_, size_t v_i_2993_, size_t v_stop_2994_, lean_object* v_b_2995_){
_start:
{
lean_object* v___x_2996_; 
v___x_2996_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3_spec__5___redArg(v_snd_2991_, v_as_2992_, v_i_2993_, v_stop_2994_, v_b_2995_);
return v___x_2996_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3_spec__5___boxed(lean_object* v_00_u03b1_2997_, lean_object* v_snd_2998_, lean_object* v_as_2999_, lean_object* v_i_3000_, lean_object* v_stop_3001_, lean_object* v_b_3002_){
_start:
{
size_t v_i_boxed_3003_; size_t v_stop_boxed_3004_; lean_object* v_res_3005_; 
v_i_boxed_3003_ = lean_unbox_usize(v_i_3000_);
lean_dec(v_i_3000_);
v_stop_boxed_3004_ = lean_unbox_usize(v_stop_3001_);
lean_dec(v_stop_3001_);
v_res_3005_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3_spec__5(v_00_u03b1_2997_, v_snd_2998_, v_as_2999_, v_i_boxed_3003_, v_stop_boxed_3004_, v_b_3002_);
lean_dec_ref(v_as_2999_);
lean_dec(v_snd_2998_);
return v_res_3005_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParam_x3f___redArg___lam__1(lean_object* v_decl_3006_, lean_object* v___x_3007_, lean_object* v___x_3008_, lean_object* v_a_3009_, lean_object* v_x_3010_, lean_object* v___y_3011_){
_start:
{
lean_object* v_fst_3012_; uint8_t v___x_3013_; 
v_fst_3012_ = lean_ctor_get(v_a_3009_, 0);
v___x_3013_ = lean_name_eq(v_fst_3012_, v_decl_3006_);
if (v___x_3013_ == 0)
{
lean_object* v___x_3014_; 
lean_dec_ref(v_a_3009_);
v___x_3014_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3014_, 0, v___x_3007_);
return v___x_3014_;
}
else
{
lean_object* v___x_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; lean_object* v___x_3018_; 
lean_dec_ref(v___x_3007_);
v___x_3015_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3015_, 0, v_a_3009_);
v___x_3016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3016_, 0, v___x_3015_);
v___x_3017_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3017_, 0, v___x_3016_);
lean_ctor_set(v___x_3017_, 1, v___x_3008_);
v___x_3018_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3018_, 0, v___x_3017_);
return v___x_3018_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParam_x3f___redArg___lam__1___boxed(lean_object* v_decl_3019_, lean_object* v___x_3020_, lean_object* v___x_3021_, lean_object* v_a_3022_, lean_object* v_x_3023_, lean_object* v___y_3024_){
_start:
{
lean_object* v_res_3025_; 
v_res_3025_ = l_Lean_ParametricAttribute_getParam_x3f___redArg___lam__1(v_decl_3019_, v___x_3020_, v___x_3021_, v_a_3022_, v_x_3023_, v___y_3024_);
lean_dec_ref(v___y_3024_);
lean_dec(v_decl_3019_);
return v_res_3025_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParam_x3f___redArg(lean_object* v_inst_3053_, lean_object* v_attr_3054_, lean_object* v_env_3055_, lean_object* v_decl_3056_){
_start:
{
lean_object* v___y_3058_; lean_object* v___x_3069_; lean_object* v___x_3070_; 
v___x_3069_ = ((lean_object*)(l_Lean_ParametricAttribute_getParam_x3f___redArg___closed__0));
v___x_3070_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3055_, v_decl_3056_);
if (lean_obj_tag(v___x_3070_) == 0)
{
lean_object* v_ext_3071_; lean_object* v_toEnvExtension_3072_; lean_object* v_asyncMode_3073_; lean_object* v___x_3074_; lean_object* v___x_3075_; lean_object* v_snd_3076_; lean_object* v___x_3077_; 
lean_dec(v_inst_3053_);
v_ext_3071_ = lean_ctor_get(v_attr_3054_, 1);
v_toEnvExtension_3072_ = lean_ctor_get(v_ext_3071_, 0);
v_asyncMode_3073_ = lean_ctor_get(v_toEnvExtension_3072_, 2);
v___x_3074_ = lean_box(0);
v___x_3075_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3069_, v_ext_3071_, v_env_3055_, v_asyncMode_3073_, v___x_3074_);
v_snd_3076_ = lean_ctor_get(v___x_3075_, 1);
lean_inc(v_snd_3076_);
lean_dec(v___x_3075_);
v___x_3077_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_snd_3076_, v_decl_3056_);
lean_dec(v_decl_3056_);
lean_dec(v_snd_3076_);
return v___x_3077_;
}
else
{
uint8_t v_preserveOrder_3078_; 
v_preserveOrder_3078_ = lean_ctor_get_uint8(v_attr_3054_, sizeof(void*)*2);
if (v_preserveOrder_3078_ == 0)
{
lean_object* v_val_3079_; lean_object* v_ext_3080_; uint8_t v___x_3081_; lean_object* v___x_3082_; lean_object* v___x_3083_; lean_object* v___x_3084_; uint8_t v___x_3085_; 
v_val_3079_ = lean_ctor_get(v___x_3070_, 0);
lean_inc(v_val_3079_);
lean_dec_ref(v___x_3070_);
v_ext_3080_ = lean_ctor_get(v_attr_3054_, 1);
v___x_3081_ = 0;
v___x_3082_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_3069_, v_ext_3080_, v_env_3055_, v_val_3079_, v___x_3081_);
lean_dec(v_val_3079_);
lean_dec_ref(v_env_3055_);
v___x_3083_ = lean_unsigned_to_nat(0u);
v___x_3084_ = lean_array_get_size(v___x_3082_);
v___x_3085_ = lean_nat_dec_lt(v___x_3083_, v___x_3084_);
if (v___x_3085_ == 0)
{
lean_object* v___x_3086_; 
lean_dec_ref(v___x_3082_);
lean_dec(v_decl_3056_);
lean_dec(v_inst_3053_);
v___x_3086_ = lean_box(0);
return v___x_3086_;
}
else
{
lean_object* v___x_3087_; lean_object* v___x_3088_; uint8_t v___x_3089_; 
v___x_3087_ = lean_unsigned_to_nat(1u);
v___x_3088_ = lean_nat_sub(v___x_3084_, v___x_3087_);
v___x_3089_ = lean_nat_dec_le(v___x_3083_, v___x_3088_);
if (v___x_3089_ == 0)
{
lean_object* v___x_3090_; 
lean_dec(v___x_3088_);
lean_dec_ref(v___x_3082_);
lean_dec(v_decl_3056_);
lean_dec(v_inst_3053_);
v___x_3090_ = lean_box(0);
return v___x_3090_;
}
else
{
lean_object* v___f_3091_; lean_object* v___x_3092_; lean_object* v___x_3093_; lean_object* v___x_3094_; 
v___f_3091_ = ((lean_object*)(l_Lean_ParametricAttribute_getParam_x3f___redArg___closed__1));
v___x_3092_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3092_, 0, v_decl_3056_);
lean_ctor_set(v___x_3092_, 1, v_inst_3053_);
v___x_3093_ = ((lean_object*)(l_Lean_ParametricAttribute_getParam_x3f___redArg___closed__2));
v___x_3094_ = l_Array_binSearchAux___redArg(v___f_3091_, v___x_3093_, v___x_3082_, v___x_3092_, v___x_3083_, v___x_3088_);
lean_dec_ref(v___x_3082_);
v___y_3058_ = v___x_3094_;
goto v___jp_3057_;
}
}
}
else
{
lean_object* v_val_3095_; lean_object* v_ext_3096_; uint8_t v___x_3097_; lean_object* v___x_3098_; lean_object* v___x_3099_; lean_object* v___x_3100_; lean_object* v___x_3101_; lean_object* v___x_3102_; lean_object* v___f_3103_; size_t v_sz_3104_; size_t v___x_3105_; lean_object* v___x_3106_; lean_object* v_fst_3107_; 
lean_dec(v_inst_3053_);
v_val_3095_ = lean_ctor_get(v___x_3070_, 0);
lean_inc(v_val_3095_);
lean_dec_ref(v___x_3070_);
v_ext_3096_ = lean_ctor_get(v_attr_3054_, 1);
v___x_3097_ = 0;
v___x_3098_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_3069_, v_ext_3096_, v_env_3055_, v_val_3095_, v___x_3097_);
lean_dec(v_val_3095_);
lean_dec_ref(v_env_3055_);
v___x_3099_ = ((lean_object*)(l_Lean_ParametricAttribute_getParam_x3f___redArg___closed__12));
v___x_3100_ = lean_box(0);
v___x_3101_ = lean_box(0);
v___x_3102_ = ((lean_object*)(l_Lean_ParametricAttribute_getParam_x3f___redArg___closed__13));
v___f_3103_ = lean_alloc_closure((void*)(l_Lean_ParametricAttribute_getParam_x3f___redArg___lam__1___boxed), 6, 3);
lean_closure_set(v___f_3103_, 0, v_decl_3056_);
lean_closure_set(v___f_3103_, 1, v___x_3102_);
lean_closure_set(v___f_3103_, 2, v___x_3101_);
v_sz_3104_ = lean_array_size(v___x_3098_);
v___x_3105_ = ((size_t)0ULL);
v___x_3106_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_3099_, v___x_3098_, v___f_3103_, v_sz_3104_, v___x_3105_, v___x_3102_);
v_fst_3107_ = lean_ctor_get(v___x_3106_, 0);
lean_inc(v_fst_3107_);
lean_dec(v___x_3106_);
if (lean_obj_tag(v_fst_3107_) == 0)
{
return v___x_3100_;
}
else
{
lean_object* v_val_3108_; 
v_val_3108_ = lean_ctor_get(v_fst_3107_, 0);
lean_inc(v_val_3108_);
lean_dec_ref(v_fst_3107_);
v___y_3058_ = v_val_3108_;
goto v___jp_3057_;
}
}
}
v___jp_3057_:
{
if (lean_obj_tag(v___y_3058_) == 0)
{
lean_object* v___x_3059_; 
v___x_3059_ = lean_box(0);
return v___x_3059_;
}
else
{
lean_object* v_val_3060_; lean_object* v___x_3062_; uint8_t v_isShared_3063_; uint8_t v_isSharedCheck_3068_; 
v_val_3060_ = lean_ctor_get(v___y_3058_, 0);
v_isSharedCheck_3068_ = !lean_is_exclusive(v___y_3058_);
if (v_isSharedCheck_3068_ == 0)
{
v___x_3062_ = v___y_3058_;
v_isShared_3063_ = v_isSharedCheck_3068_;
goto v_resetjp_3061_;
}
else
{
lean_inc(v_val_3060_);
lean_dec(v___y_3058_);
v___x_3062_ = lean_box(0);
v_isShared_3063_ = v_isSharedCheck_3068_;
goto v_resetjp_3061_;
}
v_resetjp_3061_:
{
lean_object* v_snd_3064_; lean_object* v___x_3066_; 
v_snd_3064_ = lean_ctor_get(v_val_3060_, 1);
lean_inc(v_snd_3064_);
lean_dec(v_val_3060_);
if (v_isShared_3063_ == 0)
{
lean_ctor_set(v___x_3062_, 0, v_snd_3064_);
v___x_3066_ = v___x_3062_;
goto v_reusejp_3065_;
}
else
{
lean_object* v_reuseFailAlloc_3067_; 
v_reuseFailAlloc_3067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3067_, 0, v_snd_3064_);
v___x_3066_ = v_reuseFailAlloc_3067_;
goto v_reusejp_3065_;
}
v_reusejp_3065_:
{
return v___x_3066_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParam_x3f___redArg___boxed(lean_object* v_inst_3109_, lean_object* v_attr_3110_, lean_object* v_env_3111_, lean_object* v_decl_3112_){
_start:
{
lean_object* v_res_3113_; 
v_res_3113_ = l_Lean_ParametricAttribute_getParam_x3f___redArg(v_inst_3109_, v_attr_3110_, v_env_3111_, v_decl_3112_);
lean_dec_ref(v_attr_3110_);
return v_res_3113_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParam_x3f(lean_object* v_00_u03b1_3114_, lean_object* v_inst_3115_, lean_object* v_attr_3116_, lean_object* v_env_3117_, lean_object* v_decl_3118_){
_start:
{
lean_object* v___x_3119_; 
v___x_3119_ = l_Lean_ParametricAttribute_getParam_x3f___redArg(v_inst_3115_, v_attr_3116_, v_env_3117_, v_decl_3118_);
return v___x_3119_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParam_x3f___boxed(lean_object* v_00_u03b1_3120_, lean_object* v_inst_3121_, lean_object* v_attr_3122_, lean_object* v_env_3123_, lean_object* v_decl_3124_){
_start:
{
lean_object* v_res_3125_; 
v_res_3125_ = l_Lean_ParametricAttribute_getParam_x3f(v_00_u03b1_3120_, v_inst_3121_, v_attr_3122_, v_env_3123_, v_decl_3124_);
lean_dec_ref(v_attr_3122_);
return v_res_3125_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_setParam___redArg(lean_object* v_attr_3130_, lean_object* v_env_3131_, lean_object* v_decl_3132_, lean_object* v_param_3133_){
_start:
{
lean_object* v___x_3134_; 
v___x_3134_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3131_, v_decl_3132_);
if (lean_obj_tag(v___x_3134_) == 0)
{
lean_object* v_ext_3135_; lean_object* v_toEnvExtension_3136_; lean_object* v_attr_3137_; lean_object* v_asyncMode_3138_; lean_object* v___x_3139_; lean_object* v___x_3140_; lean_object* v___x_3141_; lean_object* v_snd_3142_; lean_object* v___x_3144_; uint8_t v_isShared_3145_; uint8_t v_isSharedCheck_3172_; 
v_ext_3135_ = lean_ctor_get(v_attr_3130_, 1);
lean_inc_ref(v_ext_3135_);
v_toEnvExtension_3136_ = lean_ctor_get(v_ext_3135_, 0);
v_attr_3137_ = lean_ctor_get(v_attr_3130_, 0);
lean_inc_ref(v_attr_3137_);
lean_dec_ref(v_attr_3130_);
v_asyncMode_3138_ = lean_ctor_get(v_toEnvExtension_3136_, 2);
lean_inc(v_asyncMode_3138_);
v___x_3139_ = ((lean_object*)(l_Lean_ParametricAttribute_getParam_x3f___redArg___closed__0));
v___x_3140_ = lean_box(0);
lean_inc_ref(v_env_3131_);
v___x_3141_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3139_, v_ext_3135_, v_env_3131_, v_asyncMode_3138_, v___x_3140_);
v_snd_3142_ = lean_ctor_get(v___x_3141_, 1);
v_isSharedCheck_3172_ = !lean_is_exclusive(v___x_3141_);
if (v_isSharedCheck_3172_ == 0)
{
lean_object* v_unused_3173_; 
v_unused_3173_ = lean_ctor_get(v___x_3141_, 0);
lean_dec(v_unused_3173_);
v___x_3144_ = v___x_3141_;
v_isShared_3145_ = v_isSharedCheck_3172_;
goto v_resetjp_3143_;
}
else
{
lean_inc(v_snd_3142_);
lean_dec(v___x_3141_);
v___x_3144_ = lean_box(0);
v_isShared_3145_ = v_isSharedCheck_3172_;
goto v_resetjp_3143_;
}
v_resetjp_3143_:
{
lean_object* v___x_3146_; 
v___x_3146_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_snd_3142_, v_decl_3132_);
lean_dec(v_snd_3142_);
if (lean_obj_tag(v___x_3146_) == 0)
{
lean_object* v___x_3148_; 
lean_dec_ref(v_attr_3137_);
if (v_isShared_3145_ == 0)
{
lean_ctor_set(v___x_3144_, 1, v_param_3133_);
lean_ctor_set(v___x_3144_, 0, v_decl_3132_);
v___x_3148_ = v___x_3144_;
goto v_reusejp_3147_;
}
else
{
lean_object* v_reuseFailAlloc_3151_; 
v_reuseFailAlloc_3151_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3151_, 0, v_decl_3132_);
lean_ctor_set(v_reuseFailAlloc_3151_, 1, v_param_3133_);
v___x_3148_ = v_reuseFailAlloc_3151_;
goto v_reusejp_3147_;
}
v_reusejp_3147_:
{
lean_object* v___x_3149_; lean_object* v___x_3150_; 
v___x_3149_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_ext_3135_, v_env_3131_, v___x_3148_, v_asyncMode_3138_, v___x_3140_);
lean_dec(v_asyncMode_3138_);
v___x_3150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3150_, 0, v___x_3149_);
return v___x_3150_;
}
}
else
{
lean_object* v___x_3153_; uint8_t v_isShared_3154_; uint8_t v_isSharedCheck_3170_; 
lean_del_object(v___x_3144_);
lean_dec(v_asyncMode_3138_);
lean_dec_ref(v_ext_3135_);
lean_dec(v_param_3133_);
lean_dec_ref(v_env_3131_);
v_isSharedCheck_3170_ = !lean_is_exclusive(v___x_3146_);
if (v_isSharedCheck_3170_ == 0)
{
lean_object* v_unused_3171_; 
v_unused_3171_ = lean_ctor_get(v___x_3146_, 0);
lean_dec(v_unused_3171_);
v___x_3153_ = v___x_3146_;
v_isShared_3154_ = v_isSharedCheck_3170_;
goto v_resetjp_3152_;
}
else
{
lean_dec(v___x_3146_);
v___x_3153_ = lean_box(0);
v_isShared_3154_ = v_isSharedCheck_3170_;
goto v_resetjp_3152_;
}
v_resetjp_3152_:
{
lean_object* v_toAttributeImplCore_3155_; lean_object* v_name_3156_; uint8_t v___x_3157_; lean_object* v___x_3158_; lean_object* v___x_3159_; lean_object* v___x_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; lean_object* v___x_3163_; lean_object* v___x_3164_; lean_object* v___x_3165_; lean_object* v___x_3166_; lean_object* v___x_3168_; 
v_toAttributeImplCore_3155_ = lean_ctor_get(v_attr_3137_, 0);
lean_inc_ref(v_toAttributeImplCore_3155_);
lean_dec_ref(v_attr_3137_);
v_name_3156_ = lean_ctor_get(v_toAttributeImplCore_3155_, 1);
lean_inc(v_name_3156_);
lean_dec_ref(v_toAttributeImplCore_3155_);
v___x_3157_ = 1;
v___x_3158_ = ((lean_object*)(l_Lean_ParametricAttribute_setParam___redArg___closed__0));
v___x_3159_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_3156_, v___x_3157_);
v___x_3160_ = lean_string_append(v___x_3158_, v___x_3159_);
lean_dec_ref(v___x_3159_);
v___x_3161_ = ((lean_object*)(l_Lean_ParametricAttribute_setParam___redArg___closed__1));
v___x_3162_ = lean_string_append(v___x_3160_, v___x_3161_);
v___x_3163_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_decl_3132_, v___x_3157_);
v___x_3164_ = lean_string_append(v___x_3162_, v___x_3163_);
lean_dec_ref(v___x_3163_);
v___x_3165_ = ((lean_object*)(l_Lean_ParametricAttribute_setParam___redArg___closed__2));
v___x_3166_ = lean_string_append(v___x_3164_, v___x_3165_);
if (v_isShared_3154_ == 0)
{
lean_ctor_set_tag(v___x_3153_, 0);
lean_ctor_set(v___x_3153_, 0, v___x_3166_);
v___x_3168_ = v___x_3153_;
goto v_reusejp_3167_;
}
else
{
lean_object* v_reuseFailAlloc_3169_; 
v_reuseFailAlloc_3169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3169_, 0, v___x_3166_);
v___x_3168_ = v_reuseFailAlloc_3169_;
goto v_reusejp_3167_;
}
v_reusejp_3167_:
{
return v___x_3168_;
}
}
}
}
}
else
{
lean_object* v___x_3175_; uint8_t v_isShared_3176_; uint8_t v_isSharedCheck_3193_; 
lean_dec(v_param_3133_);
lean_dec_ref(v_env_3131_);
v_isSharedCheck_3193_ = !lean_is_exclusive(v___x_3134_);
if (v_isSharedCheck_3193_ == 0)
{
lean_object* v_unused_3194_; 
v_unused_3194_ = lean_ctor_get(v___x_3134_, 0);
lean_dec(v_unused_3194_);
v___x_3175_ = v___x_3134_;
v_isShared_3176_ = v_isSharedCheck_3193_;
goto v_resetjp_3174_;
}
else
{
lean_dec(v___x_3134_);
v___x_3175_ = lean_box(0);
v_isShared_3176_ = v_isSharedCheck_3193_;
goto v_resetjp_3174_;
}
v_resetjp_3174_:
{
lean_object* v_attr_3177_; lean_object* v_toAttributeImplCore_3178_; lean_object* v_name_3179_; uint8_t v___x_3180_; lean_object* v___x_3181_; lean_object* v___x_3182_; lean_object* v___x_3183_; lean_object* v___x_3184_; lean_object* v___x_3185_; lean_object* v___x_3186_; lean_object* v___x_3187_; lean_object* v___x_3188_; lean_object* v___x_3189_; lean_object* v___x_3191_; 
v_attr_3177_ = lean_ctor_get(v_attr_3130_, 0);
lean_inc_ref(v_attr_3177_);
lean_dec_ref(v_attr_3130_);
v_toAttributeImplCore_3178_ = lean_ctor_get(v_attr_3177_, 0);
lean_inc_ref(v_toAttributeImplCore_3178_);
lean_dec_ref(v_attr_3177_);
v_name_3179_ = lean_ctor_get(v_toAttributeImplCore_3178_, 1);
lean_inc(v_name_3179_);
lean_dec_ref(v_toAttributeImplCore_3178_);
v___x_3180_ = 1;
v___x_3181_ = ((lean_object*)(l_Lean_ParametricAttribute_setParam___redArg___closed__0));
v___x_3182_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_3179_, v___x_3180_);
v___x_3183_ = lean_string_append(v___x_3181_, v___x_3182_);
lean_dec_ref(v___x_3182_);
v___x_3184_ = ((lean_object*)(l_Lean_ParametricAttribute_setParam___redArg___closed__1));
v___x_3185_ = lean_string_append(v___x_3183_, v___x_3184_);
v___x_3186_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_decl_3132_, v___x_3180_);
v___x_3187_ = lean_string_append(v___x_3185_, v___x_3186_);
lean_dec_ref(v___x_3186_);
v___x_3188_ = ((lean_object*)(l_Lean_ParametricAttribute_setParam___redArg___closed__3));
v___x_3189_ = lean_string_append(v___x_3187_, v___x_3188_);
if (v_isShared_3176_ == 0)
{
lean_ctor_set_tag(v___x_3175_, 0);
lean_ctor_set(v___x_3175_, 0, v___x_3189_);
v___x_3191_ = v___x_3175_;
goto v_reusejp_3190_;
}
else
{
lean_object* v_reuseFailAlloc_3192_; 
v_reuseFailAlloc_3192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3192_, 0, v___x_3189_);
v___x_3191_ = v_reuseFailAlloc_3192_;
goto v_reusejp_3190_;
}
v_reusejp_3190_:
{
return v___x_3191_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_setParam(lean_object* v_00_u03b1_3195_, lean_object* v_attr_3196_, lean_object* v_env_3197_, lean_object* v_decl_3198_, lean_object* v_param_3199_){
_start:
{
lean_object* v___x_3200_; 
v___x_3200_ = l_Lean_ParametricAttribute_setParam___redArg(v_attr_3196_, v_env_3197_, v_decl_3198_, v_param_3199_);
return v___x_3200_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___lam__0(lean_object* v_x_3201_, lean_object* v___y_3202_){
_start:
{
lean_object* v___x_3204_; lean_object* v___x_3205_; 
v___x_3204_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___lam__0___closed__1));
v___x_3205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3205_, 0, v___x_3204_);
return v___x_3205_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___lam__0___boxed(lean_object* v_x_3206_, lean_object* v___y_3207_, lean_object* v___y_3208_){
_start:
{
lean_object* v_res_3209_; 
v_res_3209_ = l_Lean_instInhabitedEnumAttributes_default___lam__0(v_x_3206_, v___y_3207_);
lean_dec_ref(v___y_3207_);
lean_dec_ref(v_x_3206_);
return v_res_3209_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___lam__1(lean_object* v_s_3210_, lean_object* v_x_3211_){
_start:
{
lean_inc(v_s_3210_);
return v_s_3210_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___lam__1___boxed(lean_object* v_s_3212_, lean_object* v_x_3213_){
_start:
{
lean_object* v_res_3214_; 
v_res_3214_ = l_Lean_instInhabitedEnumAttributes_default___lam__1(v_s_3212_, v_x_3213_);
lean_dec_ref(v_x_3213_);
lean_dec(v_s_3212_);
return v_res_3214_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___lam__2(lean_object* v_x_3215_, lean_object* v_x_3216_){
_start:
{
lean_object* v___x_3217_; 
v___x_3217_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___lam__2___closed__1));
return v___x_3217_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___lam__2___boxed(lean_object* v_x_3218_, lean_object* v_x_3219_){
_start:
{
lean_object* v_res_3220_; 
v_res_3220_ = l_Lean_instInhabitedEnumAttributes_default___lam__2(v_x_3218_, v_x_3219_);
lean_dec(v_x_3219_);
lean_dec_ref(v_x_3218_);
return v_res_3220_;
}
}
static lean_object* _init_l_Lean_instInhabitedEnumAttributes_default___closed__3(void){
_start:
{
lean_object* v___x_3224_; 
v___x_3224_ = l_Lean_instInhabitedEnvExtension_default(lean_box(0));
return v___x_3224_;
}
}
static lean_object* _init_l_Lean_instInhabitedEnumAttributes_default___closed__4(void){
_start:
{
lean_object* v___f_3225_; lean_object* v___f_3226_; lean_object* v___f_3227_; lean_object* v___f_3228_; lean_object* v___x_3229_; lean_object* v___x_3230_; lean_object* v___x_3231_; 
v___f_3225_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___closed__3));
v___f_3226_ = ((lean_object*)(l_Lean_instInhabitedEnumAttributes_default___closed__2));
v___f_3227_ = ((lean_object*)(l_Lean_instInhabitedEnumAttributes_default___closed__1));
v___f_3228_ = ((lean_object*)(l_Lean_instInhabitedEnumAttributes_default___closed__0));
v___x_3229_ = lean_box(0);
v___x_3230_ = lean_obj_once(&l_Lean_instInhabitedEnumAttributes_default___closed__3, &l_Lean_instInhabitedEnumAttributes_default___closed__3_once, _init_l_Lean_instInhabitedEnumAttributes_default___closed__3);
v___x_3231_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3231_, 0, v___x_3230_);
lean_ctor_set(v___x_3231_, 1, v___x_3229_);
lean_ctor_set(v___x_3231_, 2, v___f_3228_);
lean_ctor_set(v___x_3231_, 3, v___f_3227_);
lean_ctor_set(v___x_3231_, 4, v___f_3226_);
lean_ctor_set(v___x_3231_, 5, v___f_3225_);
return v___x_3231_;
}
}
static lean_object* _init_l_Lean_instInhabitedEnumAttributes_default___closed__5(void){
_start:
{
lean_object* v___x_3232_; lean_object* v___x_3233_; lean_object* v___x_3234_; 
v___x_3232_ = lean_obj_once(&l_Lean_instInhabitedEnumAttributes_default___closed__4, &l_Lean_instInhabitedEnumAttributes_default___closed__4_once, _init_l_Lean_instInhabitedEnumAttributes_default___closed__4);
v___x_3233_ = lean_box(0);
v___x_3234_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3234_, 0, v___x_3233_);
lean_ctor_set(v___x_3234_, 1, v___x_3232_);
return v___x_3234_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default(lean_object* v_00_u03b1_3235_){
_start:
{
lean_object* v___x_3236_; 
v___x_3236_ = lean_obj_once(&l_Lean_instInhabitedEnumAttributes_default___closed__5, &l_Lean_instInhabitedEnumAttributes_default___closed__5_once, _init_l_Lean_instInhabitedEnumAttributes_default___closed__5);
return v___x_3236_;
}
}
static lean_object* _init_l_Lean_instInhabitedEnumAttributes___closed__0(void){
_start:
{
lean_object* v___x_3237_; 
v___x_3237_ = l_Lean_instInhabitedEnumAttributes_default(lean_box(0));
return v___x_3237_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes(lean_object* v_a_3238_){
_start:
{
lean_object* v___x_3239_; 
v___x_3239_ = lean_obj_once(&l_Lean_instInhabitedEnumAttributes___closed__0, &l_Lean_instInhabitedEnumAttributes___closed__0_once, _init_l_Lean_instInhabitedEnumAttributes___closed__0);
return v___x_3239_;
}
}
static lean_object* _init_l_Lean_registerEnumAttributes___auto__1(void){
_start:
{
lean_object* v___x_3240_; 
v___x_3240_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__28, &l_Lean_AttributeImplCore_ref___autoParam___closed__28_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__28);
return v___x_3240_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__0(lean_object* v_x_3241_){
_start:
{
lean_object* v___x_3242_; 
v___x_3242_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___lam__2___closed__0));
return v___x_3242_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__0___boxed(lean_object* v_x_3243_){
_start:
{
lean_object* v_res_3244_; 
v_res_3244_ = l_Lean_registerEnumAttributes___redArg___lam__0(v_x_3243_);
lean_dec(v_x_3243_);
return v_res_3244_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___redArg(lean_object* v_newState_3245_, lean_object* v_x_3246_, lean_object* v_x_3247_){
_start:
{
if (lean_obj_tag(v_x_3247_) == 0)
{
return v_x_3246_;
}
else
{
lean_object* v_head_3248_; lean_object* v_tail_3249_; lean_object* v___x_3250_; 
v_head_3248_ = lean_ctor_get(v_x_3247_, 0);
lean_inc(v_head_3248_);
v_tail_3249_ = lean_ctor_get(v_x_3247_, 1);
lean_inc(v_tail_3249_);
lean_dec_ref(v_x_3247_);
v___x_3250_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_newState_3245_, v_head_3248_);
if (lean_obj_tag(v___x_3250_) == 1)
{
lean_object* v_val_3251_; lean_object* v___x_3252_; 
v_val_3251_ = lean_ctor_get(v___x_3250_, 0);
lean_inc(v_val_3251_);
lean_dec_ref(v___x_3250_);
v___x_3252_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_head_3248_, v_val_3251_, v_x_3246_);
v_x_3246_ = v___x_3252_;
v_x_3247_ = v_tail_3249_;
goto _start;
}
else
{
lean_dec(v___x_3250_);
lean_dec(v_head_3248_);
v_x_3247_ = v_tail_3249_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___redArg___boxed(lean_object* v_newState_3255_, lean_object* v_x_3256_, lean_object* v_x_3257_){
_start:
{
lean_object* v_res_3258_; 
v_res_3258_ = l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___redArg(v_newState_3255_, v_x_3256_, v_x_3257_);
lean_dec(v_newState_3255_);
return v_res_3258_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__1(lean_object* v_x_3259_, lean_object* v_newState_3260_, lean_object* v_consts_3261_, lean_object* v_st_3262_){
_start:
{
lean_object* v___x_3263_; 
v___x_3263_ = l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___redArg(v_newState_3260_, v_st_3262_, v_consts_3261_);
return v___x_3263_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__1___boxed(lean_object* v_x_3264_, lean_object* v_newState_3265_, lean_object* v_consts_3266_, lean_object* v_st_3267_){
_start:
{
lean_object* v_res_3268_; 
v_res_3268_ = l_Lean_registerEnumAttributes___redArg___lam__1(v_x_3264_, v_newState_3265_, v_consts_3266_, v_st_3267_);
lean_dec(v_newState_3265_);
lean_dec(v_x_3264_);
return v_res_3268_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__2(lean_object* v_s_3278_){
_start:
{
lean_object* v___x_3279_; lean_object* v___y_3281_; 
v___x_3279_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___lam__2___closed__3));
if (lean_obj_tag(v_s_3278_) == 0)
{
lean_object* v_size_3285_; 
v_size_3285_ = lean_ctor_get(v_s_3278_, 0);
lean_inc(v_size_3285_);
lean_dec_ref(v_s_3278_);
v___y_3281_ = v_size_3285_;
goto v___jp_3280_;
}
else
{
lean_object* v___x_3286_; 
v___x_3286_ = lean_unsigned_to_nat(0u);
v___y_3281_ = v___x_3286_;
goto v___jp_3280_;
}
v___jp_3280_:
{
lean_object* v___x_3282_; lean_object* v___x_3283_; lean_object* v___x_3284_; 
v___x_3282_ = l_Nat_reprFast(v___y_3281_);
v___x_3283_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3283_, 0, v___x_3282_);
v___x_3284_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3284_, 0, v___x_3279_);
lean_ctor_set(v___x_3284_, 1, v___x_3283_);
return v___x_3284_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg(lean_object* v_env_3287_, lean_object* v_as_3288_, size_t v_i_3289_, size_t v_stop_3290_, lean_object* v_b_3291_){
_start:
{
lean_object* v___y_3293_; uint8_t v___x_3297_; 
v___x_3297_ = lean_usize_dec_eq(v_i_3289_, v_stop_3290_);
if (v___x_3297_ == 0)
{
lean_object* v___x_3298_; lean_object* v_fst_3299_; uint8_t v___x_3300_; lean_object* v___x_3301_; uint8_t v___x_3302_; 
v___x_3298_ = lean_array_uget_borrowed(v_as_3288_, v_i_3289_);
v_fst_3299_ = lean_ctor_get(v___x_3298_, 0);
v___x_3300_ = 1;
lean_inc_ref(v_env_3287_);
v___x_3301_ = l_Lean_Environment_setExporting(v_env_3287_, v___x_3300_);
lean_inc(v_fst_3299_);
v___x_3302_ = l_Lean_Environment_contains(v___x_3301_, v_fst_3299_, v___x_3297_);
if (v___x_3302_ == 0)
{
v___y_3293_ = v_b_3291_;
goto v___jp_3292_;
}
else
{
lean_object* v___x_3303_; 
lean_inc(v___x_3298_);
v___x_3303_ = lean_array_push(v_b_3291_, v___x_3298_);
v___y_3293_ = v___x_3303_;
goto v___jp_3292_;
}
}
else
{
lean_dec_ref(v_env_3287_);
return v_b_3291_;
}
v___jp_3292_:
{
size_t v___x_3294_; size_t v___x_3295_; 
v___x_3294_ = ((size_t)1ULL);
v___x_3295_ = lean_usize_add(v_i_3289_, v___x_3294_);
v_i_3289_ = v___x_3295_;
v_b_3291_ = v___y_3293_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg___boxed(lean_object* v_env_3304_, lean_object* v_as_3305_, lean_object* v_i_3306_, lean_object* v_stop_3307_, lean_object* v_b_3308_){
_start:
{
size_t v_i_boxed_3309_; size_t v_stop_boxed_3310_; lean_object* v_res_3311_; 
v_i_boxed_3309_ = lean_unbox_usize(v_i_3306_);
lean_dec(v_i_3306_);
v_stop_boxed_3310_ = lean_unbox_usize(v_stop_3307_);
lean_dec(v_stop_3307_);
v_res_3311_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg(v_env_3304_, v_as_3305_, v_i_boxed_3309_, v_stop_boxed_3310_, v_b_3308_);
lean_dec_ref(v_as_3305_);
return v_res_3311_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__3(lean_object* v_env_3312_, lean_object* v_m_3313_){
_start:
{
lean_object* v___x_3314_; lean_object* v___x_3315_; lean_object* v___y_3317_; lean_object* v___x_3331_; lean_object* v___x_3332_; lean_object* v___y_3334_; lean_object* v___y_3335_; uint8_t v___x_3337_; 
v___x_3314_ = lean_unsigned_to_nat(0u);
v___x_3315_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___lam__2___closed__0));
v___x_3331_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1_spec__1___redArg(v___x_3315_, v_m_3313_);
v___x_3332_ = lean_array_get_size(v___x_3331_);
v___x_3337_ = lean_nat_dec_eq(v___x_3332_, v___x_3314_);
if (v___x_3337_ == 0)
{
lean_object* v___x_3338_; lean_object* v___x_3339_; lean_object* v___y_3341_; uint8_t v___x_3343_; 
v___x_3338_ = lean_unsigned_to_nat(1u);
v___x_3339_ = lean_nat_sub(v___x_3332_, v___x_3338_);
v___x_3343_ = lean_nat_dec_le(v___x_3314_, v___x_3339_);
if (v___x_3343_ == 0)
{
lean_inc(v___x_3339_);
v___y_3341_ = v___x_3339_;
goto v___jp_3340_;
}
else
{
v___y_3341_ = v___x_3314_;
goto v___jp_3340_;
}
v___jp_3340_:
{
uint8_t v___x_3342_; 
v___x_3342_ = lean_nat_dec_le(v___y_3341_, v___x_3339_);
if (v___x_3342_ == 0)
{
lean_dec(v___x_3339_);
lean_inc(v___y_3341_);
v___y_3334_ = v___y_3341_;
v___y_3335_ = v___y_3341_;
goto v___jp_3333_;
}
else
{
v___y_3334_ = v___y_3341_;
v___y_3335_ = v___x_3339_;
goto v___jp_3333_;
}
}
}
else
{
v___y_3317_ = v___x_3331_;
goto v___jp_3316_;
}
v___jp_3316_:
{
lean_object* v___x_3318_; uint8_t v___x_3319_; 
v___x_3318_ = lean_array_get_size(v___y_3317_);
v___x_3319_ = lean_nat_dec_lt(v___x_3314_, v___x_3318_);
if (v___x_3319_ == 0)
{
lean_object* v___x_3320_; 
lean_dec_ref(v_env_3312_);
v___x_3320_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3320_, 0, v___x_3315_);
lean_ctor_set(v___x_3320_, 1, v___x_3315_);
lean_ctor_set(v___x_3320_, 2, v___y_3317_);
return v___x_3320_;
}
else
{
uint8_t v___x_3321_; 
v___x_3321_ = lean_nat_dec_le(v___x_3318_, v___x_3318_);
if (v___x_3321_ == 0)
{
if (v___x_3319_ == 0)
{
lean_object* v___x_3322_; 
lean_dec_ref(v_env_3312_);
v___x_3322_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3322_, 0, v___x_3315_);
lean_ctor_set(v___x_3322_, 1, v___x_3315_);
lean_ctor_set(v___x_3322_, 2, v___y_3317_);
return v___x_3322_;
}
else
{
size_t v___x_3323_; size_t v___x_3324_; lean_object* v___x_3325_; lean_object* v___x_3326_; 
v___x_3323_ = ((size_t)0ULL);
v___x_3324_ = lean_usize_of_nat(v___x_3318_);
v___x_3325_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg(v_env_3312_, v___y_3317_, v___x_3323_, v___x_3324_, v___x_3315_);
lean_inc_ref(v___x_3325_);
v___x_3326_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3326_, 0, v___x_3325_);
lean_ctor_set(v___x_3326_, 1, v___x_3325_);
lean_ctor_set(v___x_3326_, 2, v___y_3317_);
return v___x_3326_;
}
}
else
{
size_t v___x_3327_; size_t v___x_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; 
v___x_3327_ = ((size_t)0ULL);
v___x_3328_ = lean_usize_of_nat(v___x_3318_);
v___x_3329_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg(v_env_3312_, v___y_3317_, v___x_3327_, v___x_3328_, v___x_3315_);
lean_inc_ref(v___x_3329_);
v___x_3330_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3330_, 0, v___x_3329_);
lean_ctor_set(v___x_3330_, 1, v___x_3329_);
lean_ctor_set(v___x_3330_, 2, v___y_3317_);
return v___x_3330_;
}
}
}
v___jp_3333_:
{
lean_object* v___x_3336_; 
v___x_3336_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2___redArg(v___x_3332_, v___x_3331_, v___y_3334_, v___y_3335_);
lean_dec(v___y_3335_);
v___y_3317_ = v___x_3336_;
goto v___jp_3316_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__3___boxed(lean_object* v_env_3344_, lean_object* v_m_3345_){
_start:
{
lean_object* v_res_3346_; 
v_res_3346_ = l_Lean_registerEnumAttributes___redArg___lam__3(v_env_3344_, v_m_3345_);
lean_dec(v_m_3345_);
return v_res_3346_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__4(lean_object* v_s_3347_, lean_object* v_p_3348_){
_start:
{
lean_object* v_fst_3349_; lean_object* v_snd_3350_; lean_object* v___x_3351_; 
v_fst_3349_ = lean_ctor_get(v_p_3348_, 0);
lean_inc(v_fst_3349_);
v_snd_3350_ = lean_ctor_get(v_p_3348_, 1);
lean_inc(v_snd_3350_);
lean_dec_ref(v_p_3348_);
v___x_3351_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_3349_, v_snd_3350_, v_s_3347_);
return v___x_3351_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__6(lean_object* v___x_3352_, lean_object* v_x_3353_, lean_object* v_x_3354_){
_start:
{
lean_object* v___x_3356_; 
v___x_3356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3356_, 0, v___x_3352_);
return v___x_3356_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__6___boxed(lean_object* v___x_3357_, lean_object* v_x_3358_, lean_object* v_x_3359_, lean_object* v___y_3360_){
_start:
{
lean_object* v_res_3361_; 
v_res_3361_ = l_Lean_registerEnumAttributes___redArg___lam__6(v___x_3357_, v_x_3358_, v_x_3359_);
lean_dec_ref(v_x_3359_);
lean_dec_ref(v_x_3358_);
return v_res_3361_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_registerEnumAttributes_spec__3(lean_object* v_as_3362_){
_start:
{
if (lean_obj_tag(v_as_3362_) == 0)
{
lean_object* v___x_3364_; lean_object* v___x_3365_; 
v___x_3364_ = lean_box(0);
v___x_3365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3365_, 0, v___x_3364_);
return v___x_3365_;
}
else
{
lean_object* v_head_3366_; lean_object* v_tail_3367_; lean_object* v___x_3368_; 
v_head_3366_ = lean_ctor_get(v_as_3362_, 0);
lean_inc(v_head_3366_);
v_tail_3367_ = lean_ctor_get(v_as_3362_, 1);
lean_inc(v_tail_3367_);
lean_dec_ref(v_as_3362_);
v___x_3368_ = l_Lean_registerBuiltinAttribute(v_head_3366_);
if (lean_obj_tag(v___x_3368_) == 0)
{
lean_dec_ref(v___x_3368_);
v_as_3362_ = v_tail_3367_;
goto _start;
}
else
{
lean_dec(v_tail_3367_);
return v___x_3368_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_registerEnumAttributes_spec__3___boxed(lean_object* v_as_3370_, lean_object* v___y_3371_){
_start:
{
lean_object* v_res_3372_; 
v_res_3372_ = l_List_forM___at___00Lean_registerEnumAttributes_spec__3(v_as_3370_);
return v_res_3372_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__1(lean_object* v_validate_3373_, lean_object* v_snd_3374_, lean_object* v_a_3375_, lean_object* v_fst_3376_, lean_object* v_decl_3377_, lean_object* v_stx_3378_, uint8_t v_kind_3379_, lean_object* v___y_3380_, lean_object* v___y_3381_){
_start:
{
lean_object* v___y_3384_; lean_object* v___y_3385_; lean_object* v___y_3421_; lean_object* v___y_3422_; lean_object* v___x_3427_; 
v___x_3427_ = l_Lean_Attribute_Builtin_ensureNoArgs(v_stx_3378_, v___y_3380_, v___y_3381_);
if (lean_obj_tag(v___x_3427_) == 0)
{
uint8_t v___x_3428_; uint8_t v___x_3429_; 
lean_dec_ref(v___x_3427_);
v___x_3428_ = 0;
v___x_3429_ = l_Lean_instBEqAttributeKind_beq(v_kind_3379_, v___x_3428_);
if (v___x_3429_ == 0)
{
lean_object* v___x_3430_; 
lean_dec(v_decl_3377_);
lean_dec_ref(v_a_3375_);
lean_dec(v_snd_3374_);
lean_dec_ref(v_validate_3373_);
v___x_3430_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg(v_fst_3376_, v_kind_3379_, v___y_3380_, v___y_3381_);
return v___x_3430_;
}
else
{
v___y_3421_ = v___y_3380_;
v___y_3422_ = v___y_3381_;
goto v___jp_3420_;
}
}
else
{
lean_dec(v_decl_3377_);
lean_dec(v_fst_3376_);
lean_dec_ref(v_a_3375_);
lean_dec(v_snd_3374_);
lean_dec_ref(v_validate_3373_);
return v___x_3427_;
}
v___jp_3383_:
{
lean_object* v___x_3386_; 
lean_inc(v___y_3385_);
lean_inc_ref(v___y_3384_);
lean_inc(v_snd_3374_);
lean_inc(v_decl_3377_);
v___x_3386_ = lean_apply_5(v_validate_3373_, v_decl_3377_, v_snd_3374_, v___y_3384_, v___y_3385_, lean_box(0));
if (lean_obj_tag(v___x_3386_) == 0)
{
lean_object* v___x_3388_; uint8_t v_isShared_3389_; uint8_t v_isSharedCheck_3418_; 
v_isSharedCheck_3418_ = !lean_is_exclusive(v___x_3386_);
if (v_isSharedCheck_3418_ == 0)
{
lean_object* v_unused_3419_; 
v_unused_3419_ = lean_ctor_get(v___x_3386_, 0);
lean_dec(v_unused_3419_);
v___x_3388_ = v___x_3386_;
v_isShared_3389_ = v_isSharedCheck_3418_;
goto v_resetjp_3387_;
}
else
{
lean_dec(v___x_3386_);
v___x_3388_ = lean_box(0);
v_isShared_3389_ = v_isSharedCheck_3418_;
goto v_resetjp_3387_;
}
v_resetjp_3387_:
{
lean_object* v___x_3390_; lean_object* v_toEnvExtension_3391_; lean_object* v_env_3392_; lean_object* v_nextMacroScope_3393_; lean_object* v_ngen_3394_; lean_object* v_auxDeclNGen_3395_; lean_object* v_traceState_3396_; lean_object* v_messages_3397_; lean_object* v_infoState_3398_; lean_object* v_snapshotTasks_3399_; lean_object* v_newDecls_3400_; lean_object* v___x_3402_; uint8_t v_isShared_3403_; uint8_t v_isSharedCheck_3416_; 
v___x_3390_ = lean_st_ref_take(v___y_3385_);
v_toEnvExtension_3391_ = lean_ctor_get(v_a_3375_, 0);
v_env_3392_ = lean_ctor_get(v___x_3390_, 0);
v_nextMacroScope_3393_ = lean_ctor_get(v___x_3390_, 1);
v_ngen_3394_ = lean_ctor_get(v___x_3390_, 2);
v_auxDeclNGen_3395_ = lean_ctor_get(v___x_3390_, 3);
v_traceState_3396_ = lean_ctor_get(v___x_3390_, 4);
v_messages_3397_ = lean_ctor_get(v___x_3390_, 6);
v_infoState_3398_ = lean_ctor_get(v___x_3390_, 7);
v_snapshotTasks_3399_ = lean_ctor_get(v___x_3390_, 8);
v_newDecls_3400_ = lean_ctor_get(v___x_3390_, 9);
v_isSharedCheck_3416_ = !lean_is_exclusive(v___x_3390_);
if (v_isSharedCheck_3416_ == 0)
{
lean_object* v_unused_3417_; 
v_unused_3417_ = lean_ctor_get(v___x_3390_, 5);
lean_dec(v_unused_3417_);
v___x_3402_ = v___x_3390_;
v_isShared_3403_ = v_isSharedCheck_3416_;
goto v_resetjp_3401_;
}
else
{
lean_inc(v_newDecls_3400_);
lean_inc(v_snapshotTasks_3399_);
lean_inc(v_infoState_3398_);
lean_inc(v_messages_3397_);
lean_inc(v_traceState_3396_);
lean_inc(v_auxDeclNGen_3395_);
lean_inc(v_ngen_3394_);
lean_inc(v_nextMacroScope_3393_);
lean_inc(v_env_3392_);
lean_dec(v___x_3390_);
v___x_3402_ = lean_box(0);
v_isShared_3403_ = v_isSharedCheck_3416_;
goto v_resetjp_3401_;
}
v_resetjp_3401_:
{
lean_object* v_asyncMode_3404_; lean_object* v___x_3405_; lean_object* v___x_3406_; lean_object* v___x_3407_; lean_object* v___x_3409_; 
v_asyncMode_3404_ = lean_ctor_get(v_toEnvExtension_3391_, 2);
lean_inc(v_asyncMode_3404_);
lean_inc(v_decl_3377_);
v___x_3405_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3405_, 0, v_decl_3377_);
lean_ctor_set(v___x_3405_, 1, v_snd_3374_);
v___x_3406_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_a_3375_, v_env_3392_, v___x_3405_, v_asyncMode_3404_, v_decl_3377_);
lean_dec(v_asyncMode_3404_);
v___x_3407_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2);
if (v_isShared_3403_ == 0)
{
lean_ctor_set(v___x_3402_, 5, v___x_3407_);
lean_ctor_set(v___x_3402_, 0, v___x_3406_);
v___x_3409_ = v___x_3402_;
goto v_reusejp_3408_;
}
else
{
lean_object* v_reuseFailAlloc_3415_; 
v_reuseFailAlloc_3415_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3415_, 0, v___x_3406_);
lean_ctor_set(v_reuseFailAlloc_3415_, 1, v_nextMacroScope_3393_);
lean_ctor_set(v_reuseFailAlloc_3415_, 2, v_ngen_3394_);
lean_ctor_set(v_reuseFailAlloc_3415_, 3, v_auxDeclNGen_3395_);
lean_ctor_set(v_reuseFailAlloc_3415_, 4, v_traceState_3396_);
lean_ctor_set(v_reuseFailAlloc_3415_, 5, v___x_3407_);
lean_ctor_set(v_reuseFailAlloc_3415_, 6, v_messages_3397_);
lean_ctor_set(v_reuseFailAlloc_3415_, 7, v_infoState_3398_);
lean_ctor_set(v_reuseFailAlloc_3415_, 8, v_snapshotTasks_3399_);
lean_ctor_set(v_reuseFailAlloc_3415_, 9, v_newDecls_3400_);
v___x_3409_ = v_reuseFailAlloc_3415_;
goto v_reusejp_3408_;
}
v_reusejp_3408_:
{
lean_object* v___x_3410_; lean_object* v___x_3411_; lean_object* v___x_3413_; 
v___x_3410_ = lean_st_ref_set(v___y_3385_, v___x_3409_);
v___x_3411_ = lean_box(0);
if (v_isShared_3389_ == 0)
{
lean_ctor_set(v___x_3388_, 0, v___x_3411_);
v___x_3413_ = v___x_3388_;
goto v_reusejp_3412_;
}
else
{
lean_object* v_reuseFailAlloc_3414_; 
v_reuseFailAlloc_3414_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3414_, 0, v___x_3411_);
v___x_3413_ = v_reuseFailAlloc_3414_;
goto v_reusejp_3412_;
}
v_reusejp_3412_:
{
return v___x_3413_;
}
}
}
}
}
else
{
lean_dec(v_decl_3377_);
lean_dec_ref(v_a_3375_);
lean_dec(v_snd_3374_);
return v___x_3386_;
}
}
v___jp_3420_:
{
lean_object* v___x_3423_; lean_object* v_env_3424_; lean_object* v___x_3425_; 
v___x_3423_ = lean_st_ref_get(v___y_3422_);
v_env_3424_ = lean_ctor_get(v___x_3423_, 0);
lean_inc_ref(v_env_3424_);
lean_dec(v___x_3423_);
v___x_3425_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3424_, v_decl_3377_);
lean_dec_ref(v_env_3424_);
if (lean_obj_tag(v___x_3425_) == 0)
{
lean_dec(v_fst_3376_);
v___y_3384_ = v___y_3421_;
v___y_3385_ = v___y_3422_;
goto v___jp_3383_;
}
else
{
lean_object* v___x_3426_; 
lean_dec_ref(v___x_3425_);
lean_dec_ref(v_a_3375_);
lean_dec(v_snd_3374_);
lean_dec_ref(v_validate_3373_);
v___x_3426_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg(v_fst_3376_, v_decl_3377_, v___y_3421_, v___y_3422_);
return v___x_3426_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__1___boxed(lean_object* v_validate_3431_, lean_object* v_snd_3432_, lean_object* v_a_3433_, lean_object* v_fst_3434_, lean_object* v_decl_3435_, lean_object* v_stx_3436_, lean_object* v_kind_3437_, lean_object* v___y_3438_, lean_object* v___y_3439_, lean_object* v___y_3440_){
_start:
{
uint8_t v_kind_boxed_3441_; lean_object* v_res_3442_; 
v_kind_boxed_3441_ = lean_unbox(v_kind_3437_);
v_res_3442_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__1(v_validate_3431_, v_snd_3432_, v_a_3433_, v_fst_3434_, v_decl_3435_, v_stx_3436_, v_kind_boxed_3441_, v___y_3438_, v___y_3439_);
lean_dec(v___y_3439_);
lean_dec_ref(v___y_3438_);
return v_res_3442_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__0(lean_object* v_fst_3443_, lean_object* v_decl_3444_, lean_object* v___y_3445_, lean_object* v___y_3446_){
_start:
{
lean_object* v___x_3448_; lean_object* v___x_3449_; lean_object* v___x_3450_; lean_object* v___x_3451_; lean_object* v___x_3452_; lean_object* v___x_3453_; 
v___x_3448_ = lean_obj_once(&l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1, &l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1_once, _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1);
v___x_3449_ = l_Lean_MessageData_ofName(v_fst_3443_);
v___x_3450_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3450_, 0, v___x_3448_);
lean_ctor_set(v___x_3450_, 1, v___x_3449_);
v___x_3451_ = lean_obj_once(&l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3, &l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3_once, _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3);
v___x_3452_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3452_, 0, v___x_3450_);
lean_ctor_set(v___x_3452_, 1, v___x_3451_);
v___x_3453_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_3452_, v___y_3445_, v___y_3446_);
return v___x_3453_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__0___boxed(lean_object* v_fst_3454_, lean_object* v_decl_3455_, lean_object* v___y_3456_, lean_object* v___y_3457_, lean_object* v___y_3458_){
_start:
{
lean_object* v_res_3459_; 
v_res_3459_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__0(v_fst_3454_, v_decl_3455_, v___y_3456_, v___y_3457_);
lean_dec(v___y_3457_);
lean_dec_ref(v___y_3456_);
lean_dec(v_decl_3455_);
return v_res_3459_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg(lean_object* v_validate_3460_, lean_object* v_a_3461_, lean_object* v_ref_3462_, uint8_t v_applicationTime_3463_, lean_object* v_a_3464_, lean_object* v_a_3465_){
_start:
{
if (lean_obj_tag(v_a_3464_) == 0)
{
lean_object* v___x_3466_; 
lean_dec(v_ref_3462_);
lean_dec_ref(v_a_3461_);
lean_dec_ref(v_validate_3460_);
v___x_3466_ = l_List_reverse___redArg(v_a_3465_);
return v___x_3466_;
}
else
{
lean_object* v_head_3467_; lean_object* v_snd_3468_; lean_object* v_tail_3469_; lean_object* v___x_3471_; uint8_t v_isShared_3472_; uint8_t v_isSharedCheck_3484_; 
v_head_3467_ = lean_ctor_get(v_a_3464_, 0);
lean_inc(v_head_3467_);
v_snd_3468_ = lean_ctor_get(v_head_3467_, 1);
lean_inc(v_snd_3468_);
v_tail_3469_ = lean_ctor_get(v_a_3464_, 1);
v_isSharedCheck_3484_ = !lean_is_exclusive(v_a_3464_);
if (v_isSharedCheck_3484_ == 0)
{
lean_object* v_unused_3485_; 
v_unused_3485_ = lean_ctor_get(v_a_3464_, 0);
lean_dec(v_unused_3485_);
v___x_3471_ = v_a_3464_;
v_isShared_3472_ = v_isSharedCheck_3484_;
goto v_resetjp_3470_;
}
else
{
lean_inc(v_tail_3469_);
lean_dec(v_a_3464_);
v___x_3471_ = lean_box(0);
v_isShared_3472_ = v_isSharedCheck_3484_;
goto v_resetjp_3470_;
}
v_resetjp_3470_:
{
lean_object* v_fst_3473_; lean_object* v_fst_3474_; lean_object* v_snd_3475_; lean_object* v___f_3476_; lean_object* v___f_3477_; lean_object* v___x_3478_; lean_object* v___x_3479_; lean_object* v___x_3481_; 
v_fst_3473_ = lean_ctor_get(v_head_3467_, 0);
lean_inc_n(v_fst_3473_, 3);
lean_dec(v_head_3467_);
v_fst_3474_ = lean_ctor_get(v_snd_3468_, 0);
lean_inc(v_fst_3474_);
v_snd_3475_ = lean_ctor_get(v_snd_3468_, 1);
lean_inc(v_snd_3475_);
lean_dec(v_snd_3468_);
v___f_3476_ = lean_alloc_closure((void*)(l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__0___boxed), 5, 1);
lean_closure_set(v___f_3476_, 0, v_fst_3473_);
lean_inc_ref(v_a_3461_);
lean_inc_ref(v_validate_3460_);
v___f_3477_ = lean_alloc_closure((void*)(l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__1___boxed), 10, 4);
lean_closure_set(v___f_3477_, 0, v_validate_3460_);
lean_closure_set(v___f_3477_, 1, v_snd_3475_);
lean_closure_set(v___f_3477_, 2, v_a_3461_);
lean_closure_set(v___f_3477_, 3, v_fst_3473_);
lean_inc(v_ref_3462_);
v___x_3478_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_3478_, 0, v_ref_3462_);
lean_ctor_set(v___x_3478_, 1, v_fst_3473_);
lean_ctor_set(v___x_3478_, 2, v_fst_3474_);
lean_ctor_set_uint8(v___x_3478_, sizeof(void*)*3, v_applicationTime_3463_);
v___x_3479_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3479_, 0, v___x_3478_);
lean_ctor_set(v___x_3479_, 1, v___f_3477_);
lean_ctor_set(v___x_3479_, 2, v___f_3476_);
if (v_isShared_3472_ == 0)
{
lean_ctor_set(v___x_3471_, 1, v_a_3465_);
lean_ctor_set(v___x_3471_, 0, v___x_3479_);
v___x_3481_ = v___x_3471_;
goto v_reusejp_3480_;
}
else
{
lean_object* v_reuseFailAlloc_3483_; 
v_reuseFailAlloc_3483_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3483_, 0, v___x_3479_);
lean_ctor_set(v_reuseFailAlloc_3483_, 1, v_a_3465_);
v___x_3481_ = v_reuseFailAlloc_3483_;
goto v_reusejp_3480_;
}
v_reusejp_3480_:
{
v_a_3464_ = v_tail_3469_;
v_a_3465_ = v___x_3481_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___boxed(lean_object* v_validate_3486_, lean_object* v_a_3487_, lean_object* v_ref_3488_, lean_object* v_applicationTime_3489_, lean_object* v_a_3490_, lean_object* v_a_3491_){
_start:
{
uint8_t v_applicationTime_boxed_3492_; lean_object* v_res_3493_; 
v_applicationTime_boxed_3492_ = lean_unbox(v_applicationTime_3489_);
v_res_3493_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg(v_validate_3486_, v_a_3487_, v_ref_3488_, v_applicationTime_boxed_3492_, v_a_3490_, v_a_3491_);
return v_res_3493_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg(lean_object* v_attrDescrs_3507_, lean_object* v_validate_3508_, uint8_t v_applicationTime_3509_, lean_object* v_ref_3510_){
_start:
{
lean_object* v___f_3512_; lean_object* v___f_3513_; lean_object* v___f_3514_; lean_object* v___f_3515_; lean_object* v___f_3516_; lean_object* v___f_3517_; lean_object* v___x_3518_; lean_object* v___x_3519_; lean_object* v___x_3520_; lean_object* v___x_3521_; lean_object* v___x_3522_; 
v___f_3512_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__0));
v___f_3513_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__2));
v___f_3514_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__3));
v___f_3515_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__4));
v___f_3516_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__5));
v___f_3517_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__6));
v___x_3518_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__7));
v___x_3519_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__8));
lean_inc(v_ref_3510_);
v___x_3520_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_3520_, 0, v_ref_3510_);
lean_ctor_set(v___x_3520_, 1, v___f_3516_);
lean_ctor_set(v___x_3520_, 2, v___f_3517_);
lean_ctor_set(v___x_3520_, 3, v___f_3515_);
lean_ctor_set(v___x_3520_, 4, v___f_3514_);
lean_ctor_set(v___x_3520_, 5, v___f_3513_);
lean_ctor_set(v___x_3520_, 6, v___x_3518_);
lean_ctor_set(v___x_3520_, 7, v___x_3519_);
v___x_3521_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3521_, 0, v___x_3520_);
lean_ctor_set(v___x_3521_, 1, v___f_3512_);
v___x_3522_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_3521_);
if (lean_obj_tag(v___x_3522_) == 0)
{
lean_object* v_a_3523_; lean_object* v___x_3524_; lean_object* v___x_3525_; lean_object* v___x_3526_; 
v_a_3523_ = lean_ctor_get(v___x_3522_, 0);
lean_inc_n(v_a_3523_, 2);
lean_dec_ref(v___x_3522_);
v___x_3524_ = lean_box(0);
v___x_3525_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg(v_validate_3508_, v_a_3523_, v_ref_3510_, v_applicationTime_3509_, v_attrDescrs_3507_, v___x_3524_);
lean_inc(v___x_3525_);
v___x_3526_ = l_List_forM___at___00Lean_registerEnumAttributes_spec__3(v___x_3525_);
if (lean_obj_tag(v___x_3526_) == 0)
{
lean_object* v___x_3528_; uint8_t v_isShared_3529_; uint8_t v_isSharedCheck_3534_; 
v_isSharedCheck_3534_ = !lean_is_exclusive(v___x_3526_);
if (v_isSharedCheck_3534_ == 0)
{
lean_object* v_unused_3535_; 
v_unused_3535_ = lean_ctor_get(v___x_3526_, 0);
lean_dec(v_unused_3535_);
v___x_3528_ = v___x_3526_;
v_isShared_3529_ = v_isSharedCheck_3534_;
goto v_resetjp_3527_;
}
else
{
lean_dec(v___x_3526_);
v___x_3528_ = lean_box(0);
v_isShared_3529_ = v_isSharedCheck_3534_;
goto v_resetjp_3527_;
}
v_resetjp_3527_:
{
lean_object* v___x_3530_; lean_object* v___x_3532_; 
v___x_3530_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3530_, 0, v___x_3525_);
lean_ctor_set(v___x_3530_, 1, v_a_3523_);
if (v_isShared_3529_ == 0)
{
lean_ctor_set(v___x_3528_, 0, v___x_3530_);
v___x_3532_ = v___x_3528_;
goto v_reusejp_3531_;
}
else
{
lean_object* v_reuseFailAlloc_3533_; 
v_reuseFailAlloc_3533_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3533_, 0, v___x_3530_);
v___x_3532_ = v_reuseFailAlloc_3533_;
goto v_reusejp_3531_;
}
v_reusejp_3531_:
{
return v___x_3532_;
}
}
}
else
{
lean_object* v_a_3536_; lean_object* v___x_3538_; uint8_t v_isShared_3539_; uint8_t v_isSharedCheck_3543_; 
lean_dec(v___x_3525_);
lean_dec(v_a_3523_);
v_a_3536_ = lean_ctor_get(v___x_3526_, 0);
v_isSharedCheck_3543_ = !lean_is_exclusive(v___x_3526_);
if (v_isSharedCheck_3543_ == 0)
{
v___x_3538_ = v___x_3526_;
v_isShared_3539_ = v_isSharedCheck_3543_;
goto v_resetjp_3537_;
}
else
{
lean_inc(v_a_3536_);
lean_dec(v___x_3526_);
v___x_3538_ = lean_box(0);
v_isShared_3539_ = v_isSharedCheck_3543_;
goto v_resetjp_3537_;
}
v_resetjp_3537_:
{
lean_object* v___x_3541_; 
if (v_isShared_3539_ == 0)
{
v___x_3541_ = v___x_3538_;
goto v_reusejp_3540_;
}
else
{
lean_object* v_reuseFailAlloc_3542_; 
v_reuseFailAlloc_3542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3542_, 0, v_a_3536_);
v___x_3541_ = v_reuseFailAlloc_3542_;
goto v_reusejp_3540_;
}
v_reusejp_3540_:
{
return v___x_3541_;
}
}
}
}
else
{
lean_object* v_a_3544_; lean_object* v___x_3546_; uint8_t v_isShared_3547_; uint8_t v_isSharedCheck_3551_; 
lean_dec(v_ref_3510_);
lean_dec_ref(v_validate_3508_);
lean_dec(v_attrDescrs_3507_);
v_a_3544_ = lean_ctor_get(v___x_3522_, 0);
v_isSharedCheck_3551_ = !lean_is_exclusive(v___x_3522_);
if (v_isSharedCheck_3551_ == 0)
{
v___x_3546_ = v___x_3522_;
v_isShared_3547_ = v_isSharedCheck_3551_;
goto v_resetjp_3545_;
}
else
{
lean_inc(v_a_3544_);
lean_dec(v___x_3522_);
v___x_3546_ = lean_box(0);
v_isShared_3547_ = v_isSharedCheck_3551_;
goto v_resetjp_3545_;
}
v_resetjp_3545_:
{
lean_object* v___x_3549_; 
if (v_isShared_3547_ == 0)
{
v___x_3549_ = v___x_3546_;
goto v_reusejp_3548_;
}
else
{
lean_object* v_reuseFailAlloc_3550_; 
v_reuseFailAlloc_3550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3550_, 0, v_a_3544_);
v___x_3549_ = v_reuseFailAlloc_3550_;
goto v_reusejp_3548_;
}
v_reusejp_3548_:
{
return v___x_3549_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___boxed(lean_object* v_attrDescrs_3552_, lean_object* v_validate_3553_, lean_object* v_applicationTime_3554_, lean_object* v_ref_3555_, lean_object* v_a_3556_){
_start:
{
uint8_t v_applicationTime_boxed_3557_; lean_object* v_res_3558_; 
v_applicationTime_boxed_3557_ = lean_unbox(v_applicationTime_3554_);
v_res_3558_ = l_Lean_registerEnumAttributes___redArg(v_attrDescrs_3552_, v_validate_3553_, v_applicationTime_boxed_3557_, v_ref_3555_);
return v_res_3558_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes(lean_object* v_00_u03b1_3559_, lean_object* v_attrDescrs_3560_, lean_object* v_validate_3561_, uint8_t v_applicationTime_3562_, lean_object* v_ref_3563_){
_start:
{
lean_object* v___x_3565_; 
v___x_3565_ = l_Lean_registerEnumAttributes___redArg(v_attrDescrs_3560_, v_validate_3561_, v_applicationTime_3562_, v_ref_3563_);
return v___x_3565_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___boxed(lean_object* v_00_u03b1_3566_, lean_object* v_attrDescrs_3567_, lean_object* v_validate_3568_, lean_object* v_applicationTime_3569_, lean_object* v_ref_3570_, lean_object* v_a_3571_){
_start:
{
uint8_t v_applicationTime_boxed_3572_; lean_object* v_res_3573_; 
v_applicationTime_boxed_3572_ = lean_unbox(v_applicationTime_3569_);
v_res_3573_ = l_Lean_registerEnumAttributes(v_00_u03b1_3566_, v_attrDescrs_3567_, v_validate_3568_, v_applicationTime_boxed_3572_, v_ref_3570_);
return v_res_3573_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0(lean_object* v_00_u03b1_3574_, lean_object* v_env_3575_, lean_object* v_as_3576_, size_t v_i_3577_, size_t v_stop_3578_, lean_object* v_b_3579_){
_start:
{
lean_object* v___x_3580_; 
v___x_3580_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg(v_env_3575_, v_as_3576_, v_i_3577_, v_stop_3578_, v_b_3579_);
return v___x_3580_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___boxed(lean_object* v_00_u03b1_3581_, lean_object* v_env_3582_, lean_object* v_as_3583_, lean_object* v_i_3584_, lean_object* v_stop_3585_, lean_object* v_b_3586_){
_start:
{
size_t v_i_boxed_3587_; size_t v_stop_boxed_3588_; lean_object* v_res_3589_; 
v_i_boxed_3587_ = lean_unbox_usize(v_i_3584_);
lean_dec(v_i_3584_);
v_stop_boxed_3588_ = lean_unbox_usize(v_stop_3585_);
lean_dec(v_stop_3585_);
v_res_3589_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0(v_00_u03b1_3581_, v_env_3582_, v_as_3583_, v_i_boxed_3587_, v_stop_boxed_3588_, v_b_3586_);
lean_dec_ref(v_as_3583_);
return v_res_3589_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerEnumAttributes_spec__1(lean_object* v_00_u03b1_3590_, lean_object* v_newState_3591_, lean_object* v_x_3592_, lean_object* v_x_3593_){
_start:
{
lean_object* v___x_3594_; 
v___x_3594_ = l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___redArg(v_newState_3591_, v_x_3592_, v_x_3593_);
return v___x_3594_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___boxed(lean_object* v_00_u03b1_3595_, lean_object* v_newState_3596_, lean_object* v_x_3597_, lean_object* v_x_3598_){
_start:
{
lean_object* v_res_3599_; 
v_res_3599_ = l_List_foldl___at___00Lean_registerEnumAttributes_spec__1(v_00_u03b1_3595_, v_newState_3596_, v_x_3597_, v_x_3598_);
lean_dec(v_newState_3596_);
return v_res_3599_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2(lean_object* v_00_u03b1_3600_, lean_object* v_validate_3601_, lean_object* v_a_3602_, lean_object* v_ref_3603_, uint8_t v_applicationTime_3604_, lean_object* v_a_3605_, lean_object* v_a_3606_){
_start:
{
lean_object* v___x_3607_; 
v___x_3607_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg(v_validate_3601_, v_a_3602_, v_ref_3603_, v_applicationTime_3604_, v_a_3605_, v_a_3606_);
return v___x_3607_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___boxed(lean_object* v_00_u03b1_3608_, lean_object* v_validate_3609_, lean_object* v_a_3610_, lean_object* v_ref_3611_, lean_object* v_applicationTime_3612_, lean_object* v_a_3613_, lean_object* v_a_3614_){
_start:
{
uint8_t v_applicationTime_boxed_3615_; lean_object* v_res_3616_; 
v_applicationTime_boxed_3615_ = lean_unbox(v_applicationTime_3612_);
v_res_3616_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2(v_00_u03b1_3608_, v_validate_3609_, v_a_3610_, v_ref_3611_, v_applicationTime_boxed_3615_, v_a_3613_, v_a_3614_);
return v_res_3616_;
}
}
LEAN_EXPORT lean_object* l_Lean_EnumAttributes_getValue___redArg(lean_object* v_inst_3617_, lean_object* v_attr_3618_, lean_object* v_env_3619_, lean_object* v_decl_3620_){
_start:
{
lean_object* v___x_3621_; lean_object* v___x_3622_; 
v___x_3621_ = lean_box(1);
v___x_3622_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3619_, v_decl_3620_);
if (lean_obj_tag(v___x_3622_) == 0)
{
lean_object* v_ext_3623_; lean_object* v_toEnvExtension_3624_; lean_object* v_asyncMode_3625_; lean_object* v___x_3626_; lean_object* v___x_3627_; 
lean_dec(v_inst_3617_);
v_ext_3623_ = lean_ctor_get(v_attr_3618_, 1);
lean_inc_ref(v_ext_3623_);
lean_dec_ref(v_attr_3618_);
v_toEnvExtension_3624_ = lean_ctor_get(v_ext_3623_, 0);
v_asyncMode_3625_ = lean_ctor_get(v_toEnvExtension_3624_, 2);
lean_inc(v_asyncMode_3625_);
lean_inc(v_decl_3620_);
v___x_3626_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3621_, v_ext_3623_, v_env_3619_, v_asyncMode_3625_, v_decl_3620_);
lean_dec(v_asyncMode_3625_);
lean_dec_ref(v_ext_3623_);
v___x_3627_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_3626_, v_decl_3620_);
lean_dec(v_decl_3620_);
lean_dec(v___x_3626_);
return v___x_3627_;
}
else
{
lean_object* v_val_3628_; lean_object* v_ext_3629_; lean_object* v___x_3631_; uint8_t v_isShared_3632_; uint8_t v_isSharedCheck_3659_; 
v_val_3628_ = lean_ctor_get(v___x_3622_, 0);
lean_inc(v_val_3628_);
lean_dec_ref(v___x_3622_);
v_ext_3629_ = lean_ctor_get(v_attr_3618_, 1);
v_isSharedCheck_3659_ = !lean_is_exclusive(v_attr_3618_);
if (v_isSharedCheck_3659_ == 0)
{
lean_object* v_unused_3660_; 
v_unused_3660_ = lean_ctor_get(v_attr_3618_, 0);
lean_dec(v_unused_3660_);
v___x_3631_ = v_attr_3618_;
v_isShared_3632_ = v_isSharedCheck_3659_;
goto v_resetjp_3630_;
}
else
{
lean_inc(v_ext_3629_);
lean_dec(v_attr_3618_);
v___x_3631_ = lean_box(0);
v_isShared_3632_ = v_isSharedCheck_3659_;
goto v_resetjp_3630_;
}
v_resetjp_3630_:
{
uint8_t v___x_3633_; lean_object* v___x_3634_; lean_object* v___x_3635_; lean_object* v___x_3636_; uint8_t v___x_3637_; 
v___x_3633_ = 0;
v___x_3634_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_3621_, v_ext_3629_, v_env_3619_, v_val_3628_, v___x_3633_);
lean_dec(v_val_3628_);
lean_dec_ref(v_env_3619_);
lean_dec_ref(v_ext_3629_);
v___x_3635_ = lean_unsigned_to_nat(0u);
v___x_3636_ = lean_array_get_size(v___x_3634_);
v___x_3637_ = lean_nat_dec_lt(v___x_3635_, v___x_3636_);
if (v___x_3637_ == 0)
{
lean_object* v___x_3638_; 
lean_dec_ref(v___x_3634_);
lean_del_object(v___x_3631_);
lean_dec(v_decl_3620_);
lean_dec(v_inst_3617_);
v___x_3638_ = lean_box(0);
return v___x_3638_;
}
else
{
lean_object* v___x_3639_; lean_object* v___x_3640_; uint8_t v___x_3641_; 
v___x_3639_ = lean_unsigned_to_nat(1u);
v___x_3640_ = lean_nat_sub(v___x_3636_, v___x_3639_);
v___x_3641_ = lean_nat_dec_le(v___x_3635_, v___x_3640_);
if (v___x_3641_ == 0)
{
lean_object* v___x_3642_; 
lean_dec(v___x_3640_);
lean_dec_ref(v___x_3634_);
lean_del_object(v___x_3631_);
lean_dec(v_decl_3620_);
lean_dec(v_inst_3617_);
v___x_3642_ = lean_box(0);
return v___x_3642_;
}
else
{
lean_object* v___f_3643_; lean_object* v___x_3645_; 
v___f_3643_ = ((lean_object*)(l_Lean_ParametricAttribute_getParam_x3f___redArg___closed__1));
if (v_isShared_3632_ == 0)
{
lean_ctor_set(v___x_3631_, 1, v_inst_3617_);
lean_ctor_set(v___x_3631_, 0, v_decl_3620_);
v___x_3645_ = v___x_3631_;
goto v_reusejp_3644_;
}
else
{
lean_object* v_reuseFailAlloc_3658_; 
v_reuseFailAlloc_3658_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3658_, 0, v_decl_3620_);
lean_ctor_set(v_reuseFailAlloc_3658_, 1, v_inst_3617_);
v___x_3645_ = v_reuseFailAlloc_3658_;
goto v_reusejp_3644_;
}
v_reusejp_3644_:
{
lean_object* v___x_3646_; lean_object* v___x_3647_; 
v___x_3646_ = ((lean_object*)(l_Lean_ParametricAttribute_getParam_x3f___redArg___closed__2));
v___x_3647_ = l_Array_binSearchAux___redArg(v___f_3643_, v___x_3646_, v___x_3634_, v___x_3645_, v___x_3635_, v___x_3640_);
lean_dec_ref(v___x_3634_);
if (lean_obj_tag(v___x_3647_) == 0)
{
lean_object* v___x_3648_; 
v___x_3648_ = lean_box(0);
return v___x_3648_;
}
else
{
lean_object* v_val_3649_; lean_object* v___x_3651_; uint8_t v_isShared_3652_; uint8_t v_isSharedCheck_3657_; 
v_val_3649_ = lean_ctor_get(v___x_3647_, 0);
v_isSharedCheck_3657_ = !lean_is_exclusive(v___x_3647_);
if (v_isSharedCheck_3657_ == 0)
{
v___x_3651_ = v___x_3647_;
v_isShared_3652_ = v_isSharedCheck_3657_;
goto v_resetjp_3650_;
}
else
{
lean_inc(v_val_3649_);
lean_dec(v___x_3647_);
v___x_3651_ = lean_box(0);
v_isShared_3652_ = v_isSharedCheck_3657_;
goto v_resetjp_3650_;
}
v_resetjp_3650_:
{
lean_object* v_snd_3653_; lean_object* v___x_3655_; 
v_snd_3653_ = lean_ctor_get(v_val_3649_, 1);
lean_inc(v_snd_3653_);
lean_dec(v_val_3649_);
if (v_isShared_3652_ == 0)
{
lean_ctor_set(v___x_3651_, 0, v_snd_3653_);
v___x_3655_ = v___x_3651_;
goto v_reusejp_3654_;
}
else
{
lean_object* v_reuseFailAlloc_3656_; 
v_reuseFailAlloc_3656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3656_, 0, v_snd_3653_);
v___x_3655_ = v_reuseFailAlloc_3656_;
goto v_reusejp_3654_;
}
v_reusejp_3654_:
{
return v___x_3655_;
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
LEAN_EXPORT lean_object* l_Lean_EnumAttributes_getValue(lean_object* v_00_u03b1_3661_, lean_object* v_inst_3662_, lean_object* v_attr_3663_, lean_object* v_env_3664_, lean_object* v_decl_3665_){
_start:
{
lean_object* v___x_3666_; 
v___x_3666_ = l_Lean_EnumAttributes_getValue___redArg(v_inst_3662_, v_attr_3663_, v_env_3664_, v_decl_3665_);
return v___x_3666_;
}
}
LEAN_EXPORT lean_object* l_Lean_EnumAttributes_setValue___redArg(lean_object* v_attrs_3675_, lean_object* v_env_3676_, lean_object* v_decl_3677_, lean_object* v_val_3678_){
_start:
{
lean_object* v_ext_3679_; lean_object* v___x_3681_; uint8_t v_isShared_3682_; uint8_t v_isSharedCheck_3743_; 
v_ext_3679_ = lean_ctor_get(v_attrs_3675_, 1);
v_isSharedCheck_3743_ = !lean_is_exclusive(v_attrs_3675_);
if (v_isSharedCheck_3743_ == 0)
{
lean_object* v_unused_3744_; 
v_unused_3744_ = lean_ctor_get(v_attrs_3675_, 0);
lean_dec(v_unused_3744_);
v___x_3681_ = v_attrs_3675_;
v_isShared_3682_ = v_isSharedCheck_3743_;
goto v_resetjp_3680_;
}
else
{
lean_inc(v_ext_3679_);
lean_dec(v_attrs_3675_);
v___x_3681_ = lean_box(0);
v_isShared_3682_ = v_isSharedCheck_3743_;
goto v_resetjp_3680_;
}
v_resetjp_3680_:
{
lean_object* v_toEnvExtension_3683_; lean_object* v_name_3684_; lean_object* v___x_3685_; uint8_t v___x_3686_; lean_object* v___x_3687_; lean_object* v___x_3688_; lean_object* v___x_3689_; lean_object* v___x_3690_; lean_object* v___x_3691_; lean_object* v___x_3692_; lean_object* v___x_3693_; lean_object* v_pfx_3694_; lean_object* v___x_3695_; 
v_toEnvExtension_3683_ = lean_ctor_get(v_ext_3679_, 0);
v_name_3684_ = lean_ctor_get(v_ext_3679_, 1);
v___x_3685_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__0));
v___x_3686_ = 1;
lean_inc(v_name_3684_);
v___x_3687_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_3684_, v___x_3686_);
v___x_3688_ = lean_string_append(v___x_3685_, v___x_3687_);
lean_dec_ref(v___x_3687_);
v___x_3689_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__1));
v___x_3690_ = lean_string_append(v___x_3688_, v___x_3689_);
lean_inc(v_decl_3677_);
v___x_3691_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_decl_3677_, v___x_3686_);
v___x_3692_ = lean_string_append(v___x_3690_, v___x_3691_);
lean_dec_ref(v___x_3691_);
v___x_3693_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__4));
v_pfx_3694_ = lean_string_append(v___x_3692_, v___x_3693_);
v___x_3695_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3676_, v_decl_3677_);
if (lean_obj_tag(v___x_3695_) == 0)
{
lean_object* v_asyncMode_3696_; uint8_t v___x_3703_; 
v_asyncMode_3696_ = lean_ctor_get(v_toEnvExtension_3683_, 2);
lean_inc(v_asyncMode_3696_);
lean_inc(v_decl_3677_);
lean_inc_ref(v_env_3676_);
v___x_3703_ = l_Lean_EnvExtension_asyncMayModify___redArg(v_env_3676_, v_decl_3677_, v_asyncMode_3696_);
if (v___x_3703_ == 0)
{
lean_object* v___x_3704_; lean_object* v___x_3705_; lean_object* v___y_3707_; lean_object* v___x_3711_; 
lean_dec(v_asyncMode_3696_);
lean_del_object(v___x_3681_);
lean_dec_ref(v_ext_3679_);
lean_dec(v_val_3678_);
lean_dec(v_decl_3677_);
v___x_3704_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__2));
v___x_3705_ = lean_string_append(v_pfx_3694_, v___x_3704_);
v___x_3711_ = l_Lean_Environment_asyncPrefix_x3f(v_env_3676_);
if (lean_obj_tag(v___x_3711_) == 0)
{
lean_object* v___x_3712_; 
v___x_3712_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__3));
v___y_3707_ = v___x_3712_;
goto v___jp_3706_;
}
else
{
lean_object* v_val_3713_; lean_object* v___x_3714_; lean_object* v___x_3715_; lean_object* v___x_3716_; lean_object* v___x_3717_; lean_object* v___x_3718_; lean_object* v___x_3719_; 
v_val_3713_ = lean_ctor_get(v___x_3711_, 0);
lean_inc(v_val_3713_);
lean_dec_ref(v___x_3711_);
v___x_3714_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__4));
v___x_3715_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_val_3713_, v___x_3686_);
v___x_3716_ = l_addParenHeuristic(v___x_3715_);
v___x_3717_ = lean_string_append(v___x_3714_, v___x_3716_);
lean_dec_ref(v___x_3716_);
v___x_3718_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__5));
v___x_3719_ = lean_string_append(v___x_3717_, v___x_3718_);
v___y_3707_ = v___x_3719_;
goto v___jp_3706_;
}
v___jp_3706_:
{
lean_object* v___x_3708_; lean_object* v___x_3709_; lean_object* v___x_3710_; 
v___x_3708_ = lean_string_append(v___x_3705_, v___y_3707_);
lean_dec_ref(v___y_3707_);
v___x_3709_ = lean_string_append(v___x_3708_, v___x_3693_);
v___x_3710_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3710_, 0, v___x_3709_);
return v___x_3710_;
}
}
else
{
lean_object* v___x_3720_; lean_object* v___x_3721_; lean_object* v___x_3722_; 
v___x_3720_ = lean_box(1);
lean_inc(v_decl_3677_);
lean_inc_ref(v_env_3676_);
v___x_3721_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3720_, v_ext_3679_, v_env_3676_, v_asyncMode_3696_, v_decl_3677_);
v___x_3722_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_3721_, v_decl_3677_);
lean_dec(v___x_3721_);
if (lean_obj_tag(v___x_3722_) == 0)
{
lean_dec_ref(v_pfx_3694_);
goto v___jp_3697_;
}
else
{
lean_object* v___x_3724_; uint8_t v_isShared_3725_; uint8_t v_isSharedCheck_3731_; 
v_isSharedCheck_3731_ = !lean_is_exclusive(v___x_3722_);
if (v_isSharedCheck_3731_ == 0)
{
lean_object* v_unused_3732_; 
v_unused_3732_ = lean_ctor_get(v___x_3722_, 0);
lean_dec(v_unused_3732_);
v___x_3724_ = v___x_3722_;
v_isShared_3725_ = v_isSharedCheck_3731_;
goto v_resetjp_3723_;
}
else
{
lean_dec(v___x_3722_);
v___x_3724_ = lean_box(0);
v_isShared_3725_ = v_isSharedCheck_3731_;
goto v_resetjp_3723_;
}
v_resetjp_3723_:
{
if (v___x_3703_ == 0)
{
lean_del_object(v___x_3724_);
lean_dec_ref(v_pfx_3694_);
goto v___jp_3697_;
}
else
{
lean_object* v___x_3726_; lean_object* v___x_3727_; lean_object* v___x_3729_; 
lean_dec(v_asyncMode_3696_);
lean_del_object(v___x_3681_);
lean_dec_ref(v_ext_3679_);
lean_dec(v_val_3678_);
lean_dec(v_decl_3677_);
lean_dec_ref(v_env_3676_);
v___x_3726_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__6));
v___x_3727_ = lean_string_append(v_pfx_3694_, v___x_3726_);
if (v_isShared_3725_ == 0)
{
lean_ctor_set_tag(v___x_3724_, 0);
lean_ctor_set(v___x_3724_, 0, v___x_3727_);
v___x_3729_ = v___x_3724_;
goto v_reusejp_3728_;
}
else
{
lean_object* v_reuseFailAlloc_3730_; 
v_reuseFailAlloc_3730_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3730_, 0, v___x_3727_);
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
v___jp_3697_:
{
lean_object* v___x_3699_; 
lean_inc(v_decl_3677_);
if (v_isShared_3682_ == 0)
{
lean_ctor_set(v___x_3681_, 1, v_val_3678_);
lean_ctor_set(v___x_3681_, 0, v_decl_3677_);
v___x_3699_ = v___x_3681_;
goto v_reusejp_3698_;
}
else
{
lean_object* v_reuseFailAlloc_3702_; 
v_reuseFailAlloc_3702_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3702_, 0, v_decl_3677_);
lean_ctor_set(v_reuseFailAlloc_3702_, 1, v_val_3678_);
v___x_3699_ = v_reuseFailAlloc_3702_;
goto v_reusejp_3698_;
}
v_reusejp_3698_:
{
lean_object* v___x_3700_; lean_object* v___x_3701_; 
v___x_3700_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_ext_3679_, v_env_3676_, v___x_3699_, v_asyncMode_3696_, v_decl_3677_);
lean_dec(v_asyncMode_3696_);
v___x_3701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3701_, 0, v___x_3700_);
return v___x_3701_;
}
}
}
else
{
lean_object* v___x_3734_; uint8_t v_isShared_3735_; uint8_t v_isSharedCheck_3741_; 
lean_del_object(v___x_3681_);
lean_dec_ref(v_ext_3679_);
lean_dec(v_val_3678_);
lean_dec(v_decl_3677_);
lean_dec_ref(v_env_3676_);
v_isSharedCheck_3741_ = !lean_is_exclusive(v___x_3695_);
if (v_isSharedCheck_3741_ == 0)
{
lean_object* v_unused_3742_; 
v_unused_3742_ = lean_ctor_get(v___x_3695_, 0);
lean_dec(v_unused_3742_);
v___x_3734_ = v___x_3695_;
v_isShared_3735_ = v_isSharedCheck_3741_;
goto v_resetjp_3733_;
}
else
{
lean_dec(v___x_3695_);
v___x_3734_ = lean_box(0);
v_isShared_3735_ = v_isSharedCheck_3741_;
goto v_resetjp_3733_;
}
v_resetjp_3733_:
{
lean_object* v___x_3736_; lean_object* v___x_3737_; lean_object* v___x_3739_; 
v___x_3736_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__7));
v___x_3737_ = lean_string_append(v_pfx_3694_, v___x_3736_);
if (v_isShared_3735_ == 0)
{
lean_ctor_set_tag(v___x_3734_, 0);
lean_ctor_set(v___x_3734_, 0, v___x_3737_);
v___x_3739_ = v___x_3734_;
goto v_reusejp_3738_;
}
else
{
lean_object* v_reuseFailAlloc_3740_; 
v_reuseFailAlloc_3740_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3740_, 0, v___x_3737_);
v___x_3739_ = v_reuseFailAlloc_3740_;
goto v_reusejp_3738_;
}
v_reusejp_3738_:
{
return v___x_3739_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_EnumAttributes_setValue(lean_object* v_00_u03b1_3745_, lean_object* v_attrs_3746_, lean_object* v_env_3747_, lean_object* v_decl_3748_, lean_object* v_val_3749_){
_start:
{
lean_object* v___x_3750_; 
v___x_3750_ = l_Lean_EnumAttributes_setValue___redArg(v_attrs_3746_, v_env_3747_, v_decl_3748_, v_val_3749_);
return v___x_3750_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_2990505691____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3752_; lean_object* v___x_3753_; lean_object* v___x_3754_; 
v___x_3752_ = lean_obj_once(&l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_, &l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2__once, _init_l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_);
v___x_3753_ = lean_st_mk_ref(v___x_3752_);
v___x_3754_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3754_, 0, v___x_3753_);
return v___x_3754_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_2990505691____hygCtx___hyg_2____boxed(lean_object* v_a_3755_){
_start:
{
lean_object* v_res_3756_; 
v_res_3756_ = l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_2990505691____hygCtx___hyg_2_();
return v_res_3756_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerAttributeImplBuilder(lean_object* v_builderId_3759_, lean_object* v_builder_3760_){
_start:
{
lean_object* v___x_3762_; lean_object* v___x_3763_; uint8_t v___x_3764_; 
v___x_3762_ = l_Lean_attributeImplBuilderTableRef;
v___x_3763_ = lean_st_ref_get(v___x_3762_);
v___x_3764_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(v___x_3763_, v_builderId_3759_);
lean_dec(v___x_3763_);
if (v___x_3764_ == 0)
{
lean_object* v___x_3765_; lean_object* v___x_3766_; lean_object* v___x_3767_; lean_object* v___x_3768_; 
v___x_3765_ = lean_st_ref_take(v___x_3762_);
v___x_3766_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1___redArg(v___x_3765_, v_builderId_3759_, v_builder_3760_);
v___x_3767_ = lean_st_ref_set(v___x_3762_, v___x_3766_);
v___x_3768_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3768_, 0, v___x_3767_);
return v___x_3768_;
}
else
{
lean_object* v___x_3769_; lean_object* v___x_3770_; lean_object* v___x_3771_; lean_object* v___x_3772_; lean_object* v___x_3773_; lean_object* v___x_3774_; lean_object* v___x_3775_; 
lean_dec_ref(v_builder_3760_);
v___x_3769_ = ((lean_object*)(l_Lean_registerAttributeImplBuilder___closed__0));
v___x_3770_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_builderId_3759_, v___x_3764_);
v___x_3771_ = lean_string_append(v___x_3769_, v___x_3770_);
lean_dec_ref(v___x_3770_);
v___x_3772_ = ((lean_object*)(l_Lean_registerAttributeImplBuilder___closed__1));
v___x_3773_ = lean_string_append(v___x_3771_, v___x_3772_);
v___x_3774_ = lean_mk_io_user_error(v___x_3773_);
v___x_3775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3775_, 0, v___x_3774_);
return v___x_3775_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerAttributeImplBuilder___boxed(lean_object* v_builderId_3776_, lean_object* v_builder_3777_, lean_object* v_a_3778_){
_start:
{
lean_object* v_res_3779_; 
v_res_3779_ = l_Lean_registerAttributeImplBuilder(v_builderId_3776_, v_builder_3777_);
return v_res_3779_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___redArg(lean_object* v_e_3780_){
_start:
{
if (lean_obj_tag(v_e_3780_) == 0)
{
lean_object* v_a_3782_; lean_object* v___x_3784_; uint8_t v_isShared_3785_; uint8_t v_isSharedCheck_3790_; 
v_a_3782_ = lean_ctor_get(v_e_3780_, 0);
v_isSharedCheck_3790_ = !lean_is_exclusive(v_e_3780_);
if (v_isSharedCheck_3790_ == 0)
{
v___x_3784_ = v_e_3780_;
v_isShared_3785_ = v_isSharedCheck_3790_;
goto v_resetjp_3783_;
}
else
{
lean_inc(v_a_3782_);
lean_dec(v_e_3780_);
v___x_3784_ = lean_box(0);
v_isShared_3785_ = v_isSharedCheck_3790_;
goto v_resetjp_3783_;
}
v_resetjp_3783_:
{
lean_object* v___x_3786_; lean_object* v___x_3788_; 
v___x_3786_ = lean_mk_io_user_error(v_a_3782_);
if (v_isShared_3785_ == 0)
{
lean_ctor_set_tag(v___x_3784_, 1);
lean_ctor_set(v___x_3784_, 0, v___x_3786_);
v___x_3788_ = v___x_3784_;
goto v_reusejp_3787_;
}
else
{
lean_object* v_reuseFailAlloc_3789_; 
v_reuseFailAlloc_3789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3789_, 0, v___x_3786_);
v___x_3788_ = v_reuseFailAlloc_3789_;
goto v_reusejp_3787_;
}
v_reusejp_3787_:
{
return v___x_3788_;
}
}
}
else
{
lean_object* v_a_3791_; lean_object* v___x_3793_; uint8_t v_isShared_3794_; uint8_t v_isSharedCheck_3798_; 
v_a_3791_ = lean_ctor_get(v_e_3780_, 0);
v_isSharedCheck_3798_ = !lean_is_exclusive(v_e_3780_);
if (v_isSharedCheck_3798_ == 0)
{
v___x_3793_ = v_e_3780_;
v_isShared_3794_ = v_isSharedCheck_3798_;
goto v_resetjp_3792_;
}
else
{
lean_inc(v_a_3791_);
lean_dec(v_e_3780_);
v___x_3793_ = lean_box(0);
v_isShared_3794_ = v_isSharedCheck_3798_;
goto v_resetjp_3792_;
}
v_resetjp_3792_:
{
lean_object* v___x_3796_; 
if (v_isShared_3794_ == 0)
{
lean_ctor_set_tag(v___x_3793_, 0);
v___x_3796_ = v___x_3793_;
goto v_reusejp_3795_;
}
else
{
lean_object* v_reuseFailAlloc_3797_; 
v_reuseFailAlloc_3797_ = lean_alloc_ctor(0, 1, 0);
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
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___redArg___boxed(lean_object* v_e_3799_, lean_object* v_a_3800_){
_start:
{
lean_object* v_res_3801_; 
v_res_3801_ = l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___redArg(v_e_3799_);
return v_res_3801_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1(lean_object* v_00_u03b1_3802_, lean_object* v_e_3803_){
_start:
{
lean_object* v___x_3805_; 
v___x_3805_ = l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___redArg(v_e_3803_);
return v___x_3805_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___boxed(lean_object* v_00_u03b1_3806_, lean_object* v_e_3807_, lean_object* v_a_3808_){
_start:
{
lean_object* v_res_3809_; 
v_res_3809_ = l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1(v_00_u03b1_3806_, v_e_3807_);
return v_res_3809_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___redArg(lean_object* v_a_3810_, lean_object* v_x_3811_){
_start:
{
if (lean_obj_tag(v_x_3811_) == 0)
{
lean_object* v___x_3812_; 
v___x_3812_ = lean_box(0);
return v___x_3812_;
}
else
{
lean_object* v_key_3813_; lean_object* v_value_3814_; lean_object* v_tail_3815_; uint8_t v___x_3816_; 
v_key_3813_ = lean_ctor_get(v_x_3811_, 0);
v_value_3814_ = lean_ctor_get(v_x_3811_, 1);
v_tail_3815_ = lean_ctor_get(v_x_3811_, 2);
v___x_3816_ = lean_name_eq(v_key_3813_, v_a_3810_);
if (v___x_3816_ == 0)
{
v_x_3811_ = v_tail_3815_;
goto _start;
}
else
{
lean_object* v___x_3818_; 
lean_inc(v_value_3814_);
v___x_3818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3818_, 0, v_value_3814_);
return v___x_3818_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___redArg___boxed(lean_object* v_a_3819_, lean_object* v_x_3820_){
_start:
{
lean_object* v_res_3821_; 
v_res_3821_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___redArg(v_a_3819_, v_x_3820_);
lean_dec(v_x_3820_);
lean_dec(v_a_3819_);
return v_res_3821_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(lean_object* v_m_3822_, lean_object* v_a_3823_){
_start:
{
lean_object* v_buckets_3824_; lean_object* v___x_3825_; uint64_t v___y_3827_; 
v_buckets_3824_ = lean_ctor_get(v_m_3822_, 1);
v___x_3825_ = lean_array_get_size(v_buckets_3824_);
if (lean_obj_tag(v_a_3823_) == 0)
{
uint64_t v___x_3841_; 
v___x_3841_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg___closed__0);
v___y_3827_ = v___x_3841_;
goto v___jp_3826_;
}
else
{
uint64_t v_hash_3842_; 
v_hash_3842_ = lean_ctor_get_uint64(v_a_3823_, sizeof(void*)*2);
v___y_3827_ = v_hash_3842_;
goto v___jp_3826_;
}
v___jp_3826_:
{
uint64_t v___x_3828_; uint64_t v___x_3829_; uint64_t v_fold_3830_; uint64_t v___x_3831_; uint64_t v___x_3832_; uint64_t v___x_3833_; size_t v___x_3834_; size_t v___x_3835_; size_t v___x_3836_; size_t v___x_3837_; size_t v___x_3838_; lean_object* v___x_3839_; lean_object* v___x_3840_; 
v___x_3828_ = 32ULL;
v___x_3829_ = lean_uint64_shift_right(v___y_3827_, v___x_3828_);
v_fold_3830_ = lean_uint64_xor(v___y_3827_, v___x_3829_);
v___x_3831_ = 16ULL;
v___x_3832_ = lean_uint64_shift_right(v_fold_3830_, v___x_3831_);
v___x_3833_ = lean_uint64_xor(v_fold_3830_, v___x_3832_);
v___x_3834_ = lean_uint64_to_usize(v___x_3833_);
v___x_3835_ = lean_usize_of_nat(v___x_3825_);
v___x_3836_ = ((size_t)1ULL);
v___x_3837_ = lean_usize_sub(v___x_3835_, v___x_3836_);
v___x_3838_ = lean_usize_land(v___x_3834_, v___x_3837_);
v___x_3839_ = lean_array_uget_borrowed(v_buckets_3824_, v___x_3838_);
v___x_3840_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___redArg(v_a_3823_, v___x_3839_);
return v___x_3840_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg___boxed(lean_object* v_m_3843_, lean_object* v_a_3844_){
_start:
{
lean_object* v_res_3845_; 
v_res_3845_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(v_m_3843_, v_a_3844_);
lean_dec(v_a_3844_);
lean_dec_ref(v_m_3843_);
return v_res_3845_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAttributeImplOfEntry(lean_object* v_e_3847_){
_start:
{
lean_object* v___x_3849_; lean_object* v___x_3850_; lean_object* v_builderId_3851_; lean_object* v_ref_3852_; lean_object* v_args_3853_; lean_object* v___x_3854_; 
v___x_3849_ = l_Lean_attributeImplBuilderTableRef;
v___x_3850_ = lean_st_ref_get(v___x_3849_);
v_builderId_3851_ = lean_ctor_get(v_e_3847_, 0);
lean_inc(v_builderId_3851_);
v_ref_3852_ = lean_ctor_get(v_e_3847_, 1);
lean_inc(v_ref_3852_);
v_args_3853_ = lean_ctor_get(v_e_3847_, 2);
lean_inc(v_args_3853_);
lean_dec_ref(v_e_3847_);
v___x_3854_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(v___x_3850_, v_builderId_3851_);
lean_dec(v___x_3850_);
if (lean_obj_tag(v___x_3854_) == 0)
{
lean_object* v___x_3855_; uint8_t v___x_3856_; lean_object* v___x_3857_; lean_object* v___x_3858_; lean_object* v___x_3859_; lean_object* v___x_3860_; lean_object* v___x_3861_; lean_object* v___x_3862_; 
lean_dec(v_args_3853_);
lean_dec(v_ref_3852_);
v___x_3855_ = ((lean_object*)(l_Lean_mkAttributeImplOfEntry___closed__0));
v___x_3856_ = 1;
v___x_3857_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_builderId_3851_, v___x_3856_);
v___x_3858_ = lean_string_append(v___x_3855_, v___x_3857_);
lean_dec_ref(v___x_3857_);
v___x_3859_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__4));
v___x_3860_ = lean_string_append(v___x_3858_, v___x_3859_);
v___x_3861_ = lean_mk_io_user_error(v___x_3860_);
v___x_3862_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3862_, 0, v___x_3861_);
return v___x_3862_;
}
else
{
lean_object* v_val_3863_; lean_object* v___x_3864_; lean_object* v___x_3865_; 
lean_dec(v_builderId_3851_);
v_val_3863_ = lean_ctor_get(v___x_3854_, 0);
lean_inc(v_val_3863_);
lean_dec_ref(v___x_3854_);
v___x_3864_ = lean_apply_2(v_val_3863_, v_ref_3852_, v_args_3853_);
v___x_3865_ = l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___redArg(v___x_3864_);
return v___x_3865_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkAttributeImplOfEntry___boxed(lean_object* v_e_3866_, lean_object* v_a_3867_){
_start:
{
lean_object* v_res_3868_; 
v_res_3868_ = l_Lean_mkAttributeImplOfEntry(v_e_3866_);
return v_res_3868_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0(lean_object* v_00_u03b2_3869_, lean_object* v_m_3870_, lean_object* v_a_3871_){
_start:
{
lean_object* v___x_3872_; 
v___x_3872_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(v_m_3870_, v_a_3871_);
return v___x_3872_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___boxed(lean_object* v_00_u03b2_3873_, lean_object* v_m_3874_, lean_object* v_a_3875_){
_start:
{
lean_object* v_res_3876_; 
v_res_3876_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0(v_00_u03b2_3873_, v_m_3874_, v_a_3875_);
lean_dec(v_a_3875_);
lean_dec_ref(v_m_3874_);
return v_res_3876_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0(lean_object* v_00_u03b2_3877_, lean_object* v_a_3878_, lean_object* v_x_3879_){
_start:
{
lean_object* v___x_3880_; 
v___x_3880_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___redArg(v_a_3878_, v_x_3879_);
return v___x_3880_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3881_, lean_object* v_a_3882_, lean_object* v_x_3883_){
_start:
{
lean_object* v_res_3884_; 
v_res_3884_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0(v_00_u03b2_3881_, v_a_3882_, v_x_3883_);
lean_dec(v_x_3883_);
lean_dec(v_a_3882_);
return v_res_3884_;
}
}
static lean_object* _init_l_Lean_instInhabitedAttributeExtensionState_default___closed__0(void){
_start:
{
lean_object* v___x_3885_; lean_object* v___x_3886_; lean_object* v___x_3887_; 
v___x_3885_ = lean_obj_once(&l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_, &l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2__once, _init_l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_);
v___x_3886_ = lean_box(0);
v___x_3887_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3887_, 0, v___x_3886_);
lean_ctor_set(v___x_3887_, 1, v___x_3885_);
return v___x_3887_;
}
}
static lean_object* _init_l_Lean_instInhabitedAttributeExtensionState_default(void){
_start:
{
lean_object* v___x_3888_; 
v___x_3888_ = lean_obj_once(&l_Lean_instInhabitedAttributeExtensionState_default___closed__0, &l_Lean_instInhabitedAttributeExtensionState_default___closed__0_once, _init_l_Lean_instInhabitedAttributeExtensionState_default___closed__0);
return v___x_3888_;
}
}
static lean_object* _init_l_Lean_instInhabitedAttributeExtensionState(void){
_start:
{
lean_object* v___x_3889_; 
v___x_3889_ = l_Lean_instInhabitedAttributeExtensionState_default;
return v___x_3889_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_AttributeExtension_mkInitial(){
_start:
{
lean_object* v___x_3891_; lean_object* v___x_3892_; lean_object* v___x_3893_; lean_object* v___x_3894_; lean_object* v___x_3895_; 
v___x_3891_ = l_Lean_attributeMapRef;
v___x_3892_ = lean_st_ref_get(v___x_3891_);
v___x_3893_ = lean_box(0);
v___x_3894_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3894_, 0, v___x_3893_);
lean_ctor_set(v___x_3894_, 1, v___x_3892_);
v___x_3895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3895_, 0, v___x_3894_);
return v___x_3895_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_AttributeExtension_mkInitial___boxed(lean_object* v_a_3896_){
_start:
{
lean_object* v_res_3897_; 
v_res_3897_ = l___private_Lean_Attributes_0__Lean_AttributeExtension_mkInitial();
return v_res_3897_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAttributeImplOfConstantUnsafe(lean_object* v_env_3903_, lean_object* v_opts_3904_, lean_object* v_declName_3905_){
_start:
{
uint8_t v___x_3908_; lean_object* v___x_3909_; 
v___x_3908_ = 0;
lean_inc(v_declName_3905_);
lean_inc_ref(v_env_3903_);
v___x_3909_ = l_Lean_Environment_find_x3f(v_env_3903_, v_declName_3905_, v___x_3908_);
if (lean_obj_tag(v___x_3909_) == 0)
{
lean_object* v___x_3910_; uint8_t v___x_3911_; lean_object* v___x_3912_; lean_object* v___x_3913_; lean_object* v___x_3914_; lean_object* v___x_3915_; lean_object* v___x_3916_; 
lean_dec_ref(v_env_3903_);
v___x_3910_ = ((lean_object*)(l_Lean_mkAttributeImplOfConstantUnsafe___closed__2));
v___x_3911_ = 1;
v___x_3912_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_declName_3905_, v___x_3911_);
v___x_3913_ = lean_string_append(v___x_3910_, v___x_3912_);
lean_dec_ref(v___x_3912_);
v___x_3914_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__4));
v___x_3915_ = lean_string_append(v___x_3913_, v___x_3914_);
v___x_3916_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3916_, 0, v___x_3915_);
return v___x_3916_;
}
else
{
lean_object* v_val_3917_; lean_object* v___x_3918_; 
v_val_3917_ = lean_ctor_get(v___x_3909_, 0);
lean_inc(v_val_3917_);
lean_dec_ref(v___x_3909_);
v___x_3918_ = l_Lean_ConstantInfo_type(v_val_3917_);
lean_dec(v_val_3917_);
if (lean_obj_tag(v___x_3918_) == 4)
{
lean_object* v_declName_3919_; 
v_declName_3919_ = lean_ctor_get(v___x_3918_, 0);
lean_inc(v_declName_3919_);
lean_dec_ref(v___x_3918_);
if (lean_obj_tag(v_declName_3919_) == 1)
{
lean_object* v_pre_3920_; 
v_pre_3920_ = lean_ctor_get(v_declName_3919_, 0);
lean_inc(v_pre_3920_);
if (lean_obj_tag(v_pre_3920_) == 1)
{
lean_object* v_pre_3921_; 
v_pre_3921_ = lean_ctor_get(v_pre_3920_, 0);
if (lean_obj_tag(v_pre_3921_) == 0)
{
lean_object* v_str_3922_; lean_object* v_str_3923_; lean_object* v___x_3924_; uint8_t v___x_3925_; 
v_str_3922_ = lean_ctor_get(v_declName_3919_, 1);
lean_inc_ref(v_str_3922_);
lean_dec_ref(v_declName_3919_);
v_str_3923_ = lean_ctor_get(v_pre_3920_, 1);
lean_inc_ref(v_str_3923_);
lean_dec_ref(v_pre_3920_);
v___x_3924_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__0));
v___x_3925_ = lean_string_dec_eq(v_str_3923_, v___x_3924_);
lean_dec_ref(v_str_3923_);
if (v___x_3925_ == 0)
{
lean_dec_ref(v_str_3922_);
lean_dec(v_declName_3905_);
lean_dec_ref(v_env_3903_);
goto v___jp_3906_;
}
else
{
lean_object* v___x_3926_; uint8_t v___x_3927_; 
v___x_3926_ = ((lean_object*)(l_Lean_mkAttributeImplOfConstantUnsafe___closed__3));
v___x_3927_ = lean_string_dec_eq(v_str_3922_, v___x_3926_);
lean_dec_ref(v_str_3922_);
if (v___x_3927_ == 0)
{
lean_dec(v_declName_3905_);
lean_dec_ref(v_env_3903_);
goto v___jp_3906_;
}
else
{
lean_object* v___x_3928_; 
v___x_3928_ = l_Lean_Environment_evalConst___redArg(v_env_3903_, v_opts_3904_, v_declName_3905_, v___x_3927_);
lean_dec(v_declName_3905_);
lean_dec_ref(v_env_3903_);
return v___x_3928_;
}
}
}
else
{
lean_dec_ref(v_pre_3920_);
lean_dec_ref(v_declName_3919_);
lean_dec(v_declName_3905_);
lean_dec_ref(v_env_3903_);
goto v___jp_3906_;
}
}
else
{
lean_dec(v_pre_3920_);
lean_dec_ref(v_declName_3919_);
lean_dec(v_declName_3905_);
lean_dec_ref(v_env_3903_);
goto v___jp_3906_;
}
}
else
{
lean_dec(v_declName_3919_);
lean_dec(v_declName_3905_);
lean_dec_ref(v_env_3903_);
goto v___jp_3906_;
}
}
else
{
lean_dec_ref(v___x_3918_);
lean_dec(v_declName_3905_);
lean_dec_ref(v_env_3903_);
goto v___jp_3906_;
}
}
v___jp_3906_:
{
lean_object* v___x_3907_; 
v___x_3907_ = ((lean_object*)(l_Lean_mkAttributeImplOfConstantUnsafe___closed__1));
return v___x_3907_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkAttributeImplOfConstantUnsafe___boxed(lean_object* v_env_3929_, lean_object* v_opts_3930_, lean_object* v_declName_3931_){
_start:
{
lean_object* v_res_3932_; 
v_res_3932_ = l_Lean_mkAttributeImplOfConstantUnsafe(v_env_3929_, v_opts_3930_, v_declName_3931_);
lean_dec_ref(v_opts_3930_);
return v_res_3932_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg(lean_object* v_as_3933_, size_t v_i_3934_, size_t v_stop_3935_, lean_object* v_b_3936_){
_start:
{
uint8_t v___x_3938_; 
v___x_3938_ = lean_usize_dec_eq(v_i_3934_, v_stop_3935_);
if (v___x_3938_ == 0)
{
lean_object* v___x_3939_; lean_object* v___x_3940_; 
v___x_3939_ = lean_array_uget_borrowed(v_as_3933_, v_i_3934_);
lean_inc(v___x_3939_);
v___x_3940_ = l_Lean_mkAttributeImplOfEntry(v___x_3939_);
if (lean_obj_tag(v___x_3940_) == 0)
{
lean_object* v_a_3941_; lean_object* v_toAttributeImplCore_3942_; lean_object* v_name_3943_; lean_object* v___x_3944_; size_t v___x_3945_; size_t v___x_3946_; 
v_a_3941_ = lean_ctor_get(v___x_3940_, 0);
lean_inc(v_a_3941_);
lean_dec_ref(v___x_3940_);
v_toAttributeImplCore_3942_ = lean_ctor_get(v_a_3941_, 0);
v_name_3943_ = lean_ctor_get(v_toAttributeImplCore_3942_, 1);
lean_inc(v_name_3943_);
v___x_3944_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1___redArg(v_b_3936_, v_name_3943_, v_a_3941_);
v___x_3945_ = ((size_t)1ULL);
v___x_3946_ = lean_usize_add(v_i_3934_, v___x_3945_);
v_i_3934_ = v___x_3946_;
v_b_3936_ = v___x_3944_;
goto _start;
}
else
{
lean_object* v_a_3948_; lean_object* v___x_3950_; uint8_t v_isShared_3951_; uint8_t v_isSharedCheck_3955_; 
lean_dec_ref(v_b_3936_);
v_a_3948_ = lean_ctor_get(v___x_3940_, 0);
v_isSharedCheck_3955_ = !lean_is_exclusive(v___x_3940_);
if (v_isSharedCheck_3955_ == 0)
{
v___x_3950_ = v___x_3940_;
v_isShared_3951_ = v_isSharedCheck_3955_;
goto v_resetjp_3949_;
}
else
{
lean_inc(v_a_3948_);
lean_dec(v___x_3940_);
v___x_3950_ = lean_box(0);
v_isShared_3951_ = v_isSharedCheck_3955_;
goto v_resetjp_3949_;
}
v_resetjp_3949_:
{
lean_object* v___x_3953_; 
if (v_isShared_3951_ == 0)
{
v___x_3953_ = v___x_3950_;
goto v_reusejp_3952_;
}
else
{
lean_object* v_reuseFailAlloc_3954_; 
v_reuseFailAlloc_3954_ = lean_alloc_ctor(1, 1, 0);
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
else
{
lean_object* v___x_3956_; 
v___x_3956_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3956_, 0, v_b_3936_);
return v___x_3956_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg___boxed(lean_object* v_as_3957_, lean_object* v_i_3958_, lean_object* v_stop_3959_, lean_object* v_b_3960_, lean_object* v___y_3961_){
_start:
{
size_t v_i_boxed_3962_; size_t v_stop_boxed_3963_; lean_object* v_res_3964_; 
v_i_boxed_3962_ = lean_unbox_usize(v_i_3958_);
lean_dec(v_i_3958_);
v_stop_boxed_3963_ = lean_unbox_usize(v_stop_3959_);
lean_dec(v_stop_3959_);
v_res_3964_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg(v_as_3957_, v_i_boxed_3962_, v_stop_boxed_3963_, v_b_3960_);
lean_dec_ref(v_as_3957_);
return v_res_3964_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__1(lean_object* v_as_3965_, size_t v_i_3966_, size_t v_stop_3967_, lean_object* v_b_3968_, lean_object* v___y_3969_){
_start:
{
lean_object* v_a_3972_; lean_object* v___y_3977_; uint8_t v___x_3979_; 
v___x_3979_ = lean_usize_dec_eq(v_i_3966_, v_stop_3967_);
if (v___x_3979_ == 0)
{
lean_object* v___x_3980_; lean_object* v___x_3981_; lean_object* v___x_3982_; uint8_t v___x_3983_; 
v___x_3980_ = lean_array_uget_borrowed(v_as_3965_, v_i_3966_);
v___x_3981_ = lean_unsigned_to_nat(0u);
v___x_3982_ = lean_array_get_size(v___x_3980_);
v___x_3983_ = lean_nat_dec_lt(v___x_3981_, v___x_3982_);
if (v___x_3983_ == 0)
{
v_a_3972_ = v_b_3968_;
goto v___jp_3971_;
}
else
{
uint8_t v___x_3984_; 
v___x_3984_ = lean_nat_dec_le(v___x_3982_, v___x_3982_);
if (v___x_3984_ == 0)
{
if (v___x_3983_ == 0)
{
v_a_3972_ = v_b_3968_;
goto v___jp_3971_;
}
else
{
size_t v___x_3985_; size_t v___x_3986_; lean_object* v___x_3987_; 
v___x_3985_ = ((size_t)0ULL);
v___x_3986_ = lean_usize_of_nat(v___x_3982_);
v___x_3987_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg(v___x_3980_, v___x_3985_, v___x_3986_, v_b_3968_);
v___y_3977_ = v___x_3987_;
goto v___jp_3976_;
}
}
else
{
size_t v___x_3988_; size_t v___x_3989_; lean_object* v___x_3990_; 
v___x_3988_ = ((size_t)0ULL);
v___x_3989_ = lean_usize_of_nat(v___x_3982_);
v___x_3990_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg(v___x_3980_, v___x_3988_, v___x_3989_, v_b_3968_);
v___y_3977_ = v___x_3990_;
goto v___jp_3976_;
}
}
}
else
{
lean_object* v___x_3991_; 
v___x_3991_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3991_, 0, v_b_3968_);
return v___x_3991_;
}
v___jp_3971_:
{
size_t v___x_3973_; size_t v___x_3974_; 
v___x_3973_ = ((size_t)1ULL);
v___x_3974_ = lean_usize_add(v_i_3966_, v___x_3973_);
v_i_3966_ = v___x_3974_;
v_b_3968_ = v_a_3972_;
goto _start;
}
v___jp_3976_:
{
if (lean_obj_tag(v___y_3977_) == 0)
{
lean_object* v_a_3978_; 
v_a_3978_ = lean_ctor_get(v___y_3977_, 0);
lean_inc(v_a_3978_);
lean_dec_ref(v___y_3977_);
v_a_3972_ = v_a_3978_;
goto v___jp_3971_;
}
else
{
return v___y_3977_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__1___boxed(lean_object* v_as_3992_, lean_object* v_i_3993_, lean_object* v_stop_3994_, lean_object* v_b_3995_, lean_object* v___y_3996_, lean_object* v___y_3997_){
_start:
{
size_t v_i_boxed_3998_; size_t v_stop_boxed_3999_; lean_object* v_res_4000_; 
v_i_boxed_3998_ = lean_unbox_usize(v_i_3993_);
lean_dec(v_i_3993_);
v_stop_boxed_3999_ = lean_unbox_usize(v_stop_3994_);
lean_dec(v_stop_3994_);
v_res_4000_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__1(v_as_3992_, v_i_boxed_3998_, v_stop_boxed_3999_, v_b_3995_, v___y_3996_);
lean_dec_ref(v___y_3996_);
lean_dec_ref(v_as_3992_);
return v_res_4000_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_AttributeExtension_addImported(lean_object* v_es_4001_, lean_object* v_a_4002_){
_start:
{
lean_object* v_a_4005_; lean_object* v___y_4010_; lean_object* v___x_4020_; lean_object* v___x_4021_; lean_object* v___x_4022_; lean_object* v___x_4023_; uint8_t v___x_4024_; 
v___x_4020_ = l_Lean_attributeMapRef;
v___x_4021_ = lean_st_ref_get(v___x_4020_);
v___x_4022_ = lean_unsigned_to_nat(0u);
v___x_4023_ = lean_array_get_size(v_es_4001_);
v___x_4024_ = lean_nat_dec_lt(v___x_4022_, v___x_4023_);
if (v___x_4024_ == 0)
{
v_a_4005_ = v___x_4021_;
goto v___jp_4004_;
}
else
{
uint8_t v___x_4025_; 
v___x_4025_ = lean_nat_dec_le(v___x_4023_, v___x_4023_);
if (v___x_4025_ == 0)
{
if (v___x_4024_ == 0)
{
v_a_4005_ = v___x_4021_;
goto v___jp_4004_;
}
else
{
size_t v___x_4026_; size_t v___x_4027_; lean_object* v___x_4028_; 
v___x_4026_ = ((size_t)0ULL);
v___x_4027_ = lean_usize_of_nat(v___x_4023_);
v___x_4028_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__1(v_es_4001_, v___x_4026_, v___x_4027_, v___x_4021_, v_a_4002_);
v___y_4010_ = v___x_4028_;
goto v___jp_4009_;
}
}
else
{
size_t v___x_4029_; size_t v___x_4030_; lean_object* v___x_4031_; 
v___x_4029_ = ((size_t)0ULL);
v___x_4030_ = lean_usize_of_nat(v___x_4023_);
v___x_4031_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__1(v_es_4001_, v___x_4029_, v___x_4030_, v___x_4021_, v_a_4002_);
v___y_4010_ = v___x_4031_;
goto v___jp_4009_;
}
}
v___jp_4004_:
{
lean_object* v___x_4006_; lean_object* v___x_4007_; lean_object* v___x_4008_; 
v___x_4006_ = lean_box(0);
v___x_4007_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4007_, 0, v___x_4006_);
lean_ctor_set(v___x_4007_, 1, v_a_4005_);
v___x_4008_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4008_, 0, v___x_4007_);
return v___x_4008_;
}
v___jp_4009_:
{
if (lean_obj_tag(v___y_4010_) == 0)
{
lean_object* v_a_4011_; 
v_a_4011_ = lean_ctor_get(v___y_4010_, 0);
lean_inc(v_a_4011_);
lean_dec_ref(v___y_4010_);
v_a_4005_ = v_a_4011_;
goto v___jp_4004_;
}
else
{
lean_object* v_a_4012_; lean_object* v___x_4014_; uint8_t v_isShared_4015_; uint8_t v_isSharedCheck_4019_; 
v_a_4012_ = lean_ctor_get(v___y_4010_, 0);
v_isSharedCheck_4019_ = !lean_is_exclusive(v___y_4010_);
if (v_isSharedCheck_4019_ == 0)
{
v___x_4014_ = v___y_4010_;
v_isShared_4015_ = v_isSharedCheck_4019_;
goto v_resetjp_4013_;
}
else
{
lean_inc(v_a_4012_);
lean_dec(v___y_4010_);
v___x_4014_ = lean_box(0);
v_isShared_4015_ = v_isSharedCheck_4019_;
goto v_resetjp_4013_;
}
v_resetjp_4013_:
{
lean_object* v___x_4017_; 
if (v_isShared_4015_ == 0)
{
v___x_4017_ = v___x_4014_;
goto v_reusejp_4016_;
}
else
{
lean_object* v_reuseFailAlloc_4018_; 
v_reuseFailAlloc_4018_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4018_, 0, v_a_4012_);
v___x_4017_ = v_reuseFailAlloc_4018_;
goto v_reusejp_4016_;
}
v_reusejp_4016_:
{
return v___x_4017_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_AttributeExtension_addImported___boxed(lean_object* v_es_4032_, lean_object* v_a_4033_, lean_object* v_a_4034_){
_start:
{
lean_object* v_res_4035_; 
v_res_4035_ = l___private_Lean_Attributes_0__Lean_AttributeExtension_addImported(v_es_4032_, v_a_4033_);
lean_dec_ref(v_a_4033_);
lean_dec_ref(v_es_4032_);
return v_res_4035_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0(lean_object* v_as_4036_, size_t v_i_4037_, size_t v_stop_4038_, lean_object* v_b_4039_, lean_object* v___y_4040_){
_start:
{
lean_object* v___x_4042_; 
v___x_4042_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg(v_as_4036_, v_i_4037_, v_stop_4038_, v_b_4039_);
return v___x_4042_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___boxed(lean_object* v_as_4043_, lean_object* v_i_4044_, lean_object* v_stop_4045_, lean_object* v_b_4046_, lean_object* v___y_4047_, lean_object* v___y_4048_){
_start:
{
size_t v_i_boxed_4049_; size_t v_stop_boxed_4050_; lean_object* v_res_4051_; 
v_i_boxed_4049_ = lean_unbox_usize(v_i_4044_);
lean_dec(v_i_4044_);
v_stop_boxed_4050_ = lean_unbox_usize(v_stop_4045_);
lean_dec(v_stop_4045_);
v_res_4051_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0(v_as_4043_, v_i_boxed_4049_, v_stop_boxed_4050_, v_b_4046_, v___y_4047_);
lean_dec_ref(v___y_4047_);
lean_dec_ref(v_as_4043_);
return v_res_4051_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_addAttrEntry(lean_object* v_s_4052_, lean_object* v_e_4053_){
_start:
{
lean_object* v_snd_4054_; lean_object* v_toAttributeImplCore_4055_; lean_object* v_fst_4056_; lean_object* v___x_4058_; uint8_t v_isShared_4059_; uint8_t v_isSharedCheck_4074_; 
v_snd_4054_ = lean_ctor_get(v_e_4053_, 1);
lean_inc(v_snd_4054_);
v_toAttributeImplCore_4055_ = lean_ctor_get(v_snd_4054_, 0);
v_fst_4056_ = lean_ctor_get(v_e_4053_, 0);
v_isSharedCheck_4074_ = !lean_is_exclusive(v_e_4053_);
if (v_isSharedCheck_4074_ == 0)
{
lean_object* v_unused_4075_; 
v_unused_4075_ = lean_ctor_get(v_e_4053_, 1);
lean_dec(v_unused_4075_);
v___x_4058_ = v_e_4053_;
v_isShared_4059_ = v_isSharedCheck_4074_;
goto v_resetjp_4057_;
}
else
{
lean_inc(v_fst_4056_);
lean_dec(v_e_4053_);
v___x_4058_ = lean_box(0);
v_isShared_4059_ = v_isSharedCheck_4074_;
goto v_resetjp_4057_;
}
v_resetjp_4057_:
{
lean_object* v_newEntries_4060_; lean_object* v_map_4061_; lean_object* v___x_4063_; uint8_t v_isShared_4064_; uint8_t v_isSharedCheck_4073_; 
v_newEntries_4060_ = lean_ctor_get(v_s_4052_, 0);
v_map_4061_ = lean_ctor_get(v_s_4052_, 1);
v_isSharedCheck_4073_ = !lean_is_exclusive(v_s_4052_);
if (v_isSharedCheck_4073_ == 0)
{
v___x_4063_ = v_s_4052_;
v_isShared_4064_ = v_isSharedCheck_4073_;
goto v_resetjp_4062_;
}
else
{
lean_inc(v_map_4061_);
lean_inc(v_newEntries_4060_);
lean_dec(v_s_4052_);
v___x_4063_ = lean_box(0);
v_isShared_4064_ = v_isSharedCheck_4073_;
goto v_resetjp_4062_;
}
v_resetjp_4062_:
{
lean_object* v_name_4065_; lean_object* v___x_4067_; 
v_name_4065_ = lean_ctor_get(v_toAttributeImplCore_4055_, 1);
lean_inc(v_name_4065_);
if (v_isShared_4059_ == 0)
{
lean_ctor_set_tag(v___x_4058_, 1);
lean_ctor_set(v___x_4058_, 1, v_newEntries_4060_);
v___x_4067_ = v___x_4058_;
goto v_reusejp_4066_;
}
else
{
lean_object* v_reuseFailAlloc_4072_; 
v_reuseFailAlloc_4072_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4072_, 0, v_fst_4056_);
lean_ctor_set(v_reuseFailAlloc_4072_, 1, v_newEntries_4060_);
v___x_4067_ = v_reuseFailAlloc_4072_;
goto v_reusejp_4066_;
}
v_reusejp_4066_:
{
lean_object* v___x_4068_; lean_object* v___x_4070_; 
v___x_4068_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1___redArg(v_map_4061_, v_name_4065_, v_snd_4054_);
if (v_isShared_4064_ == 0)
{
lean_ctor_set(v___x_4063_, 1, v___x_4068_);
lean_ctor_set(v___x_4063_, 0, v___x_4067_);
v___x_4070_ = v___x_4063_;
goto v_reusejp_4069_;
}
else
{
lean_object* v_reuseFailAlloc_4071_; 
v_reuseFailAlloc_4071_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4071_, 0, v___x_4067_);
lean_ctor_set(v_reuseFailAlloc_4071_, 1, v___x_4068_);
v___x_4070_ = v_reuseFailAlloc_4071_;
goto v_reusejp_4069_;
}
v_reusejp_4069_:
{
return v___x_4070_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn___lam__0_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(lean_object* v_x_4076_, lean_object* v_s_4077_){
_start:
{
lean_object* v_newEntries_4078_; lean_object* v___x_4079_; lean_object* v___x_4080_; lean_object* v___x_4081_; 
v_newEntries_4078_ = lean_ctor_get(v_s_4077_, 0);
lean_inc(v_newEntries_4078_);
lean_dec_ref(v_s_4077_);
v___x_4079_ = l_List_reverse___redArg(v_newEntries_4078_);
v___x_4080_ = lean_array_mk(v___x_4079_);
lean_inc_ref_n(v___x_4080_, 2);
v___x_4081_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4081_, 0, v___x_4080_);
lean_ctor_set(v___x_4081_, 1, v___x_4080_);
lean_ctor_set(v___x_4081_, 2, v___x_4080_);
return v___x_4081_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn___lam__0_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2____boxed(lean_object* v_x_4082_, lean_object* v_s_4083_){
_start:
{
lean_object* v_res_4084_; 
v_res_4084_ = l___private_Lean_Attributes_0__Lean_initFn___lam__0_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(v_x_4082_, v_s_4083_);
lean_dec_ref(v_x_4082_);
return v_res_4084_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn___lam__1_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(lean_object* v_s_4085_){
_start:
{
lean_object* v_newEntries_4086_; lean_object* v___x_4088_; uint8_t v_isShared_4089_; uint8_t v_isSharedCheck_4097_; 
v_newEntries_4086_ = lean_ctor_get(v_s_4085_, 0);
v_isSharedCheck_4097_ = !lean_is_exclusive(v_s_4085_);
if (v_isSharedCheck_4097_ == 0)
{
lean_object* v_unused_4098_; 
v_unused_4098_ = lean_ctor_get(v_s_4085_, 1);
lean_dec(v_unused_4098_);
v___x_4088_ = v_s_4085_;
v_isShared_4089_ = v_isSharedCheck_4097_;
goto v_resetjp_4087_;
}
else
{
lean_inc(v_newEntries_4086_);
lean_dec(v_s_4085_);
v___x_4088_ = lean_box(0);
v_isShared_4089_ = v_isSharedCheck_4097_;
goto v_resetjp_4087_;
}
v_resetjp_4087_:
{
lean_object* v___x_4090_; lean_object* v___x_4091_; lean_object* v___x_4092_; lean_object* v___x_4093_; lean_object* v___x_4095_; 
v___x_4090_ = ((lean_object*)(l_Lean_registerTagAttribute___lam__2___closed__4));
v___x_4091_ = l_List_lengthTR___redArg(v_newEntries_4086_);
lean_dec(v_newEntries_4086_);
v___x_4092_ = l_Nat_reprFast(v___x_4091_);
v___x_4093_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4093_, 0, v___x_4092_);
if (v_isShared_4089_ == 0)
{
lean_ctor_set_tag(v___x_4088_, 5);
lean_ctor_set(v___x_4088_, 1, v___x_4093_);
lean_ctor_set(v___x_4088_, 0, v___x_4090_);
v___x_4095_ = v___x_4088_;
goto v_reusejp_4094_;
}
else
{
lean_object* v_reuseFailAlloc_4096_; 
v_reuseFailAlloc_4096_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4096_, 0, v___x_4090_);
lean_ctor_set(v_reuseFailAlloc_4096_, 1, v___x_4093_);
v___x_4095_ = v_reuseFailAlloc_4096_;
goto v_reusejp_4094_;
}
v_reusejp_4094_:
{
return v___x_4095_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn___lam__2_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(lean_object* v_s_4099_){
_start:
{
lean_object* v_newEntries_4100_; lean_object* v___x_4101_; lean_object* v___x_4102_; 
v_newEntries_4100_ = lean_ctor_get(v_s_4099_, 0);
lean_inc(v_newEntries_4100_);
lean_dec_ref(v_s_4099_);
v___x_4101_ = l_List_reverse___redArg(v_newEntries_4100_);
v___x_4102_ = lean_array_mk(v___x_4101_);
return v___x_4102_;
}
}
static lean_object* _init_l___private_Lean_Attributes_0__Lean_initFn___closed__7_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4112_; lean_object* v___x_4113_; lean_object* v___f_4114_; lean_object* v___f_4115_; lean_object* v___x_4116_; lean_object* v___x_4117_; lean_object* v___x_4118_; lean_object* v___x_4119_; lean_object* v___x_4120_; 
v___x_4112_ = lean_box(0);
v___x_4113_ = lean_box(2);
v___f_4114_ = ((lean_object*)(l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___f_4115_ = ((lean_object*)(l___private_Lean_Attributes_0__Lean_initFn___closed__0_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___x_4116_ = ((lean_object*)(l___private_Lean_Attributes_0__Lean_initFn___closed__6_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___x_4117_ = ((lean_object*)(l___private_Lean_Attributes_0__Lean_initFn___closed__5_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___x_4118_ = lean_alloc_closure((void*)(l___private_Lean_Attributes_0__Lean_AttributeExtension_mkInitial___boxed), 1, 0);
v___x_4119_ = ((lean_object*)(l___private_Lean_Attributes_0__Lean_initFn___closed__4_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___x_4120_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_4120_, 0, v___x_4119_);
lean_ctor_set(v___x_4120_, 1, v___x_4118_);
lean_ctor_set(v___x_4120_, 2, v___x_4117_);
lean_ctor_set(v___x_4120_, 3, v___x_4116_);
lean_ctor_set(v___x_4120_, 4, v___f_4115_);
lean_ctor_set(v___x_4120_, 5, v___f_4114_);
lean_ctor_set(v___x_4120_, 6, v___x_4113_);
lean_ctor_set(v___x_4120_, 7, v___x_4112_);
return v___x_4120_;
}
}
static lean_object* _init_l___private_Lean_Attributes_0__Lean_initFn___closed__8_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_4121_; lean_object* v___x_4122_; lean_object* v___x_4123_; 
v___f_4121_ = ((lean_object*)(l___private_Lean_Attributes_0__Lean_initFn___closed__2_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___x_4122_ = lean_obj_once(&l___private_Lean_Attributes_0__Lean_initFn___closed__7_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_, &l___private_Lean_Attributes_0__Lean_initFn___closed__7_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2__once, _init_l___private_Lean_Attributes_0__Lean_initFn___closed__7_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_);
v___x_4123_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4123_, 0, v___x_4122_);
lean_ctor_set(v___x_4123_, 1, v___f_4121_);
return v___x_4123_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4125_; lean_object* v___x_4126_; 
v___x_4125_ = lean_obj_once(&l___private_Lean_Attributes_0__Lean_initFn___closed__8_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_, &l___private_Lean_Attributes_0__Lean_initFn___closed__8_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2__once, _init_l___private_Lean_Attributes_0__Lean_initFn___closed__8_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_);
v___x_4126_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_4125_);
return v___x_4126_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2____boxed(lean_object* v_a_4127_){
_start:
{
lean_object* v_res_4128_; 
v_res_4128_ = l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_();
return v_res_4128_;
}
}
LEAN_EXPORT lean_object* lean_is_attribute(lean_object* v_n_4129_){
_start:
{
lean_object* v___x_4131_; lean_object* v___x_4132_; uint8_t v___x_4133_; lean_object* v___x_4134_; lean_object* v___x_4135_; 
v___x_4131_ = l_Lean_attributeMapRef;
v___x_4132_ = lean_st_ref_get(v___x_4131_);
v___x_4133_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(v___x_4132_, v_n_4129_);
lean_dec(v_n_4129_);
lean_dec(v___x_4132_);
v___x_4134_ = lean_box(v___x_4133_);
v___x_4135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4135_, 0, v___x_4134_);
return v___x_4135_;
}
}
LEAN_EXPORT lean_object* l_Lean_isBuiltinAttribute___boxed(lean_object* v_n_4136_, lean_object* v_a_4137_){
_start:
{
lean_object* v_res_4138_; 
v_res_4138_ = lean_is_attribute(v_n_4136_);
return v_res_4138_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_getBuiltinAttributeNames_spec__0(lean_object* v_x_4139_, lean_object* v_x_4140_){
_start:
{
if (lean_obj_tag(v_x_4140_) == 0)
{
return v_x_4139_;
}
else
{
lean_object* v_key_4141_; lean_object* v_tail_4142_; lean_object* v___x_4143_; 
v_key_4141_ = lean_ctor_get(v_x_4140_, 0);
v_tail_4142_ = lean_ctor_get(v_x_4140_, 2);
lean_inc(v_key_4141_);
v___x_4143_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4143_, 0, v_key_4141_);
lean_ctor_set(v___x_4143_, 1, v_x_4139_);
v_x_4139_ = v___x_4143_;
v_x_4140_ = v_tail_4142_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_getBuiltinAttributeNames_spec__0___boxed(lean_object* v_x_4145_, lean_object* v_x_4146_){
_start:
{
lean_object* v_res_4147_; 
v_res_4147_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_getBuiltinAttributeNames_spec__0(v_x_4145_, v_x_4146_);
lean_dec(v_x_4146_);
return v_res_4147_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1(lean_object* v_as_4148_, size_t v_i_4149_, size_t v_stop_4150_, lean_object* v_b_4151_){
_start:
{
uint8_t v___x_4152_; 
v___x_4152_ = lean_usize_dec_eq(v_i_4149_, v_stop_4150_);
if (v___x_4152_ == 0)
{
lean_object* v___x_4153_; lean_object* v___x_4154_; size_t v___x_4155_; size_t v___x_4156_; 
v___x_4153_ = lean_array_uget_borrowed(v_as_4148_, v_i_4149_);
v___x_4154_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_getBuiltinAttributeNames_spec__0(v_b_4151_, v___x_4153_);
v___x_4155_ = ((size_t)1ULL);
v___x_4156_ = lean_usize_add(v_i_4149_, v___x_4155_);
v_i_4149_ = v___x_4156_;
v_b_4151_ = v___x_4154_;
goto _start;
}
else
{
return v_b_4151_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1___boxed(lean_object* v_as_4158_, lean_object* v_i_4159_, lean_object* v_stop_4160_, lean_object* v_b_4161_){
_start:
{
size_t v_i_boxed_4162_; size_t v_stop_boxed_4163_; lean_object* v_res_4164_; 
v_i_boxed_4162_ = lean_unbox_usize(v_i_4159_);
lean_dec(v_i_4159_);
v_stop_boxed_4163_ = lean_unbox_usize(v_stop_4160_);
lean_dec(v_stop_4160_);
v_res_4164_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1(v_as_4158_, v_i_boxed_4162_, v_stop_boxed_4163_, v_b_4161_);
lean_dec_ref(v_as_4158_);
return v_res_4164_;
}
}
LEAN_EXPORT lean_object* l_Lean_getBuiltinAttributeNames(){
_start:
{
lean_object* v___x_4166_; lean_object* v___x_4167_; lean_object* v_buckets_4168_; lean_object* v___x_4169_; lean_object* v___x_4170_; lean_object* v___x_4171_; uint8_t v___x_4172_; 
v___x_4166_ = l_Lean_attributeMapRef;
v___x_4167_ = lean_st_ref_get(v___x_4166_);
v_buckets_4168_ = lean_ctor_get(v___x_4167_, 1);
lean_inc_ref(v_buckets_4168_);
lean_dec(v___x_4167_);
v___x_4169_ = lean_box(0);
v___x_4170_ = lean_unsigned_to_nat(0u);
v___x_4171_ = lean_array_get_size(v_buckets_4168_);
v___x_4172_ = lean_nat_dec_lt(v___x_4170_, v___x_4171_);
if (v___x_4172_ == 0)
{
lean_object* v___x_4173_; 
lean_dec_ref(v_buckets_4168_);
v___x_4173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4173_, 0, v___x_4169_);
return v___x_4173_;
}
else
{
uint8_t v___x_4174_; 
v___x_4174_ = lean_nat_dec_le(v___x_4171_, v___x_4171_);
if (v___x_4174_ == 0)
{
if (v___x_4172_ == 0)
{
lean_object* v___x_4175_; 
lean_dec_ref(v_buckets_4168_);
v___x_4175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4175_, 0, v___x_4169_);
return v___x_4175_;
}
else
{
size_t v___x_4176_; size_t v___x_4177_; lean_object* v___x_4178_; lean_object* v___x_4179_; 
v___x_4176_ = ((size_t)0ULL);
v___x_4177_ = lean_usize_of_nat(v___x_4171_);
v___x_4178_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1(v_buckets_4168_, v___x_4176_, v___x_4177_, v___x_4169_);
lean_dec_ref(v_buckets_4168_);
v___x_4179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4179_, 0, v___x_4178_);
return v___x_4179_;
}
}
else
{
size_t v___x_4180_; size_t v___x_4181_; lean_object* v___x_4182_; lean_object* v___x_4183_; 
v___x_4180_ = ((size_t)0ULL);
v___x_4181_ = lean_usize_of_nat(v___x_4171_);
v___x_4182_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1(v_buckets_4168_, v___x_4180_, v___x_4181_, v___x_4169_);
lean_dec_ref(v_buckets_4168_);
v___x_4183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4183_, 0, v___x_4182_);
return v___x_4183_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getBuiltinAttributeNames___boxed(lean_object* v_a_4184_){
_start:
{
lean_object* v_res_4185_; 
v_res_4185_ = l_Lean_getBuiltinAttributeNames();
return v_res_4185_;
}
}
LEAN_EXPORT lean_object* l_Lean_getBuiltinAttributeImpl(lean_object* v_attrName_4187_){
_start:
{
lean_object* v___x_4189_; lean_object* v___x_4190_; lean_object* v___x_4191_; 
v___x_4189_ = l_Lean_attributeMapRef;
v___x_4190_ = lean_st_ref_get(v___x_4189_);
v___x_4191_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(v___x_4190_, v_attrName_4187_);
lean_dec(v___x_4190_);
if (lean_obj_tag(v___x_4191_) == 0)
{
lean_object* v___x_4192_; uint8_t v___x_4193_; lean_object* v___x_4194_; lean_object* v___x_4195_; lean_object* v___x_4196_; lean_object* v___x_4197_; lean_object* v___x_4198_; lean_object* v___x_4199_; 
v___x_4192_ = ((lean_object*)(l_Lean_getBuiltinAttributeImpl___closed__0));
v___x_4193_ = 1;
v___x_4194_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_attrName_4187_, v___x_4193_);
v___x_4195_ = lean_string_append(v___x_4192_, v___x_4194_);
lean_dec_ref(v___x_4194_);
v___x_4196_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__4));
v___x_4197_ = lean_string_append(v___x_4195_, v___x_4196_);
v___x_4198_ = lean_mk_io_user_error(v___x_4197_);
v___x_4199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4199_, 0, v___x_4198_);
return v___x_4199_;
}
else
{
lean_object* v_val_4200_; lean_object* v___x_4202_; uint8_t v_isShared_4203_; uint8_t v_isSharedCheck_4207_; 
lean_dec(v_attrName_4187_);
v_val_4200_ = lean_ctor_get(v___x_4191_, 0);
v_isSharedCheck_4207_ = !lean_is_exclusive(v___x_4191_);
if (v_isSharedCheck_4207_ == 0)
{
v___x_4202_ = v___x_4191_;
v_isShared_4203_ = v_isSharedCheck_4207_;
goto v_resetjp_4201_;
}
else
{
lean_inc(v_val_4200_);
lean_dec(v___x_4191_);
v___x_4202_ = lean_box(0);
v_isShared_4203_ = v_isSharedCheck_4207_;
goto v_resetjp_4201_;
}
v_resetjp_4201_:
{
lean_object* v___x_4205_; 
if (v_isShared_4203_ == 0)
{
lean_ctor_set_tag(v___x_4202_, 0);
v___x_4205_ = v___x_4202_;
goto v_reusejp_4204_;
}
else
{
lean_object* v_reuseFailAlloc_4206_; 
v_reuseFailAlloc_4206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4206_, 0, v_val_4200_);
v___x_4205_ = v_reuseFailAlloc_4206_;
goto v_reusejp_4204_;
}
v_reusejp_4204_:
{
return v___x_4205_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getBuiltinAttributeImpl___boxed(lean_object* v_attrName_4208_, lean_object* v_a_4209_){
_start:
{
lean_object* v_res_4210_; 
v_res_4210_ = l_Lean_getBuiltinAttributeImpl(v_attrName_4208_);
return v_res_4210_;
}
}
LEAN_EXPORT lean_object* lean_attribute_application_time(lean_object* v_n_4211_){
_start:
{
lean_object* v___x_4213_; 
v___x_4213_ = l_Lean_getBuiltinAttributeImpl(v_n_4211_);
if (lean_obj_tag(v___x_4213_) == 0)
{
lean_object* v_a_4214_; lean_object* v___x_4216_; uint8_t v_isShared_4217_; uint8_t v_isSharedCheck_4224_; 
v_a_4214_ = lean_ctor_get(v___x_4213_, 0);
v_isSharedCheck_4224_ = !lean_is_exclusive(v___x_4213_);
if (v_isSharedCheck_4224_ == 0)
{
v___x_4216_ = v___x_4213_;
v_isShared_4217_ = v_isSharedCheck_4224_;
goto v_resetjp_4215_;
}
else
{
lean_inc(v_a_4214_);
lean_dec(v___x_4213_);
v___x_4216_ = lean_box(0);
v_isShared_4217_ = v_isSharedCheck_4224_;
goto v_resetjp_4215_;
}
v_resetjp_4215_:
{
lean_object* v_toAttributeImplCore_4218_; uint8_t v_applicationTime_4219_; lean_object* v___x_4220_; lean_object* v___x_4222_; 
v_toAttributeImplCore_4218_ = lean_ctor_get(v_a_4214_, 0);
lean_inc_ref(v_toAttributeImplCore_4218_);
lean_dec(v_a_4214_);
v_applicationTime_4219_ = lean_ctor_get_uint8(v_toAttributeImplCore_4218_, sizeof(void*)*3);
lean_dec_ref(v_toAttributeImplCore_4218_);
v___x_4220_ = lean_box(v_applicationTime_4219_);
if (v_isShared_4217_ == 0)
{
lean_ctor_set(v___x_4216_, 0, v___x_4220_);
v___x_4222_ = v___x_4216_;
goto v_reusejp_4221_;
}
else
{
lean_object* v_reuseFailAlloc_4223_; 
v_reuseFailAlloc_4223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4223_, 0, v___x_4220_);
v___x_4222_ = v_reuseFailAlloc_4223_;
goto v_reusejp_4221_;
}
v_reusejp_4221_:
{
return v___x_4222_;
}
}
}
else
{
lean_object* v_a_4225_; lean_object* v___x_4227_; uint8_t v_isShared_4228_; uint8_t v_isSharedCheck_4232_; 
v_a_4225_ = lean_ctor_get(v___x_4213_, 0);
v_isSharedCheck_4232_ = !lean_is_exclusive(v___x_4213_);
if (v_isSharedCheck_4232_ == 0)
{
v___x_4227_ = v___x_4213_;
v_isShared_4228_ = v_isSharedCheck_4232_;
goto v_resetjp_4226_;
}
else
{
lean_inc(v_a_4225_);
lean_dec(v___x_4213_);
v___x_4227_ = lean_box(0);
v_isShared_4228_ = v_isSharedCheck_4232_;
goto v_resetjp_4226_;
}
v_resetjp_4226_:
{
lean_object* v___x_4230_; 
if (v_isShared_4228_ == 0)
{
v___x_4230_ = v___x_4227_;
goto v_reusejp_4229_;
}
else
{
lean_object* v_reuseFailAlloc_4231_; 
v_reuseFailAlloc_4231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4231_, 0, v_a_4225_);
v___x_4230_ = v_reuseFailAlloc_4231_;
goto v_reusejp_4229_;
}
v_reusejp_4229_:
{
return v___x_4230_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getBuiltinAttributeApplicationTime___boxed(lean_object* v_n_4233_, lean_object* v_a_4234_){
_start:
{
lean_object* v_res_4235_; 
v_res_4235_ = lean_attribute_application_time(v_n_4233_);
return v_res_4235_;
}
}
LEAN_EXPORT uint8_t l_Lean_isAttribute(lean_object* v_env_4236_, lean_object* v_attrName_4237_){
_start:
{
lean_object* v___x_4238_; lean_object* v_toEnvExtension_4239_; lean_object* v_asyncMode_4240_; lean_object* v___x_4241_; lean_object* v___x_4242_; lean_object* v___x_4243_; lean_object* v_map_4244_; uint8_t v___x_4245_; 
v___x_4238_ = l_Lean_attributeExtension;
v_toEnvExtension_4239_ = lean_ctor_get(v___x_4238_, 0);
v_asyncMode_4240_ = lean_ctor_get(v_toEnvExtension_4239_, 2);
v___x_4241_ = l_Lean_instInhabitedAttributeExtensionState_default;
v___x_4242_ = lean_box(0);
v___x_4243_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_4241_, v___x_4238_, v_env_4236_, v_asyncMode_4240_, v___x_4242_);
v_map_4244_ = lean_ctor_get(v___x_4243_, 1);
lean_inc_ref(v_map_4244_);
lean_dec(v___x_4243_);
v___x_4245_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(v_map_4244_, v_attrName_4237_);
lean_dec_ref(v_map_4244_);
return v___x_4245_;
}
}
LEAN_EXPORT lean_object* l_Lean_isAttribute___boxed(lean_object* v_env_4246_, lean_object* v_attrName_4247_){
_start:
{
uint8_t v_res_4248_; lean_object* v_r_4249_; 
v_res_4248_ = l_Lean_isAttribute(v_env_4246_, v_attrName_4247_);
lean_dec(v_attrName_4247_);
v_r_4249_ = lean_box(v_res_4248_);
return v_r_4249_;
}
}
LEAN_EXPORT lean_object* l_Lean_getAttributeNames(lean_object* v_env_4250_){
_start:
{
lean_object* v___x_4251_; lean_object* v_toEnvExtension_4252_; lean_object* v_asyncMode_4253_; lean_object* v___x_4254_; lean_object* v___x_4255_; lean_object* v___x_4256_; lean_object* v_map_4257_; lean_object* v_buckets_4258_; lean_object* v___x_4259_; lean_object* v___x_4260_; lean_object* v___x_4261_; uint8_t v___x_4262_; 
v___x_4251_ = l_Lean_attributeExtension;
v_toEnvExtension_4252_ = lean_ctor_get(v___x_4251_, 0);
v_asyncMode_4253_ = lean_ctor_get(v_toEnvExtension_4252_, 2);
v___x_4254_ = l_Lean_instInhabitedAttributeExtensionState_default;
v___x_4255_ = lean_box(0);
v___x_4256_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_4254_, v___x_4251_, v_env_4250_, v_asyncMode_4253_, v___x_4255_);
v_map_4257_ = lean_ctor_get(v___x_4256_, 1);
lean_inc_ref(v_map_4257_);
lean_dec(v___x_4256_);
v_buckets_4258_ = lean_ctor_get(v_map_4257_, 1);
lean_inc_ref(v_buckets_4258_);
lean_dec_ref(v_map_4257_);
v___x_4259_ = lean_box(0);
v___x_4260_ = lean_unsigned_to_nat(0u);
v___x_4261_ = lean_array_get_size(v_buckets_4258_);
v___x_4262_ = lean_nat_dec_lt(v___x_4260_, v___x_4261_);
if (v___x_4262_ == 0)
{
lean_dec_ref(v_buckets_4258_);
return v___x_4259_;
}
else
{
uint8_t v___x_4263_; 
v___x_4263_ = lean_nat_dec_le(v___x_4261_, v___x_4261_);
if (v___x_4263_ == 0)
{
if (v___x_4262_ == 0)
{
lean_dec_ref(v_buckets_4258_);
return v___x_4259_;
}
else
{
size_t v___x_4264_; size_t v___x_4265_; lean_object* v___x_4266_; 
v___x_4264_ = ((size_t)0ULL);
v___x_4265_ = lean_usize_of_nat(v___x_4261_);
v___x_4266_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1(v_buckets_4258_, v___x_4264_, v___x_4265_, v___x_4259_);
lean_dec_ref(v_buckets_4258_);
return v___x_4266_;
}
}
else
{
size_t v___x_4267_; size_t v___x_4268_; lean_object* v___x_4269_; 
v___x_4267_ = ((size_t)0ULL);
v___x_4268_ = lean_usize_of_nat(v___x_4261_);
v___x_4269_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1(v_buckets_4258_, v___x_4267_, v___x_4268_, v___x_4259_);
lean_dec_ref(v_buckets_4258_);
return v___x_4269_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getAttributeImpl(lean_object* v_env_4270_, lean_object* v_attrName_4271_){
_start:
{
lean_object* v___x_4272_; lean_object* v_toEnvExtension_4273_; lean_object* v_asyncMode_4274_; lean_object* v___x_4275_; lean_object* v___x_4276_; lean_object* v___x_4277_; lean_object* v_map_4278_; lean_object* v___x_4279_; 
v___x_4272_ = l_Lean_attributeExtension;
v_toEnvExtension_4273_ = lean_ctor_get(v___x_4272_, 0);
v_asyncMode_4274_ = lean_ctor_get(v_toEnvExtension_4273_, 2);
v___x_4275_ = l_Lean_instInhabitedAttributeExtensionState_default;
v___x_4276_ = lean_box(0);
v___x_4277_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_4275_, v___x_4272_, v_env_4270_, v_asyncMode_4274_, v___x_4276_);
v_map_4278_ = lean_ctor_get(v___x_4277_, 1);
lean_inc_ref(v_map_4278_);
lean_dec(v___x_4277_);
v___x_4279_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(v_map_4278_, v_attrName_4271_);
lean_dec_ref(v_map_4278_);
if (lean_obj_tag(v___x_4279_) == 0)
{
lean_object* v___x_4280_; uint8_t v___x_4281_; lean_object* v___x_4282_; lean_object* v___x_4283_; lean_object* v___x_4284_; lean_object* v___x_4285_; lean_object* v___x_4286_; 
v___x_4280_ = ((lean_object*)(l_Lean_getBuiltinAttributeImpl___closed__0));
v___x_4281_ = 1;
v___x_4282_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_attrName_4271_, v___x_4281_);
v___x_4283_ = lean_string_append(v___x_4280_, v___x_4282_);
lean_dec_ref(v___x_4282_);
v___x_4284_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__4));
v___x_4285_ = lean_string_append(v___x_4283_, v___x_4284_);
v___x_4286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4286_, 0, v___x_4285_);
return v___x_4286_;
}
else
{
lean_object* v_val_4287_; lean_object* v___x_4289_; uint8_t v_isShared_4290_; uint8_t v_isSharedCheck_4294_; 
lean_dec(v_attrName_4271_);
v_val_4287_ = lean_ctor_get(v___x_4279_, 0);
v_isSharedCheck_4294_ = !lean_is_exclusive(v___x_4279_);
if (v_isSharedCheck_4294_ == 0)
{
v___x_4289_ = v___x_4279_;
v_isShared_4290_ = v_isSharedCheck_4294_;
goto v_resetjp_4288_;
}
else
{
lean_inc(v_val_4287_);
lean_dec(v___x_4279_);
v___x_4289_ = lean_box(0);
v_isShared_4290_ = v_isSharedCheck_4294_;
goto v_resetjp_4288_;
}
v_resetjp_4288_:
{
lean_object* v___x_4292_; 
if (v_isShared_4290_ == 0)
{
v___x_4292_ = v___x_4289_;
goto v_reusejp_4291_;
}
else
{
lean_object* v_reuseFailAlloc_4293_; 
v_reuseFailAlloc_4293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4293_, 0, v_val_4287_);
v___x_4292_ = v_reuseFailAlloc_4293_;
goto v_reusejp_4291_;
}
v_reusejp_4291_:
{
return v___x_4292_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerAttributeOfBuilder(lean_object* v_env_4295_, lean_object* v_builderId_4296_, lean_object* v_ref_4297_, lean_object* v_args_4298_){
_start:
{
lean_object* v_entry_4300_; lean_object* v___x_4301_; 
v_entry_4300_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_entry_4300_, 0, v_builderId_4296_);
lean_ctor_set(v_entry_4300_, 1, v_ref_4297_);
lean_ctor_set(v_entry_4300_, 2, v_args_4298_);
lean_inc_ref(v_entry_4300_);
v___x_4301_ = l_Lean_mkAttributeImplOfEntry(v_entry_4300_);
if (lean_obj_tag(v___x_4301_) == 0)
{
lean_object* v_a_4302_; lean_object* v___x_4304_; uint8_t v_isShared_4305_; uint8_t v_isSharedCheck_4327_; 
v_a_4302_ = lean_ctor_get(v___x_4301_, 0);
v_isSharedCheck_4327_ = !lean_is_exclusive(v___x_4301_);
if (v_isSharedCheck_4327_ == 0)
{
v___x_4304_ = v___x_4301_;
v_isShared_4305_ = v_isSharedCheck_4327_;
goto v_resetjp_4303_;
}
else
{
lean_inc(v_a_4302_);
lean_dec(v___x_4301_);
v___x_4304_ = lean_box(0);
v_isShared_4305_ = v_isSharedCheck_4327_;
goto v_resetjp_4303_;
}
v_resetjp_4303_:
{
lean_object* v_toAttributeImplCore_4306_; lean_object* v_name_4307_; uint8_t v___x_4308_; 
v_toAttributeImplCore_4306_ = lean_ctor_get(v_a_4302_, 0);
v_name_4307_ = lean_ctor_get(v_toAttributeImplCore_4306_, 1);
lean_inc_ref(v_env_4295_);
v___x_4308_ = l_Lean_isAttribute(v_env_4295_, v_name_4307_);
if (v___x_4308_ == 0)
{
lean_object* v___x_4309_; lean_object* v_toEnvExtension_4310_; lean_object* v_asyncMode_4311_; lean_object* v___x_4312_; lean_object* v___x_4313_; lean_object* v___x_4314_; lean_object* v___x_4316_; 
v___x_4309_ = l_Lean_attributeExtension;
v_toEnvExtension_4310_ = lean_ctor_get(v___x_4309_, 0);
v_asyncMode_4311_ = lean_ctor_get(v_toEnvExtension_4310_, 2);
v___x_4312_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4312_, 0, v_entry_4300_);
lean_ctor_set(v___x_4312_, 1, v_a_4302_);
v___x_4313_ = lean_box(0);
v___x_4314_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_4309_, v_env_4295_, v___x_4312_, v_asyncMode_4311_, v___x_4313_);
if (v_isShared_4305_ == 0)
{
lean_ctor_set(v___x_4304_, 0, v___x_4314_);
v___x_4316_ = v___x_4304_;
goto v_reusejp_4315_;
}
else
{
lean_object* v_reuseFailAlloc_4317_; 
v_reuseFailAlloc_4317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4317_, 0, v___x_4314_);
v___x_4316_ = v_reuseFailAlloc_4317_;
goto v_reusejp_4315_;
}
v_reusejp_4315_:
{
return v___x_4316_;
}
}
else
{
lean_object* v___x_4318_; lean_object* v___x_4319_; lean_object* v___x_4320_; lean_object* v___x_4321_; lean_object* v___x_4322_; lean_object* v___x_4323_; lean_object* v___x_4325_; 
lean_inc(v_name_4307_);
lean_dec(v_a_4302_);
lean_dec_ref(v_entry_4300_);
lean_dec_ref(v_env_4295_);
v___x_4318_ = ((lean_object*)(l_Lean_registerBuiltinAttribute___closed__2));
v___x_4319_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_4307_, v___x_4308_);
v___x_4320_ = lean_string_append(v___x_4318_, v___x_4319_);
lean_dec_ref(v___x_4319_);
v___x_4321_ = ((lean_object*)(l_Lean_registerBuiltinAttribute___closed__3));
v___x_4322_ = lean_string_append(v___x_4320_, v___x_4321_);
v___x_4323_ = lean_mk_io_user_error(v___x_4322_);
if (v_isShared_4305_ == 0)
{
lean_ctor_set_tag(v___x_4304_, 1);
lean_ctor_set(v___x_4304_, 0, v___x_4323_);
v___x_4325_ = v___x_4304_;
goto v_reusejp_4324_;
}
else
{
lean_object* v_reuseFailAlloc_4326_; 
v_reuseFailAlloc_4326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4326_, 0, v___x_4323_);
v___x_4325_ = v_reuseFailAlloc_4326_;
goto v_reusejp_4324_;
}
v_reusejp_4324_:
{
return v___x_4325_;
}
}
}
}
else
{
lean_object* v_a_4328_; lean_object* v___x_4330_; uint8_t v_isShared_4331_; uint8_t v_isSharedCheck_4335_; 
lean_dec_ref(v_entry_4300_);
lean_dec_ref(v_env_4295_);
v_a_4328_ = lean_ctor_get(v___x_4301_, 0);
v_isSharedCheck_4335_ = !lean_is_exclusive(v___x_4301_);
if (v_isSharedCheck_4335_ == 0)
{
v___x_4330_ = v___x_4301_;
v_isShared_4331_ = v_isSharedCheck_4335_;
goto v_resetjp_4329_;
}
else
{
lean_inc(v_a_4328_);
lean_dec(v___x_4301_);
v___x_4330_ = lean_box(0);
v_isShared_4331_ = v_isSharedCheck_4335_;
goto v_resetjp_4329_;
}
v_resetjp_4329_:
{
lean_object* v___x_4333_; 
if (v_isShared_4331_ == 0)
{
v___x_4333_ = v___x_4330_;
goto v_reusejp_4332_;
}
else
{
lean_object* v_reuseFailAlloc_4334_; 
v_reuseFailAlloc_4334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4334_, 0, v_a_4328_);
v___x_4333_ = v_reuseFailAlloc_4334_;
goto v_reusejp_4332_;
}
v_reusejp_4332_:
{
return v___x_4333_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerAttributeOfBuilder___boxed(lean_object* v_env_4336_, lean_object* v_builderId_4337_, lean_object* v_ref_4338_, lean_object* v_args_4339_, lean_object* v_a_4340_){
_start:
{
lean_object* v_res_4341_; 
v_res_4341_ = l_Lean_registerAttributeOfBuilder(v_env_4336_, v_builderId_4337_, v_ref_4338_, v_args_4339_);
return v_res_4341_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg(lean_object* v_x_4342_, lean_object* v___y_4343_, lean_object* v___y_4344_){
_start:
{
if (lean_obj_tag(v_x_4342_) == 0)
{
lean_object* v_a_4346_; lean_object* v___x_4347_; lean_object* v___x_4348_; 
v_a_4346_ = lean_ctor_get(v_x_4342_, 0);
lean_inc(v_a_4346_);
lean_dec_ref(v_x_4342_);
v___x_4347_ = l_Lean_stringToMessageData(v_a_4346_);
v___x_4348_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_4347_, v___y_4343_, v___y_4344_);
return v___x_4348_;
}
else
{
lean_object* v_a_4349_; lean_object* v___x_4351_; uint8_t v_isShared_4352_; uint8_t v_isSharedCheck_4356_; 
v_a_4349_ = lean_ctor_get(v_x_4342_, 0);
v_isSharedCheck_4356_ = !lean_is_exclusive(v_x_4342_);
if (v_isSharedCheck_4356_ == 0)
{
v___x_4351_ = v_x_4342_;
v_isShared_4352_ = v_isSharedCheck_4356_;
goto v_resetjp_4350_;
}
else
{
lean_inc(v_a_4349_);
lean_dec(v_x_4342_);
v___x_4351_ = lean_box(0);
v_isShared_4352_ = v_isSharedCheck_4356_;
goto v_resetjp_4350_;
}
v_resetjp_4350_:
{
lean_object* v___x_4354_; 
if (v_isShared_4352_ == 0)
{
lean_ctor_set_tag(v___x_4351_, 0);
v___x_4354_ = v___x_4351_;
goto v_reusejp_4353_;
}
else
{
lean_object* v_reuseFailAlloc_4355_; 
v_reuseFailAlloc_4355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4355_, 0, v_a_4349_);
v___x_4354_ = v_reuseFailAlloc_4355_;
goto v_reusejp_4353_;
}
v_reusejp_4353_:
{
return v___x_4354_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg___boxed(lean_object* v_x_4357_, lean_object* v___y_4358_, lean_object* v___y_4359_, lean_object* v___y_4360_){
_start:
{
lean_object* v_res_4361_; 
v_res_4361_ = l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg(v_x_4357_, v___y_4358_, v___y_4359_);
lean_dec(v___y_4359_);
lean_dec_ref(v___y_4358_);
return v_res_4361_;
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_add(lean_object* v_declName_4362_, lean_object* v_attrName_4363_, lean_object* v_stx_4364_, uint8_t v_kind_4365_, lean_object* v_a_4366_, lean_object* v_a_4367_){
_start:
{
lean_object* v___x_4369_; lean_object* v_env_4370_; lean_object* v___x_4371_; lean_object* v___x_4372_; 
v___x_4369_ = lean_st_ref_get(v_a_4367_);
v_env_4370_ = lean_ctor_get(v___x_4369_, 0);
lean_inc_ref(v_env_4370_);
lean_dec(v___x_4369_);
v___x_4371_ = l_Lean_getAttributeImpl(v_env_4370_, v_attrName_4363_);
v___x_4372_ = l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg(v___x_4371_, v_a_4366_, v_a_4367_);
if (lean_obj_tag(v___x_4372_) == 0)
{
lean_object* v_a_4373_; lean_object* v_add_4374_; lean_object* v___x_4375_; lean_object* v___x_4376_; 
v_a_4373_ = lean_ctor_get(v___x_4372_, 0);
lean_inc(v_a_4373_);
lean_dec_ref(v___x_4372_);
v_add_4374_ = lean_ctor_get(v_a_4373_, 1);
lean_inc_ref(v_add_4374_);
lean_dec(v_a_4373_);
v___x_4375_ = lean_box(v_kind_4365_);
lean_inc(v_a_4367_);
lean_inc_ref(v_a_4366_);
v___x_4376_ = lean_apply_6(v_add_4374_, v_declName_4362_, v_stx_4364_, v___x_4375_, v_a_4366_, v_a_4367_, lean_box(0));
return v___x_4376_;
}
else
{
lean_object* v_a_4377_; lean_object* v___x_4379_; uint8_t v_isShared_4380_; uint8_t v_isSharedCheck_4384_; 
lean_dec(v_stx_4364_);
lean_dec(v_declName_4362_);
v_a_4377_ = lean_ctor_get(v___x_4372_, 0);
v_isSharedCheck_4384_ = !lean_is_exclusive(v___x_4372_);
if (v_isSharedCheck_4384_ == 0)
{
v___x_4379_ = v___x_4372_;
v_isShared_4380_ = v_isSharedCheck_4384_;
goto v_resetjp_4378_;
}
else
{
lean_inc(v_a_4377_);
lean_dec(v___x_4372_);
v___x_4379_ = lean_box(0);
v_isShared_4380_ = v_isSharedCheck_4384_;
goto v_resetjp_4378_;
}
v_resetjp_4378_:
{
lean_object* v___x_4382_; 
if (v_isShared_4380_ == 0)
{
v___x_4382_ = v___x_4379_;
goto v_reusejp_4381_;
}
else
{
lean_object* v_reuseFailAlloc_4383_; 
v_reuseFailAlloc_4383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4383_, 0, v_a_4377_);
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
}
LEAN_EXPORT lean_object* l_Lean_Attribute_add___boxed(lean_object* v_declName_4385_, lean_object* v_attrName_4386_, lean_object* v_stx_4387_, lean_object* v_kind_4388_, lean_object* v_a_4389_, lean_object* v_a_4390_, lean_object* v_a_4391_){
_start:
{
uint8_t v_kind_boxed_4392_; lean_object* v_res_4393_; 
v_kind_boxed_4392_ = lean_unbox(v_kind_4388_);
v_res_4393_ = l_Lean_Attribute_add(v_declName_4385_, v_attrName_4386_, v_stx_4387_, v_kind_boxed_4392_, v_a_4389_, v_a_4390_);
lean_dec(v_a_4390_);
lean_dec_ref(v_a_4389_);
return v_res_4393_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0(lean_object* v_00_u03b1_4394_, lean_object* v_x_4395_, lean_object* v___y_4396_, lean_object* v___y_4397_){
_start:
{
lean_object* v___x_4399_; 
v___x_4399_ = l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg(v_x_4395_, v___y_4396_, v___y_4397_);
return v___x_4399_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___boxed(lean_object* v_00_u03b1_4400_, lean_object* v_x_4401_, lean_object* v___y_4402_, lean_object* v___y_4403_, lean_object* v___y_4404_){
_start:
{
lean_object* v_res_4405_; 
v_res_4405_ = l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0(v_00_u03b1_4400_, v_x_4401_, v___y_4402_, v___y_4403_);
lean_dec(v___y_4403_);
lean_dec_ref(v___y_4402_);
return v_res_4405_;
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_erase(lean_object* v_declName_4406_, lean_object* v_attrName_4407_, lean_object* v_a_4408_, lean_object* v_a_4409_){
_start:
{
lean_object* v___x_4411_; lean_object* v_env_4412_; lean_object* v___x_4413_; lean_object* v___x_4414_; 
v___x_4411_ = lean_st_ref_get(v_a_4409_);
v_env_4412_ = lean_ctor_get(v___x_4411_, 0);
lean_inc_ref(v_env_4412_);
lean_dec(v___x_4411_);
v___x_4413_ = l_Lean_getAttributeImpl(v_env_4412_, v_attrName_4407_);
v___x_4414_ = l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg(v___x_4413_, v_a_4408_, v_a_4409_);
if (lean_obj_tag(v___x_4414_) == 0)
{
lean_object* v_a_4415_; lean_object* v_erase_4416_; lean_object* v___x_4417_; 
v_a_4415_ = lean_ctor_get(v___x_4414_, 0);
lean_inc(v_a_4415_);
lean_dec_ref(v___x_4414_);
v_erase_4416_ = lean_ctor_get(v_a_4415_, 2);
lean_inc_ref(v_erase_4416_);
lean_dec(v_a_4415_);
lean_inc(v_a_4409_);
lean_inc_ref(v_a_4408_);
v___x_4417_ = lean_apply_4(v_erase_4416_, v_declName_4406_, v_a_4408_, v_a_4409_, lean_box(0));
return v___x_4417_;
}
else
{
lean_object* v_a_4418_; lean_object* v___x_4420_; uint8_t v_isShared_4421_; uint8_t v_isSharedCheck_4425_; 
lean_dec(v_declName_4406_);
v_a_4418_ = lean_ctor_get(v___x_4414_, 0);
v_isSharedCheck_4425_ = !lean_is_exclusive(v___x_4414_);
if (v_isSharedCheck_4425_ == 0)
{
v___x_4420_ = v___x_4414_;
v_isShared_4421_ = v_isSharedCheck_4425_;
goto v_resetjp_4419_;
}
else
{
lean_inc(v_a_4418_);
lean_dec(v___x_4414_);
v___x_4420_ = lean_box(0);
v_isShared_4421_ = v_isSharedCheck_4425_;
goto v_resetjp_4419_;
}
v_resetjp_4419_:
{
lean_object* v___x_4423_; 
if (v_isShared_4421_ == 0)
{
v___x_4423_ = v___x_4420_;
goto v_reusejp_4422_;
}
else
{
lean_object* v_reuseFailAlloc_4424_; 
v_reuseFailAlloc_4424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4424_, 0, v_a_4418_);
v___x_4423_ = v_reuseFailAlloc_4424_;
goto v_reusejp_4422_;
}
v_reusejp_4422_:
{
return v___x_4423_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_erase___boxed(lean_object* v_declName_4426_, lean_object* v_attrName_4427_, lean_object* v_a_4428_, lean_object* v_a_4429_, lean_object* v_a_4430_){
_start:
{
lean_object* v_res_4431_; 
v_res_4431_ = l_Lean_Attribute_erase(v_declName_4426_, v_attrName_4427_, v_a_4428_, v_a_4429_);
lean_dec(v_a_4429_);
lean_dec_ref(v_a_4428_);
return v_res_4431_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_updateEnvAttributesImpl_spec__0(lean_object* v_x_4432_, lean_object* v_x_4433_){
_start:
{
if (lean_obj_tag(v_x_4433_) == 0)
{
return v_x_4432_;
}
else
{
lean_object* v_key_4434_; lean_object* v_value_4435_; lean_object* v_tail_4436_; lean_object* v_newEntries_4437_; lean_object* v_map_4438_; uint8_t v___x_4439_; 
v_key_4434_ = lean_ctor_get(v_x_4433_, 0);
lean_inc(v_key_4434_);
v_value_4435_ = lean_ctor_get(v_x_4433_, 1);
lean_inc(v_value_4435_);
v_tail_4436_ = lean_ctor_get(v_x_4433_, 2);
lean_inc(v_tail_4436_);
lean_dec_ref(v_x_4433_);
v_newEntries_4437_ = lean_ctor_get(v_x_4432_, 0);
v_map_4438_ = lean_ctor_get(v_x_4432_, 1);
v___x_4439_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(v_map_4438_, v_key_4434_);
if (v___x_4439_ == 0)
{
lean_object* v___x_4441_; uint8_t v_isShared_4442_; uint8_t v_isSharedCheck_4448_; 
lean_inc_ref(v_map_4438_);
lean_inc(v_newEntries_4437_);
v_isSharedCheck_4448_ = !lean_is_exclusive(v_x_4432_);
if (v_isSharedCheck_4448_ == 0)
{
lean_object* v_unused_4449_; lean_object* v_unused_4450_; 
v_unused_4449_ = lean_ctor_get(v_x_4432_, 1);
lean_dec(v_unused_4449_);
v_unused_4450_ = lean_ctor_get(v_x_4432_, 0);
lean_dec(v_unused_4450_);
v___x_4441_ = v_x_4432_;
v_isShared_4442_ = v_isSharedCheck_4448_;
goto v_resetjp_4440_;
}
else
{
lean_dec(v_x_4432_);
v___x_4441_ = lean_box(0);
v_isShared_4442_ = v_isSharedCheck_4448_;
goto v_resetjp_4440_;
}
v_resetjp_4440_:
{
lean_object* v___x_4443_; lean_object* v___x_4445_; 
v___x_4443_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1___redArg(v_map_4438_, v_key_4434_, v_value_4435_);
if (v_isShared_4442_ == 0)
{
lean_ctor_set(v___x_4441_, 1, v___x_4443_);
v___x_4445_ = v___x_4441_;
goto v_reusejp_4444_;
}
else
{
lean_object* v_reuseFailAlloc_4447_; 
v_reuseFailAlloc_4447_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4447_, 0, v_newEntries_4437_);
lean_ctor_set(v_reuseFailAlloc_4447_, 1, v___x_4443_);
v___x_4445_ = v_reuseFailAlloc_4447_;
goto v_reusejp_4444_;
}
v_reusejp_4444_:
{
v_x_4432_ = v___x_4445_;
v_x_4433_ = v_tail_4436_;
goto _start;
}
}
}
else
{
lean_dec(v_value_4435_);
lean_dec(v_key_4434_);
v_x_4433_ = v_tail_4436_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_updateEnvAttributesImpl_spec__1(lean_object* v_as_4452_, size_t v_i_4453_, size_t v_stop_4454_, lean_object* v_b_4455_){
_start:
{
uint8_t v___x_4456_; 
v___x_4456_ = lean_usize_dec_eq(v_i_4453_, v_stop_4454_);
if (v___x_4456_ == 0)
{
lean_object* v___x_4457_; lean_object* v___x_4458_; size_t v___x_4459_; size_t v___x_4460_; 
v___x_4457_ = lean_array_uget_borrowed(v_as_4452_, v_i_4453_);
lean_inc(v___x_4457_);
v___x_4458_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_updateEnvAttributesImpl_spec__0(v_b_4455_, v___x_4457_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_updateEnvAttributesImpl_spec__1___boxed(lean_object* v_as_4462_, lean_object* v_i_4463_, lean_object* v_stop_4464_, lean_object* v_b_4465_){
_start:
{
size_t v_i_boxed_4466_; size_t v_stop_boxed_4467_; lean_object* v_res_4468_; 
v_i_boxed_4466_ = lean_unbox_usize(v_i_4463_);
lean_dec(v_i_4463_);
v_stop_boxed_4467_ = lean_unbox_usize(v_stop_4464_);
lean_dec(v_stop_4464_);
v_res_4468_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_updateEnvAttributesImpl_spec__1(v_as_4462_, v_i_boxed_4466_, v_stop_boxed_4467_, v_b_4465_);
lean_dec_ref(v_as_4462_);
return v_res_4468_;
}
}
LEAN_EXPORT lean_object* lean_update_env_attributes(lean_object* v_env_4469_){
_start:
{
lean_object* v___x_4471_; lean_object* v___x_4472_; lean_object* v___x_4473_; lean_object* v___y_4475_; lean_object* v_toEnvExtension_4478_; lean_object* v_asyncMode_4479_; lean_object* v_buckets_4480_; lean_object* v___x_4481_; lean_object* v___x_4482_; lean_object* v___x_4483_; lean_object* v___x_4484_; lean_object* v___x_4485_; uint8_t v___x_4486_; 
v___x_4471_ = l_Lean_attributeMapRef;
v___x_4472_ = lean_st_ref_get(v___x_4471_);
v___x_4473_ = l_Lean_attributeExtension;
v_toEnvExtension_4478_ = lean_ctor_get(v___x_4473_, 0);
v_asyncMode_4479_ = lean_ctor_get(v_toEnvExtension_4478_, 2);
v_buckets_4480_ = lean_ctor_get(v___x_4472_, 1);
lean_inc_ref(v_buckets_4480_);
lean_dec(v___x_4472_);
v___x_4481_ = l_Lean_instInhabitedAttributeExtensionState_default;
v___x_4482_ = lean_box(0);
lean_inc_ref(v_env_4469_);
v___x_4483_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_4481_, v___x_4473_, v_env_4469_, v_asyncMode_4479_, v___x_4482_);
v___x_4484_ = lean_unsigned_to_nat(0u);
v___x_4485_ = lean_array_get_size(v_buckets_4480_);
v___x_4486_ = lean_nat_dec_lt(v___x_4484_, v___x_4485_);
if (v___x_4486_ == 0)
{
lean_dec_ref(v_buckets_4480_);
v___y_4475_ = v___x_4483_;
goto v___jp_4474_;
}
else
{
uint8_t v___x_4487_; 
v___x_4487_ = lean_nat_dec_le(v___x_4485_, v___x_4485_);
if (v___x_4487_ == 0)
{
if (v___x_4486_ == 0)
{
lean_dec_ref(v_buckets_4480_);
v___y_4475_ = v___x_4483_;
goto v___jp_4474_;
}
else
{
size_t v___x_4488_; size_t v___x_4489_; lean_object* v___x_4490_; 
v___x_4488_ = ((size_t)0ULL);
v___x_4489_ = lean_usize_of_nat(v___x_4485_);
v___x_4490_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_updateEnvAttributesImpl_spec__1(v_buckets_4480_, v___x_4488_, v___x_4489_, v___x_4483_);
lean_dec_ref(v_buckets_4480_);
v___y_4475_ = v___x_4490_;
goto v___jp_4474_;
}
}
else
{
size_t v___x_4491_; size_t v___x_4492_; lean_object* v___x_4493_; 
v___x_4491_ = ((size_t)0ULL);
v___x_4492_ = lean_usize_of_nat(v___x_4485_);
v___x_4493_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_updateEnvAttributesImpl_spec__1(v_buckets_4480_, v___x_4491_, v___x_4492_, v___x_4483_);
lean_dec_ref(v_buckets_4480_);
v___y_4475_ = v___x_4493_;
goto v___jp_4474_;
}
}
v___jp_4474_:
{
lean_object* v___x_4476_; lean_object* v___x_4477_; 
v___x_4476_ = l_Lean_PersistentEnvExtension_setState___redArg(v___x_4473_, v_env_4469_, v___y_4475_);
v___x_4477_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4477_, 0, v___x_4476_);
return v___x_4477_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_updateEnvAttributesImpl___boxed(lean_object* v_env_4494_, lean_object* v_a_4495_){
_start:
{
lean_object* v_res_4496_; 
v_res_4496_ = lean_update_env_attributes(v_env_4494_);
return v_res_4496_;
}
}
LEAN_EXPORT lean_object* lean_get_num_attributes(){
_start:
{
lean_object* v___x_4498_; lean_object* v___x_4499_; lean_object* v_size_4500_; lean_object* v___x_4501_; 
v___x_4498_ = l_Lean_attributeMapRef;
v___x_4499_ = lean_st_ref_get(v___x_4498_);
v_size_4500_ = lean_ctor_get(v___x_4499_, 0);
lean_inc(v_size_4500_);
lean_dec(v___x_4499_);
v___x_4501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4501_, 0, v_size_4500_);
return v___x_4501_;
}
}
LEAN_EXPORT lean_object* l_Lean_getNumBuiltinAttributesImpl___boxed(lean_object* v_a_4502_){
_start:
{
lean_object* v_res_4503_; 
v_res_4503_ = lean_get_num_attributes();
return v_res_4503_;
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
