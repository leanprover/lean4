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
lean_object* v___x_1178_; lean_object* v_env_1179_; lean_object* v_nextMacroScope_1180_; lean_object* v_ngen_1181_; lean_object* v_auxDeclNGen_1182_; lean_object* v_traceState_1183_; lean_object* v_messages_1184_; lean_object* v_infoState_1185_; lean_object* v_snapshotTasks_1186_; lean_object* v___x_1188_; uint8_t v_isShared_1189_; uint8_t v_isSharedCheck_1197_; 
v___x_1178_ = lean_st_ref_take(v___y_1173_);
v_env_1179_ = lean_ctor_get(v___x_1178_, 0);
v_nextMacroScope_1180_ = lean_ctor_get(v___x_1178_, 1);
v_ngen_1181_ = lean_ctor_get(v___x_1178_, 2);
v_auxDeclNGen_1182_ = lean_ctor_get(v___x_1178_, 3);
v_traceState_1183_ = lean_ctor_get(v___x_1178_, 4);
v_messages_1184_ = lean_ctor_get(v___x_1178_, 6);
v_infoState_1185_ = lean_ctor_get(v___x_1178_, 7);
v_snapshotTasks_1186_ = lean_ctor_get(v___x_1178_, 8);
v_isSharedCheck_1197_ = !lean_is_exclusive(v___x_1178_);
if (v_isSharedCheck_1197_ == 0)
{
lean_object* v_unused_1198_; 
v_unused_1198_ = lean_ctor_get(v___x_1178_, 5);
lean_dec(v_unused_1198_);
v___x_1188_ = v___x_1178_;
v_isShared_1189_ = v_isSharedCheck_1197_;
goto v_resetjp_1187_;
}
else
{
lean_inc(v_snapshotTasks_1186_);
lean_inc(v_infoState_1185_);
lean_inc(v_messages_1184_);
lean_inc(v_traceState_1183_);
lean_inc(v_auxDeclNGen_1182_);
lean_inc(v_ngen_1181_);
lean_inc(v_nextMacroScope_1180_);
lean_inc(v_env_1179_);
lean_dec(v___x_1178_);
v___x_1188_ = lean_box(0);
v_isShared_1189_ = v_isSharedCheck_1197_;
goto v_resetjp_1187_;
}
v_resetjp_1187_:
{
lean_object* v___x_1190_; lean_object* v___x_1192_; 
v___x_1190_ = l_Lean_Environment_setExporting(v_env_1179_, v_isExporting_1174_);
if (v_isShared_1189_ == 0)
{
lean_ctor_set(v___x_1188_, 5, v___x_1175_);
lean_ctor_set(v___x_1188_, 0, v___x_1190_);
v___x_1192_ = v___x_1188_;
goto v_reusejp_1191_;
}
else
{
lean_object* v_reuseFailAlloc_1196_; 
v_reuseFailAlloc_1196_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1196_, 0, v___x_1190_);
lean_ctor_set(v_reuseFailAlloc_1196_, 1, v_nextMacroScope_1180_);
lean_ctor_set(v_reuseFailAlloc_1196_, 2, v_ngen_1181_);
lean_ctor_set(v_reuseFailAlloc_1196_, 3, v_auxDeclNGen_1182_);
lean_ctor_set(v_reuseFailAlloc_1196_, 4, v_traceState_1183_);
lean_ctor_set(v_reuseFailAlloc_1196_, 5, v___x_1175_);
lean_ctor_set(v_reuseFailAlloc_1196_, 6, v_messages_1184_);
lean_ctor_set(v_reuseFailAlloc_1196_, 7, v_infoState_1185_);
lean_ctor_set(v_reuseFailAlloc_1196_, 8, v_snapshotTasks_1186_);
v___x_1192_ = v_reuseFailAlloc_1196_;
goto v_reusejp_1191_;
}
v_reusejp_1191_:
{
lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; 
v___x_1193_ = lean_st_ref_set(v___y_1173_, v___x_1192_);
v___x_1194_ = lean_box(0);
v___x_1195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1195_, 0, v___x_1194_);
return v___x_1195_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___lam__0___boxed(lean_object* v___y_1199_, lean_object* v_isExporting_1200_, lean_object* v___x_1201_, lean_object* v_a_x3f_1202_, lean_object* v___y_1203_){
_start:
{
uint8_t v_isExporting_boxed_1204_; lean_object* v_res_1205_; 
v_isExporting_boxed_1204_ = lean_unbox(v_isExporting_1200_);
v_res_1205_ = l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___lam__0(v___y_1199_, v_isExporting_boxed_1204_, v___x_1201_, v_a_x3f_1202_);
lean_dec(v_a_x3f_1202_);
lean_dec(v___y_1199_);
return v_res_1205_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_1206_; 
v___x_1206_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1206_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_1207_; lean_object* v___x_1208_; 
v___x_1207_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__0, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__0);
v___x_1208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1208_, 0, v___x_1207_);
return v___x_1208_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_1209_; lean_object* v___x_1210_; 
v___x_1209_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1);
v___x_1210_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1210_, 0, v___x_1209_);
lean_ctor_set(v___x_1210_, 1, v___x_1209_);
return v___x_1210_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg(lean_object* v_x_1211_, uint8_t v_isExporting_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_){
_start:
{
lean_object* v___x_1216_; lean_object* v_env_1217_; uint8_t v_isExporting_1218_; lean_object* v___x_1219_; lean_object* v_env_1220_; lean_object* v_nextMacroScope_1221_; lean_object* v_ngen_1222_; lean_object* v_auxDeclNGen_1223_; lean_object* v_traceState_1224_; lean_object* v_messages_1225_; lean_object* v_infoState_1226_; lean_object* v_snapshotTasks_1227_; lean_object* v___x_1229_; uint8_t v_isShared_1230_; uint8_t v_isSharedCheck_1266_; 
v___x_1216_ = lean_st_ref_get(v___y_1214_);
v_env_1217_ = lean_ctor_get(v___x_1216_, 0);
lean_inc_ref(v_env_1217_);
lean_dec(v___x_1216_);
v_isExporting_1218_ = lean_ctor_get_uint8(v_env_1217_, sizeof(void*)*8);
lean_dec_ref(v_env_1217_);
v___x_1219_ = lean_st_ref_take(v___y_1214_);
v_env_1220_ = lean_ctor_get(v___x_1219_, 0);
v_nextMacroScope_1221_ = lean_ctor_get(v___x_1219_, 1);
v_ngen_1222_ = lean_ctor_get(v___x_1219_, 2);
v_auxDeclNGen_1223_ = lean_ctor_get(v___x_1219_, 3);
v_traceState_1224_ = lean_ctor_get(v___x_1219_, 4);
v_messages_1225_ = lean_ctor_get(v___x_1219_, 6);
v_infoState_1226_ = lean_ctor_get(v___x_1219_, 7);
v_snapshotTasks_1227_ = lean_ctor_get(v___x_1219_, 8);
v_isSharedCheck_1266_ = !lean_is_exclusive(v___x_1219_);
if (v_isSharedCheck_1266_ == 0)
{
lean_object* v_unused_1267_; 
v_unused_1267_ = lean_ctor_get(v___x_1219_, 5);
lean_dec(v_unused_1267_);
v___x_1229_ = v___x_1219_;
v_isShared_1230_ = v_isSharedCheck_1266_;
goto v_resetjp_1228_;
}
else
{
lean_inc(v_snapshotTasks_1227_);
lean_inc(v_infoState_1226_);
lean_inc(v_messages_1225_);
lean_inc(v_traceState_1224_);
lean_inc(v_auxDeclNGen_1223_);
lean_inc(v_ngen_1222_);
lean_inc(v_nextMacroScope_1221_);
lean_inc(v_env_1220_);
lean_dec(v___x_1219_);
v___x_1229_ = lean_box(0);
v_isShared_1230_ = v_isSharedCheck_1266_;
goto v_resetjp_1228_;
}
v_resetjp_1228_:
{
lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1234_; 
v___x_1231_ = l_Lean_Environment_setExporting(v_env_1220_, v_isExporting_1212_);
v___x_1232_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2);
if (v_isShared_1230_ == 0)
{
lean_ctor_set(v___x_1229_, 5, v___x_1232_);
lean_ctor_set(v___x_1229_, 0, v___x_1231_);
v___x_1234_ = v___x_1229_;
goto v_reusejp_1233_;
}
else
{
lean_object* v_reuseFailAlloc_1265_; 
v_reuseFailAlloc_1265_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1265_, 0, v___x_1231_);
lean_ctor_set(v_reuseFailAlloc_1265_, 1, v_nextMacroScope_1221_);
lean_ctor_set(v_reuseFailAlloc_1265_, 2, v_ngen_1222_);
lean_ctor_set(v_reuseFailAlloc_1265_, 3, v_auxDeclNGen_1223_);
lean_ctor_set(v_reuseFailAlloc_1265_, 4, v_traceState_1224_);
lean_ctor_set(v_reuseFailAlloc_1265_, 5, v___x_1232_);
lean_ctor_set(v_reuseFailAlloc_1265_, 6, v_messages_1225_);
lean_ctor_set(v_reuseFailAlloc_1265_, 7, v_infoState_1226_);
lean_ctor_set(v_reuseFailAlloc_1265_, 8, v_snapshotTasks_1227_);
v___x_1234_ = v_reuseFailAlloc_1265_;
goto v_reusejp_1233_;
}
v_reusejp_1233_:
{
lean_object* v___x_1235_; lean_object* v_r_1236_; 
v___x_1235_ = lean_st_ref_set(v___y_1214_, v___x_1234_);
lean_inc(v___y_1214_);
lean_inc_ref(v___y_1213_);
v_r_1236_ = lean_apply_3(v_x_1211_, v___y_1213_, v___y_1214_, lean_box(0));
if (lean_obj_tag(v_r_1236_) == 0)
{
lean_object* v_a_1237_; lean_object* v___x_1239_; uint8_t v_isShared_1240_; uint8_t v_isSharedCheck_1253_; 
v_a_1237_ = lean_ctor_get(v_r_1236_, 0);
v_isSharedCheck_1253_ = !lean_is_exclusive(v_r_1236_);
if (v_isSharedCheck_1253_ == 0)
{
v___x_1239_ = v_r_1236_;
v_isShared_1240_ = v_isSharedCheck_1253_;
goto v_resetjp_1238_;
}
else
{
lean_inc(v_a_1237_);
lean_dec(v_r_1236_);
v___x_1239_ = lean_box(0);
v_isShared_1240_ = v_isSharedCheck_1253_;
goto v_resetjp_1238_;
}
v_resetjp_1238_:
{
lean_object* v___x_1242_; 
lean_inc(v_a_1237_);
if (v_isShared_1240_ == 0)
{
lean_ctor_set_tag(v___x_1239_, 1);
v___x_1242_ = v___x_1239_;
goto v_reusejp_1241_;
}
else
{
lean_object* v_reuseFailAlloc_1252_; 
v_reuseFailAlloc_1252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1252_, 0, v_a_1237_);
v___x_1242_ = v_reuseFailAlloc_1252_;
goto v_reusejp_1241_;
}
v_reusejp_1241_:
{
lean_object* v___x_1243_; lean_object* v___x_1245_; uint8_t v_isShared_1246_; uint8_t v_isSharedCheck_1250_; 
v___x_1243_ = l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___lam__0(v___y_1214_, v_isExporting_1218_, v___x_1232_, v___x_1242_);
lean_dec_ref(v___x_1242_);
v_isSharedCheck_1250_ = !lean_is_exclusive(v___x_1243_);
if (v_isSharedCheck_1250_ == 0)
{
lean_object* v_unused_1251_; 
v_unused_1251_ = lean_ctor_get(v___x_1243_, 0);
lean_dec(v_unused_1251_);
v___x_1245_ = v___x_1243_;
v_isShared_1246_ = v_isSharedCheck_1250_;
goto v_resetjp_1244_;
}
else
{
lean_dec(v___x_1243_);
v___x_1245_ = lean_box(0);
v_isShared_1246_ = v_isSharedCheck_1250_;
goto v_resetjp_1244_;
}
v_resetjp_1244_:
{
lean_object* v___x_1248_; 
if (v_isShared_1246_ == 0)
{
lean_ctor_set(v___x_1245_, 0, v_a_1237_);
v___x_1248_ = v___x_1245_;
goto v_reusejp_1247_;
}
else
{
lean_object* v_reuseFailAlloc_1249_; 
v_reuseFailAlloc_1249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1249_, 0, v_a_1237_);
v___x_1248_ = v_reuseFailAlloc_1249_;
goto v_reusejp_1247_;
}
v_reusejp_1247_:
{
return v___x_1248_;
}
}
}
}
}
else
{
lean_object* v_a_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1258_; uint8_t v_isShared_1259_; uint8_t v_isSharedCheck_1263_; 
v_a_1254_ = lean_ctor_get(v_r_1236_, 0);
lean_inc(v_a_1254_);
lean_dec_ref(v_r_1236_);
v___x_1255_ = lean_box(0);
v___x_1256_ = l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___lam__0(v___y_1214_, v_isExporting_1218_, v___x_1232_, v___x_1255_);
v_isSharedCheck_1263_ = !lean_is_exclusive(v___x_1256_);
if (v_isSharedCheck_1263_ == 0)
{
lean_object* v_unused_1264_; 
v_unused_1264_ = lean_ctor_get(v___x_1256_, 0);
lean_dec(v_unused_1264_);
v___x_1258_ = v___x_1256_;
v_isShared_1259_ = v_isSharedCheck_1263_;
goto v_resetjp_1257_;
}
else
{
lean_dec(v___x_1256_);
v___x_1258_ = lean_box(0);
v_isShared_1259_ = v_isSharedCheck_1263_;
goto v_resetjp_1257_;
}
v_resetjp_1257_:
{
lean_object* v___x_1261_; 
if (v_isShared_1259_ == 0)
{
lean_ctor_set_tag(v___x_1258_, 1);
lean_ctor_set(v___x_1258_, 0, v_a_1254_);
v___x_1261_ = v___x_1258_;
goto v_reusejp_1260_;
}
else
{
lean_object* v_reuseFailAlloc_1262_; 
v_reuseFailAlloc_1262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1262_, 0, v_a_1254_);
v___x_1261_ = v_reuseFailAlloc_1262_;
goto v_reusejp_1260_;
}
v_reusejp_1260_:
{
return v___x_1261_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___boxed(lean_object* v_x_1268_, lean_object* v_isExporting_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_){
_start:
{
uint8_t v_isExporting_boxed_1273_; lean_object* v_res_1274_; 
v_isExporting_boxed_1273_ = lean_unbox(v_isExporting_1269_);
v_res_1274_ = l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg(v_x_1268_, v_isExporting_boxed_1273_, v___y_1270_, v___y_1271_);
lean_dec(v___y_1271_);
lean_dec_ref(v___y_1270_);
return v_res_1274_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2(lean_object* v_00_u03b1_1275_, lean_object* v_x_1276_, uint8_t v_isExporting_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_){
_start:
{
lean_object* v___x_1281_; 
v___x_1281_ = l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg(v_x_1276_, v_isExporting_1277_, v___y_1278_, v___y_1279_);
return v___x_1281_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___boxed(lean_object* v_00_u03b1_1282_, lean_object* v_x_1283_, lean_object* v_isExporting_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_){
_start:
{
uint8_t v_isExporting_boxed_1288_; lean_object* v_res_1289_; 
v_isExporting_boxed_1288_ = lean_unbox(v_isExporting_1284_);
v_res_1289_ = l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2(v_00_u03b1_1282_, v_x_1283_, v_isExporting_boxed_1288_, v___y_1285_, v___y_1286_);
lean_dec(v___y_1286_);
lean_dec_ref(v___y_1285_);
return v_res_1289_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0_spec__3(lean_object* v_opts_1290_, lean_object* v_opt_1291_){
_start:
{
lean_object* v_name_1292_; lean_object* v_defValue_1293_; lean_object* v_map_1294_; lean_object* v___x_1295_; 
v_name_1292_ = lean_ctor_get(v_opt_1291_, 0);
v_defValue_1293_ = lean_ctor_get(v_opt_1291_, 1);
v_map_1294_ = lean_ctor_get(v_opts_1290_, 0);
v___x_1295_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1294_, v_name_1292_);
if (lean_obj_tag(v___x_1295_) == 0)
{
uint8_t v___x_1296_; 
v___x_1296_ = lean_unbox(v_defValue_1293_);
return v___x_1296_;
}
else
{
lean_object* v_val_1297_; 
v_val_1297_ = lean_ctor_get(v___x_1295_, 0);
lean_inc(v_val_1297_);
lean_dec_ref(v___x_1295_);
if (lean_obj_tag(v_val_1297_) == 1)
{
uint8_t v_v_1298_; 
v_v_1298_ = lean_ctor_get_uint8(v_val_1297_, 0);
lean_dec_ref(v_val_1297_);
return v_v_1298_;
}
else
{
uint8_t v___x_1299_; 
lean_dec(v_val_1297_);
v___x_1299_ = lean_unbox(v_defValue_1293_);
return v___x_1299_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0_spec__3___boxed(lean_object* v_opts_1300_, lean_object* v_opt_1301_){
_start:
{
uint8_t v_res_1302_; lean_object* v_r_1303_; 
v_res_1302_ = l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0_spec__3(v_opts_1300_, v_opt_1301_);
lean_dec_ref(v_opt_1301_);
lean_dec_ref(v_opts_1300_);
v_r_1303_ = lean_box(v_res_1302_);
return v_r_1303_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0(uint8_t v___y_1311_, uint8_t v_suppressElabErrors_1312_, lean_object* v_x_1313_){
_start:
{
if (lean_obj_tag(v_x_1313_) == 1)
{
lean_object* v_pre_1314_; 
v_pre_1314_ = lean_ctor_get(v_x_1313_, 0);
switch(lean_obj_tag(v_pre_1314_))
{
case 1:
{
lean_object* v_pre_1315_; 
v_pre_1315_ = lean_ctor_get(v_pre_1314_, 0);
switch(lean_obj_tag(v_pre_1315_))
{
case 0:
{
lean_object* v_str_1316_; lean_object* v_str_1317_; lean_object* v___x_1318_; uint8_t v___x_1319_; 
v_str_1316_ = lean_ctor_get(v_x_1313_, 1);
v_str_1317_ = lean_ctor_get(v_pre_1314_, 1);
v___x_1318_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__0));
v___x_1319_ = lean_string_dec_eq(v_str_1317_, v___x_1318_);
if (v___x_1319_ == 0)
{
lean_object* v___x_1320_; uint8_t v___x_1321_; 
v___x_1320_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__2));
v___x_1321_ = lean_string_dec_eq(v_str_1317_, v___x_1320_);
if (v___x_1321_ == 0)
{
return v___y_1311_;
}
else
{
lean_object* v___x_1322_; uint8_t v___x_1323_; 
v___x_1322_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__1));
v___x_1323_ = lean_string_dec_eq(v_str_1316_, v___x_1322_);
if (v___x_1323_ == 0)
{
return v___y_1311_;
}
else
{
return v_suppressElabErrors_1312_;
}
}
}
else
{
lean_object* v___x_1324_; uint8_t v___x_1325_; 
v___x_1324_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__2));
v___x_1325_ = lean_string_dec_eq(v_str_1316_, v___x_1324_);
if (v___x_1325_ == 0)
{
return v___y_1311_;
}
else
{
return v_suppressElabErrors_1312_;
}
}
}
case 1:
{
lean_object* v_pre_1326_; 
v_pre_1326_ = lean_ctor_get(v_pre_1315_, 0);
if (lean_obj_tag(v_pre_1326_) == 0)
{
lean_object* v_str_1327_; lean_object* v_str_1328_; lean_object* v_str_1329_; lean_object* v___x_1330_; uint8_t v___x_1331_; 
v_str_1327_ = lean_ctor_get(v_x_1313_, 1);
v_str_1328_ = lean_ctor_get(v_pre_1314_, 1);
v_str_1329_ = lean_ctor_get(v_pre_1315_, 1);
v___x_1330_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__3));
v___x_1331_ = lean_string_dec_eq(v_str_1329_, v___x_1330_);
if (v___x_1331_ == 0)
{
return v___y_1311_;
}
else
{
lean_object* v___x_1332_; uint8_t v___x_1333_; 
v___x_1332_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__4));
v___x_1333_ = lean_string_dec_eq(v_str_1328_, v___x_1332_);
if (v___x_1333_ == 0)
{
return v___y_1311_;
}
else
{
lean_object* v___x_1334_; uint8_t v___x_1335_; 
v___x_1334_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__5));
v___x_1335_ = lean_string_dec_eq(v_str_1327_, v___x_1334_);
if (v___x_1335_ == 0)
{
return v___y_1311_;
}
else
{
return v_suppressElabErrors_1312_;
}
}
}
}
else
{
return v___y_1311_;
}
}
default: 
{
return v___y_1311_;
}
}
}
case 0:
{
lean_object* v_str_1336_; lean_object* v___x_1337_; uint8_t v___x_1338_; 
v_str_1336_ = lean_ctor_get(v_x_1313_, 1);
v___x_1337_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__6));
v___x_1338_ = lean_string_dec_eq(v_str_1336_, v___x_1337_);
if (v___x_1338_ == 0)
{
return v___y_1311_;
}
else
{
return v_suppressElabErrors_1312_;
}
}
default: 
{
return v___y_1311_;
}
}
}
else
{
return v___y_1311_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___boxed(lean_object* v___y_1339_, lean_object* v_suppressElabErrors_1340_, lean_object* v_x_1341_){
_start:
{
uint8_t v___y_4967__boxed_1342_; uint8_t v_suppressElabErrors_boxed_1343_; uint8_t v_res_1344_; lean_object* v_r_1345_; 
v___y_4967__boxed_1342_ = lean_unbox(v___y_1339_);
v_suppressElabErrors_boxed_1343_ = lean_unbox(v_suppressElabErrors_1340_);
v_res_1344_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0(v___y_4967__boxed_1342_, v_suppressElabErrors_boxed_1343_, v_x_1341_);
lean_dec(v_x_1341_);
v_r_1345_ = lean_box(v_res_1344_);
return v_r_1345_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6(lean_object* v_ref_1346_, lean_object* v_msgData_1347_, uint8_t v_severity_1348_, uint8_t v_isSilent_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_){
_start:
{
uint8_t v___y_1354_; lean_object* v___y_1355_; uint8_t v___y_1356_; lean_object* v___y_1357_; lean_object* v___y_1358_; lean_object* v___y_1359_; lean_object* v___y_1360_; lean_object* v___y_1361_; lean_object* v___y_1362_; lean_object* v___y_1390_; uint8_t v___y_1391_; uint8_t v___y_1392_; uint8_t v___y_1393_; lean_object* v___y_1394_; lean_object* v___y_1395_; lean_object* v___y_1396_; lean_object* v___y_1397_; lean_object* v___y_1415_; lean_object* v___y_1416_; uint8_t v___y_1417_; uint8_t v___y_1418_; lean_object* v___y_1419_; uint8_t v___y_1420_; lean_object* v___y_1421_; lean_object* v___y_1422_; lean_object* v___y_1426_; uint8_t v___y_1427_; uint8_t v___y_1428_; lean_object* v___y_1429_; lean_object* v___y_1430_; lean_object* v___y_1431_; uint8_t v___y_1432_; uint8_t v___x_1437_; lean_object* v___y_1439_; uint8_t v___y_1440_; lean_object* v___y_1441_; lean_object* v___y_1442_; lean_object* v___y_1443_; uint8_t v___y_1444_; uint8_t v___y_1445_; uint8_t v___y_1447_; uint8_t v___x_1462_; 
v___x_1437_ = 2;
v___x_1462_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1348_, v___x_1437_);
if (v___x_1462_ == 0)
{
v___y_1447_ = v___x_1462_;
goto v___jp_1446_;
}
else
{
uint8_t v___x_1463_; 
lean_inc_ref(v_msgData_1347_);
v___x_1463_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_1347_);
v___y_1447_ = v___x_1463_;
goto v___jp_1446_;
}
v___jp_1353_:
{
lean_object* v___x_1363_; lean_object* v_currNamespace_1364_; lean_object* v_openDecls_1365_; lean_object* v_env_1366_; lean_object* v_nextMacroScope_1367_; lean_object* v_ngen_1368_; lean_object* v_auxDeclNGen_1369_; lean_object* v_traceState_1370_; lean_object* v_cache_1371_; lean_object* v_messages_1372_; lean_object* v_infoState_1373_; lean_object* v_snapshotTasks_1374_; lean_object* v___x_1376_; uint8_t v_isShared_1377_; uint8_t v_isSharedCheck_1388_; 
v___x_1363_ = lean_st_ref_take(v___y_1362_);
v_currNamespace_1364_ = lean_ctor_get(v___y_1361_, 6);
v_openDecls_1365_ = lean_ctor_get(v___y_1361_, 7);
v_env_1366_ = lean_ctor_get(v___x_1363_, 0);
v_nextMacroScope_1367_ = lean_ctor_get(v___x_1363_, 1);
v_ngen_1368_ = lean_ctor_get(v___x_1363_, 2);
v_auxDeclNGen_1369_ = lean_ctor_get(v___x_1363_, 3);
v_traceState_1370_ = lean_ctor_get(v___x_1363_, 4);
v_cache_1371_ = lean_ctor_get(v___x_1363_, 5);
v_messages_1372_ = lean_ctor_get(v___x_1363_, 6);
v_infoState_1373_ = lean_ctor_get(v___x_1363_, 7);
v_snapshotTasks_1374_ = lean_ctor_get(v___x_1363_, 8);
v_isSharedCheck_1388_ = !lean_is_exclusive(v___x_1363_);
if (v_isSharedCheck_1388_ == 0)
{
v___x_1376_ = v___x_1363_;
v_isShared_1377_ = v_isSharedCheck_1388_;
goto v_resetjp_1375_;
}
else
{
lean_inc(v_snapshotTasks_1374_);
lean_inc(v_infoState_1373_);
lean_inc(v_messages_1372_);
lean_inc(v_cache_1371_);
lean_inc(v_traceState_1370_);
lean_inc(v_auxDeclNGen_1369_);
lean_inc(v_ngen_1368_);
lean_inc(v_nextMacroScope_1367_);
lean_inc(v_env_1366_);
lean_dec(v___x_1363_);
v___x_1376_ = lean_box(0);
v_isShared_1377_ = v_isSharedCheck_1388_;
goto v_resetjp_1375_;
}
v_resetjp_1375_:
{
lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1383_; 
lean_inc(v_openDecls_1365_);
lean_inc(v_currNamespace_1364_);
v___x_1378_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1378_, 0, v_currNamespace_1364_);
lean_ctor_set(v___x_1378_, 1, v_openDecls_1365_);
v___x_1379_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1379_, 0, v___x_1378_);
lean_ctor_set(v___x_1379_, 1, v___y_1359_);
lean_inc_ref(v___y_1360_);
lean_inc_ref(v___y_1358_);
v___x_1380_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1380_, 0, v___y_1358_);
lean_ctor_set(v___x_1380_, 1, v___y_1357_);
lean_ctor_set(v___x_1380_, 2, v___y_1355_);
lean_ctor_set(v___x_1380_, 3, v___y_1360_);
lean_ctor_set(v___x_1380_, 4, v___x_1379_);
lean_ctor_set_uint8(v___x_1380_, sizeof(void*)*5, v___y_1356_);
lean_ctor_set_uint8(v___x_1380_, sizeof(void*)*5 + 1, v___y_1354_);
lean_ctor_set_uint8(v___x_1380_, sizeof(void*)*5 + 2, v_isSilent_1349_);
v___x_1381_ = l_Lean_MessageLog_add(v___x_1380_, v_messages_1372_);
if (v_isShared_1377_ == 0)
{
lean_ctor_set(v___x_1376_, 6, v___x_1381_);
v___x_1383_ = v___x_1376_;
goto v_reusejp_1382_;
}
else
{
lean_object* v_reuseFailAlloc_1387_; 
v_reuseFailAlloc_1387_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1387_, 0, v_env_1366_);
lean_ctor_set(v_reuseFailAlloc_1387_, 1, v_nextMacroScope_1367_);
lean_ctor_set(v_reuseFailAlloc_1387_, 2, v_ngen_1368_);
lean_ctor_set(v_reuseFailAlloc_1387_, 3, v_auxDeclNGen_1369_);
lean_ctor_set(v_reuseFailAlloc_1387_, 4, v_traceState_1370_);
lean_ctor_set(v_reuseFailAlloc_1387_, 5, v_cache_1371_);
lean_ctor_set(v_reuseFailAlloc_1387_, 6, v___x_1381_);
lean_ctor_set(v_reuseFailAlloc_1387_, 7, v_infoState_1373_);
lean_ctor_set(v_reuseFailAlloc_1387_, 8, v_snapshotTasks_1374_);
v___x_1383_ = v_reuseFailAlloc_1387_;
goto v_reusejp_1382_;
}
v_reusejp_1382_:
{
lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; 
v___x_1384_ = lean_st_ref_set(v___y_1362_, v___x_1383_);
v___x_1385_ = lean_box(0);
v___x_1386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1386_, 0, v___x_1385_);
return v___x_1386_;
}
}
}
v___jp_1389_:
{
lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v_a_1400_; lean_object* v___x_1402_; uint8_t v_isShared_1403_; uint8_t v_isSharedCheck_1413_; 
v___x_1398_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_1347_);
v___x_1399_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0(v___x_1398_, v___y_1350_, v___y_1351_);
v_a_1400_ = lean_ctor_get(v___x_1399_, 0);
v_isSharedCheck_1413_ = !lean_is_exclusive(v___x_1399_);
if (v_isSharedCheck_1413_ == 0)
{
v___x_1402_ = v___x_1399_;
v_isShared_1403_ = v_isSharedCheck_1413_;
goto v_resetjp_1401_;
}
else
{
lean_inc(v_a_1400_);
lean_dec(v___x_1399_);
v___x_1402_ = lean_box(0);
v_isShared_1403_ = v_isSharedCheck_1413_;
goto v_resetjp_1401_;
}
v_resetjp_1401_:
{
lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; 
lean_inc_ref_n(v___y_1396_, 2);
v___x_1404_ = l_Lean_FileMap_toPosition(v___y_1396_, v___y_1395_);
lean_dec(v___y_1395_);
v___x_1405_ = l_Lean_FileMap_toPosition(v___y_1396_, v___y_1397_);
lean_dec(v___y_1397_);
v___x_1406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1406_, 0, v___x_1405_);
v___x_1407_ = ((lean_object*)(l_Lean_instInhabitedAttributeImplCore_default___closed__3));
if (v___y_1393_ == 0)
{
lean_del_object(v___x_1402_);
lean_dec_ref(v___y_1390_);
v___y_1354_ = v___y_1391_;
v___y_1355_ = v___x_1406_;
v___y_1356_ = v___y_1392_;
v___y_1357_ = v___x_1404_;
v___y_1358_ = v___y_1394_;
v___y_1359_ = v_a_1400_;
v___y_1360_ = v___x_1407_;
v___y_1361_ = v___y_1350_;
v___y_1362_ = v___y_1351_;
goto v___jp_1353_;
}
else
{
uint8_t v___x_1408_; 
lean_inc(v_a_1400_);
v___x_1408_ = l_Lean_MessageData_hasTag(v___y_1390_, v_a_1400_);
if (v___x_1408_ == 0)
{
lean_object* v___x_1409_; lean_object* v___x_1411_; 
lean_dec_ref(v___x_1406_);
lean_dec_ref(v___x_1404_);
lean_dec(v_a_1400_);
v___x_1409_ = lean_box(0);
if (v_isShared_1403_ == 0)
{
lean_ctor_set(v___x_1402_, 0, v___x_1409_);
v___x_1411_ = v___x_1402_;
goto v_reusejp_1410_;
}
else
{
lean_object* v_reuseFailAlloc_1412_; 
v_reuseFailAlloc_1412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1412_, 0, v___x_1409_);
v___x_1411_ = v_reuseFailAlloc_1412_;
goto v_reusejp_1410_;
}
v_reusejp_1410_:
{
return v___x_1411_;
}
}
else
{
lean_del_object(v___x_1402_);
v___y_1354_ = v___y_1391_;
v___y_1355_ = v___x_1406_;
v___y_1356_ = v___y_1392_;
v___y_1357_ = v___x_1404_;
v___y_1358_ = v___y_1394_;
v___y_1359_ = v_a_1400_;
v___y_1360_ = v___x_1407_;
v___y_1361_ = v___y_1350_;
v___y_1362_ = v___y_1351_;
goto v___jp_1353_;
}
}
}
}
v___jp_1414_:
{
lean_object* v___x_1423_; 
v___x_1423_ = l_Lean_Syntax_getTailPos_x3f(v___y_1416_, v___y_1418_);
lean_dec(v___y_1416_);
if (lean_obj_tag(v___x_1423_) == 0)
{
lean_inc(v___y_1422_);
v___y_1390_ = v___y_1415_;
v___y_1391_ = v___y_1417_;
v___y_1392_ = v___y_1418_;
v___y_1393_ = v___y_1420_;
v___y_1394_ = v___y_1419_;
v___y_1395_ = v___y_1422_;
v___y_1396_ = v___y_1421_;
v___y_1397_ = v___y_1422_;
goto v___jp_1389_;
}
else
{
lean_object* v_val_1424_; 
v_val_1424_ = lean_ctor_get(v___x_1423_, 0);
lean_inc(v_val_1424_);
lean_dec_ref(v___x_1423_);
v___y_1390_ = v___y_1415_;
v___y_1391_ = v___y_1417_;
v___y_1392_ = v___y_1418_;
v___y_1393_ = v___y_1420_;
v___y_1394_ = v___y_1419_;
v___y_1395_ = v___y_1422_;
v___y_1396_ = v___y_1421_;
v___y_1397_ = v_val_1424_;
goto v___jp_1389_;
}
}
v___jp_1425_:
{
lean_object* v_ref_1433_; lean_object* v___x_1434_; 
v_ref_1433_ = l_Lean_replaceRef(v_ref_1346_, v___y_1430_);
v___x_1434_ = l_Lean_Syntax_getPos_x3f(v_ref_1433_, v___y_1427_);
if (lean_obj_tag(v___x_1434_) == 0)
{
lean_object* v___x_1435_; 
v___x_1435_ = lean_unsigned_to_nat(0u);
v___y_1415_ = v___y_1426_;
v___y_1416_ = v_ref_1433_;
v___y_1417_ = v___y_1432_;
v___y_1418_ = v___y_1427_;
v___y_1419_ = v___y_1429_;
v___y_1420_ = v___y_1428_;
v___y_1421_ = v___y_1431_;
v___y_1422_ = v___x_1435_;
goto v___jp_1414_;
}
else
{
lean_object* v_val_1436_; 
v_val_1436_ = lean_ctor_get(v___x_1434_, 0);
lean_inc(v_val_1436_);
lean_dec_ref(v___x_1434_);
v___y_1415_ = v___y_1426_;
v___y_1416_ = v_ref_1433_;
v___y_1417_ = v___y_1432_;
v___y_1418_ = v___y_1427_;
v___y_1419_ = v___y_1429_;
v___y_1420_ = v___y_1428_;
v___y_1421_ = v___y_1431_;
v___y_1422_ = v_val_1436_;
goto v___jp_1414_;
}
}
v___jp_1438_:
{
if (v___y_1445_ == 0)
{
v___y_1426_ = v___y_1442_;
v___y_1427_ = v___y_1444_;
v___y_1428_ = v___y_1440_;
v___y_1429_ = v___y_1439_;
v___y_1430_ = v___y_1441_;
v___y_1431_ = v___y_1443_;
v___y_1432_ = v_severity_1348_;
goto v___jp_1425_;
}
else
{
v___y_1426_ = v___y_1442_;
v___y_1427_ = v___y_1444_;
v___y_1428_ = v___y_1440_;
v___y_1429_ = v___y_1439_;
v___y_1430_ = v___y_1441_;
v___y_1431_ = v___y_1443_;
v___y_1432_ = v___x_1437_;
goto v___jp_1425_;
}
}
v___jp_1446_:
{
if (v___y_1447_ == 0)
{
lean_object* v_fileName_1448_; lean_object* v_fileMap_1449_; lean_object* v_options_1450_; lean_object* v_ref_1451_; uint8_t v_suppressElabErrors_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___f_1455_; uint8_t v___x_1456_; uint8_t v___x_1457_; 
v_fileName_1448_ = lean_ctor_get(v___y_1350_, 0);
v_fileMap_1449_ = lean_ctor_get(v___y_1350_, 1);
v_options_1450_ = lean_ctor_get(v___y_1350_, 2);
v_ref_1451_ = lean_ctor_get(v___y_1350_, 5);
v_suppressElabErrors_1452_ = lean_ctor_get_uint8(v___y_1350_, sizeof(void*)*14 + 1);
v___x_1453_ = lean_box(v___y_1447_);
v___x_1454_ = lean_box(v_suppressElabErrors_1452_);
v___f_1455_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1455_, 0, v___x_1453_);
lean_closure_set(v___f_1455_, 1, v___x_1454_);
v___x_1456_ = 1;
v___x_1457_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1348_, v___x_1456_);
if (v___x_1457_ == 0)
{
v___y_1439_ = v_fileName_1448_;
v___y_1440_ = v_suppressElabErrors_1452_;
v___y_1441_ = v_ref_1451_;
v___y_1442_ = v___f_1455_;
v___y_1443_ = v_fileMap_1449_;
v___y_1444_ = v___y_1447_;
v___y_1445_ = v___x_1457_;
goto v___jp_1438_;
}
else
{
lean_object* v___x_1458_; uint8_t v___x_1459_; 
v___x_1458_ = l_Lean_warningAsError;
v___x_1459_ = l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0_spec__3(v_options_1450_, v___x_1458_);
v___y_1439_ = v_fileName_1448_;
v___y_1440_ = v_suppressElabErrors_1452_;
v___y_1441_ = v_ref_1451_;
v___y_1442_ = v___f_1455_;
v___y_1443_ = v_fileMap_1449_;
v___y_1444_ = v___y_1447_;
v___y_1445_ = v___x_1459_;
goto v___jp_1438_;
}
}
else
{
lean_object* v___x_1460_; lean_object* v___x_1461_; 
lean_dec_ref(v_msgData_1347_);
v___x_1460_ = lean_box(0);
v___x_1461_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1461_, 0, v___x_1460_);
return v___x_1461_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___boxed(lean_object* v_ref_1464_, lean_object* v_msgData_1465_, lean_object* v_severity_1466_, lean_object* v_isSilent_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_){
_start:
{
uint8_t v_severity_boxed_1471_; uint8_t v_isSilent_boxed_1472_; lean_object* v_res_1473_; 
v_severity_boxed_1471_ = lean_unbox(v_severity_1466_);
v_isSilent_boxed_1472_ = lean_unbox(v_isSilent_1467_);
v_res_1473_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6(v_ref_1464_, v_msgData_1465_, v_severity_boxed_1471_, v_isSilent_boxed_1472_, v___y_1468_, v___y_1469_);
lean_dec(v___y_1469_);
lean_dec_ref(v___y_1468_);
lean_dec(v_ref_1464_);
return v_res_1473_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5(lean_object* v_msgData_1474_, uint8_t v_severity_1475_, uint8_t v_isSilent_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_){
_start:
{
lean_object* v_ref_1480_; lean_object* v___x_1481_; 
v_ref_1480_ = lean_ctor_get(v___y_1477_, 5);
v___x_1481_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6(v_ref_1480_, v_msgData_1474_, v_severity_1475_, v_isSilent_1476_, v___y_1477_, v___y_1478_);
return v___x_1481_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5___boxed(lean_object* v_msgData_1482_, lean_object* v_severity_1483_, lean_object* v_isSilent_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_){
_start:
{
uint8_t v_severity_boxed_1488_; uint8_t v_isSilent_boxed_1489_; lean_object* v_res_1490_; 
v_severity_boxed_1488_ = lean_unbox(v_severity_1483_);
v_isSilent_boxed_1489_ = lean_unbox(v_isSilent_1484_);
v_res_1490_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5(v_msgData_1482_, v_severity_boxed_1488_, v_isSilent_boxed_1489_, v___y_1485_, v___y_1486_);
lean_dec(v___y_1486_);
lean_dec_ref(v___y_1485_);
return v_res_1490_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1(lean_object* v_msgData_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_){
_start:
{
uint8_t v___x_1495_; uint8_t v___x_1496_; lean_object* v___x_1497_; 
v___x_1495_ = 1;
v___x_1496_ = 0;
v___x_1497_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5(v_msgData_1491_, v___x_1495_, v___x_1496_, v___y_1492_, v___y_1493_);
return v___x_1497_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1___boxed(lean_object* v_msgData_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_){
_start:
{
lean_object* v_res_1502_; 
v_res_1502_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1(v_msgData_1498_, v___y_1499_, v___y_1500_);
lean_dec(v___y_1500_);
lean_dec_ref(v___y_1499_);
return v_res_1502_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0___redArg(lean_object* v_opt_1503_, lean_object* v___y_1504_){
_start:
{
lean_object* v_options_1506_; uint8_t v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; 
v_options_1506_ = lean_ctor_get(v___y_1504_, 2);
v___x_1507_ = l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0_spec__3(v_options_1506_, v_opt_1503_);
v___x_1508_ = lean_box(v___x_1507_);
v___x_1509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1509_, 0, v___x_1508_);
return v___x_1509_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0___redArg___boxed(lean_object* v_opt_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_){
_start:
{
lean_object* v_res_1513_; 
v_res_1513_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0___redArg(v_opt_1510_, v___y_1511_);
lean_dec_ref(v___y_1511_);
lean_dec_ref(v_opt_1510_);
return v_res_1513_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1515_; lean_object* v___x_1516_; 
v___x_1515_ = ((lean_object*)(l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__0));
v___x_1516_ = l_Lean_stringToMessageData(v___x_1515_);
return v___x_1516_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__3(void){
_start:
{
lean_object* v___x_1518_; lean_object* v___x_1519_; 
v___x_1518_ = ((lean_object*)(l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__2));
v___x_1519_ = l_Lean_stringToMessageData(v___x_1518_);
return v___x_1519_;
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0(lean_object* v_id_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_){
_start:
{
lean_object* v___x_1524_; lean_object* v_env_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v_a_1528_; lean_object* v___x_1530_; uint8_t v_isShared_1531_; uint8_t v_isSharedCheck_1547_; 
v___x_1524_ = lean_st_ref_get(v___y_1522_);
v_env_1525_ = lean_ctor_get(v___x_1524_, 0);
lean_inc_ref(v_env_1525_);
lean_dec(v___x_1524_);
v___x_1526_ = l_Lean_ResolveName_backward_privateInPublic_warn;
v___x_1527_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0___redArg(v___x_1526_, v___y_1521_);
v_a_1528_ = lean_ctor_get(v___x_1527_, 0);
v_isSharedCheck_1547_ = !lean_is_exclusive(v___x_1527_);
if (v_isSharedCheck_1547_ == 0)
{
v___x_1530_ = v___x_1527_;
v_isShared_1531_ = v_isSharedCheck_1547_;
goto v_resetjp_1529_;
}
else
{
lean_inc(v_a_1528_);
lean_dec(v___x_1527_);
v___x_1530_ = lean_box(0);
v_isShared_1531_ = v_isSharedCheck_1547_;
goto v_resetjp_1529_;
}
v_resetjp_1529_:
{
uint8_t v_isExporting_1537_; 
v_isExporting_1537_ = lean_ctor_get_uint8(v_env_1525_, sizeof(void*)*8);
lean_dec_ref(v_env_1525_);
if (v_isExporting_1537_ == 0)
{
lean_dec(v_a_1528_);
lean_dec(v_id_1520_);
goto v___jp_1532_;
}
else
{
uint8_t v___x_1538_; 
v___x_1538_ = l_Lean_isPrivateName(v_id_1520_);
if (v___x_1538_ == 0)
{
lean_dec(v_a_1528_);
lean_dec(v_id_1520_);
goto v___jp_1532_;
}
else
{
uint8_t v___x_1539_; 
v___x_1539_ = lean_unbox(v_a_1528_);
lean_dec(v_a_1528_);
if (v___x_1539_ == 0)
{
lean_dec(v_id_1520_);
goto v___jp_1532_;
}
else
{
lean_object* v___x_1540_; uint8_t v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; 
lean_del_object(v___x_1530_);
v___x_1540_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__1, &l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__1_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__1);
v___x_1541_ = 0;
v___x_1542_ = l_Lean_MessageData_ofConstName(v_id_1520_, v___x_1541_);
v___x_1543_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1543_, 0, v___x_1540_);
lean_ctor_set(v___x_1543_, 1, v___x_1542_);
v___x_1544_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__3, &l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__3_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__3);
v___x_1545_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1545_, 0, v___x_1543_);
lean_ctor_set(v___x_1545_, 1, v___x_1544_);
v___x_1546_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1(v___x_1545_, v___y_1521_, v___y_1522_);
return v___x_1546_;
}
}
}
v___jp_1532_:
{
lean_object* v___x_1533_; lean_object* v___x_1535_; 
v___x_1533_ = lean_box(0);
if (v_isShared_1531_ == 0)
{
lean_ctor_set(v___x_1530_, 0, v___x_1533_);
v___x_1535_ = v___x_1530_;
goto v_reusejp_1534_;
}
else
{
lean_object* v_reuseFailAlloc_1536_; 
v_reuseFailAlloc_1536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1536_, 0, v___x_1533_);
v___x_1535_ = v_reuseFailAlloc_1536_;
goto v_reusejp_1534_;
}
v_reusejp_1534_:
{
return v___x_1535_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___boxed(lean_object* v_id_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_){
_start:
{
lean_object* v_res_1552_; 
v_res_1552_ = l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0(v_id_1548_, v___y_1549_, v___y_1550_);
lean_dec(v___y_1550_);
lean_dec_ref(v___y_1549_);
return v_res_1552_;
}
}
static lean_object* _init_l_Lean_ensureAttrDeclIsPublic___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1554_; lean_object* v___x_1555_; 
v___x_1554_ = ((lean_object*)(l_Lean_ensureAttrDeclIsPublic___lam__0___closed__0));
v___x_1555_ = l_Lean_stringToMessageData(v___x_1554_);
return v___x_1555_;
}
}
LEAN_EXPORT lean_object* l_Lean_ensureAttrDeclIsPublic___lam__0(lean_object* v_declName_1556_, uint8_t v_isModule_1557_, lean_object* v_attrName_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_){
_start:
{
lean_object* v___x_1562_; 
lean_inc(v_declName_1556_);
v___x_1562_ = l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0(v_declName_1556_, v___y_1559_, v___y_1560_);
if (lean_obj_tag(v___x_1562_) == 0)
{
lean_object* v___x_1563_; lean_object* v_a_1564_; lean_object* v___x_1566_; uint8_t v_isShared_1567_; uint8_t v_isSharedCheck_1584_; 
lean_dec_ref(v___x_1562_);
lean_inc(v_declName_1556_);
v___x_1563_ = l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1___redArg(v_declName_1556_, v_isModule_1557_, v___y_1560_);
v_a_1564_ = lean_ctor_get(v___x_1563_, 0);
v_isSharedCheck_1584_ = !lean_is_exclusive(v___x_1563_);
if (v_isSharedCheck_1584_ == 0)
{
v___x_1566_ = v___x_1563_;
v_isShared_1567_ = v_isSharedCheck_1584_;
goto v_resetjp_1565_;
}
else
{
lean_inc(v_a_1564_);
lean_dec(v___x_1563_);
v___x_1566_ = lean_box(0);
v_isShared_1567_ = v_isSharedCheck_1584_;
goto v_resetjp_1565_;
}
v_resetjp_1565_:
{
uint8_t v___x_1568_; 
v___x_1568_ = lean_unbox(v_a_1564_);
if (v___x_1568_ == 0)
{
lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; uint8_t v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; 
lean_del_object(v___x_1566_);
v___x_1569_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1);
v___x_1570_ = l_Lean_MessageData_ofName(v_attrName_1558_);
v___x_1571_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1571_, 0, v___x_1569_);
lean_ctor_set(v___x_1571_, 1, v___x_1570_);
v___x_1572_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1, &l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1);
v___x_1573_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1573_, 0, v___x_1571_);
lean_ctor_set(v___x_1573_, 1, v___x_1572_);
v___x_1574_ = lean_unbox(v_a_1564_);
lean_dec(v_a_1564_);
v___x_1575_ = l_Lean_MessageData_ofConstName(v_declName_1556_, v___x_1574_);
v___x_1576_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1576_, 0, v___x_1573_);
lean_ctor_set(v___x_1576_, 1, v___x_1575_);
v___x_1577_ = lean_obj_once(&l_Lean_ensureAttrDeclIsPublic___lam__0___closed__1, &l_Lean_ensureAttrDeclIsPublic___lam__0___closed__1_once, _init_l_Lean_ensureAttrDeclIsPublic___lam__0___closed__1);
v___x_1578_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1578_, 0, v___x_1576_);
lean_ctor_set(v___x_1578_, 1, v___x_1577_);
v___x_1579_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_1578_, v___y_1559_, v___y_1560_);
return v___x_1579_;
}
else
{
lean_object* v___x_1580_; lean_object* v___x_1582_; 
lean_dec(v_a_1564_);
lean_dec(v_attrName_1558_);
lean_dec(v_declName_1556_);
v___x_1580_ = lean_box(0);
if (v_isShared_1567_ == 0)
{
lean_ctor_set(v___x_1566_, 0, v___x_1580_);
v___x_1582_ = v___x_1566_;
goto v_reusejp_1581_;
}
else
{
lean_object* v_reuseFailAlloc_1583_; 
v_reuseFailAlloc_1583_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1583_, 0, v___x_1580_);
v___x_1582_ = v_reuseFailAlloc_1583_;
goto v_reusejp_1581_;
}
v_reusejp_1581_:
{
return v___x_1582_;
}
}
}
}
else
{
lean_dec(v_attrName_1558_);
lean_dec(v_declName_1556_);
return v___x_1562_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ensureAttrDeclIsPublic___lam__0___boxed(lean_object* v_declName_1585_, lean_object* v_isModule_1586_, lean_object* v_attrName_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_){
_start:
{
uint8_t v_isModule_boxed_1591_; lean_object* v_res_1592_; 
v_isModule_boxed_1591_ = lean_unbox(v_isModule_1586_);
v_res_1592_ = l_Lean_ensureAttrDeclIsPublic___lam__0(v_declName_1585_, v_isModule_boxed_1591_, v_attrName_1587_, v___y_1588_, v___y_1589_);
lean_dec(v___y_1589_);
lean_dec_ref(v___y_1588_);
return v_res_1592_;
}
}
LEAN_EXPORT lean_object* l_Lean_ensureAttrDeclIsPublic(lean_object* v_attrName_1593_, lean_object* v_declName_1594_, uint8_t v_attrKind_1595_, lean_object* v_a_1596_, lean_object* v_a_1597_){
_start:
{
lean_object* v___x_1599_; lean_object* v_env_1603_; lean_object* v___x_1604_; uint8_t v_isModule_1605_; 
v___x_1599_ = lean_st_ref_get(v_a_1597_);
v_env_1603_ = lean_ctor_get(v___x_1599_, 0);
lean_inc_ref(v_env_1603_);
lean_dec(v___x_1599_);
v___x_1604_ = l_Lean_Environment_header(v_env_1603_);
lean_dec_ref(v_env_1603_);
v_isModule_1605_ = lean_ctor_get_uint8(v___x_1604_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_1604_);
if (v_isModule_1605_ == 0)
{
lean_dec(v_declName_1594_);
lean_dec(v_attrName_1593_);
goto v___jp_1600_;
}
else
{
uint8_t v___x_1606_; uint8_t v___x_1607_; 
v___x_1606_ = 1;
v___x_1607_ = l_Lean_instBEqAttributeKind_beq(v_attrKind_1595_, v___x_1606_);
if (v___x_1607_ == 0)
{
lean_object* v___x_1608_; lean_object* v___f_1609_; lean_object* v___x_1610_; 
v___x_1608_ = lean_box(v_isModule_1605_);
v___f_1609_ = lean_alloc_closure((void*)(l_Lean_ensureAttrDeclIsPublic___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1609_, 0, v_declName_1594_);
lean_closure_set(v___f_1609_, 1, v___x_1608_);
lean_closure_set(v___f_1609_, 2, v_attrName_1593_);
v___x_1610_ = l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg(v___f_1609_, v_isModule_1605_, v_a_1596_, v_a_1597_);
return v___x_1610_;
}
else
{
lean_dec(v_declName_1594_);
lean_dec(v_attrName_1593_);
goto v___jp_1600_;
}
}
v___jp_1600_:
{
lean_object* v___x_1601_; lean_object* v___x_1602_; 
v___x_1601_ = lean_box(0);
v___x_1602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1602_, 0, v___x_1601_);
return v___x_1602_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ensureAttrDeclIsPublic___boxed(lean_object* v_attrName_1611_, lean_object* v_declName_1612_, lean_object* v_attrKind_1613_, lean_object* v_a_1614_, lean_object* v_a_1615_, lean_object* v_a_1616_){
_start:
{
uint8_t v_attrKind_boxed_1617_; lean_object* v_res_1618_; 
v_attrKind_boxed_1617_ = lean_unbox(v_attrKind_1613_);
v_res_1618_ = l_Lean_ensureAttrDeclIsPublic(v_attrName_1611_, v_declName_1612_, v_attrKind_boxed_1617_, v_a_1614_, v_a_1615_);
lean_dec(v_a_1615_);
lean_dec_ref(v_a_1614_);
return v_res_1618_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0(lean_object* v_opt_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_){
_start:
{
lean_object* v___x_1623_; 
v___x_1623_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0___redArg(v_opt_1619_, v___y_1620_);
return v___x_1623_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0___boxed(lean_object* v_opt_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_){
_start:
{
lean_object* v_res_1628_; 
v_res_1628_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0(v_opt_1624_, v___y_1625_, v___y_1626_);
lean_dec(v___y_1626_);
lean_dec_ref(v___y_1625_);
lean_dec_ref(v_opt_1624_);
return v_res_1628_;
}
}
static lean_object* _init_l_Lean_ensureAttrDeclIsMeta___closed__1(void){
_start:
{
lean_object* v___x_1630_; lean_object* v___x_1631_; 
v___x_1630_ = ((lean_object*)(l_Lean_ensureAttrDeclIsMeta___closed__0));
v___x_1631_ = l_Lean_stringToMessageData(v___x_1630_);
return v___x_1631_;
}
}
LEAN_EXPORT lean_object* l_Lean_ensureAttrDeclIsMeta(lean_object* v_attrName_1632_, lean_object* v_declName_1633_, uint8_t v_attrKind_1634_, lean_object* v_a_1635_, lean_object* v_a_1636_){
_start:
{
lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v_env_1640_; lean_object* v___x_1641_; uint8_t v_isModule_1642_; 
v___x_1638_ = lean_st_ref_get(v_a_1636_);
v___x_1639_ = lean_st_ref_get(v_a_1636_);
v_env_1640_ = lean_ctor_get(v___x_1638_, 0);
lean_inc_ref(v_env_1640_);
lean_dec(v___x_1638_);
v___x_1641_ = l_Lean_Environment_header(v_env_1640_);
lean_dec_ref(v_env_1640_);
v_isModule_1642_ = lean_ctor_get_uint8(v___x_1641_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_1641_);
if (v_isModule_1642_ == 0)
{
lean_object* v___x_1643_; 
lean_dec(v___x_1639_);
v___x_1643_ = l_Lean_ensureAttrDeclIsPublic(v_attrName_1632_, v_declName_1633_, v_attrKind_1634_, v_a_1635_, v_a_1636_);
return v___x_1643_;
}
else
{
lean_object* v_env_1644_; uint8_t v___x_1645_; 
v_env_1644_ = lean_ctor_get(v___x_1639_, 0);
lean_inc_ref(v_env_1644_);
lean_dec(v___x_1639_);
lean_inc(v_declName_1633_);
v___x_1645_ = l_Lean_isMarkedMeta(v_env_1644_, v_declName_1633_);
if (v___x_1645_ == 0)
{
lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; 
v___x_1646_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1);
v___x_1647_ = l_Lean_MessageData_ofName(v_attrName_1632_);
v___x_1648_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1648_, 0, v___x_1646_);
lean_ctor_set(v___x_1648_, 1, v___x_1647_);
v___x_1649_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1, &l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1);
v___x_1650_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1650_, 0, v___x_1648_);
lean_ctor_set(v___x_1650_, 1, v___x_1649_);
v___x_1651_ = l_Lean_MessageData_ofConstName(v_declName_1633_, v___x_1645_);
v___x_1652_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1652_, 0, v___x_1650_);
lean_ctor_set(v___x_1652_, 1, v___x_1651_);
v___x_1653_ = lean_obj_once(&l_Lean_ensureAttrDeclIsMeta___closed__1, &l_Lean_ensureAttrDeclIsMeta___closed__1_once, _init_l_Lean_ensureAttrDeclIsMeta___closed__1);
v___x_1654_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1654_, 0, v___x_1652_);
lean_ctor_set(v___x_1654_, 1, v___x_1653_);
v___x_1655_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_1654_, v_a_1635_, v_a_1636_);
return v___x_1655_;
}
else
{
lean_object* v___x_1656_; 
v___x_1656_ = l_Lean_ensureAttrDeclIsPublic(v_attrName_1632_, v_declName_1633_, v_attrKind_1634_, v_a_1635_, v_a_1636_);
return v___x_1656_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ensureAttrDeclIsMeta___boxed(lean_object* v_attrName_1657_, lean_object* v_declName_1658_, lean_object* v_attrKind_1659_, lean_object* v_a_1660_, lean_object* v_a_1661_, lean_object* v_a_1662_){
_start:
{
uint8_t v_attrKind_boxed_1663_; lean_object* v_res_1664_; 
v_attrKind_boxed_1663_ = lean_unbox(v_attrKind_1659_);
v_res_1664_ = l_Lean_ensureAttrDeclIsMeta(v_attrName_1657_, v_declName_1658_, v_attrKind_boxed_1663_, v_a_1660_, v_a_1661_);
lean_dec(v_a_1661_);
lean_dec_ref(v_a_1660_);
return v_res_1664_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__0(lean_object* v_x_1668_, lean_object* v___y_1669_){
_start:
{
lean_object* v___x_1671_; lean_object* v___x_1672_; 
v___x_1671_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___lam__0___closed__1));
v___x_1672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1672_, 0, v___x_1671_);
return v___x_1672_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__0___boxed(lean_object* v_x_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_){
_start:
{
lean_object* v_res_1676_; 
v_res_1676_ = l_Lean_instInhabitedTagAttribute_default___lam__0(v_x_1673_, v___y_1674_);
lean_dec_ref(v___y_1674_);
lean_dec_ref(v_x_1673_);
return v_res_1676_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__1(lean_object* v_s_1677_, lean_object* v_x_1678_){
_start:
{
lean_inc(v_s_1677_);
return v_s_1677_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__1___boxed(lean_object* v_s_1679_, lean_object* v_x_1680_){
_start:
{
lean_object* v_res_1681_; 
v_res_1681_ = l_Lean_instInhabitedTagAttribute_default___lam__1(v_s_1679_, v_x_1680_);
lean_dec(v_x_1680_);
lean_dec(v_s_1679_);
return v_res_1681_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__2(lean_object* v_x_1686_, lean_object* v_x_1687_){
_start:
{
lean_object* v___x_1688_; 
v___x_1688_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___lam__2___closed__1));
return v___x_1688_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__2___boxed(lean_object* v_x_1689_, lean_object* v_x_1690_){
_start:
{
lean_object* v_res_1691_; 
v_res_1691_ = l_Lean_instInhabitedTagAttribute_default___lam__2(v_x_1689_, v_x_1690_);
lean_dec(v_x_1690_);
lean_dec_ref(v_x_1689_);
return v_res_1691_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__3(lean_object* v_x_1692_){
_start:
{
lean_object* v___x_1693_; 
v___x_1693_ = lean_box(0);
return v___x_1693_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__3___boxed(lean_object* v_x_1694_){
_start:
{
lean_object* v_res_1695_; 
v_res_1695_ = l_Lean_instInhabitedTagAttribute_default___lam__3(v_x_1694_);
lean_dec(v_x_1694_);
return v_res_1695_;
}
}
static lean_object* _init_l_Lean_instInhabitedTagAttribute_default___closed__4(void){
_start:
{
lean_object* v___x_1700_; 
v___x_1700_ = l_Lean_instInhabitedEnvExtension_default(lean_box(0));
return v___x_1700_;
}
}
static lean_object* _init_l_Lean_instInhabitedTagAttribute_default___closed__5(void){
_start:
{
lean_object* v___f_1701_; lean_object* v___f_1702_; lean_object* v___f_1703_; lean_object* v___f_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; 
v___f_1701_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___closed__3));
v___f_1702_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___closed__2));
v___f_1703_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___closed__1));
v___f_1704_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___closed__0));
v___x_1705_ = lean_box(0);
v___x_1706_ = lean_obj_once(&l_Lean_instInhabitedTagAttribute_default___closed__4, &l_Lean_instInhabitedTagAttribute_default___closed__4_once, _init_l_Lean_instInhabitedTagAttribute_default___closed__4);
v___x_1707_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1707_, 0, v___x_1706_);
lean_ctor_set(v___x_1707_, 1, v___x_1705_);
lean_ctor_set(v___x_1707_, 2, v___f_1704_);
lean_ctor_set(v___x_1707_, 3, v___f_1703_);
lean_ctor_set(v___x_1707_, 4, v___f_1702_);
lean_ctor_set(v___x_1707_, 5, v___f_1701_);
return v___x_1707_;
}
}
static lean_object* _init_l_Lean_instInhabitedTagAttribute_default___closed__6(void){
_start:
{
lean_object* v___x_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; 
v___x_1708_ = lean_obj_once(&l_Lean_instInhabitedTagAttribute_default___closed__5, &l_Lean_instInhabitedTagAttribute_default___closed__5_once, _init_l_Lean_instInhabitedTagAttribute_default___closed__5);
v___x_1709_ = ((lean_object*)(l_Lean_instInhabitedAttributeImpl_default));
v___x_1710_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1710_, 0, v___x_1709_);
lean_ctor_set(v___x_1710_, 1, v___x_1708_);
return v___x_1710_;
}
}
static lean_object* _init_l_Lean_instInhabitedTagAttribute_default(void){
_start:
{
lean_object* v___x_1711_; 
v___x_1711_ = lean_obj_once(&l_Lean_instInhabitedTagAttribute_default___closed__6, &l_Lean_instInhabitedTagAttribute_default___closed__6_once, _init_l_Lean_instInhabitedTagAttribute_default___closed__6);
return v___x_1711_;
}
}
static lean_object* _init_l_Lean_instInhabitedTagAttribute(void){
_start:
{
lean_object* v___x_1712_; 
v___x_1712_ = l_Lean_instInhabitedTagAttribute_default;
return v___x_1712_;
}
}
static lean_object* _init_l_Lean_registerTagAttribute___auto__1(void){
_start:
{
lean_object* v___x_1713_; 
v___x_1713_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__28, &l_Lean_AttributeImplCore_ref___autoParam___closed__28_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__28);
return v___x_1713_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__0(lean_object* v_x_1714_){
_start:
{
lean_object* v___x_1715_; 
v___x_1715_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___lam__2___closed__0));
return v___x_1715_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__0___boxed(lean_object* v_x_1716_){
_start:
{
lean_object* v_res_1717_; 
v_res_1717_ = l_Lean_registerTagAttribute___lam__0(v_x_1716_);
lean_dec(v_x_1716_);
return v_res_1717_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerTagAttribute_spec__0(lean_object* v_newState_1718_, lean_object* v_x_1719_, lean_object* v_x_1720_){
_start:
{
if (lean_obj_tag(v_x_1720_) == 0)
{
return v_x_1719_;
}
else
{
lean_object* v_head_1721_; lean_object* v_tail_1722_; uint8_t v___x_1723_; 
v_head_1721_ = lean_ctor_get(v_x_1720_, 0);
lean_inc(v_head_1721_);
v_tail_1722_ = lean_ctor_get(v_x_1720_, 1);
lean_inc(v_tail_1722_);
lean_dec_ref(v_x_1720_);
v___x_1723_ = l_Lean_NameSet_contains(v_newState_1718_, v_head_1721_);
if (v___x_1723_ == 0)
{
lean_dec(v_head_1721_);
v_x_1720_ = v_tail_1722_;
goto _start;
}
else
{
lean_object* v___x_1725_; 
v___x_1725_ = l_Lean_NameSet_insert(v_x_1719_, v_head_1721_);
v_x_1719_ = v___x_1725_;
v_x_1720_ = v_tail_1722_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerTagAttribute_spec__0___boxed(lean_object* v_newState_1727_, lean_object* v_x_1728_, lean_object* v_x_1729_){
_start:
{
lean_object* v_res_1730_; 
v_res_1730_ = l_List_foldl___at___00Lean_registerTagAttribute_spec__0(v_newState_1727_, v_x_1728_, v_x_1729_);
lean_dec(v_newState_1727_);
return v_res_1730_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__1(lean_object* v_x_1731_, lean_object* v_newState_1732_, lean_object* v_newConsts_1733_, lean_object* v_s_1734_){
_start:
{
lean_object* v___x_1735_; 
v___x_1735_ = l_List_foldl___at___00Lean_registerTagAttribute_spec__0(v_newState_1732_, v_s_1734_, v_newConsts_1733_);
return v___x_1735_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__1___boxed(lean_object* v_x_1736_, lean_object* v_newState_1737_, lean_object* v_newConsts_1738_, lean_object* v_s_1739_){
_start:
{
lean_object* v_res_1740_; 
v_res_1740_ = l_Lean_registerTagAttribute___lam__1(v_x_1736_, v_newState_1737_, v_newConsts_1738_, v_s_1739_);
lean_dec(v_newState_1737_);
lean_dec(v_x_1736_);
return v_res_1740_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__2(lean_object* v_s_1753_){
_start:
{
lean_object* v___x_1754_; lean_object* v___y_1756_; 
v___x_1754_ = ((lean_object*)(l_Lean_registerTagAttribute___lam__2___closed__5));
if (lean_obj_tag(v_s_1753_) == 0)
{
lean_object* v_size_1760_; 
v_size_1760_ = lean_ctor_get(v_s_1753_, 0);
lean_inc(v_size_1760_);
lean_dec_ref(v_s_1753_);
v___y_1756_ = v_size_1760_;
goto v___jp_1755_;
}
else
{
lean_object* v___x_1761_; 
v___x_1761_ = lean_unsigned_to_nat(0u);
v___y_1756_ = v___x_1761_;
goto v___jp_1755_;
}
v___jp_1755_:
{
lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; 
v___x_1757_ = l_Nat_reprFast(v___y_1756_);
v___x_1758_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1758_, 0, v___x_1757_);
v___x_1759_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1759_, 0, v___x_1754_);
lean_ctor_set(v___x_1759_, 1, v___x_1758_);
return v___x_1759_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4___redArg(lean_object* v_hi_1762_, lean_object* v_pivot_1763_, lean_object* v_as_1764_, lean_object* v_i_1765_, lean_object* v_k_1766_){
_start:
{
uint8_t v___x_1767_; 
v___x_1767_ = lean_nat_dec_lt(v_k_1766_, v_hi_1762_);
if (v___x_1767_ == 0)
{
lean_object* v___x_1768_; lean_object* v___x_1769_; 
lean_dec(v_k_1766_);
v___x_1768_ = lean_array_fswap(v_as_1764_, v_i_1765_, v_hi_1762_);
v___x_1769_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1769_, 0, v_i_1765_);
lean_ctor_set(v___x_1769_, 1, v___x_1768_);
return v___x_1769_;
}
else
{
lean_object* v___x_1770_; uint8_t v___x_1771_; 
v___x_1770_ = lean_array_fget_borrowed(v_as_1764_, v_k_1766_);
v___x_1771_ = l_Lean_Name_quickLt(v___x_1770_, v_pivot_1763_);
if (v___x_1771_ == 0)
{
lean_object* v___x_1772_; lean_object* v___x_1773_; 
v___x_1772_ = lean_unsigned_to_nat(1u);
v___x_1773_ = lean_nat_add(v_k_1766_, v___x_1772_);
lean_dec(v_k_1766_);
v_k_1766_ = v___x_1773_;
goto _start;
}
else
{
lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; 
v___x_1775_ = lean_array_fswap(v_as_1764_, v_i_1765_, v_k_1766_);
v___x_1776_ = lean_unsigned_to_nat(1u);
v___x_1777_ = lean_nat_add(v_i_1765_, v___x_1776_);
lean_dec(v_i_1765_);
v___x_1778_ = lean_nat_add(v_k_1766_, v___x_1776_);
lean_dec(v_k_1766_);
v_as_1764_ = v___x_1775_;
v_i_1765_ = v___x_1777_;
v_k_1766_ = v___x_1778_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4___redArg___boxed(lean_object* v_hi_1780_, lean_object* v_pivot_1781_, lean_object* v_as_1782_, lean_object* v_i_1783_, lean_object* v_k_1784_){
_start:
{
lean_object* v_res_1785_; 
v_res_1785_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4___redArg(v_hi_1780_, v_pivot_1781_, v_as_1782_, v_i_1783_, v_k_1784_);
lean_dec(v_pivot_1781_);
lean_dec(v_hi_1780_);
return v_res_1785_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___redArg(lean_object* v_n_1786_, lean_object* v_as_1787_, lean_object* v_lo_1788_, lean_object* v_hi_1789_){
_start:
{
lean_object* v___y_1791_; uint8_t v___x_1801_; 
v___x_1801_ = lean_nat_dec_lt(v_lo_1788_, v_hi_1789_);
if (v___x_1801_ == 0)
{
lean_dec(v_lo_1788_);
return v_as_1787_;
}
else
{
lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v_mid_1804_; lean_object* v___y_1806_; lean_object* v___y_1812_; lean_object* v___x_1817_; lean_object* v___x_1818_; uint8_t v___x_1819_; 
v___x_1802_ = lean_nat_add(v_lo_1788_, v_hi_1789_);
v___x_1803_ = lean_unsigned_to_nat(1u);
v_mid_1804_ = lean_nat_shiftr(v___x_1802_, v___x_1803_);
lean_dec(v___x_1802_);
v___x_1817_ = lean_array_fget_borrowed(v_as_1787_, v_mid_1804_);
v___x_1818_ = lean_array_fget_borrowed(v_as_1787_, v_lo_1788_);
v___x_1819_ = l_Lean_Name_quickLt(v___x_1817_, v___x_1818_);
if (v___x_1819_ == 0)
{
v___y_1812_ = v_as_1787_;
goto v___jp_1811_;
}
else
{
lean_object* v___x_1820_; 
v___x_1820_ = lean_array_fswap(v_as_1787_, v_lo_1788_, v_mid_1804_);
v___y_1812_ = v___x_1820_;
goto v___jp_1811_;
}
v___jp_1805_:
{
lean_object* v___x_1807_; lean_object* v___x_1808_; uint8_t v___x_1809_; 
v___x_1807_ = lean_array_fget_borrowed(v___y_1806_, v_mid_1804_);
v___x_1808_ = lean_array_fget_borrowed(v___y_1806_, v_hi_1789_);
v___x_1809_ = l_Lean_Name_quickLt(v___x_1807_, v___x_1808_);
if (v___x_1809_ == 0)
{
lean_dec(v_mid_1804_);
v___y_1791_ = v___y_1806_;
goto v___jp_1790_;
}
else
{
lean_object* v___x_1810_; 
v___x_1810_ = lean_array_fswap(v___y_1806_, v_mid_1804_, v_hi_1789_);
lean_dec(v_mid_1804_);
v___y_1791_ = v___x_1810_;
goto v___jp_1790_;
}
}
v___jp_1811_:
{
lean_object* v___x_1813_; lean_object* v___x_1814_; uint8_t v___x_1815_; 
v___x_1813_ = lean_array_fget_borrowed(v___y_1812_, v_hi_1789_);
v___x_1814_ = lean_array_fget_borrowed(v___y_1812_, v_lo_1788_);
v___x_1815_ = l_Lean_Name_quickLt(v___x_1813_, v___x_1814_);
if (v___x_1815_ == 0)
{
v___y_1806_ = v___y_1812_;
goto v___jp_1805_;
}
else
{
lean_object* v___x_1816_; 
v___x_1816_ = lean_array_fswap(v___y_1812_, v_lo_1788_, v_hi_1789_);
v___y_1806_ = v___x_1816_;
goto v___jp_1805_;
}
}
}
v___jp_1790_:
{
lean_object* v_pivot_1792_; lean_object* v___x_1793_; lean_object* v_fst_1794_; lean_object* v_snd_1795_; uint8_t v___x_1796_; 
v_pivot_1792_ = lean_array_fget(v___y_1791_, v_hi_1789_);
lean_inc_n(v_lo_1788_, 2);
v___x_1793_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4___redArg(v_hi_1789_, v_pivot_1792_, v___y_1791_, v_lo_1788_, v_lo_1788_);
lean_dec(v_pivot_1792_);
v_fst_1794_ = lean_ctor_get(v___x_1793_, 0);
lean_inc(v_fst_1794_);
v_snd_1795_ = lean_ctor_get(v___x_1793_, 1);
lean_inc(v_snd_1795_);
lean_dec_ref(v___x_1793_);
v___x_1796_ = lean_nat_dec_le(v_hi_1789_, v_fst_1794_);
if (v___x_1796_ == 0)
{
lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; 
v___x_1797_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___redArg(v_n_1786_, v_snd_1795_, v_lo_1788_, v_fst_1794_);
v___x_1798_ = lean_unsigned_to_nat(1u);
v___x_1799_ = lean_nat_add(v_fst_1794_, v___x_1798_);
lean_dec(v_fst_1794_);
v_as_1787_ = v___x_1797_;
v_lo_1788_ = v___x_1799_;
goto _start;
}
else
{
lean_dec(v_fst_1794_);
lean_dec(v_lo_1788_);
return v_snd_1795_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___redArg___boxed(lean_object* v_n_1821_, lean_object* v_as_1822_, lean_object* v_lo_1823_, lean_object* v_hi_1824_){
_start:
{
lean_object* v_res_1825_; 
v_res_1825_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___redArg(v_n_1821_, v_as_1822_, v_lo_1823_, v_hi_1824_);
lean_dec(v_hi_1824_);
lean_dec(v_n_1821_);
return v_res_1825_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerTagAttribute_spec__2(lean_object* v_env_1826_, lean_object* v_as_1827_, size_t v_i_1828_, size_t v_stop_1829_, lean_object* v_b_1830_){
_start:
{
lean_object* v___y_1832_; uint8_t v___x_1836_; 
v___x_1836_ = lean_usize_dec_eq(v_i_1828_, v_stop_1829_);
if (v___x_1836_ == 0)
{
lean_object* v___x_1837_; uint8_t v___x_1838_; lean_object* v___x_1839_; uint8_t v___x_1840_; 
v___x_1837_ = lean_array_uget_borrowed(v_as_1827_, v_i_1828_);
v___x_1838_ = 1;
lean_inc_ref(v_env_1826_);
v___x_1839_ = l_Lean_Environment_setExporting(v_env_1826_, v___x_1838_);
lean_inc(v___x_1837_);
v___x_1840_ = l_Lean_Environment_contains(v___x_1839_, v___x_1837_, v___x_1836_);
if (v___x_1840_ == 0)
{
v___y_1832_ = v_b_1830_;
goto v___jp_1831_;
}
else
{
lean_object* v___x_1841_; 
lean_inc(v___x_1837_);
v___x_1841_ = lean_array_push(v_b_1830_, v___x_1837_);
v___y_1832_ = v___x_1841_;
goto v___jp_1831_;
}
}
else
{
lean_dec_ref(v_env_1826_);
return v_b_1830_;
}
v___jp_1831_:
{
size_t v___x_1833_; size_t v___x_1834_; 
v___x_1833_ = ((size_t)1ULL);
v___x_1834_ = lean_usize_add(v_i_1828_, v___x_1833_);
v_i_1828_ = v___x_1834_;
v_b_1830_ = v___y_1832_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerTagAttribute_spec__2___boxed(lean_object* v_env_1842_, lean_object* v_as_1843_, lean_object* v_i_1844_, lean_object* v_stop_1845_, lean_object* v_b_1846_){
_start:
{
size_t v_i_boxed_1847_; size_t v_stop_boxed_1848_; lean_object* v_res_1849_; 
v_i_boxed_1847_ = lean_unbox_usize(v_i_1844_);
lean_dec(v_i_1844_);
v_stop_boxed_1848_ = lean_unbox_usize(v_stop_1845_);
lean_dec(v_stop_1845_);
v_res_1849_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerTagAttribute_spec__2(v_env_1842_, v_as_1843_, v_i_boxed_1847_, v_stop_boxed_1848_, v_b_1846_);
lean_dec_ref(v_as_1843_);
return v_res_1849_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerTagAttribute_spec__1_spec__1(lean_object* v_init_1850_, lean_object* v_x_1851_){
_start:
{
if (lean_obj_tag(v_x_1851_) == 0)
{
lean_object* v_k_1852_; lean_object* v_l_1853_; lean_object* v_r_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; 
v_k_1852_ = lean_ctor_get(v_x_1851_, 1);
lean_inc(v_k_1852_);
v_l_1853_ = lean_ctor_get(v_x_1851_, 3);
lean_inc(v_l_1853_);
v_r_1854_ = lean_ctor_get(v_x_1851_, 4);
lean_inc(v_r_1854_);
lean_dec_ref(v_x_1851_);
v___x_1855_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerTagAttribute_spec__1_spec__1(v_init_1850_, v_l_1853_);
v___x_1856_ = lean_array_push(v___x_1855_, v_k_1852_);
v_init_1850_ = v___x_1856_;
v_x_1851_ = v_r_1854_;
goto _start;
}
else
{
return v_init_1850_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__3(lean_object* v_env_1858_, lean_object* v_es_1859_){
_start:
{
lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___y_1863_; lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___y_1880_; lean_object* v___y_1881_; uint8_t v___x_1883_; 
v___x_1860_ = lean_unsigned_to_nat(0u);
v___x_1861_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___lam__2___closed__0));
v___x_1877_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerTagAttribute_spec__1_spec__1(v___x_1861_, v_es_1859_);
v___x_1878_ = lean_array_get_size(v___x_1877_);
v___x_1883_ = lean_nat_dec_eq(v___x_1878_, v___x_1860_);
if (v___x_1883_ == 0)
{
lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___y_1887_; uint8_t v___x_1889_; 
v___x_1884_ = lean_unsigned_to_nat(1u);
v___x_1885_ = lean_nat_sub(v___x_1878_, v___x_1884_);
v___x_1889_ = lean_nat_dec_le(v___x_1860_, v___x_1885_);
if (v___x_1889_ == 0)
{
lean_inc(v___x_1885_);
v___y_1887_ = v___x_1885_;
goto v___jp_1886_;
}
else
{
v___y_1887_ = v___x_1860_;
goto v___jp_1886_;
}
v___jp_1886_:
{
uint8_t v___x_1888_; 
v___x_1888_ = lean_nat_dec_le(v___y_1887_, v___x_1885_);
if (v___x_1888_ == 0)
{
lean_dec(v___x_1885_);
lean_inc(v___y_1887_);
v___y_1880_ = v___y_1887_;
v___y_1881_ = v___y_1887_;
goto v___jp_1879_;
}
else
{
v___y_1880_ = v___y_1887_;
v___y_1881_ = v___x_1885_;
goto v___jp_1879_;
}
}
}
else
{
v___y_1863_ = v___x_1877_;
goto v___jp_1862_;
}
v___jp_1862_:
{
lean_object* v___x_1864_; uint8_t v___x_1865_; 
v___x_1864_ = lean_array_get_size(v___y_1863_);
v___x_1865_ = lean_nat_dec_lt(v___x_1860_, v___x_1864_);
if (v___x_1865_ == 0)
{
lean_object* v___x_1866_; 
lean_dec_ref(v_env_1858_);
v___x_1866_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1866_, 0, v___x_1861_);
lean_ctor_set(v___x_1866_, 1, v___x_1861_);
lean_ctor_set(v___x_1866_, 2, v___y_1863_);
return v___x_1866_;
}
else
{
uint8_t v___x_1867_; 
v___x_1867_ = lean_nat_dec_le(v___x_1864_, v___x_1864_);
if (v___x_1867_ == 0)
{
if (v___x_1865_ == 0)
{
lean_object* v___x_1868_; 
lean_dec_ref(v_env_1858_);
v___x_1868_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1868_, 0, v___x_1861_);
lean_ctor_set(v___x_1868_, 1, v___x_1861_);
lean_ctor_set(v___x_1868_, 2, v___y_1863_);
return v___x_1868_;
}
else
{
size_t v___x_1869_; size_t v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; 
v___x_1869_ = ((size_t)0ULL);
v___x_1870_ = lean_usize_of_nat(v___x_1864_);
v___x_1871_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerTagAttribute_spec__2(v_env_1858_, v___y_1863_, v___x_1869_, v___x_1870_, v___x_1861_);
lean_inc_ref(v___x_1871_);
v___x_1872_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1872_, 0, v___x_1871_);
lean_ctor_set(v___x_1872_, 1, v___x_1871_);
lean_ctor_set(v___x_1872_, 2, v___y_1863_);
return v___x_1872_;
}
}
else
{
size_t v___x_1873_; size_t v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; 
v___x_1873_ = ((size_t)0ULL);
v___x_1874_ = lean_usize_of_nat(v___x_1864_);
v___x_1875_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerTagAttribute_spec__2(v_env_1858_, v___y_1863_, v___x_1873_, v___x_1874_, v___x_1861_);
lean_inc_ref(v___x_1875_);
v___x_1876_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1876_, 0, v___x_1875_);
lean_ctor_set(v___x_1876_, 1, v___x_1875_);
lean_ctor_set(v___x_1876_, 2, v___y_1863_);
return v___x_1876_;
}
}
}
v___jp_1879_:
{
lean_object* v___x_1882_; 
v___x_1882_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___redArg(v___x_1878_, v___x_1877_, v___y_1880_, v___y_1881_);
lean_dec(v___y_1881_);
v___y_1863_ = v___x_1882_;
goto v___jp_1862_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__4(lean_object* v___x_1890_, lean_object* v_x_1891_, lean_object* v_x_1892_){
_start:
{
lean_object* v___x_1894_; 
v___x_1894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1894_, 0, v___x_1890_);
return v___x_1894_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__4___boxed(lean_object* v___x_1895_, lean_object* v_x_1896_, lean_object* v_x_1897_, lean_object* v___y_1898_){
_start:
{
lean_object* v_res_1899_; 
v_res_1899_ = l_Lean_registerTagAttribute___lam__4(v___x_1895_, v_x_1896_, v_x_1897_);
lean_dec_ref(v_x_1897_);
lean_dec_ref(v_x_1896_);
return v_res_1899_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__5(lean_object* v___x_1900_){
_start:
{
lean_object* v___x_1902_; 
v___x_1902_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1902_, 0, v___x_1900_);
return v___x_1902_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__5___boxed(lean_object* v___x_1903_, lean_object* v___y_1904_){
_start:
{
lean_object* v_res_1905_; 
v_res_1905_ = l_Lean_registerTagAttribute___lam__5(v___x_1903_);
return v_res_1905_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__6(lean_object* v_name_1906_, lean_object* v_decl_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_){
_start:
{
lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; 
v___x_1911_ = lean_obj_once(&l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1, &l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1_once, _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1);
v___x_1912_ = l_Lean_MessageData_ofName(v_name_1906_);
v___x_1913_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1913_, 0, v___x_1911_);
lean_ctor_set(v___x_1913_, 1, v___x_1912_);
v___x_1914_ = lean_obj_once(&l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3, &l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3_once, _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3);
v___x_1915_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1915_, 0, v___x_1913_);
lean_ctor_set(v___x_1915_, 1, v___x_1914_);
v___x_1916_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_1915_, v___y_1908_, v___y_1909_);
return v___x_1916_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__6___boxed(lean_object* v_name_1917_, lean_object* v_decl_1918_, lean_object* v___y_1919_, lean_object* v___y_1920_, lean_object* v___y_1921_){
_start:
{
lean_object* v_res_1922_; 
v_res_1922_ = l_Lean_registerTagAttribute___lam__6(v_name_1917_, v_decl_1918_, v___y_1919_, v___y_1920_);
lean_dec(v___y_1920_);
lean_dec_ref(v___y_1919_);
lean_dec(v_decl_1918_);
return v_res_1922_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg(lean_object* v_attrName_1923_, lean_object* v_declName_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_){
_start:
{
lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; uint8_t v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; 
v___x_1928_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1);
v___x_1929_ = l_Lean_MessageData_ofName(v_attrName_1923_);
v___x_1930_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1930_, 0, v___x_1928_);
lean_ctor_set(v___x_1930_, 1, v___x_1929_);
v___x_1931_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__3, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__3_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__3);
v___x_1932_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1932_, 0, v___x_1930_);
lean_ctor_set(v___x_1932_, 1, v___x_1931_);
v___x_1933_ = 0;
v___x_1934_ = l_Lean_MessageData_ofConstName(v_declName_1924_, v___x_1933_);
v___x_1935_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1935_, 0, v___x_1932_);
lean_ctor_set(v___x_1935_, 1, v___x_1934_);
v___x_1936_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__5, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__5_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__5);
v___x_1937_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1937_, 0, v___x_1935_);
lean_ctor_set(v___x_1937_, 1, v___x_1936_);
v___x_1938_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_1937_, v___y_1925_, v___y_1926_);
return v___x_1938_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg___boxed(lean_object* v_attrName_1939_, lean_object* v_declName_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_){
_start:
{
lean_object* v_res_1944_; 
v_res_1944_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg(v_attrName_1939_, v_declName_1940_, v___y_1941_, v___y_1942_);
lean_dec(v___y_1942_);
lean_dec_ref(v___y_1941_);
return v_res_1944_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___redArg(lean_object* v_attrName_1945_, lean_object* v_declName_1946_, lean_object* v_asyncPrefix_x3f_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_){
_start:
{
lean_object* v___y_1952_; 
if (lean_obj_tag(v_asyncPrefix_x3f_1947_) == 0)
{
lean_object* v___x_1965_; 
v___x_1965_ = l_Lean_MessageData_nil;
v___y_1952_ = v___x_1965_;
goto v___jp_1951_;
}
else
{
lean_object* v_val_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; 
v_val_1966_ = lean_ctor_get(v_asyncPrefix_x3f_1947_, 0);
lean_inc(v_val_1966_);
lean_dec_ref(v_asyncPrefix_x3f_1947_);
v___x_1967_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___redArg___closed__3, &l_Lean_throwAttrNotInAsyncCtx___redArg___closed__3_once, _init_l_Lean_throwAttrNotInAsyncCtx___redArg___closed__3);
v___x_1968_ = l_Lean_MessageData_ofName(v_val_1966_);
v___x_1969_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1969_, 0, v___x_1967_);
lean_ctor_set(v___x_1969_, 1, v___x_1968_);
v___x_1970_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__5, &l_Lean_throwAttrMustBeGlobal___redArg___closed__5_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__5);
v___x_1971_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1971_, 0, v___x_1969_);
lean_ctor_set(v___x_1971_, 1, v___x_1970_);
v___y_1952_ = v___x_1971_;
goto v___jp_1951_;
}
v___jp_1951_:
{
lean_object* v___x_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; uint8_t v___x_1958_; lean_object* v___x_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; 
v___x_1953_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1);
v___x_1954_ = l_Lean_MessageData_ofName(v_attrName_1945_);
v___x_1955_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1955_, 0, v___x_1953_);
lean_ctor_set(v___x_1955_, 1, v___x_1954_);
v___x_1956_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__3, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__3_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__3);
v___x_1957_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1957_, 0, v___x_1955_);
lean_ctor_set(v___x_1957_, 1, v___x_1956_);
v___x_1958_ = 0;
v___x_1959_ = l_Lean_MessageData_ofConstName(v_declName_1946_, v___x_1958_);
v___x_1960_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1960_, 0, v___x_1957_);
lean_ctor_set(v___x_1960_, 1, v___x_1959_);
v___x_1961_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___redArg___closed__1, &l_Lean_throwAttrNotInAsyncCtx___redArg___closed__1_once, _init_l_Lean_throwAttrNotInAsyncCtx___redArg___closed__1);
v___x_1962_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1962_, 0, v___x_1960_);
lean_ctor_set(v___x_1962_, 1, v___x_1961_);
v___x_1963_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1963_, 0, v___x_1962_);
lean_ctor_set(v___x_1963_, 1, v___y_1952_);
v___x_1964_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_1963_, v___y_1948_, v___y_1949_);
return v___x_1964_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___redArg___boxed(lean_object* v_attrName_1972_, lean_object* v_declName_1973_, lean_object* v_asyncPrefix_x3f_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_){
_start:
{
lean_object* v_res_1978_; 
v_res_1978_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___redArg(v_attrName_1972_, v_declName_1973_, v_asyncPrefix_x3f_1974_, v___y_1975_, v___y_1976_);
lean_dec(v___y_1976_);
lean_dec_ref(v___y_1975_);
return v_res_1978_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg(lean_object* v_name_1979_, uint8_t v_kind_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_){
_start:
{
lean_object* v___x_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v___y_1990_; 
v___x_1984_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__1, &l_Lean_throwAttrMustBeGlobal___redArg___closed__1_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__1);
v___x_1985_ = l_Lean_MessageData_ofName(v_name_1979_);
v___x_1986_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1986_, 0, v___x_1984_);
lean_ctor_set(v___x_1986_, 1, v___x_1985_);
v___x_1987_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__3, &l_Lean_throwAttrMustBeGlobal___redArg___closed__3_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__3);
v___x_1988_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1988_, 0, v___x_1986_);
lean_ctor_set(v___x_1988_, 1, v___x_1987_);
switch(v_kind_1980_)
{
case 0:
{
lean_object* v___x_1997_; 
v___x_1997_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__0));
v___y_1990_ = v___x_1997_;
goto v___jp_1989_;
}
case 1:
{
lean_object* v___x_1998_; 
v___x_1998_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__1));
v___y_1990_ = v___x_1998_;
goto v___jp_1989_;
}
default: 
{
lean_object* v___x_1999_; 
v___x_1999_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__2));
v___y_1990_ = v___x_1999_;
goto v___jp_1989_;
}
}
v___jp_1989_:
{
lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; 
lean_inc_ref(v___y_1990_);
v___x_1991_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1991_, 0, v___y_1990_);
v___x_1992_ = l_Lean_MessageData_ofFormat(v___x_1991_);
v___x_1993_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1993_, 0, v___x_1988_);
lean_ctor_set(v___x_1993_, 1, v___x_1992_);
v___x_1994_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__5, &l_Lean_throwAttrMustBeGlobal___redArg___closed__5_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__5);
v___x_1995_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1995_, 0, v___x_1993_);
lean_ctor_set(v___x_1995_, 1, v___x_1994_);
v___x_1996_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_1995_, v___y_1981_, v___y_1982_);
return v___x_1996_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg___boxed(lean_object* v_name_2000_, lean_object* v_kind_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_){
_start:
{
uint8_t v_kind_boxed_2005_; lean_object* v_res_2006_; 
v_kind_boxed_2005_ = lean_unbox(v_kind_2001_);
v_res_2006_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg(v_name_2000_, v_kind_boxed_2005_, v___y_2002_, v___y_2003_);
lean_dec(v___y_2003_);
lean_dec_ref(v___y_2002_);
return v_res_2006_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__7(lean_object* v_validate_2007_, lean_object* v_a_2008_, lean_object* v_name_2009_, lean_object* v_decl_2010_, lean_object* v_stx_2011_, uint8_t v_kind_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_){
_start:
{
lean_object* v___y_2017_; lean_object* v___y_2018_; lean_object* v___y_2052_; lean_object* v___y_2053_; lean_object* v___y_2054_; lean_object* v___y_2061_; lean_object* v___y_2062_; lean_object* v___x_2067_; 
v___x_2067_ = l_Lean_Attribute_Builtin_ensureNoArgs(v_stx_2011_, v___y_2013_, v___y_2014_);
if (lean_obj_tag(v___x_2067_) == 0)
{
uint8_t v___x_2068_; uint8_t v___x_2069_; 
lean_dec_ref(v___x_2067_);
v___x_2068_ = 0;
v___x_2069_ = l_Lean_instBEqAttributeKind_beq(v_kind_2012_, v___x_2068_);
if (v___x_2069_ == 0)
{
lean_object* v___x_2070_; 
lean_dec(v_decl_2010_);
lean_dec_ref(v_a_2008_);
lean_dec_ref(v_validate_2007_);
v___x_2070_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg(v_name_2009_, v_kind_2012_, v___y_2013_, v___y_2014_);
return v___x_2070_;
}
else
{
v___y_2061_ = v___y_2013_;
v___y_2062_ = v___y_2014_;
goto v___jp_2060_;
}
}
else
{
lean_dec(v_decl_2010_);
lean_dec(v_name_2009_);
lean_dec_ref(v_a_2008_);
lean_dec_ref(v_validate_2007_);
return v___x_2067_;
}
v___jp_2016_:
{
lean_object* v___x_2019_; 
lean_inc(v___y_2018_);
lean_inc_ref(v___y_2017_);
lean_inc(v_decl_2010_);
v___x_2019_ = lean_apply_4(v_validate_2007_, v_decl_2010_, v___y_2017_, v___y_2018_, lean_box(0));
if (lean_obj_tag(v___x_2019_) == 0)
{
lean_object* v___x_2021_; uint8_t v_isShared_2022_; uint8_t v_isSharedCheck_2049_; 
v_isSharedCheck_2049_ = !lean_is_exclusive(v___x_2019_);
if (v_isSharedCheck_2049_ == 0)
{
lean_object* v_unused_2050_; 
v_unused_2050_ = lean_ctor_get(v___x_2019_, 0);
lean_dec(v_unused_2050_);
v___x_2021_ = v___x_2019_;
v_isShared_2022_ = v_isSharedCheck_2049_;
goto v_resetjp_2020_;
}
else
{
lean_dec(v___x_2019_);
v___x_2021_ = lean_box(0);
v_isShared_2022_ = v_isSharedCheck_2049_;
goto v_resetjp_2020_;
}
v_resetjp_2020_:
{
lean_object* v___x_2023_; lean_object* v_toEnvExtension_2024_; lean_object* v_env_2025_; lean_object* v_nextMacroScope_2026_; lean_object* v_ngen_2027_; lean_object* v_auxDeclNGen_2028_; lean_object* v_traceState_2029_; lean_object* v_messages_2030_; lean_object* v_infoState_2031_; lean_object* v_snapshotTasks_2032_; lean_object* v___x_2034_; uint8_t v_isShared_2035_; uint8_t v_isSharedCheck_2047_; 
v___x_2023_ = lean_st_ref_take(v___y_2018_);
v_toEnvExtension_2024_ = lean_ctor_get(v_a_2008_, 0);
v_env_2025_ = lean_ctor_get(v___x_2023_, 0);
v_nextMacroScope_2026_ = lean_ctor_get(v___x_2023_, 1);
v_ngen_2027_ = lean_ctor_get(v___x_2023_, 2);
v_auxDeclNGen_2028_ = lean_ctor_get(v___x_2023_, 3);
v_traceState_2029_ = lean_ctor_get(v___x_2023_, 4);
v_messages_2030_ = lean_ctor_get(v___x_2023_, 6);
v_infoState_2031_ = lean_ctor_get(v___x_2023_, 7);
v_snapshotTasks_2032_ = lean_ctor_get(v___x_2023_, 8);
v_isSharedCheck_2047_ = !lean_is_exclusive(v___x_2023_);
if (v_isSharedCheck_2047_ == 0)
{
lean_object* v_unused_2048_; 
v_unused_2048_ = lean_ctor_get(v___x_2023_, 5);
lean_dec(v_unused_2048_);
v___x_2034_ = v___x_2023_;
v_isShared_2035_ = v_isSharedCheck_2047_;
goto v_resetjp_2033_;
}
else
{
lean_inc(v_snapshotTasks_2032_);
lean_inc(v_infoState_2031_);
lean_inc(v_messages_2030_);
lean_inc(v_traceState_2029_);
lean_inc(v_auxDeclNGen_2028_);
lean_inc(v_ngen_2027_);
lean_inc(v_nextMacroScope_2026_);
lean_inc(v_env_2025_);
lean_dec(v___x_2023_);
v___x_2034_ = lean_box(0);
v_isShared_2035_ = v_isSharedCheck_2047_;
goto v_resetjp_2033_;
}
v_resetjp_2033_:
{
lean_object* v_asyncMode_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; lean_object* v___x_2040_; 
v_asyncMode_2036_ = lean_ctor_get(v_toEnvExtension_2024_, 2);
lean_inc(v_asyncMode_2036_);
lean_inc(v_decl_2010_);
v___x_2037_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_a_2008_, v_env_2025_, v_decl_2010_, v_asyncMode_2036_, v_decl_2010_);
lean_dec(v_asyncMode_2036_);
v___x_2038_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2);
if (v_isShared_2035_ == 0)
{
lean_ctor_set(v___x_2034_, 5, v___x_2038_);
lean_ctor_set(v___x_2034_, 0, v___x_2037_);
v___x_2040_ = v___x_2034_;
goto v_reusejp_2039_;
}
else
{
lean_object* v_reuseFailAlloc_2046_; 
v_reuseFailAlloc_2046_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2046_, 0, v___x_2037_);
lean_ctor_set(v_reuseFailAlloc_2046_, 1, v_nextMacroScope_2026_);
lean_ctor_set(v_reuseFailAlloc_2046_, 2, v_ngen_2027_);
lean_ctor_set(v_reuseFailAlloc_2046_, 3, v_auxDeclNGen_2028_);
lean_ctor_set(v_reuseFailAlloc_2046_, 4, v_traceState_2029_);
lean_ctor_set(v_reuseFailAlloc_2046_, 5, v___x_2038_);
lean_ctor_set(v_reuseFailAlloc_2046_, 6, v_messages_2030_);
lean_ctor_set(v_reuseFailAlloc_2046_, 7, v_infoState_2031_);
lean_ctor_set(v_reuseFailAlloc_2046_, 8, v_snapshotTasks_2032_);
v___x_2040_ = v_reuseFailAlloc_2046_;
goto v_reusejp_2039_;
}
v_reusejp_2039_:
{
lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2044_; 
v___x_2041_ = lean_st_ref_set(v___y_2018_, v___x_2040_);
v___x_2042_ = lean_box(0);
if (v_isShared_2022_ == 0)
{
lean_ctor_set(v___x_2021_, 0, v___x_2042_);
v___x_2044_ = v___x_2021_;
goto v_reusejp_2043_;
}
else
{
lean_object* v_reuseFailAlloc_2045_; 
v_reuseFailAlloc_2045_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2045_, 0, v___x_2042_);
v___x_2044_ = v_reuseFailAlloc_2045_;
goto v_reusejp_2043_;
}
v_reusejp_2043_:
{
return v___x_2044_;
}
}
}
}
}
else
{
lean_dec(v_decl_2010_);
lean_dec_ref(v_a_2008_);
return v___x_2019_;
}
}
v___jp_2051_:
{
lean_object* v_toEnvExtension_2055_; lean_object* v_asyncMode_2056_; uint8_t v___x_2057_; 
v_toEnvExtension_2055_ = lean_ctor_get(v_a_2008_, 0);
v_asyncMode_2056_ = lean_ctor_get(v_toEnvExtension_2055_, 2);
lean_inc(v_decl_2010_);
lean_inc_ref(v___y_2052_);
v___x_2057_ = l_Lean_EnvExtension_asyncMayModify___redArg(v___y_2052_, v_decl_2010_, v_asyncMode_2056_);
if (v___x_2057_ == 0)
{
lean_object* v___x_2058_; lean_object* v___x_2059_; 
lean_dec_ref(v_a_2008_);
lean_dec_ref(v_validate_2007_);
v___x_2058_ = l_Lean_Environment_asyncPrefix_x3f(v___y_2052_);
v___x_2059_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___redArg(v_name_2009_, v_decl_2010_, v___x_2058_, v___y_2053_, v___y_2054_);
return v___x_2059_;
}
else
{
lean_dec_ref(v___y_2052_);
lean_dec(v_name_2009_);
v___y_2017_ = v___y_2053_;
v___y_2018_ = v___y_2054_;
goto v___jp_2016_;
}
}
v___jp_2060_:
{
lean_object* v___x_2063_; lean_object* v_env_2064_; lean_object* v___x_2065_; 
v___x_2063_ = lean_st_ref_get(v___y_2062_);
v_env_2064_ = lean_ctor_get(v___x_2063_, 0);
lean_inc_ref(v_env_2064_);
lean_dec(v___x_2063_);
v___x_2065_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2064_, v_decl_2010_);
if (lean_obj_tag(v___x_2065_) == 0)
{
v___y_2052_ = v_env_2064_;
v___y_2053_ = v___y_2061_;
v___y_2054_ = v___y_2062_;
goto v___jp_2051_;
}
else
{
lean_object* v___x_2066_; 
lean_dec_ref(v___x_2065_);
lean_dec_ref(v_env_2064_);
lean_dec_ref(v_a_2008_);
lean_dec_ref(v_validate_2007_);
v___x_2066_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg(v_name_2009_, v_decl_2010_, v___y_2061_, v___y_2062_);
return v___x_2066_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__7___boxed(lean_object* v_validate_2071_, lean_object* v_a_2072_, lean_object* v_name_2073_, lean_object* v_decl_2074_, lean_object* v_stx_2075_, lean_object* v_kind_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_){
_start:
{
uint8_t v_kind_boxed_2080_; lean_object* v_res_2081_; 
v_kind_boxed_2080_ = lean_unbox(v_kind_2076_);
v_res_2081_ = l_Lean_registerTagAttribute___lam__7(v_validate_2071_, v_a_2072_, v_name_2073_, v_decl_2074_, v_stx_2075_, v_kind_boxed_2080_, v___y_2077_, v___y_2078_);
lean_dec(v___y_2078_);
lean_dec_ref(v___y_2077_);
return v_res_2081_;
}
}
static lean_object* _init_l_Lean_registerTagAttribute___closed__5(void){
_start:
{
lean_object* v___x_2087_; lean_object* v___f_2088_; 
v___x_2087_ = l_Lean_NameSet_empty;
v___f_2088_ = lean_alloc_closure((void*)(l_Lean_registerTagAttribute___lam__4___boxed), 4, 1);
lean_closure_set(v___f_2088_, 0, v___x_2087_);
return v___f_2088_;
}
}
static lean_object* _init_l_Lean_registerTagAttribute___closed__6(void){
_start:
{
lean_object* v___x_2089_; lean_object* v___f_2090_; 
v___x_2089_ = l_Lean_NameSet_empty;
v___f_2090_ = lean_alloc_closure((void*)(l_Lean_registerTagAttribute___lam__5___boxed), 2, 1);
lean_closure_set(v___f_2090_, 0, v___x_2089_);
return v___f_2090_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute(lean_object* v_name_2093_, lean_object* v_descr_2094_, lean_object* v_validate_2095_, lean_object* v_ref_2096_, uint8_t v_applicationTime_2097_, lean_object* v_asyncMode_2098_){
_start:
{
lean_object* v___f_2100_; lean_object* v___f_2101_; lean_object* v___f_2102_; lean_object* v___f_2103_; lean_object* v___f_2104_; lean_object* v___f_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; 
v___f_2100_ = ((lean_object*)(l_Lean_registerTagAttribute___closed__0));
v___f_2101_ = ((lean_object*)(l_Lean_registerTagAttribute___closed__2));
v___f_2102_ = ((lean_object*)(l_Lean_registerTagAttribute___closed__3));
v___f_2103_ = ((lean_object*)(l_Lean_registerTagAttribute___closed__4));
v___f_2104_ = lean_obj_once(&l_Lean_registerTagAttribute___closed__5, &l_Lean_registerTagAttribute___closed__5_once, _init_l_Lean_registerTagAttribute___closed__5);
v___f_2105_ = lean_obj_once(&l_Lean_registerTagAttribute___closed__6, &l_Lean_registerTagAttribute___closed__6_once, _init_l_Lean_registerTagAttribute___closed__6);
v___x_2106_ = ((lean_object*)(l_Lean_registerTagAttribute___closed__7));
lean_inc(v_ref_2096_);
v___x_2107_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_2107_, 0, v_ref_2096_);
lean_ctor_set(v___x_2107_, 1, v___f_2105_);
lean_ctor_set(v___x_2107_, 2, v___f_2104_);
lean_ctor_set(v___x_2107_, 3, v___f_2103_);
lean_ctor_set(v___x_2107_, 4, v___f_2102_);
lean_ctor_set(v___x_2107_, 5, v___f_2101_);
lean_ctor_set(v___x_2107_, 6, v_asyncMode_2098_);
lean_ctor_set(v___x_2107_, 7, v___x_2106_);
v___x_2108_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2108_, 0, v___x_2107_);
lean_ctor_set(v___x_2108_, 1, v___f_2100_);
v___x_2109_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_2108_);
if (lean_obj_tag(v___x_2109_) == 0)
{
lean_object* v_a_2110_; lean_object* v___f_2111_; lean_object* v___f_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; 
v_a_2110_ = lean_ctor_get(v___x_2109_, 0);
lean_inc_n(v_a_2110_, 2);
lean_dec_ref(v___x_2109_);
lean_inc_n(v_name_2093_, 2);
v___f_2111_ = lean_alloc_closure((void*)(l_Lean_registerTagAttribute___lam__6___boxed), 5, 1);
lean_closure_set(v___f_2111_, 0, v_name_2093_);
v___f_2112_ = lean_alloc_closure((void*)(l_Lean_registerTagAttribute___lam__7___boxed), 9, 3);
lean_closure_set(v___f_2112_, 0, v_validate_2095_);
lean_closure_set(v___f_2112_, 1, v_a_2110_);
lean_closure_set(v___f_2112_, 2, v_name_2093_);
v___x_2113_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2113_, 0, v_ref_2096_);
lean_ctor_set(v___x_2113_, 1, v_name_2093_);
lean_ctor_set(v___x_2113_, 2, v_descr_2094_);
lean_ctor_set_uint8(v___x_2113_, sizeof(void*)*3, v_applicationTime_2097_);
v___x_2114_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2114_, 0, v___x_2113_);
lean_ctor_set(v___x_2114_, 1, v___f_2112_);
lean_ctor_set(v___x_2114_, 2, v___f_2111_);
lean_inc_ref(v___x_2114_);
v___x_2115_ = l_Lean_registerBuiltinAttribute(v___x_2114_);
if (lean_obj_tag(v___x_2115_) == 0)
{
lean_object* v___x_2117_; uint8_t v_isShared_2118_; uint8_t v_isSharedCheck_2123_; 
v_isSharedCheck_2123_ = !lean_is_exclusive(v___x_2115_);
if (v_isSharedCheck_2123_ == 0)
{
lean_object* v_unused_2124_; 
v_unused_2124_ = lean_ctor_get(v___x_2115_, 0);
lean_dec(v_unused_2124_);
v___x_2117_ = v___x_2115_;
v_isShared_2118_ = v_isSharedCheck_2123_;
goto v_resetjp_2116_;
}
else
{
lean_dec(v___x_2115_);
v___x_2117_ = lean_box(0);
v_isShared_2118_ = v_isSharedCheck_2123_;
goto v_resetjp_2116_;
}
v_resetjp_2116_:
{
lean_object* v___x_2119_; lean_object* v___x_2121_; 
v___x_2119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2119_, 0, v___x_2114_);
lean_ctor_set(v___x_2119_, 1, v_a_2110_);
if (v_isShared_2118_ == 0)
{
lean_ctor_set(v___x_2117_, 0, v___x_2119_);
v___x_2121_ = v___x_2117_;
goto v_reusejp_2120_;
}
else
{
lean_object* v_reuseFailAlloc_2122_; 
v_reuseFailAlloc_2122_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2122_, 0, v___x_2119_);
v___x_2121_ = v_reuseFailAlloc_2122_;
goto v_reusejp_2120_;
}
v_reusejp_2120_:
{
return v___x_2121_;
}
}
}
else
{
lean_object* v_a_2125_; lean_object* v___x_2127_; uint8_t v_isShared_2128_; uint8_t v_isSharedCheck_2132_; 
lean_dec_ref(v___x_2114_);
lean_dec(v_a_2110_);
v_a_2125_ = lean_ctor_get(v___x_2115_, 0);
v_isSharedCheck_2132_ = !lean_is_exclusive(v___x_2115_);
if (v_isSharedCheck_2132_ == 0)
{
v___x_2127_ = v___x_2115_;
v_isShared_2128_ = v_isSharedCheck_2132_;
goto v_resetjp_2126_;
}
else
{
lean_inc(v_a_2125_);
lean_dec(v___x_2115_);
v___x_2127_ = lean_box(0);
v_isShared_2128_ = v_isSharedCheck_2132_;
goto v_resetjp_2126_;
}
v_resetjp_2126_:
{
lean_object* v___x_2130_; 
if (v_isShared_2128_ == 0)
{
v___x_2130_ = v___x_2127_;
goto v_reusejp_2129_;
}
else
{
lean_object* v_reuseFailAlloc_2131_; 
v_reuseFailAlloc_2131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2131_, 0, v_a_2125_);
v___x_2130_ = v_reuseFailAlloc_2131_;
goto v_reusejp_2129_;
}
v_reusejp_2129_:
{
return v___x_2130_;
}
}
}
}
else
{
lean_object* v_a_2133_; lean_object* v___x_2135_; uint8_t v_isShared_2136_; uint8_t v_isSharedCheck_2140_; 
lean_dec(v_ref_2096_);
lean_dec_ref(v_validate_2095_);
lean_dec_ref(v_descr_2094_);
lean_dec(v_name_2093_);
v_a_2133_ = lean_ctor_get(v___x_2109_, 0);
v_isSharedCheck_2140_ = !lean_is_exclusive(v___x_2109_);
if (v_isSharedCheck_2140_ == 0)
{
v___x_2135_ = v___x_2109_;
v_isShared_2136_ = v_isSharedCheck_2140_;
goto v_resetjp_2134_;
}
else
{
lean_inc(v_a_2133_);
lean_dec(v___x_2109_);
v___x_2135_ = lean_box(0);
v_isShared_2136_ = v_isSharedCheck_2140_;
goto v_resetjp_2134_;
}
v_resetjp_2134_:
{
lean_object* v___x_2138_; 
if (v_isShared_2136_ == 0)
{
v___x_2138_ = v___x_2135_;
goto v_reusejp_2137_;
}
else
{
lean_object* v_reuseFailAlloc_2139_; 
v_reuseFailAlloc_2139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2139_, 0, v_a_2133_);
v___x_2138_ = v_reuseFailAlloc_2139_;
goto v_reusejp_2137_;
}
v_reusejp_2137_:
{
return v___x_2138_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___boxed(lean_object* v_name_2141_, lean_object* v_descr_2142_, lean_object* v_validate_2143_, lean_object* v_ref_2144_, lean_object* v_applicationTime_2145_, lean_object* v_asyncMode_2146_, lean_object* v_a_2147_){
_start:
{
uint8_t v_applicationTime_boxed_2148_; lean_object* v_res_2149_; 
v_applicationTime_boxed_2148_ = lean_unbox(v_applicationTime_2145_);
v_res_2149_ = l_Lean_registerTagAttribute(v_name_2141_, v_descr_2142_, v_validate_2143_, v_ref_2144_, v_applicationTime_boxed_2148_, v_asyncMode_2146_);
return v_res_2149_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerTagAttribute_spec__1(lean_object* v_init_2150_, lean_object* v_t_2151_){
_start:
{
lean_object* v___x_2152_; 
v___x_2152_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerTagAttribute_spec__1_spec__1(v_init_2150_, v_t_2151_);
return v___x_2152_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3(lean_object* v_n_2153_, lean_object* v_as_2154_, lean_object* v_lo_2155_, lean_object* v_hi_2156_, lean_object* v_w_2157_, lean_object* v_hlo_2158_, lean_object* v_hhi_2159_){
_start:
{
lean_object* v___x_2160_; 
v___x_2160_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___redArg(v_n_2153_, v_as_2154_, v_lo_2155_, v_hi_2156_);
return v___x_2160_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___boxed(lean_object* v_n_2161_, lean_object* v_as_2162_, lean_object* v_lo_2163_, lean_object* v_hi_2164_, lean_object* v_w_2165_, lean_object* v_hlo_2166_, lean_object* v_hhi_2167_){
_start:
{
lean_object* v_res_2168_; 
v_res_2168_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3(v_n_2161_, v_as_2162_, v_lo_2163_, v_hi_2164_, v_w_2165_, v_hlo_2166_, v_hhi_2167_);
lean_dec(v_hi_2164_);
lean_dec(v_n_2161_);
return v_res_2168_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4(lean_object* v_00_u03b1_2169_, lean_object* v_attrName_2170_, lean_object* v_declName_2171_, lean_object* v_asyncPrefix_x3f_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_){
_start:
{
lean_object* v___x_2176_; 
v___x_2176_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___redArg(v_attrName_2170_, v_declName_2171_, v_asyncPrefix_x3f_2172_, v___y_2173_, v___y_2174_);
return v___x_2176_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___boxed(lean_object* v_00_u03b1_2177_, lean_object* v_attrName_2178_, lean_object* v_declName_2179_, lean_object* v_asyncPrefix_x3f_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_){
_start:
{
lean_object* v_res_2184_; 
v_res_2184_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4(v_00_u03b1_2177_, v_attrName_2178_, v_declName_2179_, v_asyncPrefix_x3f_2180_, v___y_2181_, v___y_2182_);
lean_dec(v___y_2182_);
lean_dec_ref(v___y_2181_);
return v_res_2184_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5(lean_object* v_00_u03b1_2185_, lean_object* v_attrName_2186_, lean_object* v_declName_2187_, lean_object* v___y_2188_, lean_object* v___y_2189_){
_start:
{
lean_object* v___x_2191_; 
v___x_2191_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg(v_attrName_2186_, v_declName_2187_, v___y_2188_, v___y_2189_);
return v___x_2191_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___boxed(lean_object* v_00_u03b1_2192_, lean_object* v_attrName_2193_, lean_object* v_declName_2194_, lean_object* v___y_2195_, lean_object* v___y_2196_, lean_object* v___y_2197_){
_start:
{
lean_object* v_res_2198_; 
v_res_2198_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5(v_00_u03b1_2192_, v_attrName_2193_, v_declName_2194_, v___y_2195_, v___y_2196_);
lean_dec(v___y_2196_);
lean_dec_ref(v___y_2195_);
return v_res_2198_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6(lean_object* v_00_u03b1_2199_, lean_object* v_name_2200_, uint8_t v_kind_2201_, lean_object* v___y_2202_, lean_object* v___y_2203_){
_start:
{
lean_object* v___x_2205_; 
v___x_2205_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg(v_name_2200_, v_kind_2201_, v___y_2202_, v___y_2203_);
return v___x_2205_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___boxed(lean_object* v_00_u03b1_2206_, lean_object* v_name_2207_, lean_object* v_kind_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_, lean_object* v___y_2211_){
_start:
{
uint8_t v_kind_boxed_2212_; lean_object* v_res_2213_; 
v_kind_boxed_2212_ = lean_unbox(v_kind_2208_);
v_res_2213_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6(v_00_u03b1_2206_, v_name_2207_, v_kind_boxed_2212_, v___y_2209_, v___y_2210_);
lean_dec(v___y_2210_);
lean_dec_ref(v___y_2209_);
return v_res_2213_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4(lean_object* v_n_2214_, lean_object* v_lo_2215_, lean_object* v_hi_2216_, lean_object* v_hhi_2217_, lean_object* v_pivot_2218_, lean_object* v_as_2219_, lean_object* v_i_2220_, lean_object* v_k_2221_, lean_object* v_ilo_2222_, lean_object* v_ik_2223_, lean_object* v_w_2224_){
_start:
{
lean_object* v___x_2225_; 
v___x_2225_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4___redArg(v_hi_2216_, v_pivot_2218_, v_as_2219_, v_i_2220_, v_k_2221_);
return v___x_2225_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4___boxed(lean_object* v_n_2226_, lean_object* v_lo_2227_, lean_object* v_hi_2228_, lean_object* v_hhi_2229_, lean_object* v_pivot_2230_, lean_object* v_as_2231_, lean_object* v_i_2232_, lean_object* v_k_2233_, lean_object* v_ilo_2234_, lean_object* v_ik_2235_, lean_object* v_w_2236_){
_start:
{
lean_object* v_res_2237_; 
v_res_2237_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4(v_n_2226_, v_lo_2227_, v_hi_2228_, v_hhi_2229_, v_pivot_2230_, v_as_2231_, v_i_2232_, v_k_2233_, v_ilo_2234_, v_ik_2235_, v_w_2236_);
lean_dec(v_pivot_2230_);
lean_dec(v_hi_2228_);
lean_dec(v_lo_2227_);
lean_dec(v_n_2226_);
return v_res_2237_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg___lam__0(lean_object* v_attr_2238_, lean_object* v_decl_2239_, lean_object* v_env_2240_){
_start:
{
lean_object* v_ext_2241_; lean_object* v_toEnvExtension_2242_; lean_object* v_asyncMode_2243_; lean_object* v___x_2244_; 
v_ext_2241_ = lean_ctor_get(v_attr_2238_, 1);
lean_inc_ref(v_ext_2241_);
lean_dec_ref(v_attr_2238_);
v_toEnvExtension_2242_ = lean_ctor_get(v_ext_2241_, 0);
v_asyncMode_2243_ = lean_ctor_get(v_toEnvExtension_2242_, 2);
lean_inc(v_asyncMode_2243_);
lean_inc(v_decl_2239_);
v___x_2244_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_ext_2241_, v_env_2240_, v_decl_2239_, v_asyncMode_2243_, v_decl_2239_);
lean_dec(v_asyncMode_2243_);
return v___x_2244_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg___lam__1(lean_object* v_modifyEnv_2245_, lean_object* v___f_2246_, lean_object* v_____r_2247_){
_start:
{
lean_object* v___x_2248_; 
v___x_2248_ = lean_apply_1(v_modifyEnv_2245_, v___f_2246_);
return v___x_2248_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg___lam__2(lean_object* v_attr_2249_, lean_object* v_env_2250_, lean_object* v_decl_2251_, lean_object* v_inst_2252_, lean_object* v_inst_2253_, lean_object* v_toBind_2254_, lean_object* v___f_2255_, lean_object* v_modifyEnv_2256_, lean_object* v___f_2257_, lean_object* v_____r_2258_){
_start:
{
lean_object* v_ext_2259_; lean_object* v_toEnvExtension_2260_; lean_object* v_attr_2261_; lean_object* v_asyncMode_2262_; uint8_t v___x_2263_; 
v_ext_2259_ = lean_ctor_get(v_attr_2249_, 1);
v_toEnvExtension_2260_ = lean_ctor_get(v_ext_2259_, 0);
lean_inc_ref(v_toEnvExtension_2260_);
v_attr_2261_ = lean_ctor_get(v_attr_2249_, 0);
lean_inc_ref(v_attr_2261_);
lean_dec_ref(v_attr_2249_);
v_asyncMode_2262_ = lean_ctor_get(v_toEnvExtension_2260_, 2);
lean_inc(v_asyncMode_2262_);
lean_dec_ref(v_toEnvExtension_2260_);
lean_inc(v_decl_2251_);
lean_inc_ref(v_env_2250_);
v___x_2263_ = l_Lean_EnvExtension_asyncMayModify___redArg(v_env_2250_, v_decl_2251_, v_asyncMode_2262_);
lean_dec(v_asyncMode_2262_);
if (v___x_2263_ == 0)
{
lean_object* v_toAttributeImplCore_2264_; lean_object* v_name_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; 
lean_dec_ref(v___f_2257_);
lean_dec(v_modifyEnv_2256_);
v_toAttributeImplCore_2264_ = lean_ctor_get(v_attr_2261_, 0);
lean_inc_ref(v_toAttributeImplCore_2264_);
lean_dec_ref(v_attr_2261_);
v_name_2265_ = lean_ctor_get(v_toAttributeImplCore_2264_, 1);
lean_inc(v_name_2265_);
lean_dec_ref(v_toAttributeImplCore_2264_);
v___x_2266_ = l_Lean_Environment_asyncPrefix_x3f(v_env_2250_);
v___x_2267_ = l_Lean_throwAttrNotInAsyncCtx___redArg(v_inst_2252_, v_inst_2253_, v_name_2265_, v_decl_2251_, v___x_2266_);
v___x_2268_ = lean_apply_4(v_toBind_2254_, lean_box(0), lean_box(0), v___x_2267_, v___f_2255_);
return v___x_2268_;
}
else
{
lean_object* v___x_2269_; 
lean_dec_ref(v_attr_2261_);
lean_dec(v___f_2255_);
lean_dec(v_toBind_2254_);
lean_dec_ref(v_inst_2253_);
lean_dec_ref(v_inst_2252_);
lean_dec(v_decl_2251_);
lean_dec_ref(v_env_2250_);
v___x_2269_ = lean_apply_1(v_modifyEnv_2256_, v___f_2257_);
return v___x_2269_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg___lam__3(lean_object* v___f_2270_, lean_object* v_____r_2271_){
_start:
{
lean_object* v___x_2272_; 
v___x_2272_ = lean_apply_1(v___f_2270_, v_____r_2271_);
return v___x_2272_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg___lam__4(lean_object* v_attr_2273_, lean_object* v_decl_2274_, lean_object* v_inst_2275_, lean_object* v_inst_2276_, lean_object* v_toBind_2277_, lean_object* v___f_2278_, lean_object* v_modifyEnv_2279_, lean_object* v___f_2280_, lean_object* v_env_2281_){
_start:
{
lean_object* v___f_2282_; lean_object* v___x_2283_; 
lean_inc_ref(v___f_2280_);
lean_inc(v_modifyEnv_2279_);
lean_inc(v___f_2278_);
lean_inc(v_toBind_2277_);
lean_inc_ref(v_inst_2276_);
lean_inc_ref(v_inst_2275_);
lean_inc(v_decl_2274_);
lean_inc_ref(v_env_2281_);
lean_inc_ref(v_attr_2273_);
v___f_2282_ = lean_alloc_closure((void*)(l_Lean_TagAttribute_setTag___redArg___lam__2), 10, 9);
lean_closure_set(v___f_2282_, 0, v_attr_2273_);
lean_closure_set(v___f_2282_, 1, v_env_2281_);
lean_closure_set(v___f_2282_, 2, v_decl_2274_);
lean_closure_set(v___f_2282_, 3, v_inst_2275_);
lean_closure_set(v___f_2282_, 4, v_inst_2276_);
lean_closure_set(v___f_2282_, 5, v_toBind_2277_);
lean_closure_set(v___f_2282_, 6, v___f_2278_);
lean_closure_set(v___f_2282_, 7, v_modifyEnv_2279_);
lean_closure_set(v___f_2282_, 8, v___f_2280_);
v___x_2283_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2281_, v_decl_2274_);
if (lean_obj_tag(v___x_2283_) == 0)
{
lean_object* v___x_2284_; lean_object* v___x_2285_; 
lean_dec_ref(v___f_2282_);
v___x_2284_ = lean_box(0);
v___x_2285_ = l_Lean_TagAttribute_setTag___redArg___lam__2(v_attr_2273_, v_env_2281_, v_decl_2274_, v_inst_2275_, v_inst_2276_, v_toBind_2277_, v___f_2278_, v_modifyEnv_2279_, v___f_2280_, v___x_2284_);
return v___x_2285_;
}
else
{
lean_object* v_attr_2286_; lean_object* v_toAttributeImplCore_2287_; lean_object* v_name_2288_; lean_object* v___f_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; 
lean_dec_ref(v___x_2283_);
lean_dec_ref(v_env_2281_);
lean_dec_ref(v___f_2280_);
lean_dec(v_modifyEnv_2279_);
lean_dec(v___f_2278_);
v_attr_2286_ = lean_ctor_get(v_attr_2273_, 0);
lean_inc_ref(v_attr_2286_);
lean_dec_ref(v_attr_2273_);
v_toAttributeImplCore_2287_ = lean_ctor_get(v_attr_2286_, 0);
lean_inc_ref(v_toAttributeImplCore_2287_);
lean_dec_ref(v_attr_2286_);
v_name_2288_ = lean_ctor_get(v_toAttributeImplCore_2287_, 1);
lean_inc(v_name_2288_);
lean_dec_ref(v_toAttributeImplCore_2287_);
v___f_2289_ = lean_alloc_closure((void*)(l_Lean_TagAttribute_setTag___redArg___lam__3), 2, 1);
lean_closure_set(v___f_2289_, 0, v___f_2282_);
v___x_2290_ = l_Lean_throwAttrDeclInImportedModule___redArg(v_inst_2275_, v_inst_2276_, v_name_2288_, v_decl_2274_);
v___x_2291_ = lean_apply_4(v_toBind_2277_, lean_box(0), lean_box(0), v___x_2290_, v___f_2289_);
return v___x_2291_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg(lean_object* v_inst_2292_, lean_object* v_inst_2293_, lean_object* v_inst_2294_, lean_object* v_attr_2295_, lean_object* v_decl_2296_){
_start:
{
lean_object* v_toBind_2297_; lean_object* v_getEnv_2298_; lean_object* v_modifyEnv_2299_; lean_object* v___f_2300_; lean_object* v___f_2301_; lean_object* v___f_2302_; lean_object* v___x_2303_; 
v_toBind_2297_ = lean_ctor_get(v_inst_2292_, 1);
lean_inc_n(v_toBind_2297_, 2);
v_getEnv_2298_ = lean_ctor_get(v_inst_2294_, 0);
lean_inc(v_getEnv_2298_);
v_modifyEnv_2299_ = lean_ctor_get(v_inst_2294_, 1);
lean_inc_n(v_modifyEnv_2299_, 2);
lean_dec_ref(v_inst_2294_);
lean_inc(v_decl_2296_);
lean_inc_ref(v_attr_2295_);
v___f_2300_ = lean_alloc_closure((void*)(l_Lean_TagAttribute_setTag___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2300_, 0, v_attr_2295_);
lean_closure_set(v___f_2300_, 1, v_decl_2296_);
lean_inc_ref(v___f_2300_);
v___f_2301_ = lean_alloc_closure((void*)(l_Lean_TagAttribute_setTag___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2301_, 0, v_modifyEnv_2299_);
lean_closure_set(v___f_2301_, 1, v___f_2300_);
v___f_2302_ = lean_alloc_closure((void*)(l_Lean_TagAttribute_setTag___redArg___lam__4), 9, 8);
lean_closure_set(v___f_2302_, 0, v_attr_2295_);
lean_closure_set(v___f_2302_, 1, v_decl_2296_);
lean_closure_set(v___f_2302_, 2, v_inst_2292_);
lean_closure_set(v___f_2302_, 3, v_inst_2293_);
lean_closure_set(v___f_2302_, 4, v_toBind_2297_);
lean_closure_set(v___f_2302_, 5, v___f_2301_);
lean_closure_set(v___f_2302_, 6, v_modifyEnv_2299_);
lean_closure_set(v___f_2302_, 7, v___f_2300_);
v___x_2303_ = lean_apply_4(v_toBind_2297_, lean_box(0), lean_box(0), v_getEnv_2298_, v___f_2302_);
return v___x_2303_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag(lean_object* v_m_2304_, lean_object* v_inst_2305_, lean_object* v_inst_2306_, lean_object* v_inst_2307_, lean_object* v_attr_2308_, lean_object* v_decl_2309_){
_start:
{
lean_object* v___x_2310_; 
v___x_2310_ = l_Lean_TagAttribute_setTag___redArg(v_inst_2305_, v_inst_2306_, v_inst_2307_, v_attr_2308_, v_decl_2309_);
return v___x_2310_;
}
}
LEAN_EXPORT uint8_t l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___redArg(lean_object* v_as_2311_, lean_object* v_k_2312_, lean_object* v_x_2313_, lean_object* v_x_2314_){
_start:
{
lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v_m_2317_; lean_object* v_a_2318_; uint8_t v___x_2319_; 
v___x_2315_ = lean_nat_add(v_x_2313_, v_x_2314_);
v___x_2316_ = lean_unsigned_to_nat(1u);
v_m_2317_ = lean_nat_shiftr(v___x_2315_, v___x_2316_);
lean_dec(v___x_2315_);
v_a_2318_ = lean_array_fget_borrowed(v_as_2311_, v_m_2317_);
v___x_2319_ = l_Lean_Name_quickLt(v_a_2318_, v_k_2312_);
if (v___x_2319_ == 0)
{
uint8_t v___x_2320_; 
lean_dec(v_x_2314_);
v___x_2320_ = l_Lean_Name_quickLt(v_k_2312_, v_a_2318_);
if (v___x_2320_ == 0)
{
uint8_t v___x_2321_; 
lean_dec(v_m_2317_);
lean_dec(v_x_2313_);
v___x_2321_ = 1;
return v___x_2321_;
}
else
{
lean_object* v___x_2322_; uint8_t v___x_2323_; 
v___x_2322_ = lean_unsigned_to_nat(0u);
v___x_2323_ = lean_nat_dec_eq(v_m_2317_, v___x_2322_);
if (v___x_2323_ == 0)
{
lean_object* v___x_2324_; uint8_t v___x_2325_; 
v___x_2324_ = lean_nat_sub(v_m_2317_, v___x_2316_);
lean_dec(v_m_2317_);
v___x_2325_ = lean_nat_dec_lt(v___x_2324_, v_x_2313_);
if (v___x_2325_ == 0)
{
v_x_2314_ = v___x_2324_;
goto _start;
}
else
{
lean_dec(v___x_2324_);
lean_dec(v_x_2313_);
return v___x_2319_;
}
}
else
{
lean_dec(v_m_2317_);
lean_dec(v_x_2313_);
return v___x_2319_;
}
}
}
else
{
lean_object* v___x_2327_; uint8_t v___x_2328_; 
lean_dec(v_x_2313_);
v___x_2327_ = lean_nat_add(v_m_2317_, v___x_2316_);
lean_dec(v_m_2317_);
v___x_2328_ = lean_nat_dec_le(v___x_2327_, v_x_2314_);
if (v___x_2328_ == 0)
{
lean_dec(v___x_2327_);
lean_dec(v_x_2314_);
return v___x_2328_;
}
else
{
v_x_2313_ = v___x_2327_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___redArg___boxed(lean_object* v_as_2330_, lean_object* v_k_2331_, lean_object* v_x_2332_, lean_object* v_x_2333_){
_start:
{
uint8_t v_res_2334_; lean_object* v_r_2335_; 
v_res_2334_ = l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___redArg(v_as_2330_, v_k_2331_, v_x_2332_, v_x_2333_);
lean_dec(v_k_2331_);
lean_dec_ref(v_as_2330_);
v_r_2335_ = lean_box(v_res_2334_);
return v_r_2335_;
}
}
LEAN_EXPORT uint8_t l_Lean_TagAttribute_hasTag(lean_object* v_attr_2336_, lean_object* v_env_2337_, lean_object* v_decl_2338_){
_start:
{
lean_object* v___x_2339_; lean_object* v___x_2340_; 
v___x_2339_ = lean_box(1);
v___x_2340_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2337_, v_decl_2338_);
if (lean_obj_tag(v___x_2340_) == 0)
{
lean_object* v_ext_2341_; lean_object* v_toEnvExtension_2342_; lean_object* v_asyncMode_2343_; lean_object* v___x_2344_; uint8_t v___x_2345_; 
v_ext_2341_ = lean_ctor_get(v_attr_2336_, 1);
v_toEnvExtension_2342_ = lean_ctor_get(v_ext_2341_, 0);
v_asyncMode_2343_ = lean_ctor_get(v_toEnvExtension_2342_, 2);
lean_inc(v_decl_2338_);
v___x_2344_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2339_, v_ext_2341_, v_env_2337_, v_asyncMode_2343_, v_decl_2338_);
v___x_2345_ = l_Lean_NameSet_contains(v___x_2344_, v_decl_2338_);
lean_dec(v_decl_2338_);
lean_dec(v___x_2344_);
return v___x_2345_;
}
else
{
lean_object* v_val_2346_; lean_object* v_ext_2347_; uint8_t v___x_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; lean_object* v___x_2351_; uint8_t v___x_2352_; 
v_val_2346_ = lean_ctor_get(v___x_2340_, 0);
lean_inc(v_val_2346_);
lean_dec_ref(v___x_2340_);
v_ext_2347_ = lean_ctor_get(v_attr_2336_, 1);
v___x_2348_ = 0;
v___x_2349_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_2339_, v_ext_2347_, v_env_2337_, v_val_2346_, v___x_2348_);
lean_dec(v_val_2346_);
lean_dec_ref(v_env_2337_);
v___x_2350_ = lean_unsigned_to_nat(0u);
v___x_2351_ = lean_array_get_size(v___x_2349_);
v___x_2352_ = lean_nat_dec_lt(v___x_2350_, v___x_2351_);
if (v___x_2352_ == 0)
{
lean_dec_ref(v___x_2349_);
lean_dec(v_decl_2338_);
return v___x_2352_;
}
else
{
lean_object* v___x_2353_; lean_object* v___x_2354_; uint8_t v___x_2355_; 
v___x_2353_ = lean_unsigned_to_nat(1u);
v___x_2354_ = lean_nat_sub(v___x_2351_, v___x_2353_);
v___x_2355_ = lean_nat_dec_le(v___x_2350_, v___x_2354_);
if (v___x_2355_ == 0)
{
lean_dec(v___x_2354_);
lean_dec_ref(v___x_2349_);
lean_dec(v_decl_2338_);
return v___x_2355_;
}
else
{
uint8_t v___x_2356_; 
v___x_2356_ = l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___redArg(v___x_2349_, v_decl_2338_, v___x_2350_, v___x_2354_);
lean_dec(v_decl_2338_);
lean_dec_ref(v___x_2349_);
return v___x_2356_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_hasTag___boxed(lean_object* v_attr_2357_, lean_object* v_env_2358_, lean_object* v_decl_2359_){
_start:
{
uint8_t v_res_2360_; lean_object* v_r_2361_; 
v_res_2360_ = l_Lean_TagAttribute_hasTag(v_attr_2357_, v_env_2358_, v_decl_2359_);
lean_dec_ref(v_attr_2357_);
v_r_2361_ = lean_box(v_res_2360_);
return v_r_2361_;
}
}
LEAN_EXPORT uint8_t l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0(lean_object* v_as_2362_, lean_object* v_k_2363_, lean_object* v_x_2364_, lean_object* v_x_2365_, lean_object* v_x_2366_){
_start:
{
uint8_t v___x_2367_; 
v___x_2367_ = l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___redArg(v_as_2362_, v_k_2363_, v_x_2364_, v_x_2365_);
return v___x_2367_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___boxed(lean_object* v_as_2368_, lean_object* v_k_2369_, lean_object* v_x_2370_, lean_object* v_x_2371_, lean_object* v_x_2372_){
_start:
{
uint8_t v_res_2373_; lean_object* v_r_2374_; 
v_res_2373_ = l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0(v_as_2368_, v_k_2369_, v_x_2370_, v_x_2371_, v_x_2372_);
lean_dec(v_k_2369_);
lean_dec_ref(v_as_2368_);
v_r_2374_ = lean_box(v_res_2373_);
return v_r_2374_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__0(lean_object* v_x_2375_, lean_object* v___y_2376_){
_start:
{
lean_object* v___x_2378_; lean_object* v___x_2379_; 
v___x_2378_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___lam__0___closed__1));
v___x_2379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2379_, 0, v___x_2378_);
return v___x_2379_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__0___boxed(lean_object* v_x_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_){
_start:
{
lean_object* v_res_2383_; 
v_res_2383_ = l_Lean_instInhabitedParametricAttribute_default___lam__0(v_x_2380_, v___y_2381_);
lean_dec_ref(v___y_2381_);
lean_dec_ref(v_x_2380_);
return v_res_2383_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__1(lean_object* v_s_2384_, lean_object* v_x_2385_){
_start:
{
lean_inc_ref(v_s_2384_);
return v_s_2384_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__1___boxed(lean_object* v_s_2386_, lean_object* v_x_2387_){
_start:
{
lean_object* v_res_2388_; 
v_res_2388_ = l_Lean_instInhabitedParametricAttribute_default___lam__1(v_s_2386_, v_x_2387_);
lean_dec_ref(v_x_2387_);
lean_dec_ref(v_s_2386_);
return v_res_2388_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__2(lean_object* v_x_2393_, lean_object* v_x_2394_){
_start:
{
lean_object* v___x_2395_; 
v___x_2395_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___lam__2___closed__1));
return v___x_2395_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__2___boxed(lean_object* v_x_2396_, lean_object* v_x_2397_){
_start:
{
lean_object* v_res_2398_; 
v_res_2398_ = l_Lean_instInhabitedParametricAttribute_default___lam__2(v_x_2396_, v_x_2397_);
lean_dec_ref(v_x_2397_);
lean_dec_ref(v_x_2396_);
return v_res_2398_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__3(lean_object* v_x_2399_){
_start:
{
lean_object* v___x_2400_; 
v___x_2400_ = lean_box(0);
return v___x_2400_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__3___boxed(lean_object* v_x_2401_){
_start:
{
lean_object* v_res_2402_; 
v_res_2402_ = l_Lean_instInhabitedParametricAttribute_default___lam__3(v_x_2401_);
lean_dec_ref(v_x_2401_);
return v_res_2402_;
}
}
static lean_object* _init_l_Lean_instInhabitedParametricAttribute_default___closed__4(void){
_start:
{
lean_object* v___x_2407_; 
v___x_2407_ = l_Lean_instInhabitedEnvExtension_default(lean_box(0));
return v___x_2407_;
}
}
static lean_object* _init_l_Lean_instInhabitedParametricAttribute_default___closed__5(void){
_start:
{
lean_object* v___f_2408_; lean_object* v___f_2409_; lean_object* v___f_2410_; lean_object* v___f_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; 
v___f_2408_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___closed__3));
v___f_2409_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___closed__2));
v___f_2410_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___closed__1));
v___f_2411_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___closed__0));
v___x_2412_ = lean_box(0);
v___x_2413_ = lean_obj_once(&l_Lean_instInhabitedParametricAttribute_default___closed__4, &l_Lean_instInhabitedParametricAttribute_default___closed__4_once, _init_l_Lean_instInhabitedParametricAttribute_default___closed__4);
v___x_2414_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2414_, 0, v___x_2413_);
lean_ctor_set(v___x_2414_, 1, v___x_2412_);
lean_ctor_set(v___x_2414_, 2, v___f_2411_);
lean_ctor_set(v___x_2414_, 3, v___f_2410_);
lean_ctor_set(v___x_2414_, 4, v___f_2409_);
lean_ctor_set(v___x_2414_, 5, v___f_2408_);
return v___x_2414_;
}
}
static lean_object* _init_l_Lean_instInhabitedParametricAttribute_default___closed__6(void){
_start:
{
uint8_t v___x_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; 
v___x_2415_ = 0;
v___x_2416_ = lean_obj_once(&l_Lean_instInhabitedParametricAttribute_default___closed__5, &l_Lean_instInhabitedParametricAttribute_default___closed__5_once, _init_l_Lean_instInhabitedParametricAttribute_default___closed__5);
v___x_2417_ = ((lean_object*)(l_Lean_instInhabitedAttributeImpl_default));
v___x_2418_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2418_, 0, v___x_2417_);
lean_ctor_set(v___x_2418_, 1, v___x_2416_);
lean_ctor_set_uint8(v___x_2418_, sizeof(void*)*2, v___x_2415_);
return v___x_2418_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default(lean_object* v_00_u03b1_2419_){
_start:
{
lean_object* v___x_2420_; 
v___x_2420_ = lean_obj_once(&l_Lean_instInhabitedParametricAttribute_default___closed__6, &l_Lean_instInhabitedParametricAttribute_default___closed__6_once, _init_l_Lean_instInhabitedParametricAttribute_default___closed__6);
return v___x_2420_;
}
}
static lean_object* _init_l_Lean_instInhabitedParametricAttribute___closed__0(void){
_start:
{
lean_object* v___x_2421_; 
v___x_2421_ = l_Lean_instInhabitedParametricAttribute_default(lean_box(0));
return v___x_2421_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute(lean_object* v_a_2422_){
_start:
{
lean_object* v___x_2423_; 
v___x_2423_ = lean_obj_once(&l_Lean_instInhabitedParametricAttribute___closed__0, &l_Lean_instInhabitedParametricAttribute___closed__0_once, _init_l_Lean_instInhabitedParametricAttribute___closed__0);
return v___x_2423_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_registerParametricAttribute_spec__4___redArg(lean_object* v_env_2424_, lean_object* v___y_2425_){
_start:
{
lean_object* v___x_2427_; lean_object* v_nextMacroScope_2428_; lean_object* v_ngen_2429_; lean_object* v_auxDeclNGen_2430_; lean_object* v_traceState_2431_; lean_object* v_messages_2432_; lean_object* v_infoState_2433_; lean_object* v_snapshotTasks_2434_; lean_object* v___x_2436_; uint8_t v_isShared_2437_; uint8_t v_isSharedCheck_2445_; 
v___x_2427_ = lean_st_ref_take(v___y_2425_);
v_nextMacroScope_2428_ = lean_ctor_get(v___x_2427_, 1);
v_ngen_2429_ = lean_ctor_get(v___x_2427_, 2);
v_auxDeclNGen_2430_ = lean_ctor_get(v___x_2427_, 3);
v_traceState_2431_ = lean_ctor_get(v___x_2427_, 4);
v_messages_2432_ = lean_ctor_get(v___x_2427_, 6);
v_infoState_2433_ = lean_ctor_get(v___x_2427_, 7);
v_snapshotTasks_2434_ = lean_ctor_get(v___x_2427_, 8);
v_isSharedCheck_2445_ = !lean_is_exclusive(v___x_2427_);
if (v_isSharedCheck_2445_ == 0)
{
lean_object* v_unused_2446_; lean_object* v_unused_2447_; 
v_unused_2446_ = lean_ctor_get(v___x_2427_, 5);
lean_dec(v_unused_2446_);
v_unused_2447_ = lean_ctor_get(v___x_2427_, 0);
lean_dec(v_unused_2447_);
v___x_2436_ = v___x_2427_;
v_isShared_2437_ = v_isSharedCheck_2445_;
goto v_resetjp_2435_;
}
else
{
lean_inc(v_snapshotTasks_2434_);
lean_inc(v_infoState_2433_);
lean_inc(v_messages_2432_);
lean_inc(v_traceState_2431_);
lean_inc(v_auxDeclNGen_2430_);
lean_inc(v_ngen_2429_);
lean_inc(v_nextMacroScope_2428_);
lean_dec(v___x_2427_);
v___x_2436_ = lean_box(0);
v_isShared_2437_ = v_isSharedCheck_2445_;
goto v_resetjp_2435_;
}
v_resetjp_2435_:
{
lean_object* v___x_2438_; lean_object* v___x_2440_; 
v___x_2438_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2);
if (v_isShared_2437_ == 0)
{
lean_ctor_set(v___x_2436_, 5, v___x_2438_);
lean_ctor_set(v___x_2436_, 0, v_env_2424_);
v___x_2440_ = v___x_2436_;
goto v_reusejp_2439_;
}
else
{
lean_object* v_reuseFailAlloc_2444_; 
v_reuseFailAlloc_2444_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2444_, 0, v_env_2424_);
lean_ctor_set(v_reuseFailAlloc_2444_, 1, v_nextMacroScope_2428_);
lean_ctor_set(v_reuseFailAlloc_2444_, 2, v_ngen_2429_);
lean_ctor_set(v_reuseFailAlloc_2444_, 3, v_auxDeclNGen_2430_);
lean_ctor_set(v_reuseFailAlloc_2444_, 4, v_traceState_2431_);
lean_ctor_set(v_reuseFailAlloc_2444_, 5, v___x_2438_);
lean_ctor_set(v_reuseFailAlloc_2444_, 6, v_messages_2432_);
lean_ctor_set(v_reuseFailAlloc_2444_, 7, v_infoState_2433_);
lean_ctor_set(v_reuseFailAlloc_2444_, 8, v_snapshotTasks_2434_);
v___x_2440_ = v_reuseFailAlloc_2444_;
goto v_reusejp_2439_;
}
v_reusejp_2439_:
{
lean_object* v___x_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; 
v___x_2441_ = lean_st_ref_set(v___y_2425_, v___x_2440_);
v___x_2442_ = lean_box(0);
v___x_2443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2443_, 0, v___x_2442_);
return v___x_2443_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_registerParametricAttribute_spec__4___redArg___boxed(lean_object* v_env_2448_, lean_object* v___y_2449_, lean_object* v___y_2450_){
_start:
{
lean_object* v_res_2451_; 
v_res_2451_ = l_Lean_setEnv___at___00Lean_registerParametricAttribute_spec__4___redArg(v_env_2448_, v___y_2449_);
lean_dec(v___y_2449_);
return v_res_2451_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_registerParametricAttribute_spec__4(lean_object* v_env_2452_, lean_object* v___y_2453_, lean_object* v___y_2454_){
_start:
{
lean_object* v___x_2456_; 
v___x_2456_ = l_Lean_setEnv___at___00Lean_registerParametricAttribute_spec__4___redArg(v_env_2452_, v___y_2454_);
return v___x_2456_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_registerParametricAttribute_spec__4___boxed(lean_object* v_env_2457_, lean_object* v___y_2458_, lean_object* v___y_2459_, lean_object* v___y_2460_){
_start:
{
lean_object* v_res_2461_; 
v_res_2461_ = l_Lean_setEnv___at___00Lean_registerParametricAttribute_spec__4(v_env_2457_, v___y_2458_, v___y_2459_);
lean_dec(v___y_2459_);
lean_dec_ref(v___y_2458_);
return v_res_2461_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___lam__0(lean_object* v_x_2462_, lean_object* v_p_2463_){
_start:
{
lean_object* v_fst_2464_; lean_object* v_snd_2465_; lean_object* v___x_2467_; uint8_t v_isShared_2468_; uint8_t v_isSharedCheck_2482_; 
v_fst_2464_ = lean_ctor_get(v_x_2462_, 0);
v_snd_2465_ = lean_ctor_get(v_x_2462_, 1);
v_isSharedCheck_2482_ = !lean_is_exclusive(v_x_2462_);
if (v_isSharedCheck_2482_ == 0)
{
v___x_2467_ = v_x_2462_;
v_isShared_2468_ = v_isSharedCheck_2482_;
goto v_resetjp_2466_;
}
else
{
lean_inc(v_snd_2465_);
lean_inc(v_fst_2464_);
lean_dec(v_x_2462_);
v___x_2467_ = lean_box(0);
v_isShared_2468_ = v_isSharedCheck_2482_;
goto v_resetjp_2466_;
}
v_resetjp_2466_:
{
lean_object* v_fst_2469_; lean_object* v_snd_2470_; lean_object* v___x_2472_; uint8_t v_isShared_2473_; uint8_t v_isSharedCheck_2481_; 
v_fst_2469_ = lean_ctor_get(v_p_2463_, 0);
v_snd_2470_ = lean_ctor_get(v_p_2463_, 1);
v_isSharedCheck_2481_ = !lean_is_exclusive(v_p_2463_);
if (v_isSharedCheck_2481_ == 0)
{
v___x_2472_ = v_p_2463_;
v_isShared_2473_ = v_isSharedCheck_2481_;
goto v_resetjp_2471_;
}
else
{
lean_inc(v_snd_2470_);
lean_inc(v_fst_2469_);
lean_dec(v_p_2463_);
v___x_2472_ = lean_box(0);
v_isShared_2473_ = v_isSharedCheck_2481_;
goto v_resetjp_2471_;
}
v_resetjp_2471_:
{
lean_object* v___x_2475_; 
lean_inc(v_fst_2469_);
if (v_isShared_2468_ == 0)
{
lean_ctor_set_tag(v___x_2467_, 1);
lean_ctor_set(v___x_2467_, 1, v_fst_2464_);
lean_ctor_set(v___x_2467_, 0, v_fst_2469_);
v___x_2475_ = v___x_2467_;
goto v_reusejp_2474_;
}
else
{
lean_object* v_reuseFailAlloc_2480_; 
v_reuseFailAlloc_2480_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2480_, 0, v_fst_2469_);
lean_ctor_set(v_reuseFailAlloc_2480_, 1, v_fst_2464_);
v___x_2475_ = v_reuseFailAlloc_2480_;
goto v_reusejp_2474_;
}
v_reusejp_2474_:
{
lean_object* v___x_2476_; lean_object* v___x_2478_; 
v___x_2476_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_2469_, v_snd_2470_, v_snd_2465_);
if (v_isShared_2473_ == 0)
{
lean_ctor_set(v___x_2472_, 1, v___x_2476_);
lean_ctor_set(v___x_2472_, 0, v___x_2475_);
v___x_2478_ = v___x_2472_;
goto v_reusejp_2477_;
}
else
{
lean_object* v_reuseFailAlloc_2479_; 
v_reuseFailAlloc_2479_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2479_, 0, v___x_2475_);
lean_ctor_set(v_reuseFailAlloc_2479_, 1, v___x_2476_);
v___x_2478_ = v_reuseFailAlloc_2479_;
goto v_reusejp_2477_;
}
v_reusejp_2477_:
{
return v___x_2478_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1_spec__1___redArg(lean_object* v_init_2483_, lean_object* v_x_2484_){
_start:
{
if (lean_obj_tag(v_x_2484_) == 0)
{
lean_object* v_k_2485_; lean_object* v_v_2486_; lean_object* v_l_2487_; lean_object* v_r_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; 
v_k_2485_ = lean_ctor_get(v_x_2484_, 1);
v_v_2486_ = lean_ctor_get(v_x_2484_, 2);
v_l_2487_ = lean_ctor_get(v_x_2484_, 3);
v_r_2488_ = lean_ctor_get(v_x_2484_, 4);
v___x_2489_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1_spec__1___redArg(v_init_2483_, v_l_2487_);
lean_inc(v_v_2486_);
lean_inc(v_k_2485_);
v___x_2490_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2490_, 0, v_k_2485_);
lean_ctor_set(v___x_2490_, 1, v_v_2486_);
v___x_2491_ = lean_array_push(v___x_2489_, v___x_2490_);
v_init_2483_ = v___x_2491_;
v_x_2484_ = v_r_2488_;
goto _start;
}
else
{
return v_init_2483_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1_spec__1___redArg___boxed(lean_object* v_init_2493_, lean_object* v_x_2494_){
_start:
{
lean_object* v_res_2495_; 
v_res_2495_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1_spec__1___redArg(v_init_2493_, v_x_2494_);
lean_dec(v_x_2494_);
return v_res_2495_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2_spec__3___redArg(lean_object* v_hi_2496_, lean_object* v_pivot_2497_, lean_object* v_as_2498_, lean_object* v_i_2499_, lean_object* v_k_2500_){
_start:
{
uint8_t v___x_2501_; 
v___x_2501_ = lean_nat_dec_lt(v_k_2500_, v_hi_2496_);
if (v___x_2501_ == 0)
{
lean_object* v___x_2502_; lean_object* v___x_2503_; 
lean_dec(v_k_2500_);
v___x_2502_ = lean_array_fswap(v_as_2498_, v_i_2499_, v_hi_2496_);
v___x_2503_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2503_, 0, v_i_2499_);
lean_ctor_set(v___x_2503_, 1, v___x_2502_);
return v___x_2503_;
}
else
{
lean_object* v___x_2504_; lean_object* v_fst_2505_; lean_object* v_fst_2506_; uint8_t v___x_2507_; 
v___x_2504_ = lean_array_fget_borrowed(v_as_2498_, v_k_2500_);
v_fst_2505_ = lean_ctor_get(v___x_2504_, 0);
v_fst_2506_ = lean_ctor_get(v_pivot_2497_, 0);
v___x_2507_ = l_Lean_Name_quickLt(v_fst_2505_, v_fst_2506_);
if (v___x_2507_ == 0)
{
lean_object* v___x_2508_; lean_object* v___x_2509_; 
v___x_2508_ = lean_unsigned_to_nat(1u);
v___x_2509_ = lean_nat_add(v_k_2500_, v___x_2508_);
lean_dec(v_k_2500_);
v_k_2500_ = v___x_2509_;
goto _start;
}
else
{
lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; 
v___x_2511_ = lean_array_fswap(v_as_2498_, v_i_2499_, v_k_2500_);
v___x_2512_ = lean_unsigned_to_nat(1u);
v___x_2513_ = lean_nat_add(v_i_2499_, v___x_2512_);
lean_dec(v_i_2499_);
v___x_2514_ = lean_nat_add(v_k_2500_, v___x_2512_);
lean_dec(v_k_2500_);
v_as_2498_ = v___x_2511_;
v_i_2499_ = v___x_2513_;
v_k_2500_ = v___x_2514_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2_spec__3___redArg___boxed(lean_object* v_hi_2516_, lean_object* v_pivot_2517_, lean_object* v_as_2518_, lean_object* v_i_2519_, lean_object* v_k_2520_){
_start:
{
lean_object* v_res_2521_; 
v_res_2521_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2_spec__3___redArg(v_hi_2516_, v_pivot_2517_, v_as_2518_, v_i_2519_, v_k_2520_);
lean_dec_ref(v_pivot_2517_);
lean_dec(v_hi_2516_);
return v_res_2521_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2___redArg___lam__0(lean_object* v_a_2522_, lean_object* v_b_2523_){
_start:
{
lean_object* v_fst_2524_; lean_object* v_fst_2525_; uint8_t v___x_2526_; 
v_fst_2524_ = lean_ctor_get(v_a_2522_, 0);
v_fst_2525_ = lean_ctor_get(v_b_2523_, 0);
v___x_2526_ = l_Lean_Name_quickLt(v_fst_2524_, v_fst_2525_);
return v___x_2526_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2___redArg___lam__0___boxed(lean_object* v_a_2527_, lean_object* v_b_2528_){
_start:
{
uint8_t v_res_2529_; lean_object* v_r_2530_; 
v_res_2529_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2___redArg___lam__0(v_a_2527_, v_b_2528_);
lean_dec_ref(v_b_2528_);
lean_dec_ref(v_a_2527_);
v_r_2530_ = lean_box(v_res_2529_);
return v_r_2530_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2___redArg(lean_object* v_n_2531_, lean_object* v_as_2532_, lean_object* v_lo_2533_, lean_object* v_hi_2534_){
_start:
{
lean_object* v___y_2536_; uint8_t v___x_2546_; 
v___x_2546_ = lean_nat_dec_lt(v_lo_2533_, v_hi_2534_);
if (v___x_2546_ == 0)
{
lean_dec(v_lo_2533_);
return v_as_2532_;
}
else
{
lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v_mid_2549_; lean_object* v___y_2551_; lean_object* v___y_2557_; lean_object* v___x_2562_; lean_object* v___x_2563_; uint8_t v___x_2564_; 
v___x_2547_ = lean_nat_add(v_lo_2533_, v_hi_2534_);
v___x_2548_ = lean_unsigned_to_nat(1u);
v_mid_2549_ = lean_nat_shiftr(v___x_2547_, v___x_2548_);
lean_dec(v___x_2547_);
v___x_2562_ = lean_array_fget_borrowed(v_as_2532_, v_mid_2549_);
v___x_2563_ = lean_array_fget_borrowed(v_as_2532_, v_lo_2533_);
v___x_2564_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2___redArg___lam__0(v___x_2562_, v___x_2563_);
if (v___x_2564_ == 0)
{
v___y_2557_ = v_as_2532_;
goto v___jp_2556_;
}
else
{
lean_object* v___x_2565_; 
v___x_2565_ = lean_array_fswap(v_as_2532_, v_lo_2533_, v_mid_2549_);
v___y_2557_ = v___x_2565_;
goto v___jp_2556_;
}
v___jp_2550_:
{
lean_object* v___x_2552_; lean_object* v___x_2553_; uint8_t v___x_2554_; 
v___x_2552_ = lean_array_fget_borrowed(v___y_2551_, v_mid_2549_);
v___x_2553_ = lean_array_fget_borrowed(v___y_2551_, v_hi_2534_);
v___x_2554_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2___redArg___lam__0(v___x_2552_, v___x_2553_);
if (v___x_2554_ == 0)
{
lean_dec(v_mid_2549_);
v___y_2536_ = v___y_2551_;
goto v___jp_2535_;
}
else
{
lean_object* v___x_2555_; 
v___x_2555_ = lean_array_fswap(v___y_2551_, v_mid_2549_, v_hi_2534_);
lean_dec(v_mid_2549_);
v___y_2536_ = v___x_2555_;
goto v___jp_2535_;
}
}
v___jp_2556_:
{
lean_object* v___x_2558_; lean_object* v___x_2559_; uint8_t v___x_2560_; 
v___x_2558_ = lean_array_fget_borrowed(v___y_2557_, v_hi_2534_);
v___x_2559_ = lean_array_fget_borrowed(v___y_2557_, v_lo_2533_);
v___x_2560_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2___redArg___lam__0(v___x_2558_, v___x_2559_);
if (v___x_2560_ == 0)
{
v___y_2551_ = v___y_2557_;
goto v___jp_2550_;
}
else
{
lean_object* v___x_2561_; 
v___x_2561_ = lean_array_fswap(v___y_2557_, v_lo_2533_, v_hi_2534_);
v___y_2551_ = v___x_2561_;
goto v___jp_2550_;
}
}
}
v___jp_2535_:
{
lean_object* v_pivot_2537_; lean_object* v___x_2538_; lean_object* v_fst_2539_; lean_object* v_snd_2540_; uint8_t v___x_2541_; 
v_pivot_2537_ = lean_array_fget(v___y_2536_, v_hi_2534_);
lean_inc_n(v_lo_2533_, 2);
v___x_2538_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2_spec__3___redArg(v_hi_2534_, v_pivot_2537_, v___y_2536_, v_lo_2533_, v_lo_2533_);
lean_dec(v_pivot_2537_);
v_fst_2539_ = lean_ctor_get(v___x_2538_, 0);
lean_inc(v_fst_2539_);
v_snd_2540_ = lean_ctor_get(v___x_2538_, 1);
lean_inc(v_snd_2540_);
lean_dec_ref(v___x_2538_);
v___x_2541_ = lean_nat_dec_le(v_hi_2534_, v_fst_2539_);
if (v___x_2541_ == 0)
{
lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; 
v___x_2542_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2___redArg(v_n_2531_, v_snd_2540_, v_lo_2533_, v_fst_2539_);
v___x_2543_ = lean_unsigned_to_nat(1u);
v___x_2544_ = lean_nat_add(v_fst_2539_, v___x_2543_);
lean_dec(v_fst_2539_);
v_as_2532_ = v___x_2542_;
v_lo_2533_ = v___x_2544_;
goto _start;
}
else
{
lean_dec(v_fst_2539_);
lean_dec(v_lo_2533_);
return v_snd_2540_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2___redArg___boxed(lean_object* v_n_2566_, lean_object* v_as_2567_, lean_object* v_lo_2568_, lean_object* v_hi_2569_){
_start:
{
lean_object* v_res_2570_; 
v_res_2570_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2___redArg(v_n_2566_, v_as_2567_, v_lo_2568_, v_hi_2569_);
lean_dec(v_hi_2569_);
lean_dec(v_n_2566_);
return v_res_2570_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3_spec__5___redArg(lean_object* v_snd_2571_, lean_object* v_as_2572_, size_t v_i_2573_, size_t v_stop_2574_, lean_object* v_b_2575_){
_start:
{
lean_object* v___y_2577_; uint8_t v___x_2581_; 
v___x_2581_ = lean_usize_dec_eq(v_i_2573_, v_stop_2574_);
if (v___x_2581_ == 0)
{
lean_object* v___x_2582_; lean_object* v___x_2583_; 
v___x_2582_ = lean_array_uget_borrowed(v_as_2572_, v_i_2573_);
v___x_2583_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_snd_2571_, v___x_2582_);
if (lean_obj_tag(v___x_2583_) == 0)
{
v___y_2577_ = v_b_2575_;
goto v___jp_2576_;
}
else
{
lean_object* v_val_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; 
v_val_2584_ = lean_ctor_get(v___x_2583_, 0);
lean_inc(v_val_2584_);
lean_dec_ref(v___x_2583_);
lean_inc(v___x_2582_);
v___x_2585_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2585_, 0, v___x_2582_);
lean_ctor_set(v___x_2585_, 1, v_val_2584_);
v___x_2586_ = lean_array_push(v_b_2575_, v___x_2585_);
v___y_2577_ = v___x_2586_;
goto v___jp_2576_;
}
}
else
{
return v_b_2575_;
}
v___jp_2576_:
{
size_t v___x_2578_; size_t v___x_2579_; 
v___x_2578_ = ((size_t)1ULL);
v___x_2579_ = lean_usize_add(v_i_2573_, v___x_2578_);
v_i_2573_ = v___x_2579_;
v_b_2575_ = v___y_2577_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3_spec__5___redArg___boxed(lean_object* v_snd_2587_, lean_object* v_as_2588_, lean_object* v_i_2589_, lean_object* v_stop_2590_, lean_object* v_b_2591_){
_start:
{
size_t v_i_boxed_2592_; size_t v_stop_boxed_2593_; lean_object* v_res_2594_; 
v_i_boxed_2592_ = lean_unbox_usize(v_i_2589_);
lean_dec(v_i_2589_);
v_stop_boxed_2593_ = lean_unbox_usize(v_stop_2590_);
lean_dec(v_stop_2590_);
v_res_2594_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3_spec__5___redArg(v_snd_2587_, v_as_2588_, v_i_boxed_2592_, v_stop_boxed_2593_, v_b_2591_);
lean_dec_ref(v_as_2588_);
lean_dec(v_snd_2587_);
return v_res_2594_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3___redArg(lean_object* v_snd_2595_, lean_object* v_as_2596_, lean_object* v_start_2597_, lean_object* v_stop_2598_){
_start:
{
lean_object* v___x_2599_; uint8_t v___x_2600_; 
v___x_2599_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___lam__2___closed__0));
v___x_2600_ = lean_nat_dec_lt(v_start_2597_, v_stop_2598_);
if (v___x_2600_ == 0)
{
return v___x_2599_;
}
else
{
lean_object* v___x_2601_; uint8_t v___x_2602_; 
v___x_2601_ = lean_array_get_size(v_as_2596_);
v___x_2602_ = lean_nat_dec_le(v_stop_2598_, v___x_2601_);
if (v___x_2602_ == 0)
{
uint8_t v___x_2603_; 
v___x_2603_ = lean_nat_dec_lt(v_start_2597_, v___x_2601_);
if (v___x_2603_ == 0)
{
return v___x_2599_;
}
else
{
size_t v___x_2604_; size_t v___x_2605_; lean_object* v___x_2606_; 
v___x_2604_ = lean_usize_of_nat(v_start_2597_);
v___x_2605_ = lean_usize_of_nat(v___x_2601_);
v___x_2606_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3_spec__5___redArg(v_snd_2595_, v_as_2596_, v___x_2604_, v___x_2605_, v___x_2599_);
return v___x_2606_;
}
}
else
{
size_t v___x_2607_; size_t v___x_2608_; lean_object* v___x_2609_; 
v___x_2607_ = lean_usize_of_nat(v_start_2597_);
v___x_2608_ = lean_usize_of_nat(v_stop_2598_);
v___x_2609_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3_spec__5___redArg(v_snd_2595_, v_as_2596_, v___x_2607_, v___x_2608_, v___x_2599_);
return v___x_2609_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3___redArg___boxed(lean_object* v_snd_2610_, lean_object* v_as_2611_, lean_object* v_start_2612_, lean_object* v_stop_2613_){
_start:
{
lean_object* v_res_2614_; 
v_res_2614_ = l_Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3___redArg(v_snd_2610_, v_as_2611_, v_start_2612_, v_stop_2613_);
lean_dec(v_stop_2613_);
lean_dec(v_start_2612_);
lean_dec_ref(v_as_2611_);
lean_dec(v_snd_2610_);
return v_res_2614_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttribute_spec__0___redArg(lean_object* v_impl_2615_, lean_object* v_env_2616_, lean_object* v_as_2617_, size_t v_i_2618_, size_t v_stop_2619_, lean_object* v_b_2620_){
_start:
{
lean_object* v___y_2622_; uint8_t v___x_2626_; 
v___x_2626_ = lean_usize_dec_eq(v_i_2618_, v_stop_2619_);
if (v___x_2626_ == 0)
{
lean_object* v___x_2627_; lean_object* v_fst_2628_; lean_object* v_snd_2629_; lean_object* v_filterExport_2630_; lean_object* v___x_2631_; uint8_t v___x_2632_; 
v___x_2627_ = lean_array_uget_borrowed(v_as_2617_, v_i_2618_);
v_fst_2628_ = lean_ctor_get(v___x_2627_, 0);
v_snd_2629_ = lean_ctor_get(v___x_2627_, 1);
v_filterExport_2630_ = lean_ctor_get(v_impl_2615_, 3);
lean_inc_ref(v_filterExport_2630_);
lean_inc(v_snd_2629_);
lean_inc(v_fst_2628_);
lean_inc_ref(v_env_2616_);
v___x_2631_ = lean_apply_3(v_filterExport_2630_, v_env_2616_, v_fst_2628_, v_snd_2629_);
v___x_2632_ = lean_unbox(v___x_2631_);
if (v___x_2632_ == 0)
{
v___y_2622_ = v_b_2620_;
goto v___jp_2621_;
}
else
{
lean_object* v___x_2633_; 
lean_inc(v___x_2627_);
v___x_2633_ = lean_array_push(v_b_2620_, v___x_2627_);
v___y_2622_ = v___x_2633_;
goto v___jp_2621_;
}
}
else
{
lean_dec_ref(v_env_2616_);
lean_dec_ref(v_impl_2615_);
return v_b_2620_;
}
v___jp_2621_:
{
size_t v___x_2623_; size_t v___x_2624_; 
v___x_2623_ = ((size_t)1ULL);
v___x_2624_ = lean_usize_add(v_i_2618_, v___x_2623_);
v_i_2618_ = v___x_2624_;
v_b_2620_ = v___y_2622_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttribute_spec__0___redArg___boxed(lean_object* v_impl_2634_, lean_object* v_env_2635_, lean_object* v_as_2636_, lean_object* v_i_2637_, lean_object* v_stop_2638_, lean_object* v_b_2639_){
_start:
{
size_t v_i_boxed_2640_; size_t v_stop_boxed_2641_; lean_object* v_res_2642_; 
v_i_boxed_2640_ = lean_unbox_usize(v_i_2637_);
lean_dec(v_i_2637_);
v_stop_boxed_2641_ = lean_unbox_usize(v_stop_2638_);
lean_dec(v_stop_2638_);
v_res_2642_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttribute_spec__0___redArg(v_impl_2634_, v_env_2635_, v_as_2636_, v_i_boxed_2640_, v_stop_boxed_2641_, v_b_2639_);
lean_dec_ref(v_as_2636_);
return v_res_2642_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___lam__1(lean_object* v_impl_2643_, uint8_t v_preserveOrder_2644_, lean_object* v_env_2645_, lean_object* v_x_2646_){
_start:
{
lean_object* v___y_2648_; 
if (v_preserveOrder_2644_ == 0)
{
lean_object* v_snd_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; lean_object* v_r_2667_; lean_object* v___x_2668_; lean_object* v___y_2670_; lean_object* v___y_2671_; uint8_t v___x_2673_; 
v_snd_2664_ = lean_ctor_get(v_x_2646_, 1);
lean_inc(v_snd_2664_);
lean_dec_ref(v_x_2646_);
v___x_2665_ = lean_unsigned_to_nat(0u);
v___x_2666_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___lam__2___closed__0));
v_r_2667_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1_spec__1___redArg(v___x_2666_, v_snd_2664_);
lean_dec(v_snd_2664_);
v___x_2668_ = lean_array_get_size(v_r_2667_);
v___x_2673_ = lean_nat_dec_eq(v___x_2668_, v___x_2665_);
if (v___x_2673_ == 0)
{
lean_object* v___x_2674_; lean_object* v___x_2675_; lean_object* v___y_2677_; uint8_t v___x_2679_; 
v___x_2674_ = lean_unsigned_to_nat(1u);
v___x_2675_ = lean_nat_sub(v___x_2668_, v___x_2674_);
v___x_2679_ = lean_nat_dec_le(v___x_2665_, v___x_2675_);
if (v___x_2679_ == 0)
{
lean_inc(v___x_2675_);
v___y_2677_ = v___x_2675_;
goto v___jp_2676_;
}
else
{
v___y_2677_ = v___x_2665_;
goto v___jp_2676_;
}
v___jp_2676_:
{
uint8_t v___x_2678_; 
v___x_2678_ = lean_nat_dec_le(v___y_2677_, v___x_2675_);
if (v___x_2678_ == 0)
{
lean_dec(v___x_2675_);
lean_inc(v___y_2677_);
v___y_2670_ = v___y_2677_;
v___y_2671_ = v___y_2677_;
goto v___jp_2669_;
}
else
{
v___y_2670_ = v___y_2677_;
v___y_2671_ = v___x_2675_;
goto v___jp_2669_;
}
}
}
else
{
v___y_2648_ = v_r_2667_;
goto v___jp_2647_;
}
v___jp_2669_:
{
lean_object* v___x_2672_; 
v___x_2672_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2___redArg(v___x_2668_, v_r_2667_, v___y_2670_, v___y_2671_);
lean_dec(v___y_2671_);
v___y_2648_ = v___x_2672_;
goto v___jp_2647_;
}
}
else
{
lean_object* v_fst_2680_; lean_object* v_snd_2681_; lean_object* v___x_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; 
v_fst_2680_ = lean_ctor_get(v_x_2646_, 0);
lean_inc(v_fst_2680_);
v_snd_2681_ = lean_ctor_get(v_x_2646_, 1);
lean_inc(v_snd_2681_);
lean_dec_ref(v_x_2646_);
v___x_2682_ = lean_array_mk(v_fst_2680_);
v___x_2683_ = l_Array_reverse___redArg(v___x_2682_);
v___x_2684_ = lean_unsigned_to_nat(0u);
v___x_2685_ = lean_array_get_size(v___x_2683_);
v___x_2686_ = l_Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3___redArg(v_snd_2681_, v___x_2683_, v___x_2684_, v___x_2685_);
lean_dec_ref(v___x_2683_);
lean_dec(v_snd_2681_);
v___y_2648_ = v___x_2686_;
goto v___jp_2647_;
}
v___jp_2647_:
{
lean_object* v___x_2649_; lean_object* v___x_2650_; lean_object* v___x_2651_; uint8_t v___x_2652_; 
v___x_2649_ = lean_unsigned_to_nat(0u);
v___x_2650_ = lean_array_get_size(v___y_2648_);
v___x_2651_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___lam__2___closed__0));
v___x_2652_ = lean_nat_dec_lt(v___x_2649_, v___x_2650_);
if (v___x_2652_ == 0)
{
lean_object* v___x_2653_; 
lean_dec_ref(v_env_2645_);
lean_dec_ref(v_impl_2643_);
v___x_2653_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2653_, 0, v___x_2651_);
lean_ctor_set(v___x_2653_, 1, v___x_2651_);
lean_ctor_set(v___x_2653_, 2, v___y_2648_);
return v___x_2653_;
}
else
{
uint8_t v___x_2654_; 
v___x_2654_ = lean_nat_dec_le(v___x_2650_, v___x_2650_);
if (v___x_2654_ == 0)
{
if (v___x_2652_ == 0)
{
lean_object* v___x_2655_; 
lean_dec_ref(v_env_2645_);
lean_dec_ref(v_impl_2643_);
v___x_2655_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2655_, 0, v___x_2651_);
lean_ctor_set(v___x_2655_, 1, v___x_2651_);
lean_ctor_set(v___x_2655_, 2, v___y_2648_);
return v___x_2655_;
}
else
{
size_t v___x_2656_; size_t v___x_2657_; lean_object* v___x_2658_; lean_object* v___x_2659_; 
v___x_2656_ = ((size_t)0ULL);
v___x_2657_ = lean_usize_of_nat(v___x_2650_);
v___x_2658_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttribute_spec__0___redArg(v_impl_2643_, v_env_2645_, v___y_2648_, v___x_2656_, v___x_2657_, v___x_2651_);
lean_inc_ref(v___x_2658_);
v___x_2659_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2659_, 0, v___x_2658_);
lean_ctor_set(v___x_2659_, 1, v___x_2658_);
lean_ctor_set(v___x_2659_, 2, v___y_2648_);
return v___x_2659_;
}
}
else
{
size_t v___x_2660_; size_t v___x_2661_; lean_object* v___x_2662_; lean_object* v___x_2663_; 
v___x_2660_ = ((size_t)0ULL);
v___x_2661_ = lean_usize_of_nat(v___x_2650_);
v___x_2662_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttribute_spec__0___redArg(v_impl_2643_, v_env_2645_, v___y_2648_, v___x_2660_, v___x_2661_, v___x_2651_);
lean_inc_ref(v___x_2662_);
v___x_2663_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2663_, 0, v___x_2662_);
lean_ctor_set(v___x_2663_, 1, v___x_2662_);
lean_ctor_set(v___x_2663_, 2, v___y_2648_);
return v___x_2663_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___lam__1___boxed(lean_object* v_impl_2687_, lean_object* v_preserveOrder_2688_, lean_object* v_env_2689_, lean_object* v_x_2690_){
_start:
{
uint8_t v_preserveOrder_boxed_2691_; lean_object* v_res_2692_; 
v_preserveOrder_boxed_2691_ = lean_unbox(v_preserveOrder_2688_);
v_res_2692_ = l_Lean_registerParametricAttribute___redArg___lam__1(v_impl_2687_, v_preserveOrder_boxed_2691_, v_env_2689_, v_x_2690_);
return v_res_2692_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___lam__2(lean_object* v_x_2702_){
_start:
{
lean_object* v_snd_2703_; lean_object* v___x_2705_; uint8_t v_isShared_2706_; uint8_t v_isSharedCheck_2717_; 
v_snd_2703_ = lean_ctor_get(v_x_2702_, 1);
v_isSharedCheck_2717_ = !lean_is_exclusive(v_x_2702_);
if (v_isSharedCheck_2717_ == 0)
{
lean_object* v_unused_2718_; 
v_unused_2718_ = lean_ctor_get(v_x_2702_, 0);
lean_dec(v_unused_2718_);
v___x_2705_ = v_x_2702_;
v_isShared_2706_ = v_isSharedCheck_2717_;
goto v_resetjp_2704_;
}
else
{
lean_inc(v_snd_2703_);
lean_dec(v_x_2702_);
v___x_2705_ = lean_box(0);
v_isShared_2706_ = v_isSharedCheck_2717_;
goto v_resetjp_2704_;
}
v_resetjp_2704_:
{
lean_object* v___x_2707_; lean_object* v___y_2709_; 
v___x_2707_ = ((lean_object*)(l_Lean_registerParametricAttribute___redArg___lam__2___closed__3));
if (lean_obj_tag(v_snd_2703_) == 0)
{
lean_object* v_size_2715_; 
v_size_2715_ = lean_ctor_get(v_snd_2703_, 0);
lean_inc(v_size_2715_);
lean_dec_ref(v_snd_2703_);
v___y_2709_ = v_size_2715_;
goto v___jp_2708_;
}
else
{
lean_object* v___x_2716_; 
v___x_2716_ = lean_unsigned_to_nat(0u);
v___y_2709_ = v___x_2716_;
goto v___jp_2708_;
}
v___jp_2708_:
{
lean_object* v___x_2710_; lean_object* v___x_2711_; lean_object* v___x_2713_; 
v___x_2710_ = l_Nat_reprFast(v___y_2709_);
v___x_2711_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2711_, 0, v___x_2710_);
if (v_isShared_2706_ == 0)
{
lean_ctor_set_tag(v___x_2705_, 5);
lean_ctor_set(v___x_2705_, 1, v___x_2711_);
lean_ctor_set(v___x_2705_, 0, v___x_2707_);
v___x_2713_ = v___x_2705_;
goto v_reusejp_2712_;
}
else
{
lean_object* v_reuseFailAlloc_2714_; 
v_reuseFailAlloc_2714_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2714_, 0, v___x_2707_);
lean_ctor_set(v_reuseFailAlloc_2714_, 1, v___x_2711_);
v___x_2713_ = v_reuseFailAlloc_2714_;
goto v_reusejp_2712_;
}
v_reusejp_2712_:
{
return v___x_2713_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___lam__3(lean_object* v_x_2719_){
_start:
{
lean_object* v___x_2720_; 
v___x_2720_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___lam__2___closed__0));
return v___x_2720_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___lam__3___boxed(lean_object* v_x_2721_){
_start:
{
lean_object* v_res_2722_; 
v_res_2722_ = l_Lean_registerParametricAttribute___redArg___lam__3(v_x_2721_);
lean_dec_ref(v_x_2721_);
return v_res_2722_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___lam__4(lean_object* v___x_2723_, lean_object* v_x_2724_, lean_object* v___y_2725_){
_start:
{
lean_object* v___x_2727_; 
v___x_2727_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2727_, 0, v___x_2723_);
return v___x_2727_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___lam__4___boxed(lean_object* v___x_2728_, lean_object* v_x_2729_, lean_object* v___y_2730_, lean_object* v___y_2731_){
_start:
{
lean_object* v_res_2732_; 
v_res_2732_ = l_Lean_registerParametricAttribute___redArg___lam__4(v___x_2728_, v_x_2729_, v___y_2730_);
lean_dec_ref(v___y_2730_);
lean_dec_ref(v_x_2729_);
return v_res_2732_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___lam__5(lean_object* v___x_2733_){
_start:
{
lean_object* v___x_2735_; 
v___x_2735_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2735_, 0, v___x_2733_);
return v___x_2735_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___lam__5___boxed(lean_object* v___x_2736_, lean_object* v___y_2737_){
_start:
{
lean_object* v_res_2738_; 
v_res_2738_ = l_Lean_registerParametricAttribute___redArg___lam__5(v___x_2736_);
return v_res_2738_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___lam__7(lean_object* v_getParam_2739_, lean_object* v_a_2740_, lean_object* v_afterSet_2741_, lean_object* v_name_2742_, lean_object* v_decl_2743_, lean_object* v_stx_2744_, uint8_t v_kind_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_){
_start:
{
lean_object* v___y_2750_; lean_object* v___y_2751_; lean_object* v___y_2752_; lean_object* v___y_2753_; uint8_t v___y_2754_; lean_object* v___y_2757_; lean_object* v___y_2758_; lean_object* v___y_2759_; uint8_t v___x_2802_; uint8_t v___x_2803_; 
v___x_2802_ = 0;
v___x_2803_ = l_Lean_instBEqAttributeKind_beq(v_kind_2745_, v___x_2802_);
if (v___x_2803_ == 0)
{
lean_object* v___x_2804_; 
lean_dec(v_stx_2744_);
lean_dec(v_decl_2743_);
lean_dec_ref(v_afterSet_2741_);
lean_dec_ref(v_a_2740_);
lean_dec_ref(v_getParam_2739_);
v___x_2804_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg(v_name_2742_, v_kind_2745_, v___y_2746_, v___y_2747_);
return v___x_2804_;
}
else
{
goto v___jp_2797_;
}
v___jp_2749_:
{
if (v___y_2754_ == 0)
{
lean_object* v___x_2755_; 
lean_dec_ref(v___y_2750_);
v___x_2755_ = l_Lean_setEnv___at___00Lean_registerParametricAttribute_spec__4___redArg(v___y_2753_, v___y_2752_);
return v___x_2755_;
}
else
{
lean_dec_ref(v___y_2753_);
return v___y_2750_;
}
}
v___jp_2756_:
{
lean_object* v___x_2760_; 
lean_inc(v___y_2759_);
lean_inc_ref(v___y_2758_);
lean_inc(v_decl_2743_);
v___x_2760_ = lean_apply_5(v_getParam_2739_, v_decl_2743_, v_stx_2744_, v___y_2758_, v___y_2759_, lean_box(0));
if (lean_obj_tag(v___x_2760_) == 0)
{
lean_object* v_a_2761_; lean_object* v___x_2762_; lean_object* v_toEnvExtension_2763_; lean_object* v_env_2764_; lean_object* v_nextMacroScope_2765_; lean_object* v_ngen_2766_; lean_object* v_auxDeclNGen_2767_; lean_object* v_traceState_2768_; lean_object* v_messages_2769_; lean_object* v_infoState_2770_; lean_object* v_snapshotTasks_2771_; lean_object* v___x_2773_; uint8_t v_isShared_2774_; uint8_t v_isSharedCheck_2787_; 
v_a_2761_ = lean_ctor_get(v___x_2760_, 0);
lean_inc(v_a_2761_);
lean_dec_ref(v___x_2760_);
v___x_2762_ = lean_st_ref_take(v___y_2759_);
v_toEnvExtension_2763_ = lean_ctor_get(v_a_2740_, 0);
v_env_2764_ = lean_ctor_get(v___x_2762_, 0);
v_nextMacroScope_2765_ = lean_ctor_get(v___x_2762_, 1);
v_ngen_2766_ = lean_ctor_get(v___x_2762_, 2);
v_auxDeclNGen_2767_ = lean_ctor_get(v___x_2762_, 3);
v_traceState_2768_ = lean_ctor_get(v___x_2762_, 4);
v_messages_2769_ = lean_ctor_get(v___x_2762_, 6);
v_infoState_2770_ = lean_ctor_get(v___x_2762_, 7);
v_snapshotTasks_2771_ = lean_ctor_get(v___x_2762_, 8);
v_isSharedCheck_2787_ = !lean_is_exclusive(v___x_2762_);
if (v_isSharedCheck_2787_ == 0)
{
lean_object* v_unused_2788_; 
v_unused_2788_ = lean_ctor_get(v___x_2762_, 5);
lean_dec(v_unused_2788_);
v___x_2773_ = v___x_2762_;
v_isShared_2774_ = v_isSharedCheck_2787_;
goto v_resetjp_2772_;
}
else
{
lean_inc(v_snapshotTasks_2771_);
lean_inc(v_infoState_2770_);
lean_inc(v_messages_2769_);
lean_inc(v_traceState_2768_);
lean_inc(v_auxDeclNGen_2767_);
lean_inc(v_ngen_2766_);
lean_inc(v_nextMacroScope_2765_);
lean_inc(v_env_2764_);
lean_dec(v___x_2762_);
v___x_2773_ = lean_box(0);
v_isShared_2774_ = v_isSharedCheck_2787_;
goto v_resetjp_2772_;
}
v_resetjp_2772_:
{
lean_object* v_asyncMode_2775_; lean_object* v___x_2776_; lean_object* v___x_2777_; lean_object* v___x_2778_; lean_object* v___x_2780_; 
v_asyncMode_2775_ = lean_ctor_get(v_toEnvExtension_2763_, 2);
lean_inc(v_asyncMode_2775_);
lean_inc(v_a_2761_);
lean_inc_n(v_decl_2743_, 2);
v___x_2776_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2776_, 0, v_decl_2743_);
lean_ctor_set(v___x_2776_, 1, v_a_2761_);
v___x_2777_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_a_2740_, v_env_2764_, v___x_2776_, v_asyncMode_2775_, v_decl_2743_);
lean_dec(v_asyncMode_2775_);
v___x_2778_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2);
if (v_isShared_2774_ == 0)
{
lean_ctor_set(v___x_2773_, 5, v___x_2778_);
lean_ctor_set(v___x_2773_, 0, v___x_2777_);
v___x_2780_ = v___x_2773_;
goto v_reusejp_2779_;
}
else
{
lean_object* v_reuseFailAlloc_2786_; 
v_reuseFailAlloc_2786_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2786_, 0, v___x_2777_);
lean_ctor_set(v_reuseFailAlloc_2786_, 1, v_nextMacroScope_2765_);
lean_ctor_set(v_reuseFailAlloc_2786_, 2, v_ngen_2766_);
lean_ctor_set(v_reuseFailAlloc_2786_, 3, v_auxDeclNGen_2767_);
lean_ctor_set(v_reuseFailAlloc_2786_, 4, v_traceState_2768_);
lean_ctor_set(v_reuseFailAlloc_2786_, 5, v___x_2778_);
lean_ctor_set(v_reuseFailAlloc_2786_, 6, v_messages_2769_);
lean_ctor_set(v_reuseFailAlloc_2786_, 7, v_infoState_2770_);
lean_ctor_set(v_reuseFailAlloc_2786_, 8, v_snapshotTasks_2771_);
v___x_2780_ = v_reuseFailAlloc_2786_;
goto v_reusejp_2779_;
}
v_reusejp_2779_:
{
lean_object* v___x_2781_; lean_object* v___x_2782_; 
v___x_2781_ = lean_st_ref_set(v___y_2759_, v___x_2780_);
lean_inc(v___y_2759_);
lean_inc_ref(v___y_2758_);
v___x_2782_ = lean_apply_5(v_afterSet_2741_, v_decl_2743_, v_a_2761_, v___y_2758_, v___y_2759_, lean_box(0));
if (lean_obj_tag(v___x_2782_) == 0)
{
lean_dec_ref(v___y_2757_);
return v___x_2782_;
}
else
{
lean_object* v_a_2783_; uint8_t v___x_2784_; 
v_a_2783_ = lean_ctor_get(v___x_2782_, 0);
lean_inc(v_a_2783_);
v___x_2784_ = l_Lean_Exception_isInterrupt(v_a_2783_);
if (v___x_2784_ == 0)
{
uint8_t v___x_2785_; 
v___x_2785_ = l_Lean_Exception_isRuntime(v_a_2783_);
v___y_2750_ = v___x_2782_;
v___y_2751_ = v___y_2758_;
v___y_2752_ = v___y_2759_;
v___y_2753_ = v___y_2757_;
v___y_2754_ = v___x_2785_;
goto v___jp_2749_;
}
else
{
lean_dec(v_a_2783_);
v___y_2750_ = v___x_2782_;
v___y_2751_ = v___y_2758_;
v___y_2752_ = v___y_2759_;
v___y_2753_ = v___y_2757_;
v___y_2754_ = v___x_2784_;
goto v___jp_2749_;
}
}
}
}
}
else
{
lean_object* v_a_2789_; lean_object* v___x_2791_; uint8_t v_isShared_2792_; uint8_t v_isSharedCheck_2796_; 
lean_dec_ref(v___y_2757_);
lean_dec(v_decl_2743_);
lean_dec_ref(v_afterSet_2741_);
lean_dec_ref(v_a_2740_);
v_a_2789_ = lean_ctor_get(v___x_2760_, 0);
v_isSharedCheck_2796_ = !lean_is_exclusive(v___x_2760_);
if (v_isSharedCheck_2796_ == 0)
{
v___x_2791_ = v___x_2760_;
v_isShared_2792_ = v_isSharedCheck_2796_;
goto v_resetjp_2790_;
}
else
{
lean_inc(v_a_2789_);
lean_dec(v___x_2760_);
v___x_2791_ = lean_box(0);
v_isShared_2792_ = v_isSharedCheck_2796_;
goto v_resetjp_2790_;
}
v_resetjp_2790_:
{
lean_object* v___x_2794_; 
if (v_isShared_2792_ == 0)
{
v___x_2794_ = v___x_2791_;
goto v_reusejp_2793_;
}
else
{
lean_object* v_reuseFailAlloc_2795_; 
v_reuseFailAlloc_2795_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2795_, 0, v_a_2789_);
v___x_2794_ = v_reuseFailAlloc_2795_;
goto v_reusejp_2793_;
}
v_reusejp_2793_:
{
return v___x_2794_;
}
}
}
}
v___jp_2797_:
{
lean_object* v___x_2798_; lean_object* v_env_2799_; lean_object* v___x_2800_; 
v___x_2798_ = lean_st_ref_get(v___y_2747_);
v_env_2799_ = lean_ctor_get(v___x_2798_, 0);
lean_inc_ref(v_env_2799_);
lean_dec(v___x_2798_);
v___x_2800_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2799_, v_decl_2743_);
if (lean_obj_tag(v___x_2800_) == 0)
{
lean_dec(v_name_2742_);
v___y_2757_ = v_env_2799_;
v___y_2758_ = v___y_2746_;
v___y_2759_ = v___y_2747_;
goto v___jp_2756_;
}
else
{
lean_object* v___x_2801_; 
lean_dec_ref(v___x_2800_);
lean_dec_ref(v_env_2799_);
lean_dec(v_stx_2744_);
lean_dec_ref(v_afterSet_2741_);
lean_dec_ref(v_a_2740_);
lean_dec_ref(v_getParam_2739_);
v___x_2801_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg(v_name_2742_, v_decl_2743_, v___y_2746_, v___y_2747_);
return v___x_2801_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___lam__7___boxed(lean_object* v_getParam_2805_, lean_object* v_a_2806_, lean_object* v_afterSet_2807_, lean_object* v_name_2808_, lean_object* v_decl_2809_, lean_object* v_stx_2810_, lean_object* v_kind_2811_, lean_object* v___y_2812_, lean_object* v___y_2813_, lean_object* v___y_2814_){
_start:
{
uint8_t v_kind_boxed_2815_; lean_object* v_res_2816_; 
v_kind_boxed_2815_ = lean_unbox(v_kind_2811_);
v_res_2816_ = l_Lean_registerParametricAttribute___redArg___lam__7(v_getParam_2805_, v_a_2806_, v_afterSet_2807_, v_name_2808_, v_decl_2809_, v_stx_2810_, v_kind_boxed_2815_, v___y_2812_, v___y_2813_);
lean_dec(v___y_2813_);
lean_dec_ref(v___y_2812_);
return v_res_2816_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg(lean_object* v_impl_2827_){
_start:
{
lean_object* v_toAttributeImplCore_2829_; lean_object* v_getParam_2830_; lean_object* v_afterSet_2831_; uint8_t v_preserveOrder_2832_; lean_object* v_ref_2833_; lean_object* v_name_2834_; lean_object* v___f_2835_; lean_object* v___x_2836_; lean_object* v___f_2837_; lean_object* v___f_2838_; lean_object* v___f_2839_; lean_object* v___f_2840_; lean_object* v___f_2841_; lean_object* v___x_2842_; lean_object* v___x_2843_; lean_object* v___x_2844_; lean_object* v___x_2845_; lean_object* v___x_2846_; 
v_toAttributeImplCore_2829_ = lean_ctor_get(v_impl_2827_, 0);
lean_inc_ref(v_toAttributeImplCore_2829_);
v_getParam_2830_ = lean_ctor_get(v_impl_2827_, 1);
lean_inc_ref(v_getParam_2830_);
v_afterSet_2831_ = lean_ctor_get(v_impl_2827_, 2);
lean_inc_ref(v_afterSet_2831_);
v_preserveOrder_2832_ = lean_ctor_get_uint8(v_impl_2827_, sizeof(void*)*4);
v_ref_2833_ = lean_ctor_get(v_toAttributeImplCore_2829_, 0);
v_name_2834_ = lean_ctor_get(v_toAttributeImplCore_2829_, 1);
v___f_2835_ = ((lean_object*)(l_Lean_registerParametricAttribute___redArg___closed__0));
v___x_2836_ = lean_box(v_preserveOrder_2832_);
v___f_2837_ = lean_alloc_closure((void*)(l_Lean_registerParametricAttribute___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_2837_, 0, v_impl_2827_);
lean_closure_set(v___f_2837_, 1, v___x_2836_);
v___f_2838_ = ((lean_object*)(l_Lean_registerParametricAttribute___redArg___closed__1));
v___f_2839_ = ((lean_object*)(l_Lean_registerParametricAttribute___redArg___closed__2));
v___f_2840_ = ((lean_object*)(l_Lean_registerParametricAttribute___redArg___closed__4));
v___f_2841_ = ((lean_object*)(l_Lean_registerParametricAttribute___redArg___closed__5));
v___x_2842_ = lean_box(2);
v___x_2843_ = lean_box(0);
lean_inc(v_ref_2833_);
v___x_2844_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_2844_, 0, v_ref_2833_);
lean_ctor_set(v___x_2844_, 1, v___f_2841_);
lean_ctor_set(v___x_2844_, 2, v___f_2840_);
lean_ctor_set(v___x_2844_, 3, v___f_2835_);
lean_ctor_set(v___x_2844_, 4, v___f_2837_);
lean_ctor_set(v___x_2844_, 5, v___f_2838_);
lean_ctor_set(v___x_2844_, 6, v___x_2842_);
lean_ctor_set(v___x_2844_, 7, v___x_2843_);
v___x_2845_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2845_, 0, v___x_2844_);
lean_ctor_set(v___x_2845_, 1, v___f_2839_);
v___x_2846_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_2845_);
if (lean_obj_tag(v___x_2846_) == 0)
{
lean_object* v_a_2847_; lean_object* v___f_2848_; lean_object* v___f_2849_; lean_object* v___x_2850_; lean_object* v___x_2851_; 
v_a_2847_ = lean_ctor_get(v___x_2846_, 0);
lean_inc_n(v_a_2847_, 2);
lean_dec_ref(v___x_2846_);
lean_inc_n(v_name_2834_, 2);
v___f_2848_ = lean_alloc_closure((void*)(l_Lean_registerTagAttribute___lam__6___boxed), 5, 1);
lean_closure_set(v___f_2848_, 0, v_name_2834_);
v___f_2849_ = lean_alloc_closure((void*)(l_Lean_registerParametricAttribute___redArg___lam__7___boxed), 10, 4);
lean_closure_set(v___f_2849_, 0, v_getParam_2830_);
lean_closure_set(v___f_2849_, 1, v_a_2847_);
lean_closure_set(v___f_2849_, 2, v_afterSet_2831_);
lean_closure_set(v___f_2849_, 3, v_name_2834_);
v___x_2850_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2850_, 0, v_toAttributeImplCore_2829_);
lean_ctor_set(v___x_2850_, 1, v___f_2849_);
lean_ctor_set(v___x_2850_, 2, v___f_2848_);
lean_inc_ref(v___x_2850_);
v___x_2851_ = l_Lean_registerBuiltinAttribute(v___x_2850_);
if (lean_obj_tag(v___x_2851_) == 0)
{
lean_object* v___x_2853_; uint8_t v_isShared_2854_; uint8_t v_isSharedCheck_2859_; 
v_isSharedCheck_2859_ = !lean_is_exclusive(v___x_2851_);
if (v_isSharedCheck_2859_ == 0)
{
lean_object* v_unused_2860_; 
v_unused_2860_ = lean_ctor_get(v___x_2851_, 0);
lean_dec(v_unused_2860_);
v___x_2853_ = v___x_2851_;
v_isShared_2854_ = v_isSharedCheck_2859_;
goto v_resetjp_2852_;
}
else
{
lean_dec(v___x_2851_);
v___x_2853_ = lean_box(0);
v_isShared_2854_ = v_isSharedCheck_2859_;
goto v_resetjp_2852_;
}
v_resetjp_2852_:
{
lean_object* v___x_2855_; lean_object* v___x_2857_; 
v___x_2855_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2855_, 0, v___x_2850_);
lean_ctor_set(v___x_2855_, 1, v_a_2847_);
lean_ctor_set_uint8(v___x_2855_, sizeof(void*)*2, v_preserveOrder_2832_);
if (v_isShared_2854_ == 0)
{
lean_ctor_set(v___x_2853_, 0, v___x_2855_);
v___x_2857_ = v___x_2853_;
goto v_reusejp_2856_;
}
else
{
lean_object* v_reuseFailAlloc_2858_; 
v_reuseFailAlloc_2858_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2858_, 0, v___x_2855_);
v___x_2857_ = v_reuseFailAlloc_2858_;
goto v_reusejp_2856_;
}
v_reusejp_2856_:
{
return v___x_2857_;
}
}
}
else
{
lean_object* v_a_2861_; lean_object* v___x_2863_; uint8_t v_isShared_2864_; uint8_t v_isSharedCheck_2868_; 
lean_dec_ref(v___x_2850_);
lean_dec(v_a_2847_);
v_a_2861_ = lean_ctor_get(v___x_2851_, 0);
v_isSharedCheck_2868_ = !lean_is_exclusive(v___x_2851_);
if (v_isSharedCheck_2868_ == 0)
{
v___x_2863_ = v___x_2851_;
v_isShared_2864_ = v_isSharedCheck_2868_;
goto v_resetjp_2862_;
}
else
{
lean_inc(v_a_2861_);
lean_dec(v___x_2851_);
v___x_2863_ = lean_box(0);
v_isShared_2864_ = v_isSharedCheck_2868_;
goto v_resetjp_2862_;
}
v_resetjp_2862_:
{
lean_object* v___x_2866_; 
if (v_isShared_2864_ == 0)
{
v___x_2866_ = v___x_2863_;
goto v_reusejp_2865_;
}
else
{
lean_object* v_reuseFailAlloc_2867_; 
v_reuseFailAlloc_2867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2867_, 0, v_a_2861_);
v___x_2866_ = v_reuseFailAlloc_2867_;
goto v_reusejp_2865_;
}
v_reusejp_2865_:
{
return v___x_2866_;
}
}
}
}
else
{
lean_object* v_a_2869_; lean_object* v___x_2871_; uint8_t v_isShared_2872_; uint8_t v_isSharedCheck_2876_; 
lean_dec_ref(v_afterSet_2831_);
lean_dec_ref(v_getParam_2830_);
lean_dec_ref(v_toAttributeImplCore_2829_);
v_a_2869_ = lean_ctor_get(v___x_2846_, 0);
v_isSharedCheck_2876_ = !lean_is_exclusive(v___x_2846_);
if (v_isSharedCheck_2876_ == 0)
{
v___x_2871_ = v___x_2846_;
v_isShared_2872_ = v_isSharedCheck_2876_;
goto v_resetjp_2870_;
}
else
{
lean_inc(v_a_2869_);
lean_dec(v___x_2846_);
v___x_2871_ = lean_box(0);
v_isShared_2872_ = v_isSharedCheck_2876_;
goto v_resetjp_2870_;
}
v_resetjp_2870_:
{
lean_object* v___x_2874_; 
if (v_isShared_2872_ == 0)
{
v___x_2874_ = v___x_2871_;
goto v_reusejp_2873_;
}
else
{
lean_object* v_reuseFailAlloc_2875_; 
v_reuseFailAlloc_2875_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2875_, 0, v_a_2869_);
v___x_2874_ = v_reuseFailAlloc_2875_;
goto v_reusejp_2873_;
}
v_reusejp_2873_:
{
return v___x_2874_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___boxed(lean_object* v_impl_2877_, lean_object* v_a_2878_){
_start:
{
lean_object* v_res_2879_; 
v_res_2879_ = l_Lean_registerParametricAttribute___redArg(v_impl_2877_);
return v_res_2879_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute(lean_object* v_00_u03b1_2880_, lean_object* v_impl_2881_){
_start:
{
lean_object* v___x_2883_; 
v___x_2883_ = l_Lean_registerParametricAttribute___redArg(v_impl_2881_);
return v___x_2883_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___boxed(lean_object* v_00_u03b1_2884_, lean_object* v_impl_2885_, lean_object* v_a_2886_){
_start:
{
lean_object* v_res_2887_; 
v_res_2887_ = l_Lean_registerParametricAttribute(v_00_u03b1_2884_, v_impl_2885_);
return v_res_2887_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttribute_spec__0(lean_object* v_00_u03b1_2888_, lean_object* v_impl_2889_, lean_object* v_env_2890_, lean_object* v_as_2891_, size_t v_i_2892_, size_t v_stop_2893_, lean_object* v_b_2894_){
_start:
{
lean_object* v___x_2895_; 
v___x_2895_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttribute_spec__0___redArg(v_impl_2889_, v_env_2890_, v_as_2891_, v_i_2892_, v_stop_2893_, v_b_2894_);
return v___x_2895_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttribute_spec__0___boxed(lean_object* v_00_u03b1_2896_, lean_object* v_impl_2897_, lean_object* v_env_2898_, lean_object* v_as_2899_, lean_object* v_i_2900_, lean_object* v_stop_2901_, lean_object* v_b_2902_){
_start:
{
size_t v_i_boxed_2903_; size_t v_stop_boxed_2904_; lean_object* v_res_2905_; 
v_i_boxed_2903_ = lean_unbox_usize(v_i_2900_);
lean_dec(v_i_2900_);
v_stop_boxed_2904_ = lean_unbox_usize(v_stop_2901_);
lean_dec(v_stop_2901_);
v_res_2905_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttribute_spec__0(v_00_u03b1_2896_, v_impl_2897_, v_env_2898_, v_as_2899_, v_i_boxed_2903_, v_stop_boxed_2904_, v_b_2902_);
lean_dec_ref(v_as_2899_);
return v_res_2905_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1___redArg(lean_object* v_init_2906_, lean_object* v_t_2907_){
_start:
{
lean_object* v___x_2908_; 
v___x_2908_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1_spec__1___redArg(v_init_2906_, v_t_2907_);
return v___x_2908_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1___redArg___boxed(lean_object* v_init_2909_, lean_object* v_t_2910_){
_start:
{
lean_object* v_res_2911_; 
v_res_2911_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1___redArg(v_init_2909_, v_t_2910_);
lean_dec(v_t_2910_);
return v_res_2911_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1(lean_object* v_00_u03b1_2912_, lean_object* v_init_2913_, lean_object* v_t_2914_){
_start:
{
lean_object* v___x_2915_; 
v___x_2915_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1_spec__1___redArg(v_init_2913_, v_t_2914_);
return v___x_2915_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1___boxed(lean_object* v_00_u03b1_2916_, lean_object* v_init_2917_, lean_object* v_t_2918_){
_start:
{
lean_object* v_res_2919_; 
v_res_2919_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1(v_00_u03b1_2916_, v_init_2917_, v_t_2918_);
lean_dec(v_t_2918_);
return v_res_2919_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2(lean_object* v_00_u03b1_2920_, lean_object* v_n_2921_, lean_object* v_as_2922_, lean_object* v_lo_2923_, lean_object* v_hi_2924_, lean_object* v_w_2925_, lean_object* v_hlo_2926_, lean_object* v_hhi_2927_){
_start:
{
lean_object* v___x_2928_; 
v___x_2928_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2___redArg(v_n_2921_, v_as_2922_, v_lo_2923_, v_hi_2924_);
return v___x_2928_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2___boxed(lean_object* v_00_u03b1_2929_, lean_object* v_n_2930_, lean_object* v_as_2931_, lean_object* v_lo_2932_, lean_object* v_hi_2933_, lean_object* v_w_2934_, lean_object* v_hlo_2935_, lean_object* v_hhi_2936_){
_start:
{
lean_object* v_res_2937_; 
v_res_2937_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2(v_00_u03b1_2929_, v_n_2930_, v_as_2931_, v_lo_2932_, v_hi_2933_, v_w_2934_, v_hlo_2935_, v_hhi_2936_);
lean_dec(v_hi_2933_);
lean_dec(v_n_2930_);
return v_res_2937_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3(lean_object* v_00_u03b1_2938_, lean_object* v_snd_2939_, lean_object* v_as_2940_, lean_object* v_start_2941_, lean_object* v_stop_2942_){
_start:
{
lean_object* v___x_2943_; 
v___x_2943_ = l_Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3___redArg(v_snd_2939_, v_as_2940_, v_start_2941_, v_stop_2942_);
return v___x_2943_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3___boxed(lean_object* v_00_u03b1_2944_, lean_object* v_snd_2945_, lean_object* v_as_2946_, lean_object* v_start_2947_, lean_object* v_stop_2948_){
_start:
{
lean_object* v_res_2949_; 
v_res_2949_ = l_Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3(v_00_u03b1_2944_, v_snd_2945_, v_as_2946_, v_start_2947_, v_stop_2948_);
lean_dec(v_stop_2948_);
lean_dec(v_start_2947_);
lean_dec_ref(v_as_2946_);
lean_dec(v_snd_2945_);
return v_res_2949_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1_spec__1(lean_object* v_00_u03b1_2950_, lean_object* v_init_2951_, lean_object* v_x_2952_){
_start:
{
lean_object* v___x_2953_; 
v___x_2953_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1_spec__1___redArg(v_init_2951_, v_x_2952_);
return v___x_2953_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1_spec__1___boxed(lean_object* v_00_u03b1_2954_, lean_object* v_init_2955_, lean_object* v_x_2956_){
_start:
{
lean_object* v_res_2957_; 
v_res_2957_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1_spec__1(v_00_u03b1_2954_, v_init_2955_, v_x_2956_);
lean_dec(v_x_2956_);
return v_res_2957_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2_spec__3(lean_object* v_00_u03b1_2958_, lean_object* v_n_2959_, lean_object* v_lo_2960_, lean_object* v_hi_2961_, lean_object* v_hhi_2962_, lean_object* v_pivot_2963_, lean_object* v_as_2964_, lean_object* v_i_2965_, lean_object* v_k_2966_, lean_object* v_ilo_2967_, lean_object* v_ik_2968_, lean_object* v_w_2969_){
_start:
{
lean_object* v___x_2970_; 
v___x_2970_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2_spec__3___redArg(v_hi_2961_, v_pivot_2963_, v_as_2964_, v_i_2965_, v_k_2966_);
return v___x_2970_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2_spec__3___boxed(lean_object* v_00_u03b1_2971_, lean_object* v_n_2972_, lean_object* v_lo_2973_, lean_object* v_hi_2974_, lean_object* v_hhi_2975_, lean_object* v_pivot_2976_, lean_object* v_as_2977_, lean_object* v_i_2978_, lean_object* v_k_2979_, lean_object* v_ilo_2980_, lean_object* v_ik_2981_, lean_object* v_w_2982_){
_start:
{
lean_object* v_res_2983_; 
v_res_2983_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2_spec__3(v_00_u03b1_2971_, v_n_2972_, v_lo_2973_, v_hi_2974_, v_hhi_2975_, v_pivot_2976_, v_as_2977_, v_i_2978_, v_k_2979_, v_ilo_2980_, v_ik_2981_, v_w_2982_);
lean_dec_ref(v_pivot_2976_);
lean_dec(v_hi_2974_);
lean_dec(v_lo_2973_);
lean_dec(v_n_2972_);
return v_res_2983_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3_spec__5(lean_object* v_00_u03b1_2984_, lean_object* v_snd_2985_, lean_object* v_as_2986_, size_t v_i_2987_, size_t v_stop_2988_, lean_object* v_b_2989_){
_start:
{
lean_object* v___x_2990_; 
v___x_2990_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3_spec__5___redArg(v_snd_2985_, v_as_2986_, v_i_2987_, v_stop_2988_, v_b_2989_);
return v___x_2990_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3_spec__5___boxed(lean_object* v_00_u03b1_2991_, lean_object* v_snd_2992_, lean_object* v_as_2993_, lean_object* v_i_2994_, lean_object* v_stop_2995_, lean_object* v_b_2996_){
_start:
{
size_t v_i_boxed_2997_; size_t v_stop_boxed_2998_; lean_object* v_res_2999_; 
v_i_boxed_2997_ = lean_unbox_usize(v_i_2994_);
lean_dec(v_i_2994_);
v_stop_boxed_2998_ = lean_unbox_usize(v_stop_2995_);
lean_dec(v_stop_2995_);
v_res_2999_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3_spec__5(v_00_u03b1_2991_, v_snd_2992_, v_as_2993_, v_i_boxed_2997_, v_stop_boxed_2998_, v_b_2996_);
lean_dec_ref(v_as_2993_);
lean_dec(v_snd_2992_);
return v_res_2999_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParam_x3f___redArg___lam__1(lean_object* v_decl_3000_, lean_object* v___x_3001_, lean_object* v___x_3002_, lean_object* v_a_3003_, lean_object* v_x_3004_, lean_object* v___y_3005_){
_start:
{
lean_object* v_fst_3006_; uint8_t v___x_3007_; 
v_fst_3006_ = lean_ctor_get(v_a_3003_, 0);
v___x_3007_ = lean_name_eq(v_fst_3006_, v_decl_3000_);
if (v___x_3007_ == 0)
{
lean_object* v___x_3008_; 
lean_dec_ref(v_a_3003_);
v___x_3008_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3008_, 0, v___x_3001_);
return v___x_3008_;
}
else
{
lean_object* v___x_3009_; lean_object* v___x_3010_; lean_object* v___x_3011_; lean_object* v___x_3012_; 
lean_dec_ref(v___x_3001_);
v___x_3009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3009_, 0, v_a_3003_);
v___x_3010_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3010_, 0, v___x_3009_);
v___x_3011_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3011_, 0, v___x_3010_);
lean_ctor_set(v___x_3011_, 1, v___x_3002_);
v___x_3012_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3012_, 0, v___x_3011_);
return v___x_3012_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParam_x3f___redArg___lam__1___boxed(lean_object* v_decl_3013_, lean_object* v___x_3014_, lean_object* v___x_3015_, lean_object* v_a_3016_, lean_object* v_x_3017_, lean_object* v___y_3018_){
_start:
{
lean_object* v_res_3019_; 
v_res_3019_ = l_Lean_ParametricAttribute_getParam_x3f___redArg___lam__1(v_decl_3013_, v___x_3014_, v___x_3015_, v_a_3016_, v_x_3017_, v___y_3018_);
lean_dec_ref(v___y_3018_);
lean_dec(v_decl_3013_);
return v_res_3019_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParam_x3f___redArg(lean_object* v_inst_3047_, lean_object* v_attr_3048_, lean_object* v_env_3049_, lean_object* v_decl_3050_){
_start:
{
lean_object* v___y_3052_; lean_object* v___x_3063_; lean_object* v___x_3064_; 
v___x_3063_ = ((lean_object*)(l_Lean_ParametricAttribute_getParam_x3f___redArg___closed__0));
v___x_3064_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3049_, v_decl_3050_);
if (lean_obj_tag(v___x_3064_) == 0)
{
lean_object* v_ext_3065_; lean_object* v_toEnvExtension_3066_; lean_object* v_asyncMode_3067_; lean_object* v___x_3068_; lean_object* v___x_3069_; lean_object* v_snd_3070_; lean_object* v___x_3071_; 
lean_dec(v_inst_3047_);
v_ext_3065_ = lean_ctor_get(v_attr_3048_, 1);
v_toEnvExtension_3066_ = lean_ctor_get(v_ext_3065_, 0);
v_asyncMode_3067_ = lean_ctor_get(v_toEnvExtension_3066_, 2);
v___x_3068_ = lean_box(0);
v___x_3069_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3063_, v_ext_3065_, v_env_3049_, v_asyncMode_3067_, v___x_3068_);
v_snd_3070_ = lean_ctor_get(v___x_3069_, 1);
lean_inc(v_snd_3070_);
lean_dec(v___x_3069_);
v___x_3071_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_snd_3070_, v_decl_3050_);
lean_dec(v_decl_3050_);
lean_dec(v_snd_3070_);
return v___x_3071_;
}
else
{
uint8_t v_preserveOrder_3072_; 
v_preserveOrder_3072_ = lean_ctor_get_uint8(v_attr_3048_, sizeof(void*)*2);
if (v_preserveOrder_3072_ == 0)
{
lean_object* v_val_3073_; lean_object* v_ext_3074_; uint8_t v___x_3075_; lean_object* v___x_3076_; lean_object* v___x_3077_; lean_object* v___x_3078_; uint8_t v___x_3079_; 
v_val_3073_ = lean_ctor_get(v___x_3064_, 0);
lean_inc(v_val_3073_);
lean_dec_ref(v___x_3064_);
v_ext_3074_ = lean_ctor_get(v_attr_3048_, 1);
v___x_3075_ = 0;
v___x_3076_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_3063_, v_ext_3074_, v_env_3049_, v_val_3073_, v___x_3075_);
lean_dec(v_val_3073_);
lean_dec_ref(v_env_3049_);
v___x_3077_ = lean_unsigned_to_nat(0u);
v___x_3078_ = lean_array_get_size(v___x_3076_);
v___x_3079_ = lean_nat_dec_lt(v___x_3077_, v___x_3078_);
if (v___x_3079_ == 0)
{
lean_object* v___x_3080_; 
lean_dec_ref(v___x_3076_);
lean_dec(v_decl_3050_);
lean_dec(v_inst_3047_);
v___x_3080_ = lean_box(0);
return v___x_3080_;
}
else
{
lean_object* v___x_3081_; lean_object* v___x_3082_; uint8_t v___x_3083_; 
v___x_3081_ = lean_unsigned_to_nat(1u);
v___x_3082_ = lean_nat_sub(v___x_3078_, v___x_3081_);
v___x_3083_ = lean_nat_dec_le(v___x_3077_, v___x_3082_);
if (v___x_3083_ == 0)
{
lean_object* v___x_3084_; 
lean_dec(v___x_3082_);
lean_dec_ref(v___x_3076_);
lean_dec(v_decl_3050_);
lean_dec(v_inst_3047_);
v___x_3084_ = lean_box(0);
return v___x_3084_;
}
else
{
lean_object* v___f_3085_; lean_object* v___x_3086_; lean_object* v___x_3087_; lean_object* v___x_3088_; 
v___f_3085_ = ((lean_object*)(l_Lean_ParametricAttribute_getParam_x3f___redArg___closed__1));
v___x_3086_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3086_, 0, v_decl_3050_);
lean_ctor_set(v___x_3086_, 1, v_inst_3047_);
v___x_3087_ = ((lean_object*)(l_Lean_ParametricAttribute_getParam_x3f___redArg___closed__2));
v___x_3088_ = l_Array_binSearchAux___redArg(v___f_3085_, v___x_3087_, v___x_3076_, v___x_3086_, v___x_3077_, v___x_3082_);
lean_dec_ref(v___x_3076_);
v___y_3052_ = v___x_3088_;
goto v___jp_3051_;
}
}
}
else
{
lean_object* v_val_3089_; lean_object* v_ext_3090_; uint8_t v___x_3091_; lean_object* v___x_3092_; lean_object* v___x_3093_; lean_object* v___x_3094_; lean_object* v___x_3095_; lean_object* v___x_3096_; lean_object* v___f_3097_; size_t v_sz_3098_; size_t v___x_3099_; lean_object* v___x_3100_; lean_object* v_fst_3101_; 
lean_dec(v_inst_3047_);
v_val_3089_ = lean_ctor_get(v___x_3064_, 0);
lean_inc(v_val_3089_);
lean_dec_ref(v___x_3064_);
v_ext_3090_ = lean_ctor_get(v_attr_3048_, 1);
v___x_3091_ = 0;
v___x_3092_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_3063_, v_ext_3090_, v_env_3049_, v_val_3089_, v___x_3091_);
lean_dec(v_val_3089_);
lean_dec_ref(v_env_3049_);
v___x_3093_ = ((lean_object*)(l_Lean_ParametricAttribute_getParam_x3f___redArg___closed__12));
v___x_3094_ = lean_box(0);
v___x_3095_ = lean_box(0);
v___x_3096_ = ((lean_object*)(l_Lean_ParametricAttribute_getParam_x3f___redArg___closed__13));
v___f_3097_ = lean_alloc_closure((void*)(l_Lean_ParametricAttribute_getParam_x3f___redArg___lam__1___boxed), 6, 3);
lean_closure_set(v___f_3097_, 0, v_decl_3050_);
lean_closure_set(v___f_3097_, 1, v___x_3096_);
lean_closure_set(v___f_3097_, 2, v___x_3095_);
v_sz_3098_ = lean_array_size(v___x_3092_);
v___x_3099_ = ((size_t)0ULL);
v___x_3100_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_3093_, v___x_3092_, v___f_3097_, v_sz_3098_, v___x_3099_, v___x_3096_);
v_fst_3101_ = lean_ctor_get(v___x_3100_, 0);
lean_inc(v_fst_3101_);
lean_dec(v___x_3100_);
if (lean_obj_tag(v_fst_3101_) == 0)
{
return v___x_3094_;
}
else
{
lean_object* v_val_3102_; 
v_val_3102_ = lean_ctor_get(v_fst_3101_, 0);
lean_inc(v_val_3102_);
lean_dec_ref(v_fst_3101_);
v___y_3052_ = v_val_3102_;
goto v___jp_3051_;
}
}
}
v___jp_3051_:
{
if (lean_obj_tag(v___y_3052_) == 0)
{
lean_object* v___x_3053_; 
v___x_3053_ = lean_box(0);
return v___x_3053_;
}
else
{
lean_object* v_val_3054_; lean_object* v___x_3056_; uint8_t v_isShared_3057_; uint8_t v_isSharedCheck_3062_; 
v_val_3054_ = lean_ctor_get(v___y_3052_, 0);
v_isSharedCheck_3062_ = !lean_is_exclusive(v___y_3052_);
if (v_isSharedCheck_3062_ == 0)
{
v___x_3056_ = v___y_3052_;
v_isShared_3057_ = v_isSharedCheck_3062_;
goto v_resetjp_3055_;
}
else
{
lean_inc(v_val_3054_);
lean_dec(v___y_3052_);
v___x_3056_ = lean_box(0);
v_isShared_3057_ = v_isSharedCheck_3062_;
goto v_resetjp_3055_;
}
v_resetjp_3055_:
{
lean_object* v_snd_3058_; lean_object* v___x_3060_; 
v_snd_3058_ = lean_ctor_get(v_val_3054_, 1);
lean_inc(v_snd_3058_);
lean_dec(v_val_3054_);
if (v_isShared_3057_ == 0)
{
lean_ctor_set(v___x_3056_, 0, v_snd_3058_);
v___x_3060_ = v___x_3056_;
goto v_reusejp_3059_;
}
else
{
lean_object* v_reuseFailAlloc_3061_; 
v_reuseFailAlloc_3061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3061_, 0, v_snd_3058_);
v___x_3060_ = v_reuseFailAlloc_3061_;
goto v_reusejp_3059_;
}
v_reusejp_3059_:
{
return v___x_3060_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParam_x3f___redArg___boxed(lean_object* v_inst_3103_, lean_object* v_attr_3104_, lean_object* v_env_3105_, lean_object* v_decl_3106_){
_start:
{
lean_object* v_res_3107_; 
v_res_3107_ = l_Lean_ParametricAttribute_getParam_x3f___redArg(v_inst_3103_, v_attr_3104_, v_env_3105_, v_decl_3106_);
lean_dec_ref(v_attr_3104_);
return v_res_3107_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParam_x3f(lean_object* v_00_u03b1_3108_, lean_object* v_inst_3109_, lean_object* v_attr_3110_, lean_object* v_env_3111_, lean_object* v_decl_3112_){
_start:
{
lean_object* v___x_3113_; 
v___x_3113_ = l_Lean_ParametricAttribute_getParam_x3f___redArg(v_inst_3109_, v_attr_3110_, v_env_3111_, v_decl_3112_);
return v___x_3113_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParam_x3f___boxed(lean_object* v_00_u03b1_3114_, lean_object* v_inst_3115_, lean_object* v_attr_3116_, lean_object* v_env_3117_, lean_object* v_decl_3118_){
_start:
{
lean_object* v_res_3119_; 
v_res_3119_ = l_Lean_ParametricAttribute_getParam_x3f(v_00_u03b1_3114_, v_inst_3115_, v_attr_3116_, v_env_3117_, v_decl_3118_);
lean_dec_ref(v_attr_3116_);
return v_res_3119_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_setParam___redArg(lean_object* v_attr_3124_, lean_object* v_env_3125_, lean_object* v_decl_3126_, lean_object* v_param_3127_){
_start:
{
lean_object* v___x_3128_; 
v___x_3128_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3125_, v_decl_3126_);
if (lean_obj_tag(v___x_3128_) == 0)
{
lean_object* v_ext_3129_; lean_object* v_toEnvExtension_3130_; lean_object* v_attr_3131_; lean_object* v_asyncMode_3132_; lean_object* v___x_3133_; lean_object* v___x_3134_; lean_object* v___x_3135_; lean_object* v_snd_3136_; lean_object* v___x_3138_; uint8_t v_isShared_3139_; uint8_t v_isSharedCheck_3166_; 
v_ext_3129_ = lean_ctor_get(v_attr_3124_, 1);
lean_inc_ref(v_ext_3129_);
v_toEnvExtension_3130_ = lean_ctor_get(v_ext_3129_, 0);
v_attr_3131_ = lean_ctor_get(v_attr_3124_, 0);
lean_inc_ref(v_attr_3131_);
lean_dec_ref(v_attr_3124_);
v_asyncMode_3132_ = lean_ctor_get(v_toEnvExtension_3130_, 2);
lean_inc(v_asyncMode_3132_);
v___x_3133_ = ((lean_object*)(l_Lean_ParametricAttribute_getParam_x3f___redArg___closed__0));
v___x_3134_ = lean_box(0);
lean_inc_ref(v_env_3125_);
v___x_3135_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3133_, v_ext_3129_, v_env_3125_, v_asyncMode_3132_, v___x_3134_);
v_snd_3136_ = lean_ctor_get(v___x_3135_, 1);
v_isSharedCheck_3166_ = !lean_is_exclusive(v___x_3135_);
if (v_isSharedCheck_3166_ == 0)
{
lean_object* v_unused_3167_; 
v_unused_3167_ = lean_ctor_get(v___x_3135_, 0);
lean_dec(v_unused_3167_);
v___x_3138_ = v___x_3135_;
v_isShared_3139_ = v_isSharedCheck_3166_;
goto v_resetjp_3137_;
}
else
{
lean_inc(v_snd_3136_);
lean_dec(v___x_3135_);
v___x_3138_ = lean_box(0);
v_isShared_3139_ = v_isSharedCheck_3166_;
goto v_resetjp_3137_;
}
v_resetjp_3137_:
{
lean_object* v___x_3140_; 
v___x_3140_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_snd_3136_, v_decl_3126_);
lean_dec(v_snd_3136_);
if (lean_obj_tag(v___x_3140_) == 0)
{
lean_object* v___x_3142_; 
lean_dec_ref(v_attr_3131_);
if (v_isShared_3139_ == 0)
{
lean_ctor_set(v___x_3138_, 1, v_param_3127_);
lean_ctor_set(v___x_3138_, 0, v_decl_3126_);
v___x_3142_ = v___x_3138_;
goto v_reusejp_3141_;
}
else
{
lean_object* v_reuseFailAlloc_3145_; 
v_reuseFailAlloc_3145_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3145_, 0, v_decl_3126_);
lean_ctor_set(v_reuseFailAlloc_3145_, 1, v_param_3127_);
v___x_3142_ = v_reuseFailAlloc_3145_;
goto v_reusejp_3141_;
}
v_reusejp_3141_:
{
lean_object* v___x_3143_; lean_object* v___x_3144_; 
v___x_3143_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_ext_3129_, v_env_3125_, v___x_3142_, v_asyncMode_3132_, v___x_3134_);
lean_dec(v_asyncMode_3132_);
v___x_3144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3144_, 0, v___x_3143_);
return v___x_3144_;
}
}
else
{
lean_object* v___x_3147_; uint8_t v_isShared_3148_; uint8_t v_isSharedCheck_3164_; 
lean_del_object(v___x_3138_);
lean_dec(v_asyncMode_3132_);
lean_dec_ref(v_ext_3129_);
lean_dec(v_param_3127_);
lean_dec_ref(v_env_3125_);
v_isSharedCheck_3164_ = !lean_is_exclusive(v___x_3140_);
if (v_isSharedCheck_3164_ == 0)
{
lean_object* v_unused_3165_; 
v_unused_3165_ = lean_ctor_get(v___x_3140_, 0);
lean_dec(v_unused_3165_);
v___x_3147_ = v___x_3140_;
v_isShared_3148_ = v_isSharedCheck_3164_;
goto v_resetjp_3146_;
}
else
{
lean_dec(v___x_3140_);
v___x_3147_ = lean_box(0);
v_isShared_3148_ = v_isSharedCheck_3164_;
goto v_resetjp_3146_;
}
v_resetjp_3146_:
{
lean_object* v_toAttributeImplCore_3149_; lean_object* v_name_3150_; uint8_t v___x_3151_; lean_object* v___x_3152_; lean_object* v___x_3153_; lean_object* v___x_3154_; lean_object* v___x_3155_; lean_object* v___x_3156_; lean_object* v___x_3157_; lean_object* v___x_3158_; lean_object* v___x_3159_; lean_object* v___x_3160_; lean_object* v___x_3162_; 
v_toAttributeImplCore_3149_ = lean_ctor_get(v_attr_3131_, 0);
lean_inc_ref(v_toAttributeImplCore_3149_);
lean_dec_ref(v_attr_3131_);
v_name_3150_ = lean_ctor_get(v_toAttributeImplCore_3149_, 1);
lean_inc(v_name_3150_);
lean_dec_ref(v_toAttributeImplCore_3149_);
v___x_3151_ = 1;
v___x_3152_ = ((lean_object*)(l_Lean_ParametricAttribute_setParam___redArg___closed__0));
v___x_3153_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_3150_, v___x_3151_);
v___x_3154_ = lean_string_append(v___x_3152_, v___x_3153_);
lean_dec_ref(v___x_3153_);
v___x_3155_ = ((lean_object*)(l_Lean_ParametricAttribute_setParam___redArg___closed__1));
v___x_3156_ = lean_string_append(v___x_3154_, v___x_3155_);
v___x_3157_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_decl_3126_, v___x_3151_);
v___x_3158_ = lean_string_append(v___x_3156_, v___x_3157_);
lean_dec_ref(v___x_3157_);
v___x_3159_ = ((lean_object*)(l_Lean_ParametricAttribute_setParam___redArg___closed__2));
v___x_3160_ = lean_string_append(v___x_3158_, v___x_3159_);
if (v_isShared_3148_ == 0)
{
lean_ctor_set_tag(v___x_3147_, 0);
lean_ctor_set(v___x_3147_, 0, v___x_3160_);
v___x_3162_ = v___x_3147_;
goto v_reusejp_3161_;
}
else
{
lean_object* v_reuseFailAlloc_3163_; 
v_reuseFailAlloc_3163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3163_, 0, v___x_3160_);
v___x_3162_ = v_reuseFailAlloc_3163_;
goto v_reusejp_3161_;
}
v_reusejp_3161_:
{
return v___x_3162_;
}
}
}
}
}
else
{
lean_object* v___x_3169_; uint8_t v_isShared_3170_; uint8_t v_isSharedCheck_3187_; 
lean_dec(v_param_3127_);
lean_dec_ref(v_env_3125_);
v_isSharedCheck_3187_ = !lean_is_exclusive(v___x_3128_);
if (v_isSharedCheck_3187_ == 0)
{
lean_object* v_unused_3188_; 
v_unused_3188_ = lean_ctor_get(v___x_3128_, 0);
lean_dec(v_unused_3188_);
v___x_3169_ = v___x_3128_;
v_isShared_3170_ = v_isSharedCheck_3187_;
goto v_resetjp_3168_;
}
else
{
lean_dec(v___x_3128_);
v___x_3169_ = lean_box(0);
v_isShared_3170_ = v_isSharedCheck_3187_;
goto v_resetjp_3168_;
}
v_resetjp_3168_:
{
lean_object* v_attr_3171_; lean_object* v_toAttributeImplCore_3172_; lean_object* v_name_3173_; uint8_t v___x_3174_; lean_object* v___x_3175_; lean_object* v___x_3176_; lean_object* v___x_3177_; lean_object* v___x_3178_; lean_object* v___x_3179_; lean_object* v___x_3180_; lean_object* v___x_3181_; lean_object* v___x_3182_; lean_object* v___x_3183_; lean_object* v___x_3185_; 
v_attr_3171_ = lean_ctor_get(v_attr_3124_, 0);
lean_inc_ref(v_attr_3171_);
lean_dec_ref(v_attr_3124_);
v_toAttributeImplCore_3172_ = lean_ctor_get(v_attr_3171_, 0);
lean_inc_ref(v_toAttributeImplCore_3172_);
lean_dec_ref(v_attr_3171_);
v_name_3173_ = lean_ctor_get(v_toAttributeImplCore_3172_, 1);
lean_inc(v_name_3173_);
lean_dec_ref(v_toAttributeImplCore_3172_);
v___x_3174_ = 1;
v___x_3175_ = ((lean_object*)(l_Lean_ParametricAttribute_setParam___redArg___closed__0));
v___x_3176_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_3173_, v___x_3174_);
v___x_3177_ = lean_string_append(v___x_3175_, v___x_3176_);
lean_dec_ref(v___x_3176_);
v___x_3178_ = ((lean_object*)(l_Lean_ParametricAttribute_setParam___redArg___closed__1));
v___x_3179_ = lean_string_append(v___x_3177_, v___x_3178_);
v___x_3180_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_decl_3126_, v___x_3174_);
v___x_3181_ = lean_string_append(v___x_3179_, v___x_3180_);
lean_dec_ref(v___x_3180_);
v___x_3182_ = ((lean_object*)(l_Lean_ParametricAttribute_setParam___redArg___closed__3));
v___x_3183_ = lean_string_append(v___x_3181_, v___x_3182_);
if (v_isShared_3170_ == 0)
{
lean_ctor_set_tag(v___x_3169_, 0);
lean_ctor_set(v___x_3169_, 0, v___x_3183_);
v___x_3185_ = v___x_3169_;
goto v_reusejp_3184_;
}
else
{
lean_object* v_reuseFailAlloc_3186_; 
v_reuseFailAlloc_3186_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3186_, 0, v___x_3183_);
v___x_3185_ = v_reuseFailAlloc_3186_;
goto v_reusejp_3184_;
}
v_reusejp_3184_:
{
return v___x_3185_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_setParam(lean_object* v_00_u03b1_3189_, lean_object* v_attr_3190_, lean_object* v_env_3191_, lean_object* v_decl_3192_, lean_object* v_param_3193_){
_start:
{
lean_object* v___x_3194_; 
v___x_3194_ = l_Lean_ParametricAttribute_setParam___redArg(v_attr_3190_, v_env_3191_, v_decl_3192_, v_param_3193_);
return v___x_3194_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___lam__0(lean_object* v_x_3195_, lean_object* v___y_3196_){
_start:
{
lean_object* v___x_3198_; lean_object* v___x_3199_; 
v___x_3198_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___lam__0___closed__1));
v___x_3199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3199_, 0, v___x_3198_);
return v___x_3199_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___lam__0___boxed(lean_object* v_x_3200_, lean_object* v___y_3201_, lean_object* v___y_3202_){
_start:
{
lean_object* v_res_3203_; 
v_res_3203_ = l_Lean_instInhabitedEnumAttributes_default___lam__0(v_x_3200_, v___y_3201_);
lean_dec_ref(v___y_3201_);
lean_dec_ref(v_x_3200_);
return v_res_3203_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___lam__1(lean_object* v_s_3204_, lean_object* v_x_3205_){
_start:
{
lean_inc(v_s_3204_);
return v_s_3204_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___lam__1___boxed(lean_object* v_s_3206_, lean_object* v_x_3207_){
_start:
{
lean_object* v_res_3208_; 
v_res_3208_ = l_Lean_instInhabitedEnumAttributes_default___lam__1(v_s_3206_, v_x_3207_);
lean_dec_ref(v_x_3207_);
lean_dec(v_s_3206_);
return v_res_3208_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___lam__2(lean_object* v_x_3209_, lean_object* v_x_3210_){
_start:
{
lean_object* v___x_3211_; 
v___x_3211_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___lam__2___closed__1));
return v___x_3211_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___lam__2___boxed(lean_object* v_x_3212_, lean_object* v_x_3213_){
_start:
{
lean_object* v_res_3214_; 
v_res_3214_ = l_Lean_instInhabitedEnumAttributes_default___lam__2(v_x_3212_, v_x_3213_);
lean_dec(v_x_3213_);
lean_dec_ref(v_x_3212_);
return v_res_3214_;
}
}
static lean_object* _init_l_Lean_instInhabitedEnumAttributes_default___closed__3(void){
_start:
{
lean_object* v___x_3218_; 
v___x_3218_ = l_Lean_instInhabitedEnvExtension_default(lean_box(0));
return v___x_3218_;
}
}
static lean_object* _init_l_Lean_instInhabitedEnumAttributes_default___closed__4(void){
_start:
{
lean_object* v___f_3219_; lean_object* v___f_3220_; lean_object* v___f_3221_; lean_object* v___f_3222_; lean_object* v___x_3223_; lean_object* v___x_3224_; lean_object* v___x_3225_; 
v___f_3219_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___closed__3));
v___f_3220_ = ((lean_object*)(l_Lean_instInhabitedEnumAttributes_default___closed__2));
v___f_3221_ = ((lean_object*)(l_Lean_instInhabitedEnumAttributes_default___closed__1));
v___f_3222_ = ((lean_object*)(l_Lean_instInhabitedEnumAttributes_default___closed__0));
v___x_3223_ = lean_box(0);
v___x_3224_ = lean_obj_once(&l_Lean_instInhabitedEnumAttributes_default___closed__3, &l_Lean_instInhabitedEnumAttributes_default___closed__3_once, _init_l_Lean_instInhabitedEnumAttributes_default___closed__3);
v___x_3225_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3225_, 0, v___x_3224_);
lean_ctor_set(v___x_3225_, 1, v___x_3223_);
lean_ctor_set(v___x_3225_, 2, v___f_3222_);
lean_ctor_set(v___x_3225_, 3, v___f_3221_);
lean_ctor_set(v___x_3225_, 4, v___f_3220_);
lean_ctor_set(v___x_3225_, 5, v___f_3219_);
return v___x_3225_;
}
}
static lean_object* _init_l_Lean_instInhabitedEnumAttributes_default___closed__5(void){
_start:
{
lean_object* v___x_3226_; lean_object* v___x_3227_; lean_object* v___x_3228_; 
v___x_3226_ = lean_obj_once(&l_Lean_instInhabitedEnumAttributes_default___closed__4, &l_Lean_instInhabitedEnumAttributes_default___closed__4_once, _init_l_Lean_instInhabitedEnumAttributes_default___closed__4);
v___x_3227_ = lean_box(0);
v___x_3228_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3228_, 0, v___x_3227_);
lean_ctor_set(v___x_3228_, 1, v___x_3226_);
return v___x_3228_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default(lean_object* v_00_u03b1_3229_){
_start:
{
lean_object* v___x_3230_; 
v___x_3230_ = lean_obj_once(&l_Lean_instInhabitedEnumAttributes_default___closed__5, &l_Lean_instInhabitedEnumAttributes_default___closed__5_once, _init_l_Lean_instInhabitedEnumAttributes_default___closed__5);
return v___x_3230_;
}
}
static lean_object* _init_l_Lean_instInhabitedEnumAttributes___closed__0(void){
_start:
{
lean_object* v___x_3231_; 
v___x_3231_ = l_Lean_instInhabitedEnumAttributes_default(lean_box(0));
return v___x_3231_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes(lean_object* v_a_3232_){
_start:
{
lean_object* v___x_3233_; 
v___x_3233_ = lean_obj_once(&l_Lean_instInhabitedEnumAttributes___closed__0, &l_Lean_instInhabitedEnumAttributes___closed__0_once, _init_l_Lean_instInhabitedEnumAttributes___closed__0);
return v___x_3233_;
}
}
static lean_object* _init_l_Lean_registerEnumAttributes___auto__1(void){
_start:
{
lean_object* v___x_3234_; 
v___x_3234_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__28, &l_Lean_AttributeImplCore_ref___autoParam___closed__28_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__28);
return v___x_3234_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__0(lean_object* v_x_3235_){
_start:
{
lean_object* v___x_3236_; 
v___x_3236_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___lam__2___closed__0));
return v___x_3236_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__0___boxed(lean_object* v_x_3237_){
_start:
{
lean_object* v_res_3238_; 
v_res_3238_ = l_Lean_registerEnumAttributes___redArg___lam__0(v_x_3237_);
lean_dec(v_x_3237_);
return v_res_3238_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___redArg(lean_object* v_newState_3239_, lean_object* v_x_3240_, lean_object* v_x_3241_){
_start:
{
if (lean_obj_tag(v_x_3241_) == 0)
{
return v_x_3240_;
}
else
{
lean_object* v_head_3242_; lean_object* v_tail_3243_; lean_object* v___x_3244_; 
v_head_3242_ = lean_ctor_get(v_x_3241_, 0);
lean_inc(v_head_3242_);
v_tail_3243_ = lean_ctor_get(v_x_3241_, 1);
lean_inc(v_tail_3243_);
lean_dec_ref(v_x_3241_);
v___x_3244_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_newState_3239_, v_head_3242_);
if (lean_obj_tag(v___x_3244_) == 1)
{
lean_object* v_val_3245_; lean_object* v___x_3246_; 
v_val_3245_ = lean_ctor_get(v___x_3244_, 0);
lean_inc(v_val_3245_);
lean_dec_ref(v___x_3244_);
v___x_3246_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_head_3242_, v_val_3245_, v_x_3240_);
v_x_3240_ = v___x_3246_;
v_x_3241_ = v_tail_3243_;
goto _start;
}
else
{
lean_dec(v___x_3244_);
lean_dec(v_head_3242_);
v_x_3241_ = v_tail_3243_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___redArg___boxed(lean_object* v_newState_3249_, lean_object* v_x_3250_, lean_object* v_x_3251_){
_start:
{
lean_object* v_res_3252_; 
v_res_3252_ = l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___redArg(v_newState_3249_, v_x_3250_, v_x_3251_);
lean_dec(v_newState_3249_);
return v_res_3252_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__1(lean_object* v_x_3253_, lean_object* v_newState_3254_, lean_object* v_consts_3255_, lean_object* v_st_3256_){
_start:
{
lean_object* v___x_3257_; 
v___x_3257_ = l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___redArg(v_newState_3254_, v_st_3256_, v_consts_3255_);
return v___x_3257_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__1___boxed(lean_object* v_x_3258_, lean_object* v_newState_3259_, lean_object* v_consts_3260_, lean_object* v_st_3261_){
_start:
{
lean_object* v_res_3262_; 
v_res_3262_ = l_Lean_registerEnumAttributes___redArg___lam__1(v_x_3258_, v_newState_3259_, v_consts_3260_, v_st_3261_);
lean_dec(v_newState_3259_);
lean_dec(v_x_3258_);
return v_res_3262_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__2(lean_object* v_s_3272_){
_start:
{
lean_object* v___x_3273_; lean_object* v___y_3275_; 
v___x_3273_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___lam__2___closed__3));
if (lean_obj_tag(v_s_3272_) == 0)
{
lean_object* v_size_3279_; 
v_size_3279_ = lean_ctor_get(v_s_3272_, 0);
lean_inc(v_size_3279_);
lean_dec_ref(v_s_3272_);
v___y_3275_ = v_size_3279_;
goto v___jp_3274_;
}
else
{
lean_object* v___x_3280_; 
v___x_3280_ = lean_unsigned_to_nat(0u);
v___y_3275_ = v___x_3280_;
goto v___jp_3274_;
}
v___jp_3274_:
{
lean_object* v___x_3276_; lean_object* v___x_3277_; lean_object* v___x_3278_; 
v___x_3276_ = l_Nat_reprFast(v___y_3275_);
v___x_3277_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3277_, 0, v___x_3276_);
v___x_3278_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3278_, 0, v___x_3273_);
lean_ctor_set(v___x_3278_, 1, v___x_3277_);
return v___x_3278_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg(lean_object* v_env_3281_, lean_object* v_as_3282_, size_t v_i_3283_, size_t v_stop_3284_, lean_object* v_b_3285_){
_start:
{
lean_object* v___y_3287_; uint8_t v___x_3291_; 
v___x_3291_ = lean_usize_dec_eq(v_i_3283_, v_stop_3284_);
if (v___x_3291_ == 0)
{
lean_object* v___x_3292_; lean_object* v_fst_3293_; uint8_t v___x_3294_; lean_object* v___x_3295_; uint8_t v___x_3296_; 
v___x_3292_ = lean_array_uget_borrowed(v_as_3282_, v_i_3283_);
v_fst_3293_ = lean_ctor_get(v___x_3292_, 0);
v___x_3294_ = 1;
lean_inc_ref(v_env_3281_);
v___x_3295_ = l_Lean_Environment_setExporting(v_env_3281_, v___x_3294_);
lean_inc(v_fst_3293_);
v___x_3296_ = l_Lean_Environment_contains(v___x_3295_, v_fst_3293_, v___x_3291_);
if (v___x_3296_ == 0)
{
v___y_3287_ = v_b_3285_;
goto v___jp_3286_;
}
else
{
lean_object* v___x_3297_; 
lean_inc(v___x_3292_);
v___x_3297_ = lean_array_push(v_b_3285_, v___x_3292_);
v___y_3287_ = v___x_3297_;
goto v___jp_3286_;
}
}
else
{
lean_dec_ref(v_env_3281_);
return v_b_3285_;
}
v___jp_3286_:
{
size_t v___x_3288_; size_t v___x_3289_; 
v___x_3288_ = ((size_t)1ULL);
v___x_3289_ = lean_usize_add(v_i_3283_, v___x_3288_);
v_i_3283_ = v___x_3289_;
v_b_3285_ = v___y_3287_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg___boxed(lean_object* v_env_3298_, lean_object* v_as_3299_, lean_object* v_i_3300_, lean_object* v_stop_3301_, lean_object* v_b_3302_){
_start:
{
size_t v_i_boxed_3303_; size_t v_stop_boxed_3304_; lean_object* v_res_3305_; 
v_i_boxed_3303_ = lean_unbox_usize(v_i_3300_);
lean_dec(v_i_3300_);
v_stop_boxed_3304_ = lean_unbox_usize(v_stop_3301_);
lean_dec(v_stop_3301_);
v_res_3305_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg(v_env_3298_, v_as_3299_, v_i_boxed_3303_, v_stop_boxed_3304_, v_b_3302_);
lean_dec_ref(v_as_3299_);
return v_res_3305_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__3(lean_object* v_env_3306_, lean_object* v_m_3307_){
_start:
{
lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v___y_3311_; lean_object* v___x_3325_; lean_object* v___x_3326_; lean_object* v___y_3328_; lean_object* v___y_3329_; uint8_t v___x_3331_; 
v___x_3308_ = lean_unsigned_to_nat(0u);
v___x_3309_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___lam__2___closed__0));
v___x_3325_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1_spec__1___redArg(v___x_3309_, v_m_3307_);
v___x_3326_ = lean_array_get_size(v___x_3325_);
v___x_3331_ = lean_nat_dec_eq(v___x_3326_, v___x_3308_);
if (v___x_3331_ == 0)
{
lean_object* v___x_3332_; lean_object* v___x_3333_; lean_object* v___y_3335_; uint8_t v___x_3337_; 
v___x_3332_ = lean_unsigned_to_nat(1u);
v___x_3333_ = lean_nat_sub(v___x_3326_, v___x_3332_);
v___x_3337_ = lean_nat_dec_le(v___x_3308_, v___x_3333_);
if (v___x_3337_ == 0)
{
lean_inc(v___x_3333_);
v___y_3335_ = v___x_3333_;
goto v___jp_3334_;
}
else
{
v___y_3335_ = v___x_3308_;
goto v___jp_3334_;
}
v___jp_3334_:
{
uint8_t v___x_3336_; 
v___x_3336_ = lean_nat_dec_le(v___y_3335_, v___x_3333_);
if (v___x_3336_ == 0)
{
lean_dec(v___x_3333_);
lean_inc(v___y_3335_);
v___y_3328_ = v___y_3335_;
v___y_3329_ = v___y_3335_;
goto v___jp_3327_;
}
else
{
v___y_3328_ = v___y_3335_;
v___y_3329_ = v___x_3333_;
goto v___jp_3327_;
}
}
}
else
{
v___y_3311_ = v___x_3325_;
goto v___jp_3310_;
}
v___jp_3310_:
{
lean_object* v___x_3312_; uint8_t v___x_3313_; 
v___x_3312_ = lean_array_get_size(v___y_3311_);
v___x_3313_ = lean_nat_dec_lt(v___x_3308_, v___x_3312_);
if (v___x_3313_ == 0)
{
lean_object* v___x_3314_; 
lean_dec_ref(v_env_3306_);
v___x_3314_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3314_, 0, v___x_3309_);
lean_ctor_set(v___x_3314_, 1, v___x_3309_);
lean_ctor_set(v___x_3314_, 2, v___y_3311_);
return v___x_3314_;
}
else
{
uint8_t v___x_3315_; 
v___x_3315_ = lean_nat_dec_le(v___x_3312_, v___x_3312_);
if (v___x_3315_ == 0)
{
if (v___x_3313_ == 0)
{
lean_object* v___x_3316_; 
lean_dec_ref(v_env_3306_);
v___x_3316_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3316_, 0, v___x_3309_);
lean_ctor_set(v___x_3316_, 1, v___x_3309_);
lean_ctor_set(v___x_3316_, 2, v___y_3311_);
return v___x_3316_;
}
else
{
size_t v___x_3317_; size_t v___x_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; 
v___x_3317_ = ((size_t)0ULL);
v___x_3318_ = lean_usize_of_nat(v___x_3312_);
v___x_3319_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg(v_env_3306_, v___y_3311_, v___x_3317_, v___x_3318_, v___x_3309_);
lean_inc_ref(v___x_3319_);
v___x_3320_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3320_, 0, v___x_3319_);
lean_ctor_set(v___x_3320_, 1, v___x_3319_);
lean_ctor_set(v___x_3320_, 2, v___y_3311_);
return v___x_3320_;
}
}
else
{
size_t v___x_3321_; size_t v___x_3322_; lean_object* v___x_3323_; lean_object* v___x_3324_; 
v___x_3321_ = ((size_t)0ULL);
v___x_3322_ = lean_usize_of_nat(v___x_3312_);
v___x_3323_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg(v_env_3306_, v___y_3311_, v___x_3321_, v___x_3322_, v___x_3309_);
lean_inc_ref(v___x_3323_);
v___x_3324_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3324_, 0, v___x_3323_);
lean_ctor_set(v___x_3324_, 1, v___x_3323_);
lean_ctor_set(v___x_3324_, 2, v___y_3311_);
return v___x_3324_;
}
}
}
v___jp_3327_:
{
lean_object* v___x_3330_; 
v___x_3330_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2___redArg(v___x_3326_, v___x_3325_, v___y_3328_, v___y_3329_);
lean_dec(v___y_3329_);
v___y_3311_ = v___x_3330_;
goto v___jp_3310_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__3___boxed(lean_object* v_env_3338_, lean_object* v_m_3339_){
_start:
{
lean_object* v_res_3340_; 
v_res_3340_ = l_Lean_registerEnumAttributes___redArg___lam__3(v_env_3338_, v_m_3339_);
lean_dec(v_m_3339_);
return v_res_3340_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__4(lean_object* v_s_3341_, lean_object* v_p_3342_){
_start:
{
lean_object* v_fst_3343_; lean_object* v_snd_3344_; lean_object* v___x_3345_; 
v_fst_3343_ = lean_ctor_get(v_p_3342_, 0);
lean_inc(v_fst_3343_);
v_snd_3344_ = lean_ctor_get(v_p_3342_, 1);
lean_inc(v_snd_3344_);
lean_dec_ref(v_p_3342_);
v___x_3345_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_3343_, v_snd_3344_, v_s_3341_);
return v___x_3345_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__6(lean_object* v___x_3346_, lean_object* v_x_3347_, lean_object* v_x_3348_){
_start:
{
lean_object* v___x_3350_; 
v___x_3350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3350_, 0, v___x_3346_);
return v___x_3350_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__6___boxed(lean_object* v___x_3351_, lean_object* v_x_3352_, lean_object* v_x_3353_, lean_object* v___y_3354_){
_start:
{
lean_object* v_res_3355_; 
v_res_3355_ = l_Lean_registerEnumAttributes___redArg___lam__6(v___x_3351_, v_x_3352_, v_x_3353_);
lean_dec_ref(v_x_3353_);
lean_dec_ref(v_x_3352_);
return v_res_3355_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_registerEnumAttributes_spec__3(lean_object* v_as_3356_){
_start:
{
if (lean_obj_tag(v_as_3356_) == 0)
{
lean_object* v___x_3358_; lean_object* v___x_3359_; 
v___x_3358_ = lean_box(0);
v___x_3359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3359_, 0, v___x_3358_);
return v___x_3359_;
}
else
{
lean_object* v_head_3360_; lean_object* v_tail_3361_; lean_object* v___x_3362_; 
v_head_3360_ = lean_ctor_get(v_as_3356_, 0);
lean_inc(v_head_3360_);
v_tail_3361_ = lean_ctor_get(v_as_3356_, 1);
lean_inc(v_tail_3361_);
lean_dec_ref(v_as_3356_);
v___x_3362_ = l_Lean_registerBuiltinAttribute(v_head_3360_);
if (lean_obj_tag(v___x_3362_) == 0)
{
lean_dec_ref(v___x_3362_);
v_as_3356_ = v_tail_3361_;
goto _start;
}
else
{
lean_dec(v_tail_3361_);
return v___x_3362_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_registerEnumAttributes_spec__3___boxed(lean_object* v_as_3364_, lean_object* v___y_3365_){
_start:
{
lean_object* v_res_3366_; 
v_res_3366_ = l_List_forM___at___00Lean_registerEnumAttributes_spec__3(v_as_3364_);
return v_res_3366_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__1(lean_object* v_validate_3367_, lean_object* v_snd_3368_, lean_object* v_a_3369_, lean_object* v_fst_3370_, lean_object* v_decl_3371_, lean_object* v_stx_3372_, uint8_t v_kind_3373_, lean_object* v___y_3374_, lean_object* v___y_3375_){
_start:
{
lean_object* v___y_3378_; lean_object* v___y_3379_; lean_object* v___y_3414_; lean_object* v___y_3415_; lean_object* v___x_3420_; 
v___x_3420_ = l_Lean_Attribute_Builtin_ensureNoArgs(v_stx_3372_, v___y_3374_, v___y_3375_);
if (lean_obj_tag(v___x_3420_) == 0)
{
uint8_t v___x_3421_; uint8_t v___x_3422_; 
lean_dec_ref(v___x_3420_);
v___x_3421_ = 0;
v___x_3422_ = l_Lean_instBEqAttributeKind_beq(v_kind_3373_, v___x_3421_);
if (v___x_3422_ == 0)
{
lean_object* v___x_3423_; 
lean_dec(v_decl_3371_);
lean_dec_ref(v_a_3369_);
lean_dec(v_snd_3368_);
lean_dec_ref(v_validate_3367_);
v___x_3423_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg(v_fst_3370_, v_kind_3373_, v___y_3374_, v___y_3375_);
return v___x_3423_;
}
else
{
v___y_3414_ = v___y_3374_;
v___y_3415_ = v___y_3375_;
goto v___jp_3413_;
}
}
else
{
lean_dec(v_decl_3371_);
lean_dec(v_fst_3370_);
lean_dec_ref(v_a_3369_);
lean_dec(v_snd_3368_);
lean_dec_ref(v_validate_3367_);
return v___x_3420_;
}
v___jp_3377_:
{
lean_object* v___x_3380_; 
lean_inc(v___y_3379_);
lean_inc_ref(v___y_3378_);
lean_inc(v_snd_3368_);
lean_inc(v_decl_3371_);
v___x_3380_ = lean_apply_5(v_validate_3367_, v_decl_3371_, v_snd_3368_, v___y_3378_, v___y_3379_, lean_box(0));
if (lean_obj_tag(v___x_3380_) == 0)
{
lean_object* v___x_3382_; uint8_t v_isShared_3383_; uint8_t v_isSharedCheck_3411_; 
v_isSharedCheck_3411_ = !lean_is_exclusive(v___x_3380_);
if (v_isSharedCheck_3411_ == 0)
{
lean_object* v_unused_3412_; 
v_unused_3412_ = lean_ctor_get(v___x_3380_, 0);
lean_dec(v_unused_3412_);
v___x_3382_ = v___x_3380_;
v_isShared_3383_ = v_isSharedCheck_3411_;
goto v_resetjp_3381_;
}
else
{
lean_dec(v___x_3380_);
v___x_3382_ = lean_box(0);
v_isShared_3383_ = v_isSharedCheck_3411_;
goto v_resetjp_3381_;
}
v_resetjp_3381_:
{
lean_object* v___x_3384_; lean_object* v_toEnvExtension_3385_; lean_object* v_env_3386_; lean_object* v_nextMacroScope_3387_; lean_object* v_ngen_3388_; lean_object* v_auxDeclNGen_3389_; lean_object* v_traceState_3390_; lean_object* v_messages_3391_; lean_object* v_infoState_3392_; lean_object* v_snapshotTasks_3393_; lean_object* v___x_3395_; uint8_t v_isShared_3396_; uint8_t v_isSharedCheck_3409_; 
v___x_3384_ = lean_st_ref_take(v___y_3379_);
v_toEnvExtension_3385_ = lean_ctor_get(v_a_3369_, 0);
v_env_3386_ = lean_ctor_get(v___x_3384_, 0);
v_nextMacroScope_3387_ = lean_ctor_get(v___x_3384_, 1);
v_ngen_3388_ = lean_ctor_get(v___x_3384_, 2);
v_auxDeclNGen_3389_ = lean_ctor_get(v___x_3384_, 3);
v_traceState_3390_ = lean_ctor_get(v___x_3384_, 4);
v_messages_3391_ = lean_ctor_get(v___x_3384_, 6);
v_infoState_3392_ = lean_ctor_get(v___x_3384_, 7);
v_snapshotTasks_3393_ = lean_ctor_get(v___x_3384_, 8);
v_isSharedCheck_3409_ = !lean_is_exclusive(v___x_3384_);
if (v_isSharedCheck_3409_ == 0)
{
lean_object* v_unused_3410_; 
v_unused_3410_ = lean_ctor_get(v___x_3384_, 5);
lean_dec(v_unused_3410_);
v___x_3395_ = v___x_3384_;
v_isShared_3396_ = v_isSharedCheck_3409_;
goto v_resetjp_3394_;
}
else
{
lean_inc(v_snapshotTasks_3393_);
lean_inc(v_infoState_3392_);
lean_inc(v_messages_3391_);
lean_inc(v_traceState_3390_);
lean_inc(v_auxDeclNGen_3389_);
lean_inc(v_ngen_3388_);
lean_inc(v_nextMacroScope_3387_);
lean_inc(v_env_3386_);
lean_dec(v___x_3384_);
v___x_3395_ = lean_box(0);
v_isShared_3396_ = v_isSharedCheck_3409_;
goto v_resetjp_3394_;
}
v_resetjp_3394_:
{
lean_object* v_asyncMode_3397_; lean_object* v___x_3398_; lean_object* v___x_3399_; lean_object* v___x_3400_; lean_object* v___x_3402_; 
v_asyncMode_3397_ = lean_ctor_get(v_toEnvExtension_3385_, 2);
lean_inc(v_asyncMode_3397_);
lean_inc(v_decl_3371_);
v___x_3398_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3398_, 0, v_decl_3371_);
lean_ctor_set(v___x_3398_, 1, v_snd_3368_);
v___x_3399_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_a_3369_, v_env_3386_, v___x_3398_, v_asyncMode_3397_, v_decl_3371_);
lean_dec(v_asyncMode_3397_);
v___x_3400_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2);
if (v_isShared_3396_ == 0)
{
lean_ctor_set(v___x_3395_, 5, v___x_3400_);
lean_ctor_set(v___x_3395_, 0, v___x_3399_);
v___x_3402_ = v___x_3395_;
goto v_reusejp_3401_;
}
else
{
lean_object* v_reuseFailAlloc_3408_; 
v_reuseFailAlloc_3408_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3408_, 0, v___x_3399_);
lean_ctor_set(v_reuseFailAlloc_3408_, 1, v_nextMacroScope_3387_);
lean_ctor_set(v_reuseFailAlloc_3408_, 2, v_ngen_3388_);
lean_ctor_set(v_reuseFailAlloc_3408_, 3, v_auxDeclNGen_3389_);
lean_ctor_set(v_reuseFailAlloc_3408_, 4, v_traceState_3390_);
lean_ctor_set(v_reuseFailAlloc_3408_, 5, v___x_3400_);
lean_ctor_set(v_reuseFailAlloc_3408_, 6, v_messages_3391_);
lean_ctor_set(v_reuseFailAlloc_3408_, 7, v_infoState_3392_);
lean_ctor_set(v_reuseFailAlloc_3408_, 8, v_snapshotTasks_3393_);
v___x_3402_ = v_reuseFailAlloc_3408_;
goto v_reusejp_3401_;
}
v_reusejp_3401_:
{
lean_object* v___x_3403_; lean_object* v___x_3404_; lean_object* v___x_3406_; 
v___x_3403_ = lean_st_ref_set(v___y_3379_, v___x_3402_);
v___x_3404_ = lean_box(0);
if (v_isShared_3383_ == 0)
{
lean_ctor_set(v___x_3382_, 0, v___x_3404_);
v___x_3406_ = v___x_3382_;
goto v_reusejp_3405_;
}
else
{
lean_object* v_reuseFailAlloc_3407_; 
v_reuseFailAlloc_3407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3407_, 0, v___x_3404_);
v___x_3406_ = v_reuseFailAlloc_3407_;
goto v_reusejp_3405_;
}
v_reusejp_3405_:
{
return v___x_3406_;
}
}
}
}
}
else
{
lean_dec(v_decl_3371_);
lean_dec_ref(v_a_3369_);
lean_dec(v_snd_3368_);
return v___x_3380_;
}
}
v___jp_3413_:
{
lean_object* v___x_3416_; lean_object* v_env_3417_; lean_object* v___x_3418_; 
v___x_3416_ = lean_st_ref_get(v___y_3415_);
v_env_3417_ = lean_ctor_get(v___x_3416_, 0);
lean_inc_ref(v_env_3417_);
lean_dec(v___x_3416_);
v___x_3418_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3417_, v_decl_3371_);
lean_dec_ref(v_env_3417_);
if (lean_obj_tag(v___x_3418_) == 0)
{
lean_dec(v_fst_3370_);
v___y_3378_ = v___y_3414_;
v___y_3379_ = v___y_3415_;
goto v___jp_3377_;
}
else
{
lean_object* v___x_3419_; 
lean_dec_ref(v___x_3418_);
lean_dec_ref(v_a_3369_);
lean_dec(v_snd_3368_);
lean_dec_ref(v_validate_3367_);
v___x_3419_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg(v_fst_3370_, v_decl_3371_, v___y_3414_, v___y_3415_);
return v___x_3419_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__1___boxed(lean_object* v_validate_3424_, lean_object* v_snd_3425_, lean_object* v_a_3426_, lean_object* v_fst_3427_, lean_object* v_decl_3428_, lean_object* v_stx_3429_, lean_object* v_kind_3430_, lean_object* v___y_3431_, lean_object* v___y_3432_, lean_object* v___y_3433_){
_start:
{
uint8_t v_kind_boxed_3434_; lean_object* v_res_3435_; 
v_kind_boxed_3434_ = lean_unbox(v_kind_3430_);
v_res_3435_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__1(v_validate_3424_, v_snd_3425_, v_a_3426_, v_fst_3427_, v_decl_3428_, v_stx_3429_, v_kind_boxed_3434_, v___y_3431_, v___y_3432_);
lean_dec(v___y_3432_);
lean_dec_ref(v___y_3431_);
return v_res_3435_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__0(lean_object* v_fst_3436_, lean_object* v_decl_3437_, lean_object* v___y_3438_, lean_object* v___y_3439_){
_start:
{
lean_object* v___x_3441_; lean_object* v___x_3442_; lean_object* v___x_3443_; lean_object* v___x_3444_; lean_object* v___x_3445_; lean_object* v___x_3446_; 
v___x_3441_ = lean_obj_once(&l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1, &l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1_once, _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1);
v___x_3442_ = l_Lean_MessageData_ofName(v_fst_3436_);
v___x_3443_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3443_, 0, v___x_3441_);
lean_ctor_set(v___x_3443_, 1, v___x_3442_);
v___x_3444_ = lean_obj_once(&l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3, &l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3_once, _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3);
v___x_3445_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3445_, 0, v___x_3443_);
lean_ctor_set(v___x_3445_, 1, v___x_3444_);
v___x_3446_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_3445_, v___y_3438_, v___y_3439_);
return v___x_3446_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__0___boxed(lean_object* v_fst_3447_, lean_object* v_decl_3448_, lean_object* v___y_3449_, lean_object* v___y_3450_, lean_object* v___y_3451_){
_start:
{
lean_object* v_res_3452_; 
v_res_3452_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__0(v_fst_3447_, v_decl_3448_, v___y_3449_, v___y_3450_);
lean_dec(v___y_3450_);
lean_dec_ref(v___y_3449_);
lean_dec(v_decl_3448_);
return v_res_3452_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg(lean_object* v_validate_3453_, lean_object* v_a_3454_, lean_object* v_ref_3455_, uint8_t v_applicationTime_3456_, lean_object* v_a_3457_, lean_object* v_a_3458_){
_start:
{
if (lean_obj_tag(v_a_3457_) == 0)
{
lean_object* v___x_3459_; 
lean_dec(v_ref_3455_);
lean_dec_ref(v_a_3454_);
lean_dec_ref(v_validate_3453_);
v___x_3459_ = l_List_reverse___redArg(v_a_3458_);
return v___x_3459_;
}
else
{
lean_object* v_head_3460_; lean_object* v_snd_3461_; lean_object* v_tail_3462_; lean_object* v___x_3464_; uint8_t v_isShared_3465_; uint8_t v_isSharedCheck_3477_; 
v_head_3460_ = lean_ctor_get(v_a_3457_, 0);
lean_inc(v_head_3460_);
v_snd_3461_ = lean_ctor_get(v_head_3460_, 1);
lean_inc(v_snd_3461_);
v_tail_3462_ = lean_ctor_get(v_a_3457_, 1);
v_isSharedCheck_3477_ = !lean_is_exclusive(v_a_3457_);
if (v_isSharedCheck_3477_ == 0)
{
lean_object* v_unused_3478_; 
v_unused_3478_ = lean_ctor_get(v_a_3457_, 0);
lean_dec(v_unused_3478_);
v___x_3464_ = v_a_3457_;
v_isShared_3465_ = v_isSharedCheck_3477_;
goto v_resetjp_3463_;
}
else
{
lean_inc(v_tail_3462_);
lean_dec(v_a_3457_);
v___x_3464_ = lean_box(0);
v_isShared_3465_ = v_isSharedCheck_3477_;
goto v_resetjp_3463_;
}
v_resetjp_3463_:
{
lean_object* v_fst_3466_; lean_object* v_fst_3467_; lean_object* v_snd_3468_; lean_object* v___f_3469_; lean_object* v___f_3470_; lean_object* v___x_3471_; lean_object* v___x_3472_; lean_object* v___x_3474_; 
v_fst_3466_ = lean_ctor_get(v_head_3460_, 0);
lean_inc_n(v_fst_3466_, 3);
lean_dec(v_head_3460_);
v_fst_3467_ = lean_ctor_get(v_snd_3461_, 0);
lean_inc(v_fst_3467_);
v_snd_3468_ = lean_ctor_get(v_snd_3461_, 1);
lean_inc(v_snd_3468_);
lean_dec(v_snd_3461_);
v___f_3469_ = lean_alloc_closure((void*)(l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__0___boxed), 5, 1);
lean_closure_set(v___f_3469_, 0, v_fst_3466_);
lean_inc_ref(v_a_3454_);
lean_inc_ref(v_validate_3453_);
v___f_3470_ = lean_alloc_closure((void*)(l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__1___boxed), 10, 4);
lean_closure_set(v___f_3470_, 0, v_validate_3453_);
lean_closure_set(v___f_3470_, 1, v_snd_3468_);
lean_closure_set(v___f_3470_, 2, v_a_3454_);
lean_closure_set(v___f_3470_, 3, v_fst_3466_);
lean_inc(v_ref_3455_);
v___x_3471_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_3471_, 0, v_ref_3455_);
lean_ctor_set(v___x_3471_, 1, v_fst_3466_);
lean_ctor_set(v___x_3471_, 2, v_fst_3467_);
lean_ctor_set_uint8(v___x_3471_, sizeof(void*)*3, v_applicationTime_3456_);
v___x_3472_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3472_, 0, v___x_3471_);
lean_ctor_set(v___x_3472_, 1, v___f_3470_);
lean_ctor_set(v___x_3472_, 2, v___f_3469_);
if (v_isShared_3465_ == 0)
{
lean_ctor_set(v___x_3464_, 1, v_a_3458_);
lean_ctor_set(v___x_3464_, 0, v___x_3472_);
v___x_3474_ = v___x_3464_;
goto v_reusejp_3473_;
}
else
{
lean_object* v_reuseFailAlloc_3476_; 
v_reuseFailAlloc_3476_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3476_, 0, v___x_3472_);
lean_ctor_set(v_reuseFailAlloc_3476_, 1, v_a_3458_);
v___x_3474_ = v_reuseFailAlloc_3476_;
goto v_reusejp_3473_;
}
v_reusejp_3473_:
{
v_a_3457_ = v_tail_3462_;
v_a_3458_ = v___x_3474_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___boxed(lean_object* v_validate_3479_, lean_object* v_a_3480_, lean_object* v_ref_3481_, lean_object* v_applicationTime_3482_, lean_object* v_a_3483_, lean_object* v_a_3484_){
_start:
{
uint8_t v_applicationTime_boxed_3485_; lean_object* v_res_3486_; 
v_applicationTime_boxed_3485_ = lean_unbox(v_applicationTime_3482_);
v_res_3486_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg(v_validate_3479_, v_a_3480_, v_ref_3481_, v_applicationTime_boxed_3485_, v_a_3483_, v_a_3484_);
return v_res_3486_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg(lean_object* v_attrDescrs_3500_, lean_object* v_validate_3501_, uint8_t v_applicationTime_3502_, lean_object* v_ref_3503_){
_start:
{
lean_object* v___f_3505_; lean_object* v___f_3506_; lean_object* v___f_3507_; lean_object* v___f_3508_; lean_object* v___f_3509_; lean_object* v___f_3510_; lean_object* v___x_3511_; lean_object* v___x_3512_; lean_object* v___x_3513_; lean_object* v___x_3514_; lean_object* v___x_3515_; 
v___f_3505_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__0));
v___f_3506_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__2));
v___f_3507_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__3));
v___f_3508_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__4));
v___f_3509_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__5));
v___f_3510_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__6));
v___x_3511_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__7));
v___x_3512_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__8));
lean_inc(v_ref_3503_);
v___x_3513_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_3513_, 0, v_ref_3503_);
lean_ctor_set(v___x_3513_, 1, v___f_3509_);
lean_ctor_set(v___x_3513_, 2, v___f_3510_);
lean_ctor_set(v___x_3513_, 3, v___f_3508_);
lean_ctor_set(v___x_3513_, 4, v___f_3507_);
lean_ctor_set(v___x_3513_, 5, v___f_3506_);
lean_ctor_set(v___x_3513_, 6, v___x_3511_);
lean_ctor_set(v___x_3513_, 7, v___x_3512_);
v___x_3514_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3514_, 0, v___x_3513_);
lean_ctor_set(v___x_3514_, 1, v___f_3505_);
v___x_3515_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_3514_);
if (lean_obj_tag(v___x_3515_) == 0)
{
lean_object* v_a_3516_; lean_object* v___x_3517_; lean_object* v___x_3518_; lean_object* v___x_3519_; 
v_a_3516_ = lean_ctor_get(v___x_3515_, 0);
lean_inc_n(v_a_3516_, 2);
lean_dec_ref(v___x_3515_);
v___x_3517_ = lean_box(0);
v___x_3518_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg(v_validate_3501_, v_a_3516_, v_ref_3503_, v_applicationTime_3502_, v_attrDescrs_3500_, v___x_3517_);
lean_inc(v___x_3518_);
v___x_3519_ = l_List_forM___at___00Lean_registerEnumAttributes_spec__3(v___x_3518_);
if (lean_obj_tag(v___x_3519_) == 0)
{
lean_object* v___x_3521_; uint8_t v_isShared_3522_; uint8_t v_isSharedCheck_3527_; 
v_isSharedCheck_3527_ = !lean_is_exclusive(v___x_3519_);
if (v_isSharedCheck_3527_ == 0)
{
lean_object* v_unused_3528_; 
v_unused_3528_ = lean_ctor_get(v___x_3519_, 0);
lean_dec(v_unused_3528_);
v___x_3521_ = v___x_3519_;
v_isShared_3522_ = v_isSharedCheck_3527_;
goto v_resetjp_3520_;
}
else
{
lean_dec(v___x_3519_);
v___x_3521_ = lean_box(0);
v_isShared_3522_ = v_isSharedCheck_3527_;
goto v_resetjp_3520_;
}
v_resetjp_3520_:
{
lean_object* v___x_3523_; lean_object* v___x_3525_; 
v___x_3523_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3523_, 0, v___x_3518_);
lean_ctor_set(v___x_3523_, 1, v_a_3516_);
if (v_isShared_3522_ == 0)
{
lean_ctor_set(v___x_3521_, 0, v___x_3523_);
v___x_3525_ = v___x_3521_;
goto v_reusejp_3524_;
}
else
{
lean_object* v_reuseFailAlloc_3526_; 
v_reuseFailAlloc_3526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3526_, 0, v___x_3523_);
v___x_3525_ = v_reuseFailAlloc_3526_;
goto v_reusejp_3524_;
}
v_reusejp_3524_:
{
return v___x_3525_;
}
}
}
else
{
lean_object* v_a_3529_; lean_object* v___x_3531_; uint8_t v_isShared_3532_; uint8_t v_isSharedCheck_3536_; 
lean_dec(v___x_3518_);
lean_dec(v_a_3516_);
v_a_3529_ = lean_ctor_get(v___x_3519_, 0);
v_isSharedCheck_3536_ = !lean_is_exclusive(v___x_3519_);
if (v_isSharedCheck_3536_ == 0)
{
v___x_3531_ = v___x_3519_;
v_isShared_3532_ = v_isSharedCheck_3536_;
goto v_resetjp_3530_;
}
else
{
lean_inc(v_a_3529_);
lean_dec(v___x_3519_);
v___x_3531_ = lean_box(0);
v_isShared_3532_ = v_isSharedCheck_3536_;
goto v_resetjp_3530_;
}
v_resetjp_3530_:
{
lean_object* v___x_3534_; 
if (v_isShared_3532_ == 0)
{
v___x_3534_ = v___x_3531_;
goto v_reusejp_3533_;
}
else
{
lean_object* v_reuseFailAlloc_3535_; 
v_reuseFailAlloc_3535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3535_, 0, v_a_3529_);
v___x_3534_ = v_reuseFailAlloc_3535_;
goto v_reusejp_3533_;
}
v_reusejp_3533_:
{
return v___x_3534_;
}
}
}
}
else
{
lean_object* v_a_3537_; lean_object* v___x_3539_; uint8_t v_isShared_3540_; uint8_t v_isSharedCheck_3544_; 
lean_dec(v_ref_3503_);
lean_dec_ref(v_validate_3501_);
lean_dec(v_attrDescrs_3500_);
v_a_3537_ = lean_ctor_get(v___x_3515_, 0);
v_isSharedCheck_3544_ = !lean_is_exclusive(v___x_3515_);
if (v_isSharedCheck_3544_ == 0)
{
v___x_3539_ = v___x_3515_;
v_isShared_3540_ = v_isSharedCheck_3544_;
goto v_resetjp_3538_;
}
else
{
lean_inc(v_a_3537_);
lean_dec(v___x_3515_);
v___x_3539_ = lean_box(0);
v_isShared_3540_ = v_isSharedCheck_3544_;
goto v_resetjp_3538_;
}
v_resetjp_3538_:
{
lean_object* v___x_3542_; 
if (v_isShared_3540_ == 0)
{
v___x_3542_ = v___x_3539_;
goto v_reusejp_3541_;
}
else
{
lean_object* v_reuseFailAlloc_3543_; 
v_reuseFailAlloc_3543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3543_, 0, v_a_3537_);
v___x_3542_ = v_reuseFailAlloc_3543_;
goto v_reusejp_3541_;
}
v_reusejp_3541_:
{
return v___x_3542_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___boxed(lean_object* v_attrDescrs_3545_, lean_object* v_validate_3546_, lean_object* v_applicationTime_3547_, lean_object* v_ref_3548_, lean_object* v_a_3549_){
_start:
{
uint8_t v_applicationTime_boxed_3550_; lean_object* v_res_3551_; 
v_applicationTime_boxed_3550_ = lean_unbox(v_applicationTime_3547_);
v_res_3551_ = l_Lean_registerEnumAttributes___redArg(v_attrDescrs_3545_, v_validate_3546_, v_applicationTime_boxed_3550_, v_ref_3548_);
return v_res_3551_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes(lean_object* v_00_u03b1_3552_, lean_object* v_attrDescrs_3553_, lean_object* v_validate_3554_, uint8_t v_applicationTime_3555_, lean_object* v_ref_3556_){
_start:
{
lean_object* v___x_3558_; 
v___x_3558_ = l_Lean_registerEnumAttributes___redArg(v_attrDescrs_3553_, v_validate_3554_, v_applicationTime_3555_, v_ref_3556_);
return v___x_3558_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___boxed(lean_object* v_00_u03b1_3559_, lean_object* v_attrDescrs_3560_, lean_object* v_validate_3561_, lean_object* v_applicationTime_3562_, lean_object* v_ref_3563_, lean_object* v_a_3564_){
_start:
{
uint8_t v_applicationTime_boxed_3565_; lean_object* v_res_3566_; 
v_applicationTime_boxed_3565_ = lean_unbox(v_applicationTime_3562_);
v_res_3566_ = l_Lean_registerEnumAttributes(v_00_u03b1_3559_, v_attrDescrs_3560_, v_validate_3561_, v_applicationTime_boxed_3565_, v_ref_3563_);
return v_res_3566_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0(lean_object* v_00_u03b1_3567_, lean_object* v_env_3568_, lean_object* v_as_3569_, size_t v_i_3570_, size_t v_stop_3571_, lean_object* v_b_3572_){
_start:
{
lean_object* v___x_3573_; 
v___x_3573_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg(v_env_3568_, v_as_3569_, v_i_3570_, v_stop_3571_, v_b_3572_);
return v___x_3573_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___boxed(lean_object* v_00_u03b1_3574_, lean_object* v_env_3575_, lean_object* v_as_3576_, lean_object* v_i_3577_, lean_object* v_stop_3578_, lean_object* v_b_3579_){
_start:
{
size_t v_i_boxed_3580_; size_t v_stop_boxed_3581_; lean_object* v_res_3582_; 
v_i_boxed_3580_ = lean_unbox_usize(v_i_3577_);
lean_dec(v_i_3577_);
v_stop_boxed_3581_ = lean_unbox_usize(v_stop_3578_);
lean_dec(v_stop_3578_);
v_res_3582_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0(v_00_u03b1_3574_, v_env_3575_, v_as_3576_, v_i_boxed_3580_, v_stop_boxed_3581_, v_b_3579_);
lean_dec_ref(v_as_3576_);
return v_res_3582_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerEnumAttributes_spec__1(lean_object* v_00_u03b1_3583_, lean_object* v_newState_3584_, lean_object* v_x_3585_, lean_object* v_x_3586_){
_start:
{
lean_object* v___x_3587_; 
v___x_3587_ = l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___redArg(v_newState_3584_, v_x_3585_, v_x_3586_);
return v___x_3587_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___boxed(lean_object* v_00_u03b1_3588_, lean_object* v_newState_3589_, lean_object* v_x_3590_, lean_object* v_x_3591_){
_start:
{
lean_object* v_res_3592_; 
v_res_3592_ = l_List_foldl___at___00Lean_registerEnumAttributes_spec__1(v_00_u03b1_3588_, v_newState_3589_, v_x_3590_, v_x_3591_);
lean_dec(v_newState_3589_);
return v_res_3592_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2(lean_object* v_00_u03b1_3593_, lean_object* v_validate_3594_, lean_object* v_a_3595_, lean_object* v_ref_3596_, uint8_t v_applicationTime_3597_, lean_object* v_a_3598_, lean_object* v_a_3599_){
_start:
{
lean_object* v___x_3600_; 
v___x_3600_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg(v_validate_3594_, v_a_3595_, v_ref_3596_, v_applicationTime_3597_, v_a_3598_, v_a_3599_);
return v___x_3600_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___boxed(lean_object* v_00_u03b1_3601_, lean_object* v_validate_3602_, lean_object* v_a_3603_, lean_object* v_ref_3604_, lean_object* v_applicationTime_3605_, lean_object* v_a_3606_, lean_object* v_a_3607_){
_start:
{
uint8_t v_applicationTime_boxed_3608_; lean_object* v_res_3609_; 
v_applicationTime_boxed_3608_ = lean_unbox(v_applicationTime_3605_);
v_res_3609_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2(v_00_u03b1_3601_, v_validate_3602_, v_a_3603_, v_ref_3604_, v_applicationTime_boxed_3608_, v_a_3606_, v_a_3607_);
return v_res_3609_;
}
}
LEAN_EXPORT lean_object* l_Lean_EnumAttributes_getValue___redArg(lean_object* v_inst_3610_, lean_object* v_attr_3611_, lean_object* v_env_3612_, lean_object* v_decl_3613_){
_start:
{
lean_object* v___x_3614_; lean_object* v___x_3615_; 
v___x_3614_ = lean_box(1);
v___x_3615_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3612_, v_decl_3613_);
if (lean_obj_tag(v___x_3615_) == 0)
{
lean_object* v_ext_3616_; lean_object* v_toEnvExtension_3617_; lean_object* v_asyncMode_3618_; lean_object* v___x_3619_; lean_object* v___x_3620_; 
lean_dec(v_inst_3610_);
v_ext_3616_ = lean_ctor_get(v_attr_3611_, 1);
lean_inc_ref(v_ext_3616_);
lean_dec_ref(v_attr_3611_);
v_toEnvExtension_3617_ = lean_ctor_get(v_ext_3616_, 0);
v_asyncMode_3618_ = lean_ctor_get(v_toEnvExtension_3617_, 2);
lean_inc(v_asyncMode_3618_);
lean_inc(v_decl_3613_);
v___x_3619_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3614_, v_ext_3616_, v_env_3612_, v_asyncMode_3618_, v_decl_3613_);
lean_dec(v_asyncMode_3618_);
lean_dec_ref(v_ext_3616_);
v___x_3620_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_3619_, v_decl_3613_);
lean_dec(v_decl_3613_);
lean_dec(v___x_3619_);
return v___x_3620_;
}
else
{
lean_object* v_val_3621_; lean_object* v_ext_3622_; lean_object* v___x_3624_; uint8_t v_isShared_3625_; uint8_t v_isSharedCheck_3652_; 
v_val_3621_ = lean_ctor_get(v___x_3615_, 0);
lean_inc(v_val_3621_);
lean_dec_ref(v___x_3615_);
v_ext_3622_ = lean_ctor_get(v_attr_3611_, 1);
v_isSharedCheck_3652_ = !lean_is_exclusive(v_attr_3611_);
if (v_isSharedCheck_3652_ == 0)
{
lean_object* v_unused_3653_; 
v_unused_3653_ = lean_ctor_get(v_attr_3611_, 0);
lean_dec(v_unused_3653_);
v___x_3624_ = v_attr_3611_;
v_isShared_3625_ = v_isSharedCheck_3652_;
goto v_resetjp_3623_;
}
else
{
lean_inc(v_ext_3622_);
lean_dec(v_attr_3611_);
v___x_3624_ = lean_box(0);
v_isShared_3625_ = v_isSharedCheck_3652_;
goto v_resetjp_3623_;
}
v_resetjp_3623_:
{
uint8_t v___x_3626_; lean_object* v___x_3627_; lean_object* v___x_3628_; lean_object* v___x_3629_; uint8_t v___x_3630_; 
v___x_3626_ = 0;
v___x_3627_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_3614_, v_ext_3622_, v_env_3612_, v_val_3621_, v___x_3626_);
lean_dec(v_val_3621_);
lean_dec_ref(v_env_3612_);
lean_dec_ref(v_ext_3622_);
v___x_3628_ = lean_unsigned_to_nat(0u);
v___x_3629_ = lean_array_get_size(v___x_3627_);
v___x_3630_ = lean_nat_dec_lt(v___x_3628_, v___x_3629_);
if (v___x_3630_ == 0)
{
lean_object* v___x_3631_; 
lean_dec_ref(v___x_3627_);
lean_del_object(v___x_3624_);
lean_dec(v_decl_3613_);
lean_dec(v_inst_3610_);
v___x_3631_ = lean_box(0);
return v___x_3631_;
}
else
{
lean_object* v___x_3632_; lean_object* v___x_3633_; uint8_t v___x_3634_; 
v___x_3632_ = lean_unsigned_to_nat(1u);
v___x_3633_ = lean_nat_sub(v___x_3629_, v___x_3632_);
v___x_3634_ = lean_nat_dec_le(v___x_3628_, v___x_3633_);
if (v___x_3634_ == 0)
{
lean_object* v___x_3635_; 
lean_dec(v___x_3633_);
lean_dec_ref(v___x_3627_);
lean_del_object(v___x_3624_);
lean_dec(v_decl_3613_);
lean_dec(v_inst_3610_);
v___x_3635_ = lean_box(0);
return v___x_3635_;
}
else
{
lean_object* v___f_3636_; lean_object* v___x_3638_; 
v___f_3636_ = ((lean_object*)(l_Lean_ParametricAttribute_getParam_x3f___redArg___closed__1));
if (v_isShared_3625_ == 0)
{
lean_ctor_set(v___x_3624_, 1, v_inst_3610_);
lean_ctor_set(v___x_3624_, 0, v_decl_3613_);
v___x_3638_ = v___x_3624_;
goto v_reusejp_3637_;
}
else
{
lean_object* v_reuseFailAlloc_3651_; 
v_reuseFailAlloc_3651_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3651_, 0, v_decl_3613_);
lean_ctor_set(v_reuseFailAlloc_3651_, 1, v_inst_3610_);
v___x_3638_ = v_reuseFailAlloc_3651_;
goto v_reusejp_3637_;
}
v_reusejp_3637_:
{
lean_object* v___x_3639_; lean_object* v___x_3640_; 
v___x_3639_ = ((lean_object*)(l_Lean_ParametricAttribute_getParam_x3f___redArg___closed__2));
v___x_3640_ = l_Array_binSearchAux___redArg(v___f_3636_, v___x_3639_, v___x_3627_, v___x_3638_, v___x_3628_, v___x_3633_);
lean_dec_ref(v___x_3627_);
if (lean_obj_tag(v___x_3640_) == 0)
{
lean_object* v___x_3641_; 
v___x_3641_ = lean_box(0);
return v___x_3641_;
}
else
{
lean_object* v_val_3642_; lean_object* v___x_3644_; uint8_t v_isShared_3645_; uint8_t v_isSharedCheck_3650_; 
v_val_3642_ = lean_ctor_get(v___x_3640_, 0);
v_isSharedCheck_3650_ = !lean_is_exclusive(v___x_3640_);
if (v_isSharedCheck_3650_ == 0)
{
v___x_3644_ = v___x_3640_;
v_isShared_3645_ = v_isSharedCheck_3650_;
goto v_resetjp_3643_;
}
else
{
lean_inc(v_val_3642_);
lean_dec(v___x_3640_);
v___x_3644_ = lean_box(0);
v_isShared_3645_ = v_isSharedCheck_3650_;
goto v_resetjp_3643_;
}
v_resetjp_3643_:
{
lean_object* v_snd_3646_; lean_object* v___x_3648_; 
v_snd_3646_ = lean_ctor_get(v_val_3642_, 1);
lean_inc(v_snd_3646_);
lean_dec(v_val_3642_);
if (v_isShared_3645_ == 0)
{
lean_ctor_set(v___x_3644_, 0, v_snd_3646_);
v___x_3648_ = v___x_3644_;
goto v_reusejp_3647_;
}
else
{
lean_object* v_reuseFailAlloc_3649_; 
v_reuseFailAlloc_3649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3649_, 0, v_snd_3646_);
v___x_3648_ = v_reuseFailAlloc_3649_;
goto v_reusejp_3647_;
}
v_reusejp_3647_:
{
return v___x_3648_;
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
LEAN_EXPORT lean_object* l_Lean_EnumAttributes_getValue(lean_object* v_00_u03b1_3654_, lean_object* v_inst_3655_, lean_object* v_attr_3656_, lean_object* v_env_3657_, lean_object* v_decl_3658_){
_start:
{
lean_object* v___x_3659_; 
v___x_3659_ = l_Lean_EnumAttributes_getValue___redArg(v_inst_3655_, v_attr_3656_, v_env_3657_, v_decl_3658_);
return v___x_3659_;
}
}
LEAN_EXPORT lean_object* l_Lean_EnumAttributes_setValue___redArg(lean_object* v_attrs_3668_, lean_object* v_env_3669_, lean_object* v_decl_3670_, lean_object* v_val_3671_){
_start:
{
lean_object* v_ext_3672_; lean_object* v___x_3674_; uint8_t v_isShared_3675_; uint8_t v_isSharedCheck_3736_; 
v_ext_3672_ = lean_ctor_get(v_attrs_3668_, 1);
v_isSharedCheck_3736_ = !lean_is_exclusive(v_attrs_3668_);
if (v_isSharedCheck_3736_ == 0)
{
lean_object* v_unused_3737_; 
v_unused_3737_ = lean_ctor_get(v_attrs_3668_, 0);
lean_dec(v_unused_3737_);
v___x_3674_ = v_attrs_3668_;
v_isShared_3675_ = v_isSharedCheck_3736_;
goto v_resetjp_3673_;
}
else
{
lean_inc(v_ext_3672_);
lean_dec(v_attrs_3668_);
v___x_3674_ = lean_box(0);
v_isShared_3675_ = v_isSharedCheck_3736_;
goto v_resetjp_3673_;
}
v_resetjp_3673_:
{
lean_object* v_toEnvExtension_3676_; lean_object* v_name_3677_; lean_object* v___x_3678_; uint8_t v___x_3679_; lean_object* v___x_3680_; lean_object* v___x_3681_; lean_object* v___x_3682_; lean_object* v___x_3683_; lean_object* v___x_3684_; lean_object* v___x_3685_; lean_object* v___x_3686_; lean_object* v_pfx_3687_; lean_object* v___x_3688_; 
v_toEnvExtension_3676_ = lean_ctor_get(v_ext_3672_, 0);
v_name_3677_ = lean_ctor_get(v_ext_3672_, 1);
v___x_3678_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__0));
v___x_3679_ = 1;
lean_inc(v_name_3677_);
v___x_3680_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_3677_, v___x_3679_);
v___x_3681_ = lean_string_append(v___x_3678_, v___x_3680_);
lean_dec_ref(v___x_3680_);
v___x_3682_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__1));
v___x_3683_ = lean_string_append(v___x_3681_, v___x_3682_);
lean_inc(v_decl_3670_);
v___x_3684_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_decl_3670_, v___x_3679_);
v___x_3685_ = lean_string_append(v___x_3683_, v___x_3684_);
lean_dec_ref(v___x_3684_);
v___x_3686_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__4));
v_pfx_3687_ = lean_string_append(v___x_3685_, v___x_3686_);
v___x_3688_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3669_, v_decl_3670_);
if (lean_obj_tag(v___x_3688_) == 0)
{
lean_object* v_asyncMode_3689_; uint8_t v___x_3696_; 
v_asyncMode_3689_ = lean_ctor_get(v_toEnvExtension_3676_, 2);
lean_inc(v_asyncMode_3689_);
lean_inc(v_decl_3670_);
lean_inc_ref(v_env_3669_);
v___x_3696_ = l_Lean_EnvExtension_asyncMayModify___redArg(v_env_3669_, v_decl_3670_, v_asyncMode_3689_);
if (v___x_3696_ == 0)
{
lean_object* v___x_3697_; lean_object* v___x_3698_; lean_object* v___y_3700_; lean_object* v___x_3704_; 
lean_dec(v_asyncMode_3689_);
lean_del_object(v___x_3674_);
lean_dec_ref(v_ext_3672_);
lean_dec(v_val_3671_);
lean_dec(v_decl_3670_);
v___x_3697_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__2));
v___x_3698_ = lean_string_append(v_pfx_3687_, v___x_3697_);
v___x_3704_ = l_Lean_Environment_asyncPrefix_x3f(v_env_3669_);
if (lean_obj_tag(v___x_3704_) == 0)
{
lean_object* v___x_3705_; 
v___x_3705_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__3));
v___y_3700_ = v___x_3705_;
goto v___jp_3699_;
}
else
{
lean_object* v_val_3706_; lean_object* v___x_3707_; lean_object* v___x_3708_; lean_object* v___x_3709_; lean_object* v___x_3710_; lean_object* v___x_3711_; lean_object* v___x_3712_; 
v_val_3706_ = lean_ctor_get(v___x_3704_, 0);
lean_inc(v_val_3706_);
lean_dec_ref(v___x_3704_);
v___x_3707_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__4));
v___x_3708_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_val_3706_, v___x_3679_);
v___x_3709_ = l_addParenHeuristic(v___x_3708_);
v___x_3710_ = lean_string_append(v___x_3707_, v___x_3709_);
lean_dec_ref(v___x_3709_);
v___x_3711_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__5));
v___x_3712_ = lean_string_append(v___x_3710_, v___x_3711_);
v___y_3700_ = v___x_3712_;
goto v___jp_3699_;
}
v___jp_3699_:
{
lean_object* v___x_3701_; lean_object* v___x_3702_; lean_object* v___x_3703_; 
v___x_3701_ = lean_string_append(v___x_3698_, v___y_3700_);
lean_dec_ref(v___y_3700_);
v___x_3702_ = lean_string_append(v___x_3701_, v___x_3686_);
v___x_3703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3703_, 0, v___x_3702_);
return v___x_3703_;
}
}
else
{
lean_object* v___x_3713_; lean_object* v___x_3714_; lean_object* v___x_3715_; 
v___x_3713_ = lean_box(1);
lean_inc(v_decl_3670_);
lean_inc_ref(v_env_3669_);
v___x_3714_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3713_, v_ext_3672_, v_env_3669_, v_asyncMode_3689_, v_decl_3670_);
v___x_3715_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_3714_, v_decl_3670_);
lean_dec(v___x_3714_);
if (lean_obj_tag(v___x_3715_) == 0)
{
lean_dec_ref(v_pfx_3687_);
goto v___jp_3690_;
}
else
{
lean_object* v___x_3717_; uint8_t v_isShared_3718_; uint8_t v_isSharedCheck_3724_; 
v_isSharedCheck_3724_ = !lean_is_exclusive(v___x_3715_);
if (v_isSharedCheck_3724_ == 0)
{
lean_object* v_unused_3725_; 
v_unused_3725_ = lean_ctor_get(v___x_3715_, 0);
lean_dec(v_unused_3725_);
v___x_3717_ = v___x_3715_;
v_isShared_3718_ = v_isSharedCheck_3724_;
goto v_resetjp_3716_;
}
else
{
lean_dec(v___x_3715_);
v___x_3717_ = lean_box(0);
v_isShared_3718_ = v_isSharedCheck_3724_;
goto v_resetjp_3716_;
}
v_resetjp_3716_:
{
if (v___x_3696_ == 0)
{
lean_del_object(v___x_3717_);
lean_dec_ref(v_pfx_3687_);
goto v___jp_3690_;
}
else
{
lean_object* v___x_3719_; lean_object* v___x_3720_; lean_object* v___x_3722_; 
lean_dec(v_asyncMode_3689_);
lean_del_object(v___x_3674_);
lean_dec_ref(v_ext_3672_);
lean_dec(v_val_3671_);
lean_dec(v_decl_3670_);
lean_dec_ref(v_env_3669_);
v___x_3719_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__6));
v___x_3720_ = lean_string_append(v_pfx_3687_, v___x_3719_);
if (v_isShared_3718_ == 0)
{
lean_ctor_set_tag(v___x_3717_, 0);
lean_ctor_set(v___x_3717_, 0, v___x_3720_);
v___x_3722_ = v___x_3717_;
goto v_reusejp_3721_;
}
else
{
lean_object* v_reuseFailAlloc_3723_; 
v_reuseFailAlloc_3723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3723_, 0, v___x_3720_);
v___x_3722_ = v_reuseFailAlloc_3723_;
goto v_reusejp_3721_;
}
v_reusejp_3721_:
{
return v___x_3722_;
}
}
}
}
}
v___jp_3690_:
{
lean_object* v___x_3692_; 
lean_inc(v_decl_3670_);
if (v_isShared_3675_ == 0)
{
lean_ctor_set(v___x_3674_, 1, v_val_3671_);
lean_ctor_set(v___x_3674_, 0, v_decl_3670_);
v___x_3692_ = v___x_3674_;
goto v_reusejp_3691_;
}
else
{
lean_object* v_reuseFailAlloc_3695_; 
v_reuseFailAlloc_3695_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3695_, 0, v_decl_3670_);
lean_ctor_set(v_reuseFailAlloc_3695_, 1, v_val_3671_);
v___x_3692_ = v_reuseFailAlloc_3695_;
goto v_reusejp_3691_;
}
v_reusejp_3691_:
{
lean_object* v___x_3693_; lean_object* v___x_3694_; 
v___x_3693_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_ext_3672_, v_env_3669_, v___x_3692_, v_asyncMode_3689_, v_decl_3670_);
lean_dec(v_asyncMode_3689_);
v___x_3694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3694_, 0, v___x_3693_);
return v___x_3694_;
}
}
}
else
{
lean_object* v___x_3727_; uint8_t v_isShared_3728_; uint8_t v_isSharedCheck_3734_; 
lean_del_object(v___x_3674_);
lean_dec_ref(v_ext_3672_);
lean_dec(v_val_3671_);
lean_dec(v_decl_3670_);
lean_dec_ref(v_env_3669_);
v_isSharedCheck_3734_ = !lean_is_exclusive(v___x_3688_);
if (v_isSharedCheck_3734_ == 0)
{
lean_object* v_unused_3735_; 
v_unused_3735_ = lean_ctor_get(v___x_3688_, 0);
lean_dec(v_unused_3735_);
v___x_3727_ = v___x_3688_;
v_isShared_3728_ = v_isSharedCheck_3734_;
goto v_resetjp_3726_;
}
else
{
lean_dec(v___x_3688_);
v___x_3727_ = lean_box(0);
v_isShared_3728_ = v_isSharedCheck_3734_;
goto v_resetjp_3726_;
}
v_resetjp_3726_:
{
lean_object* v___x_3729_; lean_object* v___x_3730_; lean_object* v___x_3732_; 
v___x_3729_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__7));
v___x_3730_ = lean_string_append(v_pfx_3687_, v___x_3729_);
if (v_isShared_3728_ == 0)
{
lean_ctor_set_tag(v___x_3727_, 0);
lean_ctor_set(v___x_3727_, 0, v___x_3730_);
v___x_3732_ = v___x_3727_;
goto v_reusejp_3731_;
}
else
{
lean_object* v_reuseFailAlloc_3733_; 
v_reuseFailAlloc_3733_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3733_, 0, v___x_3730_);
v___x_3732_ = v_reuseFailAlloc_3733_;
goto v_reusejp_3731_;
}
v_reusejp_3731_:
{
return v___x_3732_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_EnumAttributes_setValue(lean_object* v_00_u03b1_3738_, lean_object* v_attrs_3739_, lean_object* v_env_3740_, lean_object* v_decl_3741_, lean_object* v_val_3742_){
_start:
{
lean_object* v___x_3743_; 
v___x_3743_ = l_Lean_EnumAttributes_setValue___redArg(v_attrs_3739_, v_env_3740_, v_decl_3741_, v_val_3742_);
return v___x_3743_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_2990505691____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3745_; lean_object* v___x_3746_; lean_object* v___x_3747_; 
v___x_3745_ = lean_obj_once(&l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_, &l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2__once, _init_l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_);
v___x_3746_ = lean_st_mk_ref(v___x_3745_);
v___x_3747_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3747_, 0, v___x_3746_);
return v___x_3747_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_2990505691____hygCtx___hyg_2____boxed(lean_object* v_a_3748_){
_start:
{
lean_object* v_res_3749_; 
v_res_3749_ = l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_2990505691____hygCtx___hyg_2_();
return v_res_3749_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerAttributeImplBuilder(lean_object* v_builderId_3752_, lean_object* v_builder_3753_){
_start:
{
lean_object* v___x_3755_; lean_object* v___x_3756_; uint8_t v___x_3757_; 
v___x_3755_ = l_Lean_attributeImplBuilderTableRef;
v___x_3756_ = lean_st_ref_get(v___x_3755_);
v___x_3757_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(v___x_3756_, v_builderId_3752_);
lean_dec(v___x_3756_);
if (v___x_3757_ == 0)
{
lean_object* v___x_3758_; lean_object* v___x_3759_; lean_object* v___x_3760_; lean_object* v___x_3761_; 
v___x_3758_ = lean_st_ref_take(v___x_3755_);
v___x_3759_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1___redArg(v___x_3758_, v_builderId_3752_, v_builder_3753_);
v___x_3760_ = lean_st_ref_set(v___x_3755_, v___x_3759_);
v___x_3761_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3761_, 0, v___x_3760_);
return v___x_3761_;
}
else
{
lean_object* v___x_3762_; lean_object* v___x_3763_; lean_object* v___x_3764_; lean_object* v___x_3765_; lean_object* v___x_3766_; lean_object* v___x_3767_; lean_object* v___x_3768_; 
lean_dec_ref(v_builder_3753_);
v___x_3762_ = ((lean_object*)(l_Lean_registerAttributeImplBuilder___closed__0));
v___x_3763_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_builderId_3752_, v___x_3757_);
v___x_3764_ = lean_string_append(v___x_3762_, v___x_3763_);
lean_dec_ref(v___x_3763_);
v___x_3765_ = ((lean_object*)(l_Lean_registerAttributeImplBuilder___closed__1));
v___x_3766_ = lean_string_append(v___x_3764_, v___x_3765_);
v___x_3767_ = lean_mk_io_user_error(v___x_3766_);
v___x_3768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3768_, 0, v___x_3767_);
return v___x_3768_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerAttributeImplBuilder___boxed(lean_object* v_builderId_3769_, lean_object* v_builder_3770_, lean_object* v_a_3771_){
_start:
{
lean_object* v_res_3772_; 
v_res_3772_ = l_Lean_registerAttributeImplBuilder(v_builderId_3769_, v_builder_3770_);
return v_res_3772_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___redArg(lean_object* v_e_3773_){
_start:
{
if (lean_obj_tag(v_e_3773_) == 0)
{
lean_object* v_a_3775_; lean_object* v___x_3777_; uint8_t v_isShared_3778_; uint8_t v_isSharedCheck_3783_; 
v_a_3775_ = lean_ctor_get(v_e_3773_, 0);
v_isSharedCheck_3783_ = !lean_is_exclusive(v_e_3773_);
if (v_isSharedCheck_3783_ == 0)
{
v___x_3777_ = v_e_3773_;
v_isShared_3778_ = v_isSharedCheck_3783_;
goto v_resetjp_3776_;
}
else
{
lean_inc(v_a_3775_);
lean_dec(v_e_3773_);
v___x_3777_ = lean_box(0);
v_isShared_3778_ = v_isSharedCheck_3783_;
goto v_resetjp_3776_;
}
v_resetjp_3776_:
{
lean_object* v___x_3779_; lean_object* v___x_3781_; 
v___x_3779_ = lean_mk_io_user_error(v_a_3775_);
if (v_isShared_3778_ == 0)
{
lean_ctor_set_tag(v___x_3777_, 1);
lean_ctor_set(v___x_3777_, 0, v___x_3779_);
v___x_3781_ = v___x_3777_;
goto v_reusejp_3780_;
}
else
{
lean_object* v_reuseFailAlloc_3782_; 
v_reuseFailAlloc_3782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3782_, 0, v___x_3779_);
v___x_3781_ = v_reuseFailAlloc_3782_;
goto v_reusejp_3780_;
}
v_reusejp_3780_:
{
return v___x_3781_;
}
}
}
else
{
lean_object* v_a_3784_; lean_object* v___x_3786_; uint8_t v_isShared_3787_; uint8_t v_isSharedCheck_3791_; 
v_a_3784_ = lean_ctor_get(v_e_3773_, 0);
v_isSharedCheck_3791_ = !lean_is_exclusive(v_e_3773_);
if (v_isSharedCheck_3791_ == 0)
{
v___x_3786_ = v_e_3773_;
v_isShared_3787_ = v_isSharedCheck_3791_;
goto v_resetjp_3785_;
}
else
{
lean_inc(v_a_3784_);
lean_dec(v_e_3773_);
v___x_3786_ = lean_box(0);
v_isShared_3787_ = v_isSharedCheck_3791_;
goto v_resetjp_3785_;
}
v_resetjp_3785_:
{
lean_object* v___x_3789_; 
if (v_isShared_3787_ == 0)
{
lean_ctor_set_tag(v___x_3786_, 0);
v___x_3789_ = v___x_3786_;
goto v_reusejp_3788_;
}
else
{
lean_object* v_reuseFailAlloc_3790_; 
v_reuseFailAlloc_3790_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3790_, 0, v_a_3784_);
v___x_3789_ = v_reuseFailAlloc_3790_;
goto v_reusejp_3788_;
}
v_reusejp_3788_:
{
return v___x_3789_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___redArg___boxed(lean_object* v_e_3792_, lean_object* v_a_3793_){
_start:
{
lean_object* v_res_3794_; 
v_res_3794_ = l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___redArg(v_e_3792_);
return v_res_3794_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1(lean_object* v_00_u03b1_3795_, lean_object* v_e_3796_){
_start:
{
lean_object* v___x_3798_; 
v___x_3798_ = l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___redArg(v_e_3796_);
return v___x_3798_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___boxed(lean_object* v_00_u03b1_3799_, lean_object* v_e_3800_, lean_object* v_a_3801_){
_start:
{
lean_object* v_res_3802_; 
v_res_3802_ = l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1(v_00_u03b1_3799_, v_e_3800_);
return v_res_3802_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___redArg(lean_object* v_a_3803_, lean_object* v_x_3804_){
_start:
{
if (lean_obj_tag(v_x_3804_) == 0)
{
lean_object* v___x_3805_; 
v___x_3805_ = lean_box(0);
return v___x_3805_;
}
else
{
lean_object* v_key_3806_; lean_object* v_value_3807_; lean_object* v_tail_3808_; uint8_t v___x_3809_; 
v_key_3806_ = lean_ctor_get(v_x_3804_, 0);
v_value_3807_ = lean_ctor_get(v_x_3804_, 1);
v_tail_3808_ = lean_ctor_get(v_x_3804_, 2);
v___x_3809_ = lean_name_eq(v_key_3806_, v_a_3803_);
if (v___x_3809_ == 0)
{
v_x_3804_ = v_tail_3808_;
goto _start;
}
else
{
lean_object* v___x_3811_; 
lean_inc(v_value_3807_);
v___x_3811_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3811_, 0, v_value_3807_);
return v___x_3811_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___redArg___boxed(lean_object* v_a_3812_, lean_object* v_x_3813_){
_start:
{
lean_object* v_res_3814_; 
v_res_3814_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___redArg(v_a_3812_, v_x_3813_);
lean_dec(v_x_3813_);
lean_dec(v_a_3812_);
return v_res_3814_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(lean_object* v_m_3815_, lean_object* v_a_3816_){
_start:
{
lean_object* v_buckets_3817_; lean_object* v___x_3818_; uint64_t v___y_3820_; 
v_buckets_3817_ = lean_ctor_get(v_m_3815_, 1);
v___x_3818_ = lean_array_get_size(v_buckets_3817_);
if (lean_obj_tag(v_a_3816_) == 0)
{
uint64_t v___x_3834_; 
v___x_3834_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg___closed__0);
v___y_3820_ = v___x_3834_;
goto v___jp_3819_;
}
else
{
uint64_t v_hash_3835_; 
v_hash_3835_ = lean_ctor_get_uint64(v_a_3816_, sizeof(void*)*2);
v___y_3820_ = v_hash_3835_;
goto v___jp_3819_;
}
v___jp_3819_:
{
uint64_t v___x_3821_; uint64_t v___x_3822_; uint64_t v_fold_3823_; uint64_t v___x_3824_; uint64_t v___x_3825_; uint64_t v___x_3826_; size_t v___x_3827_; size_t v___x_3828_; size_t v___x_3829_; size_t v___x_3830_; size_t v___x_3831_; lean_object* v___x_3832_; lean_object* v___x_3833_; 
v___x_3821_ = 32ULL;
v___x_3822_ = lean_uint64_shift_right(v___y_3820_, v___x_3821_);
v_fold_3823_ = lean_uint64_xor(v___y_3820_, v___x_3822_);
v___x_3824_ = 16ULL;
v___x_3825_ = lean_uint64_shift_right(v_fold_3823_, v___x_3824_);
v___x_3826_ = lean_uint64_xor(v_fold_3823_, v___x_3825_);
v___x_3827_ = lean_uint64_to_usize(v___x_3826_);
v___x_3828_ = lean_usize_of_nat(v___x_3818_);
v___x_3829_ = ((size_t)1ULL);
v___x_3830_ = lean_usize_sub(v___x_3828_, v___x_3829_);
v___x_3831_ = lean_usize_land(v___x_3827_, v___x_3830_);
v___x_3832_ = lean_array_uget_borrowed(v_buckets_3817_, v___x_3831_);
v___x_3833_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___redArg(v_a_3816_, v___x_3832_);
return v___x_3833_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg___boxed(lean_object* v_m_3836_, lean_object* v_a_3837_){
_start:
{
lean_object* v_res_3838_; 
v_res_3838_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(v_m_3836_, v_a_3837_);
lean_dec(v_a_3837_);
lean_dec_ref(v_m_3836_);
return v_res_3838_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAttributeImplOfEntry(lean_object* v_e_3840_){
_start:
{
lean_object* v___x_3842_; lean_object* v___x_3843_; lean_object* v_builderId_3844_; lean_object* v_ref_3845_; lean_object* v_args_3846_; lean_object* v___x_3847_; 
v___x_3842_ = l_Lean_attributeImplBuilderTableRef;
v___x_3843_ = lean_st_ref_get(v___x_3842_);
v_builderId_3844_ = lean_ctor_get(v_e_3840_, 0);
lean_inc(v_builderId_3844_);
v_ref_3845_ = lean_ctor_get(v_e_3840_, 1);
lean_inc(v_ref_3845_);
v_args_3846_ = lean_ctor_get(v_e_3840_, 2);
lean_inc(v_args_3846_);
lean_dec_ref(v_e_3840_);
v___x_3847_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(v___x_3843_, v_builderId_3844_);
lean_dec(v___x_3843_);
if (lean_obj_tag(v___x_3847_) == 0)
{
lean_object* v___x_3848_; uint8_t v___x_3849_; lean_object* v___x_3850_; lean_object* v___x_3851_; lean_object* v___x_3852_; lean_object* v___x_3853_; lean_object* v___x_3854_; lean_object* v___x_3855_; 
lean_dec(v_args_3846_);
lean_dec(v_ref_3845_);
v___x_3848_ = ((lean_object*)(l_Lean_mkAttributeImplOfEntry___closed__0));
v___x_3849_ = 1;
v___x_3850_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_builderId_3844_, v___x_3849_);
v___x_3851_ = lean_string_append(v___x_3848_, v___x_3850_);
lean_dec_ref(v___x_3850_);
v___x_3852_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__4));
v___x_3853_ = lean_string_append(v___x_3851_, v___x_3852_);
v___x_3854_ = lean_mk_io_user_error(v___x_3853_);
v___x_3855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3855_, 0, v___x_3854_);
return v___x_3855_;
}
else
{
lean_object* v_val_3856_; lean_object* v___x_3857_; lean_object* v___x_3858_; 
lean_dec(v_builderId_3844_);
v_val_3856_ = lean_ctor_get(v___x_3847_, 0);
lean_inc(v_val_3856_);
lean_dec_ref(v___x_3847_);
v___x_3857_ = lean_apply_2(v_val_3856_, v_ref_3845_, v_args_3846_);
v___x_3858_ = l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___redArg(v___x_3857_);
return v___x_3858_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkAttributeImplOfEntry___boxed(lean_object* v_e_3859_, lean_object* v_a_3860_){
_start:
{
lean_object* v_res_3861_; 
v_res_3861_ = l_Lean_mkAttributeImplOfEntry(v_e_3859_);
return v_res_3861_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0(lean_object* v_00_u03b2_3862_, lean_object* v_m_3863_, lean_object* v_a_3864_){
_start:
{
lean_object* v___x_3865_; 
v___x_3865_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(v_m_3863_, v_a_3864_);
return v___x_3865_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___boxed(lean_object* v_00_u03b2_3866_, lean_object* v_m_3867_, lean_object* v_a_3868_){
_start:
{
lean_object* v_res_3869_; 
v_res_3869_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0(v_00_u03b2_3866_, v_m_3867_, v_a_3868_);
lean_dec(v_a_3868_);
lean_dec_ref(v_m_3867_);
return v_res_3869_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0(lean_object* v_00_u03b2_3870_, lean_object* v_a_3871_, lean_object* v_x_3872_){
_start:
{
lean_object* v___x_3873_; 
v___x_3873_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___redArg(v_a_3871_, v_x_3872_);
return v___x_3873_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3874_, lean_object* v_a_3875_, lean_object* v_x_3876_){
_start:
{
lean_object* v_res_3877_; 
v_res_3877_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0(v_00_u03b2_3874_, v_a_3875_, v_x_3876_);
lean_dec(v_x_3876_);
lean_dec(v_a_3875_);
return v_res_3877_;
}
}
static lean_object* _init_l_Lean_instInhabitedAttributeExtensionState_default___closed__0(void){
_start:
{
lean_object* v___x_3878_; lean_object* v___x_3879_; lean_object* v___x_3880_; 
v___x_3878_ = lean_obj_once(&l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_, &l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2__once, _init_l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_);
v___x_3879_ = lean_box(0);
v___x_3880_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3880_, 0, v___x_3879_);
lean_ctor_set(v___x_3880_, 1, v___x_3878_);
return v___x_3880_;
}
}
static lean_object* _init_l_Lean_instInhabitedAttributeExtensionState_default(void){
_start:
{
lean_object* v___x_3881_; 
v___x_3881_ = lean_obj_once(&l_Lean_instInhabitedAttributeExtensionState_default___closed__0, &l_Lean_instInhabitedAttributeExtensionState_default___closed__0_once, _init_l_Lean_instInhabitedAttributeExtensionState_default___closed__0);
return v___x_3881_;
}
}
static lean_object* _init_l_Lean_instInhabitedAttributeExtensionState(void){
_start:
{
lean_object* v___x_3882_; 
v___x_3882_ = l_Lean_instInhabitedAttributeExtensionState_default;
return v___x_3882_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_AttributeExtension_mkInitial(){
_start:
{
lean_object* v___x_3884_; lean_object* v___x_3885_; lean_object* v___x_3886_; lean_object* v___x_3887_; lean_object* v___x_3888_; 
v___x_3884_ = l_Lean_attributeMapRef;
v___x_3885_ = lean_st_ref_get(v___x_3884_);
v___x_3886_ = lean_box(0);
v___x_3887_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3887_, 0, v___x_3886_);
lean_ctor_set(v___x_3887_, 1, v___x_3885_);
v___x_3888_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3888_, 0, v___x_3887_);
return v___x_3888_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_AttributeExtension_mkInitial___boxed(lean_object* v_a_3889_){
_start:
{
lean_object* v_res_3890_; 
v_res_3890_ = l___private_Lean_Attributes_0__Lean_AttributeExtension_mkInitial();
return v_res_3890_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAttributeImplOfConstantUnsafe(lean_object* v_env_3896_, lean_object* v_opts_3897_, lean_object* v_declName_3898_){
_start:
{
uint8_t v___x_3901_; lean_object* v___x_3902_; 
v___x_3901_ = 0;
lean_inc(v_declName_3898_);
lean_inc_ref(v_env_3896_);
v___x_3902_ = l_Lean_Environment_find_x3f(v_env_3896_, v_declName_3898_, v___x_3901_);
if (lean_obj_tag(v___x_3902_) == 0)
{
lean_object* v___x_3903_; uint8_t v___x_3904_; lean_object* v___x_3905_; lean_object* v___x_3906_; lean_object* v___x_3907_; lean_object* v___x_3908_; lean_object* v___x_3909_; 
lean_dec_ref(v_env_3896_);
v___x_3903_ = ((lean_object*)(l_Lean_mkAttributeImplOfConstantUnsafe___closed__2));
v___x_3904_ = 1;
v___x_3905_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_declName_3898_, v___x_3904_);
v___x_3906_ = lean_string_append(v___x_3903_, v___x_3905_);
lean_dec_ref(v___x_3905_);
v___x_3907_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__4));
v___x_3908_ = lean_string_append(v___x_3906_, v___x_3907_);
v___x_3909_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3909_, 0, v___x_3908_);
return v___x_3909_;
}
else
{
lean_object* v_val_3910_; lean_object* v___x_3911_; 
v_val_3910_ = lean_ctor_get(v___x_3902_, 0);
lean_inc(v_val_3910_);
lean_dec_ref(v___x_3902_);
v___x_3911_ = l_Lean_ConstantInfo_type(v_val_3910_);
lean_dec(v_val_3910_);
if (lean_obj_tag(v___x_3911_) == 4)
{
lean_object* v_declName_3912_; 
v_declName_3912_ = lean_ctor_get(v___x_3911_, 0);
lean_inc(v_declName_3912_);
lean_dec_ref(v___x_3911_);
if (lean_obj_tag(v_declName_3912_) == 1)
{
lean_object* v_pre_3913_; 
v_pre_3913_ = lean_ctor_get(v_declName_3912_, 0);
lean_inc(v_pre_3913_);
if (lean_obj_tag(v_pre_3913_) == 1)
{
lean_object* v_pre_3914_; 
v_pre_3914_ = lean_ctor_get(v_pre_3913_, 0);
if (lean_obj_tag(v_pre_3914_) == 0)
{
lean_object* v_str_3915_; lean_object* v_str_3916_; lean_object* v___x_3917_; uint8_t v___x_3918_; 
v_str_3915_ = lean_ctor_get(v_declName_3912_, 1);
lean_inc_ref(v_str_3915_);
lean_dec_ref(v_declName_3912_);
v_str_3916_ = lean_ctor_get(v_pre_3913_, 1);
lean_inc_ref(v_str_3916_);
lean_dec_ref(v_pre_3913_);
v___x_3917_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__0));
v___x_3918_ = lean_string_dec_eq(v_str_3916_, v___x_3917_);
lean_dec_ref(v_str_3916_);
if (v___x_3918_ == 0)
{
lean_dec_ref(v_str_3915_);
lean_dec(v_declName_3898_);
lean_dec_ref(v_env_3896_);
goto v___jp_3899_;
}
else
{
lean_object* v___x_3919_; uint8_t v___x_3920_; 
v___x_3919_ = ((lean_object*)(l_Lean_mkAttributeImplOfConstantUnsafe___closed__3));
v___x_3920_ = lean_string_dec_eq(v_str_3915_, v___x_3919_);
lean_dec_ref(v_str_3915_);
if (v___x_3920_ == 0)
{
lean_dec(v_declName_3898_);
lean_dec_ref(v_env_3896_);
goto v___jp_3899_;
}
else
{
lean_object* v___x_3921_; 
v___x_3921_ = l_Lean_Environment_evalConst___redArg(v_env_3896_, v_opts_3897_, v_declName_3898_, v___x_3920_);
lean_dec(v_declName_3898_);
lean_dec_ref(v_env_3896_);
return v___x_3921_;
}
}
}
else
{
lean_dec_ref(v_pre_3913_);
lean_dec_ref(v_declName_3912_);
lean_dec(v_declName_3898_);
lean_dec_ref(v_env_3896_);
goto v___jp_3899_;
}
}
else
{
lean_dec(v_pre_3913_);
lean_dec_ref(v_declName_3912_);
lean_dec(v_declName_3898_);
lean_dec_ref(v_env_3896_);
goto v___jp_3899_;
}
}
else
{
lean_dec(v_declName_3912_);
lean_dec(v_declName_3898_);
lean_dec_ref(v_env_3896_);
goto v___jp_3899_;
}
}
else
{
lean_dec_ref(v___x_3911_);
lean_dec(v_declName_3898_);
lean_dec_ref(v_env_3896_);
goto v___jp_3899_;
}
}
v___jp_3899_:
{
lean_object* v___x_3900_; 
v___x_3900_ = ((lean_object*)(l_Lean_mkAttributeImplOfConstantUnsafe___closed__1));
return v___x_3900_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkAttributeImplOfConstantUnsafe___boxed(lean_object* v_env_3922_, lean_object* v_opts_3923_, lean_object* v_declName_3924_){
_start:
{
lean_object* v_res_3925_; 
v_res_3925_ = l_Lean_mkAttributeImplOfConstantUnsafe(v_env_3922_, v_opts_3923_, v_declName_3924_);
lean_dec_ref(v_opts_3923_);
return v_res_3925_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg(lean_object* v_as_3926_, size_t v_i_3927_, size_t v_stop_3928_, lean_object* v_b_3929_){
_start:
{
uint8_t v___x_3931_; 
v___x_3931_ = lean_usize_dec_eq(v_i_3927_, v_stop_3928_);
if (v___x_3931_ == 0)
{
lean_object* v___x_3932_; lean_object* v___x_3933_; 
v___x_3932_ = lean_array_uget_borrowed(v_as_3926_, v_i_3927_);
lean_inc(v___x_3932_);
v___x_3933_ = l_Lean_mkAttributeImplOfEntry(v___x_3932_);
if (lean_obj_tag(v___x_3933_) == 0)
{
lean_object* v_a_3934_; lean_object* v_toAttributeImplCore_3935_; lean_object* v_name_3936_; lean_object* v___x_3937_; size_t v___x_3938_; size_t v___x_3939_; 
v_a_3934_ = lean_ctor_get(v___x_3933_, 0);
lean_inc(v_a_3934_);
lean_dec_ref(v___x_3933_);
v_toAttributeImplCore_3935_ = lean_ctor_get(v_a_3934_, 0);
v_name_3936_ = lean_ctor_get(v_toAttributeImplCore_3935_, 1);
lean_inc(v_name_3936_);
v___x_3937_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1___redArg(v_b_3929_, v_name_3936_, v_a_3934_);
v___x_3938_ = ((size_t)1ULL);
v___x_3939_ = lean_usize_add(v_i_3927_, v___x_3938_);
v_i_3927_ = v___x_3939_;
v_b_3929_ = v___x_3937_;
goto _start;
}
else
{
lean_object* v_a_3941_; lean_object* v___x_3943_; uint8_t v_isShared_3944_; uint8_t v_isSharedCheck_3948_; 
lean_dec_ref(v_b_3929_);
v_a_3941_ = lean_ctor_get(v___x_3933_, 0);
v_isSharedCheck_3948_ = !lean_is_exclusive(v___x_3933_);
if (v_isSharedCheck_3948_ == 0)
{
v___x_3943_ = v___x_3933_;
v_isShared_3944_ = v_isSharedCheck_3948_;
goto v_resetjp_3942_;
}
else
{
lean_inc(v_a_3941_);
lean_dec(v___x_3933_);
v___x_3943_ = lean_box(0);
v_isShared_3944_ = v_isSharedCheck_3948_;
goto v_resetjp_3942_;
}
v_resetjp_3942_:
{
lean_object* v___x_3946_; 
if (v_isShared_3944_ == 0)
{
v___x_3946_ = v___x_3943_;
goto v_reusejp_3945_;
}
else
{
lean_object* v_reuseFailAlloc_3947_; 
v_reuseFailAlloc_3947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3947_, 0, v_a_3941_);
v___x_3946_ = v_reuseFailAlloc_3947_;
goto v_reusejp_3945_;
}
v_reusejp_3945_:
{
return v___x_3946_;
}
}
}
}
else
{
lean_object* v___x_3949_; 
v___x_3949_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3949_, 0, v_b_3929_);
return v___x_3949_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg___boxed(lean_object* v_as_3950_, lean_object* v_i_3951_, lean_object* v_stop_3952_, lean_object* v_b_3953_, lean_object* v___y_3954_){
_start:
{
size_t v_i_boxed_3955_; size_t v_stop_boxed_3956_; lean_object* v_res_3957_; 
v_i_boxed_3955_ = lean_unbox_usize(v_i_3951_);
lean_dec(v_i_3951_);
v_stop_boxed_3956_ = lean_unbox_usize(v_stop_3952_);
lean_dec(v_stop_3952_);
v_res_3957_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg(v_as_3950_, v_i_boxed_3955_, v_stop_boxed_3956_, v_b_3953_);
lean_dec_ref(v_as_3950_);
return v_res_3957_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__1(lean_object* v_as_3958_, size_t v_i_3959_, size_t v_stop_3960_, lean_object* v_b_3961_, lean_object* v___y_3962_){
_start:
{
lean_object* v_a_3965_; lean_object* v___y_3970_; uint8_t v___x_3972_; 
v___x_3972_ = lean_usize_dec_eq(v_i_3959_, v_stop_3960_);
if (v___x_3972_ == 0)
{
lean_object* v___x_3973_; lean_object* v___x_3974_; lean_object* v___x_3975_; uint8_t v___x_3976_; 
v___x_3973_ = lean_array_uget_borrowed(v_as_3958_, v_i_3959_);
v___x_3974_ = lean_unsigned_to_nat(0u);
v___x_3975_ = lean_array_get_size(v___x_3973_);
v___x_3976_ = lean_nat_dec_lt(v___x_3974_, v___x_3975_);
if (v___x_3976_ == 0)
{
v_a_3965_ = v_b_3961_;
goto v___jp_3964_;
}
else
{
uint8_t v___x_3977_; 
v___x_3977_ = lean_nat_dec_le(v___x_3975_, v___x_3975_);
if (v___x_3977_ == 0)
{
if (v___x_3976_ == 0)
{
v_a_3965_ = v_b_3961_;
goto v___jp_3964_;
}
else
{
size_t v___x_3978_; size_t v___x_3979_; lean_object* v___x_3980_; 
v___x_3978_ = ((size_t)0ULL);
v___x_3979_ = lean_usize_of_nat(v___x_3975_);
v___x_3980_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg(v___x_3973_, v___x_3978_, v___x_3979_, v_b_3961_);
v___y_3970_ = v___x_3980_;
goto v___jp_3969_;
}
}
else
{
size_t v___x_3981_; size_t v___x_3982_; lean_object* v___x_3983_; 
v___x_3981_ = ((size_t)0ULL);
v___x_3982_ = lean_usize_of_nat(v___x_3975_);
v___x_3983_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg(v___x_3973_, v___x_3981_, v___x_3982_, v_b_3961_);
v___y_3970_ = v___x_3983_;
goto v___jp_3969_;
}
}
}
else
{
lean_object* v___x_3984_; 
v___x_3984_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3984_, 0, v_b_3961_);
return v___x_3984_;
}
v___jp_3964_:
{
size_t v___x_3966_; size_t v___x_3967_; 
v___x_3966_ = ((size_t)1ULL);
v___x_3967_ = lean_usize_add(v_i_3959_, v___x_3966_);
v_i_3959_ = v___x_3967_;
v_b_3961_ = v_a_3965_;
goto _start;
}
v___jp_3969_:
{
if (lean_obj_tag(v___y_3970_) == 0)
{
lean_object* v_a_3971_; 
v_a_3971_ = lean_ctor_get(v___y_3970_, 0);
lean_inc(v_a_3971_);
lean_dec_ref(v___y_3970_);
v_a_3965_ = v_a_3971_;
goto v___jp_3964_;
}
else
{
return v___y_3970_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__1___boxed(lean_object* v_as_3985_, lean_object* v_i_3986_, lean_object* v_stop_3987_, lean_object* v_b_3988_, lean_object* v___y_3989_, lean_object* v___y_3990_){
_start:
{
size_t v_i_boxed_3991_; size_t v_stop_boxed_3992_; lean_object* v_res_3993_; 
v_i_boxed_3991_ = lean_unbox_usize(v_i_3986_);
lean_dec(v_i_3986_);
v_stop_boxed_3992_ = lean_unbox_usize(v_stop_3987_);
lean_dec(v_stop_3987_);
v_res_3993_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__1(v_as_3985_, v_i_boxed_3991_, v_stop_boxed_3992_, v_b_3988_, v___y_3989_);
lean_dec_ref(v___y_3989_);
lean_dec_ref(v_as_3985_);
return v_res_3993_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_AttributeExtension_addImported(lean_object* v_es_3994_, lean_object* v_a_3995_){
_start:
{
lean_object* v_a_3998_; lean_object* v___y_4003_; lean_object* v___x_4013_; lean_object* v___x_4014_; lean_object* v___x_4015_; lean_object* v___x_4016_; uint8_t v___x_4017_; 
v___x_4013_ = l_Lean_attributeMapRef;
v___x_4014_ = lean_st_ref_get(v___x_4013_);
v___x_4015_ = lean_unsigned_to_nat(0u);
v___x_4016_ = lean_array_get_size(v_es_3994_);
v___x_4017_ = lean_nat_dec_lt(v___x_4015_, v___x_4016_);
if (v___x_4017_ == 0)
{
v_a_3998_ = v___x_4014_;
goto v___jp_3997_;
}
else
{
uint8_t v___x_4018_; 
v___x_4018_ = lean_nat_dec_le(v___x_4016_, v___x_4016_);
if (v___x_4018_ == 0)
{
if (v___x_4017_ == 0)
{
v_a_3998_ = v___x_4014_;
goto v___jp_3997_;
}
else
{
size_t v___x_4019_; size_t v___x_4020_; lean_object* v___x_4021_; 
v___x_4019_ = ((size_t)0ULL);
v___x_4020_ = lean_usize_of_nat(v___x_4016_);
v___x_4021_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__1(v_es_3994_, v___x_4019_, v___x_4020_, v___x_4014_, v_a_3995_);
v___y_4003_ = v___x_4021_;
goto v___jp_4002_;
}
}
else
{
size_t v___x_4022_; size_t v___x_4023_; lean_object* v___x_4024_; 
v___x_4022_ = ((size_t)0ULL);
v___x_4023_ = lean_usize_of_nat(v___x_4016_);
v___x_4024_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__1(v_es_3994_, v___x_4022_, v___x_4023_, v___x_4014_, v_a_3995_);
v___y_4003_ = v___x_4024_;
goto v___jp_4002_;
}
}
v___jp_3997_:
{
lean_object* v___x_3999_; lean_object* v___x_4000_; lean_object* v___x_4001_; 
v___x_3999_ = lean_box(0);
v___x_4000_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4000_, 0, v___x_3999_);
lean_ctor_set(v___x_4000_, 1, v_a_3998_);
v___x_4001_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4001_, 0, v___x_4000_);
return v___x_4001_;
}
v___jp_4002_:
{
if (lean_obj_tag(v___y_4003_) == 0)
{
lean_object* v_a_4004_; 
v_a_4004_ = lean_ctor_get(v___y_4003_, 0);
lean_inc(v_a_4004_);
lean_dec_ref(v___y_4003_);
v_a_3998_ = v_a_4004_;
goto v___jp_3997_;
}
else
{
lean_object* v_a_4005_; lean_object* v___x_4007_; uint8_t v_isShared_4008_; uint8_t v_isSharedCheck_4012_; 
v_a_4005_ = lean_ctor_get(v___y_4003_, 0);
v_isSharedCheck_4012_ = !lean_is_exclusive(v___y_4003_);
if (v_isSharedCheck_4012_ == 0)
{
v___x_4007_ = v___y_4003_;
v_isShared_4008_ = v_isSharedCheck_4012_;
goto v_resetjp_4006_;
}
else
{
lean_inc(v_a_4005_);
lean_dec(v___y_4003_);
v___x_4007_ = lean_box(0);
v_isShared_4008_ = v_isSharedCheck_4012_;
goto v_resetjp_4006_;
}
v_resetjp_4006_:
{
lean_object* v___x_4010_; 
if (v_isShared_4008_ == 0)
{
v___x_4010_ = v___x_4007_;
goto v_reusejp_4009_;
}
else
{
lean_object* v_reuseFailAlloc_4011_; 
v_reuseFailAlloc_4011_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4011_, 0, v_a_4005_);
v___x_4010_ = v_reuseFailAlloc_4011_;
goto v_reusejp_4009_;
}
v_reusejp_4009_:
{
return v___x_4010_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_AttributeExtension_addImported___boxed(lean_object* v_es_4025_, lean_object* v_a_4026_, lean_object* v_a_4027_){
_start:
{
lean_object* v_res_4028_; 
v_res_4028_ = l___private_Lean_Attributes_0__Lean_AttributeExtension_addImported(v_es_4025_, v_a_4026_);
lean_dec_ref(v_a_4026_);
lean_dec_ref(v_es_4025_);
return v_res_4028_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0(lean_object* v_as_4029_, size_t v_i_4030_, size_t v_stop_4031_, lean_object* v_b_4032_, lean_object* v___y_4033_){
_start:
{
lean_object* v___x_4035_; 
v___x_4035_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg(v_as_4029_, v_i_4030_, v_stop_4031_, v_b_4032_);
return v___x_4035_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___boxed(lean_object* v_as_4036_, lean_object* v_i_4037_, lean_object* v_stop_4038_, lean_object* v_b_4039_, lean_object* v___y_4040_, lean_object* v___y_4041_){
_start:
{
size_t v_i_boxed_4042_; size_t v_stop_boxed_4043_; lean_object* v_res_4044_; 
v_i_boxed_4042_ = lean_unbox_usize(v_i_4037_);
lean_dec(v_i_4037_);
v_stop_boxed_4043_ = lean_unbox_usize(v_stop_4038_);
lean_dec(v_stop_4038_);
v_res_4044_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0(v_as_4036_, v_i_boxed_4042_, v_stop_boxed_4043_, v_b_4039_, v___y_4040_);
lean_dec_ref(v___y_4040_);
lean_dec_ref(v_as_4036_);
return v_res_4044_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_addAttrEntry(lean_object* v_s_4045_, lean_object* v_e_4046_){
_start:
{
lean_object* v_snd_4047_; lean_object* v_toAttributeImplCore_4048_; lean_object* v_fst_4049_; lean_object* v___x_4051_; uint8_t v_isShared_4052_; uint8_t v_isSharedCheck_4067_; 
v_snd_4047_ = lean_ctor_get(v_e_4046_, 1);
lean_inc(v_snd_4047_);
v_toAttributeImplCore_4048_ = lean_ctor_get(v_snd_4047_, 0);
v_fst_4049_ = lean_ctor_get(v_e_4046_, 0);
v_isSharedCheck_4067_ = !lean_is_exclusive(v_e_4046_);
if (v_isSharedCheck_4067_ == 0)
{
lean_object* v_unused_4068_; 
v_unused_4068_ = lean_ctor_get(v_e_4046_, 1);
lean_dec(v_unused_4068_);
v___x_4051_ = v_e_4046_;
v_isShared_4052_ = v_isSharedCheck_4067_;
goto v_resetjp_4050_;
}
else
{
lean_inc(v_fst_4049_);
lean_dec(v_e_4046_);
v___x_4051_ = lean_box(0);
v_isShared_4052_ = v_isSharedCheck_4067_;
goto v_resetjp_4050_;
}
v_resetjp_4050_:
{
lean_object* v_newEntries_4053_; lean_object* v_map_4054_; lean_object* v___x_4056_; uint8_t v_isShared_4057_; uint8_t v_isSharedCheck_4066_; 
v_newEntries_4053_ = lean_ctor_get(v_s_4045_, 0);
v_map_4054_ = lean_ctor_get(v_s_4045_, 1);
v_isSharedCheck_4066_ = !lean_is_exclusive(v_s_4045_);
if (v_isSharedCheck_4066_ == 0)
{
v___x_4056_ = v_s_4045_;
v_isShared_4057_ = v_isSharedCheck_4066_;
goto v_resetjp_4055_;
}
else
{
lean_inc(v_map_4054_);
lean_inc(v_newEntries_4053_);
lean_dec(v_s_4045_);
v___x_4056_ = lean_box(0);
v_isShared_4057_ = v_isSharedCheck_4066_;
goto v_resetjp_4055_;
}
v_resetjp_4055_:
{
lean_object* v_name_4058_; lean_object* v___x_4060_; 
v_name_4058_ = lean_ctor_get(v_toAttributeImplCore_4048_, 1);
lean_inc(v_name_4058_);
if (v_isShared_4052_ == 0)
{
lean_ctor_set_tag(v___x_4051_, 1);
lean_ctor_set(v___x_4051_, 1, v_newEntries_4053_);
v___x_4060_ = v___x_4051_;
goto v_reusejp_4059_;
}
else
{
lean_object* v_reuseFailAlloc_4065_; 
v_reuseFailAlloc_4065_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4065_, 0, v_fst_4049_);
lean_ctor_set(v_reuseFailAlloc_4065_, 1, v_newEntries_4053_);
v___x_4060_ = v_reuseFailAlloc_4065_;
goto v_reusejp_4059_;
}
v_reusejp_4059_:
{
lean_object* v___x_4061_; lean_object* v___x_4063_; 
v___x_4061_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1___redArg(v_map_4054_, v_name_4058_, v_snd_4047_);
if (v_isShared_4057_ == 0)
{
lean_ctor_set(v___x_4056_, 1, v___x_4061_);
lean_ctor_set(v___x_4056_, 0, v___x_4060_);
v___x_4063_ = v___x_4056_;
goto v_reusejp_4062_;
}
else
{
lean_object* v_reuseFailAlloc_4064_; 
v_reuseFailAlloc_4064_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4064_, 0, v___x_4060_);
lean_ctor_set(v_reuseFailAlloc_4064_, 1, v___x_4061_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn___lam__0_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(lean_object* v_x_4069_, lean_object* v_s_4070_){
_start:
{
lean_object* v_newEntries_4071_; lean_object* v___x_4072_; lean_object* v___x_4073_; lean_object* v___x_4074_; 
v_newEntries_4071_ = lean_ctor_get(v_s_4070_, 0);
lean_inc(v_newEntries_4071_);
lean_dec_ref(v_s_4070_);
v___x_4072_ = l_List_reverse___redArg(v_newEntries_4071_);
v___x_4073_ = lean_array_mk(v___x_4072_);
lean_inc_ref_n(v___x_4073_, 2);
v___x_4074_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4074_, 0, v___x_4073_);
lean_ctor_set(v___x_4074_, 1, v___x_4073_);
lean_ctor_set(v___x_4074_, 2, v___x_4073_);
return v___x_4074_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn___lam__0_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2____boxed(lean_object* v_x_4075_, lean_object* v_s_4076_){
_start:
{
lean_object* v_res_4077_; 
v_res_4077_ = l___private_Lean_Attributes_0__Lean_initFn___lam__0_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(v_x_4075_, v_s_4076_);
lean_dec_ref(v_x_4075_);
return v_res_4077_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn___lam__1_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(lean_object* v_s_4078_){
_start:
{
lean_object* v_newEntries_4079_; lean_object* v___x_4081_; uint8_t v_isShared_4082_; uint8_t v_isSharedCheck_4090_; 
v_newEntries_4079_ = lean_ctor_get(v_s_4078_, 0);
v_isSharedCheck_4090_ = !lean_is_exclusive(v_s_4078_);
if (v_isSharedCheck_4090_ == 0)
{
lean_object* v_unused_4091_; 
v_unused_4091_ = lean_ctor_get(v_s_4078_, 1);
lean_dec(v_unused_4091_);
v___x_4081_ = v_s_4078_;
v_isShared_4082_ = v_isSharedCheck_4090_;
goto v_resetjp_4080_;
}
else
{
lean_inc(v_newEntries_4079_);
lean_dec(v_s_4078_);
v___x_4081_ = lean_box(0);
v_isShared_4082_ = v_isSharedCheck_4090_;
goto v_resetjp_4080_;
}
v_resetjp_4080_:
{
lean_object* v___x_4083_; lean_object* v___x_4084_; lean_object* v___x_4085_; lean_object* v___x_4086_; lean_object* v___x_4088_; 
v___x_4083_ = ((lean_object*)(l_Lean_registerTagAttribute___lam__2___closed__4));
v___x_4084_ = l_List_lengthTR___redArg(v_newEntries_4079_);
lean_dec(v_newEntries_4079_);
v___x_4085_ = l_Nat_reprFast(v___x_4084_);
v___x_4086_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4086_, 0, v___x_4085_);
if (v_isShared_4082_ == 0)
{
lean_ctor_set_tag(v___x_4081_, 5);
lean_ctor_set(v___x_4081_, 1, v___x_4086_);
lean_ctor_set(v___x_4081_, 0, v___x_4083_);
v___x_4088_ = v___x_4081_;
goto v_reusejp_4087_;
}
else
{
lean_object* v_reuseFailAlloc_4089_; 
v_reuseFailAlloc_4089_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4089_, 0, v___x_4083_);
lean_ctor_set(v_reuseFailAlloc_4089_, 1, v___x_4086_);
v___x_4088_ = v_reuseFailAlloc_4089_;
goto v_reusejp_4087_;
}
v_reusejp_4087_:
{
return v___x_4088_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn___lam__2_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(lean_object* v_s_4092_){
_start:
{
lean_object* v_newEntries_4093_; lean_object* v___x_4094_; lean_object* v___x_4095_; 
v_newEntries_4093_ = lean_ctor_get(v_s_4092_, 0);
lean_inc(v_newEntries_4093_);
lean_dec_ref(v_s_4092_);
v___x_4094_ = l_List_reverse___redArg(v_newEntries_4093_);
v___x_4095_ = lean_array_mk(v___x_4094_);
return v___x_4095_;
}
}
static lean_object* _init_l___private_Lean_Attributes_0__Lean_initFn___closed__7_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4105_; lean_object* v___x_4106_; lean_object* v___f_4107_; lean_object* v___f_4108_; lean_object* v___x_4109_; lean_object* v___x_4110_; lean_object* v___x_4111_; lean_object* v___x_4112_; lean_object* v___x_4113_; 
v___x_4105_ = lean_box(0);
v___x_4106_ = lean_box(2);
v___f_4107_ = ((lean_object*)(l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___f_4108_ = ((lean_object*)(l___private_Lean_Attributes_0__Lean_initFn___closed__0_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___x_4109_ = ((lean_object*)(l___private_Lean_Attributes_0__Lean_initFn___closed__6_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___x_4110_ = ((lean_object*)(l___private_Lean_Attributes_0__Lean_initFn___closed__5_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___x_4111_ = lean_alloc_closure((void*)(l___private_Lean_Attributes_0__Lean_AttributeExtension_mkInitial___boxed), 1, 0);
v___x_4112_ = ((lean_object*)(l___private_Lean_Attributes_0__Lean_initFn___closed__4_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___x_4113_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_4113_, 0, v___x_4112_);
lean_ctor_set(v___x_4113_, 1, v___x_4111_);
lean_ctor_set(v___x_4113_, 2, v___x_4110_);
lean_ctor_set(v___x_4113_, 3, v___x_4109_);
lean_ctor_set(v___x_4113_, 4, v___f_4108_);
lean_ctor_set(v___x_4113_, 5, v___f_4107_);
lean_ctor_set(v___x_4113_, 6, v___x_4106_);
lean_ctor_set(v___x_4113_, 7, v___x_4105_);
return v___x_4113_;
}
}
static lean_object* _init_l___private_Lean_Attributes_0__Lean_initFn___closed__8_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_4114_; lean_object* v___x_4115_; lean_object* v___x_4116_; 
v___f_4114_ = ((lean_object*)(l___private_Lean_Attributes_0__Lean_initFn___closed__2_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___x_4115_ = lean_obj_once(&l___private_Lean_Attributes_0__Lean_initFn___closed__7_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_, &l___private_Lean_Attributes_0__Lean_initFn___closed__7_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2__once, _init_l___private_Lean_Attributes_0__Lean_initFn___closed__7_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_);
v___x_4116_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4116_, 0, v___x_4115_);
lean_ctor_set(v___x_4116_, 1, v___f_4114_);
return v___x_4116_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4118_; lean_object* v___x_4119_; 
v___x_4118_ = lean_obj_once(&l___private_Lean_Attributes_0__Lean_initFn___closed__8_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_, &l___private_Lean_Attributes_0__Lean_initFn___closed__8_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2__once, _init_l___private_Lean_Attributes_0__Lean_initFn___closed__8_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_);
v___x_4119_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_4118_);
return v___x_4119_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2____boxed(lean_object* v_a_4120_){
_start:
{
lean_object* v_res_4121_; 
v_res_4121_ = l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_();
return v_res_4121_;
}
}
LEAN_EXPORT lean_object* lean_is_attribute(lean_object* v_n_4122_){
_start:
{
lean_object* v___x_4124_; lean_object* v___x_4125_; uint8_t v___x_4126_; lean_object* v___x_4127_; lean_object* v___x_4128_; 
v___x_4124_ = l_Lean_attributeMapRef;
v___x_4125_ = lean_st_ref_get(v___x_4124_);
v___x_4126_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(v___x_4125_, v_n_4122_);
lean_dec(v_n_4122_);
lean_dec(v___x_4125_);
v___x_4127_ = lean_box(v___x_4126_);
v___x_4128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4128_, 0, v___x_4127_);
return v___x_4128_;
}
}
LEAN_EXPORT lean_object* l_Lean_isBuiltinAttribute___boxed(lean_object* v_n_4129_, lean_object* v_a_4130_){
_start:
{
lean_object* v_res_4131_; 
v_res_4131_ = lean_is_attribute(v_n_4129_);
return v_res_4131_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_getBuiltinAttributeNames_spec__0(lean_object* v_x_4132_, lean_object* v_x_4133_){
_start:
{
if (lean_obj_tag(v_x_4133_) == 0)
{
return v_x_4132_;
}
else
{
lean_object* v_key_4134_; lean_object* v_tail_4135_; lean_object* v___x_4136_; 
v_key_4134_ = lean_ctor_get(v_x_4133_, 0);
v_tail_4135_ = lean_ctor_get(v_x_4133_, 2);
lean_inc(v_key_4134_);
v___x_4136_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4136_, 0, v_key_4134_);
lean_ctor_set(v___x_4136_, 1, v_x_4132_);
v_x_4132_ = v___x_4136_;
v_x_4133_ = v_tail_4135_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_getBuiltinAttributeNames_spec__0___boxed(lean_object* v_x_4138_, lean_object* v_x_4139_){
_start:
{
lean_object* v_res_4140_; 
v_res_4140_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_getBuiltinAttributeNames_spec__0(v_x_4138_, v_x_4139_);
lean_dec(v_x_4139_);
return v_res_4140_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1(lean_object* v_as_4141_, size_t v_i_4142_, size_t v_stop_4143_, lean_object* v_b_4144_){
_start:
{
uint8_t v___x_4145_; 
v___x_4145_ = lean_usize_dec_eq(v_i_4142_, v_stop_4143_);
if (v___x_4145_ == 0)
{
lean_object* v___x_4146_; lean_object* v___x_4147_; size_t v___x_4148_; size_t v___x_4149_; 
v___x_4146_ = lean_array_uget_borrowed(v_as_4141_, v_i_4142_);
v___x_4147_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_getBuiltinAttributeNames_spec__0(v_b_4144_, v___x_4146_);
v___x_4148_ = ((size_t)1ULL);
v___x_4149_ = lean_usize_add(v_i_4142_, v___x_4148_);
v_i_4142_ = v___x_4149_;
v_b_4144_ = v___x_4147_;
goto _start;
}
else
{
return v_b_4144_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1___boxed(lean_object* v_as_4151_, lean_object* v_i_4152_, lean_object* v_stop_4153_, lean_object* v_b_4154_){
_start:
{
size_t v_i_boxed_4155_; size_t v_stop_boxed_4156_; lean_object* v_res_4157_; 
v_i_boxed_4155_ = lean_unbox_usize(v_i_4152_);
lean_dec(v_i_4152_);
v_stop_boxed_4156_ = lean_unbox_usize(v_stop_4153_);
lean_dec(v_stop_4153_);
v_res_4157_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1(v_as_4151_, v_i_boxed_4155_, v_stop_boxed_4156_, v_b_4154_);
lean_dec_ref(v_as_4151_);
return v_res_4157_;
}
}
LEAN_EXPORT lean_object* l_Lean_getBuiltinAttributeNames(){
_start:
{
lean_object* v___x_4159_; lean_object* v___x_4160_; lean_object* v_buckets_4161_; lean_object* v___x_4162_; lean_object* v___x_4163_; lean_object* v___x_4164_; uint8_t v___x_4165_; 
v___x_4159_ = l_Lean_attributeMapRef;
v___x_4160_ = lean_st_ref_get(v___x_4159_);
v_buckets_4161_ = lean_ctor_get(v___x_4160_, 1);
lean_inc_ref(v_buckets_4161_);
lean_dec(v___x_4160_);
v___x_4162_ = lean_box(0);
v___x_4163_ = lean_unsigned_to_nat(0u);
v___x_4164_ = lean_array_get_size(v_buckets_4161_);
v___x_4165_ = lean_nat_dec_lt(v___x_4163_, v___x_4164_);
if (v___x_4165_ == 0)
{
lean_object* v___x_4166_; 
lean_dec_ref(v_buckets_4161_);
v___x_4166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4166_, 0, v___x_4162_);
return v___x_4166_;
}
else
{
uint8_t v___x_4167_; 
v___x_4167_ = lean_nat_dec_le(v___x_4164_, v___x_4164_);
if (v___x_4167_ == 0)
{
if (v___x_4165_ == 0)
{
lean_object* v___x_4168_; 
lean_dec_ref(v_buckets_4161_);
v___x_4168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4168_, 0, v___x_4162_);
return v___x_4168_;
}
else
{
size_t v___x_4169_; size_t v___x_4170_; lean_object* v___x_4171_; lean_object* v___x_4172_; 
v___x_4169_ = ((size_t)0ULL);
v___x_4170_ = lean_usize_of_nat(v___x_4164_);
v___x_4171_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1(v_buckets_4161_, v___x_4169_, v___x_4170_, v___x_4162_);
lean_dec_ref(v_buckets_4161_);
v___x_4172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4172_, 0, v___x_4171_);
return v___x_4172_;
}
}
else
{
size_t v___x_4173_; size_t v___x_4174_; lean_object* v___x_4175_; lean_object* v___x_4176_; 
v___x_4173_ = ((size_t)0ULL);
v___x_4174_ = lean_usize_of_nat(v___x_4164_);
v___x_4175_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1(v_buckets_4161_, v___x_4173_, v___x_4174_, v___x_4162_);
lean_dec_ref(v_buckets_4161_);
v___x_4176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4176_, 0, v___x_4175_);
return v___x_4176_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getBuiltinAttributeNames___boxed(lean_object* v_a_4177_){
_start:
{
lean_object* v_res_4178_; 
v_res_4178_ = l_Lean_getBuiltinAttributeNames();
return v_res_4178_;
}
}
LEAN_EXPORT lean_object* l_Lean_getBuiltinAttributeImpl(lean_object* v_attrName_4180_){
_start:
{
lean_object* v___x_4182_; lean_object* v___x_4183_; lean_object* v___x_4184_; 
v___x_4182_ = l_Lean_attributeMapRef;
v___x_4183_ = lean_st_ref_get(v___x_4182_);
v___x_4184_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(v___x_4183_, v_attrName_4180_);
lean_dec(v___x_4183_);
if (lean_obj_tag(v___x_4184_) == 0)
{
lean_object* v___x_4185_; uint8_t v___x_4186_; lean_object* v___x_4187_; lean_object* v___x_4188_; lean_object* v___x_4189_; lean_object* v___x_4190_; lean_object* v___x_4191_; lean_object* v___x_4192_; 
v___x_4185_ = ((lean_object*)(l_Lean_getBuiltinAttributeImpl___closed__0));
v___x_4186_ = 1;
v___x_4187_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_attrName_4180_, v___x_4186_);
v___x_4188_ = lean_string_append(v___x_4185_, v___x_4187_);
lean_dec_ref(v___x_4187_);
v___x_4189_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__4));
v___x_4190_ = lean_string_append(v___x_4188_, v___x_4189_);
v___x_4191_ = lean_mk_io_user_error(v___x_4190_);
v___x_4192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4192_, 0, v___x_4191_);
return v___x_4192_;
}
else
{
lean_object* v_val_4193_; lean_object* v___x_4195_; uint8_t v_isShared_4196_; uint8_t v_isSharedCheck_4200_; 
lean_dec(v_attrName_4180_);
v_val_4193_ = lean_ctor_get(v___x_4184_, 0);
v_isSharedCheck_4200_ = !lean_is_exclusive(v___x_4184_);
if (v_isSharedCheck_4200_ == 0)
{
v___x_4195_ = v___x_4184_;
v_isShared_4196_ = v_isSharedCheck_4200_;
goto v_resetjp_4194_;
}
else
{
lean_inc(v_val_4193_);
lean_dec(v___x_4184_);
v___x_4195_ = lean_box(0);
v_isShared_4196_ = v_isSharedCheck_4200_;
goto v_resetjp_4194_;
}
v_resetjp_4194_:
{
lean_object* v___x_4198_; 
if (v_isShared_4196_ == 0)
{
lean_ctor_set_tag(v___x_4195_, 0);
v___x_4198_ = v___x_4195_;
goto v_reusejp_4197_;
}
else
{
lean_object* v_reuseFailAlloc_4199_; 
v_reuseFailAlloc_4199_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4199_, 0, v_val_4193_);
v___x_4198_ = v_reuseFailAlloc_4199_;
goto v_reusejp_4197_;
}
v_reusejp_4197_:
{
return v___x_4198_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getBuiltinAttributeImpl___boxed(lean_object* v_attrName_4201_, lean_object* v_a_4202_){
_start:
{
lean_object* v_res_4203_; 
v_res_4203_ = l_Lean_getBuiltinAttributeImpl(v_attrName_4201_);
return v_res_4203_;
}
}
LEAN_EXPORT lean_object* lean_attribute_application_time(lean_object* v_n_4204_){
_start:
{
lean_object* v___x_4206_; 
v___x_4206_ = l_Lean_getBuiltinAttributeImpl(v_n_4204_);
if (lean_obj_tag(v___x_4206_) == 0)
{
lean_object* v_a_4207_; lean_object* v___x_4209_; uint8_t v_isShared_4210_; uint8_t v_isSharedCheck_4217_; 
v_a_4207_ = lean_ctor_get(v___x_4206_, 0);
v_isSharedCheck_4217_ = !lean_is_exclusive(v___x_4206_);
if (v_isSharedCheck_4217_ == 0)
{
v___x_4209_ = v___x_4206_;
v_isShared_4210_ = v_isSharedCheck_4217_;
goto v_resetjp_4208_;
}
else
{
lean_inc(v_a_4207_);
lean_dec(v___x_4206_);
v___x_4209_ = lean_box(0);
v_isShared_4210_ = v_isSharedCheck_4217_;
goto v_resetjp_4208_;
}
v_resetjp_4208_:
{
lean_object* v_toAttributeImplCore_4211_; uint8_t v_applicationTime_4212_; lean_object* v___x_4213_; lean_object* v___x_4215_; 
v_toAttributeImplCore_4211_ = lean_ctor_get(v_a_4207_, 0);
lean_inc_ref(v_toAttributeImplCore_4211_);
lean_dec(v_a_4207_);
v_applicationTime_4212_ = lean_ctor_get_uint8(v_toAttributeImplCore_4211_, sizeof(void*)*3);
lean_dec_ref(v_toAttributeImplCore_4211_);
v___x_4213_ = lean_box(v_applicationTime_4212_);
if (v_isShared_4210_ == 0)
{
lean_ctor_set(v___x_4209_, 0, v___x_4213_);
v___x_4215_ = v___x_4209_;
goto v_reusejp_4214_;
}
else
{
lean_object* v_reuseFailAlloc_4216_; 
v_reuseFailAlloc_4216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4216_, 0, v___x_4213_);
v___x_4215_ = v_reuseFailAlloc_4216_;
goto v_reusejp_4214_;
}
v_reusejp_4214_:
{
return v___x_4215_;
}
}
}
else
{
lean_object* v_a_4218_; lean_object* v___x_4220_; uint8_t v_isShared_4221_; uint8_t v_isSharedCheck_4225_; 
v_a_4218_ = lean_ctor_get(v___x_4206_, 0);
v_isSharedCheck_4225_ = !lean_is_exclusive(v___x_4206_);
if (v_isSharedCheck_4225_ == 0)
{
v___x_4220_ = v___x_4206_;
v_isShared_4221_ = v_isSharedCheck_4225_;
goto v_resetjp_4219_;
}
else
{
lean_inc(v_a_4218_);
lean_dec(v___x_4206_);
v___x_4220_ = lean_box(0);
v_isShared_4221_ = v_isSharedCheck_4225_;
goto v_resetjp_4219_;
}
v_resetjp_4219_:
{
lean_object* v___x_4223_; 
if (v_isShared_4221_ == 0)
{
v___x_4223_ = v___x_4220_;
goto v_reusejp_4222_;
}
else
{
lean_object* v_reuseFailAlloc_4224_; 
v_reuseFailAlloc_4224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4224_, 0, v_a_4218_);
v___x_4223_ = v_reuseFailAlloc_4224_;
goto v_reusejp_4222_;
}
v_reusejp_4222_:
{
return v___x_4223_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getBuiltinAttributeApplicationTime___boxed(lean_object* v_n_4226_, lean_object* v_a_4227_){
_start:
{
lean_object* v_res_4228_; 
v_res_4228_ = lean_attribute_application_time(v_n_4226_);
return v_res_4228_;
}
}
LEAN_EXPORT uint8_t l_Lean_isAttribute(lean_object* v_env_4229_, lean_object* v_attrName_4230_){
_start:
{
lean_object* v___x_4231_; lean_object* v_toEnvExtension_4232_; lean_object* v_asyncMode_4233_; lean_object* v___x_4234_; lean_object* v___x_4235_; lean_object* v___x_4236_; lean_object* v_map_4237_; uint8_t v___x_4238_; 
v___x_4231_ = l_Lean_attributeExtension;
v_toEnvExtension_4232_ = lean_ctor_get(v___x_4231_, 0);
v_asyncMode_4233_ = lean_ctor_get(v_toEnvExtension_4232_, 2);
v___x_4234_ = l_Lean_instInhabitedAttributeExtensionState_default;
v___x_4235_ = lean_box(0);
v___x_4236_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_4234_, v___x_4231_, v_env_4229_, v_asyncMode_4233_, v___x_4235_);
v_map_4237_ = lean_ctor_get(v___x_4236_, 1);
lean_inc_ref(v_map_4237_);
lean_dec(v___x_4236_);
v___x_4238_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(v_map_4237_, v_attrName_4230_);
lean_dec_ref(v_map_4237_);
return v___x_4238_;
}
}
LEAN_EXPORT lean_object* l_Lean_isAttribute___boxed(lean_object* v_env_4239_, lean_object* v_attrName_4240_){
_start:
{
uint8_t v_res_4241_; lean_object* v_r_4242_; 
v_res_4241_ = l_Lean_isAttribute(v_env_4239_, v_attrName_4240_);
lean_dec(v_attrName_4240_);
v_r_4242_ = lean_box(v_res_4241_);
return v_r_4242_;
}
}
LEAN_EXPORT lean_object* l_Lean_getAttributeNames(lean_object* v_env_4243_){
_start:
{
lean_object* v___x_4244_; lean_object* v_toEnvExtension_4245_; lean_object* v_asyncMode_4246_; lean_object* v___x_4247_; lean_object* v___x_4248_; lean_object* v___x_4249_; lean_object* v_map_4250_; lean_object* v_buckets_4251_; lean_object* v___x_4252_; lean_object* v___x_4253_; lean_object* v___x_4254_; uint8_t v___x_4255_; 
v___x_4244_ = l_Lean_attributeExtension;
v_toEnvExtension_4245_ = lean_ctor_get(v___x_4244_, 0);
v_asyncMode_4246_ = lean_ctor_get(v_toEnvExtension_4245_, 2);
v___x_4247_ = l_Lean_instInhabitedAttributeExtensionState_default;
v___x_4248_ = lean_box(0);
v___x_4249_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_4247_, v___x_4244_, v_env_4243_, v_asyncMode_4246_, v___x_4248_);
v_map_4250_ = lean_ctor_get(v___x_4249_, 1);
lean_inc_ref(v_map_4250_);
lean_dec(v___x_4249_);
v_buckets_4251_ = lean_ctor_get(v_map_4250_, 1);
lean_inc_ref(v_buckets_4251_);
lean_dec_ref(v_map_4250_);
v___x_4252_ = lean_box(0);
v___x_4253_ = lean_unsigned_to_nat(0u);
v___x_4254_ = lean_array_get_size(v_buckets_4251_);
v___x_4255_ = lean_nat_dec_lt(v___x_4253_, v___x_4254_);
if (v___x_4255_ == 0)
{
lean_dec_ref(v_buckets_4251_);
return v___x_4252_;
}
else
{
uint8_t v___x_4256_; 
v___x_4256_ = lean_nat_dec_le(v___x_4254_, v___x_4254_);
if (v___x_4256_ == 0)
{
if (v___x_4255_ == 0)
{
lean_dec_ref(v_buckets_4251_);
return v___x_4252_;
}
else
{
size_t v___x_4257_; size_t v___x_4258_; lean_object* v___x_4259_; 
v___x_4257_ = ((size_t)0ULL);
v___x_4258_ = lean_usize_of_nat(v___x_4254_);
v___x_4259_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1(v_buckets_4251_, v___x_4257_, v___x_4258_, v___x_4252_);
lean_dec_ref(v_buckets_4251_);
return v___x_4259_;
}
}
else
{
size_t v___x_4260_; size_t v___x_4261_; lean_object* v___x_4262_; 
v___x_4260_ = ((size_t)0ULL);
v___x_4261_ = lean_usize_of_nat(v___x_4254_);
v___x_4262_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1(v_buckets_4251_, v___x_4260_, v___x_4261_, v___x_4252_);
lean_dec_ref(v_buckets_4251_);
return v___x_4262_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getAttributeImpl(lean_object* v_env_4263_, lean_object* v_attrName_4264_){
_start:
{
lean_object* v___x_4265_; lean_object* v_toEnvExtension_4266_; lean_object* v_asyncMode_4267_; lean_object* v___x_4268_; lean_object* v___x_4269_; lean_object* v___x_4270_; lean_object* v_map_4271_; lean_object* v___x_4272_; 
v___x_4265_ = l_Lean_attributeExtension;
v_toEnvExtension_4266_ = lean_ctor_get(v___x_4265_, 0);
v_asyncMode_4267_ = lean_ctor_get(v_toEnvExtension_4266_, 2);
v___x_4268_ = l_Lean_instInhabitedAttributeExtensionState_default;
v___x_4269_ = lean_box(0);
v___x_4270_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_4268_, v___x_4265_, v_env_4263_, v_asyncMode_4267_, v___x_4269_);
v_map_4271_ = lean_ctor_get(v___x_4270_, 1);
lean_inc_ref(v_map_4271_);
lean_dec(v___x_4270_);
v___x_4272_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(v_map_4271_, v_attrName_4264_);
lean_dec_ref(v_map_4271_);
if (lean_obj_tag(v___x_4272_) == 0)
{
lean_object* v___x_4273_; uint8_t v___x_4274_; lean_object* v___x_4275_; lean_object* v___x_4276_; lean_object* v___x_4277_; lean_object* v___x_4278_; lean_object* v___x_4279_; 
v___x_4273_ = ((lean_object*)(l_Lean_getBuiltinAttributeImpl___closed__0));
v___x_4274_ = 1;
v___x_4275_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_attrName_4264_, v___x_4274_);
v___x_4276_ = lean_string_append(v___x_4273_, v___x_4275_);
lean_dec_ref(v___x_4275_);
v___x_4277_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__4));
v___x_4278_ = lean_string_append(v___x_4276_, v___x_4277_);
v___x_4279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4279_, 0, v___x_4278_);
return v___x_4279_;
}
else
{
lean_object* v_val_4280_; lean_object* v___x_4282_; uint8_t v_isShared_4283_; uint8_t v_isSharedCheck_4287_; 
lean_dec(v_attrName_4264_);
v_val_4280_ = lean_ctor_get(v___x_4272_, 0);
v_isSharedCheck_4287_ = !lean_is_exclusive(v___x_4272_);
if (v_isSharedCheck_4287_ == 0)
{
v___x_4282_ = v___x_4272_;
v_isShared_4283_ = v_isSharedCheck_4287_;
goto v_resetjp_4281_;
}
else
{
lean_inc(v_val_4280_);
lean_dec(v___x_4272_);
v___x_4282_ = lean_box(0);
v_isShared_4283_ = v_isSharedCheck_4287_;
goto v_resetjp_4281_;
}
v_resetjp_4281_:
{
lean_object* v___x_4285_; 
if (v_isShared_4283_ == 0)
{
v___x_4285_ = v___x_4282_;
goto v_reusejp_4284_;
}
else
{
lean_object* v_reuseFailAlloc_4286_; 
v_reuseFailAlloc_4286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4286_, 0, v_val_4280_);
v___x_4285_ = v_reuseFailAlloc_4286_;
goto v_reusejp_4284_;
}
v_reusejp_4284_:
{
return v___x_4285_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerAttributeOfBuilder(lean_object* v_env_4288_, lean_object* v_builderId_4289_, lean_object* v_ref_4290_, lean_object* v_args_4291_){
_start:
{
lean_object* v_entry_4293_; lean_object* v___x_4294_; 
v_entry_4293_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_entry_4293_, 0, v_builderId_4289_);
lean_ctor_set(v_entry_4293_, 1, v_ref_4290_);
lean_ctor_set(v_entry_4293_, 2, v_args_4291_);
lean_inc_ref(v_entry_4293_);
v___x_4294_ = l_Lean_mkAttributeImplOfEntry(v_entry_4293_);
if (lean_obj_tag(v___x_4294_) == 0)
{
lean_object* v_a_4295_; lean_object* v___x_4297_; uint8_t v_isShared_4298_; uint8_t v_isSharedCheck_4320_; 
v_a_4295_ = lean_ctor_get(v___x_4294_, 0);
v_isSharedCheck_4320_ = !lean_is_exclusive(v___x_4294_);
if (v_isSharedCheck_4320_ == 0)
{
v___x_4297_ = v___x_4294_;
v_isShared_4298_ = v_isSharedCheck_4320_;
goto v_resetjp_4296_;
}
else
{
lean_inc(v_a_4295_);
lean_dec(v___x_4294_);
v___x_4297_ = lean_box(0);
v_isShared_4298_ = v_isSharedCheck_4320_;
goto v_resetjp_4296_;
}
v_resetjp_4296_:
{
lean_object* v_toAttributeImplCore_4299_; lean_object* v_name_4300_; uint8_t v___x_4301_; 
v_toAttributeImplCore_4299_ = lean_ctor_get(v_a_4295_, 0);
v_name_4300_ = lean_ctor_get(v_toAttributeImplCore_4299_, 1);
lean_inc_ref(v_env_4288_);
v___x_4301_ = l_Lean_isAttribute(v_env_4288_, v_name_4300_);
if (v___x_4301_ == 0)
{
lean_object* v___x_4302_; lean_object* v_toEnvExtension_4303_; lean_object* v_asyncMode_4304_; lean_object* v___x_4305_; lean_object* v___x_4306_; lean_object* v___x_4307_; lean_object* v___x_4309_; 
v___x_4302_ = l_Lean_attributeExtension;
v_toEnvExtension_4303_ = lean_ctor_get(v___x_4302_, 0);
v_asyncMode_4304_ = lean_ctor_get(v_toEnvExtension_4303_, 2);
v___x_4305_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4305_, 0, v_entry_4293_);
lean_ctor_set(v___x_4305_, 1, v_a_4295_);
v___x_4306_ = lean_box(0);
v___x_4307_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_4302_, v_env_4288_, v___x_4305_, v_asyncMode_4304_, v___x_4306_);
if (v_isShared_4298_ == 0)
{
lean_ctor_set(v___x_4297_, 0, v___x_4307_);
v___x_4309_ = v___x_4297_;
goto v_reusejp_4308_;
}
else
{
lean_object* v_reuseFailAlloc_4310_; 
v_reuseFailAlloc_4310_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4310_, 0, v___x_4307_);
v___x_4309_ = v_reuseFailAlloc_4310_;
goto v_reusejp_4308_;
}
v_reusejp_4308_:
{
return v___x_4309_;
}
}
else
{
lean_object* v___x_4311_; lean_object* v___x_4312_; lean_object* v___x_4313_; lean_object* v___x_4314_; lean_object* v___x_4315_; lean_object* v___x_4316_; lean_object* v___x_4318_; 
lean_inc(v_name_4300_);
lean_dec(v_a_4295_);
lean_dec_ref(v_entry_4293_);
lean_dec_ref(v_env_4288_);
v___x_4311_ = ((lean_object*)(l_Lean_registerBuiltinAttribute___closed__2));
v___x_4312_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_4300_, v___x_4301_);
v___x_4313_ = lean_string_append(v___x_4311_, v___x_4312_);
lean_dec_ref(v___x_4312_);
v___x_4314_ = ((lean_object*)(l_Lean_registerBuiltinAttribute___closed__3));
v___x_4315_ = lean_string_append(v___x_4313_, v___x_4314_);
v___x_4316_ = lean_mk_io_user_error(v___x_4315_);
if (v_isShared_4298_ == 0)
{
lean_ctor_set_tag(v___x_4297_, 1);
lean_ctor_set(v___x_4297_, 0, v___x_4316_);
v___x_4318_ = v___x_4297_;
goto v_reusejp_4317_;
}
else
{
lean_object* v_reuseFailAlloc_4319_; 
v_reuseFailAlloc_4319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4319_, 0, v___x_4316_);
v___x_4318_ = v_reuseFailAlloc_4319_;
goto v_reusejp_4317_;
}
v_reusejp_4317_:
{
return v___x_4318_;
}
}
}
}
else
{
lean_object* v_a_4321_; lean_object* v___x_4323_; uint8_t v_isShared_4324_; uint8_t v_isSharedCheck_4328_; 
lean_dec_ref(v_entry_4293_);
lean_dec_ref(v_env_4288_);
v_a_4321_ = lean_ctor_get(v___x_4294_, 0);
v_isSharedCheck_4328_ = !lean_is_exclusive(v___x_4294_);
if (v_isSharedCheck_4328_ == 0)
{
v___x_4323_ = v___x_4294_;
v_isShared_4324_ = v_isSharedCheck_4328_;
goto v_resetjp_4322_;
}
else
{
lean_inc(v_a_4321_);
lean_dec(v___x_4294_);
v___x_4323_ = lean_box(0);
v_isShared_4324_ = v_isSharedCheck_4328_;
goto v_resetjp_4322_;
}
v_resetjp_4322_:
{
lean_object* v___x_4326_; 
if (v_isShared_4324_ == 0)
{
v___x_4326_ = v___x_4323_;
goto v_reusejp_4325_;
}
else
{
lean_object* v_reuseFailAlloc_4327_; 
v_reuseFailAlloc_4327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4327_, 0, v_a_4321_);
v___x_4326_ = v_reuseFailAlloc_4327_;
goto v_reusejp_4325_;
}
v_reusejp_4325_:
{
return v___x_4326_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerAttributeOfBuilder___boxed(lean_object* v_env_4329_, lean_object* v_builderId_4330_, lean_object* v_ref_4331_, lean_object* v_args_4332_, lean_object* v_a_4333_){
_start:
{
lean_object* v_res_4334_; 
v_res_4334_ = l_Lean_registerAttributeOfBuilder(v_env_4329_, v_builderId_4330_, v_ref_4331_, v_args_4332_);
return v_res_4334_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg(lean_object* v_x_4335_, lean_object* v___y_4336_, lean_object* v___y_4337_){
_start:
{
if (lean_obj_tag(v_x_4335_) == 0)
{
lean_object* v_a_4339_; lean_object* v___x_4340_; lean_object* v___x_4341_; 
v_a_4339_ = lean_ctor_get(v_x_4335_, 0);
lean_inc(v_a_4339_);
lean_dec_ref(v_x_4335_);
v___x_4340_ = l_Lean_stringToMessageData(v_a_4339_);
v___x_4341_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_4340_, v___y_4336_, v___y_4337_);
return v___x_4341_;
}
else
{
lean_object* v_a_4342_; lean_object* v___x_4344_; uint8_t v_isShared_4345_; uint8_t v_isSharedCheck_4349_; 
v_a_4342_ = lean_ctor_get(v_x_4335_, 0);
v_isSharedCheck_4349_ = !lean_is_exclusive(v_x_4335_);
if (v_isSharedCheck_4349_ == 0)
{
v___x_4344_ = v_x_4335_;
v_isShared_4345_ = v_isSharedCheck_4349_;
goto v_resetjp_4343_;
}
else
{
lean_inc(v_a_4342_);
lean_dec(v_x_4335_);
v___x_4344_ = lean_box(0);
v_isShared_4345_ = v_isSharedCheck_4349_;
goto v_resetjp_4343_;
}
v_resetjp_4343_:
{
lean_object* v___x_4347_; 
if (v_isShared_4345_ == 0)
{
lean_ctor_set_tag(v___x_4344_, 0);
v___x_4347_ = v___x_4344_;
goto v_reusejp_4346_;
}
else
{
lean_object* v_reuseFailAlloc_4348_; 
v_reuseFailAlloc_4348_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4348_, 0, v_a_4342_);
v___x_4347_ = v_reuseFailAlloc_4348_;
goto v_reusejp_4346_;
}
v_reusejp_4346_:
{
return v___x_4347_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg___boxed(lean_object* v_x_4350_, lean_object* v___y_4351_, lean_object* v___y_4352_, lean_object* v___y_4353_){
_start:
{
lean_object* v_res_4354_; 
v_res_4354_ = l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg(v_x_4350_, v___y_4351_, v___y_4352_);
lean_dec(v___y_4352_);
lean_dec_ref(v___y_4351_);
return v_res_4354_;
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_add(lean_object* v_declName_4355_, lean_object* v_attrName_4356_, lean_object* v_stx_4357_, uint8_t v_kind_4358_, lean_object* v_a_4359_, lean_object* v_a_4360_){
_start:
{
lean_object* v___x_4362_; lean_object* v_env_4363_; lean_object* v___x_4364_; lean_object* v___x_4365_; 
v___x_4362_ = lean_st_ref_get(v_a_4360_);
v_env_4363_ = lean_ctor_get(v___x_4362_, 0);
lean_inc_ref(v_env_4363_);
lean_dec(v___x_4362_);
v___x_4364_ = l_Lean_getAttributeImpl(v_env_4363_, v_attrName_4356_);
v___x_4365_ = l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg(v___x_4364_, v_a_4359_, v_a_4360_);
if (lean_obj_tag(v___x_4365_) == 0)
{
lean_object* v_a_4366_; lean_object* v_add_4367_; lean_object* v___x_4368_; lean_object* v___x_4369_; 
v_a_4366_ = lean_ctor_get(v___x_4365_, 0);
lean_inc(v_a_4366_);
lean_dec_ref(v___x_4365_);
v_add_4367_ = lean_ctor_get(v_a_4366_, 1);
lean_inc_ref(v_add_4367_);
lean_dec(v_a_4366_);
v___x_4368_ = lean_box(v_kind_4358_);
lean_inc(v_a_4360_);
lean_inc_ref(v_a_4359_);
v___x_4369_ = lean_apply_6(v_add_4367_, v_declName_4355_, v_stx_4357_, v___x_4368_, v_a_4359_, v_a_4360_, lean_box(0));
return v___x_4369_;
}
else
{
lean_object* v_a_4370_; lean_object* v___x_4372_; uint8_t v_isShared_4373_; uint8_t v_isSharedCheck_4377_; 
lean_dec(v_stx_4357_);
lean_dec(v_declName_4355_);
v_a_4370_ = lean_ctor_get(v___x_4365_, 0);
v_isSharedCheck_4377_ = !lean_is_exclusive(v___x_4365_);
if (v_isSharedCheck_4377_ == 0)
{
v___x_4372_ = v___x_4365_;
v_isShared_4373_ = v_isSharedCheck_4377_;
goto v_resetjp_4371_;
}
else
{
lean_inc(v_a_4370_);
lean_dec(v___x_4365_);
v___x_4372_ = lean_box(0);
v_isShared_4373_ = v_isSharedCheck_4377_;
goto v_resetjp_4371_;
}
v_resetjp_4371_:
{
lean_object* v___x_4375_; 
if (v_isShared_4373_ == 0)
{
v___x_4375_ = v___x_4372_;
goto v_reusejp_4374_;
}
else
{
lean_object* v_reuseFailAlloc_4376_; 
v_reuseFailAlloc_4376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4376_, 0, v_a_4370_);
v___x_4375_ = v_reuseFailAlloc_4376_;
goto v_reusejp_4374_;
}
v_reusejp_4374_:
{
return v___x_4375_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_add___boxed(lean_object* v_declName_4378_, lean_object* v_attrName_4379_, lean_object* v_stx_4380_, lean_object* v_kind_4381_, lean_object* v_a_4382_, lean_object* v_a_4383_, lean_object* v_a_4384_){
_start:
{
uint8_t v_kind_boxed_4385_; lean_object* v_res_4386_; 
v_kind_boxed_4385_ = lean_unbox(v_kind_4381_);
v_res_4386_ = l_Lean_Attribute_add(v_declName_4378_, v_attrName_4379_, v_stx_4380_, v_kind_boxed_4385_, v_a_4382_, v_a_4383_);
lean_dec(v_a_4383_);
lean_dec_ref(v_a_4382_);
return v_res_4386_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0(lean_object* v_00_u03b1_4387_, lean_object* v_x_4388_, lean_object* v___y_4389_, lean_object* v___y_4390_){
_start:
{
lean_object* v___x_4392_; 
v___x_4392_ = l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg(v_x_4388_, v___y_4389_, v___y_4390_);
return v___x_4392_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___boxed(lean_object* v_00_u03b1_4393_, lean_object* v_x_4394_, lean_object* v___y_4395_, lean_object* v___y_4396_, lean_object* v___y_4397_){
_start:
{
lean_object* v_res_4398_; 
v_res_4398_ = l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0(v_00_u03b1_4393_, v_x_4394_, v___y_4395_, v___y_4396_);
lean_dec(v___y_4396_);
lean_dec_ref(v___y_4395_);
return v_res_4398_;
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_erase(lean_object* v_declName_4399_, lean_object* v_attrName_4400_, lean_object* v_a_4401_, lean_object* v_a_4402_){
_start:
{
lean_object* v___x_4404_; lean_object* v_env_4405_; lean_object* v___x_4406_; lean_object* v___x_4407_; 
v___x_4404_ = lean_st_ref_get(v_a_4402_);
v_env_4405_ = lean_ctor_get(v___x_4404_, 0);
lean_inc_ref(v_env_4405_);
lean_dec(v___x_4404_);
v___x_4406_ = l_Lean_getAttributeImpl(v_env_4405_, v_attrName_4400_);
v___x_4407_ = l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg(v___x_4406_, v_a_4401_, v_a_4402_);
if (lean_obj_tag(v___x_4407_) == 0)
{
lean_object* v_a_4408_; lean_object* v_erase_4409_; lean_object* v___x_4410_; 
v_a_4408_ = lean_ctor_get(v___x_4407_, 0);
lean_inc(v_a_4408_);
lean_dec_ref(v___x_4407_);
v_erase_4409_ = lean_ctor_get(v_a_4408_, 2);
lean_inc_ref(v_erase_4409_);
lean_dec(v_a_4408_);
lean_inc(v_a_4402_);
lean_inc_ref(v_a_4401_);
v___x_4410_ = lean_apply_4(v_erase_4409_, v_declName_4399_, v_a_4401_, v_a_4402_, lean_box(0));
return v___x_4410_;
}
else
{
lean_object* v_a_4411_; lean_object* v___x_4413_; uint8_t v_isShared_4414_; uint8_t v_isSharedCheck_4418_; 
lean_dec(v_declName_4399_);
v_a_4411_ = lean_ctor_get(v___x_4407_, 0);
v_isSharedCheck_4418_ = !lean_is_exclusive(v___x_4407_);
if (v_isSharedCheck_4418_ == 0)
{
v___x_4413_ = v___x_4407_;
v_isShared_4414_ = v_isSharedCheck_4418_;
goto v_resetjp_4412_;
}
else
{
lean_inc(v_a_4411_);
lean_dec(v___x_4407_);
v___x_4413_ = lean_box(0);
v_isShared_4414_ = v_isSharedCheck_4418_;
goto v_resetjp_4412_;
}
v_resetjp_4412_:
{
lean_object* v___x_4416_; 
if (v_isShared_4414_ == 0)
{
v___x_4416_ = v___x_4413_;
goto v_reusejp_4415_;
}
else
{
lean_object* v_reuseFailAlloc_4417_; 
v_reuseFailAlloc_4417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4417_, 0, v_a_4411_);
v___x_4416_ = v_reuseFailAlloc_4417_;
goto v_reusejp_4415_;
}
v_reusejp_4415_:
{
return v___x_4416_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_erase___boxed(lean_object* v_declName_4419_, lean_object* v_attrName_4420_, lean_object* v_a_4421_, lean_object* v_a_4422_, lean_object* v_a_4423_){
_start:
{
lean_object* v_res_4424_; 
v_res_4424_ = l_Lean_Attribute_erase(v_declName_4419_, v_attrName_4420_, v_a_4421_, v_a_4422_);
lean_dec(v_a_4422_);
lean_dec_ref(v_a_4421_);
return v_res_4424_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_updateEnvAttributesImpl_spec__0(lean_object* v_x_4425_, lean_object* v_x_4426_){
_start:
{
if (lean_obj_tag(v_x_4426_) == 0)
{
return v_x_4425_;
}
else
{
lean_object* v_key_4427_; lean_object* v_value_4428_; lean_object* v_tail_4429_; lean_object* v_newEntries_4430_; lean_object* v_map_4431_; uint8_t v___x_4432_; 
v_key_4427_ = lean_ctor_get(v_x_4426_, 0);
lean_inc(v_key_4427_);
v_value_4428_ = lean_ctor_get(v_x_4426_, 1);
lean_inc(v_value_4428_);
v_tail_4429_ = lean_ctor_get(v_x_4426_, 2);
lean_inc(v_tail_4429_);
lean_dec_ref(v_x_4426_);
v_newEntries_4430_ = lean_ctor_get(v_x_4425_, 0);
v_map_4431_ = lean_ctor_get(v_x_4425_, 1);
v___x_4432_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(v_map_4431_, v_key_4427_);
if (v___x_4432_ == 0)
{
lean_object* v___x_4434_; uint8_t v_isShared_4435_; uint8_t v_isSharedCheck_4441_; 
lean_inc_ref(v_map_4431_);
lean_inc(v_newEntries_4430_);
v_isSharedCheck_4441_ = !lean_is_exclusive(v_x_4425_);
if (v_isSharedCheck_4441_ == 0)
{
lean_object* v_unused_4442_; lean_object* v_unused_4443_; 
v_unused_4442_ = lean_ctor_get(v_x_4425_, 1);
lean_dec(v_unused_4442_);
v_unused_4443_ = lean_ctor_get(v_x_4425_, 0);
lean_dec(v_unused_4443_);
v___x_4434_ = v_x_4425_;
v_isShared_4435_ = v_isSharedCheck_4441_;
goto v_resetjp_4433_;
}
else
{
lean_dec(v_x_4425_);
v___x_4434_ = lean_box(0);
v_isShared_4435_ = v_isSharedCheck_4441_;
goto v_resetjp_4433_;
}
v_resetjp_4433_:
{
lean_object* v___x_4436_; lean_object* v___x_4438_; 
v___x_4436_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1___redArg(v_map_4431_, v_key_4427_, v_value_4428_);
if (v_isShared_4435_ == 0)
{
lean_ctor_set(v___x_4434_, 1, v___x_4436_);
v___x_4438_ = v___x_4434_;
goto v_reusejp_4437_;
}
else
{
lean_object* v_reuseFailAlloc_4440_; 
v_reuseFailAlloc_4440_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4440_, 0, v_newEntries_4430_);
lean_ctor_set(v_reuseFailAlloc_4440_, 1, v___x_4436_);
v___x_4438_ = v_reuseFailAlloc_4440_;
goto v_reusejp_4437_;
}
v_reusejp_4437_:
{
v_x_4425_ = v___x_4438_;
v_x_4426_ = v_tail_4429_;
goto _start;
}
}
}
else
{
lean_dec(v_value_4428_);
lean_dec(v_key_4427_);
v_x_4426_ = v_tail_4429_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_updateEnvAttributesImpl_spec__1(lean_object* v_as_4445_, size_t v_i_4446_, size_t v_stop_4447_, lean_object* v_b_4448_){
_start:
{
uint8_t v___x_4449_; 
v___x_4449_ = lean_usize_dec_eq(v_i_4446_, v_stop_4447_);
if (v___x_4449_ == 0)
{
lean_object* v___x_4450_; lean_object* v___x_4451_; size_t v___x_4452_; size_t v___x_4453_; 
v___x_4450_ = lean_array_uget_borrowed(v_as_4445_, v_i_4446_);
lean_inc(v___x_4450_);
v___x_4451_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_updateEnvAttributesImpl_spec__0(v_b_4448_, v___x_4450_);
v___x_4452_ = ((size_t)1ULL);
v___x_4453_ = lean_usize_add(v_i_4446_, v___x_4452_);
v_i_4446_ = v___x_4453_;
v_b_4448_ = v___x_4451_;
goto _start;
}
else
{
return v_b_4448_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_updateEnvAttributesImpl_spec__1___boxed(lean_object* v_as_4455_, lean_object* v_i_4456_, lean_object* v_stop_4457_, lean_object* v_b_4458_){
_start:
{
size_t v_i_boxed_4459_; size_t v_stop_boxed_4460_; lean_object* v_res_4461_; 
v_i_boxed_4459_ = lean_unbox_usize(v_i_4456_);
lean_dec(v_i_4456_);
v_stop_boxed_4460_ = lean_unbox_usize(v_stop_4457_);
lean_dec(v_stop_4457_);
v_res_4461_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_updateEnvAttributesImpl_spec__1(v_as_4455_, v_i_boxed_4459_, v_stop_boxed_4460_, v_b_4458_);
lean_dec_ref(v_as_4455_);
return v_res_4461_;
}
}
LEAN_EXPORT lean_object* lean_update_env_attributes(lean_object* v_env_4462_){
_start:
{
lean_object* v___x_4464_; lean_object* v___x_4465_; lean_object* v___x_4466_; lean_object* v___y_4468_; lean_object* v_toEnvExtension_4471_; lean_object* v_asyncMode_4472_; lean_object* v_buckets_4473_; lean_object* v___x_4474_; lean_object* v___x_4475_; lean_object* v___x_4476_; lean_object* v___x_4477_; lean_object* v___x_4478_; uint8_t v___x_4479_; 
v___x_4464_ = l_Lean_attributeMapRef;
v___x_4465_ = lean_st_ref_get(v___x_4464_);
v___x_4466_ = l_Lean_attributeExtension;
v_toEnvExtension_4471_ = lean_ctor_get(v___x_4466_, 0);
v_asyncMode_4472_ = lean_ctor_get(v_toEnvExtension_4471_, 2);
v_buckets_4473_ = lean_ctor_get(v___x_4465_, 1);
lean_inc_ref(v_buckets_4473_);
lean_dec(v___x_4465_);
v___x_4474_ = l_Lean_instInhabitedAttributeExtensionState_default;
v___x_4475_ = lean_box(0);
lean_inc_ref(v_env_4462_);
v___x_4476_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_4474_, v___x_4466_, v_env_4462_, v_asyncMode_4472_, v___x_4475_);
v___x_4477_ = lean_unsigned_to_nat(0u);
v___x_4478_ = lean_array_get_size(v_buckets_4473_);
v___x_4479_ = lean_nat_dec_lt(v___x_4477_, v___x_4478_);
if (v___x_4479_ == 0)
{
lean_dec_ref(v_buckets_4473_);
v___y_4468_ = v___x_4476_;
goto v___jp_4467_;
}
else
{
uint8_t v___x_4480_; 
v___x_4480_ = lean_nat_dec_le(v___x_4478_, v___x_4478_);
if (v___x_4480_ == 0)
{
if (v___x_4479_ == 0)
{
lean_dec_ref(v_buckets_4473_);
v___y_4468_ = v___x_4476_;
goto v___jp_4467_;
}
else
{
size_t v___x_4481_; size_t v___x_4482_; lean_object* v___x_4483_; 
v___x_4481_ = ((size_t)0ULL);
v___x_4482_ = lean_usize_of_nat(v___x_4478_);
v___x_4483_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_updateEnvAttributesImpl_spec__1(v_buckets_4473_, v___x_4481_, v___x_4482_, v___x_4476_);
lean_dec_ref(v_buckets_4473_);
v___y_4468_ = v___x_4483_;
goto v___jp_4467_;
}
}
else
{
size_t v___x_4484_; size_t v___x_4485_; lean_object* v___x_4486_; 
v___x_4484_ = ((size_t)0ULL);
v___x_4485_ = lean_usize_of_nat(v___x_4478_);
v___x_4486_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_updateEnvAttributesImpl_spec__1(v_buckets_4473_, v___x_4484_, v___x_4485_, v___x_4476_);
lean_dec_ref(v_buckets_4473_);
v___y_4468_ = v___x_4486_;
goto v___jp_4467_;
}
}
v___jp_4467_:
{
lean_object* v___x_4469_; lean_object* v___x_4470_; 
v___x_4469_ = l_Lean_PersistentEnvExtension_setState___redArg(v___x_4466_, v_env_4462_, v___y_4468_);
v___x_4470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4470_, 0, v___x_4469_);
return v___x_4470_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_updateEnvAttributesImpl___boxed(lean_object* v_env_4487_, lean_object* v_a_4488_){
_start:
{
lean_object* v_res_4489_; 
v_res_4489_ = lean_update_env_attributes(v_env_4487_);
return v_res_4489_;
}
}
LEAN_EXPORT lean_object* lean_get_num_attributes(){
_start:
{
lean_object* v___x_4491_; lean_object* v___x_4492_; lean_object* v_size_4493_; lean_object* v___x_4494_; 
v___x_4491_ = l_Lean_attributeMapRef;
v___x_4492_ = lean_st_ref_get(v___x_4491_);
v_size_4493_ = lean_ctor_get(v___x_4492_, 0);
lean_inc(v_size_4493_);
lean_dec(v___x_4492_);
v___x_4494_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4494_, 0, v_size_4493_);
return v___x_4494_;
}
}
LEAN_EXPORT lean_object* l_Lean_getNumBuiltinAttributesImpl___boxed(lean_object* v_a_4495_){
_start:
{
lean_object* v_res_4496_; 
v_res_4496_ = lean_get_num_attributes();
return v_res_4496_;
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
