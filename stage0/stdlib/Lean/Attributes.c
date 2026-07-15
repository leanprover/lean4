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
lean_dec_ref_known(v_a_830_, 1);
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
lean_dec_ref_known(v_asyncPrefix_x3f_1068_, 1);
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
lean_object* v___x_1216_; lean_object* v_env_1217_; uint8_t v_isExporting_1218_; lean_object* v___x_1269_; uint8_t v_isModule_1270_; 
v___x_1216_ = lean_st_ref_get(v___y_1214_);
v_env_1217_ = lean_ctor_get(v___x_1216_, 0);
lean_inc_ref(v_env_1217_);
lean_dec(v___x_1216_);
v_isExporting_1218_ = lean_ctor_get_uint8(v_env_1217_, sizeof(void*)*8);
v___x_1269_ = l_Lean_Environment_header(v_env_1217_);
lean_dec_ref(v_env_1217_);
v_isModule_1270_ = lean_ctor_get_uint8(v___x_1269_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_1269_);
if (v_isModule_1270_ == 0)
{
lean_object* v___x_1271_; 
lean_inc(v___y_1214_);
lean_inc_ref(v___y_1213_);
v___x_1271_ = lean_apply_3(v_x_1211_, v___y_1213_, v___y_1214_, lean_box(0));
return v___x_1271_;
}
else
{
if (v_isExporting_1218_ == 0)
{
if (v_isExporting_1212_ == 0)
{
lean_object* v___x_1272_; 
lean_inc(v___y_1214_);
lean_inc_ref(v___y_1213_);
v___x_1272_ = lean_apply_3(v_x_1211_, v___y_1213_, v___y_1214_, lean_box(0));
return v___x_1272_;
}
else
{
goto v___jp_1219_;
}
}
else
{
if (v_isExporting_1212_ == 0)
{
goto v___jp_1219_;
}
else
{
lean_object* v___x_1273_; 
lean_inc(v___y_1214_);
lean_inc_ref(v___y_1213_);
v___x_1273_ = lean_apply_3(v_x_1211_, v___y_1213_, v___y_1214_, lean_box(0));
return v___x_1273_;
}
}
}
v___jp_1219_:
{
lean_object* v___x_1220_; lean_object* v_env_1221_; lean_object* v_nextMacroScope_1222_; lean_object* v_ngen_1223_; lean_object* v_auxDeclNGen_1224_; lean_object* v_traceState_1225_; lean_object* v_messages_1226_; lean_object* v_infoState_1227_; lean_object* v_snapshotTasks_1228_; lean_object* v___x_1230_; uint8_t v_isShared_1231_; uint8_t v_isSharedCheck_1267_; 
v___x_1220_ = lean_st_ref_take(v___y_1214_);
v_env_1221_ = lean_ctor_get(v___x_1220_, 0);
v_nextMacroScope_1222_ = lean_ctor_get(v___x_1220_, 1);
v_ngen_1223_ = lean_ctor_get(v___x_1220_, 2);
v_auxDeclNGen_1224_ = lean_ctor_get(v___x_1220_, 3);
v_traceState_1225_ = lean_ctor_get(v___x_1220_, 4);
v_messages_1226_ = lean_ctor_get(v___x_1220_, 6);
v_infoState_1227_ = lean_ctor_get(v___x_1220_, 7);
v_snapshotTasks_1228_ = lean_ctor_get(v___x_1220_, 8);
v_isSharedCheck_1267_ = !lean_is_exclusive(v___x_1220_);
if (v_isSharedCheck_1267_ == 0)
{
lean_object* v_unused_1268_; 
v_unused_1268_ = lean_ctor_get(v___x_1220_, 5);
lean_dec(v_unused_1268_);
v___x_1230_ = v___x_1220_;
v_isShared_1231_ = v_isSharedCheck_1267_;
goto v_resetjp_1229_;
}
else
{
lean_inc(v_snapshotTasks_1228_);
lean_inc(v_infoState_1227_);
lean_inc(v_messages_1226_);
lean_inc(v_traceState_1225_);
lean_inc(v_auxDeclNGen_1224_);
lean_inc(v_ngen_1223_);
lean_inc(v_nextMacroScope_1222_);
lean_inc(v_env_1221_);
lean_dec(v___x_1220_);
v___x_1230_ = lean_box(0);
v_isShared_1231_ = v_isSharedCheck_1267_;
goto v_resetjp_1229_;
}
v_resetjp_1229_:
{
lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1235_; 
v___x_1232_ = l_Lean_Environment_setExporting(v_env_1221_, v_isExporting_1212_);
v___x_1233_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2);
if (v_isShared_1231_ == 0)
{
lean_ctor_set(v___x_1230_, 5, v___x_1233_);
lean_ctor_set(v___x_1230_, 0, v___x_1232_);
v___x_1235_ = v___x_1230_;
goto v_reusejp_1234_;
}
else
{
lean_object* v_reuseFailAlloc_1266_; 
v_reuseFailAlloc_1266_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1266_, 0, v___x_1232_);
lean_ctor_set(v_reuseFailAlloc_1266_, 1, v_nextMacroScope_1222_);
lean_ctor_set(v_reuseFailAlloc_1266_, 2, v_ngen_1223_);
lean_ctor_set(v_reuseFailAlloc_1266_, 3, v_auxDeclNGen_1224_);
lean_ctor_set(v_reuseFailAlloc_1266_, 4, v_traceState_1225_);
lean_ctor_set(v_reuseFailAlloc_1266_, 5, v___x_1233_);
lean_ctor_set(v_reuseFailAlloc_1266_, 6, v_messages_1226_);
lean_ctor_set(v_reuseFailAlloc_1266_, 7, v_infoState_1227_);
lean_ctor_set(v_reuseFailAlloc_1266_, 8, v_snapshotTasks_1228_);
v___x_1235_ = v_reuseFailAlloc_1266_;
goto v_reusejp_1234_;
}
v_reusejp_1234_:
{
lean_object* v___x_1236_; lean_object* v_r_1237_; 
v___x_1236_ = lean_st_ref_set(v___y_1214_, v___x_1235_);
lean_inc(v___y_1214_);
lean_inc_ref(v___y_1213_);
v_r_1237_ = lean_apply_3(v_x_1211_, v___y_1213_, v___y_1214_, lean_box(0));
if (lean_obj_tag(v_r_1237_) == 0)
{
lean_object* v_a_1238_; lean_object* v___x_1240_; uint8_t v_isShared_1241_; uint8_t v_isSharedCheck_1254_; 
v_a_1238_ = lean_ctor_get(v_r_1237_, 0);
v_isSharedCheck_1254_ = !lean_is_exclusive(v_r_1237_);
if (v_isSharedCheck_1254_ == 0)
{
v___x_1240_ = v_r_1237_;
v_isShared_1241_ = v_isSharedCheck_1254_;
goto v_resetjp_1239_;
}
else
{
lean_inc(v_a_1238_);
lean_dec(v_r_1237_);
v___x_1240_ = lean_box(0);
v_isShared_1241_ = v_isSharedCheck_1254_;
goto v_resetjp_1239_;
}
v_resetjp_1239_:
{
lean_object* v___x_1243_; 
lean_inc(v_a_1238_);
if (v_isShared_1241_ == 0)
{
lean_ctor_set_tag(v___x_1240_, 1);
v___x_1243_ = v___x_1240_;
goto v_reusejp_1242_;
}
else
{
lean_object* v_reuseFailAlloc_1253_; 
v_reuseFailAlloc_1253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1253_, 0, v_a_1238_);
v___x_1243_ = v_reuseFailAlloc_1253_;
goto v_reusejp_1242_;
}
v_reusejp_1242_:
{
lean_object* v___x_1244_; lean_object* v___x_1246_; uint8_t v_isShared_1247_; uint8_t v_isSharedCheck_1251_; 
v___x_1244_ = l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___lam__0(v___y_1214_, v_isExporting_1218_, v___x_1233_, v___x_1243_);
lean_dec_ref(v___x_1243_);
v_isSharedCheck_1251_ = !lean_is_exclusive(v___x_1244_);
if (v_isSharedCheck_1251_ == 0)
{
lean_object* v_unused_1252_; 
v_unused_1252_ = lean_ctor_get(v___x_1244_, 0);
lean_dec(v_unused_1252_);
v___x_1246_ = v___x_1244_;
v_isShared_1247_ = v_isSharedCheck_1251_;
goto v_resetjp_1245_;
}
else
{
lean_dec(v___x_1244_);
v___x_1246_ = lean_box(0);
v_isShared_1247_ = v_isSharedCheck_1251_;
goto v_resetjp_1245_;
}
v_resetjp_1245_:
{
lean_object* v___x_1249_; 
if (v_isShared_1247_ == 0)
{
lean_ctor_set(v___x_1246_, 0, v_a_1238_);
v___x_1249_ = v___x_1246_;
goto v_reusejp_1248_;
}
else
{
lean_object* v_reuseFailAlloc_1250_; 
v_reuseFailAlloc_1250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1250_, 0, v_a_1238_);
v___x_1249_ = v_reuseFailAlloc_1250_;
goto v_reusejp_1248_;
}
v_reusejp_1248_:
{
return v___x_1249_;
}
}
}
}
}
else
{
lean_object* v_a_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1259_; uint8_t v_isShared_1260_; uint8_t v_isSharedCheck_1264_; 
v_a_1255_ = lean_ctor_get(v_r_1237_, 0);
lean_inc(v_a_1255_);
lean_dec_ref_known(v_r_1237_, 1);
v___x_1256_ = lean_box(0);
v___x_1257_ = l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___lam__0(v___y_1214_, v_isExporting_1218_, v___x_1233_, v___x_1256_);
v_isSharedCheck_1264_ = !lean_is_exclusive(v___x_1257_);
if (v_isSharedCheck_1264_ == 0)
{
lean_object* v_unused_1265_; 
v_unused_1265_ = lean_ctor_get(v___x_1257_, 0);
lean_dec(v_unused_1265_);
v___x_1259_ = v___x_1257_;
v_isShared_1260_ = v_isSharedCheck_1264_;
goto v_resetjp_1258_;
}
else
{
lean_dec(v___x_1257_);
v___x_1259_ = lean_box(0);
v_isShared_1260_ = v_isSharedCheck_1264_;
goto v_resetjp_1258_;
}
v_resetjp_1258_:
{
lean_object* v___x_1262_; 
if (v_isShared_1260_ == 0)
{
lean_ctor_set_tag(v___x_1259_, 1);
lean_ctor_set(v___x_1259_, 0, v_a_1255_);
v___x_1262_ = v___x_1259_;
goto v_reusejp_1261_;
}
else
{
lean_object* v_reuseFailAlloc_1263_; 
v_reuseFailAlloc_1263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1263_, 0, v_a_1255_);
v___x_1262_ = v_reuseFailAlloc_1263_;
goto v_reusejp_1261_;
}
v_reusejp_1261_:
{
return v___x_1262_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___boxed(lean_object* v_x_1274_, lean_object* v_isExporting_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_){
_start:
{
uint8_t v_isExporting_boxed_1279_; lean_object* v_res_1280_; 
v_isExporting_boxed_1279_ = lean_unbox(v_isExporting_1275_);
v_res_1280_ = l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg(v_x_1274_, v_isExporting_boxed_1279_, v___y_1276_, v___y_1277_);
lean_dec(v___y_1277_);
lean_dec_ref(v___y_1276_);
return v_res_1280_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2(lean_object* v_00_u03b1_1281_, lean_object* v_x_1282_, uint8_t v_isExporting_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_){
_start:
{
lean_object* v___x_1287_; 
v___x_1287_ = l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg(v_x_1282_, v_isExporting_1283_, v___y_1284_, v___y_1285_);
return v___x_1287_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___boxed(lean_object* v_00_u03b1_1288_, lean_object* v_x_1289_, lean_object* v_isExporting_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_){
_start:
{
uint8_t v_isExporting_boxed_1294_; lean_object* v_res_1295_; 
v_isExporting_boxed_1294_ = lean_unbox(v_isExporting_1290_);
v_res_1295_ = l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2(v_00_u03b1_1288_, v_x_1289_, v_isExporting_boxed_1294_, v___y_1291_, v___y_1292_);
lean_dec(v___y_1292_);
lean_dec_ref(v___y_1291_);
return v_res_1295_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0_spec__3(lean_object* v_opts_1296_, lean_object* v_opt_1297_){
_start:
{
lean_object* v_name_1298_; lean_object* v_defValue_1299_; lean_object* v_map_1300_; lean_object* v___x_1301_; 
v_name_1298_ = lean_ctor_get(v_opt_1297_, 0);
v_defValue_1299_ = lean_ctor_get(v_opt_1297_, 1);
v_map_1300_ = lean_ctor_get(v_opts_1296_, 0);
v___x_1301_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1300_, v_name_1298_);
if (lean_obj_tag(v___x_1301_) == 0)
{
uint8_t v___x_1302_; 
v___x_1302_ = lean_unbox(v_defValue_1299_);
return v___x_1302_;
}
else
{
lean_object* v_val_1303_; 
v_val_1303_ = lean_ctor_get(v___x_1301_, 0);
lean_inc(v_val_1303_);
lean_dec_ref_known(v___x_1301_, 1);
if (lean_obj_tag(v_val_1303_) == 1)
{
uint8_t v_v_1304_; 
v_v_1304_ = lean_ctor_get_uint8(v_val_1303_, 0);
lean_dec_ref_known(v_val_1303_, 0);
return v_v_1304_;
}
else
{
uint8_t v___x_1305_; 
lean_dec(v_val_1303_);
v___x_1305_ = lean_unbox(v_defValue_1299_);
return v___x_1305_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0_spec__3___boxed(lean_object* v_opts_1306_, lean_object* v_opt_1307_){
_start:
{
uint8_t v_res_1308_; lean_object* v_r_1309_; 
v_res_1308_ = l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0_spec__3(v_opts_1306_, v_opt_1307_);
lean_dec_ref(v_opt_1307_);
lean_dec_ref(v_opts_1306_);
v_r_1309_ = lean_box(v_res_1308_);
return v_r_1309_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0(uint8_t v___y_1317_, uint8_t v_suppressElabErrors_1318_, lean_object* v_x_1319_){
_start:
{
if (lean_obj_tag(v_x_1319_) == 1)
{
lean_object* v_pre_1320_; 
v_pre_1320_ = lean_ctor_get(v_x_1319_, 0);
switch(lean_obj_tag(v_pre_1320_))
{
case 1:
{
lean_object* v_pre_1321_; 
v_pre_1321_ = lean_ctor_get(v_pre_1320_, 0);
switch(lean_obj_tag(v_pre_1321_))
{
case 0:
{
lean_object* v_str_1322_; lean_object* v_str_1323_; lean_object* v___x_1324_; uint8_t v___x_1325_; 
v_str_1322_ = lean_ctor_get(v_x_1319_, 1);
v_str_1323_ = lean_ctor_get(v_pre_1320_, 1);
v___x_1324_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__0));
v___x_1325_ = lean_string_dec_eq(v_str_1323_, v___x_1324_);
if (v___x_1325_ == 0)
{
lean_object* v___x_1326_; uint8_t v___x_1327_; 
v___x_1326_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__2));
v___x_1327_ = lean_string_dec_eq(v_str_1323_, v___x_1326_);
if (v___x_1327_ == 0)
{
return v___y_1317_;
}
else
{
lean_object* v___x_1328_; uint8_t v___x_1329_; 
v___x_1328_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__1));
v___x_1329_ = lean_string_dec_eq(v_str_1322_, v___x_1328_);
if (v___x_1329_ == 0)
{
return v___y_1317_;
}
else
{
return v_suppressElabErrors_1318_;
}
}
}
else
{
lean_object* v___x_1330_; uint8_t v___x_1331_; 
v___x_1330_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__2));
v___x_1331_ = lean_string_dec_eq(v_str_1322_, v___x_1330_);
if (v___x_1331_ == 0)
{
return v___y_1317_;
}
else
{
return v_suppressElabErrors_1318_;
}
}
}
case 1:
{
lean_object* v_pre_1332_; 
v_pre_1332_ = lean_ctor_get(v_pre_1321_, 0);
if (lean_obj_tag(v_pre_1332_) == 0)
{
lean_object* v_str_1333_; lean_object* v_str_1334_; lean_object* v_str_1335_; lean_object* v___x_1336_; uint8_t v___x_1337_; 
v_str_1333_ = lean_ctor_get(v_x_1319_, 1);
v_str_1334_ = lean_ctor_get(v_pre_1320_, 1);
v_str_1335_ = lean_ctor_get(v_pre_1321_, 1);
v___x_1336_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__3));
v___x_1337_ = lean_string_dec_eq(v_str_1335_, v___x_1336_);
if (v___x_1337_ == 0)
{
return v___y_1317_;
}
else
{
lean_object* v___x_1338_; uint8_t v___x_1339_; 
v___x_1338_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__4));
v___x_1339_ = lean_string_dec_eq(v_str_1334_, v___x_1338_);
if (v___x_1339_ == 0)
{
return v___y_1317_;
}
else
{
lean_object* v___x_1340_; uint8_t v___x_1341_; 
v___x_1340_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__5));
v___x_1341_ = lean_string_dec_eq(v_str_1333_, v___x_1340_);
if (v___x_1341_ == 0)
{
return v___y_1317_;
}
else
{
return v_suppressElabErrors_1318_;
}
}
}
}
else
{
return v___y_1317_;
}
}
default: 
{
return v___y_1317_;
}
}
}
case 0:
{
lean_object* v_str_1342_; lean_object* v___x_1343_; uint8_t v___x_1344_; 
v_str_1342_ = lean_ctor_get(v_x_1319_, 1);
v___x_1343_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__6));
v___x_1344_ = lean_string_dec_eq(v_str_1342_, v___x_1343_);
if (v___x_1344_ == 0)
{
return v___y_1317_;
}
else
{
return v_suppressElabErrors_1318_;
}
}
default: 
{
return v___y_1317_;
}
}
}
else
{
return v___y_1317_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___boxed(lean_object* v___y_1345_, lean_object* v_suppressElabErrors_1346_, lean_object* v_x_1347_){
_start:
{
uint8_t v___y_4996__boxed_1348_; uint8_t v_suppressElabErrors_boxed_1349_; uint8_t v_res_1350_; lean_object* v_r_1351_; 
v___y_4996__boxed_1348_ = lean_unbox(v___y_1345_);
v_suppressElabErrors_boxed_1349_ = lean_unbox(v_suppressElabErrors_1346_);
v_res_1350_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0(v___y_4996__boxed_1348_, v_suppressElabErrors_boxed_1349_, v_x_1347_);
lean_dec(v_x_1347_);
v_r_1351_ = lean_box(v_res_1350_);
return v_r_1351_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6(lean_object* v_ref_1352_, lean_object* v_msgData_1353_, uint8_t v_severity_1354_, uint8_t v_isSilent_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_){
_start:
{
uint8_t v___y_1360_; lean_object* v___y_1361_; lean_object* v___y_1362_; lean_object* v___y_1363_; uint8_t v___y_1364_; lean_object* v___y_1365_; lean_object* v___y_1366_; lean_object* v___y_1367_; lean_object* v___y_1368_; lean_object* v___y_1396_; uint8_t v___y_1397_; uint8_t v___y_1398_; uint8_t v___y_1399_; lean_object* v___y_1400_; lean_object* v___y_1401_; lean_object* v___y_1402_; lean_object* v___y_1403_; lean_object* v___y_1421_; lean_object* v___y_1422_; uint8_t v___y_1423_; uint8_t v___y_1424_; uint8_t v___y_1425_; lean_object* v___y_1426_; lean_object* v___y_1427_; lean_object* v___y_1428_; lean_object* v___y_1432_; uint8_t v___y_1433_; uint8_t v___y_1434_; lean_object* v___y_1435_; lean_object* v___y_1436_; lean_object* v___y_1437_; uint8_t v___y_1438_; uint8_t v___x_1443_; uint8_t v___y_1445_; lean_object* v___y_1446_; lean_object* v___y_1447_; lean_object* v___y_1448_; lean_object* v___y_1449_; uint8_t v___y_1450_; uint8_t v___y_1451_; uint8_t v___y_1453_; uint8_t v___x_1468_; 
v___x_1443_ = 2;
v___x_1468_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1354_, v___x_1443_);
if (v___x_1468_ == 0)
{
v___y_1453_ = v___x_1468_;
goto v___jp_1452_;
}
else
{
uint8_t v___x_1469_; 
lean_inc_ref(v_msgData_1353_);
v___x_1469_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_1353_);
v___y_1453_ = v___x_1469_;
goto v___jp_1452_;
}
v___jp_1359_:
{
lean_object* v___x_1369_; lean_object* v_currNamespace_1370_; lean_object* v_openDecls_1371_; lean_object* v_env_1372_; lean_object* v_nextMacroScope_1373_; lean_object* v_ngen_1374_; lean_object* v_auxDeclNGen_1375_; lean_object* v_traceState_1376_; lean_object* v_cache_1377_; lean_object* v_messages_1378_; lean_object* v_infoState_1379_; lean_object* v_snapshotTasks_1380_; lean_object* v___x_1382_; uint8_t v_isShared_1383_; uint8_t v_isSharedCheck_1394_; 
v___x_1369_ = lean_st_ref_take(v___y_1368_);
v_currNamespace_1370_ = lean_ctor_get(v___y_1367_, 6);
v_openDecls_1371_ = lean_ctor_get(v___y_1367_, 7);
v_env_1372_ = lean_ctor_get(v___x_1369_, 0);
v_nextMacroScope_1373_ = lean_ctor_get(v___x_1369_, 1);
v_ngen_1374_ = lean_ctor_get(v___x_1369_, 2);
v_auxDeclNGen_1375_ = lean_ctor_get(v___x_1369_, 3);
v_traceState_1376_ = lean_ctor_get(v___x_1369_, 4);
v_cache_1377_ = lean_ctor_get(v___x_1369_, 5);
v_messages_1378_ = lean_ctor_get(v___x_1369_, 6);
v_infoState_1379_ = lean_ctor_get(v___x_1369_, 7);
v_snapshotTasks_1380_ = lean_ctor_get(v___x_1369_, 8);
v_isSharedCheck_1394_ = !lean_is_exclusive(v___x_1369_);
if (v_isSharedCheck_1394_ == 0)
{
v___x_1382_ = v___x_1369_;
v_isShared_1383_ = v_isSharedCheck_1394_;
goto v_resetjp_1381_;
}
else
{
lean_inc(v_snapshotTasks_1380_);
lean_inc(v_infoState_1379_);
lean_inc(v_messages_1378_);
lean_inc(v_cache_1377_);
lean_inc(v_traceState_1376_);
lean_inc(v_auxDeclNGen_1375_);
lean_inc(v_ngen_1374_);
lean_inc(v_nextMacroScope_1373_);
lean_inc(v_env_1372_);
lean_dec(v___x_1369_);
v___x_1382_ = lean_box(0);
v_isShared_1383_ = v_isSharedCheck_1394_;
goto v_resetjp_1381_;
}
v_resetjp_1381_:
{
lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1389_; 
lean_inc(v_openDecls_1371_);
lean_inc(v_currNamespace_1370_);
v___x_1384_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1384_, 0, v_currNamespace_1370_);
lean_ctor_set(v___x_1384_, 1, v_openDecls_1371_);
v___x_1385_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1385_, 0, v___x_1384_);
lean_ctor_set(v___x_1385_, 1, v___y_1363_);
lean_inc_ref(v___y_1362_);
lean_inc_ref(v___y_1366_);
v___x_1386_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1386_, 0, v___y_1366_);
lean_ctor_set(v___x_1386_, 1, v___y_1361_);
lean_ctor_set(v___x_1386_, 2, v___y_1365_);
lean_ctor_set(v___x_1386_, 3, v___y_1362_);
lean_ctor_set(v___x_1386_, 4, v___x_1385_);
lean_ctor_set_uint8(v___x_1386_, sizeof(void*)*5, v___y_1360_);
lean_ctor_set_uint8(v___x_1386_, sizeof(void*)*5 + 1, v___y_1364_);
lean_ctor_set_uint8(v___x_1386_, sizeof(void*)*5 + 2, v_isSilent_1355_);
v___x_1387_ = l_Lean_MessageLog_add(v___x_1386_, v_messages_1378_);
if (v_isShared_1383_ == 0)
{
lean_ctor_set(v___x_1382_, 6, v___x_1387_);
v___x_1389_ = v___x_1382_;
goto v_reusejp_1388_;
}
else
{
lean_object* v_reuseFailAlloc_1393_; 
v_reuseFailAlloc_1393_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1393_, 0, v_env_1372_);
lean_ctor_set(v_reuseFailAlloc_1393_, 1, v_nextMacroScope_1373_);
lean_ctor_set(v_reuseFailAlloc_1393_, 2, v_ngen_1374_);
lean_ctor_set(v_reuseFailAlloc_1393_, 3, v_auxDeclNGen_1375_);
lean_ctor_set(v_reuseFailAlloc_1393_, 4, v_traceState_1376_);
lean_ctor_set(v_reuseFailAlloc_1393_, 5, v_cache_1377_);
lean_ctor_set(v_reuseFailAlloc_1393_, 6, v___x_1387_);
lean_ctor_set(v_reuseFailAlloc_1393_, 7, v_infoState_1379_);
lean_ctor_set(v_reuseFailAlloc_1393_, 8, v_snapshotTasks_1380_);
v___x_1389_ = v_reuseFailAlloc_1393_;
goto v_reusejp_1388_;
}
v_reusejp_1388_:
{
lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; 
v___x_1390_ = lean_st_ref_set(v___y_1368_, v___x_1389_);
v___x_1391_ = lean_box(0);
v___x_1392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1392_, 0, v___x_1391_);
return v___x_1392_;
}
}
}
v___jp_1395_:
{
lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v_a_1406_; lean_object* v___x_1408_; uint8_t v_isShared_1409_; uint8_t v_isSharedCheck_1419_; 
v___x_1404_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_1353_);
v___x_1405_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0(v___x_1404_, v___y_1356_, v___y_1357_);
v_a_1406_ = lean_ctor_get(v___x_1405_, 0);
v_isSharedCheck_1419_ = !lean_is_exclusive(v___x_1405_);
if (v_isSharedCheck_1419_ == 0)
{
v___x_1408_ = v___x_1405_;
v_isShared_1409_ = v_isSharedCheck_1419_;
goto v_resetjp_1407_;
}
else
{
lean_inc(v_a_1406_);
lean_dec(v___x_1405_);
v___x_1408_ = lean_box(0);
v_isShared_1409_ = v_isSharedCheck_1419_;
goto v_resetjp_1407_;
}
v_resetjp_1407_:
{
lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; 
lean_inc_ref_n(v___y_1401_, 2);
v___x_1410_ = l_Lean_FileMap_toPosition(v___y_1401_, v___y_1400_);
lean_dec(v___y_1400_);
v___x_1411_ = l_Lean_FileMap_toPosition(v___y_1401_, v___y_1403_);
lean_dec(v___y_1403_);
v___x_1412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1412_, 0, v___x_1411_);
v___x_1413_ = ((lean_object*)(l_Lean_instInhabitedAttributeImplCore_default___closed__3));
if (v___y_1398_ == 0)
{
lean_del_object(v___x_1408_);
lean_dec_ref(v___y_1396_);
v___y_1360_ = v___y_1397_;
v___y_1361_ = v___x_1410_;
v___y_1362_ = v___x_1413_;
v___y_1363_ = v_a_1406_;
v___y_1364_ = v___y_1399_;
v___y_1365_ = v___x_1412_;
v___y_1366_ = v___y_1402_;
v___y_1367_ = v___y_1356_;
v___y_1368_ = v___y_1357_;
goto v___jp_1359_;
}
else
{
uint8_t v___x_1414_; 
lean_inc(v_a_1406_);
v___x_1414_ = l_Lean_MessageData_hasTag(v___y_1396_, v_a_1406_);
if (v___x_1414_ == 0)
{
lean_object* v___x_1415_; lean_object* v___x_1417_; 
lean_dec_ref_known(v___x_1412_, 1);
lean_dec_ref(v___x_1410_);
lean_dec(v_a_1406_);
v___x_1415_ = lean_box(0);
if (v_isShared_1409_ == 0)
{
lean_ctor_set(v___x_1408_, 0, v___x_1415_);
v___x_1417_ = v___x_1408_;
goto v_reusejp_1416_;
}
else
{
lean_object* v_reuseFailAlloc_1418_; 
v_reuseFailAlloc_1418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1418_, 0, v___x_1415_);
v___x_1417_ = v_reuseFailAlloc_1418_;
goto v_reusejp_1416_;
}
v_reusejp_1416_:
{
return v___x_1417_;
}
}
else
{
lean_del_object(v___x_1408_);
v___y_1360_ = v___y_1397_;
v___y_1361_ = v___x_1410_;
v___y_1362_ = v___x_1413_;
v___y_1363_ = v_a_1406_;
v___y_1364_ = v___y_1399_;
v___y_1365_ = v___x_1412_;
v___y_1366_ = v___y_1402_;
v___y_1367_ = v___y_1356_;
v___y_1368_ = v___y_1357_;
goto v___jp_1359_;
}
}
}
}
v___jp_1420_:
{
lean_object* v___x_1429_; 
v___x_1429_ = l_Lean_Syntax_getTailPos_x3f(v___y_1422_, v___y_1423_);
lean_dec(v___y_1422_);
if (lean_obj_tag(v___x_1429_) == 0)
{
lean_inc(v___y_1428_);
v___y_1396_ = v___y_1421_;
v___y_1397_ = v___y_1423_;
v___y_1398_ = v___y_1424_;
v___y_1399_ = v___y_1425_;
v___y_1400_ = v___y_1428_;
v___y_1401_ = v___y_1426_;
v___y_1402_ = v___y_1427_;
v___y_1403_ = v___y_1428_;
goto v___jp_1395_;
}
else
{
lean_object* v_val_1430_; 
v_val_1430_ = lean_ctor_get(v___x_1429_, 0);
lean_inc(v_val_1430_);
lean_dec_ref_known(v___x_1429_, 1);
v___y_1396_ = v___y_1421_;
v___y_1397_ = v___y_1423_;
v___y_1398_ = v___y_1424_;
v___y_1399_ = v___y_1425_;
v___y_1400_ = v___y_1428_;
v___y_1401_ = v___y_1426_;
v___y_1402_ = v___y_1427_;
v___y_1403_ = v_val_1430_;
goto v___jp_1395_;
}
}
v___jp_1431_:
{
lean_object* v_ref_1439_; lean_object* v___x_1440_; 
v_ref_1439_ = l_Lean_replaceRef(v_ref_1352_, v___y_1436_);
v___x_1440_ = l_Lean_Syntax_getPos_x3f(v_ref_1439_, v___y_1433_);
if (lean_obj_tag(v___x_1440_) == 0)
{
lean_object* v___x_1441_; 
v___x_1441_ = lean_unsigned_to_nat(0u);
v___y_1421_ = v___y_1432_;
v___y_1422_ = v_ref_1439_;
v___y_1423_ = v___y_1433_;
v___y_1424_ = v___y_1434_;
v___y_1425_ = v___y_1438_;
v___y_1426_ = v___y_1435_;
v___y_1427_ = v___y_1437_;
v___y_1428_ = v___x_1441_;
goto v___jp_1420_;
}
else
{
lean_object* v_val_1442_; 
v_val_1442_ = lean_ctor_get(v___x_1440_, 0);
lean_inc(v_val_1442_);
lean_dec_ref_known(v___x_1440_, 1);
v___y_1421_ = v___y_1432_;
v___y_1422_ = v_ref_1439_;
v___y_1423_ = v___y_1433_;
v___y_1424_ = v___y_1434_;
v___y_1425_ = v___y_1438_;
v___y_1426_ = v___y_1435_;
v___y_1427_ = v___y_1437_;
v___y_1428_ = v_val_1442_;
goto v___jp_1420_;
}
}
v___jp_1444_:
{
if (v___y_1451_ == 0)
{
v___y_1432_ = v___y_1446_;
v___y_1433_ = v___y_1450_;
v___y_1434_ = v___y_1445_;
v___y_1435_ = v___y_1448_;
v___y_1436_ = v___y_1447_;
v___y_1437_ = v___y_1449_;
v___y_1438_ = v_severity_1354_;
goto v___jp_1431_;
}
else
{
v___y_1432_ = v___y_1446_;
v___y_1433_ = v___y_1450_;
v___y_1434_ = v___y_1445_;
v___y_1435_ = v___y_1448_;
v___y_1436_ = v___y_1447_;
v___y_1437_ = v___y_1449_;
v___y_1438_ = v___x_1443_;
goto v___jp_1431_;
}
}
v___jp_1452_:
{
if (v___y_1453_ == 0)
{
lean_object* v_fileName_1454_; lean_object* v_fileMap_1455_; lean_object* v_options_1456_; lean_object* v_ref_1457_; uint8_t v_suppressElabErrors_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___f_1461_; uint8_t v___x_1462_; uint8_t v___x_1463_; 
v_fileName_1454_ = lean_ctor_get(v___y_1356_, 0);
v_fileMap_1455_ = lean_ctor_get(v___y_1356_, 1);
v_options_1456_ = lean_ctor_get(v___y_1356_, 2);
v_ref_1457_ = lean_ctor_get(v___y_1356_, 5);
v_suppressElabErrors_1458_ = lean_ctor_get_uint8(v___y_1356_, sizeof(void*)*14 + 1);
v___x_1459_ = lean_box(v___y_1453_);
v___x_1460_ = lean_box(v_suppressElabErrors_1458_);
v___f_1461_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1461_, 0, v___x_1459_);
lean_closure_set(v___f_1461_, 1, v___x_1460_);
v___x_1462_ = 1;
v___x_1463_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1354_, v___x_1462_);
if (v___x_1463_ == 0)
{
v___y_1445_ = v_suppressElabErrors_1458_;
v___y_1446_ = v___f_1461_;
v___y_1447_ = v_ref_1457_;
v___y_1448_ = v_fileMap_1455_;
v___y_1449_ = v_fileName_1454_;
v___y_1450_ = v___y_1453_;
v___y_1451_ = v___x_1463_;
goto v___jp_1444_;
}
else
{
lean_object* v___x_1464_; uint8_t v___x_1465_; 
v___x_1464_ = l_Lean_warningAsError;
v___x_1465_ = l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0_spec__3(v_options_1456_, v___x_1464_);
v___y_1445_ = v_suppressElabErrors_1458_;
v___y_1446_ = v___f_1461_;
v___y_1447_ = v_ref_1457_;
v___y_1448_ = v_fileMap_1455_;
v___y_1449_ = v_fileName_1454_;
v___y_1450_ = v___y_1453_;
v___y_1451_ = v___x_1465_;
goto v___jp_1444_;
}
}
else
{
lean_object* v___x_1466_; lean_object* v___x_1467_; 
lean_dec_ref(v_msgData_1353_);
v___x_1466_ = lean_box(0);
v___x_1467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1467_, 0, v___x_1466_);
return v___x_1467_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___boxed(lean_object* v_ref_1470_, lean_object* v_msgData_1471_, lean_object* v_severity_1472_, lean_object* v_isSilent_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_){
_start:
{
uint8_t v_severity_boxed_1477_; uint8_t v_isSilent_boxed_1478_; lean_object* v_res_1479_; 
v_severity_boxed_1477_ = lean_unbox(v_severity_1472_);
v_isSilent_boxed_1478_ = lean_unbox(v_isSilent_1473_);
v_res_1479_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6(v_ref_1470_, v_msgData_1471_, v_severity_boxed_1477_, v_isSilent_boxed_1478_, v___y_1474_, v___y_1475_);
lean_dec(v___y_1475_);
lean_dec_ref(v___y_1474_);
lean_dec(v_ref_1470_);
return v_res_1479_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5(lean_object* v_msgData_1480_, uint8_t v_severity_1481_, uint8_t v_isSilent_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_){
_start:
{
lean_object* v_ref_1486_; lean_object* v___x_1487_; 
v_ref_1486_ = lean_ctor_get(v___y_1483_, 5);
v___x_1487_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6(v_ref_1486_, v_msgData_1480_, v_severity_1481_, v_isSilent_1482_, v___y_1483_, v___y_1484_);
return v___x_1487_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5___boxed(lean_object* v_msgData_1488_, lean_object* v_severity_1489_, lean_object* v_isSilent_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_){
_start:
{
uint8_t v_severity_boxed_1494_; uint8_t v_isSilent_boxed_1495_; lean_object* v_res_1496_; 
v_severity_boxed_1494_ = lean_unbox(v_severity_1489_);
v_isSilent_boxed_1495_ = lean_unbox(v_isSilent_1490_);
v_res_1496_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5(v_msgData_1488_, v_severity_boxed_1494_, v_isSilent_boxed_1495_, v___y_1491_, v___y_1492_);
lean_dec(v___y_1492_);
lean_dec_ref(v___y_1491_);
return v_res_1496_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1(lean_object* v_msgData_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_){
_start:
{
uint8_t v___x_1501_; uint8_t v___x_1502_; lean_object* v___x_1503_; 
v___x_1501_ = 1;
v___x_1502_ = 0;
v___x_1503_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5(v_msgData_1497_, v___x_1501_, v___x_1502_, v___y_1498_, v___y_1499_);
return v___x_1503_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1___boxed(lean_object* v_msgData_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_){
_start:
{
lean_object* v_res_1508_; 
v_res_1508_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1(v_msgData_1504_, v___y_1505_, v___y_1506_);
lean_dec(v___y_1506_);
lean_dec_ref(v___y_1505_);
return v_res_1508_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0___redArg(lean_object* v_opt_1509_, lean_object* v___y_1510_){
_start:
{
lean_object* v_options_1512_; uint8_t v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; 
v_options_1512_ = lean_ctor_get(v___y_1510_, 2);
v___x_1513_ = l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0_spec__3(v_options_1512_, v_opt_1509_);
v___x_1514_ = lean_box(v___x_1513_);
v___x_1515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1515_, 0, v___x_1514_);
return v___x_1515_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0___redArg___boxed(lean_object* v_opt_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_){
_start:
{
lean_object* v_res_1519_; 
v_res_1519_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0___redArg(v_opt_1516_, v___y_1517_);
lean_dec_ref(v___y_1517_);
lean_dec_ref(v_opt_1516_);
return v_res_1519_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1521_; lean_object* v___x_1522_; 
v___x_1521_ = ((lean_object*)(l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__0));
v___x_1522_ = l_Lean_stringToMessageData(v___x_1521_);
return v___x_1522_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__3(void){
_start:
{
lean_object* v___x_1524_; lean_object* v___x_1525_; 
v___x_1524_ = ((lean_object*)(l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__2));
v___x_1525_ = l_Lean_stringToMessageData(v___x_1524_);
return v___x_1525_;
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0(lean_object* v_id_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_){
_start:
{
lean_object* v___x_1530_; lean_object* v_env_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v_a_1534_; lean_object* v___x_1536_; uint8_t v_isShared_1537_; uint8_t v_isSharedCheck_1553_; 
v___x_1530_ = lean_st_ref_get(v___y_1528_);
v_env_1531_ = lean_ctor_get(v___x_1530_, 0);
lean_inc_ref(v_env_1531_);
lean_dec(v___x_1530_);
v___x_1532_ = l_Lean_ResolveName_backward_privateInPublic_warn;
v___x_1533_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0___redArg(v___x_1532_, v___y_1527_);
v_a_1534_ = lean_ctor_get(v___x_1533_, 0);
v_isSharedCheck_1553_ = !lean_is_exclusive(v___x_1533_);
if (v_isSharedCheck_1553_ == 0)
{
v___x_1536_ = v___x_1533_;
v_isShared_1537_ = v_isSharedCheck_1553_;
goto v_resetjp_1535_;
}
else
{
lean_inc(v_a_1534_);
lean_dec(v___x_1533_);
v___x_1536_ = lean_box(0);
v_isShared_1537_ = v_isSharedCheck_1553_;
goto v_resetjp_1535_;
}
v_resetjp_1535_:
{
uint8_t v_isExporting_1543_; 
v_isExporting_1543_ = lean_ctor_get_uint8(v_env_1531_, sizeof(void*)*8);
lean_dec_ref(v_env_1531_);
if (v_isExporting_1543_ == 0)
{
lean_dec(v_a_1534_);
lean_dec(v_id_1526_);
goto v___jp_1538_;
}
else
{
uint8_t v___x_1544_; 
v___x_1544_ = l_Lean_isPrivateName(v_id_1526_);
if (v___x_1544_ == 0)
{
lean_dec(v_a_1534_);
lean_dec(v_id_1526_);
goto v___jp_1538_;
}
else
{
uint8_t v___x_1545_; 
v___x_1545_ = lean_unbox(v_a_1534_);
lean_dec(v_a_1534_);
if (v___x_1545_ == 0)
{
lean_dec(v_id_1526_);
goto v___jp_1538_;
}
else
{
lean_object* v___x_1546_; uint8_t v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; 
lean_del_object(v___x_1536_);
v___x_1546_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__1, &l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__1_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__1);
v___x_1547_ = 0;
v___x_1548_ = l_Lean_MessageData_ofConstName(v_id_1526_, v___x_1547_);
v___x_1549_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1549_, 0, v___x_1546_);
lean_ctor_set(v___x_1549_, 1, v___x_1548_);
v___x_1550_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__3, &l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__3_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__3);
v___x_1551_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1551_, 0, v___x_1549_);
lean_ctor_set(v___x_1551_, 1, v___x_1550_);
v___x_1552_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1(v___x_1551_, v___y_1527_, v___y_1528_);
return v___x_1552_;
}
}
}
v___jp_1538_:
{
lean_object* v___x_1539_; lean_object* v___x_1541_; 
v___x_1539_ = lean_box(0);
if (v_isShared_1537_ == 0)
{
lean_ctor_set(v___x_1536_, 0, v___x_1539_);
v___x_1541_ = v___x_1536_;
goto v_reusejp_1540_;
}
else
{
lean_object* v_reuseFailAlloc_1542_; 
v_reuseFailAlloc_1542_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1542_, 0, v___x_1539_);
v___x_1541_ = v_reuseFailAlloc_1542_;
goto v_reusejp_1540_;
}
v_reusejp_1540_:
{
return v___x_1541_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___boxed(lean_object* v_id_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_){
_start:
{
lean_object* v_res_1558_; 
v_res_1558_ = l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0(v_id_1554_, v___y_1555_, v___y_1556_);
lean_dec(v___y_1556_);
lean_dec_ref(v___y_1555_);
return v_res_1558_;
}
}
static lean_object* _init_l_Lean_ensureAttrDeclIsPublic___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1560_; lean_object* v___x_1561_; 
v___x_1560_ = ((lean_object*)(l_Lean_ensureAttrDeclIsPublic___lam__0___closed__0));
v___x_1561_ = l_Lean_stringToMessageData(v___x_1560_);
return v___x_1561_;
}
}
LEAN_EXPORT lean_object* l_Lean_ensureAttrDeclIsPublic___lam__0(lean_object* v_declName_1562_, uint8_t v_isModule_1563_, lean_object* v_attrName_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_){
_start:
{
lean_object* v___x_1568_; 
lean_inc(v_declName_1562_);
v___x_1568_ = l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0(v_declName_1562_, v___y_1565_, v___y_1566_);
if (lean_obj_tag(v___x_1568_) == 0)
{
lean_object* v___x_1569_; lean_object* v_a_1570_; lean_object* v___x_1572_; uint8_t v_isShared_1573_; uint8_t v_isSharedCheck_1590_; 
lean_dec_ref_known(v___x_1568_, 1);
lean_inc(v_declName_1562_);
v___x_1569_ = l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1___redArg(v_declName_1562_, v_isModule_1563_, v___y_1566_);
v_a_1570_ = lean_ctor_get(v___x_1569_, 0);
v_isSharedCheck_1590_ = !lean_is_exclusive(v___x_1569_);
if (v_isSharedCheck_1590_ == 0)
{
v___x_1572_ = v___x_1569_;
v_isShared_1573_ = v_isSharedCheck_1590_;
goto v_resetjp_1571_;
}
else
{
lean_inc(v_a_1570_);
lean_dec(v___x_1569_);
v___x_1572_ = lean_box(0);
v_isShared_1573_ = v_isSharedCheck_1590_;
goto v_resetjp_1571_;
}
v_resetjp_1571_:
{
uint8_t v___x_1574_; 
v___x_1574_ = lean_unbox(v_a_1570_);
if (v___x_1574_ == 0)
{
lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; uint8_t v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; 
lean_del_object(v___x_1572_);
v___x_1575_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1);
v___x_1576_ = l_Lean_MessageData_ofName(v_attrName_1564_);
v___x_1577_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1577_, 0, v___x_1575_);
lean_ctor_set(v___x_1577_, 1, v___x_1576_);
v___x_1578_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1, &l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1);
v___x_1579_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1579_, 0, v___x_1577_);
lean_ctor_set(v___x_1579_, 1, v___x_1578_);
v___x_1580_ = lean_unbox(v_a_1570_);
lean_dec(v_a_1570_);
v___x_1581_ = l_Lean_MessageData_ofConstName(v_declName_1562_, v___x_1580_);
v___x_1582_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1582_, 0, v___x_1579_);
lean_ctor_set(v___x_1582_, 1, v___x_1581_);
v___x_1583_ = lean_obj_once(&l_Lean_ensureAttrDeclIsPublic___lam__0___closed__1, &l_Lean_ensureAttrDeclIsPublic___lam__0___closed__1_once, _init_l_Lean_ensureAttrDeclIsPublic___lam__0___closed__1);
v___x_1584_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1584_, 0, v___x_1582_);
lean_ctor_set(v___x_1584_, 1, v___x_1583_);
v___x_1585_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_1584_, v___y_1565_, v___y_1566_);
return v___x_1585_;
}
else
{
lean_object* v___x_1586_; lean_object* v___x_1588_; 
lean_dec(v_a_1570_);
lean_dec(v_attrName_1564_);
lean_dec(v_declName_1562_);
v___x_1586_ = lean_box(0);
if (v_isShared_1573_ == 0)
{
lean_ctor_set(v___x_1572_, 0, v___x_1586_);
v___x_1588_ = v___x_1572_;
goto v_reusejp_1587_;
}
else
{
lean_object* v_reuseFailAlloc_1589_; 
v_reuseFailAlloc_1589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1589_, 0, v___x_1586_);
v___x_1588_ = v_reuseFailAlloc_1589_;
goto v_reusejp_1587_;
}
v_reusejp_1587_:
{
return v___x_1588_;
}
}
}
}
else
{
lean_dec(v_attrName_1564_);
lean_dec(v_declName_1562_);
return v___x_1568_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ensureAttrDeclIsPublic___lam__0___boxed(lean_object* v_declName_1591_, lean_object* v_isModule_1592_, lean_object* v_attrName_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_){
_start:
{
uint8_t v_isModule_boxed_1597_; lean_object* v_res_1598_; 
v_isModule_boxed_1597_ = lean_unbox(v_isModule_1592_);
v_res_1598_ = l_Lean_ensureAttrDeclIsPublic___lam__0(v_declName_1591_, v_isModule_boxed_1597_, v_attrName_1593_, v___y_1594_, v___y_1595_);
lean_dec(v___y_1595_);
lean_dec_ref(v___y_1594_);
return v_res_1598_;
}
}
LEAN_EXPORT lean_object* l_Lean_ensureAttrDeclIsPublic(lean_object* v_attrName_1599_, lean_object* v_declName_1600_, uint8_t v_attrKind_1601_, lean_object* v_a_1602_, lean_object* v_a_1603_){
_start:
{
lean_object* v___x_1605_; lean_object* v_env_1609_; lean_object* v___x_1610_; uint8_t v_isModule_1611_; 
v___x_1605_ = lean_st_ref_get(v_a_1603_);
v_env_1609_ = lean_ctor_get(v___x_1605_, 0);
lean_inc_ref(v_env_1609_);
lean_dec(v___x_1605_);
v___x_1610_ = l_Lean_Environment_header(v_env_1609_);
lean_dec_ref(v_env_1609_);
v_isModule_1611_ = lean_ctor_get_uint8(v___x_1610_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_1610_);
if (v_isModule_1611_ == 0)
{
lean_dec(v_declName_1600_);
lean_dec(v_attrName_1599_);
goto v___jp_1606_;
}
else
{
uint8_t v___x_1612_; uint8_t v___x_1613_; 
v___x_1612_ = 1;
v___x_1613_ = l_Lean_instBEqAttributeKind_beq(v_attrKind_1601_, v___x_1612_);
if (v___x_1613_ == 0)
{
lean_object* v___x_1614_; lean_object* v___f_1615_; lean_object* v___x_1616_; 
v___x_1614_ = lean_box(v_isModule_1611_);
v___f_1615_ = lean_alloc_closure((void*)(l_Lean_ensureAttrDeclIsPublic___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1615_, 0, v_declName_1600_);
lean_closure_set(v___f_1615_, 1, v___x_1614_);
lean_closure_set(v___f_1615_, 2, v_attrName_1599_);
v___x_1616_ = l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg(v___f_1615_, v_isModule_1611_, v_a_1602_, v_a_1603_);
return v___x_1616_;
}
else
{
lean_dec(v_declName_1600_);
lean_dec(v_attrName_1599_);
goto v___jp_1606_;
}
}
v___jp_1606_:
{
lean_object* v___x_1607_; lean_object* v___x_1608_; 
v___x_1607_ = lean_box(0);
v___x_1608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1608_, 0, v___x_1607_);
return v___x_1608_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ensureAttrDeclIsPublic___boxed(lean_object* v_attrName_1617_, lean_object* v_declName_1618_, lean_object* v_attrKind_1619_, lean_object* v_a_1620_, lean_object* v_a_1621_, lean_object* v_a_1622_){
_start:
{
uint8_t v_attrKind_boxed_1623_; lean_object* v_res_1624_; 
v_attrKind_boxed_1623_ = lean_unbox(v_attrKind_1619_);
v_res_1624_ = l_Lean_ensureAttrDeclIsPublic(v_attrName_1617_, v_declName_1618_, v_attrKind_boxed_1623_, v_a_1620_, v_a_1621_);
lean_dec(v_a_1621_);
lean_dec_ref(v_a_1620_);
return v_res_1624_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0(lean_object* v_opt_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_){
_start:
{
lean_object* v___x_1629_; 
v___x_1629_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0___redArg(v_opt_1625_, v___y_1626_);
return v___x_1629_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0___boxed(lean_object* v_opt_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_){
_start:
{
lean_object* v_res_1634_; 
v_res_1634_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0(v_opt_1630_, v___y_1631_, v___y_1632_);
lean_dec(v___y_1632_);
lean_dec_ref(v___y_1631_);
lean_dec_ref(v_opt_1630_);
return v_res_1634_;
}
}
static lean_object* _init_l_Lean_ensureAttrDeclIsMeta___closed__1(void){
_start:
{
lean_object* v___x_1636_; lean_object* v___x_1637_; 
v___x_1636_ = ((lean_object*)(l_Lean_ensureAttrDeclIsMeta___closed__0));
v___x_1637_ = l_Lean_stringToMessageData(v___x_1636_);
return v___x_1637_;
}
}
LEAN_EXPORT lean_object* l_Lean_ensureAttrDeclIsMeta(lean_object* v_attrName_1638_, lean_object* v_declName_1639_, uint8_t v_attrKind_1640_, lean_object* v_a_1641_, lean_object* v_a_1642_){
_start:
{
lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v_env_1646_; lean_object* v___x_1647_; uint8_t v_isModule_1648_; 
v___x_1644_ = lean_st_ref_get(v_a_1642_);
v___x_1645_ = lean_st_ref_get(v_a_1642_);
v_env_1646_ = lean_ctor_get(v___x_1644_, 0);
lean_inc_ref(v_env_1646_);
lean_dec(v___x_1644_);
v___x_1647_ = l_Lean_Environment_header(v_env_1646_);
lean_dec_ref(v_env_1646_);
v_isModule_1648_ = lean_ctor_get_uint8(v___x_1647_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_1647_);
if (v_isModule_1648_ == 0)
{
lean_object* v___x_1649_; 
lean_dec(v___x_1645_);
v___x_1649_ = l_Lean_ensureAttrDeclIsPublic(v_attrName_1638_, v_declName_1639_, v_attrKind_1640_, v_a_1641_, v_a_1642_);
return v___x_1649_;
}
else
{
lean_object* v_env_1650_; uint8_t v___x_1651_; 
v_env_1650_ = lean_ctor_get(v___x_1645_, 0);
lean_inc_ref(v_env_1650_);
lean_dec(v___x_1645_);
lean_inc(v_declName_1639_);
v___x_1651_ = l_Lean_isMarkedMeta(v_env_1650_, v_declName_1639_);
if (v___x_1651_ == 0)
{
lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; 
v___x_1652_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1);
v___x_1653_ = l_Lean_MessageData_ofName(v_attrName_1638_);
v___x_1654_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1654_, 0, v___x_1652_);
lean_ctor_set(v___x_1654_, 1, v___x_1653_);
v___x_1655_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1, &l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1);
v___x_1656_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1656_, 0, v___x_1654_);
lean_ctor_set(v___x_1656_, 1, v___x_1655_);
v___x_1657_ = l_Lean_MessageData_ofConstName(v_declName_1639_, v___x_1651_);
v___x_1658_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1658_, 0, v___x_1656_);
lean_ctor_set(v___x_1658_, 1, v___x_1657_);
v___x_1659_ = lean_obj_once(&l_Lean_ensureAttrDeclIsMeta___closed__1, &l_Lean_ensureAttrDeclIsMeta___closed__1_once, _init_l_Lean_ensureAttrDeclIsMeta___closed__1);
v___x_1660_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1660_, 0, v___x_1658_);
lean_ctor_set(v___x_1660_, 1, v___x_1659_);
v___x_1661_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_1660_, v_a_1641_, v_a_1642_);
return v___x_1661_;
}
else
{
lean_object* v___x_1662_; 
v___x_1662_ = l_Lean_ensureAttrDeclIsPublic(v_attrName_1638_, v_declName_1639_, v_attrKind_1640_, v_a_1641_, v_a_1642_);
return v___x_1662_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ensureAttrDeclIsMeta___boxed(lean_object* v_attrName_1663_, lean_object* v_declName_1664_, lean_object* v_attrKind_1665_, lean_object* v_a_1666_, lean_object* v_a_1667_, lean_object* v_a_1668_){
_start:
{
uint8_t v_attrKind_boxed_1669_; lean_object* v_res_1670_; 
v_attrKind_boxed_1669_ = lean_unbox(v_attrKind_1665_);
v_res_1670_ = l_Lean_ensureAttrDeclIsMeta(v_attrName_1663_, v_declName_1664_, v_attrKind_boxed_1669_, v_a_1666_, v_a_1667_);
lean_dec(v_a_1667_);
lean_dec_ref(v_a_1666_);
return v_res_1670_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__0(lean_object* v_x_1674_, lean_object* v___y_1675_){
_start:
{
lean_object* v___x_1677_; lean_object* v___x_1678_; 
v___x_1677_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___lam__0___closed__1));
v___x_1678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1678_, 0, v___x_1677_);
return v___x_1678_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__0___boxed(lean_object* v_x_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_){
_start:
{
lean_object* v_res_1682_; 
v_res_1682_ = l_Lean_instInhabitedTagAttribute_default___lam__0(v_x_1679_, v___y_1680_);
lean_dec_ref(v___y_1680_);
lean_dec_ref(v_x_1679_);
return v_res_1682_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__1(lean_object* v_s_1683_, lean_object* v_x_1684_){
_start:
{
lean_inc(v_s_1683_);
return v_s_1683_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__1___boxed(lean_object* v_s_1685_, lean_object* v_x_1686_){
_start:
{
lean_object* v_res_1687_; 
v_res_1687_ = l_Lean_instInhabitedTagAttribute_default___lam__1(v_s_1685_, v_x_1686_);
lean_dec(v_x_1686_);
lean_dec(v_s_1685_);
return v_res_1687_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__2(lean_object* v_x_1692_, lean_object* v_x_1693_){
_start:
{
lean_object* v___x_1694_; 
v___x_1694_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___lam__2___closed__1));
return v___x_1694_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__2___boxed(lean_object* v_x_1695_, lean_object* v_x_1696_){
_start:
{
lean_object* v_res_1697_; 
v_res_1697_ = l_Lean_instInhabitedTagAttribute_default___lam__2(v_x_1695_, v_x_1696_);
lean_dec(v_x_1696_);
lean_dec_ref(v_x_1695_);
return v_res_1697_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__3(lean_object* v_x_1698_){
_start:
{
lean_object* v___x_1699_; 
v___x_1699_ = lean_box(0);
return v___x_1699_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__3___boxed(lean_object* v_x_1700_){
_start:
{
lean_object* v_res_1701_; 
v_res_1701_ = l_Lean_instInhabitedTagAttribute_default___lam__3(v_x_1700_);
lean_dec(v_x_1700_);
return v_res_1701_;
}
}
static lean_object* _init_l_Lean_instInhabitedTagAttribute_default___closed__4(void){
_start:
{
lean_object* v___x_1706_; 
v___x_1706_ = l_Lean_instInhabitedEnvExtension_default(lean_box(0));
return v___x_1706_;
}
}
static lean_object* _init_l_Lean_instInhabitedTagAttribute_default___closed__5(void){
_start:
{
lean_object* v___f_1707_; lean_object* v___f_1708_; lean_object* v___f_1709_; lean_object* v___f_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; 
v___f_1707_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___closed__3));
v___f_1708_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___closed__2));
v___f_1709_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___closed__1));
v___f_1710_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___closed__0));
v___x_1711_ = lean_box(0);
v___x_1712_ = lean_obj_once(&l_Lean_instInhabitedTagAttribute_default___closed__4, &l_Lean_instInhabitedTagAttribute_default___closed__4_once, _init_l_Lean_instInhabitedTagAttribute_default___closed__4);
v___x_1713_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1713_, 0, v___x_1712_);
lean_ctor_set(v___x_1713_, 1, v___x_1711_);
lean_ctor_set(v___x_1713_, 2, v___f_1710_);
lean_ctor_set(v___x_1713_, 3, v___f_1709_);
lean_ctor_set(v___x_1713_, 4, v___f_1708_);
lean_ctor_set(v___x_1713_, 5, v___f_1707_);
return v___x_1713_;
}
}
static lean_object* _init_l_Lean_instInhabitedTagAttribute_default___closed__6(void){
_start:
{
lean_object* v___x_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; 
v___x_1714_ = lean_obj_once(&l_Lean_instInhabitedTagAttribute_default___closed__5, &l_Lean_instInhabitedTagAttribute_default___closed__5_once, _init_l_Lean_instInhabitedTagAttribute_default___closed__5);
v___x_1715_ = ((lean_object*)(l_Lean_instInhabitedAttributeImpl_default));
v___x_1716_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1716_, 0, v___x_1715_);
lean_ctor_set(v___x_1716_, 1, v___x_1714_);
return v___x_1716_;
}
}
static lean_object* _init_l_Lean_instInhabitedTagAttribute_default(void){
_start:
{
lean_object* v___x_1717_; 
v___x_1717_ = lean_obj_once(&l_Lean_instInhabitedTagAttribute_default___closed__6, &l_Lean_instInhabitedTagAttribute_default___closed__6_once, _init_l_Lean_instInhabitedTagAttribute_default___closed__6);
return v___x_1717_;
}
}
static lean_object* _init_l_Lean_instInhabitedTagAttribute(void){
_start:
{
lean_object* v___x_1718_; 
v___x_1718_ = l_Lean_instInhabitedTagAttribute_default;
return v___x_1718_;
}
}
static lean_object* _init_l_Lean_registerTagAttribute___auto__1(void){
_start:
{
lean_object* v___x_1719_; 
v___x_1719_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__28, &l_Lean_AttributeImplCore_ref___autoParam___closed__28_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__28);
return v___x_1719_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__0(lean_object* v_x_1720_){
_start:
{
lean_object* v___x_1721_; 
v___x_1721_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___lam__2___closed__0));
return v___x_1721_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__0___boxed(lean_object* v_x_1722_){
_start:
{
lean_object* v_res_1723_; 
v_res_1723_ = l_Lean_registerTagAttribute___lam__0(v_x_1722_);
lean_dec(v_x_1722_);
return v_res_1723_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerTagAttribute_spec__0(lean_object* v_newState_1724_, lean_object* v_x_1725_, lean_object* v_x_1726_){
_start:
{
if (lean_obj_tag(v_x_1726_) == 0)
{
return v_x_1725_;
}
else
{
lean_object* v_head_1727_; lean_object* v_tail_1728_; uint8_t v___x_1729_; 
v_head_1727_ = lean_ctor_get(v_x_1726_, 0);
lean_inc(v_head_1727_);
v_tail_1728_ = lean_ctor_get(v_x_1726_, 1);
lean_inc(v_tail_1728_);
lean_dec_ref_known(v_x_1726_, 2);
v___x_1729_ = l_Lean_NameSet_contains(v_newState_1724_, v_head_1727_);
if (v___x_1729_ == 0)
{
lean_dec(v_head_1727_);
v_x_1726_ = v_tail_1728_;
goto _start;
}
else
{
lean_object* v___x_1731_; 
v___x_1731_ = l_Lean_NameSet_insert(v_x_1725_, v_head_1727_);
v_x_1725_ = v___x_1731_;
v_x_1726_ = v_tail_1728_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerTagAttribute_spec__0___boxed(lean_object* v_newState_1733_, lean_object* v_x_1734_, lean_object* v_x_1735_){
_start:
{
lean_object* v_res_1736_; 
v_res_1736_ = l_List_foldl___at___00Lean_registerTagAttribute_spec__0(v_newState_1733_, v_x_1734_, v_x_1735_);
lean_dec(v_newState_1733_);
return v_res_1736_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__1(lean_object* v_x_1737_, lean_object* v_newState_1738_, lean_object* v_newConsts_1739_, lean_object* v_s_1740_){
_start:
{
lean_object* v___x_1741_; 
v___x_1741_ = l_List_foldl___at___00Lean_registerTagAttribute_spec__0(v_newState_1738_, v_s_1740_, v_newConsts_1739_);
return v___x_1741_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__1___boxed(lean_object* v_x_1742_, lean_object* v_newState_1743_, lean_object* v_newConsts_1744_, lean_object* v_s_1745_){
_start:
{
lean_object* v_res_1746_; 
v_res_1746_ = l_Lean_registerTagAttribute___lam__1(v_x_1742_, v_newState_1743_, v_newConsts_1744_, v_s_1745_);
lean_dec(v_newState_1743_);
lean_dec(v_x_1742_);
return v_res_1746_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__2(lean_object* v_s_1759_){
_start:
{
lean_object* v___x_1760_; lean_object* v___y_1762_; 
v___x_1760_ = ((lean_object*)(l_Lean_registerTagAttribute___lam__2___closed__5));
if (lean_obj_tag(v_s_1759_) == 0)
{
lean_object* v_size_1766_; 
v_size_1766_ = lean_ctor_get(v_s_1759_, 0);
lean_inc(v_size_1766_);
lean_dec_ref_known(v_s_1759_, 5);
v___y_1762_ = v_size_1766_;
goto v___jp_1761_;
}
else
{
lean_object* v___x_1767_; 
v___x_1767_ = lean_unsigned_to_nat(0u);
v___y_1762_ = v___x_1767_;
goto v___jp_1761_;
}
v___jp_1761_:
{
lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; 
v___x_1763_ = l_Nat_reprFast(v___y_1762_);
v___x_1764_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1764_, 0, v___x_1763_);
v___x_1765_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1765_, 0, v___x_1760_);
lean_ctor_set(v___x_1765_, 1, v___x_1764_);
return v___x_1765_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4___redArg(lean_object* v_hi_1768_, lean_object* v_pivot_1769_, lean_object* v_as_1770_, lean_object* v_i_1771_, lean_object* v_k_1772_){
_start:
{
uint8_t v___x_1773_; 
v___x_1773_ = lean_nat_dec_lt(v_k_1772_, v_hi_1768_);
if (v___x_1773_ == 0)
{
lean_object* v___x_1774_; lean_object* v___x_1775_; 
lean_dec(v_k_1772_);
v___x_1774_ = lean_array_fswap(v_as_1770_, v_i_1771_, v_hi_1768_);
v___x_1775_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1775_, 0, v_i_1771_);
lean_ctor_set(v___x_1775_, 1, v___x_1774_);
return v___x_1775_;
}
else
{
lean_object* v___x_1776_; uint8_t v___x_1777_; 
v___x_1776_ = lean_array_fget_borrowed(v_as_1770_, v_k_1772_);
v___x_1777_ = l_Lean_Name_quickLt(v___x_1776_, v_pivot_1769_);
if (v___x_1777_ == 0)
{
lean_object* v___x_1778_; lean_object* v___x_1779_; 
v___x_1778_ = lean_unsigned_to_nat(1u);
v___x_1779_ = lean_nat_add(v_k_1772_, v___x_1778_);
lean_dec(v_k_1772_);
v_k_1772_ = v___x_1779_;
goto _start;
}
else
{
lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; 
v___x_1781_ = lean_array_fswap(v_as_1770_, v_i_1771_, v_k_1772_);
v___x_1782_ = lean_unsigned_to_nat(1u);
v___x_1783_ = lean_nat_add(v_i_1771_, v___x_1782_);
lean_dec(v_i_1771_);
v___x_1784_ = lean_nat_add(v_k_1772_, v___x_1782_);
lean_dec(v_k_1772_);
v_as_1770_ = v___x_1781_;
v_i_1771_ = v___x_1783_;
v_k_1772_ = v___x_1784_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4___redArg___boxed(lean_object* v_hi_1786_, lean_object* v_pivot_1787_, lean_object* v_as_1788_, lean_object* v_i_1789_, lean_object* v_k_1790_){
_start:
{
lean_object* v_res_1791_; 
v_res_1791_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4___redArg(v_hi_1786_, v_pivot_1787_, v_as_1788_, v_i_1789_, v_k_1790_);
lean_dec(v_pivot_1787_);
lean_dec(v_hi_1786_);
return v_res_1791_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___redArg(lean_object* v_n_1792_, lean_object* v_as_1793_, lean_object* v_lo_1794_, lean_object* v_hi_1795_){
_start:
{
lean_object* v___y_1797_; uint8_t v___x_1807_; 
v___x_1807_ = lean_nat_dec_lt(v_lo_1794_, v_hi_1795_);
if (v___x_1807_ == 0)
{
lean_dec(v_lo_1794_);
return v_as_1793_;
}
else
{
lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v_mid_1810_; lean_object* v___y_1812_; lean_object* v___y_1818_; lean_object* v___x_1823_; lean_object* v___x_1824_; uint8_t v___x_1825_; 
v___x_1808_ = lean_nat_add(v_lo_1794_, v_hi_1795_);
v___x_1809_ = lean_unsigned_to_nat(1u);
v_mid_1810_ = lean_nat_shiftr(v___x_1808_, v___x_1809_);
lean_dec(v___x_1808_);
v___x_1823_ = lean_array_fget_borrowed(v_as_1793_, v_mid_1810_);
v___x_1824_ = lean_array_fget_borrowed(v_as_1793_, v_lo_1794_);
v___x_1825_ = l_Lean_Name_quickLt(v___x_1823_, v___x_1824_);
if (v___x_1825_ == 0)
{
v___y_1818_ = v_as_1793_;
goto v___jp_1817_;
}
else
{
lean_object* v___x_1826_; 
v___x_1826_ = lean_array_fswap(v_as_1793_, v_lo_1794_, v_mid_1810_);
v___y_1818_ = v___x_1826_;
goto v___jp_1817_;
}
v___jp_1811_:
{
lean_object* v___x_1813_; lean_object* v___x_1814_; uint8_t v___x_1815_; 
v___x_1813_ = lean_array_fget_borrowed(v___y_1812_, v_mid_1810_);
v___x_1814_ = lean_array_fget_borrowed(v___y_1812_, v_hi_1795_);
v___x_1815_ = l_Lean_Name_quickLt(v___x_1813_, v___x_1814_);
if (v___x_1815_ == 0)
{
lean_dec(v_mid_1810_);
v___y_1797_ = v___y_1812_;
goto v___jp_1796_;
}
else
{
lean_object* v___x_1816_; 
v___x_1816_ = lean_array_fswap(v___y_1812_, v_mid_1810_, v_hi_1795_);
lean_dec(v_mid_1810_);
v___y_1797_ = v___x_1816_;
goto v___jp_1796_;
}
}
v___jp_1817_:
{
lean_object* v___x_1819_; lean_object* v___x_1820_; uint8_t v___x_1821_; 
v___x_1819_ = lean_array_fget_borrowed(v___y_1818_, v_hi_1795_);
v___x_1820_ = lean_array_fget_borrowed(v___y_1818_, v_lo_1794_);
v___x_1821_ = l_Lean_Name_quickLt(v___x_1819_, v___x_1820_);
if (v___x_1821_ == 0)
{
v___y_1812_ = v___y_1818_;
goto v___jp_1811_;
}
else
{
lean_object* v___x_1822_; 
v___x_1822_ = lean_array_fswap(v___y_1818_, v_lo_1794_, v_hi_1795_);
v___y_1812_ = v___x_1822_;
goto v___jp_1811_;
}
}
}
v___jp_1796_:
{
lean_object* v_pivot_1798_; lean_object* v___x_1799_; lean_object* v_fst_1800_; lean_object* v_snd_1801_; uint8_t v___x_1802_; 
v_pivot_1798_ = lean_array_fget(v___y_1797_, v_hi_1795_);
lean_inc_n(v_lo_1794_, 2);
v___x_1799_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4___redArg(v_hi_1795_, v_pivot_1798_, v___y_1797_, v_lo_1794_, v_lo_1794_);
lean_dec(v_pivot_1798_);
v_fst_1800_ = lean_ctor_get(v___x_1799_, 0);
lean_inc(v_fst_1800_);
v_snd_1801_ = lean_ctor_get(v___x_1799_, 1);
lean_inc(v_snd_1801_);
lean_dec_ref(v___x_1799_);
v___x_1802_ = lean_nat_dec_le(v_hi_1795_, v_fst_1800_);
if (v___x_1802_ == 0)
{
lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; 
v___x_1803_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___redArg(v_n_1792_, v_snd_1801_, v_lo_1794_, v_fst_1800_);
v___x_1804_ = lean_unsigned_to_nat(1u);
v___x_1805_ = lean_nat_add(v_fst_1800_, v___x_1804_);
lean_dec(v_fst_1800_);
v_as_1793_ = v___x_1803_;
v_lo_1794_ = v___x_1805_;
goto _start;
}
else
{
lean_dec(v_fst_1800_);
lean_dec(v_lo_1794_);
return v_snd_1801_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___redArg___boxed(lean_object* v_n_1827_, lean_object* v_as_1828_, lean_object* v_lo_1829_, lean_object* v_hi_1830_){
_start:
{
lean_object* v_res_1831_; 
v_res_1831_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___redArg(v_n_1827_, v_as_1828_, v_lo_1829_, v_hi_1830_);
lean_dec(v_hi_1830_);
lean_dec(v_n_1827_);
return v_res_1831_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerTagAttribute_spec__2(lean_object* v_env_1832_, lean_object* v_as_1833_, size_t v_i_1834_, size_t v_stop_1835_, lean_object* v_b_1836_){
_start:
{
lean_object* v___y_1838_; uint8_t v___x_1842_; 
v___x_1842_ = lean_usize_dec_eq(v_i_1834_, v_stop_1835_);
if (v___x_1842_ == 0)
{
lean_object* v___x_1843_; uint8_t v___x_1844_; lean_object* v___x_1845_; uint8_t v___x_1846_; 
v___x_1843_ = lean_array_uget_borrowed(v_as_1833_, v_i_1834_);
v___x_1844_ = 1;
lean_inc_ref(v_env_1832_);
v___x_1845_ = l_Lean_Environment_setExporting(v_env_1832_, v___x_1844_);
lean_inc(v___x_1843_);
v___x_1846_ = l_Lean_Environment_contains(v___x_1845_, v___x_1843_, v___x_1842_);
if (v___x_1846_ == 0)
{
v___y_1838_ = v_b_1836_;
goto v___jp_1837_;
}
else
{
lean_object* v___x_1847_; 
lean_inc(v___x_1843_);
v___x_1847_ = lean_array_push(v_b_1836_, v___x_1843_);
v___y_1838_ = v___x_1847_;
goto v___jp_1837_;
}
}
else
{
lean_dec_ref(v_env_1832_);
return v_b_1836_;
}
v___jp_1837_:
{
size_t v___x_1839_; size_t v___x_1840_; 
v___x_1839_ = ((size_t)1ULL);
v___x_1840_ = lean_usize_add(v_i_1834_, v___x_1839_);
v_i_1834_ = v___x_1840_;
v_b_1836_ = v___y_1838_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerTagAttribute_spec__2___boxed(lean_object* v_env_1848_, lean_object* v_as_1849_, lean_object* v_i_1850_, lean_object* v_stop_1851_, lean_object* v_b_1852_){
_start:
{
size_t v_i_boxed_1853_; size_t v_stop_boxed_1854_; lean_object* v_res_1855_; 
v_i_boxed_1853_ = lean_unbox_usize(v_i_1850_);
lean_dec(v_i_1850_);
v_stop_boxed_1854_ = lean_unbox_usize(v_stop_1851_);
lean_dec(v_stop_1851_);
v_res_1855_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerTagAttribute_spec__2(v_env_1848_, v_as_1849_, v_i_boxed_1853_, v_stop_boxed_1854_, v_b_1852_);
lean_dec_ref(v_as_1849_);
return v_res_1855_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerTagAttribute_spec__1_spec__1(lean_object* v_init_1856_, lean_object* v_x_1857_){
_start:
{
if (lean_obj_tag(v_x_1857_) == 0)
{
lean_object* v_k_1858_; lean_object* v_l_1859_; lean_object* v_r_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; 
v_k_1858_ = lean_ctor_get(v_x_1857_, 1);
lean_inc(v_k_1858_);
v_l_1859_ = lean_ctor_get(v_x_1857_, 3);
lean_inc(v_l_1859_);
v_r_1860_ = lean_ctor_get(v_x_1857_, 4);
lean_inc(v_r_1860_);
lean_dec_ref_known(v_x_1857_, 5);
v___x_1861_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerTagAttribute_spec__1_spec__1(v_init_1856_, v_l_1859_);
v___x_1862_ = lean_array_push(v___x_1861_, v_k_1858_);
v_init_1856_ = v___x_1862_;
v_x_1857_ = v_r_1860_;
goto _start;
}
else
{
return v_init_1856_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__3(lean_object* v_env_1864_, lean_object* v_es_1865_){
_start:
{
lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___y_1869_; lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___y_1886_; lean_object* v___y_1887_; uint8_t v___x_1889_; 
v___x_1866_ = lean_unsigned_to_nat(0u);
v___x_1867_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___lam__2___closed__0));
v___x_1883_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerTagAttribute_spec__1_spec__1(v___x_1867_, v_es_1865_);
v___x_1884_ = lean_array_get_size(v___x_1883_);
v___x_1889_ = lean_nat_dec_eq(v___x_1884_, v___x_1866_);
if (v___x_1889_ == 0)
{
lean_object* v___x_1890_; lean_object* v___x_1891_; lean_object* v___y_1893_; uint8_t v___x_1895_; 
v___x_1890_ = lean_unsigned_to_nat(1u);
v___x_1891_ = lean_nat_sub(v___x_1884_, v___x_1890_);
v___x_1895_ = lean_nat_dec_le(v___x_1866_, v___x_1891_);
if (v___x_1895_ == 0)
{
lean_inc(v___x_1891_);
v___y_1893_ = v___x_1891_;
goto v___jp_1892_;
}
else
{
v___y_1893_ = v___x_1866_;
goto v___jp_1892_;
}
v___jp_1892_:
{
uint8_t v___x_1894_; 
v___x_1894_ = lean_nat_dec_le(v___y_1893_, v___x_1891_);
if (v___x_1894_ == 0)
{
lean_dec(v___x_1891_);
lean_inc(v___y_1893_);
v___y_1886_ = v___y_1893_;
v___y_1887_ = v___y_1893_;
goto v___jp_1885_;
}
else
{
v___y_1886_ = v___y_1893_;
v___y_1887_ = v___x_1891_;
goto v___jp_1885_;
}
}
}
else
{
v___y_1869_ = v___x_1883_;
goto v___jp_1868_;
}
v___jp_1868_:
{
lean_object* v___x_1870_; uint8_t v___x_1871_; 
v___x_1870_ = lean_array_get_size(v___y_1869_);
v___x_1871_ = lean_nat_dec_lt(v___x_1866_, v___x_1870_);
if (v___x_1871_ == 0)
{
lean_object* v___x_1872_; 
lean_dec_ref(v_env_1864_);
v___x_1872_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1872_, 0, v___x_1867_);
lean_ctor_set(v___x_1872_, 1, v___x_1867_);
lean_ctor_set(v___x_1872_, 2, v___y_1869_);
return v___x_1872_;
}
else
{
uint8_t v___x_1873_; 
v___x_1873_ = lean_nat_dec_le(v___x_1870_, v___x_1870_);
if (v___x_1873_ == 0)
{
if (v___x_1871_ == 0)
{
lean_object* v___x_1874_; 
lean_dec_ref(v_env_1864_);
v___x_1874_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1874_, 0, v___x_1867_);
lean_ctor_set(v___x_1874_, 1, v___x_1867_);
lean_ctor_set(v___x_1874_, 2, v___y_1869_);
return v___x_1874_;
}
else
{
size_t v___x_1875_; size_t v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; 
v___x_1875_ = ((size_t)0ULL);
v___x_1876_ = lean_usize_of_nat(v___x_1870_);
v___x_1877_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerTagAttribute_spec__2(v_env_1864_, v___y_1869_, v___x_1875_, v___x_1876_, v___x_1867_);
lean_inc_ref(v___x_1877_);
v___x_1878_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1878_, 0, v___x_1877_);
lean_ctor_set(v___x_1878_, 1, v___x_1877_);
lean_ctor_set(v___x_1878_, 2, v___y_1869_);
return v___x_1878_;
}
}
else
{
size_t v___x_1879_; size_t v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; 
v___x_1879_ = ((size_t)0ULL);
v___x_1880_ = lean_usize_of_nat(v___x_1870_);
v___x_1881_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerTagAttribute_spec__2(v_env_1864_, v___y_1869_, v___x_1879_, v___x_1880_, v___x_1867_);
lean_inc_ref(v___x_1881_);
v___x_1882_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1882_, 0, v___x_1881_);
lean_ctor_set(v___x_1882_, 1, v___x_1881_);
lean_ctor_set(v___x_1882_, 2, v___y_1869_);
return v___x_1882_;
}
}
}
v___jp_1885_:
{
lean_object* v___x_1888_; 
v___x_1888_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___redArg(v___x_1884_, v___x_1883_, v___y_1886_, v___y_1887_);
lean_dec(v___y_1887_);
v___y_1869_ = v___x_1888_;
goto v___jp_1868_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__4(lean_object* v___x_1896_, lean_object* v_x_1897_, lean_object* v_x_1898_){
_start:
{
lean_object* v___x_1900_; 
v___x_1900_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1900_, 0, v___x_1896_);
return v___x_1900_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__4___boxed(lean_object* v___x_1901_, lean_object* v_x_1902_, lean_object* v_x_1903_, lean_object* v___y_1904_){
_start:
{
lean_object* v_res_1905_; 
v_res_1905_ = l_Lean_registerTagAttribute___lam__4(v___x_1901_, v_x_1902_, v_x_1903_);
lean_dec_ref(v_x_1903_);
lean_dec_ref(v_x_1902_);
return v_res_1905_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__5(lean_object* v___x_1906_){
_start:
{
lean_object* v___x_1908_; 
v___x_1908_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1908_, 0, v___x_1906_);
return v___x_1908_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__5___boxed(lean_object* v___x_1909_, lean_object* v___y_1910_){
_start:
{
lean_object* v_res_1911_; 
v_res_1911_ = l_Lean_registerTagAttribute___lam__5(v___x_1909_);
return v_res_1911_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__6(lean_object* v_name_1912_, lean_object* v_decl_1913_, lean_object* v___y_1914_, lean_object* v___y_1915_){
_start:
{
lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; 
v___x_1917_ = lean_obj_once(&l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1, &l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1_once, _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1);
v___x_1918_ = l_Lean_MessageData_ofName(v_name_1912_);
v___x_1919_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1919_, 0, v___x_1917_);
lean_ctor_set(v___x_1919_, 1, v___x_1918_);
v___x_1920_ = lean_obj_once(&l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3, &l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3_once, _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3);
v___x_1921_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1921_, 0, v___x_1919_);
lean_ctor_set(v___x_1921_, 1, v___x_1920_);
v___x_1922_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_1921_, v___y_1914_, v___y_1915_);
return v___x_1922_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__6___boxed(lean_object* v_name_1923_, lean_object* v_decl_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_){
_start:
{
lean_object* v_res_1928_; 
v_res_1928_ = l_Lean_registerTagAttribute___lam__6(v_name_1923_, v_decl_1924_, v___y_1925_, v___y_1926_);
lean_dec(v___y_1926_);
lean_dec_ref(v___y_1925_);
lean_dec(v_decl_1924_);
return v_res_1928_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg(lean_object* v_attrName_1929_, lean_object* v_declName_1930_, lean_object* v___y_1931_, lean_object* v___y_1932_){
_start:
{
lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; uint8_t v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; 
v___x_1934_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1);
v___x_1935_ = l_Lean_MessageData_ofName(v_attrName_1929_);
v___x_1936_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1936_, 0, v___x_1934_);
lean_ctor_set(v___x_1936_, 1, v___x_1935_);
v___x_1937_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__3, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__3_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__3);
v___x_1938_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1938_, 0, v___x_1936_);
lean_ctor_set(v___x_1938_, 1, v___x_1937_);
v___x_1939_ = 0;
v___x_1940_ = l_Lean_MessageData_ofConstName(v_declName_1930_, v___x_1939_);
v___x_1941_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1941_, 0, v___x_1938_);
lean_ctor_set(v___x_1941_, 1, v___x_1940_);
v___x_1942_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__5, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__5_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__5);
v___x_1943_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1943_, 0, v___x_1941_);
lean_ctor_set(v___x_1943_, 1, v___x_1942_);
v___x_1944_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_1943_, v___y_1931_, v___y_1932_);
return v___x_1944_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg___boxed(lean_object* v_attrName_1945_, lean_object* v_declName_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_){
_start:
{
lean_object* v_res_1950_; 
v_res_1950_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg(v_attrName_1945_, v_declName_1946_, v___y_1947_, v___y_1948_);
lean_dec(v___y_1948_);
lean_dec_ref(v___y_1947_);
return v_res_1950_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___redArg(lean_object* v_attrName_1951_, lean_object* v_declName_1952_, lean_object* v_asyncPrefix_x3f_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_){
_start:
{
lean_object* v___y_1958_; 
if (lean_obj_tag(v_asyncPrefix_x3f_1953_) == 0)
{
lean_object* v___x_1971_; 
v___x_1971_ = l_Lean_MessageData_nil;
v___y_1958_ = v___x_1971_;
goto v___jp_1957_;
}
else
{
lean_object* v_val_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; 
v_val_1972_ = lean_ctor_get(v_asyncPrefix_x3f_1953_, 0);
lean_inc(v_val_1972_);
lean_dec_ref_known(v_asyncPrefix_x3f_1953_, 1);
v___x_1973_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___redArg___closed__3, &l_Lean_throwAttrNotInAsyncCtx___redArg___closed__3_once, _init_l_Lean_throwAttrNotInAsyncCtx___redArg___closed__3);
v___x_1974_ = l_Lean_MessageData_ofName(v_val_1972_);
v___x_1975_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1975_, 0, v___x_1973_);
lean_ctor_set(v___x_1975_, 1, v___x_1974_);
v___x_1976_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__5, &l_Lean_throwAttrMustBeGlobal___redArg___closed__5_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__5);
v___x_1977_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1977_, 0, v___x_1975_);
lean_ctor_set(v___x_1977_, 1, v___x_1976_);
v___y_1958_ = v___x_1977_;
goto v___jp_1957_;
}
v___jp_1957_:
{
lean_object* v___x_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; uint8_t v___x_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; 
v___x_1959_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1);
v___x_1960_ = l_Lean_MessageData_ofName(v_attrName_1951_);
v___x_1961_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1961_, 0, v___x_1959_);
lean_ctor_set(v___x_1961_, 1, v___x_1960_);
v___x_1962_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__3, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__3_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__3);
v___x_1963_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1963_, 0, v___x_1961_);
lean_ctor_set(v___x_1963_, 1, v___x_1962_);
v___x_1964_ = 0;
v___x_1965_ = l_Lean_MessageData_ofConstName(v_declName_1952_, v___x_1964_);
v___x_1966_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1966_, 0, v___x_1963_);
lean_ctor_set(v___x_1966_, 1, v___x_1965_);
v___x_1967_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___redArg___closed__1, &l_Lean_throwAttrNotInAsyncCtx___redArg___closed__1_once, _init_l_Lean_throwAttrNotInAsyncCtx___redArg___closed__1);
v___x_1968_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1968_, 0, v___x_1966_);
lean_ctor_set(v___x_1968_, 1, v___x_1967_);
v___x_1969_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1969_, 0, v___x_1968_);
lean_ctor_set(v___x_1969_, 1, v___y_1958_);
v___x_1970_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_1969_, v___y_1954_, v___y_1955_);
return v___x_1970_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___redArg___boxed(lean_object* v_attrName_1978_, lean_object* v_declName_1979_, lean_object* v_asyncPrefix_x3f_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_){
_start:
{
lean_object* v_res_1984_; 
v_res_1984_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___redArg(v_attrName_1978_, v_declName_1979_, v_asyncPrefix_x3f_1980_, v___y_1981_, v___y_1982_);
lean_dec(v___y_1982_);
lean_dec_ref(v___y_1981_);
return v_res_1984_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg(lean_object* v_name_1985_, uint8_t v_kind_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_){
_start:
{
lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; lean_object* v___y_1996_; 
v___x_1990_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__1, &l_Lean_throwAttrMustBeGlobal___redArg___closed__1_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__1);
v___x_1991_ = l_Lean_MessageData_ofName(v_name_1985_);
v___x_1992_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1992_, 0, v___x_1990_);
lean_ctor_set(v___x_1992_, 1, v___x_1991_);
v___x_1993_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__3, &l_Lean_throwAttrMustBeGlobal___redArg___closed__3_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__3);
v___x_1994_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1994_, 0, v___x_1992_);
lean_ctor_set(v___x_1994_, 1, v___x_1993_);
switch(v_kind_1986_)
{
case 0:
{
lean_object* v___x_2003_; 
v___x_2003_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__0));
v___y_1996_ = v___x_2003_;
goto v___jp_1995_;
}
case 1:
{
lean_object* v___x_2004_; 
v___x_2004_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__1));
v___y_1996_ = v___x_2004_;
goto v___jp_1995_;
}
default: 
{
lean_object* v___x_2005_; 
v___x_2005_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__2));
v___y_1996_ = v___x_2005_;
goto v___jp_1995_;
}
}
v___jp_1995_:
{
lean_object* v___x_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; lean_object* v___x_2001_; lean_object* v___x_2002_; 
lean_inc_ref(v___y_1996_);
v___x_1997_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1997_, 0, v___y_1996_);
v___x_1998_ = l_Lean_MessageData_ofFormat(v___x_1997_);
v___x_1999_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1999_, 0, v___x_1994_);
lean_ctor_set(v___x_1999_, 1, v___x_1998_);
v___x_2000_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__5, &l_Lean_throwAttrMustBeGlobal___redArg___closed__5_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__5);
v___x_2001_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2001_, 0, v___x_1999_);
lean_ctor_set(v___x_2001_, 1, v___x_2000_);
v___x_2002_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_2001_, v___y_1987_, v___y_1988_);
return v___x_2002_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg___boxed(lean_object* v_name_2006_, lean_object* v_kind_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_){
_start:
{
uint8_t v_kind_boxed_2011_; lean_object* v_res_2012_; 
v_kind_boxed_2011_ = lean_unbox(v_kind_2007_);
v_res_2012_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg(v_name_2006_, v_kind_boxed_2011_, v___y_2008_, v___y_2009_);
lean_dec(v___y_2009_);
lean_dec_ref(v___y_2008_);
return v_res_2012_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__7(lean_object* v_validate_2013_, lean_object* v_a_2014_, lean_object* v_name_2015_, lean_object* v_decl_2016_, lean_object* v_stx_2017_, uint8_t v_kind_2018_, lean_object* v___y_2019_, lean_object* v___y_2020_){
_start:
{
lean_object* v___y_2023_; lean_object* v___y_2024_; lean_object* v___y_2058_; lean_object* v___y_2059_; lean_object* v___y_2060_; lean_object* v___y_2067_; lean_object* v___y_2068_; lean_object* v___x_2073_; 
v___x_2073_ = l_Lean_Attribute_Builtin_ensureNoArgs(v_stx_2017_, v___y_2019_, v___y_2020_);
if (lean_obj_tag(v___x_2073_) == 0)
{
uint8_t v___x_2074_; uint8_t v___x_2075_; 
lean_dec_ref_known(v___x_2073_, 1);
v___x_2074_ = 0;
v___x_2075_ = l_Lean_instBEqAttributeKind_beq(v_kind_2018_, v___x_2074_);
if (v___x_2075_ == 0)
{
lean_object* v___x_2076_; 
lean_dec(v_decl_2016_);
lean_dec_ref(v_a_2014_);
lean_dec_ref(v_validate_2013_);
v___x_2076_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg(v_name_2015_, v_kind_2018_, v___y_2019_, v___y_2020_);
return v___x_2076_;
}
else
{
v___y_2067_ = v___y_2019_;
v___y_2068_ = v___y_2020_;
goto v___jp_2066_;
}
}
else
{
lean_dec(v_decl_2016_);
lean_dec(v_name_2015_);
lean_dec_ref(v_a_2014_);
lean_dec_ref(v_validate_2013_);
return v___x_2073_;
}
v___jp_2022_:
{
lean_object* v___x_2025_; 
lean_inc(v___y_2024_);
lean_inc_ref(v___y_2023_);
lean_inc(v_decl_2016_);
v___x_2025_ = lean_apply_4(v_validate_2013_, v_decl_2016_, v___y_2023_, v___y_2024_, lean_box(0));
if (lean_obj_tag(v___x_2025_) == 0)
{
lean_object* v___x_2027_; uint8_t v_isShared_2028_; uint8_t v_isSharedCheck_2055_; 
v_isSharedCheck_2055_ = !lean_is_exclusive(v___x_2025_);
if (v_isSharedCheck_2055_ == 0)
{
lean_object* v_unused_2056_; 
v_unused_2056_ = lean_ctor_get(v___x_2025_, 0);
lean_dec(v_unused_2056_);
v___x_2027_ = v___x_2025_;
v_isShared_2028_ = v_isSharedCheck_2055_;
goto v_resetjp_2026_;
}
else
{
lean_dec(v___x_2025_);
v___x_2027_ = lean_box(0);
v_isShared_2028_ = v_isSharedCheck_2055_;
goto v_resetjp_2026_;
}
v_resetjp_2026_:
{
lean_object* v___x_2029_; lean_object* v_toEnvExtension_2030_; lean_object* v_env_2031_; lean_object* v_nextMacroScope_2032_; lean_object* v_ngen_2033_; lean_object* v_auxDeclNGen_2034_; lean_object* v_traceState_2035_; lean_object* v_messages_2036_; lean_object* v_infoState_2037_; lean_object* v_snapshotTasks_2038_; lean_object* v___x_2040_; uint8_t v_isShared_2041_; uint8_t v_isSharedCheck_2053_; 
v___x_2029_ = lean_st_ref_take(v___y_2024_);
v_toEnvExtension_2030_ = lean_ctor_get(v_a_2014_, 0);
v_env_2031_ = lean_ctor_get(v___x_2029_, 0);
v_nextMacroScope_2032_ = lean_ctor_get(v___x_2029_, 1);
v_ngen_2033_ = lean_ctor_get(v___x_2029_, 2);
v_auxDeclNGen_2034_ = lean_ctor_get(v___x_2029_, 3);
v_traceState_2035_ = lean_ctor_get(v___x_2029_, 4);
v_messages_2036_ = lean_ctor_get(v___x_2029_, 6);
v_infoState_2037_ = lean_ctor_get(v___x_2029_, 7);
v_snapshotTasks_2038_ = lean_ctor_get(v___x_2029_, 8);
v_isSharedCheck_2053_ = !lean_is_exclusive(v___x_2029_);
if (v_isSharedCheck_2053_ == 0)
{
lean_object* v_unused_2054_; 
v_unused_2054_ = lean_ctor_get(v___x_2029_, 5);
lean_dec(v_unused_2054_);
v___x_2040_ = v___x_2029_;
v_isShared_2041_ = v_isSharedCheck_2053_;
goto v_resetjp_2039_;
}
else
{
lean_inc(v_snapshotTasks_2038_);
lean_inc(v_infoState_2037_);
lean_inc(v_messages_2036_);
lean_inc(v_traceState_2035_);
lean_inc(v_auxDeclNGen_2034_);
lean_inc(v_ngen_2033_);
lean_inc(v_nextMacroScope_2032_);
lean_inc(v_env_2031_);
lean_dec(v___x_2029_);
v___x_2040_ = lean_box(0);
v_isShared_2041_ = v_isSharedCheck_2053_;
goto v_resetjp_2039_;
}
v_resetjp_2039_:
{
lean_object* v_asyncMode_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2046_; 
v_asyncMode_2042_ = lean_ctor_get(v_toEnvExtension_2030_, 2);
lean_inc(v_asyncMode_2042_);
lean_inc(v_decl_2016_);
v___x_2043_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_a_2014_, v_env_2031_, v_decl_2016_, v_asyncMode_2042_, v_decl_2016_);
lean_dec(v_asyncMode_2042_);
v___x_2044_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2);
if (v_isShared_2041_ == 0)
{
lean_ctor_set(v___x_2040_, 5, v___x_2044_);
lean_ctor_set(v___x_2040_, 0, v___x_2043_);
v___x_2046_ = v___x_2040_;
goto v_reusejp_2045_;
}
else
{
lean_object* v_reuseFailAlloc_2052_; 
v_reuseFailAlloc_2052_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2052_, 0, v___x_2043_);
lean_ctor_set(v_reuseFailAlloc_2052_, 1, v_nextMacroScope_2032_);
lean_ctor_set(v_reuseFailAlloc_2052_, 2, v_ngen_2033_);
lean_ctor_set(v_reuseFailAlloc_2052_, 3, v_auxDeclNGen_2034_);
lean_ctor_set(v_reuseFailAlloc_2052_, 4, v_traceState_2035_);
lean_ctor_set(v_reuseFailAlloc_2052_, 5, v___x_2044_);
lean_ctor_set(v_reuseFailAlloc_2052_, 6, v_messages_2036_);
lean_ctor_set(v_reuseFailAlloc_2052_, 7, v_infoState_2037_);
lean_ctor_set(v_reuseFailAlloc_2052_, 8, v_snapshotTasks_2038_);
v___x_2046_ = v_reuseFailAlloc_2052_;
goto v_reusejp_2045_;
}
v_reusejp_2045_:
{
lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2050_; 
v___x_2047_ = lean_st_ref_set(v___y_2024_, v___x_2046_);
v___x_2048_ = lean_box(0);
if (v_isShared_2028_ == 0)
{
lean_ctor_set(v___x_2027_, 0, v___x_2048_);
v___x_2050_ = v___x_2027_;
goto v_reusejp_2049_;
}
else
{
lean_object* v_reuseFailAlloc_2051_; 
v_reuseFailAlloc_2051_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2051_, 0, v___x_2048_);
v___x_2050_ = v_reuseFailAlloc_2051_;
goto v_reusejp_2049_;
}
v_reusejp_2049_:
{
return v___x_2050_;
}
}
}
}
}
else
{
lean_dec(v_decl_2016_);
lean_dec_ref(v_a_2014_);
return v___x_2025_;
}
}
v___jp_2057_:
{
lean_object* v_toEnvExtension_2061_; lean_object* v_asyncMode_2062_; uint8_t v___x_2063_; 
v_toEnvExtension_2061_ = lean_ctor_get(v_a_2014_, 0);
v_asyncMode_2062_ = lean_ctor_get(v_toEnvExtension_2061_, 2);
lean_inc(v_decl_2016_);
lean_inc_ref(v___y_2058_);
v___x_2063_ = l_Lean_EnvExtension_asyncMayModify___redArg(v___y_2058_, v_decl_2016_, v_asyncMode_2062_);
if (v___x_2063_ == 0)
{
lean_object* v___x_2064_; lean_object* v___x_2065_; 
lean_dec_ref(v_a_2014_);
lean_dec_ref(v_validate_2013_);
v___x_2064_ = l_Lean_Environment_asyncPrefix_x3f(v___y_2058_);
v___x_2065_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___redArg(v_name_2015_, v_decl_2016_, v___x_2064_, v___y_2059_, v___y_2060_);
return v___x_2065_;
}
else
{
lean_dec_ref(v___y_2058_);
lean_dec(v_name_2015_);
v___y_2023_ = v___y_2059_;
v___y_2024_ = v___y_2060_;
goto v___jp_2022_;
}
}
v___jp_2066_:
{
lean_object* v___x_2069_; lean_object* v_env_2070_; lean_object* v___x_2071_; 
v___x_2069_ = lean_st_ref_get(v___y_2068_);
v_env_2070_ = lean_ctor_get(v___x_2069_, 0);
lean_inc_ref(v_env_2070_);
lean_dec(v___x_2069_);
v___x_2071_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2070_, v_decl_2016_);
if (lean_obj_tag(v___x_2071_) == 0)
{
v___y_2058_ = v_env_2070_;
v___y_2059_ = v___y_2067_;
v___y_2060_ = v___y_2068_;
goto v___jp_2057_;
}
else
{
lean_object* v___x_2072_; 
lean_dec_ref_known(v___x_2071_, 1);
lean_dec_ref(v_env_2070_);
lean_dec_ref(v_a_2014_);
lean_dec_ref(v_validate_2013_);
v___x_2072_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg(v_name_2015_, v_decl_2016_, v___y_2067_, v___y_2068_);
return v___x_2072_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__7___boxed(lean_object* v_validate_2077_, lean_object* v_a_2078_, lean_object* v_name_2079_, lean_object* v_decl_2080_, lean_object* v_stx_2081_, lean_object* v_kind_2082_, lean_object* v___y_2083_, lean_object* v___y_2084_, lean_object* v___y_2085_){
_start:
{
uint8_t v_kind_boxed_2086_; lean_object* v_res_2087_; 
v_kind_boxed_2086_ = lean_unbox(v_kind_2082_);
v_res_2087_ = l_Lean_registerTagAttribute___lam__7(v_validate_2077_, v_a_2078_, v_name_2079_, v_decl_2080_, v_stx_2081_, v_kind_boxed_2086_, v___y_2083_, v___y_2084_);
lean_dec(v___y_2084_);
lean_dec_ref(v___y_2083_);
return v_res_2087_;
}
}
static lean_object* _init_l_Lean_registerTagAttribute___closed__5(void){
_start:
{
lean_object* v___x_2093_; lean_object* v___f_2094_; 
v___x_2093_ = l_Lean_NameSet_empty;
v___f_2094_ = lean_alloc_closure((void*)(l_Lean_registerTagAttribute___lam__4___boxed), 4, 1);
lean_closure_set(v___f_2094_, 0, v___x_2093_);
return v___f_2094_;
}
}
static lean_object* _init_l_Lean_registerTagAttribute___closed__6(void){
_start:
{
lean_object* v___x_2095_; lean_object* v___f_2096_; 
v___x_2095_ = l_Lean_NameSet_empty;
v___f_2096_ = lean_alloc_closure((void*)(l_Lean_registerTagAttribute___lam__5___boxed), 2, 1);
lean_closure_set(v___f_2096_, 0, v___x_2095_);
return v___f_2096_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute(lean_object* v_name_2099_, lean_object* v_descr_2100_, lean_object* v_validate_2101_, lean_object* v_ref_2102_, uint8_t v_applicationTime_2103_, lean_object* v_asyncMode_2104_){
_start:
{
lean_object* v___f_2106_; lean_object* v___f_2107_; lean_object* v___f_2108_; lean_object* v___f_2109_; lean_object* v___f_2110_; lean_object* v___f_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; 
v___f_2106_ = ((lean_object*)(l_Lean_registerTagAttribute___closed__0));
v___f_2107_ = ((lean_object*)(l_Lean_registerTagAttribute___closed__2));
v___f_2108_ = ((lean_object*)(l_Lean_registerTagAttribute___closed__3));
v___f_2109_ = ((lean_object*)(l_Lean_registerTagAttribute___closed__4));
v___f_2110_ = lean_obj_once(&l_Lean_registerTagAttribute___closed__5, &l_Lean_registerTagAttribute___closed__5_once, _init_l_Lean_registerTagAttribute___closed__5);
v___f_2111_ = lean_obj_once(&l_Lean_registerTagAttribute___closed__6, &l_Lean_registerTagAttribute___closed__6_once, _init_l_Lean_registerTagAttribute___closed__6);
v___x_2112_ = ((lean_object*)(l_Lean_registerTagAttribute___closed__7));
lean_inc(v_ref_2102_);
v___x_2113_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_2113_, 0, v_ref_2102_);
lean_ctor_set(v___x_2113_, 1, v___f_2111_);
lean_ctor_set(v___x_2113_, 2, v___f_2110_);
lean_ctor_set(v___x_2113_, 3, v___f_2109_);
lean_ctor_set(v___x_2113_, 4, v___f_2108_);
lean_ctor_set(v___x_2113_, 5, v___f_2107_);
lean_ctor_set(v___x_2113_, 6, v_asyncMode_2104_);
lean_ctor_set(v___x_2113_, 7, v___x_2112_);
v___x_2114_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2114_, 0, v___x_2113_);
lean_ctor_set(v___x_2114_, 1, v___f_2106_);
v___x_2115_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_2114_);
if (lean_obj_tag(v___x_2115_) == 0)
{
lean_object* v_a_2116_; lean_object* v___f_2117_; lean_object* v___f_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; 
v_a_2116_ = lean_ctor_get(v___x_2115_, 0);
lean_inc_n(v_a_2116_, 2);
lean_dec_ref_known(v___x_2115_, 1);
lean_inc_n(v_name_2099_, 2);
v___f_2117_ = lean_alloc_closure((void*)(l_Lean_registerTagAttribute___lam__6___boxed), 5, 1);
lean_closure_set(v___f_2117_, 0, v_name_2099_);
v___f_2118_ = lean_alloc_closure((void*)(l_Lean_registerTagAttribute___lam__7___boxed), 9, 3);
lean_closure_set(v___f_2118_, 0, v_validate_2101_);
lean_closure_set(v___f_2118_, 1, v_a_2116_);
lean_closure_set(v___f_2118_, 2, v_name_2099_);
v___x_2119_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2119_, 0, v_ref_2102_);
lean_ctor_set(v___x_2119_, 1, v_name_2099_);
lean_ctor_set(v___x_2119_, 2, v_descr_2100_);
lean_ctor_set_uint8(v___x_2119_, sizeof(void*)*3, v_applicationTime_2103_);
v___x_2120_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2120_, 0, v___x_2119_);
lean_ctor_set(v___x_2120_, 1, v___f_2118_);
lean_ctor_set(v___x_2120_, 2, v___f_2117_);
lean_inc_ref(v___x_2120_);
v___x_2121_ = l_Lean_registerBuiltinAttribute(v___x_2120_);
if (lean_obj_tag(v___x_2121_) == 0)
{
lean_object* v___x_2123_; uint8_t v_isShared_2124_; uint8_t v_isSharedCheck_2129_; 
v_isSharedCheck_2129_ = !lean_is_exclusive(v___x_2121_);
if (v_isSharedCheck_2129_ == 0)
{
lean_object* v_unused_2130_; 
v_unused_2130_ = lean_ctor_get(v___x_2121_, 0);
lean_dec(v_unused_2130_);
v___x_2123_ = v___x_2121_;
v_isShared_2124_ = v_isSharedCheck_2129_;
goto v_resetjp_2122_;
}
else
{
lean_dec(v___x_2121_);
v___x_2123_ = lean_box(0);
v_isShared_2124_ = v_isSharedCheck_2129_;
goto v_resetjp_2122_;
}
v_resetjp_2122_:
{
lean_object* v___x_2125_; lean_object* v___x_2127_; 
v___x_2125_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2125_, 0, v___x_2120_);
lean_ctor_set(v___x_2125_, 1, v_a_2116_);
if (v_isShared_2124_ == 0)
{
lean_ctor_set(v___x_2123_, 0, v___x_2125_);
v___x_2127_ = v___x_2123_;
goto v_reusejp_2126_;
}
else
{
lean_object* v_reuseFailAlloc_2128_; 
v_reuseFailAlloc_2128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2128_, 0, v___x_2125_);
v___x_2127_ = v_reuseFailAlloc_2128_;
goto v_reusejp_2126_;
}
v_reusejp_2126_:
{
return v___x_2127_;
}
}
}
else
{
lean_object* v_a_2131_; lean_object* v___x_2133_; uint8_t v_isShared_2134_; uint8_t v_isSharedCheck_2138_; 
lean_dec_ref_known(v___x_2120_, 3);
lean_dec(v_a_2116_);
v_a_2131_ = lean_ctor_get(v___x_2121_, 0);
v_isSharedCheck_2138_ = !lean_is_exclusive(v___x_2121_);
if (v_isSharedCheck_2138_ == 0)
{
v___x_2133_ = v___x_2121_;
v_isShared_2134_ = v_isSharedCheck_2138_;
goto v_resetjp_2132_;
}
else
{
lean_inc(v_a_2131_);
lean_dec(v___x_2121_);
v___x_2133_ = lean_box(0);
v_isShared_2134_ = v_isSharedCheck_2138_;
goto v_resetjp_2132_;
}
v_resetjp_2132_:
{
lean_object* v___x_2136_; 
if (v_isShared_2134_ == 0)
{
v___x_2136_ = v___x_2133_;
goto v_reusejp_2135_;
}
else
{
lean_object* v_reuseFailAlloc_2137_; 
v_reuseFailAlloc_2137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2137_, 0, v_a_2131_);
v___x_2136_ = v_reuseFailAlloc_2137_;
goto v_reusejp_2135_;
}
v_reusejp_2135_:
{
return v___x_2136_;
}
}
}
}
else
{
lean_object* v_a_2139_; lean_object* v___x_2141_; uint8_t v_isShared_2142_; uint8_t v_isSharedCheck_2146_; 
lean_dec(v_ref_2102_);
lean_dec_ref(v_validate_2101_);
lean_dec_ref(v_descr_2100_);
lean_dec(v_name_2099_);
v_a_2139_ = lean_ctor_get(v___x_2115_, 0);
v_isSharedCheck_2146_ = !lean_is_exclusive(v___x_2115_);
if (v_isSharedCheck_2146_ == 0)
{
v___x_2141_ = v___x_2115_;
v_isShared_2142_ = v_isSharedCheck_2146_;
goto v_resetjp_2140_;
}
else
{
lean_inc(v_a_2139_);
lean_dec(v___x_2115_);
v___x_2141_ = lean_box(0);
v_isShared_2142_ = v_isSharedCheck_2146_;
goto v_resetjp_2140_;
}
v_resetjp_2140_:
{
lean_object* v___x_2144_; 
if (v_isShared_2142_ == 0)
{
v___x_2144_ = v___x_2141_;
goto v_reusejp_2143_;
}
else
{
lean_object* v_reuseFailAlloc_2145_; 
v_reuseFailAlloc_2145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2145_, 0, v_a_2139_);
v___x_2144_ = v_reuseFailAlloc_2145_;
goto v_reusejp_2143_;
}
v_reusejp_2143_:
{
return v___x_2144_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___boxed(lean_object* v_name_2147_, lean_object* v_descr_2148_, lean_object* v_validate_2149_, lean_object* v_ref_2150_, lean_object* v_applicationTime_2151_, lean_object* v_asyncMode_2152_, lean_object* v_a_2153_){
_start:
{
uint8_t v_applicationTime_boxed_2154_; lean_object* v_res_2155_; 
v_applicationTime_boxed_2154_ = lean_unbox(v_applicationTime_2151_);
v_res_2155_ = l_Lean_registerTagAttribute(v_name_2147_, v_descr_2148_, v_validate_2149_, v_ref_2150_, v_applicationTime_boxed_2154_, v_asyncMode_2152_);
return v_res_2155_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerTagAttribute_spec__1(lean_object* v_init_2156_, lean_object* v_t_2157_){
_start:
{
lean_object* v___x_2158_; 
v___x_2158_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerTagAttribute_spec__1_spec__1(v_init_2156_, v_t_2157_);
return v___x_2158_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3(lean_object* v_n_2159_, lean_object* v_as_2160_, lean_object* v_lo_2161_, lean_object* v_hi_2162_, lean_object* v_w_2163_, lean_object* v_hlo_2164_, lean_object* v_hhi_2165_){
_start:
{
lean_object* v___x_2166_; 
v___x_2166_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___redArg(v_n_2159_, v_as_2160_, v_lo_2161_, v_hi_2162_);
return v___x_2166_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___boxed(lean_object* v_n_2167_, lean_object* v_as_2168_, lean_object* v_lo_2169_, lean_object* v_hi_2170_, lean_object* v_w_2171_, lean_object* v_hlo_2172_, lean_object* v_hhi_2173_){
_start:
{
lean_object* v_res_2174_; 
v_res_2174_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3(v_n_2167_, v_as_2168_, v_lo_2169_, v_hi_2170_, v_w_2171_, v_hlo_2172_, v_hhi_2173_);
lean_dec(v_hi_2170_);
lean_dec(v_n_2167_);
return v_res_2174_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4(lean_object* v_00_u03b1_2175_, lean_object* v_attrName_2176_, lean_object* v_declName_2177_, lean_object* v_asyncPrefix_x3f_2178_, lean_object* v___y_2179_, lean_object* v___y_2180_){
_start:
{
lean_object* v___x_2182_; 
v___x_2182_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___redArg(v_attrName_2176_, v_declName_2177_, v_asyncPrefix_x3f_2178_, v___y_2179_, v___y_2180_);
return v___x_2182_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___boxed(lean_object* v_00_u03b1_2183_, lean_object* v_attrName_2184_, lean_object* v_declName_2185_, lean_object* v_asyncPrefix_x3f_2186_, lean_object* v___y_2187_, lean_object* v___y_2188_, lean_object* v___y_2189_){
_start:
{
lean_object* v_res_2190_; 
v_res_2190_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4(v_00_u03b1_2183_, v_attrName_2184_, v_declName_2185_, v_asyncPrefix_x3f_2186_, v___y_2187_, v___y_2188_);
lean_dec(v___y_2188_);
lean_dec_ref(v___y_2187_);
return v_res_2190_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5(lean_object* v_00_u03b1_2191_, lean_object* v_attrName_2192_, lean_object* v_declName_2193_, lean_object* v___y_2194_, lean_object* v___y_2195_){
_start:
{
lean_object* v___x_2197_; 
v___x_2197_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg(v_attrName_2192_, v_declName_2193_, v___y_2194_, v___y_2195_);
return v___x_2197_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___boxed(lean_object* v_00_u03b1_2198_, lean_object* v_attrName_2199_, lean_object* v_declName_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_, lean_object* v___y_2203_){
_start:
{
lean_object* v_res_2204_; 
v_res_2204_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5(v_00_u03b1_2198_, v_attrName_2199_, v_declName_2200_, v___y_2201_, v___y_2202_);
lean_dec(v___y_2202_);
lean_dec_ref(v___y_2201_);
return v_res_2204_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6(lean_object* v_00_u03b1_2205_, lean_object* v_name_2206_, uint8_t v_kind_2207_, lean_object* v___y_2208_, lean_object* v___y_2209_){
_start:
{
lean_object* v___x_2211_; 
v___x_2211_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg(v_name_2206_, v_kind_2207_, v___y_2208_, v___y_2209_);
return v___x_2211_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___boxed(lean_object* v_00_u03b1_2212_, lean_object* v_name_2213_, lean_object* v_kind_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_){
_start:
{
uint8_t v_kind_boxed_2218_; lean_object* v_res_2219_; 
v_kind_boxed_2218_ = lean_unbox(v_kind_2214_);
v_res_2219_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6(v_00_u03b1_2212_, v_name_2213_, v_kind_boxed_2218_, v___y_2215_, v___y_2216_);
lean_dec(v___y_2216_);
lean_dec_ref(v___y_2215_);
return v_res_2219_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4(lean_object* v_n_2220_, lean_object* v_lo_2221_, lean_object* v_hi_2222_, lean_object* v_hhi_2223_, lean_object* v_pivot_2224_, lean_object* v_as_2225_, lean_object* v_i_2226_, lean_object* v_k_2227_, lean_object* v_ilo_2228_, lean_object* v_ik_2229_, lean_object* v_w_2230_){
_start:
{
lean_object* v___x_2231_; 
v___x_2231_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4___redArg(v_hi_2222_, v_pivot_2224_, v_as_2225_, v_i_2226_, v_k_2227_);
return v___x_2231_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4___boxed(lean_object* v_n_2232_, lean_object* v_lo_2233_, lean_object* v_hi_2234_, lean_object* v_hhi_2235_, lean_object* v_pivot_2236_, lean_object* v_as_2237_, lean_object* v_i_2238_, lean_object* v_k_2239_, lean_object* v_ilo_2240_, lean_object* v_ik_2241_, lean_object* v_w_2242_){
_start:
{
lean_object* v_res_2243_; 
v_res_2243_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4(v_n_2232_, v_lo_2233_, v_hi_2234_, v_hhi_2235_, v_pivot_2236_, v_as_2237_, v_i_2238_, v_k_2239_, v_ilo_2240_, v_ik_2241_, v_w_2242_);
lean_dec(v_pivot_2236_);
lean_dec(v_hi_2234_);
lean_dec(v_lo_2233_);
lean_dec(v_n_2232_);
return v_res_2243_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg___lam__0(lean_object* v_attr_2244_, lean_object* v_decl_2245_, lean_object* v_env_2246_){
_start:
{
lean_object* v_ext_2247_; lean_object* v_toEnvExtension_2248_; lean_object* v_asyncMode_2249_; lean_object* v___x_2250_; 
v_ext_2247_ = lean_ctor_get(v_attr_2244_, 1);
lean_inc_ref(v_ext_2247_);
lean_dec_ref(v_attr_2244_);
v_toEnvExtension_2248_ = lean_ctor_get(v_ext_2247_, 0);
v_asyncMode_2249_ = lean_ctor_get(v_toEnvExtension_2248_, 2);
lean_inc(v_asyncMode_2249_);
lean_inc(v_decl_2245_);
v___x_2250_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_ext_2247_, v_env_2246_, v_decl_2245_, v_asyncMode_2249_, v_decl_2245_);
lean_dec(v_asyncMode_2249_);
return v___x_2250_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg___lam__1(lean_object* v_modifyEnv_2251_, lean_object* v___f_2252_, lean_object* v_____r_2253_){
_start:
{
lean_object* v___x_2254_; 
v___x_2254_ = lean_apply_1(v_modifyEnv_2251_, v___f_2252_);
return v___x_2254_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg___lam__2(lean_object* v_attr_2255_, lean_object* v_env_2256_, lean_object* v_decl_2257_, lean_object* v_inst_2258_, lean_object* v_inst_2259_, lean_object* v_toBind_2260_, lean_object* v___f_2261_, lean_object* v_modifyEnv_2262_, lean_object* v___f_2263_, lean_object* v_____r_2264_){
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
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg___lam__3(lean_object* v___f_2276_, lean_object* v_____r_2277_){
_start:
{
lean_object* v___x_2278_; 
v___x_2278_ = lean_apply_1(v___f_2276_, v_____r_2277_);
return v___x_2278_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg___lam__4(lean_object* v_attr_2279_, lean_object* v_decl_2280_, lean_object* v_inst_2281_, lean_object* v_inst_2282_, lean_object* v_toBind_2283_, lean_object* v___f_2284_, lean_object* v_modifyEnv_2285_, lean_object* v___f_2286_, lean_object* v_env_2287_){
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
v___f_2288_ = lean_alloc_closure((void*)(l_Lean_TagAttribute_setTag___redArg___lam__2), 10, 9);
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
v___x_2291_ = l_Lean_TagAttribute_setTag___redArg___lam__2(v_attr_2279_, v_env_2287_, v_decl_2280_, v_inst_2281_, v_inst_2282_, v_toBind_2283_, v___f_2284_, v_modifyEnv_2285_, v___f_2286_, v___x_2290_);
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
v___f_2295_ = lean_alloc_closure((void*)(l_Lean_TagAttribute_setTag___redArg___lam__3), 2, 1);
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
v___f_2306_ = lean_alloc_closure((void*)(l_Lean_TagAttribute_setTag___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2306_, 0, v_attr_2301_);
lean_closure_set(v___f_2306_, 1, v_decl_2302_);
lean_inc_ref(v___f_2306_);
v___f_2307_ = lean_alloc_closure((void*)(l_Lean_TagAttribute_setTag___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2307_, 0, v_modifyEnv_2305_);
lean_closure_set(v___f_2307_, 1, v___f_2306_);
v___f_2308_ = lean_alloc_closure((void*)(l_Lean_TagAttribute_setTag___redArg___lam__4), 9, 8);
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
LEAN_EXPORT uint8_t l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___redArg(lean_object* v_as_2317_, lean_object* v_k_2318_, lean_object* v_x_2319_, lean_object* v_x_2320_){
_start:
{
lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v_m_2323_; lean_object* v_a_2324_; uint8_t v___x_2325_; 
v___x_2321_ = lean_nat_add(v_x_2319_, v_x_2320_);
v___x_2322_ = lean_unsigned_to_nat(1u);
v_m_2323_ = lean_nat_shiftr(v___x_2321_, v___x_2322_);
lean_dec(v___x_2321_);
v_a_2324_ = lean_array_fget_borrowed(v_as_2317_, v_m_2323_);
v___x_2325_ = l_Lean_Name_quickLt(v_a_2324_, v_k_2318_);
if (v___x_2325_ == 0)
{
uint8_t v___x_2326_; 
lean_dec(v_x_2320_);
v___x_2326_ = l_Lean_Name_quickLt(v_k_2318_, v_a_2324_);
if (v___x_2326_ == 0)
{
uint8_t v___x_2327_; 
lean_dec(v_m_2323_);
lean_dec(v_x_2319_);
v___x_2327_ = 1;
return v___x_2327_;
}
else
{
lean_object* v___x_2328_; uint8_t v___x_2329_; 
v___x_2328_ = lean_unsigned_to_nat(0u);
v___x_2329_ = lean_nat_dec_eq(v_m_2323_, v___x_2328_);
if (v___x_2329_ == 0)
{
lean_object* v___x_2330_; uint8_t v___x_2331_; 
v___x_2330_ = lean_nat_sub(v_m_2323_, v___x_2322_);
lean_dec(v_m_2323_);
v___x_2331_ = lean_nat_dec_lt(v___x_2330_, v_x_2319_);
if (v___x_2331_ == 0)
{
v_x_2320_ = v___x_2330_;
goto _start;
}
else
{
lean_dec(v___x_2330_);
lean_dec(v_x_2319_);
return v___x_2325_;
}
}
else
{
lean_dec(v_m_2323_);
lean_dec(v_x_2319_);
return v___x_2325_;
}
}
}
else
{
lean_object* v___x_2333_; uint8_t v___x_2334_; 
lean_dec(v_x_2319_);
v___x_2333_ = lean_nat_add(v_m_2323_, v___x_2322_);
lean_dec(v_m_2323_);
v___x_2334_ = lean_nat_dec_le(v___x_2333_, v_x_2320_);
if (v___x_2334_ == 0)
{
lean_dec(v___x_2333_);
lean_dec(v_x_2320_);
return v___x_2334_;
}
else
{
v_x_2319_ = v___x_2333_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___redArg___boxed(lean_object* v_as_2336_, lean_object* v_k_2337_, lean_object* v_x_2338_, lean_object* v_x_2339_){
_start:
{
uint8_t v_res_2340_; lean_object* v_r_2341_; 
v_res_2340_ = l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___redArg(v_as_2336_, v_k_2337_, v_x_2338_, v_x_2339_);
lean_dec(v_k_2337_);
lean_dec_ref(v_as_2336_);
v_r_2341_ = lean_box(v_res_2340_);
return v_r_2341_;
}
}
LEAN_EXPORT uint8_t l_Lean_TagAttribute_hasTag(lean_object* v_attr_2342_, lean_object* v_env_2343_, lean_object* v_decl_2344_){
_start:
{
lean_object* v___x_2345_; lean_object* v___x_2346_; 
v___x_2345_ = lean_box(1);
v___x_2346_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2343_, v_decl_2344_);
if (lean_obj_tag(v___x_2346_) == 0)
{
lean_object* v_ext_2347_; lean_object* v_toEnvExtension_2348_; lean_object* v_asyncMode_2349_; lean_object* v___x_2350_; uint8_t v___x_2351_; 
v_ext_2347_ = lean_ctor_get(v_attr_2342_, 1);
v_toEnvExtension_2348_ = lean_ctor_get(v_ext_2347_, 0);
v_asyncMode_2349_ = lean_ctor_get(v_toEnvExtension_2348_, 2);
lean_inc(v_decl_2344_);
v___x_2350_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2345_, v_ext_2347_, v_env_2343_, v_asyncMode_2349_, v_decl_2344_);
v___x_2351_ = l_Lean_NameSet_contains(v___x_2350_, v_decl_2344_);
lean_dec(v_decl_2344_);
lean_dec(v___x_2350_);
return v___x_2351_;
}
else
{
lean_object* v_val_2352_; lean_object* v_ext_2353_; uint8_t v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; uint8_t v___x_2358_; 
v_val_2352_ = lean_ctor_get(v___x_2346_, 0);
lean_inc(v_val_2352_);
lean_dec_ref_known(v___x_2346_, 1);
v_ext_2353_ = lean_ctor_get(v_attr_2342_, 1);
v___x_2354_ = 0;
v___x_2355_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_2345_, v_ext_2353_, v_env_2343_, v_val_2352_, v___x_2354_);
lean_dec(v_val_2352_);
lean_dec_ref(v_env_2343_);
v___x_2356_ = lean_unsigned_to_nat(0u);
v___x_2357_ = lean_array_get_size(v___x_2355_);
v___x_2358_ = lean_nat_dec_lt(v___x_2356_, v___x_2357_);
if (v___x_2358_ == 0)
{
lean_dec_ref(v___x_2355_);
lean_dec(v_decl_2344_);
return v___x_2358_;
}
else
{
lean_object* v___x_2359_; lean_object* v___x_2360_; uint8_t v___x_2361_; 
v___x_2359_ = lean_unsigned_to_nat(1u);
v___x_2360_ = lean_nat_sub(v___x_2357_, v___x_2359_);
v___x_2361_ = lean_nat_dec_le(v___x_2356_, v___x_2360_);
if (v___x_2361_ == 0)
{
lean_dec(v___x_2360_);
lean_dec_ref(v___x_2355_);
lean_dec(v_decl_2344_);
return v___x_2361_;
}
else
{
uint8_t v___x_2362_; 
v___x_2362_ = l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___redArg(v___x_2355_, v_decl_2344_, v___x_2356_, v___x_2360_);
lean_dec(v_decl_2344_);
lean_dec_ref(v___x_2355_);
return v___x_2362_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_hasTag___boxed(lean_object* v_attr_2363_, lean_object* v_env_2364_, lean_object* v_decl_2365_){
_start:
{
uint8_t v_res_2366_; lean_object* v_r_2367_; 
v_res_2366_ = l_Lean_TagAttribute_hasTag(v_attr_2363_, v_env_2364_, v_decl_2365_);
lean_dec_ref(v_attr_2363_);
v_r_2367_ = lean_box(v_res_2366_);
return v_r_2367_;
}
}
LEAN_EXPORT uint8_t l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0(lean_object* v_as_2368_, lean_object* v_k_2369_, lean_object* v_x_2370_, lean_object* v_x_2371_, lean_object* v_x_2372_){
_start:
{
uint8_t v___x_2373_; 
v___x_2373_ = l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___redArg(v_as_2368_, v_k_2369_, v_x_2370_, v_x_2371_);
return v___x_2373_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___boxed(lean_object* v_as_2374_, lean_object* v_k_2375_, lean_object* v_x_2376_, lean_object* v_x_2377_, lean_object* v_x_2378_){
_start:
{
uint8_t v_res_2379_; lean_object* v_r_2380_; 
v_res_2379_ = l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0(v_as_2374_, v_k_2375_, v_x_2376_, v_x_2377_, v_x_2378_);
lean_dec(v_k_2375_);
lean_dec_ref(v_as_2374_);
v_r_2380_ = lean_box(v_res_2379_);
return v_r_2380_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__0(lean_object* v_x_2381_, lean_object* v___y_2382_){
_start:
{
lean_object* v___x_2384_; lean_object* v___x_2385_; 
v___x_2384_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___lam__0___closed__1));
v___x_2385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2385_, 0, v___x_2384_);
return v___x_2385_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__0___boxed(lean_object* v_x_2386_, lean_object* v___y_2387_, lean_object* v___y_2388_){
_start:
{
lean_object* v_res_2389_; 
v_res_2389_ = l_Lean_instInhabitedParametricAttribute_default___lam__0(v_x_2386_, v___y_2387_);
lean_dec_ref(v___y_2387_);
lean_dec_ref(v_x_2386_);
return v_res_2389_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__1(lean_object* v_s_2390_, lean_object* v_x_2391_){
_start:
{
lean_inc_ref(v_s_2390_);
return v_s_2390_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__1___boxed(lean_object* v_s_2392_, lean_object* v_x_2393_){
_start:
{
lean_object* v_res_2394_; 
v_res_2394_ = l_Lean_instInhabitedParametricAttribute_default___lam__1(v_s_2392_, v_x_2393_);
lean_dec_ref(v_x_2393_);
lean_dec_ref(v_s_2392_);
return v_res_2394_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__2(lean_object* v_x_2399_, lean_object* v_x_2400_){
_start:
{
lean_object* v___x_2401_; 
v___x_2401_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___lam__2___closed__1));
return v___x_2401_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__2___boxed(lean_object* v_x_2402_, lean_object* v_x_2403_){
_start:
{
lean_object* v_res_2404_; 
v_res_2404_ = l_Lean_instInhabitedParametricAttribute_default___lam__2(v_x_2402_, v_x_2403_);
lean_dec_ref(v_x_2403_);
lean_dec_ref(v_x_2402_);
return v_res_2404_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__3(lean_object* v_x_2405_){
_start:
{
lean_object* v___x_2406_; 
v___x_2406_ = lean_box(0);
return v___x_2406_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__3___boxed(lean_object* v_x_2407_){
_start:
{
lean_object* v_res_2408_; 
v_res_2408_ = l_Lean_instInhabitedParametricAttribute_default___lam__3(v_x_2407_);
lean_dec_ref(v_x_2407_);
return v_res_2408_;
}
}
static lean_object* _init_l_Lean_instInhabitedParametricAttribute_default___closed__4(void){
_start:
{
lean_object* v___x_2413_; 
v___x_2413_ = l_Lean_instInhabitedEnvExtension_default(lean_box(0));
return v___x_2413_;
}
}
static lean_object* _init_l_Lean_instInhabitedParametricAttribute_default___closed__5(void){
_start:
{
lean_object* v___f_2414_; lean_object* v___f_2415_; lean_object* v___f_2416_; lean_object* v___f_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; lean_object* v___x_2420_; 
v___f_2414_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___closed__3));
v___f_2415_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___closed__2));
v___f_2416_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___closed__1));
v___f_2417_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___closed__0));
v___x_2418_ = lean_box(0);
v___x_2419_ = lean_obj_once(&l_Lean_instInhabitedParametricAttribute_default___closed__4, &l_Lean_instInhabitedParametricAttribute_default___closed__4_once, _init_l_Lean_instInhabitedParametricAttribute_default___closed__4);
v___x_2420_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2420_, 0, v___x_2419_);
lean_ctor_set(v___x_2420_, 1, v___x_2418_);
lean_ctor_set(v___x_2420_, 2, v___f_2417_);
lean_ctor_set(v___x_2420_, 3, v___f_2416_);
lean_ctor_set(v___x_2420_, 4, v___f_2415_);
lean_ctor_set(v___x_2420_, 5, v___f_2414_);
return v___x_2420_;
}
}
static lean_object* _init_l_Lean_instInhabitedParametricAttribute_default___closed__6(void){
_start:
{
uint8_t v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; 
v___x_2421_ = 0;
v___x_2422_ = lean_obj_once(&l_Lean_instInhabitedParametricAttribute_default___closed__5, &l_Lean_instInhabitedParametricAttribute_default___closed__5_once, _init_l_Lean_instInhabitedParametricAttribute_default___closed__5);
v___x_2423_ = ((lean_object*)(l_Lean_instInhabitedAttributeImpl_default));
v___x_2424_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2424_, 0, v___x_2423_);
lean_ctor_set(v___x_2424_, 1, v___x_2422_);
lean_ctor_set_uint8(v___x_2424_, sizeof(void*)*2, v___x_2421_);
return v___x_2424_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default(lean_object* v_00_u03b1_2425_){
_start:
{
lean_object* v___x_2426_; 
v___x_2426_ = lean_obj_once(&l_Lean_instInhabitedParametricAttribute_default___closed__6, &l_Lean_instInhabitedParametricAttribute_default___closed__6_once, _init_l_Lean_instInhabitedParametricAttribute_default___closed__6);
return v___x_2426_;
}
}
static lean_object* _init_l_Lean_instInhabitedParametricAttribute___closed__0(void){
_start:
{
lean_object* v___x_2427_; 
v___x_2427_ = l_Lean_instInhabitedParametricAttribute_default(lean_box(0));
return v___x_2427_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute(lean_object* v_a_2428_){
_start:
{
lean_object* v___x_2429_; 
v___x_2429_ = lean_obj_once(&l_Lean_instInhabitedParametricAttribute___closed__0, &l_Lean_instInhabitedParametricAttribute___closed__0_once, _init_l_Lean_instInhabitedParametricAttribute___closed__0);
return v___x_2429_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_registerParametricAttribute_spec__4___redArg(lean_object* v_env_2430_, lean_object* v___y_2431_){
_start:
{
lean_object* v___x_2433_; lean_object* v_nextMacroScope_2434_; lean_object* v_ngen_2435_; lean_object* v_auxDeclNGen_2436_; lean_object* v_traceState_2437_; lean_object* v_messages_2438_; lean_object* v_infoState_2439_; lean_object* v_snapshotTasks_2440_; lean_object* v___x_2442_; uint8_t v_isShared_2443_; uint8_t v_isSharedCheck_2451_; 
v___x_2433_ = lean_st_ref_take(v___y_2431_);
v_nextMacroScope_2434_ = lean_ctor_get(v___x_2433_, 1);
v_ngen_2435_ = lean_ctor_get(v___x_2433_, 2);
v_auxDeclNGen_2436_ = lean_ctor_get(v___x_2433_, 3);
v_traceState_2437_ = lean_ctor_get(v___x_2433_, 4);
v_messages_2438_ = lean_ctor_get(v___x_2433_, 6);
v_infoState_2439_ = lean_ctor_get(v___x_2433_, 7);
v_snapshotTasks_2440_ = lean_ctor_get(v___x_2433_, 8);
v_isSharedCheck_2451_ = !lean_is_exclusive(v___x_2433_);
if (v_isSharedCheck_2451_ == 0)
{
lean_object* v_unused_2452_; lean_object* v_unused_2453_; 
v_unused_2452_ = lean_ctor_get(v___x_2433_, 5);
lean_dec(v_unused_2452_);
v_unused_2453_ = lean_ctor_get(v___x_2433_, 0);
lean_dec(v_unused_2453_);
v___x_2442_ = v___x_2433_;
v_isShared_2443_ = v_isSharedCheck_2451_;
goto v_resetjp_2441_;
}
else
{
lean_inc(v_snapshotTasks_2440_);
lean_inc(v_infoState_2439_);
lean_inc(v_messages_2438_);
lean_inc(v_traceState_2437_);
lean_inc(v_auxDeclNGen_2436_);
lean_inc(v_ngen_2435_);
lean_inc(v_nextMacroScope_2434_);
lean_dec(v___x_2433_);
v___x_2442_ = lean_box(0);
v_isShared_2443_ = v_isSharedCheck_2451_;
goto v_resetjp_2441_;
}
v_resetjp_2441_:
{
lean_object* v___x_2444_; lean_object* v___x_2446_; 
v___x_2444_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2);
if (v_isShared_2443_ == 0)
{
lean_ctor_set(v___x_2442_, 5, v___x_2444_);
lean_ctor_set(v___x_2442_, 0, v_env_2430_);
v___x_2446_ = v___x_2442_;
goto v_reusejp_2445_;
}
else
{
lean_object* v_reuseFailAlloc_2450_; 
v_reuseFailAlloc_2450_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2450_, 0, v_env_2430_);
lean_ctor_set(v_reuseFailAlloc_2450_, 1, v_nextMacroScope_2434_);
lean_ctor_set(v_reuseFailAlloc_2450_, 2, v_ngen_2435_);
lean_ctor_set(v_reuseFailAlloc_2450_, 3, v_auxDeclNGen_2436_);
lean_ctor_set(v_reuseFailAlloc_2450_, 4, v_traceState_2437_);
lean_ctor_set(v_reuseFailAlloc_2450_, 5, v___x_2444_);
lean_ctor_set(v_reuseFailAlloc_2450_, 6, v_messages_2438_);
lean_ctor_set(v_reuseFailAlloc_2450_, 7, v_infoState_2439_);
lean_ctor_set(v_reuseFailAlloc_2450_, 8, v_snapshotTasks_2440_);
v___x_2446_ = v_reuseFailAlloc_2450_;
goto v_reusejp_2445_;
}
v_reusejp_2445_:
{
lean_object* v___x_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; 
v___x_2447_ = lean_st_ref_set(v___y_2431_, v___x_2446_);
v___x_2448_ = lean_box(0);
v___x_2449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2449_, 0, v___x_2448_);
return v___x_2449_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_registerParametricAttribute_spec__4___redArg___boxed(lean_object* v_env_2454_, lean_object* v___y_2455_, lean_object* v___y_2456_){
_start:
{
lean_object* v_res_2457_; 
v_res_2457_ = l_Lean_setEnv___at___00Lean_registerParametricAttribute_spec__4___redArg(v_env_2454_, v___y_2455_);
lean_dec(v___y_2455_);
return v_res_2457_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_registerParametricAttribute_spec__4(lean_object* v_env_2458_, lean_object* v___y_2459_, lean_object* v___y_2460_){
_start:
{
lean_object* v___x_2462_; 
v___x_2462_ = l_Lean_setEnv___at___00Lean_registerParametricAttribute_spec__4___redArg(v_env_2458_, v___y_2460_);
return v___x_2462_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_registerParametricAttribute_spec__4___boxed(lean_object* v_env_2463_, lean_object* v___y_2464_, lean_object* v___y_2465_, lean_object* v___y_2466_){
_start:
{
lean_object* v_res_2467_; 
v_res_2467_ = l_Lean_setEnv___at___00Lean_registerParametricAttribute_spec__4(v_env_2463_, v___y_2464_, v___y_2465_);
lean_dec(v___y_2465_);
lean_dec_ref(v___y_2464_);
return v_res_2467_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___lam__0(lean_object* v_x_2468_, lean_object* v_p_2469_){
_start:
{
lean_object* v_fst_2470_; lean_object* v_snd_2471_; lean_object* v___x_2473_; uint8_t v_isShared_2474_; uint8_t v_isSharedCheck_2488_; 
v_fst_2470_ = lean_ctor_get(v_x_2468_, 0);
v_snd_2471_ = lean_ctor_get(v_x_2468_, 1);
v_isSharedCheck_2488_ = !lean_is_exclusive(v_x_2468_);
if (v_isSharedCheck_2488_ == 0)
{
v___x_2473_ = v_x_2468_;
v_isShared_2474_ = v_isSharedCheck_2488_;
goto v_resetjp_2472_;
}
else
{
lean_inc(v_snd_2471_);
lean_inc(v_fst_2470_);
lean_dec(v_x_2468_);
v___x_2473_ = lean_box(0);
v_isShared_2474_ = v_isSharedCheck_2488_;
goto v_resetjp_2472_;
}
v_resetjp_2472_:
{
lean_object* v_fst_2475_; lean_object* v_snd_2476_; lean_object* v___x_2478_; uint8_t v_isShared_2479_; uint8_t v_isSharedCheck_2487_; 
v_fst_2475_ = lean_ctor_get(v_p_2469_, 0);
v_snd_2476_ = lean_ctor_get(v_p_2469_, 1);
v_isSharedCheck_2487_ = !lean_is_exclusive(v_p_2469_);
if (v_isSharedCheck_2487_ == 0)
{
v___x_2478_ = v_p_2469_;
v_isShared_2479_ = v_isSharedCheck_2487_;
goto v_resetjp_2477_;
}
else
{
lean_inc(v_snd_2476_);
lean_inc(v_fst_2475_);
lean_dec(v_p_2469_);
v___x_2478_ = lean_box(0);
v_isShared_2479_ = v_isSharedCheck_2487_;
goto v_resetjp_2477_;
}
v_resetjp_2477_:
{
lean_object* v___x_2481_; 
lean_inc(v_fst_2475_);
if (v_isShared_2474_ == 0)
{
lean_ctor_set_tag(v___x_2473_, 1);
lean_ctor_set(v___x_2473_, 1, v_fst_2470_);
lean_ctor_set(v___x_2473_, 0, v_fst_2475_);
v___x_2481_ = v___x_2473_;
goto v_reusejp_2480_;
}
else
{
lean_object* v_reuseFailAlloc_2486_; 
v_reuseFailAlloc_2486_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2486_, 0, v_fst_2475_);
lean_ctor_set(v_reuseFailAlloc_2486_, 1, v_fst_2470_);
v___x_2481_ = v_reuseFailAlloc_2486_;
goto v_reusejp_2480_;
}
v_reusejp_2480_:
{
lean_object* v___x_2482_; lean_object* v___x_2484_; 
v___x_2482_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_2475_, v_snd_2476_, v_snd_2471_);
if (v_isShared_2479_ == 0)
{
lean_ctor_set(v___x_2478_, 1, v___x_2482_);
lean_ctor_set(v___x_2478_, 0, v___x_2481_);
v___x_2484_ = v___x_2478_;
goto v_reusejp_2483_;
}
else
{
lean_object* v_reuseFailAlloc_2485_; 
v_reuseFailAlloc_2485_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2485_, 0, v___x_2481_);
lean_ctor_set(v_reuseFailAlloc_2485_, 1, v___x_2482_);
v___x_2484_ = v_reuseFailAlloc_2485_;
goto v_reusejp_2483_;
}
v_reusejp_2483_:
{
return v___x_2484_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1_spec__1___redArg(lean_object* v_init_2489_, lean_object* v_x_2490_){
_start:
{
if (lean_obj_tag(v_x_2490_) == 0)
{
lean_object* v_k_2491_; lean_object* v_v_2492_; lean_object* v_l_2493_; lean_object* v_r_2494_; lean_object* v___x_2495_; lean_object* v___x_2496_; lean_object* v___x_2497_; 
v_k_2491_ = lean_ctor_get(v_x_2490_, 1);
v_v_2492_ = lean_ctor_get(v_x_2490_, 2);
v_l_2493_ = lean_ctor_get(v_x_2490_, 3);
v_r_2494_ = lean_ctor_get(v_x_2490_, 4);
v___x_2495_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1_spec__1___redArg(v_init_2489_, v_l_2493_);
lean_inc(v_v_2492_);
lean_inc(v_k_2491_);
v___x_2496_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2496_, 0, v_k_2491_);
lean_ctor_set(v___x_2496_, 1, v_v_2492_);
v___x_2497_ = lean_array_push(v___x_2495_, v___x_2496_);
v_init_2489_ = v___x_2497_;
v_x_2490_ = v_r_2494_;
goto _start;
}
else
{
return v_init_2489_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1_spec__1___redArg___boxed(lean_object* v_init_2499_, lean_object* v_x_2500_){
_start:
{
lean_object* v_res_2501_; 
v_res_2501_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1_spec__1___redArg(v_init_2499_, v_x_2500_);
lean_dec(v_x_2500_);
return v_res_2501_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2_spec__3___redArg(lean_object* v_hi_2502_, lean_object* v_pivot_2503_, lean_object* v_as_2504_, lean_object* v_i_2505_, lean_object* v_k_2506_){
_start:
{
uint8_t v___x_2507_; 
v___x_2507_ = lean_nat_dec_lt(v_k_2506_, v_hi_2502_);
if (v___x_2507_ == 0)
{
lean_object* v___x_2508_; lean_object* v___x_2509_; 
lean_dec(v_k_2506_);
v___x_2508_ = lean_array_fswap(v_as_2504_, v_i_2505_, v_hi_2502_);
v___x_2509_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2509_, 0, v_i_2505_);
lean_ctor_set(v___x_2509_, 1, v___x_2508_);
return v___x_2509_;
}
else
{
lean_object* v___x_2510_; lean_object* v_fst_2511_; lean_object* v_fst_2512_; uint8_t v___x_2513_; 
v___x_2510_ = lean_array_fget_borrowed(v_as_2504_, v_k_2506_);
v_fst_2511_ = lean_ctor_get(v___x_2510_, 0);
v_fst_2512_ = lean_ctor_get(v_pivot_2503_, 0);
v___x_2513_ = l_Lean_Name_quickLt(v_fst_2511_, v_fst_2512_);
if (v___x_2513_ == 0)
{
lean_object* v___x_2514_; lean_object* v___x_2515_; 
v___x_2514_ = lean_unsigned_to_nat(1u);
v___x_2515_ = lean_nat_add(v_k_2506_, v___x_2514_);
lean_dec(v_k_2506_);
v_k_2506_ = v___x_2515_;
goto _start;
}
else
{
lean_object* v___x_2517_; lean_object* v___x_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; 
v___x_2517_ = lean_array_fswap(v_as_2504_, v_i_2505_, v_k_2506_);
v___x_2518_ = lean_unsigned_to_nat(1u);
v___x_2519_ = lean_nat_add(v_i_2505_, v___x_2518_);
lean_dec(v_i_2505_);
v___x_2520_ = lean_nat_add(v_k_2506_, v___x_2518_);
lean_dec(v_k_2506_);
v_as_2504_ = v___x_2517_;
v_i_2505_ = v___x_2519_;
v_k_2506_ = v___x_2520_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2_spec__3___redArg___boxed(lean_object* v_hi_2522_, lean_object* v_pivot_2523_, lean_object* v_as_2524_, lean_object* v_i_2525_, lean_object* v_k_2526_){
_start:
{
lean_object* v_res_2527_; 
v_res_2527_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2_spec__3___redArg(v_hi_2522_, v_pivot_2523_, v_as_2524_, v_i_2525_, v_k_2526_);
lean_dec_ref(v_pivot_2523_);
lean_dec(v_hi_2522_);
return v_res_2527_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2___redArg___lam__0(lean_object* v_a_2528_, lean_object* v_b_2529_){
_start:
{
lean_object* v_fst_2530_; lean_object* v_fst_2531_; uint8_t v___x_2532_; 
v_fst_2530_ = lean_ctor_get(v_a_2528_, 0);
v_fst_2531_ = lean_ctor_get(v_b_2529_, 0);
v___x_2532_ = l_Lean_Name_quickLt(v_fst_2530_, v_fst_2531_);
return v___x_2532_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2___redArg___lam__0___boxed(lean_object* v_a_2533_, lean_object* v_b_2534_){
_start:
{
uint8_t v_res_2535_; lean_object* v_r_2536_; 
v_res_2535_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2___redArg___lam__0(v_a_2533_, v_b_2534_);
lean_dec_ref(v_b_2534_);
lean_dec_ref(v_a_2533_);
v_r_2536_ = lean_box(v_res_2535_);
return v_r_2536_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2___redArg(lean_object* v_n_2537_, lean_object* v_as_2538_, lean_object* v_lo_2539_, lean_object* v_hi_2540_){
_start:
{
lean_object* v___y_2542_; uint8_t v___x_2552_; 
v___x_2552_ = lean_nat_dec_lt(v_lo_2539_, v_hi_2540_);
if (v___x_2552_ == 0)
{
lean_dec(v_lo_2539_);
return v_as_2538_;
}
else
{
lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v_mid_2555_; lean_object* v___y_2557_; lean_object* v___y_2563_; lean_object* v___x_2568_; lean_object* v___x_2569_; uint8_t v___x_2570_; 
v___x_2553_ = lean_nat_add(v_lo_2539_, v_hi_2540_);
v___x_2554_ = lean_unsigned_to_nat(1u);
v_mid_2555_ = lean_nat_shiftr(v___x_2553_, v___x_2554_);
lean_dec(v___x_2553_);
v___x_2568_ = lean_array_fget_borrowed(v_as_2538_, v_mid_2555_);
v___x_2569_ = lean_array_fget_borrowed(v_as_2538_, v_lo_2539_);
v___x_2570_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2___redArg___lam__0(v___x_2568_, v___x_2569_);
if (v___x_2570_ == 0)
{
v___y_2563_ = v_as_2538_;
goto v___jp_2562_;
}
else
{
lean_object* v___x_2571_; 
v___x_2571_ = lean_array_fswap(v_as_2538_, v_lo_2539_, v_mid_2555_);
v___y_2563_ = v___x_2571_;
goto v___jp_2562_;
}
v___jp_2556_:
{
lean_object* v___x_2558_; lean_object* v___x_2559_; uint8_t v___x_2560_; 
v___x_2558_ = lean_array_fget_borrowed(v___y_2557_, v_mid_2555_);
v___x_2559_ = lean_array_fget_borrowed(v___y_2557_, v_hi_2540_);
v___x_2560_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2___redArg___lam__0(v___x_2558_, v___x_2559_);
if (v___x_2560_ == 0)
{
lean_dec(v_mid_2555_);
v___y_2542_ = v___y_2557_;
goto v___jp_2541_;
}
else
{
lean_object* v___x_2561_; 
v___x_2561_ = lean_array_fswap(v___y_2557_, v_mid_2555_, v_hi_2540_);
lean_dec(v_mid_2555_);
v___y_2542_ = v___x_2561_;
goto v___jp_2541_;
}
}
v___jp_2562_:
{
lean_object* v___x_2564_; lean_object* v___x_2565_; uint8_t v___x_2566_; 
v___x_2564_ = lean_array_fget_borrowed(v___y_2563_, v_hi_2540_);
v___x_2565_ = lean_array_fget_borrowed(v___y_2563_, v_lo_2539_);
v___x_2566_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2___redArg___lam__0(v___x_2564_, v___x_2565_);
if (v___x_2566_ == 0)
{
v___y_2557_ = v___y_2563_;
goto v___jp_2556_;
}
else
{
lean_object* v___x_2567_; 
v___x_2567_ = lean_array_fswap(v___y_2563_, v_lo_2539_, v_hi_2540_);
v___y_2557_ = v___x_2567_;
goto v___jp_2556_;
}
}
}
v___jp_2541_:
{
lean_object* v_pivot_2543_; lean_object* v___x_2544_; lean_object* v_fst_2545_; lean_object* v_snd_2546_; uint8_t v___x_2547_; 
v_pivot_2543_ = lean_array_fget(v___y_2542_, v_hi_2540_);
lean_inc_n(v_lo_2539_, 2);
v___x_2544_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2_spec__3___redArg(v_hi_2540_, v_pivot_2543_, v___y_2542_, v_lo_2539_, v_lo_2539_);
lean_dec(v_pivot_2543_);
v_fst_2545_ = lean_ctor_get(v___x_2544_, 0);
lean_inc(v_fst_2545_);
v_snd_2546_ = lean_ctor_get(v___x_2544_, 1);
lean_inc(v_snd_2546_);
lean_dec_ref(v___x_2544_);
v___x_2547_ = lean_nat_dec_le(v_hi_2540_, v_fst_2545_);
if (v___x_2547_ == 0)
{
lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; 
v___x_2548_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2___redArg(v_n_2537_, v_snd_2546_, v_lo_2539_, v_fst_2545_);
v___x_2549_ = lean_unsigned_to_nat(1u);
v___x_2550_ = lean_nat_add(v_fst_2545_, v___x_2549_);
lean_dec(v_fst_2545_);
v_as_2538_ = v___x_2548_;
v_lo_2539_ = v___x_2550_;
goto _start;
}
else
{
lean_dec(v_fst_2545_);
lean_dec(v_lo_2539_);
return v_snd_2546_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2___redArg___boxed(lean_object* v_n_2572_, lean_object* v_as_2573_, lean_object* v_lo_2574_, lean_object* v_hi_2575_){
_start:
{
lean_object* v_res_2576_; 
v_res_2576_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2___redArg(v_n_2572_, v_as_2573_, v_lo_2574_, v_hi_2575_);
lean_dec(v_hi_2575_);
lean_dec(v_n_2572_);
return v_res_2576_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3_spec__5___redArg(lean_object* v_snd_2577_, lean_object* v_as_2578_, size_t v_i_2579_, size_t v_stop_2580_, lean_object* v_b_2581_){
_start:
{
lean_object* v___y_2583_; uint8_t v___x_2587_; 
v___x_2587_ = lean_usize_dec_eq(v_i_2579_, v_stop_2580_);
if (v___x_2587_ == 0)
{
lean_object* v___x_2588_; lean_object* v___x_2589_; 
v___x_2588_ = lean_array_uget_borrowed(v_as_2578_, v_i_2579_);
v___x_2589_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_snd_2577_, v___x_2588_);
if (lean_obj_tag(v___x_2589_) == 0)
{
v___y_2583_ = v_b_2581_;
goto v___jp_2582_;
}
else
{
lean_object* v_val_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; 
v_val_2590_ = lean_ctor_get(v___x_2589_, 0);
lean_inc(v_val_2590_);
lean_dec_ref_known(v___x_2589_, 1);
lean_inc(v___x_2588_);
v___x_2591_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2591_, 0, v___x_2588_);
lean_ctor_set(v___x_2591_, 1, v_val_2590_);
v___x_2592_ = lean_array_push(v_b_2581_, v___x_2591_);
v___y_2583_ = v___x_2592_;
goto v___jp_2582_;
}
}
else
{
return v_b_2581_;
}
v___jp_2582_:
{
size_t v___x_2584_; size_t v___x_2585_; 
v___x_2584_ = ((size_t)1ULL);
v___x_2585_ = lean_usize_add(v_i_2579_, v___x_2584_);
v_i_2579_ = v___x_2585_;
v_b_2581_ = v___y_2583_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3_spec__5___redArg___boxed(lean_object* v_snd_2593_, lean_object* v_as_2594_, lean_object* v_i_2595_, lean_object* v_stop_2596_, lean_object* v_b_2597_){
_start:
{
size_t v_i_boxed_2598_; size_t v_stop_boxed_2599_; lean_object* v_res_2600_; 
v_i_boxed_2598_ = lean_unbox_usize(v_i_2595_);
lean_dec(v_i_2595_);
v_stop_boxed_2599_ = lean_unbox_usize(v_stop_2596_);
lean_dec(v_stop_2596_);
v_res_2600_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3_spec__5___redArg(v_snd_2593_, v_as_2594_, v_i_boxed_2598_, v_stop_boxed_2599_, v_b_2597_);
lean_dec_ref(v_as_2594_);
lean_dec(v_snd_2593_);
return v_res_2600_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3___redArg(lean_object* v_snd_2601_, lean_object* v_as_2602_, lean_object* v_start_2603_, lean_object* v_stop_2604_){
_start:
{
lean_object* v___x_2605_; uint8_t v___x_2606_; 
v___x_2605_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___lam__2___closed__0));
v___x_2606_ = lean_nat_dec_lt(v_start_2603_, v_stop_2604_);
if (v___x_2606_ == 0)
{
return v___x_2605_;
}
else
{
lean_object* v___x_2607_; uint8_t v___x_2608_; 
v___x_2607_ = lean_array_get_size(v_as_2602_);
v___x_2608_ = lean_nat_dec_le(v_stop_2604_, v___x_2607_);
if (v___x_2608_ == 0)
{
uint8_t v___x_2609_; 
v___x_2609_ = lean_nat_dec_lt(v_start_2603_, v___x_2607_);
if (v___x_2609_ == 0)
{
return v___x_2605_;
}
else
{
size_t v___x_2610_; size_t v___x_2611_; lean_object* v___x_2612_; 
v___x_2610_ = lean_usize_of_nat(v_start_2603_);
v___x_2611_ = lean_usize_of_nat(v___x_2607_);
v___x_2612_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3_spec__5___redArg(v_snd_2601_, v_as_2602_, v___x_2610_, v___x_2611_, v___x_2605_);
return v___x_2612_;
}
}
else
{
size_t v___x_2613_; size_t v___x_2614_; lean_object* v___x_2615_; 
v___x_2613_ = lean_usize_of_nat(v_start_2603_);
v___x_2614_ = lean_usize_of_nat(v_stop_2604_);
v___x_2615_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3_spec__5___redArg(v_snd_2601_, v_as_2602_, v___x_2613_, v___x_2614_, v___x_2605_);
return v___x_2615_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3___redArg___boxed(lean_object* v_snd_2616_, lean_object* v_as_2617_, lean_object* v_start_2618_, lean_object* v_stop_2619_){
_start:
{
lean_object* v_res_2620_; 
v_res_2620_ = l_Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3___redArg(v_snd_2616_, v_as_2617_, v_start_2618_, v_stop_2619_);
lean_dec(v_stop_2619_);
lean_dec(v_start_2618_);
lean_dec_ref(v_as_2617_);
lean_dec(v_snd_2616_);
return v_res_2620_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttribute_spec__0___redArg(lean_object* v_impl_2621_, lean_object* v_env_2622_, lean_object* v_as_2623_, size_t v_i_2624_, size_t v_stop_2625_, lean_object* v_b_2626_){
_start:
{
lean_object* v___y_2628_; uint8_t v___x_2632_; 
v___x_2632_ = lean_usize_dec_eq(v_i_2624_, v_stop_2625_);
if (v___x_2632_ == 0)
{
lean_object* v___x_2633_; lean_object* v_fst_2634_; lean_object* v_snd_2635_; lean_object* v_filterExport_2636_; lean_object* v___x_2637_; uint8_t v___x_2638_; 
v___x_2633_ = lean_array_uget_borrowed(v_as_2623_, v_i_2624_);
v_fst_2634_ = lean_ctor_get(v___x_2633_, 0);
v_snd_2635_ = lean_ctor_get(v___x_2633_, 1);
v_filterExport_2636_ = lean_ctor_get(v_impl_2621_, 3);
lean_inc_ref(v_filterExport_2636_);
lean_inc(v_snd_2635_);
lean_inc(v_fst_2634_);
lean_inc_ref(v_env_2622_);
v___x_2637_ = lean_apply_3(v_filterExport_2636_, v_env_2622_, v_fst_2634_, v_snd_2635_);
v___x_2638_ = lean_unbox(v___x_2637_);
if (v___x_2638_ == 0)
{
v___y_2628_ = v_b_2626_;
goto v___jp_2627_;
}
else
{
lean_object* v___x_2639_; 
lean_inc(v___x_2633_);
v___x_2639_ = lean_array_push(v_b_2626_, v___x_2633_);
v___y_2628_ = v___x_2639_;
goto v___jp_2627_;
}
}
else
{
lean_dec_ref(v_env_2622_);
lean_dec_ref(v_impl_2621_);
return v_b_2626_;
}
v___jp_2627_:
{
size_t v___x_2629_; size_t v___x_2630_; 
v___x_2629_ = ((size_t)1ULL);
v___x_2630_ = lean_usize_add(v_i_2624_, v___x_2629_);
v_i_2624_ = v___x_2630_;
v_b_2626_ = v___y_2628_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttribute_spec__0___redArg___boxed(lean_object* v_impl_2640_, lean_object* v_env_2641_, lean_object* v_as_2642_, lean_object* v_i_2643_, lean_object* v_stop_2644_, lean_object* v_b_2645_){
_start:
{
size_t v_i_boxed_2646_; size_t v_stop_boxed_2647_; lean_object* v_res_2648_; 
v_i_boxed_2646_ = lean_unbox_usize(v_i_2643_);
lean_dec(v_i_2643_);
v_stop_boxed_2647_ = lean_unbox_usize(v_stop_2644_);
lean_dec(v_stop_2644_);
v_res_2648_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttribute_spec__0___redArg(v_impl_2640_, v_env_2641_, v_as_2642_, v_i_boxed_2646_, v_stop_boxed_2647_, v_b_2645_);
lean_dec_ref(v_as_2642_);
return v_res_2648_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___lam__1(lean_object* v_impl_2649_, uint8_t v_preserveOrder_2650_, lean_object* v_env_2651_, lean_object* v_x_2652_){
_start:
{
lean_object* v___y_2654_; 
if (v_preserveOrder_2650_ == 0)
{
lean_object* v_snd_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; lean_object* v_r_2673_; lean_object* v___x_2674_; lean_object* v___y_2676_; lean_object* v___y_2677_; uint8_t v___x_2679_; 
v_snd_2670_ = lean_ctor_get(v_x_2652_, 1);
lean_inc(v_snd_2670_);
lean_dec_ref(v_x_2652_);
v___x_2671_ = lean_unsigned_to_nat(0u);
v___x_2672_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___lam__2___closed__0));
v_r_2673_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1_spec__1___redArg(v___x_2672_, v_snd_2670_);
lean_dec(v_snd_2670_);
v___x_2674_ = lean_array_get_size(v_r_2673_);
v___x_2679_ = lean_nat_dec_eq(v___x_2674_, v___x_2671_);
if (v___x_2679_ == 0)
{
lean_object* v___x_2680_; lean_object* v___x_2681_; lean_object* v___y_2683_; uint8_t v___x_2685_; 
v___x_2680_ = lean_unsigned_to_nat(1u);
v___x_2681_ = lean_nat_sub(v___x_2674_, v___x_2680_);
v___x_2685_ = lean_nat_dec_le(v___x_2671_, v___x_2681_);
if (v___x_2685_ == 0)
{
lean_inc(v___x_2681_);
v___y_2683_ = v___x_2681_;
goto v___jp_2682_;
}
else
{
v___y_2683_ = v___x_2671_;
goto v___jp_2682_;
}
v___jp_2682_:
{
uint8_t v___x_2684_; 
v___x_2684_ = lean_nat_dec_le(v___y_2683_, v___x_2681_);
if (v___x_2684_ == 0)
{
lean_dec(v___x_2681_);
lean_inc(v___y_2683_);
v___y_2676_ = v___y_2683_;
v___y_2677_ = v___y_2683_;
goto v___jp_2675_;
}
else
{
v___y_2676_ = v___y_2683_;
v___y_2677_ = v___x_2681_;
goto v___jp_2675_;
}
}
}
else
{
v___y_2654_ = v_r_2673_;
goto v___jp_2653_;
}
v___jp_2675_:
{
lean_object* v___x_2678_; 
v___x_2678_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2___redArg(v___x_2674_, v_r_2673_, v___y_2676_, v___y_2677_);
lean_dec(v___y_2677_);
v___y_2654_ = v___x_2678_;
goto v___jp_2653_;
}
}
else
{
lean_object* v_fst_2686_; lean_object* v_snd_2687_; lean_object* v___x_2688_; lean_object* v___x_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; 
v_fst_2686_ = lean_ctor_get(v_x_2652_, 0);
lean_inc(v_fst_2686_);
v_snd_2687_ = lean_ctor_get(v_x_2652_, 1);
lean_inc(v_snd_2687_);
lean_dec_ref(v_x_2652_);
v___x_2688_ = lean_array_mk(v_fst_2686_);
v___x_2689_ = l_Array_reverse___redArg(v___x_2688_);
v___x_2690_ = lean_unsigned_to_nat(0u);
v___x_2691_ = lean_array_get_size(v___x_2689_);
v___x_2692_ = l_Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3___redArg(v_snd_2687_, v___x_2689_, v___x_2690_, v___x_2691_);
lean_dec_ref(v___x_2689_);
lean_dec(v_snd_2687_);
v___y_2654_ = v___x_2692_;
goto v___jp_2653_;
}
v___jp_2653_:
{
lean_object* v___x_2655_; lean_object* v___x_2656_; lean_object* v___x_2657_; uint8_t v___x_2658_; 
v___x_2655_ = lean_unsigned_to_nat(0u);
v___x_2656_ = lean_array_get_size(v___y_2654_);
v___x_2657_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___lam__2___closed__0));
v___x_2658_ = lean_nat_dec_lt(v___x_2655_, v___x_2656_);
if (v___x_2658_ == 0)
{
lean_object* v___x_2659_; 
lean_dec_ref(v_env_2651_);
lean_dec_ref(v_impl_2649_);
v___x_2659_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2659_, 0, v___x_2657_);
lean_ctor_set(v___x_2659_, 1, v___x_2657_);
lean_ctor_set(v___x_2659_, 2, v___y_2654_);
return v___x_2659_;
}
else
{
uint8_t v___x_2660_; 
v___x_2660_ = lean_nat_dec_le(v___x_2656_, v___x_2656_);
if (v___x_2660_ == 0)
{
if (v___x_2658_ == 0)
{
lean_object* v___x_2661_; 
lean_dec_ref(v_env_2651_);
lean_dec_ref(v_impl_2649_);
v___x_2661_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2661_, 0, v___x_2657_);
lean_ctor_set(v___x_2661_, 1, v___x_2657_);
lean_ctor_set(v___x_2661_, 2, v___y_2654_);
return v___x_2661_;
}
else
{
size_t v___x_2662_; size_t v___x_2663_; lean_object* v___x_2664_; lean_object* v___x_2665_; 
v___x_2662_ = ((size_t)0ULL);
v___x_2663_ = lean_usize_of_nat(v___x_2656_);
v___x_2664_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttribute_spec__0___redArg(v_impl_2649_, v_env_2651_, v___y_2654_, v___x_2662_, v___x_2663_, v___x_2657_);
lean_inc_ref(v___x_2664_);
v___x_2665_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2665_, 0, v___x_2664_);
lean_ctor_set(v___x_2665_, 1, v___x_2664_);
lean_ctor_set(v___x_2665_, 2, v___y_2654_);
return v___x_2665_;
}
}
else
{
size_t v___x_2666_; size_t v___x_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; 
v___x_2666_ = ((size_t)0ULL);
v___x_2667_ = lean_usize_of_nat(v___x_2656_);
v___x_2668_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttribute_spec__0___redArg(v_impl_2649_, v_env_2651_, v___y_2654_, v___x_2666_, v___x_2667_, v___x_2657_);
lean_inc_ref(v___x_2668_);
v___x_2669_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2669_, 0, v___x_2668_);
lean_ctor_set(v___x_2669_, 1, v___x_2668_);
lean_ctor_set(v___x_2669_, 2, v___y_2654_);
return v___x_2669_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___lam__1___boxed(lean_object* v_impl_2693_, lean_object* v_preserveOrder_2694_, lean_object* v_env_2695_, lean_object* v_x_2696_){
_start:
{
uint8_t v_preserveOrder_boxed_2697_; lean_object* v_res_2698_; 
v_preserveOrder_boxed_2697_ = lean_unbox(v_preserveOrder_2694_);
v_res_2698_ = l_Lean_registerParametricAttribute___redArg___lam__1(v_impl_2693_, v_preserveOrder_boxed_2697_, v_env_2695_, v_x_2696_);
return v_res_2698_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___lam__2(lean_object* v_x_2708_){
_start:
{
lean_object* v_snd_2709_; lean_object* v___x_2711_; uint8_t v_isShared_2712_; uint8_t v_isSharedCheck_2723_; 
v_snd_2709_ = lean_ctor_get(v_x_2708_, 1);
v_isSharedCheck_2723_ = !lean_is_exclusive(v_x_2708_);
if (v_isSharedCheck_2723_ == 0)
{
lean_object* v_unused_2724_; 
v_unused_2724_ = lean_ctor_get(v_x_2708_, 0);
lean_dec(v_unused_2724_);
v___x_2711_ = v_x_2708_;
v_isShared_2712_ = v_isSharedCheck_2723_;
goto v_resetjp_2710_;
}
else
{
lean_inc(v_snd_2709_);
lean_dec(v_x_2708_);
v___x_2711_ = lean_box(0);
v_isShared_2712_ = v_isSharedCheck_2723_;
goto v_resetjp_2710_;
}
v_resetjp_2710_:
{
lean_object* v___x_2713_; lean_object* v___y_2715_; 
v___x_2713_ = ((lean_object*)(l_Lean_registerParametricAttribute___redArg___lam__2___closed__3));
if (lean_obj_tag(v_snd_2709_) == 0)
{
lean_object* v_size_2721_; 
v_size_2721_ = lean_ctor_get(v_snd_2709_, 0);
lean_inc(v_size_2721_);
lean_dec_ref_known(v_snd_2709_, 5);
v___y_2715_ = v_size_2721_;
goto v___jp_2714_;
}
else
{
lean_object* v___x_2722_; 
v___x_2722_ = lean_unsigned_to_nat(0u);
v___y_2715_ = v___x_2722_;
goto v___jp_2714_;
}
v___jp_2714_:
{
lean_object* v___x_2716_; lean_object* v___x_2717_; lean_object* v___x_2719_; 
v___x_2716_ = l_Nat_reprFast(v___y_2715_);
v___x_2717_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2717_, 0, v___x_2716_);
if (v_isShared_2712_ == 0)
{
lean_ctor_set_tag(v___x_2711_, 5);
lean_ctor_set(v___x_2711_, 1, v___x_2717_);
lean_ctor_set(v___x_2711_, 0, v___x_2713_);
v___x_2719_ = v___x_2711_;
goto v_reusejp_2718_;
}
else
{
lean_object* v_reuseFailAlloc_2720_; 
v_reuseFailAlloc_2720_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2720_, 0, v___x_2713_);
lean_ctor_set(v_reuseFailAlloc_2720_, 1, v___x_2717_);
v___x_2719_ = v_reuseFailAlloc_2720_;
goto v_reusejp_2718_;
}
v_reusejp_2718_:
{
return v___x_2719_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___lam__3(lean_object* v_x_2725_){
_start:
{
lean_object* v___x_2726_; 
v___x_2726_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___lam__2___closed__0));
return v___x_2726_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___lam__3___boxed(lean_object* v_x_2727_){
_start:
{
lean_object* v_res_2728_; 
v_res_2728_ = l_Lean_registerParametricAttribute___redArg___lam__3(v_x_2727_);
lean_dec_ref(v_x_2727_);
return v_res_2728_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___lam__4(lean_object* v___x_2729_, lean_object* v_x_2730_, lean_object* v___y_2731_){
_start:
{
lean_object* v___x_2733_; 
v___x_2733_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2733_, 0, v___x_2729_);
return v___x_2733_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___lam__4___boxed(lean_object* v___x_2734_, lean_object* v_x_2735_, lean_object* v___y_2736_, lean_object* v___y_2737_){
_start:
{
lean_object* v_res_2738_; 
v_res_2738_ = l_Lean_registerParametricAttribute___redArg___lam__4(v___x_2734_, v_x_2735_, v___y_2736_);
lean_dec_ref(v___y_2736_);
lean_dec_ref(v_x_2735_);
return v_res_2738_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___lam__5(lean_object* v___x_2739_){
_start:
{
lean_object* v___x_2741_; 
v___x_2741_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2741_, 0, v___x_2739_);
return v___x_2741_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___lam__5___boxed(lean_object* v___x_2742_, lean_object* v___y_2743_){
_start:
{
lean_object* v_res_2744_; 
v_res_2744_ = l_Lean_registerParametricAttribute___redArg___lam__5(v___x_2742_);
return v_res_2744_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___lam__7(lean_object* v_getParam_2745_, lean_object* v_a_2746_, lean_object* v_afterSet_2747_, lean_object* v_name_2748_, lean_object* v_decl_2749_, lean_object* v_stx_2750_, uint8_t v_kind_2751_, lean_object* v___y_2752_, lean_object* v___y_2753_){
_start:
{
lean_object* v___y_2756_; lean_object* v___y_2757_; lean_object* v___y_2758_; lean_object* v___y_2759_; uint8_t v___y_2760_; lean_object* v___y_2763_; lean_object* v___y_2764_; lean_object* v___y_2765_; uint8_t v___x_2808_; uint8_t v___x_2809_; 
v___x_2808_ = 0;
v___x_2809_ = l_Lean_instBEqAttributeKind_beq(v_kind_2751_, v___x_2808_);
if (v___x_2809_ == 0)
{
lean_object* v___x_2810_; 
lean_dec(v_stx_2750_);
lean_dec(v_decl_2749_);
lean_dec_ref(v_afterSet_2747_);
lean_dec_ref(v_a_2746_);
lean_dec_ref(v_getParam_2745_);
v___x_2810_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg(v_name_2748_, v_kind_2751_, v___y_2752_, v___y_2753_);
return v___x_2810_;
}
else
{
goto v___jp_2803_;
}
v___jp_2755_:
{
if (v___y_2760_ == 0)
{
lean_object* v___x_2761_; 
lean_dec_ref(v___y_2758_);
v___x_2761_ = l_Lean_setEnv___at___00Lean_registerParametricAttribute_spec__4___redArg(v___y_2757_, v___y_2759_);
return v___x_2761_;
}
else
{
lean_dec_ref(v___y_2757_);
return v___y_2758_;
}
}
v___jp_2762_:
{
lean_object* v___x_2766_; 
lean_inc(v___y_2765_);
lean_inc_ref(v___y_2764_);
lean_inc(v_decl_2749_);
v___x_2766_ = lean_apply_5(v_getParam_2745_, v_decl_2749_, v_stx_2750_, v___y_2764_, v___y_2765_, lean_box(0));
if (lean_obj_tag(v___x_2766_) == 0)
{
lean_object* v_a_2767_; lean_object* v___x_2768_; lean_object* v_toEnvExtension_2769_; lean_object* v_env_2770_; lean_object* v_nextMacroScope_2771_; lean_object* v_ngen_2772_; lean_object* v_auxDeclNGen_2773_; lean_object* v_traceState_2774_; lean_object* v_messages_2775_; lean_object* v_infoState_2776_; lean_object* v_snapshotTasks_2777_; lean_object* v___x_2779_; uint8_t v_isShared_2780_; uint8_t v_isSharedCheck_2793_; 
v_a_2767_ = lean_ctor_get(v___x_2766_, 0);
lean_inc(v_a_2767_);
lean_dec_ref_known(v___x_2766_, 1);
v___x_2768_ = lean_st_ref_take(v___y_2765_);
v_toEnvExtension_2769_ = lean_ctor_get(v_a_2746_, 0);
v_env_2770_ = lean_ctor_get(v___x_2768_, 0);
v_nextMacroScope_2771_ = lean_ctor_get(v___x_2768_, 1);
v_ngen_2772_ = lean_ctor_get(v___x_2768_, 2);
v_auxDeclNGen_2773_ = lean_ctor_get(v___x_2768_, 3);
v_traceState_2774_ = lean_ctor_get(v___x_2768_, 4);
v_messages_2775_ = lean_ctor_get(v___x_2768_, 6);
v_infoState_2776_ = lean_ctor_get(v___x_2768_, 7);
v_snapshotTasks_2777_ = lean_ctor_get(v___x_2768_, 8);
v_isSharedCheck_2793_ = !lean_is_exclusive(v___x_2768_);
if (v_isSharedCheck_2793_ == 0)
{
lean_object* v_unused_2794_; 
v_unused_2794_ = lean_ctor_get(v___x_2768_, 5);
lean_dec(v_unused_2794_);
v___x_2779_ = v___x_2768_;
v_isShared_2780_ = v_isSharedCheck_2793_;
goto v_resetjp_2778_;
}
else
{
lean_inc(v_snapshotTasks_2777_);
lean_inc(v_infoState_2776_);
lean_inc(v_messages_2775_);
lean_inc(v_traceState_2774_);
lean_inc(v_auxDeclNGen_2773_);
lean_inc(v_ngen_2772_);
lean_inc(v_nextMacroScope_2771_);
lean_inc(v_env_2770_);
lean_dec(v___x_2768_);
v___x_2779_ = lean_box(0);
v_isShared_2780_ = v_isSharedCheck_2793_;
goto v_resetjp_2778_;
}
v_resetjp_2778_:
{
lean_object* v_asyncMode_2781_; lean_object* v___x_2782_; lean_object* v___x_2783_; lean_object* v___x_2784_; lean_object* v___x_2786_; 
v_asyncMode_2781_ = lean_ctor_get(v_toEnvExtension_2769_, 2);
lean_inc(v_asyncMode_2781_);
lean_inc(v_a_2767_);
lean_inc_n(v_decl_2749_, 2);
v___x_2782_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2782_, 0, v_decl_2749_);
lean_ctor_set(v___x_2782_, 1, v_a_2767_);
v___x_2783_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_a_2746_, v_env_2770_, v___x_2782_, v_asyncMode_2781_, v_decl_2749_);
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
v_reuseFailAlloc_2792_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2792_, 0, v___x_2783_);
lean_ctor_set(v_reuseFailAlloc_2792_, 1, v_nextMacroScope_2771_);
lean_ctor_set(v_reuseFailAlloc_2792_, 2, v_ngen_2772_);
lean_ctor_set(v_reuseFailAlloc_2792_, 3, v_auxDeclNGen_2773_);
lean_ctor_set(v_reuseFailAlloc_2792_, 4, v_traceState_2774_);
lean_ctor_set(v_reuseFailAlloc_2792_, 5, v___x_2784_);
lean_ctor_set(v_reuseFailAlloc_2792_, 6, v_messages_2775_);
lean_ctor_set(v_reuseFailAlloc_2792_, 7, v_infoState_2776_);
lean_ctor_set(v_reuseFailAlloc_2792_, 8, v_snapshotTasks_2777_);
v___x_2786_ = v_reuseFailAlloc_2792_;
goto v_reusejp_2785_;
}
v_reusejp_2785_:
{
lean_object* v___x_2787_; lean_object* v___x_2788_; 
v___x_2787_ = lean_st_ref_set(v___y_2765_, v___x_2786_);
lean_inc(v___y_2765_);
lean_inc_ref(v___y_2764_);
v___x_2788_ = lean_apply_5(v_afterSet_2747_, v_decl_2749_, v_a_2767_, v___y_2764_, v___y_2765_, lean_box(0));
if (lean_obj_tag(v___x_2788_) == 0)
{
lean_dec_ref(v___y_2763_);
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
v___y_2756_ = v___y_2764_;
v___y_2757_ = v___y_2763_;
v___y_2758_ = v___x_2788_;
v___y_2759_ = v___y_2765_;
v___y_2760_ = v___x_2791_;
goto v___jp_2755_;
}
else
{
lean_dec(v_a_2789_);
v___y_2756_ = v___y_2764_;
v___y_2757_ = v___y_2763_;
v___y_2758_ = v___x_2788_;
v___y_2759_ = v___y_2765_;
v___y_2760_ = v___x_2790_;
goto v___jp_2755_;
}
}
}
}
}
else
{
lean_object* v_a_2795_; lean_object* v___x_2797_; uint8_t v_isShared_2798_; uint8_t v_isSharedCheck_2802_; 
lean_dec_ref(v___y_2763_);
lean_dec(v_decl_2749_);
lean_dec_ref(v_afterSet_2747_);
lean_dec_ref(v_a_2746_);
v_a_2795_ = lean_ctor_get(v___x_2766_, 0);
v_isSharedCheck_2802_ = !lean_is_exclusive(v___x_2766_);
if (v_isSharedCheck_2802_ == 0)
{
v___x_2797_ = v___x_2766_;
v_isShared_2798_ = v_isSharedCheck_2802_;
goto v_resetjp_2796_;
}
else
{
lean_inc(v_a_2795_);
lean_dec(v___x_2766_);
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
v___x_2804_ = lean_st_ref_get(v___y_2753_);
v_env_2805_ = lean_ctor_get(v___x_2804_, 0);
lean_inc_ref(v_env_2805_);
lean_dec(v___x_2804_);
v___x_2806_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2805_, v_decl_2749_);
if (lean_obj_tag(v___x_2806_) == 0)
{
lean_dec(v_name_2748_);
v___y_2763_ = v_env_2805_;
v___y_2764_ = v___y_2752_;
v___y_2765_ = v___y_2753_;
goto v___jp_2762_;
}
else
{
lean_object* v___x_2807_; 
lean_dec_ref_known(v___x_2806_, 1);
lean_dec_ref(v_env_2805_);
lean_dec(v_stx_2750_);
lean_dec_ref(v_afterSet_2747_);
lean_dec_ref(v_a_2746_);
lean_dec_ref(v_getParam_2745_);
v___x_2807_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg(v_name_2748_, v_decl_2749_, v___y_2752_, v___y_2753_);
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
lean_dec_ref_known(v___x_2852_, 1);
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
lean_dec_ref_known(v___x_2856_, 3);
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
lean_dec_ref_known(v___x_3070_, 1);
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
lean_dec_ref_known(v___x_3070_, 1);
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
lean_dec_ref_known(v_fst_3107_, 1);
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
lean_dec_ref_known(v_x_3247_, 2);
v___x_3250_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_newState_3245_, v_head_3248_);
if (lean_obj_tag(v___x_3250_) == 1)
{
lean_object* v_val_3251_; lean_object* v___x_3252_; 
v_val_3251_ = lean_ctor_get(v___x_3250_, 0);
lean_inc(v_val_3251_);
lean_dec_ref_known(v___x_3250_, 1);
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
lean_dec_ref_known(v_s_3278_, 5);
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
lean_dec_ref_known(v_as_3362_, 2);
v___x_3368_ = l_Lean_registerBuiltinAttribute(v_head_3366_);
if (lean_obj_tag(v___x_3368_) == 0)
{
lean_dec_ref_known(v___x_3368_, 1);
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
lean_object* v___y_3384_; lean_object* v___y_3385_; lean_object* v___y_3420_; lean_object* v___y_3421_; lean_object* v___x_3426_; 
v___x_3426_ = l_Lean_Attribute_Builtin_ensureNoArgs(v_stx_3378_, v___y_3380_, v___y_3381_);
if (lean_obj_tag(v___x_3426_) == 0)
{
uint8_t v___x_3427_; uint8_t v___x_3428_; 
lean_dec_ref_known(v___x_3426_, 1);
v___x_3427_ = 0;
v___x_3428_ = l_Lean_instBEqAttributeKind_beq(v_kind_3379_, v___x_3427_);
if (v___x_3428_ == 0)
{
lean_object* v___x_3429_; 
lean_dec(v_decl_3377_);
lean_dec_ref(v_a_3375_);
lean_dec(v_snd_3374_);
lean_dec_ref(v_validate_3373_);
v___x_3429_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg(v_fst_3376_, v_kind_3379_, v___y_3380_, v___y_3381_);
return v___x_3429_;
}
else
{
v___y_3420_ = v___y_3380_;
v___y_3421_ = v___y_3381_;
goto v___jp_3419_;
}
}
else
{
lean_dec(v_decl_3377_);
lean_dec(v_fst_3376_);
lean_dec_ref(v_a_3375_);
lean_dec(v_snd_3374_);
lean_dec_ref(v_validate_3373_);
return v___x_3426_;
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
lean_object* v___x_3388_; uint8_t v_isShared_3389_; uint8_t v_isSharedCheck_3417_; 
v_isSharedCheck_3417_ = !lean_is_exclusive(v___x_3386_);
if (v_isSharedCheck_3417_ == 0)
{
lean_object* v_unused_3418_; 
v_unused_3418_ = lean_ctor_get(v___x_3386_, 0);
lean_dec(v_unused_3418_);
v___x_3388_ = v___x_3386_;
v_isShared_3389_ = v_isSharedCheck_3417_;
goto v_resetjp_3387_;
}
else
{
lean_dec(v___x_3386_);
v___x_3388_ = lean_box(0);
v_isShared_3389_ = v_isSharedCheck_3417_;
goto v_resetjp_3387_;
}
v_resetjp_3387_:
{
lean_object* v___x_3390_; lean_object* v_toEnvExtension_3391_; lean_object* v_env_3392_; lean_object* v_nextMacroScope_3393_; lean_object* v_ngen_3394_; lean_object* v_auxDeclNGen_3395_; lean_object* v_traceState_3396_; lean_object* v_messages_3397_; lean_object* v_infoState_3398_; lean_object* v_snapshotTasks_3399_; lean_object* v___x_3401_; uint8_t v_isShared_3402_; uint8_t v_isSharedCheck_3415_; 
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
v_isSharedCheck_3415_ = !lean_is_exclusive(v___x_3390_);
if (v_isSharedCheck_3415_ == 0)
{
lean_object* v_unused_3416_; 
v_unused_3416_ = lean_ctor_get(v___x_3390_, 5);
lean_dec(v_unused_3416_);
v___x_3401_ = v___x_3390_;
v_isShared_3402_ = v_isSharedCheck_3415_;
goto v_resetjp_3400_;
}
else
{
lean_inc(v_snapshotTasks_3399_);
lean_inc(v_infoState_3398_);
lean_inc(v_messages_3397_);
lean_inc(v_traceState_3396_);
lean_inc(v_auxDeclNGen_3395_);
lean_inc(v_ngen_3394_);
lean_inc(v_nextMacroScope_3393_);
lean_inc(v_env_3392_);
lean_dec(v___x_3390_);
v___x_3401_ = lean_box(0);
v_isShared_3402_ = v_isSharedCheck_3415_;
goto v_resetjp_3400_;
}
v_resetjp_3400_:
{
lean_object* v_asyncMode_3403_; lean_object* v___x_3404_; lean_object* v___x_3405_; lean_object* v___x_3406_; lean_object* v___x_3408_; 
v_asyncMode_3403_ = lean_ctor_get(v_toEnvExtension_3391_, 2);
lean_inc(v_asyncMode_3403_);
lean_inc(v_decl_3377_);
v___x_3404_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3404_, 0, v_decl_3377_);
lean_ctor_set(v___x_3404_, 1, v_snd_3374_);
v___x_3405_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_a_3375_, v_env_3392_, v___x_3404_, v_asyncMode_3403_, v_decl_3377_);
lean_dec(v_asyncMode_3403_);
v___x_3406_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2);
if (v_isShared_3402_ == 0)
{
lean_ctor_set(v___x_3401_, 5, v___x_3406_);
lean_ctor_set(v___x_3401_, 0, v___x_3405_);
v___x_3408_ = v___x_3401_;
goto v_reusejp_3407_;
}
else
{
lean_object* v_reuseFailAlloc_3414_; 
v_reuseFailAlloc_3414_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3414_, 0, v___x_3405_);
lean_ctor_set(v_reuseFailAlloc_3414_, 1, v_nextMacroScope_3393_);
lean_ctor_set(v_reuseFailAlloc_3414_, 2, v_ngen_3394_);
lean_ctor_set(v_reuseFailAlloc_3414_, 3, v_auxDeclNGen_3395_);
lean_ctor_set(v_reuseFailAlloc_3414_, 4, v_traceState_3396_);
lean_ctor_set(v_reuseFailAlloc_3414_, 5, v___x_3406_);
lean_ctor_set(v_reuseFailAlloc_3414_, 6, v_messages_3397_);
lean_ctor_set(v_reuseFailAlloc_3414_, 7, v_infoState_3398_);
lean_ctor_set(v_reuseFailAlloc_3414_, 8, v_snapshotTasks_3399_);
v___x_3408_ = v_reuseFailAlloc_3414_;
goto v_reusejp_3407_;
}
v_reusejp_3407_:
{
lean_object* v___x_3409_; lean_object* v___x_3410_; lean_object* v___x_3412_; 
v___x_3409_ = lean_st_ref_set(v___y_3385_, v___x_3408_);
v___x_3410_ = lean_box(0);
if (v_isShared_3389_ == 0)
{
lean_ctor_set(v___x_3388_, 0, v___x_3410_);
v___x_3412_ = v___x_3388_;
goto v_reusejp_3411_;
}
else
{
lean_object* v_reuseFailAlloc_3413_; 
v_reuseFailAlloc_3413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3413_, 0, v___x_3410_);
v___x_3412_ = v_reuseFailAlloc_3413_;
goto v_reusejp_3411_;
}
v_reusejp_3411_:
{
return v___x_3412_;
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
v___jp_3419_:
{
lean_object* v___x_3422_; lean_object* v_env_3423_; lean_object* v___x_3424_; 
v___x_3422_ = lean_st_ref_get(v___y_3421_);
v_env_3423_ = lean_ctor_get(v___x_3422_, 0);
lean_inc_ref(v_env_3423_);
lean_dec(v___x_3422_);
v___x_3424_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3423_, v_decl_3377_);
lean_dec_ref(v_env_3423_);
if (lean_obj_tag(v___x_3424_) == 0)
{
lean_dec(v_fst_3376_);
v___y_3384_ = v___y_3420_;
v___y_3385_ = v___y_3421_;
goto v___jp_3383_;
}
else
{
lean_object* v___x_3425_; 
lean_dec_ref_known(v___x_3424_, 1);
lean_dec_ref(v_a_3375_);
lean_dec(v_snd_3374_);
lean_dec_ref(v_validate_3373_);
v___x_3425_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg(v_fst_3376_, v_decl_3377_, v___y_3420_, v___y_3421_);
return v___x_3425_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__1___boxed(lean_object* v_validate_3430_, lean_object* v_snd_3431_, lean_object* v_a_3432_, lean_object* v_fst_3433_, lean_object* v_decl_3434_, lean_object* v_stx_3435_, lean_object* v_kind_3436_, lean_object* v___y_3437_, lean_object* v___y_3438_, lean_object* v___y_3439_){
_start:
{
uint8_t v_kind_boxed_3440_; lean_object* v_res_3441_; 
v_kind_boxed_3440_ = lean_unbox(v_kind_3436_);
v_res_3441_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__1(v_validate_3430_, v_snd_3431_, v_a_3432_, v_fst_3433_, v_decl_3434_, v_stx_3435_, v_kind_boxed_3440_, v___y_3437_, v___y_3438_);
lean_dec(v___y_3438_);
lean_dec_ref(v___y_3437_);
return v_res_3441_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__0(lean_object* v_fst_3442_, lean_object* v_decl_3443_, lean_object* v___y_3444_, lean_object* v___y_3445_){
_start:
{
lean_object* v___x_3447_; lean_object* v___x_3448_; lean_object* v___x_3449_; lean_object* v___x_3450_; lean_object* v___x_3451_; lean_object* v___x_3452_; 
v___x_3447_ = lean_obj_once(&l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1, &l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1_once, _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1);
v___x_3448_ = l_Lean_MessageData_ofName(v_fst_3442_);
v___x_3449_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3449_, 0, v___x_3447_);
lean_ctor_set(v___x_3449_, 1, v___x_3448_);
v___x_3450_ = lean_obj_once(&l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3, &l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3_once, _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3);
v___x_3451_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3451_, 0, v___x_3449_);
lean_ctor_set(v___x_3451_, 1, v___x_3450_);
v___x_3452_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_3451_, v___y_3444_, v___y_3445_);
return v___x_3452_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__0___boxed(lean_object* v_fst_3453_, lean_object* v_decl_3454_, lean_object* v___y_3455_, lean_object* v___y_3456_, lean_object* v___y_3457_){
_start:
{
lean_object* v_res_3458_; 
v_res_3458_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__0(v_fst_3453_, v_decl_3454_, v___y_3455_, v___y_3456_);
lean_dec(v___y_3456_);
lean_dec_ref(v___y_3455_);
lean_dec(v_decl_3454_);
return v_res_3458_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg(lean_object* v_validate_3459_, lean_object* v_a_3460_, lean_object* v_ref_3461_, uint8_t v_applicationTime_3462_, lean_object* v_a_3463_, lean_object* v_a_3464_){
_start:
{
if (lean_obj_tag(v_a_3463_) == 0)
{
lean_object* v___x_3465_; 
lean_dec(v_ref_3461_);
lean_dec_ref(v_a_3460_);
lean_dec_ref(v_validate_3459_);
v___x_3465_ = l_List_reverse___redArg(v_a_3464_);
return v___x_3465_;
}
else
{
lean_object* v_head_3466_; lean_object* v_snd_3467_; lean_object* v_tail_3468_; lean_object* v___x_3470_; uint8_t v_isShared_3471_; uint8_t v_isSharedCheck_3483_; 
v_head_3466_ = lean_ctor_get(v_a_3463_, 0);
lean_inc(v_head_3466_);
v_snd_3467_ = lean_ctor_get(v_head_3466_, 1);
lean_inc(v_snd_3467_);
v_tail_3468_ = lean_ctor_get(v_a_3463_, 1);
v_isSharedCheck_3483_ = !lean_is_exclusive(v_a_3463_);
if (v_isSharedCheck_3483_ == 0)
{
lean_object* v_unused_3484_; 
v_unused_3484_ = lean_ctor_get(v_a_3463_, 0);
lean_dec(v_unused_3484_);
v___x_3470_ = v_a_3463_;
v_isShared_3471_ = v_isSharedCheck_3483_;
goto v_resetjp_3469_;
}
else
{
lean_inc(v_tail_3468_);
lean_dec(v_a_3463_);
v___x_3470_ = lean_box(0);
v_isShared_3471_ = v_isSharedCheck_3483_;
goto v_resetjp_3469_;
}
v_resetjp_3469_:
{
lean_object* v_fst_3472_; lean_object* v_fst_3473_; lean_object* v_snd_3474_; lean_object* v___f_3475_; lean_object* v___f_3476_; lean_object* v___x_3477_; lean_object* v___x_3478_; lean_object* v___x_3480_; 
v_fst_3472_ = lean_ctor_get(v_head_3466_, 0);
lean_inc_n(v_fst_3472_, 3);
lean_dec(v_head_3466_);
v_fst_3473_ = lean_ctor_get(v_snd_3467_, 0);
lean_inc(v_fst_3473_);
v_snd_3474_ = lean_ctor_get(v_snd_3467_, 1);
lean_inc(v_snd_3474_);
lean_dec(v_snd_3467_);
v___f_3475_ = lean_alloc_closure((void*)(l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__0___boxed), 5, 1);
lean_closure_set(v___f_3475_, 0, v_fst_3472_);
lean_inc_ref(v_a_3460_);
lean_inc_ref(v_validate_3459_);
v___f_3476_ = lean_alloc_closure((void*)(l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__1___boxed), 10, 4);
lean_closure_set(v___f_3476_, 0, v_validate_3459_);
lean_closure_set(v___f_3476_, 1, v_snd_3474_);
lean_closure_set(v___f_3476_, 2, v_a_3460_);
lean_closure_set(v___f_3476_, 3, v_fst_3472_);
lean_inc(v_ref_3461_);
v___x_3477_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_3477_, 0, v_ref_3461_);
lean_ctor_set(v___x_3477_, 1, v_fst_3472_);
lean_ctor_set(v___x_3477_, 2, v_fst_3473_);
lean_ctor_set_uint8(v___x_3477_, sizeof(void*)*3, v_applicationTime_3462_);
v___x_3478_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3478_, 0, v___x_3477_);
lean_ctor_set(v___x_3478_, 1, v___f_3476_);
lean_ctor_set(v___x_3478_, 2, v___f_3475_);
if (v_isShared_3471_ == 0)
{
lean_ctor_set(v___x_3470_, 1, v_a_3464_);
lean_ctor_set(v___x_3470_, 0, v___x_3478_);
v___x_3480_ = v___x_3470_;
goto v_reusejp_3479_;
}
else
{
lean_object* v_reuseFailAlloc_3482_; 
v_reuseFailAlloc_3482_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3482_, 0, v___x_3478_);
lean_ctor_set(v_reuseFailAlloc_3482_, 1, v_a_3464_);
v___x_3480_ = v_reuseFailAlloc_3482_;
goto v_reusejp_3479_;
}
v_reusejp_3479_:
{
v_a_3463_ = v_tail_3468_;
v_a_3464_ = v___x_3480_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___boxed(lean_object* v_validate_3485_, lean_object* v_a_3486_, lean_object* v_ref_3487_, lean_object* v_applicationTime_3488_, lean_object* v_a_3489_, lean_object* v_a_3490_){
_start:
{
uint8_t v_applicationTime_boxed_3491_; lean_object* v_res_3492_; 
v_applicationTime_boxed_3491_ = lean_unbox(v_applicationTime_3488_);
v_res_3492_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg(v_validate_3485_, v_a_3486_, v_ref_3487_, v_applicationTime_boxed_3491_, v_a_3489_, v_a_3490_);
return v_res_3492_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg(lean_object* v_attrDescrs_3506_, lean_object* v_validate_3507_, uint8_t v_applicationTime_3508_, lean_object* v_ref_3509_){
_start:
{
lean_object* v___f_3511_; lean_object* v___f_3512_; lean_object* v___f_3513_; lean_object* v___f_3514_; lean_object* v___f_3515_; lean_object* v___f_3516_; lean_object* v___x_3517_; lean_object* v___x_3518_; lean_object* v___x_3519_; lean_object* v___x_3520_; lean_object* v___x_3521_; 
v___f_3511_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__0));
v___f_3512_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__2));
v___f_3513_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__3));
v___f_3514_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__4));
v___f_3515_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__5));
v___f_3516_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__6));
v___x_3517_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__7));
v___x_3518_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__8));
lean_inc(v_ref_3509_);
v___x_3519_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_3519_, 0, v_ref_3509_);
lean_ctor_set(v___x_3519_, 1, v___f_3515_);
lean_ctor_set(v___x_3519_, 2, v___f_3516_);
lean_ctor_set(v___x_3519_, 3, v___f_3514_);
lean_ctor_set(v___x_3519_, 4, v___f_3513_);
lean_ctor_set(v___x_3519_, 5, v___f_3512_);
lean_ctor_set(v___x_3519_, 6, v___x_3517_);
lean_ctor_set(v___x_3519_, 7, v___x_3518_);
v___x_3520_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3520_, 0, v___x_3519_);
lean_ctor_set(v___x_3520_, 1, v___f_3511_);
v___x_3521_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_3520_);
if (lean_obj_tag(v___x_3521_) == 0)
{
lean_object* v_a_3522_; lean_object* v___x_3523_; lean_object* v___x_3524_; lean_object* v___x_3525_; 
v_a_3522_ = lean_ctor_get(v___x_3521_, 0);
lean_inc_n(v_a_3522_, 2);
lean_dec_ref_known(v___x_3521_, 1);
v___x_3523_ = lean_box(0);
v___x_3524_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg(v_validate_3507_, v_a_3522_, v_ref_3509_, v_applicationTime_3508_, v_attrDescrs_3506_, v___x_3523_);
lean_inc(v___x_3524_);
v___x_3525_ = l_List_forM___at___00Lean_registerEnumAttributes_spec__3(v___x_3524_);
if (lean_obj_tag(v___x_3525_) == 0)
{
lean_object* v___x_3527_; uint8_t v_isShared_3528_; uint8_t v_isSharedCheck_3533_; 
v_isSharedCheck_3533_ = !lean_is_exclusive(v___x_3525_);
if (v_isSharedCheck_3533_ == 0)
{
lean_object* v_unused_3534_; 
v_unused_3534_ = lean_ctor_get(v___x_3525_, 0);
lean_dec(v_unused_3534_);
v___x_3527_ = v___x_3525_;
v_isShared_3528_ = v_isSharedCheck_3533_;
goto v_resetjp_3526_;
}
else
{
lean_dec(v___x_3525_);
v___x_3527_ = lean_box(0);
v_isShared_3528_ = v_isSharedCheck_3533_;
goto v_resetjp_3526_;
}
v_resetjp_3526_:
{
lean_object* v___x_3529_; lean_object* v___x_3531_; 
v___x_3529_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3529_, 0, v___x_3524_);
lean_ctor_set(v___x_3529_, 1, v_a_3522_);
if (v_isShared_3528_ == 0)
{
lean_ctor_set(v___x_3527_, 0, v___x_3529_);
v___x_3531_ = v___x_3527_;
goto v_reusejp_3530_;
}
else
{
lean_object* v_reuseFailAlloc_3532_; 
v_reuseFailAlloc_3532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3532_, 0, v___x_3529_);
v___x_3531_ = v_reuseFailAlloc_3532_;
goto v_reusejp_3530_;
}
v_reusejp_3530_:
{
return v___x_3531_;
}
}
}
else
{
lean_object* v_a_3535_; lean_object* v___x_3537_; uint8_t v_isShared_3538_; uint8_t v_isSharedCheck_3542_; 
lean_dec(v___x_3524_);
lean_dec(v_a_3522_);
v_a_3535_ = lean_ctor_get(v___x_3525_, 0);
v_isSharedCheck_3542_ = !lean_is_exclusive(v___x_3525_);
if (v_isSharedCheck_3542_ == 0)
{
v___x_3537_ = v___x_3525_;
v_isShared_3538_ = v_isSharedCheck_3542_;
goto v_resetjp_3536_;
}
else
{
lean_inc(v_a_3535_);
lean_dec(v___x_3525_);
v___x_3537_ = lean_box(0);
v_isShared_3538_ = v_isSharedCheck_3542_;
goto v_resetjp_3536_;
}
v_resetjp_3536_:
{
lean_object* v___x_3540_; 
if (v_isShared_3538_ == 0)
{
v___x_3540_ = v___x_3537_;
goto v_reusejp_3539_;
}
else
{
lean_object* v_reuseFailAlloc_3541_; 
v_reuseFailAlloc_3541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3541_, 0, v_a_3535_);
v___x_3540_ = v_reuseFailAlloc_3541_;
goto v_reusejp_3539_;
}
v_reusejp_3539_:
{
return v___x_3540_;
}
}
}
}
else
{
lean_object* v_a_3543_; lean_object* v___x_3545_; uint8_t v_isShared_3546_; uint8_t v_isSharedCheck_3550_; 
lean_dec(v_ref_3509_);
lean_dec_ref(v_validate_3507_);
lean_dec(v_attrDescrs_3506_);
v_a_3543_ = lean_ctor_get(v___x_3521_, 0);
v_isSharedCheck_3550_ = !lean_is_exclusive(v___x_3521_);
if (v_isSharedCheck_3550_ == 0)
{
v___x_3545_ = v___x_3521_;
v_isShared_3546_ = v_isSharedCheck_3550_;
goto v_resetjp_3544_;
}
else
{
lean_inc(v_a_3543_);
lean_dec(v___x_3521_);
v___x_3545_ = lean_box(0);
v_isShared_3546_ = v_isSharedCheck_3550_;
goto v_resetjp_3544_;
}
v_resetjp_3544_:
{
lean_object* v___x_3548_; 
if (v_isShared_3546_ == 0)
{
v___x_3548_ = v___x_3545_;
goto v_reusejp_3547_;
}
else
{
lean_object* v_reuseFailAlloc_3549_; 
v_reuseFailAlloc_3549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3549_, 0, v_a_3543_);
v___x_3548_ = v_reuseFailAlloc_3549_;
goto v_reusejp_3547_;
}
v_reusejp_3547_:
{
return v___x_3548_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___boxed(lean_object* v_attrDescrs_3551_, lean_object* v_validate_3552_, lean_object* v_applicationTime_3553_, lean_object* v_ref_3554_, lean_object* v_a_3555_){
_start:
{
uint8_t v_applicationTime_boxed_3556_; lean_object* v_res_3557_; 
v_applicationTime_boxed_3556_ = lean_unbox(v_applicationTime_3553_);
v_res_3557_ = l_Lean_registerEnumAttributes___redArg(v_attrDescrs_3551_, v_validate_3552_, v_applicationTime_boxed_3556_, v_ref_3554_);
return v_res_3557_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes(lean_object* v_00_u03b1_3558_, lean_object* v_attrDescrs_3559_, lean_object* v_validate_3560_, uint8_t v_applicationTime_3561_, lean_object* v_ref_3562_){
_start:
{
lean_object* v___x_3564_; 
v___x_3564_ = l_Lean_registerEnumAttributes___redArg(v_attrDescrs_3559_, v_validate_3560_, v_applicationTime_3561_, v_ref_3562_);
return v___x_3564_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___boxed(lean_object* v_00_u03b1_3565_, lean_object* v_attrDescrs_3566_, lean_object* v_validate_3567_, lean_object* v_applicationTime_3568_, lean_object* v_ref_3569_, lean_object* v_a_3570_){
_start:
{
uint8_t v_applicationTime_boxed_3571_; lean_object* v_res_3572_; 
v_applicationTime_boxed_3571_ = lean_unbox(v_applicationTime_3568_);
v_res_3572_ = l_Lean_registerEnumAttributes(v_00_u03b1_3565_, v_attrDescrs_3566_, v_validate_3567_, v_applicationTime_boxed_3571_, v_ref_3569_);
return v_res_3572_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0(lean_object* v_00_u03b1_3573_, lean_object* v_env_3574_, lean_object* v_as_3575_, size_t v_i_3576_, size_t v_stop_3577_, lean_object* v_b_3578_){
_start:
{
lean_object* v___x_3579_; 
v___x_3579_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg(v_env_3574_, v_as_3575_, v_i_3576_, v_stop_3577_, v_b_3578_);
return v___x_3579_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___boxed(lean_object* v_00_u03b1_3580_, lean_object* v_env_3581_, lean_object* v_as_3582_, lean_object* v_i_3583_, lean_object* v_stop_3584_, lean_object* v_b_3585_){
_start:
{
size_t v_i_boxed_3586_; size_t v_stop_boxed_3587_; lean_object* v_res_3588_; 
v_i_boxed_3586_ = lean_unbox_usize(v_i_3583_);
lean_dec(v_i_3583_);
v_stop_boxed_3587_ = lean_unbox_usize(v_stop_3584_);
lean_dec(v_stop_3584_);
v_res_3588_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0(v_00_u03b1_3580_, v_env_3581_, v_as_3582_, v_i_boxed_3586_, v_stop_boxed_3587_, v_b_3585_);
lean_dec_ref(v_as_3582_);
return v_res_3588_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerEnumAttributes_spec__1(lean_object* v_00_u03b1_3589_, lean_object* v_newState_3590_, lean_object* v_x_3591_, lean_object* v_x_3592_){
_start:
{
lean_object* v___x_3593_; 
v___x_3593_ = l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___redArg(v_newState_3590_, v_x_3591_, v_x_3592_);
return v___x_3593_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___boxed(lean_object* v_00_u03b1_3594_, lean_object* v_newState_3595_, lean_object* v_x_3596_, lean_object* v_x_3597_){
_start:
{
lean_object* v_res_3598_; 
v_res_3598_ = l_List_foldl___at___00Lean_registerEnumAttributes_spec__1(v_00_u03b1_3594_, v_newState_3595_, v_x_3596_, v_x_3597_);
lean_dec(v_newState_3595_);
return v_res_3598_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2(lean_object* v_00_u03b1_3599_, lean_object* v_validate_3600_, lean_object* v_a_3601_, lean_object* v_ref_3602_, uint8_t v_applicationTime_3603_, lean_object* v_a_3604_, lean_object* v_a_3605_){
_start:
{
lean_object* v___x_3606_; 
v___x_3606_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg(v_validate_3600_, v_a_3601_, v_ref_3602_, v_applicationTime_3603_, v_a_3604_, v_a_3605_);
return v___x_3606_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___boxed(lean_object* v_00_u03b1_3607_, lean_object* v_validate_3608_, lean_object* v_a_3609_, lean_object* v_ref_3610_, lean_object* v_applicationTime_3611_, lean_object* v_a_3612_, lean_object* v_a_3613_){
_start:
{
uint8_t v_applicationTime_boxed_3614_; lean_object* v_res_3615_; 
v_applicationTime_boxed_3614_ = lean_unbox(v_applicationTime_3611_);
v_res_3615_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2(v_00_u03b1_3607_, v_validate_3608_, v_a_3609_, v_ref_3610_, v_applicationTime_boxed_3614_, v_a_3612_, v_a_3613_);
return v_res_3615_;
}
}
LEAN_EXPORT lean_object* l_Lean_EnumAttributes_getValue___redArg(lean_object* v_inst_3616_, lean_object* v_attr_3617_, lean_object* v_env_3618_, lean_object* v_decl_3619_){
_start:
{
lean_object* v___x_3620_; lean_object* v___x_3621_; 
v___x_3620_ = lean_box(1);
v___x_3621_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3618_, v_decl_3619_);
if (lean_obj_tag(v___x_3621_) == 0)
{
lean_object* v_ext_3622_; lean_object* v_toEnvExtension_3623_; lean_object* v_asyncMode_3624_; lean_object* v___x_3625_; lean_object* v___x_3626_; 
lean_dec(v_inst_3616_);
v_ext_3622_ = lean_ctor_get(v_attr_3617_, 1);
lean_inc_ref(v_ext_3622_);
lean_dec_ref(v_attr_3617_);
v_toEnvExtension_3623_ = lean_ctor_get(v_ext_3622_, 0);
v_asyncMode_3624_ = lean_ctor_get(v_toEnvExtension_3623_, 2);
lean_inc(v_asyncMode_3624_);
lean_inc(v_decl_3619_);
v___x_3625_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3620_, v_ext_3622_, v_env_3618_, v_asyncMode_3624_, v_decl_3619_);
lean_dec(v_asyncMode_3624_);
lean_dec_ref(v_ext_3622_);
v___x_3626_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_3625_, v_decl_3619_);
lean_dec(v_decl_3619_);
lean_dec(v___x_3625_);
return v___x_3626_;
}
else
{
lean_object* v_val_3627_; lean_object* v_ext_3628_; lean_object* v___x_3630_; uint8_t v_isShared_3631_; uint8_t v_isSharedCheck_3658_; 
v_val_3627_ = lean_ctor_get(v___x_3621_, 0);
lean_inc(v_val_3627_);
lean_dec_ref_known(v___x_3621_, 1);
v_ext_3628_ = lean_ctor_get(v_attr_3617_, 1);
v_isSharedCheck_3658_ = !lean_is_exclusive(v_attr_3617_);
if (v_isSharedCheck_3658_ == 0)
{
lean_object* v_unused_3659_; 
v_unused_3659_ = lean_ctor_get(v_attr_3617_, 0);
lean_dec(v_unused_3659_);
v___x_3630_ = v_attr_3617_;
v_isShared_3631_ = v_isSharedCheck_3658_;
goto v_resetjp_3629_;
}
else
{
lean_inc(v_ext_3628_);
lean_dec(v_attr_3617_);
v___x_3630_ = lean_box(0);
v_isShared_3631_ = v_isSharedCheck_3658_;
goto v_resetjp_3629_;
}
v_resetjp_3629_:
{
uint8_t v___x_3632_; lean_object* v___x_3633_; lean_object* v___x_3634_; lean_object* v___x_3635_; uint8_t v___x_3636_; 
v___x_3632_ = 0;
v___x_3633_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_3620_, v_ext_3628_, v_env_3618_, v_val_3627_, v___x_3632_);
lean_dec(v_val_3627_);
lean_dec_ref(v_env_3618_);
lean_dec_ref(v_ext_3628_);
v___x_3634_ = lean_unsigned_to_nat(0u);
v___x_3635_ = lean_array_get_size(v___x_3633_);
v___x_3636_ = lean_nat_dec_lt(v___x_3634_, v___x_3635_);
if (v___x_3636_ == 0)
{
lean_object* v___x_3637_; 
lean_dec_ref(v___x_3633_);
lean_del_object(v___x_3630_);
lean_dec(v_decl_3619_);
lean_dec(v_inst_3616_);
v___x_3637_ = lean_box(0);
return v___x_3637_;
}
else
{
lean_object* v___x_3638_; lean_object* v___x_3639_; uint8_t v___x_3640_; 
v___x_3638_ = lean_unsigned_to_nat(1u);
v___x_3639_ = lean_nat_sub(v___x_3635_, v___x_3638_);
v___x_3640_ = lean_nat_dec_le(v___x_3634_, v___x_3639_);
if (v___x_3640_ == 0)
{
lean_object* v___x_3641_; 
lean_dec(v___x_3639_);
lean_dec_ref(v___x_3633_);
lean_del_object(v___x_3630_);
lean_dec(v_decl_3619_);
lean_dec(v_inst_3616_);
v___x_3641_ = lean_box(0);
return v___x_3641_;
}
else
{
lean_object* v___f_3642_; lean_object* v___x_3644_; 
v___f_3642_ = ((lean_object*)(l_Lean_ParametricAttribute_getParam_x3f___redArg___closed__1));
if (v_isShared_3631_ == 0)
{
lean_ctor_set(v___x_3630_, 1, v_inst_3616_);
lean_ctor_set(v___x_3630_, 0, v_decl_3619_);
v___x_3644_ = v___x_3630_;
goto v_reusejp_3643_;
}
else
{
lean_object* v_reuseFailAlloc_3657_; 
v_reuseFailAlloc_3657_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3657_, 0, v_decl_3619_);
lean_ctor_set(v_reuseFailAlloc_3657_, 1, v_inst_3616_);
v___x_3644_ = v_reuseFailAlloc_3657_;
goto v_reusejp_3643_;
}
v_reusejp_3643_:
{
lean_object* v___x_3645_; lean_object* v___x_3646_; 
v___x_3645_ = ((lean_object*)(l_Lean_ParametricAttribute_getParam_x3f___redArg___closed__2));
v___x_3646_ = l_Array_binSearchAux___redArg(v___f_3642_, v___x_3645_, v___x_3633_, v___x_3644_, v___x_3634_, v___x_3639_);
lean_dec_ref(v___x_3633_);
if (lean_obj_tag(v___x_3646_) == 0)
{
lean_object* v___x_3647_; 
v___x_3647_ = lean_box(0);
return v___x_3647_;
}
else
{
lean_object* v_val_3648_; lean_object* v___x_3650_; uint8_t v_isShared_3651_; uint8_t v_isSharedCheck_3656_; 
v_val_3648_ = lean_ctor_get(v___x_3646_, 0);
v_isSharedCheck_3656_ = !lean_is_exclusive(v___x_3646_);
if (v_isSharedCheck_3656_ == 0)
{
v___x_3650_ = v___x_3646_;
v_isShared_3651_ = v_isSharedCheck_3656_;
goto v_resetjp_3649_;
}
else
{
lean_inc(v_val_3648_);
lean_dec(v___x_3646_);
v___x_3650_ = lean_box(0);
v_isShared_3651_ = v_isSharedCheck_3656_;
goto v_resetjp_3649_;
}
v_resetjp_3649_:
{
lean_object* v_snd_3652_; lean_object* v___x_3654_; 
v_snd_3652_ = lean_ctor_get(v_val_3648_, 1);
lean_inc(v_snd_3652_);
lean_dec(v_val_3648_);
if (v_isShared_3651_ == 0)
{
lean_ctor_set(v___x_3650_, 0, v_snd_3652_);
v___x_3654_ = v___x_3650_;
goto v_reusejp_3653_;
}
else
{
lean_object* v_reuseFailAlloc_3655_; 
v_reuseFailAlloc_3655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3655_, 0, v_snd_3652_);
v___x_3654_ = v_reuseFailAlloc_3655_;
goto v_reusejp_3653_;
}
v_reusejp_3653_:
{
return v___x_3654_;
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
LEAN_EXPORT lean_object* l_Lean_EnumAttributes_getValue(lean_object* v_00_u03b1_3660_, lean_object* v_inst_3661_, lean_object* v_attr_3662_, lean_object* v_env_3663_, lean_object* v_decl_3664_){
_start:
{
lean_object* v___x_3665_; 
v___x_3665_ = l_Lean_EnumAttributes_getValue___redArg(v_inst_3661_, v_attr_3662_, v_env_3663_, v_decl_3664_);
return v___x_3665_;
}
}
LEAN_EXPORT lean_object* l_Lean_EnumAttributes_setValue___redArg(lean_object* v_attrs_3674_, lean_object* v_env_3675_, lean_object* v_decl_3676_, lean_object* v_val_3677_){
_start:
{
lean_object* v_ext_3678_; lean_object* v___x_3680_; uint8_t v_isShared_3681_; uint8_t v_isSharedCheck_3742_; 
v_ext_3678_ = lean_ctor_get(v_attrs_3674_, 1);
v_isSharedCheck_3742_ = !lean_is_exclusive(v_attrs_3674_);
if (v_isSharedCheck_3742_ == 0)
{
lean_object* v_unused_3743_; 
v_unused_3743_ = lean_ctor_get(v_attrs_3674_, 0);
lean_dec(v_unused_3743_);
v___x_3680_ = v_attrs_3674_;
v_isShared_3681_ = v_isSharedCheck_3742_;
goto v_resetjp_3679_;
}
else
{
lean_inc(v_ext_3678_);
lean_dec(v_attrs_3674_);
v___x_3680_ = lean_box(0);
v_isShared_3681_ = v_isSharedCheck_3742_;
goto v_resetjp_3679_;
}
v_resetjp_3679_:
{
lean_object* v_toEnvExtension_3682_; lean_object* v_name_3683_; lean_object* v___x_3684_; uint8_t v___x_3685_; lean_object* v___x_3686_; lean_object* v___x_3687_; lean_object* v___x_3688_; lean_object* v___x_3689_; lean_object* v___x_3690_; lean_object* v___x_3691_; lean_object* v___x_3692_; lean_object* v_pfx_3693_; lean_object* v___x_3694_; 
v_toEnvExtension_3682_ = lean_ctor_get(v_ext_3678_, 0);
v_name_3683_ = lean_ctor_get(v_ext_3678_, 1);
v___x_3684_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__0));
v___x_3685_ = 1;
lean_inc(v_name_3683_);
v___x_3686_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_3683_, v___x_3685_);
v___x_3687_ = lean_string_append(v___x_3684_, v___x_3686_);
lean_dec_ref(v___x_3686_);
v___x_3688_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__1));
v___x_3689_ = lean_string_append(v___x_3687_, v___x_3688_);
lean_inc(v_decl_3676_);
v___x_3690_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_decl_3676_, v___x_3685_);
v___x_3691_ = lean_string_append(v___x_3689_, v___x_3690_);
lean_dec_ref(v___x_3690_);
v___x_3692_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__4));
v_pfx_3693_ = lean_string_append(v___x_3691_, v___x_3692_);
v___x_3694_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3675_, v_decl_3676_);
if (lean_obj_tag(v___x_3694_) == 0)
{
lean_object* v_asyncMode_3695_; uint8_t v___x_3702_; 
v_asyncMode_3695_ = lean_ctor_get(v_toEnvExtension_3682_, 2);
lean_inc(v_asyncMode_3695_);
lean_inc(v_decl_3676_);
lean_inc_ref(v_env_3675_);
v___x_3702_ = l_Lean_EnvExtension_asyncMayModify___redArg(v_env_3675_, v_decl_3676_, v_asyncMode_3695_);
if (v___x_3702_ == 0)
{
lean_object* v___x_3703_; lean_object* v___x_3704_; lean_object* v___y_3706_; lean_object* v___x_3710_; 
lean_dec(v_asyncMode_3695_);
lean_del_object(v___x_3680_);
lean_dec_ref(v_ext_3678_);
lean_dec(v_val_3677_);
lean_dec(v_decl_3676_);
v___x_3703_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__2));
v___x_3704_ = lean_string_append(v_pfx_3693_, v___x_3703_);
v___x_3710_ = l_Lean_Environment_asyncPrefix_x3f(v_env_3675_);
if (lean_obj_tag(v___x_3710_) == 0)
{
lean_object* v___x_3711_; 
v___x_3711_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__3));
v___y_3706_ = v___x_3711_;
goto v___jp_3705_;
}
else
{
lean_object* v_val_3712_; lean_object* v___x_3713_; lean_object* v___x_3714_; lean_object* v___x_3715_; lean_object* v___x_3716_; lean_object* v___x_3717_; lean_object* v___x_3718_; 
v_val_3712_ = lean_ctor_get(v___x_3710_, 0);
lean_inc(v_val_3712_);
lean_dec_ref_known(v___x_3710_, 1);
v___x_3713_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__4));
v___x_3714_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_val_3712_, v___x_3685_);
v___x_3715_ = l_addParenHeuristic(v___x_3714_);
v___x_3716_ = lean_string_append(v___x_3713_, v___x_3715_);
lean_dec_ref(v___x_3715_);
v___x_3717_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__5));
v___x_3718_ = lean_string_append(v___x_3716_, v___x_3717_);
v___y_3706_ = v___x_3718_;
goto v___jp_3705_;
}
v___jp_3705_:
{
lean_object* v___x_3707_; lean_object* v___x_3708_; lean_object* v___x_3709_; 
v___x_3707_ = lean_string_append(v___x_3704_, v___y_3706_);
lean_dec_ref(v___y_3706_);
v___x_3708_ = lean_string_append(v___x_3707_, v___x_3692_);
v___x_3709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3709_, 0, v___x_3708_);
return v___x_3709_;
}
}
else
{
lean_object* v___x_3719_; lean_object* v___x_3720_; lean_object* v___x_3721_; 
v___x_3719_ = lean_box(1);
lean_inc(v_decl_3676_);
lean_inc_ref(v_env_3675_);
v___x_3720_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3719_, v_ext_3678_, v_env_3675_, v_asyncMode_3695_, v_decl_3676_);
v___x_3721_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_3720_, v_decl_3676_);
lean_dec(v___x_3720_);
if (lean_obj_tag(v___x_3721_) == 0)
{
lean_dec_ref(v_pfx_3693_);
goto v___jp_3696_;
}
else
{
lean_object* v___x_3723_; uint8_t v_isShared_3724_; uint8_t v_isSharedCheck_3730_; 
v_isSharedCheck_3730_ = !lean_is_exclusive(v___x_3721_);
if (v_isSharedCheck_3730_ == 0)
{
lean_object* v_unused_3731_; 
v_unused_3731_ = lean_ctor_get(v___x_3721_, 0);
lean_dec(v_unused_3731_);
v___x_3723_ = v___x_3721_;
v_isShared_3724_ = v_isSharedCheck_3730_;
goto v_resetjp_3722_;
}
else
{
lean_dec(v___x_3721_);
v___x_3723_ = lean_box(0);
v_isShared_3724_ = v_isSharedCheck_3730_;
goto v_resetjp_3722_;
}
v_resetjp_3722_:
{
if (v___x_3702_ == 0)
{
lean_del_object(v___x_3723_);
lean_dec_ref(v_pfx_3693_);
goto v___jp_3696_;
}
else
{
lean_object* v___x_3725_; lean_object* v___x_3726_; lean_object* v___x_3728_; 
lean_dec(v_asyncMode_3695_);
lean_del_object(v___x_3680_);
lean_dec_ref(v_ext_3678_);
lean_dec(v_val_3677_);
lean_dec(v_decl_3676_);
lean_dec_ref(v_env_3675_);
v___x_3725_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__6));
v___x_3726_ = lean_string_append(v_pfx_3693_, v___x_3725_);
if (v_isShared_3724_ == 0)
{
lean_ctor_set_tag(v___x_3723_, 0);
lean_ctor_set(v___x_3723_, 0, v___x_3726_);
v___x_3728_ = v___x_3723_;
goto v_reusejp_3727_;
}
else
{
lean_object* v_reuseFailAlloc_3729_; 
v_reuseFailAlloc_3729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3729_, 0, v___x_3726_);
v___x_3728_ = v_reuseFailAlloc_3729_;
goto v_reusejp_3727_;
}
v_reusejp_3727_:
{
return v___x_3728_;
}
}
}
}
}
v___jp_3696_:
{
lean_object* v___x_3698_; 
lean_inc(v_decl_3676_);
if (v_isShared_3681_ == 0)
{
lean_ctor_set(v___x_3680_, 1, v_val_3677_);
lean_ctor_set(v___x_3680_, 0, v_decl_3676_);
v___x_3698_ = v___x_3680_;
goto v_reusejp_3697_;
}
else
{
lean_object* v_reuseFailAlloc_3701_; 
v_reuseFailAlloc_3701_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3701_, 0, v_decl_3676_);
lean_ctor_set(v_reuseFailAlloc_3701_, 1, v_val_3677_);
v___x_3698_ = v_reuseFailAlloc_3701_;
goto v_reusejp_3697_;
}
v_reusejp_3697_:
{
lean_object* v___x_3699_; lean_object* v___x_3700_; 
v___x_3699_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_ext_3678_, v_env_3675_, v___x_3698_, v_asyncMode_3695_, v_decl_3676_);
lean_dec(v_asyncMode_3695_);
v___x_3700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3700_, 0, v___x_3699_);
return v___x_3700_;
}
}
}
else
{
lean_object* v___x_3733_; uint8_t v_isShared_3734_; uint8_t v_isSharedCheck_3740_; 
lean_del_object(v___x_3680_);
lean_dec_ref(v_ext_3678_);
lean_dec(v_val_3677_);
lean_dec(v_decl_3676_);
lean_dec_ref(v_env_3675_);
v_isSharedCheck_3740_ = !lean_is_exclusive(v___x_3694_);
if (v_isSharedCheck_3740_ == 0)
{
lean_object* v_unused_3741_; 
v_unused_3741_ = lean_ctor_get(v___x_3694_, 0);
lean_dec(v_unused_3741_);
v___x_3733_ = v___x_3694_;
v_isShared_3734_ = v_isSharedCheck_3740_;
goto v_resetjp_3732_;
}
else
{
lean_dec(v___x_3694_);
v___x_3733_ = lean_box(0);
v_isShared_3734_ = v_isSharedCheck_3740_;
goto v_resetjp_3732_;
}
v_resetjp_3732_:
{
lean_object* v___x_3735_; lean_object* v___x_3736_; lean_object* v___x_3738_; 
v___x_3735_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__7));
v___x_3736_ = lean_string_append(v_pfx_3693_, v___x_3735_);
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
}
LEAN_EXPORT lean_object* l_Lean_EnumAttributes_setValue(lean_object* v_00_u03b1_3744_, lean_object* v_attrs_3745_, lean_object* v_env_3746_, lean_object* v_decl_3747_, lean_object* v_val_3748_){
_start:
{
lean_object* v___x_3749_; 
v___x_3749_ = l_Lean_EnumAttributes_setValue___redArg(v_attrs_3745_, v_env_3746_, v_decl_3747_, v_val_3748_);
return v___x_3749_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_2990505691____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3751_; lean_object* v___x_3752_; lean_object* v___x_3753_; 
v___x_3751_ = lean_obj_once(&l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_, &l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2__once, _init_l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_);
v___x_3752_ = lean_st_mk_ref(v___x_3751_);
v___x_3753_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3753_, 0, v___x_3752_);
return v___x_3753_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_2990505691____hygCtx___hyg_2____boxed(lean_object* v_a_3754_){
_start:
{
lean_object* v_res_3755_; 
v_res_3755_ = l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_2990505691____hygCtx___hyg_2_();
return v_res_3755_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerAttributeImplBuilder(lean_object* v_builderId_3758_, lean_object* v_builder_3759_){
_start:
{
lean_object* v___x_3761_; lean_object* v___x_3762_; uint8_t v___x_3763_; 
v___x_3761_ = l_Lean_attributeImplBuilderTableRef;
v___x_3762_ = lean_st_ref_get(v___x_3761_);
v___x_3763_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(v___x_3762_, v_builderId_3758_);
lean_dec(v___x_3762_);
if (v___x_3763_ == 0)
{
lean_object* v___x_3764_; lean_object* v___x_3765_; lean_object* v___x_3766_; lean_object* v___x_3767_; 
v___x_3764_ = lean_st_ref_take(v___x_3761_);
v___x_3765_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1___redArg(v___x_3764_, v_builderId_3758_, v_builder_3759_);
v___x_3766_ = lean_st_ref_set(v___x_3761_, v___x_3765_);
v___x_3767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3767_, 0, v___x_3766_);
return v___x_3767_;
}
else
{
lean_object* v___x_3768_; lean_object* v___x_3769_; lean_object* v___x_3770_; lean_object* v___x_3771_; lean_object* v___x_3772_; lean_object* v___x_3773_; lean_object* v___x_3774_; 
lean_dec_ref(v_builder_3759_);
v___x_3768_ = ((lean_object*)(l_Lean_registerAttributeImplBuilder___closed__0));
v___x_3769_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_builderId_3758_, v___x_3763_);
v___x_3770_ = lean_string_append(v___x_3768_, v___x_3769_);
lean_dec_ref(v___x_3769_);
v___x_3771_ = ((lean_object*)(l_Lean_registerAttributeImplBuilder___closed__1));
v___x_3772_ = lean_string_append(v___x_3770_, v___x_3771_);
v___x_3773_ = lean_mk_io_user_error(v___x_3772_);
v___x_3774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3774_, 0, v___x_3773_);
return v___x_3774_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerAttributeImplBuilder___boxed(lean_object* v_builderId_3775_, lean_object* v_builder_3776_, lean_object* v_a_3777_){
_start:
{
lean_object* v_res_3778_; 
v_res_3778_ = l_Lean_registerAttributeImplBuilder(v_builderId_3775_, v_builder_3776_);
return v_res_3778_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___redArg(lean_object* v_e_3779_){
_start:
{
if (lean_obj_tag(v_e_3779_) == 0)
{
lean_object* v_a_3781_; lean_object* v___x_3783_; uint8_t v_isShared_3784_; uint8_t v_isSharedCheck_3789_; 
v_a_3781_ = lean_ctor_get(v_e_3779_, 0);
v_isSharedCheck_3789_ = !lean_is_exclusive(v_e_3779_);
if (v_isSharedCheck_3789_ == 0)
{
v___x_3783_ = v_e_3779_;
v_isShared_3784_ = v_isSharedCheck_3789_;
goto v_resetjp_3782_;
}
else
{
lean_inc(v_a_3781_);
lean_dec(v_e_3779_);
v___x_3783_ = lean_box(0);
v_isShared_3784_ = v_isSharedCheck_3789_;
goto v_resetjp_3782_;
}
v_resetjp_3782_:
{
lean_object* v___x_3785_; lean_object* v___x_3787_; 
v___x_3785_ = lean_mk_io_user_error(v_a_3781_);
if (v_isShared_3784_ == 0)
{
lean_ctor_set_tag(v___x_3783_, 1);
lean_ctor_set(v___x_3783_, 0, v___x_3785_);
v___x_3787_ = v___x_3783_;
goto v_reusejp_3786_;
}
else
{
lean_object* v_reuseFailAlloc_3788_; 
v_reuseFailAlloc_3788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3788_, 0, v___x_3785_);
v___x_3787_ = v_reuseFailAlloc_3788_;
goto v_reusejp_3786_;
}
v_reusejp_3786_:
{
return v___x_3787_;
}
}
}
else
{
lean_object* v_a_3790_; lean_object* v___x_3792_; uint8_t v_isShared_3793_; uint8_t v_isSharedCheck_3797_; 
v_a_3790_ = lean_ctor_get(v_e_3779_, 0);
v_isSharedCheck_3797_ = !lean_is_exclusive(v_e_3779_);
if (v_isSharedCheck_3797_ == 0)
{
v___x_3792_ = v_e_3779_;
v_isShared_3793_ = v_isSharedCheck_3797_;
goto v_resetjp_3791_;
}
else
{
lean_inc(v_a_3790_);
lean_dec(v_e_3779_);
v___x_3792_ = lean_box(0);
v_isShared_3793_ = v_isSharedCheck_3797_;
goto v_resetjp_3791_;
}
v_resetjp_3791_:
{
lean_object* v___x_3795_; 
if (v_isShared_3793_ == 0)
{
lean_ctor_set_tag(v___x_3792_, 0);
v___x_3795_ = v___x_3792_;
goto v_reusejp_3794_;
}
else
{
lean_object* v_reuseFailAlloc_3796_; 
v_reuseFailAlloc_3796_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3796_, 0, v_a_3790_);
v___x_3795_ = v_reuseFailAlloc_3796_;
goto v_reusejp_3794_;
}
v_reusejp_3794_:
{
return v___x_3795_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___redArg___boxed(lean_object* v_e_3798_, lean_object* v_a_3799_){
_start:
{
lean_object* v_res_3800_; 
v_res_3800_ = l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___redArg(v_e_3798_);
return v_res_3800_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1(lean_object* v_00_u03b1_3801_, lean_object* v_e_3802_){
_start:
{
lean_object* v___x_3804_; 
v___x_3804_ = l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___redArg(v_e_3802_);
return v___x_3804_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___boxed(lean_object* v_00_u03b1_3805_, lean_object* v_e_3806_, lean_object* v_a_3807_){
_start:
{
lean_object* v_res_3808_; 
v_res_3808_ = l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1(v_00_u03b1_3805_, v_e_3806_);
return v_res_3808_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___redArg(lean_object* v_a_3809_, lean_object* v_x_3810_){
_start:
{
if (lean_obj_tag(v_x_3810_) == 0)
{
lean_object* v___x_3811_; 
v___x_3811_ = lean_box(0);
return v___x_3811_;
}
else
{
lean_object* v_key_3812_; lean_object* v_value_3813_; lean_object* v_tail_3814_; uint8_t v___x_3815_; 
v_key_3812_ = lean_ctor_get(v_x_3810_, 0);
v_value_3813_ = lean_ctor_get(v_x_3810_, 1);
v_tail_3814_ = lean_ctor_get(v_x_3810_, 2);
v___x_3815_ = lean_name_eq(v_key_3812_, v_a_3809_);
if (v___x_3815_ == 0)
{
v_x_3810_ = v_tail_3814_;
goto _start;
}
else
{
lean_object* v___x_3817_; 
lean_inc(v_value_3813_);
v___x_3817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3817_, 0, v_value_3813_);
return v___x_3817_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___redArg___boxed(lean_object* v_a_3818_, lean_object* v_x_3819_){
_start:
{
lean_object* v_res_3820_; 
v_res_3820_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___redArg(v_a_3818_, v_x_3819_);
lean_dec(v_x_3819_);
lean_dec(v_a_3818_);
return v_res_3820_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(lean_object* v_m_3821_, lean_object* v_a_3822_){
_start:
{
lean_object* v_buckets_3823_; lean_object* v___x_3824_; uint64_t v___y_3826_; 
v_buckets_3823_ = lean_ctor_get(v_m_3821_, 1);
v___x_3824_ = lean_array_get_size(v_buckets_3823_);
if (lean_obj_tag(v_a_3822_) == 0)
{
uint64_t v___x_3840_; 
v___x_3840_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg___closed__0);
v___y_3826_ = v___x_3840_;
goto v___jp_3825_;
}
else
{
uint64_t v_hash_3841_; 
v_hash_3841_ = lean_ctor_get_uint64(v_a_3822_, sizeof(void*)*2);
v___y_3826_ = v_hash_3841_;
goto v___jp_3825_;
}
v___jp_3825_:
{
uint64_t v___x_3827_; uint64_t v___x_3828_; uint64_t v_fold_3829_; uint64_t v___x_3830_; uint64_t v___x_3831_; uint64_t v___x_3832_; size_t v___x_3833_; size_t v___x_3834_; size_t v___x_3835_; size_t v___x_3836_; size_t v___x_3837_; lean_object* v___x_3838_; lean_object* v___x_3839_; 
v___x_3827_ = 32ULL;
v___x_3828_ = lean_uint64_shift_right(v___y_3826_, v___x_3827_);
v_fold_3829_ = lean_uint64_xor(v___y_3826_, v___x_3828_);
v___x_3830_ = 16ULL;
v___x_3831_ = lean_uint64_shift_right(v_fold_3829_, v___x_3830_);
v___x_3832_ = lean_uint64_xor(v_fold_3829_, v___x_3831_);
v___x_3833_ = lean_uint64_to_usize(v___x_3832_);
v___x_3834_ = lean_usize_of_nat(v___x_3824_);
v___x_3835_ = ((size_t)1ULL);
v___x_3836_ = lean_usize_sub(v___x_3834_, v___x_3835_);
v___x_3837_ = lean_usize_land(v___x_3833_, v___x_3836_);
v___x_3838_ = lean_array_uget_borrowed(v_buckets_3823_, v___x_3837_);
v___x_3839_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___redArg(v_a_3822_, v___x_3838_);
return v___x_3839_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg___boxed(lean_object* v_m_3842_, lean_object* v_a_3843_){
_start:
{
lean_object* v_res_3844_; 
v_res_3844_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(v_m_3842_, v_a_3843_);
lean_dec(v_a_3843_);
lean_dec_ref(v_m_3842_);
return v_res_3844_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAttributeImplOfEntry(lean_object* v_e_3846_){
_start:
{
lean_object* v___x_3848_; lean_object* v___x_3849_; lean_object* v_builderId_3850_; lean_object* v_ref_3851_; lean_object* v_args_3852_; lean_object* v___x_3853_; 
v___x_3848_ = l_Lean_attributeImplBuilderTableRef;
v___x_3849_ = lean_st_ref_get(v___x_3848_);
v_builderId_3850_ = lean_ctor_get(v_e_3846_, 0);
lean_inc(v_builderId_3850_);
v_ref_3851_ = lean_ctor_get(v_e_3846_, 1);
lean_inc(v_ref_3851_);
v_args_3852_ = lean_ctor_get(v_e_3846_, 2);
lean_inc(v_args_3852_);
lean_dec_ref(v_e_3846_);
v___x_3853_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(v___x_3849_, v_builderId_3850_);
lean_dec(v___x_3849_);
if (lean_obj_tag(v___x_3853_) == 0)
{
lean_object* v___x_3854_; uint8_t v___x_3855_; lean_object* v___x_3856_; lean_object* v___x_3857_; lean_object* v___x_3858_; lean_object* v___x_3859_; lean_object* v___x_3860_; lean_object* v___x_3861_; 
lean_dec(v_args_3852_);
lean_dec(v_ref_3851_);
v___x_3854_ = ((lean_object*)(l_Lean_mkAttributeImplOfEntry___closed__0));
v___x_3855_ = 1;
v___x_3856_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_builderId_3850_, v___x_3855_);
v___x_3857_ = lean_string_append(v___x_3854_, v___x_3856_);
lean_dec_ref(v___x_3856_);
v___x_3858_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__4));
v___x_3859_ = lean_string_append(v___x_3857_, v___x_3858_);
v___x_3860_ = lean_mk_io_user_error(v___x_3859_);
v___x_3861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3861_, 0, v___x_3860_);
return v___x_3861_;
}
else
{
lean_object* v_val_3862_; lean_object* v___x_3863_; lean_object* v___x_3864_; 
lean_dec(v_builderId_3850_);
v_val_3862_ = lean_ctor_get(v___x_3853_, 0);
lean_inc(v_val_3862_);
lean_dec_ref_known(v___x_3853_, 1);
v___x_3863_ = lean_apply_2(v_val_3862_, v_ref_3851_, v_args_3852_);
v___x_3864_ = l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___redArg(v___x_3863_);
return v___x_3864_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkAttributeImplOfEntry___boxed(lean_object* v_e_3865_, lean_object* v_a_3866_){
_start:
{
lean_object* v_res_3867_; 
v_res_3867_ = l_Lean_mkAttributeImplOfEntry(v_e_3865_);
return v_res_3867_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0(lean_object* v_00_u03b2_3868_, lean_object* v_m_3869_, lean_object* v_a_3870_){
_start:
{
lean_object* v___x_3871_; 
v___x_3871_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(v_m_3869_, v_a_3870_);
return v___x_3871_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___boxed(lean_object* v_00_u03b2_3872_, lean_object* v_m_3873_, lean_object* v_a_3874_){
_start:
{
lean_object* v_res_3875_; 
v_res_3875_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0(v_00_u03b2_3872_, v_m_3873_, v_a_3874_);
lean_dec(v_a_3874_);
lean_dec_ref(v_m_3873_);
return v_res_3875_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0(lean_object* v_00_u03b2_3876_, lean_object* v_a_3877_, lean_object* v_x_3878_){
_start:
{
lean_object* v___x_3879_; 
v___x_3879_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___redArg(v_a_3877_, v_x_3878_);
return v___x_3879_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3880_, lean_object* v_a_3881_, lean_object* v_x_3882_){
_start:
{
lean_object* v_res_3883_; 
v_res_3883_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0(v_00_u03b2_3880_, v_a_3881_, v_x_3882_);
lean_dec(v_x_3882_);
lean_dec(v_a_3881_);
return v_res_3883_;
}
}
static lean_object* _init_l_Lean_instInhabitedAttributeExtensionState_default___closed__0(void){
_start:
{
lean_object* v___x_3884_; lean_object* v___x_3885_; lean_object* v___x_3886_; 
v___x_3884_ = lean_obj_once(&l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_, &l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2__once, _init_l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_);
v___x_3885_ = lean_box(0);
v___x_3886_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3886_, 0, v___x_3885_);
lean_ctor_set(v___x_3886_, 1, v___x_3884_);
return v___x_3886_;
}
}
static lean_object* _init_l_Lean_instInhabitedAttributeExtensionState_default(void){
_start:
{
lean_object* v___x_3887_; 
v___x_3887_ = lean_obj_once(&l_Lean_instInhabitedAttributeExtensionState_default___closed__0, &l_Lean_instInhabitedAttributeExtensionState_default___closed__0_once, _init_l_Lean_instInhabitedAttributeExtensionState_default___closed__0);
return v___x_3887_;
}
}
static lean_object* _init_l_Lean_instInhabitedAttributeExtensionState(void){
_start:
{
lean_object* v___x_3888_; 
v___x_3888_ = l_Lean_instInhabitedAttributeExtensionState_default;
return v___x_3888_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_AttributeExtension_mkInitial(){
_start:
{
lean_object* v___x_3890_; lean_object* v___x_3891_; lean_object* v___x_3892_; lean_object* v___x_3893_; lean_object* v___x_3894_; 
v___x_3890_ = l_Lean_attributeMapRef;
v___x_3891_ = lean_st_ref_get(v___x_3890_);
v___x_3892_ = lean_box(0);
v___x_3893_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3893_, 0, v___x_3892_);
lean_ctor_set(v___x_3893_, 1, v___x_3891_);
v___x_3894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3894_, 0, v___x_3893_);
return v___x_3894_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_AttributeExtension_mkInitial___boxed(lean_object* v_a_3895_){
_start:
{
lean_object* v_res_3896_; 
v_res_3896_ = l___private_Lean_Attributes_0__Lean_AttributeExtension_mkInitial();
return v_res_3896_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAttributeImplOfConstantUnsafe(lean_object* v_env_3902_, lean_object* v_opts_3903_, lean_object* v_declName_3904_){
_start:
{
uint8_t v___x_3907_; lean_object* v___x_3908_; 
v___x_3907_ = 0;
lean_inc(v_declName_3904_);
lean_inc_ref(v_env_3902_);
v___x_3908_ = l_Lean_Environment_find_x3f(v_env_3902_, v_declName_3904_, v___x_3907_);
if (lean_obj_tag(v___x_3908_) == 0)
{
lean_object* v___x_3909_; uint8_t v___x_3910_; lean_object* v___x_3911_; lean_object* v___x_3912_; lean_object* v___x_3913_; lean_object* v___x_3914_; lean_object* v___x_3915_; 
lean_dec_ref(v_env_3902_);
v___x_3909_ = ((lean_object*)(l_Lean_mkAttributeImplOfConstantUnsafe___closed__2));
v___x_3910_ = 1;
v___x_3911_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_declName_3904_, v___x_3910_);
v___x_3912_ = lean_string_append(v___x_3909_, v___x_3911_);
lean_dec_ref(v___x_3911_);
v___x_3913_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__4));
v___x_3914_ = lean_string_append(v___x_3912_, v___x_3913_);
v___x_3915_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3915_, 0, v___x_3914_);
return v___x_3915_;
}
else
{
lean_object* v_val_3916_; lean_object* v___x_3917_; 
v_val_3916_ = lean_ctor_get(v___x_3908_, 0);
lean_inc(v_val_3916_);
lean_dec_ref_known(v___x_3908_, 1);
v___x_3917_ = l_Lean_ConstantInfo_type(v_val_3916_);
lean_dec(v_val_3916_);
if (lean_obj_tag(v___x_3917_) == 4)
{
lean_object* v_declName_3918_; 
v_declName_3918_ = lean_ctor_get(v___x_3917_, 0);
lean_inc(v_declName_3918_);
lean_dec_ref_known(v___x_3917_, 2);
if (lean_obj_tag(v_declName_3918_) == 1)
{
lean_object* v_pre_3919_; 
v_pre_3919_ = lean_ctor_get(v_declName_3918_, 0);
lean_inc(v_pre_3919_);
if (lean_obj_tag(v_pre_3919_) == 1)
{
lean_object* v_pre_3920_; 
v_pre_3920_ = lean_ctor_get(v_pre_3919_, 0);
if (lean_obj_tag(v_pre_3920_) == 0)
{
lean_object* v_str_3921_; lean_object* v_str_3922_; lean_object* v___x_3923_; uint8_t v___x_3924_; 
v_str_3921_ = lean_ctor_get(v_declName_3918_, 1);
lean_inc_ref(v_str_3921_);
lean_dec_ref_known(v_declName_3918_, 2);
v_str_3922_ = lean_ctor_get(v_pre_3919_, 1);
lean_inc_ref(v_str_3922_);
lean_dec_ref_known(v_pre_3919_, 2);
v___x_3923_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__0));
v___x_3924_ = lean_string_dec_eq(v_str_3922_, v___x_3923_);
lean_dec_ref(v_str_3922_);
if (v___x_3924_ == 0)
{
lean_dec_ref(v_str_3921_);
lean_dec(v_declName_3904_);
lean_dec_ref(v_env_3902_);
goto v___jp_3905_;
}
else
{
lean_object* v___x_3925_; uint8_t v___x_3926_; 
v___x_3925_ = ((lean_object*)(l_Lean_mkAttributeImplOfConstantUnsafe___closed__3));
v___x_3926_ = lean_string_dec_eq(v_str_3921_, v___x_3925_);
lean_dec_ref(v_str_3921_);
if (v___x_3926_ == 0)
{
lean_dec(v_declName_3904_);
lean_dec_ref(v_env_3902_);
goto v___jp_3905_;
}
else
{
lean_object* v___x_3927_; 
v___x_3927_ = l_Lean_Environment_evalConst___redArg(v_env_3902_, v_opts_3903_, v_declName_3904_, v___x_3926_);
lean_dec(v_declName_3904_);
lean_dec_ref(v_env_3902_);
return v___x_3927_;
}
}
}
else
{
lean_dec_ref_known(v_pre_3919_, 2);
lean_dec_ref_known(v_declName_3918_, 2);
lean_dec(v_declName_3904_);
lean_dec_ref(v_env_3902_);
goto v___jp_3905_;
}
}
else
{
lean_dec(v_pre_3919_);
lean_dec_ref_known(v_declName_3918_, 2);
lean_dec(v_declName_3904_);
lean_dec_ref(v_env_3902_);
goto v___jp_3905_;
}
}
else
{
lean_dec(v_declName_3918_);
lean_dec(v_declName_3904_);
lean_dec_ref(v_env_3902_);
goto v___jp_3905_;
}
}
else
{
lean_dec_ref(v___x_3917_);
lean_dec(v_declName_3904_);
lean_dec_ref(v_env_3902_);
goto v___jp_3905_;
}
}
v___jp_3905_:
{
lean_object* v___x_3906_; 
v___x_3906_ = ((lean_object*)(l_Lean_mkAttributeImplOfConstantUnsafe___closed__1));
return v___x_3906_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkAttributeImplOfConstantUnsafe___boxed(lean_object* v_env_3928_, lean_object* v_opts_3929_, lean_object* v_declName_3930_){
_start:
{
lean_object* v_res_3931_; 
v_res_3931_ = l_Lean_mkAttributeImplOfConstantUnsafe(v_env_3928_, v_opts_3929_, v_declName_3930_);
lean_dec_ref(v_opts_3929_);
return v_res_3931_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg(lean_object* v_as_3932_, size_t v_i_3933_, size_t v_stop_3934_, lean_object* v_b_3935_){
_start:
{
uint8_t v___x_3937_; 
v___x_3937_ = lean_usize_dec_eq(v_i_3933_, v_stop_3934_);
if (v___x_3937_ == 0)
{
lean_object* v___x_3938_; lean_object* v___x_3939_; 
v___x_3938_ = lean_array_uget_borrowed(v_as_3932_, v_i_3933_);
lean_inc(v___x_3938_);
v___x_3939_ = l_Lean_mkAttributeImplOfEntry(v___x_3938_);
if (lean_obj_tag(v___x_3939_) == 0)
{
lean_object* v_a_3940_; lean_object* v_toAttributeImplCore_3941_; lean_object* v_name_3942_; lean_object* v___x_3943_; size_t v___x_3944_; size_t v___x_3945_; 
v_a_3940_ = lean_ctor_get(v___x_3939_, 0);
lean_inc(v_a_3940_);
lean_dec_ref_known(v___x_3939_, 1);
v_toAttributeImplCore_3941_ = lean_ctor_get(v_a_3940_, 0);
v_name_3942_ = lean_ctor_get(v_toAttributeImplCore_3941_, 1);
lean_inc(v_name_3942_);
v___x_3943_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1___redArg(v_b_3935_, v_name_3942_, v_a_3940_);
v___x_3944_ = ((size_t)1ULL);
v___x_3945_ = lean_usize_add(v_i_3933_, v___x_3944_);
v_i_3933_ = v___x_3945_;
v_b_3935_ = v___x_3943_;
goto _start;
}
else
{
lean_object* v_a_3947_; lean_object* v___x_3949_; uint8_t v_isShared_3950_; uint8_t v_isSharedCheck_3954_; 
lean_dec_ref(v_b_3935_);
v_a_3947_ = lean_ctor_get(v___x_3939_, 0);
v_isSharedCheck_3954_ = !lean_is_exclusive(v___x_3939_);
if (v_isSharedCheck_3954_ == 0)
{
v___x_3949_ = v___x_3939_;
v_isShared_3950_ = v_isSharedCheck_3954_;
goto v_resetjp_3948_;
}
else
{
lean_inc(v_a_3947_);
lean_dec(v___x_3939_);
v___x_3949_ = lean_box(0);
v_isShared_3950_ = v_isSharedCheck_3954_;
goto v_resetjp_3948_;
}
v_resetjp_3948_:
{
lean_object* v___x_3952_; 
if (v_isShared_3950_ == 0)
{
v___x_3952_ = v___x_3949_;
goto v_reusejp_3951_;
}
else
{
lean_object* v_reuseFailAlloc_3953_; 
v_reuseFailAlloc_3953_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3953_, 0, v_a_3947_);
v___x_3952_ = v_reuseFailAlloc_3953_;
goto v_reusejp_3951_;
}
v_reusejp_3951_:
{
return v___x_3952_;
}
}
}
}
else
{
lean_object* v___x_3955_; 
v___x_3955_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3955_, 0, v_b_3935_);
return v___x_3955_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg___boxed(lean_object* v_as_3956_, lean_object* v_i_3957_, lean_object* v_stop_3958_, lean_object* v_b_3959_, lean_object* v___y_3960_){
_start:
{
size_t v_i_boxed_3961_; size_t v_stop_boxed_3962_; lean_object* v_res_3963_; 
v_i_boxed_3961_ = lean_unbox_usize(v_i_3957_);
lean_dec(v_i_3957_);
v_stop_boxed_3962_ = lean_unbox_usize(v_stop_3958_);
lean_dec(v_stop_3958_);
v_res_3963_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg(v_as_3956_, v_i_boxed_3961_, v_stop_boxed_3962_, v_b_3959_);
lean_dec_ref(v_as_3956_);
return v_res_3963_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__1(lean_object* v_as_3964_, size_t v_i_3965_, size_t v_stop_3966_, lean_object* v_b_3967_, lean_object* v___y_3968_){
_start:
{
lean_object* v_a_3971_; lean_object* v___y_3976_; uint8_t v___x_3978_; 
v___x_3978_ = lean_usize_dec_eq(v_i_3965_, v_stop_3966_);
if (v___x_3978_ == 0)
{
lean_object* v___x_3979_; lean_object* v___x_3980_; lean_object* v___x_3981_; uint8_t v___x_3982_; 
v___x_3979_ = lean_array_uget_borrowed(v_as_3964_, v_i_3965_);
v___x_3980_ = lean_unsigned_to_nat(0u);
v___x_3981_ = lean_array_get_size(v___x_3979_);
v___x_3982_ = lean_nat_dec_lt(v___x_3980_, v___x_3981_);
if (v___x_3982_ == 0)
{
v_a_3971_ = v_b_3967_;
goto v___jp_3970_;
}
else
{
uint8_t v___x_3983_; 
v___x_3983_ = lean_nat_dec_le(v___x_3981_, v___x_3981_);
if (v___x_3983_ == 0)
{
if (v___x_3982_ == 0)
{
v_a_3971_ = v_b_3967_;
goto v___jp_3970_;
}
else
{
size_t v___x_3984_; size_t v___x_3985_; lean_object* v___x_3986_; 
v___x_3984_ = ((size_t)0ULL);
v___x_3985_ = lean_usize_of_nat(v___x_3981_);
v___x_3986_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg(v___x_3979_, v___x_3984_, v___x_3985_, v_b_3967_);
v___y_3976_ = v___x_3986_;
goto v___jp_3975_;
}
}
else
{
size_t v___x_3987_; size_t v___x_3988_; lean_object* v___x_3989_; 
v___x_3987_ = ((size_t)0ULL);
v___x_3988_ = lean_usize_of_nat(v___x_3981_);
v___x_3989_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg(v___x_3979_, v___x_3987_, v___x_3988_, v_b_3967_);
v___y_3976_ = v___x_3989_;
goto v___jp_3975_;
}
}
}
else
{
lean_object* v___x_3990_; 
v___x_3990_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3990_, 0, v_b_3967_);
return v___x_3990_;
}
v___jp_3970_:
{
size_t v___x_3972_; size_t v___x_3973_; 
v___x_3972_ = ((size_t)1ULL);
v___x_3973_ = lean_usize_add(v_i_3965_, v___x_3972_);
v_i_3965_ = v___x_3973_;
v_b_3967_ = v_a_3971_;
goto _start;
}
v___jp_3975_:
{
if (lean_obj_tag(v___y_3976_) == 0)
{
lean_object* v_a_3977_; 
v_a_3977_ = lean_ctor_get(v___y_3976_, 0);
lean_inc(v_a_3977_);
lean_dec_ref_known(v___y_3976_, 1);
v_a_3971_ = v_a_3977_;
goto v___jp_3970_;
}
else
{
return v___y_3976_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__1___boxed(lean_object* v_as_3991_, lean_object* v_i_3992_, lean_object* v_stop_3993_, lean_object* v_b_3994_, lean_object* v___y_3995_, lean_object* v___y_3996_){
_start:
{
size_t v_i_boxed_3997_; size_t v_stop_boxed_3998_; lean_object* v_res_3999_; 
v_i_boxed_3997_ = lean_unbox_usize(v_i_3992_);
lean_dec(v_i_3992_);
v_stop_boxed_3998_ = lean_unbox_usize(v_stop_3993_);
lean_dec(v_stop_3993_);
v_res_3999_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__1(v_as_3991_, v_i_boxed_3997_, v_stop_boxed_3998_, v_b_3994_, v___y_3995_);
lean_dec_ref(v___y_3995_);
lean_dec_ref(v_as_3991_);
return v_res_3999_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_AttributeExtension_addImported(lean_object* v_es_4000_, lean_object* v_a_4001_){
_start:
{
lean_object* v_a_4004_; lean_object* v___y_4009_; lean_object* v___x_4019_; lean_object* v___x_4020_; lean_object* v___x_4021_; lean_object* v___x_4022_; uint8_t v___x_4023_; 
v___x_4019_ = l_Lean_attributeMapRef;
v___x_4020_ = lean_st_ref_get(v___x_4019_);
v___x_4021_ = lean_unsigned_to_nat(0u);
v___x_4022_ = lean_array_get_size(v_es_4000_);
v___x_4023_ = lean_nat_dec_lt(v___x_4021_, v___x_4022_);
if (v___x_4023_ == 0)
{
v_a_4004_ = v___x_4020_;
goto v___jp_4003_;
}
else
{
uint8_t v___x_4024_; 
v___x_4024_ = lean_nat_dec_le(v___x_4022_, v___x_4022_);
if (v___x_4024_ == 0)
{
if (v___x_4023_ == 0)
{
v_a_4004_ = v___x_4020_;
goto v___jp_4003_;
}
else
{
size_t v___x_4025_; size_t v___x_4026_; lean_object* v___x_4027_; 
v___x_4025_ = ((size_t)0ULL);
v___x_4026_ = lean_usize_of_nat(v___x_4022_);
v___x_4027_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__1(v_es_4000_, v___x_4025_, v___x_4026_, v___x_4020_, v_a_4001_);
v___y_4009_ = v___x_4027_;
goto v___jp_4008_;
}
}
else
{
size_t v___x_4028_; size_t v___x_4029_; lean_object* v___x_4030_; 
v___x_4028_ = ((size_t)0ULL);
v___x_4029_ = lean_usize_of_nat(v___x_4022_);
v___x_4030_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__1(v_es_4000_, v___x_4028_, v___x_4029_, v___x_4020_, v_a_4001_);
v___y_4009_ = v___x_4030_;
goto v___jp_4008_;
}
}
v___jp_4003_:
{
lean_object* v___x_4005_; lean_object* v___x_4006_; lean_object* v___x_4007_; 
v___x_4005_ = lean_box(0);
v___x_4006_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4006_, 0, v___x_4005_);
lean_ctor_set(v___x_4006_, 1, v_a_4004_);
v___x_4007_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4007_, 0, v___x_4006_);
return v___x_4007_;
}
v___jp_4008_:
{
if (lean_obj_tag(v___y_4009_) == 0)
{
lean_object* v_a_4010_; 
v_a_4010_ = lean_ctor_get(v___y_4009_, 0);
lean_inc(v_a_4010_);
lean_dec_ref_known(v___y_4009_, 1);
v_a_4004_ = v_a_4010_;
goto v___jp_4003_;
}
else
{
lean_object* v_a_4011_; lean_object* v___x_4013_; uint8_t v_isShared_4014_; uint8_t v_isSharedCheck_4018_; 
v_a_4011_ = lean_ctor_get(v___y_4009_, 0);
v_isSharedCheck_4018_ = !lean_is_exclusive(v___y_4009_);
if (v_isSharedCheck_4018_ == 0)
{
v___x_4013_ = v___y_4009_;
v_isShared_4014_ = v_isSharedCheck_4018_;
goto v_resetjp_4012_;
}
else
{
lean_inc(v_a_4011_);
lean_dec(v___y_4009_);
v___x_4013_ = lean_box(0);
v_isShared_4014_ = v_isSharedCheck_4018_;
goto v_resetjp_4012_;
}
v_resetjp_4012_:
{
lean_object* v___x_4016_; 
if (v_isShared_4014_ == 0)
{
v___x_4016_ = v___x_4013_;
goto v_reusejp_4015_;
}
else
{
lean_object* v_reuseFailAlloc_4017_; 
v_reuseFailAlloc_4017_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4017_, 0, v_a_4011_);
v___x_4016_ = v_reuseFailAlloc_4017_;
goto v_reusejp_4015_;
}
v_reusejp_4015_:
{
return v___x_4016_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_AttributeExtension_addImported___boxed(lean_object* v_es_4031_, lean_object* v_a_4032_, lean_object* v_a_4033_){
_start:
{
lean_object* v_res_4034_; 
v_res_4034_ = l___private_Lean_Attributes_0__Lean_AttributeExtension_addImported(v_es_4031_, v_a_4032_);
lean_dec_ref(v_a_4032_);
lean_dec_ref(v_es_4031_);
return v_res_4034_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0(lean_object* v_as_4035_, size_t v_i_4036_, size_t v_stop_4037_, lean_object* v_b_4038_, lean_object* v___y_4039_){
_start:
{
lean_object* v___x_4041_; 
v___x_4041_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg(v_as_4035_, v_i_4036_, v_stop_4037_, v_b_4038_);
return v___x_4041_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___boxed(lean_object* v_as_4042_, lean_object* v_i_4043_, lean_object* v_stop_4044_, lean_object* v_b_4045_, lean_object* v___y_4046_, lean_object* v___y_4047_){
_start:
{
size_t v_i_boxed_4048_; size_t v_stop_boxed_4049_; lean_object* v_res_4050_; 
v_i_boxed_4048_ = lean_unbox_usize(v_i_4043_);
lean_dec(v_i_4043_);
v_stop_boxed_4049_ = lean_unbox_usize(v_stop_4044_);
lean_dec(v_stop_4044_);
v_res_4050_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0(v_as_4042_, v_i_boxed_4048_, v_stop_boxed_4049_, v_b_4045_, v___y_4046_);
lean_dec_ref(v___y_4046_);
lean_dec_ref(v_as_4042_);
return v_res_4050_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_addAttrEntry(lean_object* v_s_4051_, lean_object* v_e_4052_){
_start:
{
lean_object* v_snd_4053_; lean_object* v_toAttributeImplCore_4054_; lean_object* v_fst_4055_; lean_object* v___x_4057_; uint8_t v_isShared_4058_; uint8_t v_isSharedCheck_4073_; 
v_snd_4053_ = lean_ctor_get(v_e_4052_, 1);
lean_inc(v_snd_4053_);
v_toAttributeImplCore_4054_ = lean_ctor_get(v_snd_4053_, 0);
v_fst_4055_ = lean_ctor_get(v_e_4052_, 0);
v_isSharedCheck_4073_ = !lean_is_exclusive(v_e_4052_);
if (v_isSharedCheck_4073_ == 0)
{
lean_object* v_unused_4074_; 
v_unused_4074_ = lean_ctor_get(v_e_4052_, 1);
lean_dec(v_unused_4074_);
v___x_4057_ = v_e_4052_;
v_isShared_4058_ = v_isSharedCheck_4073_;
goto v_resetjp_4056_;
}
else
{
lean_inc(v_fst_4055_);
lean_dec(v_e_4052_);
v___x_4057_ = lean_box(0);
v_isShared_4058_ = v_isSharedCheck_4073_;
goto v_resetjp_4056_;
}
v_resetjp_4056_:
{
lean_object* v_newEntries_4059_; lean_object* v_map_4060_; lean_object* v___x_4062_; uint8_t v_isShared_4063_; uint8_t v_isSharedCheck_4072_; 
v_newEntries_4059_ = lean_ctor_get(v_s_4051_, 0);
v_map_4060_ = lean_ctor_get(v_s_4051_, 1);
v_isSharedCheck_4072_ = !lean_is_exclusive(v_s_4051_);
if (v_isSharedCheck_4072_ == 0)
{
v___x_4062_ = v_s_4051_;
v_isShared_4063_ = v_isSharedCheck_4072_;
goto v_resetjp_4061_;
}
else
{
lean_inc(v_map_4060_);
lean_inc(v_newEntries_4059_);
lean_dec(v_s_4051_);
v___x_4062_ = lean_box(0);
v_isShared_4063_ = v_isSharedCheck_4072_;
goto v_resetjp_4061_;
}
v_resetjp_4061_:
{
lean_object* v_name_4064_; lean_object* v___x_4066_; 
v_name_4064_ = lean_ctor_get(v_toAttributeImplCore_4054_, 1);
lean_inc(v_name_4064_);
if (v_isShared_4058_ == 0)
{
lean_ctor_set_tag(v___x_4057_, 1);
lean_ctor_set(v___x_4057_, 1, v_newEntries_4059_);
v___x_4066_ = v___x_4057_;
goto v_reusejp_4065_;
}
else
{
lean_object* v_reuseFailAlloc_4071_; 
v_reuseFailAlloc_4071_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4071_, 0, v_fst_4055_);
lean_ctor_set(v_reuseFailAlloc_4071_, 1, v_newEntries_4059_);
v___x_4066_ = v_reuseFailAlloc_4071_;
goto v_reusejp_4065_;
}
v_reusejp_4065_:
{
lean_object* v___x_4067_; lean_object* v___x_4069_; 
v___x_4067_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1___redArg(v_map_4060_, v_name_4064_, v_snd_4053_);
if (v_isShared_4063_ == 0)
{
lean_ctor_set(v___x_4062_, 1, v___x_4067_);
lean_ctor_set(v___x_4062_, 0, v___x_4066_);
v___x_4069_ = v___x_4062_;
goto v_reusejp_4068_;
}
else
{
lean_object* v_reuseFailAlloc_4070_; 
v_reuseFailAlloc_4070_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4070_, 0, v___x_4066_);
lean_ctor_set(v_reuseFailAlloc_4070_, 1, v___x_4067_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn___lam__0_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(lean_object* v_x_4075_, lean_object* v_s_4076_){
_start:
{
lean_object* v_newEntries_4077_; lean_object* v___x_4078_; lean_object* v___x_4079_; lean_object* v___x_4080_; 
v_newEntries_4077_ = lean_ctor_get(v_s_4076_, 0);
lean_inc(v_newEntries_4077_);
lean_dec_ref(v_s_4076_);
v___x_4078_ = l_List_reverse___redArg(v_newEntries_4077_);
v___x_4079_ = lean_array_mk(v___x_4078_);
lean_inc_ref_n(v___x_4079_, 2);
v___x_4080_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4080_, 0, v___x_4079_);
lean_ctor_set(v___x_4080_, 1, v___x_4079_);
lean_ctor_set(v___x_4080_, 2, v___x_4079_);
return v___x_4080_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn___lam__0_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2____boxed(lean_object* v_x_4081_, lean_object* v_s_4082_){
_start:
{
lean_object* v_res_4083_; 
v_res_4083_ = l___private_Lean_Attributes_0__Lean_initFn___lam__0_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(v_x_4081_, v_s_4082_);
lean_dec_ref(v_x_4081_);
return v_res_4083_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn___lam__1_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(lean_object* v_s_4084_){
_start:
{
lean_object* v_newEntries_4085_; lean_object* v___x_4087_; uint8_t v_isShared_4088_; uint8_t v_isSharedCheck_4096_; 
v_newEntries_4085_ = lean_ctor_get(v_s_4084_, 0);
v_isSharedCheck_4096_ = !lean_is_exclusive(v_s_4084_);
if (v_isSharedCheck_4096_ == 0)
{
lean_object* v_unused_4097_; 
v_unused_4097_ = lean_ctor_get(v_s_4084_, 1);
lean_dec(v_unused_4097_);
v___x_4087_ = v_s_4084_;
v_isShared_4088_ = v_isSharedCheck_4096_;
goto v_resetjp_4086_;
}
else
{
lean_inc(v_newEntries_4085_);
lean_dec(v_s_4084_);
v___x_4087_ = lean_box(0);
v_isShared_4088_ = v_isSharedCheck_4096_;
goto v_resetjp_4086_;
}
v_resetjp_4086_:
{
lean_object* v___x_4089_; lean_object* v___x_4090_; lean_object* v___x_4091_; lean_object* v___x_4092_; lean_object* v___x_4094_; 
v___x_4089_ = ((lean_object*)(l_Lean_registerTagAttribute___lam__2___closed__4));
v___x_4090_ = l_List_lengthTR___redArg(v_newEntries_4085_);
lean_dec(v_newEntries_4085_);
v___x_4091_ = l_Nat_reprFast(v___x_4090_);
v___x_4092_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4092_, 0, v___x_4091_);
if (v_isShared_4088_ == 0)
{
lean_ctor_set_tag(v___x_4087_, 5);
lean_ctor_set(v___x_4087_, 1, v___x_4092_);
lean_ctor_set(v___x_4087_, 0, v___x_4089_);
v___x_4094_ = v___x_4087_;
goto v_reusejp_4093_;
}
else
{
lean_object* v_reuseFailAlloc_4095_; 
v_reuseFailAlloc_4095_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4095_, 0, v___x_4089_);
lean_ctor_set(v_reuseFailAlloc_4095_, 1, v___x_4092_);
v___x_4094_ = v_reuseFailAlloc_4095_;
goto v_reusejp_4093_;
}
v_reusejp_4093_:
{
return v___x_4094_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn___lam__2_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(lean_object* v_s_4098_){
_start:
{
lean_object* v_newEntries_4099_; lean_object* v___x_4100_; lean_object* v___x_4101_; 
v_newEntries_4099_ = lean_ctor_get(v_s_4098_, 0);
lean_inc(v_newEntries_4099_);
lean_dec_ref(v_s_4098_);
v___x_4100_ = l_List_reverse___redArg(v_newEntries_4099_);
v___x_4101_ = lean_array_mk(v___x_4100_);
return v___x_4101_;
}
}
static lean_object* _init_l___private_Lean_Attributes_0__Lean_initFn___closed__7_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4111_; lean_object* v___x_4112_; lean_object* v___f_4113_; lean_object* v___f_4114_; lean_object* v___x_4115_; lean_object* v___x_4116_; lean_object* v___x_4117_; lean_object* v___x_4118_; lean_object* v___x_4119_; 
v___x_4111_ = lean_box(0);
v___x_4112_ = lean_box(2);
v___f_4113_ = ((lean_object*)(l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___f_4114_ = ((lean_object*)(l___private_Lean_Attributes_0__Lean_initFn___closed__0_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___x_4115_ = ((lean_object*)(l___private_Lean_Attributes_0__Lean_initFn___closed__6_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___x_4116_ = ((lean_object*)(l___private_Lean_Attributes_0__Lean_initFn___closed__5_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___x_4117_ = lean_alloc_closure((void*)(l___private_Lean_Attributes_0__Lean_AttributeExtension_mkInitial___boxed), 1, 0);
v___x_4118_ = ((lean_object*)(l___private_Lean_Attributes_0__Lean_initFn___closed__4_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___x_4119_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_4119_, 0, v___x_4118_);
lean_ctor_set(v___x_4119_, 1, v___x_4117_);
lean_ctor_set(v___x_4119_, 2, v___x_4116_);
lean_ctor_set(v___x_4119_, 3, v___x_4115_);
lean_ctor_set(v___x_4119_, 4, v___f_4114_);
lean_ctor_set(v___x_4119_, 5, v___f_4113_);
lean_ctor_set(v___x_4119_, 6, v___x_4112_);
lean_ctor_set(v___x_4119_, 7, v___x_4111_);
return v___x_4119_;
}
}
static lean_object* _init_l___private_Lean_Attributes_0__Lean_initFn___closed__8_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_4120_; lean_object* v___x_4121_; lean_object* v___x_4122_; 
v___f_4120_ = ((lean_object*)(l___private_Lean_Attributes_0__Lean_initFn___closed__2_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___x_4121_ = lean_obj_once(&l___private_Lean_Attributes_0__Lean_initFn___closed__7_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_, &l___private_Lean_Attributes_0__Lean_initFn___closed__7_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2__once, _init_l___private_Lean_Attributes_0__Lean_initFn___closed__7_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_);
v___x_4122_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4122_, 0, v___x_4121_);
lean_ctor_set(v___x_4122_, 1, v___f_4120_);
return v___x_4122_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4124_; lean_object* v___x_4125_; 
v___x_4124_ = lean_obj_once(&l___private_Lean_Attributes_0__Lean_initFn___closed__8_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_, &l___private_Lean_Attributes_0__Lean_initFn___closed__8_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2__once, _init_l___private_Lean_Attributes_0__Lean_initFn___closed__8_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_);
v___x_4125_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_4124_);
return v___x_4125_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2____boxed(lean_object* v_a_4126_){
_start:
{
lean_object* v_res_4127_; 
v_res_4127_ = l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_();
return v_res_4127_;
}
}
LEAN_EXPORT lean_object* l_Lean_isBuiltinAttribute(lean_object* v_n_4128_){
_start:
{
lean_object* v___x_4130_; lean_object* v___x_4131_; uint8_t v___x_4132_; lean_object* v___x_4133_; lean_object* v___x_4134_; 
v___x_4130_ = l_Lean_attributeMapRef;
v___x_4131_ = lean_st_ref_get(v___x_4130_);
v___x_4132_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(v___x_4131_, v_n_4128_);
lean_dec(v___x_4131_);
v___x_4133_ = lean_box(v___x_4132_);
v___x_4134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4134_, 0, v___x_4133_);
return v___x_4134_;
}
}
LEAN_EXPORT lean_object* l_Lean_isBuiltinAttribute___boxed(lean_object* v_n_4135_, lean_object* v_a_4136_){
_start:
{
lean_object* v_res_4137_; 
v_res_4137_ = l_Lean_isBuiltinAttribute(v_n_4135_);
lean_dec(v_n_4135_);
return v_res_4137_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_getBuiltinAttributeNames_spec__0(lean_object* v_x_4138_, lean_object* v_x_4139_){
_start:
{
if (lean_obj_tag(v_x_4139_) == 0)
{
return v_x_4138_;
}
else
{
lean_object* v_key_4140_; lean_object* v_tail_4141_; lean_object* v___x_4142_; 
v_key_4140_ = lean_ctor_get(v_x_4139_, 0);
v_tail_4141_ = lean_ctor_get(v_x_4139_, 2);
lean_inc(v_key_4140_);
v___x_4142_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4142_, 0, v_key_4140_);
lean_ctor_set(v___x_4142_, 1, v_x_4138_);
v_x_4138_ = v___x_4142_;
v_x_4139_ = v_tail_4141_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_getBuiltinAttributeNames_spec__0___boxed(lean_object* v_x_4144_, lean_object* v_x_4145_){
_start:
{
lean_object* v_res_4146_; 
v_res_4146_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_getBuiltinAttributeNames_spec__0(v_x_4144_, v_x_4145_);
lean_dec(v_x_4145_);
return v_res_4146_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1(lean_object* v_as_4147_, size_t v_i_4148_, size_t v_stop_4149_, lean_object* v_b_4150_){
_start:
{
uint8_t v___x_4151_; 
v___x_4151_ = lean_usize_dec_eq(v_i_4148_, v_stop_4149_);
if (v___x_4151_ == 0)
{
lean_object* v___x_4152_; lean_object* v___x_4153_; size_t v___x_4154_; size_t v___x_4155_; 
v___x_4152_ = lean_array_uget_borrowed(v_as_4147_, v_i_4148_);
v___x_4153_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_getBuiltinAttributeNames_spec__0(v_b_4150_, v___x_4152_);
v___x_4154_ = ((size_t)1ULL);
v___x_4155_ = lean_usize_add(v_i_4148_, v___x_4154_);
v_i_4148_ = v___x_4155_;
v_b_4150_ = v___x_4153_;
goto _start;
}
else
{
return v_b_4150_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1___boxed(lean_object* v_as_4157_, lean_object* v_i_4158_, lean_object* v_stop_4159_, lean_object* v_b_4160_){
_start:
{
size_t v_i_boxed_4161_; size_t v_stop_boxed_4162_; lean_object* v_res_4163_; 
v_i_boxed_4161_ = lean_unbox_usize(v_i_4158_);
lean_dec(v_i_4158_);
v_stop_boxed_4162_ = lean_unbox_usize(v_stop_4159_);
lean_dec(v_stop_4159_);
v_res_4163_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1(v_as_4157_, v_i_boxed_4161_, v_stop_boxed_4162_, v_b_4160_);
lean_dec_ref(v_as_4157_);
return v_res_4163_;
}
}
LEAN_EXPORT lean_object* l_Lean_getBuiltinAttributeNames(){
_start:
{
lean_object* v___x_4165_; lean_object* v___x_4166_; lean_object* v_buckets_4167_; lean_object* v___x_4168_; lean_object* v___x_4169_; lean_object* v___x_4170_; uint8_t v___x_4171_; 
v___x_4165_ = l_Lean_attributeMapRef;
v___x_4166_ = lean_st_ref_get(v___x_4165_);
v_buckets_4167_ = lean_ctor_get(v___x_4166_, 1);
lean_inc_ref(v_buckets_4167_);
lean_dec(v___x_4166_);
v___x_4168_ = lean_box(0);
v___x_4169_ = lean_unsigned_to_nat(0u);
v___x_4170_ = lean_array_get_size(v_buckets_4167_);
v___x_4171_ = lean_nat_dec_lt(v___x_4169_, v___x_4170_);
if (v___x_4171_ == 0)
{
lean_object* v___x_4172_; 
lean_dec_ref(v_buckets_4167_);
v___x_4172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4172_, 0, v___x_4168_);
return v___x_4172_;
}
else
{
uint8_t v___x_4173_; 
v___x_4173_ = lean_nat_dec_le(v___x_4170_, v___x_4170_);
if (v___x_4173_ == 0)
{
if (v___x_4171_ == 0)
{
lean_object* v___x_4174_; 
lean_dec_ref(v_buckets_4167_);
v___x_4174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4174_, 0, v___x_4168_);
return v___x_4174_;
}
else
{
size_t v___x_4175_; size_t v___x_4176_; lean_object* v___x_4177_; lean_object* v___x_4178_; 
v___x_4175_ = ((size_t)0ULL);
v___x_4176_ = lean_usize_of_nat(v___x_4170_);
v___x_4177_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1(v_buckets_4167_, v___x_4175_, v___x_4176_, v___x_4168_);
lean_dec_ref(v_buckets_4167_);
v___x_4178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4178_, 0, v___x_4177_);
return v___x_4178_;
}
}
else
{
size_t v___x_4179_; size_t v___x_4180_; lean_object* v___x_4181_; lean_object* v___x_4182_; 
v___x_4179_ = ((size_t)0ULL);
v___x_4180_ = lean_usize_of_nat(v___x_4170_);
v___x_4181_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1(v_buckets_4167_, v___x_4179_, v___x_4180_, v___x_4168_);
lean_dec_ref(v_buckets_4167_);
v___x_4182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4182_, 0, v___x_4181_);
return v___x_4182_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getBuiltinAttributeNames___boxed(lean_object* v_a_4183_){
_start:
{
lean_object* v_res_4184_; 
v_res_4184_ = l_Lean_getBuiltinAttributeNames();
return v_res_4184_;
}
}
LEAN_EXPORT lean_object* l_Lean_getBuiltinAttributeImpl(lean_object* v_attrName_4186_){
_start:
{
lean_object* v___x_4188_; lean_object* v___x_4189_; lean_object* v___x_4190_; 
v___x_4188_ = l_Lean_attributeMapRef;
v___x_4189_ = lean_st_ref_get(v___x_4188_);
v___x_4190_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(v___x_4189_, v_attrName_4186_);
lean_dec(v___x_4189_);
if (lean_obj_tag(v___x_4190_) == 0)
{
lean_object* v___x_4191_; uint8_t v___x_4192_; lean_object* v___x_4193_; lean_object* v___x_4194_; lean_object* v___x_4195_; lean_object* v___x_4196_; lean_object* v___x_4197_; lean_object* v___x_4198_; 
v___x_4191_ = ((lean_object*)(l_Lean_getBuiltinAttributeImpl___closed__0));
v___x_4192_ = 1;
v___x_4193_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_attrName_4186_, v___x_4192_);
v___x_4194_ = lean_string_append(v___x_4191_, v___x_4193_);
lean_dec_ref(v___x_4193_);
v___x_4195_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__4));
v___x_4196_ = lean_string_append(v___x_4194_, v___x_4195_);
v___x_4197_ = lean_mk_io_user_error(v___x_4196_);
v___x_4198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4198_, 0, v___x_4197_);
return v___x_4198_;
}
else
{
lean_object* v_val_4199_; lean_object* v___x_4201_; uint8_t v_isShared_4202_; uint8_t v_isSharedCheck_4206_; 
lean_dec(v_attrName_4186_);
v_val_4199_ = lean_ctor_get(v___x_4190_, 0);
v_isSharedCheck_4206_ = !lean_is_exclusive(v___x_4190_);
if (v_isSharedCheck_4206_ == 0)
{
v___x_4201_ = v___x_4190_;
v_isShared_4202_ = v_isSharedCheck_4206_;
goto v_resetjp_4200_;
}
else
{
lean_inc(v_val_4199_);
lean_dec(v___x_4190_);
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
lean_ctor_set(v_reuseFailAlloc_4205_, 0, v_val_4199_);
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
LEAN_EXPORT lean_object* l_Lean_getBuiltinAttributeImpl___boxed(lean_object* v_attrName_4207_, lean_object* v_a_4208_){
_start:
{
lean_object* v_res_4209_; 
v_res_4209_ = l_Lean_getBuiltinAttributeImpl(v_attrName_4207_);
return v_res_4209_;
}
}
LEAN_EXPORT uint8_t l_Lean_isAttribute(lean_object* v_env_4210_, lean_object* v_attrName_4211_){
_start:
{
lean_object* v___x_4212_; lean_object* v_toEnvExtension_4213_; lean_object* v_asyncMode_4214_; lean_object* v___x_4215_; lean_object* v___x_4216_; lean_object* v___x_4217_; lean_object* v_map_4218_; uint8_t v___x_4219_; 
v___x_4212_ = l_Lean_attributeExtension;
v_toEnvExtension_4213_ = lean_ctor_get(v___x_4212_, 0);
v_asyncMode_4214_ = lean_ctor_get(v_toEnvExtension_4213_, 2);
v___x_4215_ = l_Lean_instInhabitedAttributeExtensionState_default;
v___x_4216_ = lean_box(0);
v___x_4217_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_4215_, v___x_4212_, v_env_4210_, v_asyncMode_4214_, v___x_4216_);
v_map_4218_ = lean_ctor_get(v___x_4217_, 1);
lean_inc_ref(v_map_4218_);
lean_dec(v___x_4217_);
v___x_4219_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(v_map_4218_, v_attrName_4211_);
lean_dec_ref(v_map_4218_);
return v___x_4219_;
}
}
LEAN_EXPORT lean_object* l_Lean_isAttribute___boxed(lean_object* v_env_4220_, lean_object* v_attrName_4221_){
_start:
{
uint8_t v_res_4222_; lean_object* v_r_4223_; 
v_res_4222_ = l_Lean_isAttribute(v_env_4220_, v_attrName_4221_);
lean_dec(v_attrName_4221_);
v_r_4223_ = lean_box(v_res_4222_);
return v_r_4223_;
}
}
LEAN_EXPORT lean_object* l_Lean_getAttributeNames(lean_object* v_env_4224_){
_start:
{
lean_object* v___x_4225_; lean_object* v_toEnvExtension_4226_; lean_object* v_asyncMode_4227_; lean_object* v___x_4228_; lean_object* v___x_4229_; lean_object* v___x_4230_; lean_object* v_map_4231_; lean_object* v_buckets_4232_; lean_object* v___x_4233_; lean_object* v___x_4234_; lean_object* v___x_4235_; uint8_t v___x_4236_; 
v___x_4225_ = l_Lean_attributeExtension;
v_toEnvExtension_4226_ = lean_ctor_get(v___x_4225_, 0);
v_asyncMode_4227_ = lean_ctor_get(v_toEnvExtension_4226_, 2);
v___x_4228_ = l_Lean_instInhabitedAttributeExtensionState_default;
v___x_4229_ = lean_box(0);
v___x_4230_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_4228_, v___x_4225_, v_env_4224_, v_asyncMode_4227_, v___x_4229_);
v_map_4231_ = lean_ctor_get(v___x_4230_, 1);
lean_inc_ref(v_map_4231_);
lean_dec(v___x_4230_);
v_buckets_4232_ = lean_ctor_get(v_map_4231_, 1);
lean_inc_ref(v_buckets_4232_);
lean_dec_ref(v_map_4231_);
v___x_4233_ = lean_box(0);
v___x_4234_ = lean_unsigned_to_nat(0u);
v___x_4235_ = lean_array_get_size(v_buckets_4232_);
v___x_4236_ = lean_nat_dec_lt(v___x_4234_, v___x_4235_);
if (v___x_4236_ == 0)
{
lean_dec_ref(v_buckets_4232_);
return v___x_4233_;
}
else
{
uint8_t v___x_4237_; 
v___x_4237_ = lean_nat_dec_le(v___x_4235_, v___x_4235_);
if (v___x_4237_ == 0)
{
if (v___x_4236_ == 0)
{
lean_dec_ref(v_buckets_4232_);
return v___x_4233_;
}
else
{
size_t v___x_4238_; size_t v___x_4239_; lean_object* v___x_4240_; 
v___x_4238_ = ((size_t)0ULL);
v___x_4239_ = lean_usize_of_nat(v___x_4235_);
v___x_4240_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1(v_buckets_4232_, v___x_4238_, v___x_4239_, v___x_4233_);
lean_dec_ref(v_buckets_4232_);
return v___x_4240_;
}
}
else
{
size_t v___x_4241_; size_t v___x_4242_; lean_object* v___x_4243_; 
v___x_4241_ = ((size_t)0ULL);
v___x_4242_ = lean_usize_of_nat(v___x_4235_);
v___x_4243_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1(v_buckets_4232_, v___x_4241_, v___x_4242_, v___x_4233_);
lean_dec_ref(v_buckets_4232_);
return v___x_4243_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getAttributeImpl(lean_object* v_env_4244_, lean_object* v_attrName_4245_){
_start:
{
lean_object* v___x_4246_; lean_object* v_toEnvExtension_4247_; lean_object* v_asyncMode_4248_; lean_object* v___x_4249_; lean_object* v___x_4250_; lean_object* v___x_4251_; lean_object* v_map_4252_; lean_object* v___x_4253_; 
v___x_4246_ = l_Lean_attributeExtension;
v_toEnvExtension_4247_ = lean_ctor_get(v___x_4246_, 0);
v_asyncMode_4248_ = lean_ctor_get(v_toEnvExtension_4247_, 2);
v___x_4249_ = l_Lean_instInhabitedAttributeExtensionState_default;
v___x_4250_ = lean_box(0);
v___x_4251_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_4249_, v___x_4246_, v_env_4244_, v_asyncMode_4248_, v___x_4250_);
v_map_4252_ = lean_ctor_get(v___x_4251_, 1);
lean_inc_ref(v_map_4252_);
lean_dec(v___x_4251_);
v___x_4253_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(v_map_4252_, v_attrName_4245_);
lean_dec_ref(v_map_4252_);
if (lean_obj_tag(v___x_4253_) == 0)
{
lean_object* v___x_4254_; uint8_t v___x_4255_; lean_object* v___x_4256_; lean_object* v___x_4257_; lean_object* v___x_4258_; lean_object* v___x_4259_; lean_object* v___x_4260_; 
v___x_4254_ = ((lean_object*)(l_Lean_getBuiltinAttributeImpl___closed__0));
v___x_4255_ = 1;
v___x_4256_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_attrName_4245_, v___x_4255_);
v___x_4257_ = lean_string_append(v___x_4254_, v___x_4256_);
lean_dec_ref(v___x_4256_);
v___x_4258_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__4));
v___x_4259_ = lean_string_append(v___x_4257_, v___x_4258_);
v___x_4260_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4260_, 0, v___x_4259_);
return v___x_4260_;
}
else
{
lean_object* v_val_4261_; lean_object* v___x_4263_; uint8_t v_isShared_4264_; uint8_t v_isSharedCheck_4268_; 
lean_dec(v_attrName_4245_);
v_val_4261_ = lean_ctor_get(v___x_4253_, 0);
v_isSharedCheck_4268_ = !lean_is_exclusive(v___x_4253_);
if (v_isSharedCheck_4268_ == 0)
{
v___x_4263_ = v___x_4253_;
v_isShared_4264_ = v_isSharedCheck_4268_;
goto v_resetjp_4262_;
}
else
{
lean_inc(v_val_4261_);
lean_dec(v___x_4253_);
v___x_4263_ = lean_box(0);
v_isShared_4264_ = v_isSharedCheck_4268_;
goto v_resetjp_4262_;
}
v_resetjp_4262_:
{
lean_object* v___x_4266_; 
if (v_isShared_4264_ == 0)
{
v___x_4266_ = v___x_4263_;
goto v_reusejp_4265_;
}
else
{
lean_object* v_reuseFailAlloc_4267_; 
v_reuseFailAlloc_4267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4267_, 0, v_val_4261_);
v___x_4266_ = v_reuseFailAlloc_4267_;
goto v_reusejp_4265_;
}
v_reusejp_4265_:
{
return v___x_4266_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerAttributeOfBuilder(lean_object* v_env_4269_, lean_object* v_builderId_4270_, lean_object* v_ref_4271_, lean_object* v_args_4272_){
_start:
{
lean_object* v_entry_4274_; lean_object* v___x_4275_; 
v_entry_4274_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_entry_4274_, 0, v_builderId_4270_);
lean_ctor_set(v_entry_4274_, 1, v_ref_4271_);
lean_ctor_set(v_entry_4274_, 2, v_args_4272_);
lean_inc_ref(v_entry_4274_);
v___x_4275_ = l_Lean_mkAttributeImplOfEntry(v_entry_4274_);
if (lean_obj_tag(v___x_4275_) == 0)
{
lean_object* v_a_4276_; lean_object* v___x_4278_; uint8_t v_isShared_4279_; uint8_t v_isSharedCheck_4301_; 
v_a_4276_ = lean_ctor_get(v___x_4275_, 0);
v_isSharedCheck_4301_ = !lean_is_exclusive(v___x_4275_);
if (v_isSharedCheck_4301_ == 0)
{
v___x_4278_ = v___x_4275_;
v_isShared_4279_ = v_isSharedCheck_4301_;
goto v_resetjp_4277_;
}
else
{
lean_inc(v_a_4276_);
lean_dec(v___x_4275_);
v___x_4278_ = lean_box(0);
v_isShared_4279_ = v_isSharedCheck_4301_;
goto v_resetjp_4277_;
}
v_resetjp_4277_:
{
lean_object* v_toAttributeImplCore_4280_; lean_object* v_name_4281_; uint8_t v___x_4282_; 
v_toAttributeImplCore_4280_ = lean_ctor_get(v_a_4276_, 0);
v_name_4281_ = lean_ctor_get(v_toAttributeImplCore_4280_, 1);
lean_inc_ref(v_env_4269_);
v___x_4282_ = l_Lean_isAttribute(v_env_4269_, v_name_4281_);
if (v___x_4282_ == 0)
{
lean_object* v___x_4283_; lean_object* v_toEnvExtension_4284_; lean_object* v_asyncMode_4285_; lean_object* v___x_4286_; lean_object* v___x_4287_; lean_object* v___x_4288_; lean_object* v___x_4290_; 
v___x_4283_ = l_Lean_attributeExtension;
v_toEnvExtension_4284_ = lean_ctor_get(v___x_4283_, 0);
v_asyncMode_4285_ = lean_ctor_get(v_toEnvExtension_4284_, 2);
v___x_4286_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4286_, 0, v_entry_4274_);
lean_ctor_set(v___x_4286_, 1, v_a_4276_);
v___x_4287_ = lean_box(0);
v___x_4288_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_4283_, v_env_4269_, v___x_4286_, v_asyncMode_4285_, v___x_4287_);
if (v_isShared_4279_ == 0)
{
lean_ctor_set(v___x_4278_, 0, v___x_4288_);
v___x_4290_ = v___x_4278_;
goto v_reusejp_4289_;
}
else
{
lean_object* v_reuseFailAlloc_4291_; 
v_reuseFailAlloc_4291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4291_, 0, v___x_4288_);
v___x_4290_ = v_reuseFailAlloc_4291_;
goto v_reusejp_4289_;
}
v_reusejp_4289_:
{
return v___x_4290_;
}
}
else
{
lean_object* v___x_4292_; lean_object* v___x_4293_; lean_object* v___x_4294_; lean_object* v___x_4295_; lean_object* v___x_4296_; lean_object* v___x_4297_; lean_object* v___x_4299_; 
lean_inc(v_name_4281_);
lean_dec(v_a_4276_);
lean_dec_ref_known(v_entry_4274_, 3);
lean_dec_ref(v_env_4269_);
v___x_4292_ = ((lean_object*)(l_Lean_registerBuiltinAttribute___closed__2));
v___x_4293_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_4281_, v___x_4282_);
v___x_4294_ = lean_string_append(v___x_4292_, v___x_4293_);
lean_dec_ref(v___x_4293_);
v___x_4295_ = ((lean_object*)(l_Lean_registerBuiltinAttribute___closed__3));
v___x_4296_ = lean_string_append(v___x_4294_, v___x_4295_);
v___x_4297_ = lean_mk_io_user_error(v___x_4296_);
if (v_isShared_4279_ == 0)
{
lean_ctor_set_tag(v___x_4278_, 1);
lean_ctor_set(v___x_4278_, 0, v___x_4297_);
v___x_4299_ = v___x_4278_;
goto v_reusejp_4298_;
}
else
{
lean_object* v_reuseFailAlloc_4300_; 
v_reuseFailAlloc_4300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4300_, 0, v___x_4297_);
v___x_4299_ = v_reuseFailAlloc_4300_;
goto v_reusejp_4298_;
}
v_reusejp_4298_:
{
return v___x_4299_;
}
}
}
}
else
{
lean_object* v_a_4302_; lean_object* v___x_4304_; uint8_t v_isShared_4305_; uint8_t v_isSharedCheck_4309_; 
lean_dec_ref_known(v_entry_4274_, 3);
lean_dec_ref(v_env_4269_);
v_a_4302_ = lean_ctor_get(v___x_4275_, 0);
v_isSharedCheck_4309_ = !lean_is_exclusive(v___x_4275_);
if (v_isSharedCheck_4309_ == 0)
{
v___x_4304_ = v___x_4275_;
v_isShared_4305_ = v_isSharedCheck_4309_;
goto v_resetjp_4303_;
}
else
{
lean_inc(v_a_4302_);
lean_dec(v___x_4275_);
v___x_4304_ = lean_box(0);
v_isShared_4305_ = v_isSharedCheck_4309_;
goto v_resetjp_4303_;
}
v_resetjp_4303_:
{
lean_object* v___x_4307_; 
if (v_isShared_4305_ == 0)
{
v___x_4307_ = v___x_4304_;
goto v_reusejp_4306_;
}
else
{
lean_object* v_reuseFailAlloc_4308_; 
v_reuseFailAlloc_4308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4308_, 0, v_a_4302_);
v___x_4307_ = v_reuseFailAlloc_4308_;
goto v_reusejp_4306_;
}
v_reusejp_4306_:
{
return v___x_4307_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerAttributeOfBuilder___boxed(lean_object* v_env_4310_, lean_object* v_builderId_4311_, lean_object* v_ref_4312_, lean_object* v_args_4313_, lean_object* v_a_4314_){
_start:
{
lean_object* v_res_4315_; 
v_res_4315_ = l_Lean_registerAttributeOfBuilder(v_env_4310_, v_builderId_4311_, v_ref_4312_, v_args_4313_);
return v_res_4315_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg(lean_object* v_x_4316_, lean_object* v___y_4317_, lean_object* v___y_4318_){
_start:
{
if (lean_obj_tag(v_x_4316_) == 0)
{
lean_object* v_a_4320_; lean_object* v___x_4321_; lean_object* v___x_4322_; 
v_a_4320_ = lean_ctor_get(v_x_4316_, 0);
lean_inc(v_a_4320_);
lean_dec_ref_known(v_x_4316_, 1);
v___x_4321_ = l_Lean_stringToMessageData(v_a_4320_);
v___x_4322_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_4321_, v___y_4317_, v___y_4318_);
return v___x_4322_;
}
else
{
lean_object* v_a_4323_; lean_object* v___x_4325_; uint8_t v_isShared_4326_; uint8_t v_isSharedCheck_4330_; 
v_a_4323_ = lean_ctor_get(v_x_4316_, 0);
v_isSharedCheck_4330_ = !lean_is_exclusive(v_x_4316_);
if (v_isSharedCheck_4330_ == 0)
{
v___x_4325_ = v_x_4316_;
v_isShared_4326_ = v_isSharedCheck_4330_;
goto v_resetjp_4324_;
}
else
{
lean_inc(v_a_4323_);
lean_dec(v_x_4316_);
v___x_4325_ = lean_box(0);
v_isShared_4326_ = v_isSharedCheck_4330_;
goto v_resetjp_4324_;
}
v_resetjp_4324_:
{
lean_object* v___x_4328_; 
if (v_isShared_4326_ == 0)
{
lean_ctor_set_tag(v___x_4325_, 0);
v___x_4328_ = v___x_4325_;
goto v_reusejp_4327_;
}
else
{
lean_object* v_reuseFailAlloc_4329_; 
v_reuseFailAlloc_4329_ = lean_alloc_ctor(0, 1, 0);
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
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg___boxed(lean_object* v_x_4331_, lean_object* v___y_4332_, lean_object* v___y_4333_, lean_object* v___y_4334_){
_start:
{
lean_object* v_res_4335_; 
v_res_4335_ = l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg(v_x_4331_, v___y_4332_, v___y_4333_);
lean_dec(v___y_4333_);
lean_dec_ref(v___y_4332_);
return v_res_4335_;
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_add(lean_object* v_declName_4336_, lean_object* v_attrName_4337_, lean_object* v_stx_4338_, uint8_t v_kind_4339_, lean_object* v_a_4340_, lean_object* v_a_4341_){
_start:
{
lean_object* v___x_4343_; lean_object* v_env_4344_; lean_object* v___x_4345_; lean_object* v___x_4346_; 
v___x_4343_ = lean_st_ref_get(v_a_4341_);
v_env_4344_ = lean_ctor_get(v___x_4343_, 0);
lean_inc_ref(v_env_4344_);
lean_dec(v___x_4343_);
v___x_4345_ = l_Lean_getAttributeImpl(v_env_4344_, v_attrName_4337_);
v___x_4346_ = l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg(v___x_4345_, v_a_4340_, v_a_4341_);
if (lean_obj_tag(v___x_4346_) == 0)
{
lean_object* v_a_4347_; lean_object* v_add_4348_; lean_object* v___x_4349_; lean_object* v___x_4350_; 
v_a_4347_ = lean_ctor_get(v___x_4346_, 0);
lean_inc(v_a_4347_);
lean_dec_ref_known(v___x_4346_, 1);
v_add_4348_ = lean_ctor_get(v_a_4347_, 1);
lean_inc_ref(v_add_4348_);
lean_dec(v_a_4347_);
v___x_4349_ = lean_box(v_kind_4339_);
lean_inc(v_a_4341_);
lean_inc_ref(v_a_4340_);
v___x_4350_ = lean_apply_6(v_add_4348_, v_declName_4336_, v_stx_4338_, v___x_4349_, v_a_4340_, v_a_4341_, lean_box(0));
return v___x_4350_;
}
else
{
lean_object* v_a_4351_; lean_object* v___x_4353_; uint8_t v_isShared_4354_; uint8_t v_isSharedCheck_4358_; 
lean_dec(v_stx_4338_);
lean_dec(v_declName_4336_);
v_a_4351_ = lean_ctor_get(v___x_4346_, 0);
v_isSharedCheck_4358_ = !lean_is_exclusive(v___x_4346_);
if (v_isSharedCheck_4358_ == 0)
{
v___x_4353_ = v___x_4346_;
v_isShared_4354_ = v_isSharedCheck_4358_;
goto v_resetjp_4352_;
}
else
{
lean_inc(v_a_4351_);
lean_dec(v___x_4346_);
v___x_4353_ = lean_box(0);
v_isShared_4354_ = v_isSharedCheck_4358_;
goto v_resetjp_4352_;
}
v_resetjp_4352_:
{
lean_object* v___x_4356_; 
if (v_isShared_4354_ == 0)
{
v___x_4356_ = v___x_4353_;
goto v_reusejp_4355_;
}
else
{
lean_object* v_reuseFailAlloc_4357_; 
v_reuseFailAlloc_4357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4357_, 0, v_a_4351_);
v___x_4356_ = v_reuseFailAlloc_4357_;
goto v_reusejp_4355_;
}
v_reusejp_4355_:
{
return v___x_4356_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_add___boxed(lean_object* v_declName_4359_, lean_object* v_attrName_4360_, lean_object* v_stx_4361_, lean_object* v_kind_4362_, lean_object* v_a_4363_, lean_object* v_a_4364_, lean_object* v_a_4365_){
_start:
{
uint8_t v_kind_boxed_4366_; lean_object* v_res_4367_; 
v_kind_boxed_4366_ = lean_unbox(v_kind_4362_);
v_res_4367_ = l_Lean_Attribute_add(v_declName_4359_, v_attrName_4360_, v_stx_4361_, v_kind_boxed_4366_, v_a_4363_, v_a_4364_);
lean_dec(v_a_4364_);
lean_dec_ref(v_a_4363_);
return v_res_4367_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0(lean_object* v_00_u03b1_4368_, lean_object* v_x_4369_, lean_object* v___y_4370_, lean_object* v___y_4371_){
_start:
{
lean_object* v___x_4373_; 
v___x_4373_ = l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg(v_x_4369_, v___y_4370_, v___y_4371_);
return v___x_4373_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___boxed(lean_object* v_00_u03b1_4374_, lean_object* v_x_4375_, lean_object* v___y_4376_, lean_object* v___y_4377_, lean_object* v___y_4378_){
_start:
{
lean_object* v_res_4379_; 
v_res_4379_ = l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0(v_00_u03b1_4374_, v_x_4375_, v___y_4376_, v___y_4377_);
lean_dec(v___y_4377_);
lean_dec_ref(v___y_4376_);
return v_res_4379_;
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_erase(lean_object* v_declName_4380_, lean_object* v_attrName_4381_, lean_object* v_a_4382_, lean_object* v_a_4383_){
_start:
{
lean_object* v___x_4385_; lean_object* v_env_4386_; lean_object* v___x_4387_; lean_object* v___x_4388_; 
v___x_4385_ = lean_st_ref_get(v_a_4383_);
v_env_4386_ = lean_ctor_get(v___x_4385_, 0);
lean_inc_ref(v_env_4386_);
lean_dec(v___x_4385_);
v___x_4387_ = l_Lean_getAttributeImpl(v_env_4386_, v_attrName_4381_);
v___x_4388_ = l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg(v___x_4387_, v_a_4382_, v_a_4383_);
if (lean_obj_tag(v___x_4388_) == 0)
{
lean_object* v_a_4389_; lean_object* v_erase_4390_; lean_object* v___x_4391_; 
v_a_4389_ = lean_ctor_get(v___x_4388_, 0);
lean_inc(v_a_4389_);
lean_dec_ref_known(v___x_4388_, 1);
v_erase_4390_ = lean_ctor_get(v_a_4389_, 2);
lean_inc_ref(v_erase_4390_);
lean_dec(v_a_4389_);
lean_inc(v_a_4383_);
lean_inc_ref(v_a_4382_);
v___x_4391_ = lean_apply_4(v_erase_4390_, v_declName_4380_, v_a_4382_, v_a_4383_, lean_box(0));
return v___x_4391_;
}
else
{
lean_object* v_a_4392_; lean_object* v___x_4394_; uint8_t v_isShared_4395_; uint8_t v_isSharedCheck_4399_; 
lean_dec(v_declName_4380_);
v_a_4392_ = lean_ctor_get(v___x_4388_, 0);
v_isSharedCheck_4399_ = !lean_is_exclusive(v___x_4388_);
if (v_isSharedCheck_4399_ == 0)
{
v___x_4394_ = v___x_4388_;
v_isShared_4395_ = v_isSharedCheck_4399_;
goto v_resetjp_4393_;
}
else
{
lean_inc(v_a_4392_);
lean_dec(v___x_4388_);
v___x_4394_ = lean_box(0);
v_isShared_4395_ = v_isSharedCheck_4399_;
goto v_resetjp_4393_;
}
v_resetjp_4393_:
{
lean_object* v___x_4397_; 
if (v_isShared_4395_ == 0)
{
v___x_4397_ = v___x_4394_;
goto v_reusejp_4396_;
}
else
{
lean_object* v_reuseFailAlloc_4398_; 
v_reuseFailAlloc_4398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4398_, 0, v_a_4392_);
v___x_4397_ = v_reuseFailAlloc_4398_;
goto v_reusejp_4396_;
}
v_reusejp_4396_:
{
return v___x_4397_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_erase___boxed(lean_object* v_declName_4400_, lean_object* v_attrName_4401_, lean_object* v_a_4402_, lean_object* v_a_4403_, lean_object* v_a_4404_){
_start:
{
lean_object* v_res_4405_; 
v_res_4405_ = l_Lean_Attribute_erase(v_declName_4400_, v_attrName_4401_, v_a_4402_, v_a_4403_);
lean_dec(v_a_4403_);
lean_dec_ref(v_a_4402_);
return v_res_4405_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_updateEnvAttributesImpl_spec__0(lean_object* v_x_4406_, lean_object* v_x_4407_){
_start:
{
if (lean_obj_tag(v_x_4407_) == 0)
{
return v_x_4406_;
}
else
{
lean_object* v_key_4408_; lean_object* v_value_4409_; lean_object* v_tail_4410_; lean_object* v_newEntries_4411_; lean_object* v_map_4412_; uint8_t v___x_4413_; 
v_key_4408_ = lean_ctor_get(v_x_4407_, 0);
lean_inc(v_key_4408_);
v_value_4409_ = lean_ctor_get(v_x_4407_, 1);
lean_inc(v_value_4409_);
v_tail_4410_ = lean_ctor_get(v_x_4407_, 2);
lean_inc(v_tail_4410_);
lean_dec_ref_known(v_x_4407_, 3);
v_newEntries_4411_ = lean_ctor_get(v_x_4406_, 0);
v_map_4412_ = lean_ctor_get(v_x_4406_, 1);
v___x_4413_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(v_map_4412_, v_key_4408_);
if (v___x_4413_ == 0)
{
lean_object* v___x_4415_; uint8_t v_isShared_4416_; uint8_t v_isSharedCheck_4422_; 
lean_inc_ref(v_map_4412_);
lean_inc(v_newEntries_4411_);
v_isSharedCheck_4422_ = !lean_is_exclusive(v_x_4406_);
if (v_isSharedCheck_4422_ == 0)
{
lean_object* v_unused_4423_; lean_object* v_unused_4424_; 
v_unused_4423_ = lean_ctor_get(v_x_4406_, 1);
lean_dec(v_unused_4423_);
v_unused_4424_ = lean_ctor_get(v_x_4406_, 0);
lean_dec(v_unused_4424_);
v___x_4415_ = v_x_4406_;
v_isShared_4416_ = v_isSharedCheck_4422_;
goto v_resetjp_4414_;
}
else
{
lean_dec(v_x_4406_);
v___x_4415_ = lean_box(0);
v_isShared_4416_ = v_isSharedCheck_4422_;
goto v_resetjp_4414_;
}
v_resetjp_4414_:
{
lean_object* v___x_4417_; lean_object* v___x_4419_; 
v___x_4417_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1___redArg(v_map_4412_, v_key_4408_, v_value_4409_);
if (v_isShared_4416_ == 0)
{
lean_ctor_set(v___x_4415_, 1, v___x_4417_);
v___x_4419_ = v___x_4415_;
goto v_reusejp_4418_;
}
else
{
lean_object* v_reuseFailAlloc_4421_; 
v_reuseFailAlloc_4421_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4421_, 0, v_newEntries_4411_);
lean_ctor_set(v_reuseFailAlloc_4421_, 1, v___x_4417_);
v___x_4419_ = v_reuseFailAlloc_4421_;
goto v_reusejp_4418_;
}
v_reusejp_4418_:
{
v_x_4406_ = v___x_4419_;
v_x_4407_ = v_tail_4410_;
goto _start;
}
}
}
else
{
lean_dec(v_value_4409_);
lean_dec(v_key_4408_);
v_x_4407_ = v_tail_4410_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_updateEnvAttributesImpl_spec__1(lean_object* v_as_4426_, size_t v_i_4427_, size_t v_stop_4428_, lean_object* v_b_4429_){
_start:
{
uint8_t v___x_4430_; 
v___x_4430_ = lean_usize_dec_eq(v_i_4427_, v_stop_4428_);
if (v___x_4430_ == 0)
{
lean_object* v___x_4431_; lean_object* v___x_4432_; size_t v___x_4433_; size_t v___x_4434_; 
v___x_4431_ = lean_array_uget_borrowed(v_as_4426_, v_i_4427_);
lean_inc(v___x_4431_);
v___x_4432_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_updateEnvAttributesImpl_spec__0(v_b_4429_, v___x_4431_);
v___x_4433_ = ((size_t)1ULL);
v___x_4434_ = lean_usize_add(v_i_4427_, v___x_4433_);
v_i_4427_ = v___x_4434_;
v_b_4429_ = v___x_4432_;
goto _start;
}
else
{
return v_b_4429_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_updateEnvAttributesImpl_spec__1___boxed(lean_object* v_as_4436_, lean_object* v_i_4437_, lean_object* v_stop_4438_, lean_object* v_b_4439_){
_start:
{
size_t v_i_boxed_4440_; size_t v_stop_boxed_4441_; lean_object* v_res_4442_; 
v_i_boxed_4440_ = lean_unbox_usize(v_i_4437_);
lean_dec(v_i_4437_);
v_stop_boxed_4441_ = lean_unbox_usize(v_stop_4438_);
lean_dec(v_stop_4438_);
v_res_4442_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_updateEnvAttributesImpl_spec__1(v_as_4436_, v_i_boxed_4440_, v_stop_boxed_4441_, v_b_4439_);
lean_dec_ref(v_as_4436_);
return v_res_4442_;
}
}
LEAN_EXPORT lean_object* lean_update_env_attributes(lean_object* v_env_4443_){
_start:
{
lean_object* v___x_4445_; lean_object* v___x_4446_; lean_object* v___x_4447_; lean_object* v___y_4449_; lean_object* v_toEnvExtension_4452_; lean_object* v_asyncMode_4453_; lean_object* v_buckets_4454_; lean_object* v___x_4455_; lean_object* v___x_4456_; lean_object* v___x_4457_; lean_object* v___x_4458_; lean_object* v___x_4459_; uint8_t v___x_4460_; 
v___x_4445_ = l_Lean_attributeMapRef;
v___x_4446_ = lean_st_ref_get(v___x_4445_);
v___x_4447_ = l_Lean_attributeExtension;
v_toEnvExtension_4452_ = lean_ctor_get(v___x_4447_, 0);
v_asyncMode_4453_ = lean_ctor_get(v_toEnvExtension_4452_, 2);
v_buckets_4454_ = lean_ctor_get(v___x_4446_, 1);
lean_inc_ref(v_buckets_4454_);
lean_dec(v___x_4446_);
v___x_4455_ = l_Lean_instInhabitedAttributeExtensionState_default;
v___x_4456_ = lean_box(0);
lean_inc_ref(v_env_4443_);
v___x_4457_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_4455_, v___x_4447_, v_env_4443_, v_asyncMode_4453_, v___x_4456_);
v___x_4458_ = lean_unsigned_to_nat(0u);
v___x_4459_ = lean_array_get_size(v_buckets_4454_);
v___x_4460_ = lean_nat_dec_lt(v___x_4458_, v___x_4459_);
if (v___x_4460_ == 0)
{
lean_dec_ref(v_buckets_4454_);
v___y_4449_ = v___x_4457_;
goto v___jp_4448_;
}
else
{
uint8_t v___x_4461_; 
v___x_4461_ = lean_nat_dec_le(v___x_4459_, v___x_4459_);
if (v___x_4461_ == 0)
{
if (v___x_4460_ == 0)
{
lean_dec_ref(v_buckets_4454_);
v___y_4449_ = v___x_4457_;
goto v___jp_4448_;
}
else
{
size_t v___x_4462_; size_t v___x_4463_; lean_object* v___x_4464_; 
v___x_4462_ = ((size_t)0ULL);
v___x_4463_ = lean_usize_of_nat(v___x_4459_);
v___x_4464_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_updateEnvAttributesImpl_spec__1(v_buckets_4454_, v___x_4462_, v___x_4463_, v___x_4457_);
lean_dec_ref(v_buckets_4454_);
v___y_4449_ = v___x_4464_;
goto v___jp_4448_;
}
}
else
{
size_t v___x_4465_; size_t v___x_4466_; lean_object* v___x_4467_; 
v___x_4465_ = ((size_t)0ULL);
v___x_4466_ = lean_usize_of_nat(v___x_4459_);
v___x_4467_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_updateEnvAttributesImpl_spec__1(v_buckets_4454_, v___x_4465_, v___x_4466_, v___x_4457_);
lean_dec_ref(v_buckets_4454_);
v___y_4449_ = v___x_4467_;
goto v___jp_4448_;
}
}
v___jp_4448_:
{
lean_object* v___x_4450_; lean_object* v___x_4451_; 
v___x_4450_ = l_Lean_PersistentEnvExtension_setState___redArg(v___x_4447_, v_env_4443_, v___y_4449_);
v___x_4451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4451_, 0, v___x_4450_);
return v___x_4451_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_updateEnvAttributesImpl___boxed(lean_object* v_env_4468_, lean_object* v_a_4469_){
_start:
{
lean_object* v_res_4470_; 
v_res_4470_ = lean_update_env_attributes(v_env_4468_);
return v_res_4470_;
}
}
LEAN_EXPORT lean_object* lean_get_num_attributes(){
_start:
{
lean_object* v___x_4472_; lean_object* v___x_4473_; lean_object* v_size_4474_; lean_object* v___x_4475_; 
v___x_4472_ = l_Lean_attributeMapRef;
v___x_4473_ = lean_st_ref_get(v___x_4472_);
v_size_4474_ = lean_ctor_get(v___x_4473_, 0);
lean_inc(v_size_4474_);
lean_dec(v___x_4473_);
v___x_4475_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4475_, 0, v_size_4474_);
return v___x_4475_;
}
}
LEAN_EXPORT lean_object* l_Lean_getNumBuiltinAttributesImpl___boxed(lean_object* v_a_4476_){
_start:
{
lean_object* v_res_4477_; 
v_res_4477_ = lean_get_num_attributes();
return v_res_4477_;
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
