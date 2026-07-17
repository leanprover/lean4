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
lean_object* v___y_1342_; uint8_t v___y_1343_; lean_object* v___y_1344_; lean_object* v___y_1345_; lean_object* v___y_1346_; uint8_t v___y_1347_; lean_object* v___y_1348_; lean_object* v___y_1349_; lean_object* v___y_1350_; lean_object* v___y_1378_; lean_object* v___y_1379_; lean_object* v___y_1380_; uint8_t v___y_1381_; uint8_t v___y_1382_; uint8_t v___y_1383_; lean_object* v___y_1384_; lean_object* v___y_1385_; lean_object* v___y_1403_; lean_object* v___y_1404_; uint8_t v___y_1405_; uint8_t v___y_1406_; lean_object* v___y_1407_; uint8_t v___y_1408_; lean_object* v___y_1409_; lean_object* v___y_1410_; lean_object* v___y_1414_; lean_object* v___y_1415_; uint8_t v___y_1416_; uint8_t v___y_1417_; lean_object* v___y_1418_; lean_object* v___y_1419_; uint8_t v___y_1420_; uint8_t v___x_1425_; lean_object* v___y_1427_; uint8_t v___y_1428_; lean_object* v___y_1429_; lean_object* v___y_1430_; lean_object* v___y_1431_; uint8_t v___y_1432_; uint8_t v___y_1433_; uint8_t v___y_1435_; uint8_t v___x_1450_; 
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
lean_ctor_set(v___x_1367_, 1, v___y_1344_);
lean_inc_ref(v___y_1345_);
lean_inc_ref(v___y_1342_);
v___x_1368_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1368_, 0, v___y_1342_);
lean_ctor_set(v___x_1368_, 1, v___y_1348_);
lean_ctor_set(v___x_1368_, 2, v___y_1346_);
lean_ctor_set(v___x_1368_, 3, v___y_1345_);
lean_ctor_set(v___x_1368_, 4, v___x_1367_);
lean_ctor_set_uint8(v___x_1368_, sizeof(void*)*5, v___y_1343_);
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
lean_inc_ref_n(v___y_1384_, 2);
v___x_1392_ = l_Lean_FileMap_toPosition(v___y_1384_, v___y_1380_);
lean_dec(v___y_1380_);
v___x_1393_ = l_Lean_FileMap_toPosition(v___y_1384_, v___y_1385_);
lean_dec(v___y_1385_);
v___x_1394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1394_, 0, v___x_1393_);
v___x_1395_ = ((lean_object*)(l_Lean_instInhabitedAttributeImplCore_default___closed__3));
if (v___y_1382_ == 0)
{
lean_del_object(v___x_1390_);
lean_dec_ref(v___y_1378_);
v___y_1342_ = v___y_1379_;
v___y_1343_ = v___y_1381_;
v___y_1344_ = v_a_1388_;
v___y_1345_ = v___x_1395_;
v___y_1346_ = v___x_1394_;
v___y_1347_ = v___y_1383_;
v___y_1348_ = v___x_1392_;
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
v___y_1342_ = v___y_1379_;
v___y_1343_ = v___y_1381_;
v___y_1344_ = v_a_1388_;
v___y_1345_ = v___x_1395_;
v___y_1346_ = v___x_1394_;
v___y_1347_ = v___y_1383_;
v___y_1348_ = v___x_1392_;
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
v___x_1411_ = l_Lean_Syntax_getTailPos_x3f(v___y_1409_, v___y_1405_);
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
v___x_1422_ = l_Lean_Syntax_getPos_x3f(v_ref_1421_, v___y_1416_);
if (lean_obj_tag(v___x_1422_) == 0)
{
lean_object* v___x_1423_; 
v___x_1423_ = lean_unsigned_to_nat(0u);
v___y_1403_ = v___y_1414_;
v___y_1404_ = v___y_1415_;
v___y_1405_ = v___y_1416_;
v___y_1406_ = v___y_1417_;
v___y_1407_ = v___y_1419_;
v___y_1408_ = v___y_1420_;
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
v___y_1407_ = v___y_1419_;
v___y_1408_ = v___y_1420_;
v___y_1409_ = v_ref_1421_;
v___y_1410_ = v_val_1424_;
goto v___jp_1402_;
}
}
v___jp_1426_:
{
if (v___y_1433_ == 0)
{
v___y_1414_ = v___y_1430_;
v___y_1415_ = v___y_1427_;
v___y_1416_ = v___y_1432_;
v___y_1417_ = v___y_1428_;
v___y_1418_ = v___y_1429_;
v___y_1419_ = v___y_1431_;
v___y_1420_ = v_severity_1336_;
goto v___jp_1413_;
}
else
{
v___y_1414_ = v___y_1430_;
v___y_1415_ = v___y_1427_;
v___y_1416_ = v___y_1432_;
v___y_1417_ = v___y_1428_;
v___y_1418_ = v___y_1429_;
v___y_1419_ = v___y_1431_;
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
v___y_1428_ = v_suppressElabErrors_1440_;
v___y_1429_ = v_ref_1439_;
v___y_1430_ = v___f_1443_;
v___y_1431_ = v_fileMap_1437_;
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
v___y_1428_ = v_suppressElabErrors_1440_;
v___y_1429_ = v_ref_1439_;
v___y_1430_ = v___f_1443_;
v___y_1431_ = v_fileMap_1437_;
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
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_registerParametricAttribute_spec__4___redArg(lean_object* v_env_2412_, lean_object* v___y_2413_){
_start:
{
lean_object* v___x_2415_; lean_object* v_nextMacroScope_2416_; lean_object* v_ngen_2417_; lean_object* v_auxDeclNGen_2418_; lean_object* v_traceState_2419_; lean_object* v_messages_2420_; lean_object* v_infoState_2421_; lean_object* v_snapshotTasks_2422_; lean_object* v___x_2424_; uint8_t v_isShared_2425_; uint8_t v_isSharedCheck_2433_; 
v___x_2415_ = lean_st_ref_take(v___y_2413_);
v_nextMacroScope_2416_ = lean_ctor_get(v___x_2415_, 1);
v_ngen_2417_ = lean_ctor_get(v___x_2415_, 2);
v_auxDeclNGen_2418_ = lean_ctor_get(v___x_2415_, 3);
v_traceState_2419_ = lean_ctor_get(v___x_2415_, 4);
v_messages_2420_ = lean_ctor_get(v___x_2415_, 6);
v_infoState_2421_ = lean_ctor_get(v___x_2415_, 7);
v_snapshotTasks_2422_ = lean_ctor_get(v___x_2415_, 8);
v_isSharedCheck_2433_ = !lean_is_exclusive(v___x_2415_);
if (v_isSharedCheck_2433_ == 0)
{
lean_object* v_unused_2434_; lean_object* v_unused_2435_; 
v_unused_2434_ = lean_ctor_get(v___x_2415_, 5);
lean_dec(v_unused_2434_);
v_unused_2435_ = lean_ctor_get(v___x_2415_, 0);
lean_dec(v_unused_2435_);
v___x_2424_ = v___x_2415_;
v_isShared_2425_ = v_isSharedCheck_2433_;
goto v_resetjp_2423_;
}
else
{
lean_inc(v_snapshotTasks_2422_);
lean_inc(v_infoState_2421_);
lean_inc(v_messages_2420_);
lean_inc(v_traceState_2419_);
lean_inc(v_auxDeclNGen_2418_);
lean_inc(v_ngen_2417_);
lean_inc(v_nextMacroScope_2416_);
lean_dec(v___x_2415_);
v___x_2424_ = lean_box(0);
v_isShared_2425_ = v_isSharedCheck_2433_;
goto v_resetjp_2423_;
}
v_resetjp_2423_:
{
lean_object* v___x_2426_; lean_object* v___x_2428_; 
v___x_2426_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2);
if (v_isShared_2425_ == 0)
{
lean_ctor_set(v___x_2424_, 5, v___x_2426_);
lean_ctor_set(v___x_2424_, 0, v_env_2412_);
v___x_2428_ = v___x_2424_;
goto v_reusejp_2427_;
}
else
{
lean_object* v_reuseFailAlloc_2432_; 
v_reuseFailAlloc_2432_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2432_, 0, v_env_2412_);
lean_ctor_set(v_reuseFailAlloc_2432_, 1, v_nextMacroScope_2416_);
lean_ctor_set(v_reuseFailAlloc_2432_, 2, v_ngen_2417_);
lean_ctor_set(v_reuseFailAlloc_2432_, 3, v_auxDeclNGen_2418_);
lean_ctor_set(v_reuseFailAlloc_2432_, 4, v_traceState_2419_);
lean_ctor_set(v_reuseFailAlloc_2432_, 5, v___x_2426_);
lean_ctor_set(v_reuseFailAlloc_2432_, 6, v_messages_2420_);
lean_ctor_set(v_reuseFailAlloc_2432_, 7, v_infoState_2421_);
lean_ctor_set(v_reuseFailAlloc_2432_, 8, v_snapshotTasks_2422_);
v___x_2428_ = v_reuseFailAlloc_2432_;
goto v_reusejp_2427_;
}
v_reusejp_2427_:
{
lean_object* v___x_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; 
v___x_2429_ = lean_st_ref_set(v___y_2413_, v___x_2428_);
v___x_2430_ = lean_box(0);
v___x_2431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2431_, 0, v___x_2430_);
return v___x_2431_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_registerParametricAttribute_spec__4___redArg___boxed(lean_object* v_env_2436_, lean_object* v___y_2437_, lean_object* v___y_2438_){
_start:
{
lean_object* v_res_2439_; 
v_res_2439_ = l_Lean_setEnv___at___00Lean_registerParametricAttribute_spec__4___redArg(v_env_2436_, v___y_2437_);
lean_dec(v___y_2437_);
return v_res_2439_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_registerParametricAttribute_spec__4(lean_object* v_env_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_){
_start:
{
lean_object* v___x_2444_; 
v___x_2444_ = l_Lean_setEnv___at___00Lean_registerParametricAttribute_spec__4___redArg(v_env_2440_, v___y_2442_);
return v___x_2444_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_registerParametricAttribute_spec__4___boxed(lean_object* v_env_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_){
_start:
{
lean_object* v_res_2449_; 
v_res_2449_ = l_Lean_setEnv___at___00Lean_registerParametricAttribute_spec__4(v_env_2445_, v___y_2446_, v___y_2447_);
lean_dec(v___y_2447_);
lean_dec_ref(v___y_2446_);
return v_res_2449_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___lam__0(lean_object* v_x_2450_, lean_object* v_p_2451_){
_start:
{
lean_object* v_fst_2452_; lean_object* v_snd_2453_; lean_object* v___x_2455_; uint8_t v_isShared_2456_; uint8_t v_isSharedCheck_2470_; 
v_fst_2452_ = lean_ctor_get(v_x_2450_, 0);
v_snd_2453_ = lean_ctor_get(v_x_2450_, 1);
v_isSharedCheck_2470_ = !lean_is_exclusive(v_x_2450_);
if (v_isSharedCheck_2470_ == 0)
{
v___x_2455_ = v_x_2450_;
v_isShared_2456_ = v_isSharedCheck_2470_;
goto v_resetjp_2454_;
}
else
{
lean_inc(v_snd_2453_);
lean_inc(v_fst_2452_);
lean_dec(v_x_2450_);
v___x_2455_ = lean_box(0);
v_isShared_2456_ = v_isSharedCheck_2470_;
goto v_resetjp_2454_;
}
v_resetjp_2454_:
{
lean_object* v_fst_2457_; lean_object* v_snd_2458_; lean_object* v___x_2460_; uint8_t v_isShared_2461_; uint8_t v_isSharedCheck_2469_; 
v_fst_2457_ = lean_ctor_get(v_p_2451_, 0);
v_snd_2458_ = lean_ctor_get(v_p_2451_, 1);
v_isSharedCheck_2469_ = !lean_is_exclusive(v_p_2451_);
if (v_isSharedCheck_2469_ == 0)
{
v___x_2460_ = v_p_2451_;
v_isShared_2461_ = v_isSharedCheck_2469_;
goto v_resetjp_2459_;
}
else
{
lean_inc(v_snd_2458_);
lean_inc(v_fst_2457_);
lean_dec(v_p_2451_);
v___x_2460_ = lean_box(0);
v_isShared_2461_ = v_isSharedCheck_2469_;
goto v_resetjp_2459_;
}
v_resetjp_2459_:
{
lean_object* v___x_2463_; 
lean_inc(v_fst_2457_);
if (v_isShared_2456_ == 0)
{
lean_ctor_set_tag(v___x_2455_, 1);
lean_ctor_set(v___x_2455_, 1, v_fst_2452_);
lean_ctor_set(v___x_2455_, 0, v_fst_2457_);
v___x_2463_ = v___x_2455_;
goto v_reusejp_2462_;
}
else
{
lean_object* v_reuseFailAlloc_2468_; 
v_reuseFailAlloc_2468_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2468_, 0, v_fst_2457_);
lean_ctor_set(v_reuseFailAlloc_2468_, 1, v_fst_2452_);
v___x_2463_ = v_reuseFailAlloc_2468_;
goto v_reusejp_2462_;
}
v_reusejp_2462_:
{
lean_object* v___x_2464_; lean_object* v___x_2466_; 
v___x_2464_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_2457_, v_snd_2458_, v_snd_2453_);
if (v_isShared_2461_ == 0)
{
lean_ctor_set(v___x_2460_, 1, v___x_2464_);
lean_ctor_set(v___x_2460_, 0, v___x_2463_);
v___x_2466_ = v___x_2460_;
goto v_reusejp_2465_;
}
else
{
lean_object* v_reuseFailAlloc_2467_; 
v_reuseFailAlloc_2467_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2467_, 0, v___x_2463_);
lean_ctor_set(v_reuseFailAlloc_2467_, 1, v___x_2464_);
v___x_2466_ = v_reuseFailAlloc_2467_;
goto v_reusejp_2465_;
}
v_reusejp_2465_:
{
return v___x_2466_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1_spec__1___redArg(lean_object* v_init_2471_, lean_object* v_x_2472_){
_start:
{
if (lean_obj_tag(v_x_2472_) == 0)
{
lean_object* v_k_2473_; lean_object* v_v_2474_; lean_object* v_l_2475_; lean_object* v_r_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; 
v_k_2473_ = lean_ctor_get(v_x_2472_, 1);
v_v_2474_ = lean_ctor_get(v_x_2472_, 2);
v_l_2475_ = lean_ctor_get(v_x_2472_, 3);
v_r_2476_ = lean_ctor_get(v_x_2472_, 4);
v___x_2477_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1_spec__1___redArg(v_init_2471_, v_l_2475_);
lean_inc(v_v_2474_);
lean_inc(v_k_2473_);
v___x_2478_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2478_, 0, v_k_2473_);
lean_ctor_set(v___x_2478_, 1, v_v_2474_);
v___x_2479_ = lean_array_push(v___x_2477_, v___x_2478_);
v_init_2471_ = v___x_2479_;
v_x_2472_ = v_r_2476_;
goto _start;
}
else
{
return v_init_2471_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1_spec__1___redArg___boxed(lean_object* v_init_2481_, lean_object* v_x_2482_){
_start:
{
lean_object* v_res_2483_; 
v_res_2483_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1_spec__1___redArg(v_init_2481_, v_x_2482_);
lean_dec(v_x_2482_);
return v_res_2483_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2_spec__3___redArg(lean_object* v_hi_2484_, lean_object* v_pivot_2485_, lean_object* v_as_2486_, lean_object* v_i_2487_, lean_object* v_k_2488_){
_start:
{
uint8_t v___x_2489_; 
v___x_2489_ = lean_nat_dec_lt(v_k_2488_, v_hi_2484_);
if (v___x_2489_ == 0)
{
lean_object* v___x_2490_; lean_object* v___x_2491_; 
lean_dec(v_k_2488_);
v___x_2490_ = lean_array_fswap(v_as_2486_, v_i_2487_, v_hi_2484_);
v___x_2491_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2491_, 0, v_i_2487_);
lean_ctor_set(v___x_2491_, 1, v___x_2490_);
return v___x_2491_;
}
else
{
lean_object* v___x_2492_; lean_object* v_fst_2493_; lean_object* v_fst_2494_; uint8_t v___x_2495_; 
v___x_2492_ = lean_array_fget_borrowed(v_as_2486_, v_k_2488_);
v_fst_2493_ = lean_ctor_get(v___x_2492_, 0);
v_fst_2494_ = lean_ctor_get(v_pivot_2485_, 0);
v___x_2495_ = l_Lean_Name_quickLt(v_fst_2493_, v_fst_2494_);
if (v___x_2495_ == 0)
{
lean_object* v___x_2496_; lean_object* v___x_2497_; 
v___x_2496_ = lean_unsigned_to_nat(1u);
v___x_2497_ = lean_nat_add(v_k_2488_, v___x_2496_);
lean_dec(v_k_2488_);
v_k_2488_ = v___x_2497_;
goto _start;
}
else
{
lean_object* v___x_2499_; lean_object* v___x_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; 
v___x_2499_ = lean_array_fswap(v_as_2486_, v_i_2487_, v_k_2488_);
v___x_2500_ = lean_unsigned_to_nat(1u);
v___x_2501_ = lean_nat_add(v_i_2487_, v___x_2500_);
lean_dec(v_i_2487_);
v___x_2502_ = lean_nat_add(v_k_2488_, v___x_2500_);
lean_dec(v_k_2488_);
v_as_2486_ = v___x_2499_;
v_i_2487_ = v___x_2501_;
v_k_2488_ = v___x_2502_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2_spec__3___redArg___boxed(lean_object* v_hi_2504_, lean_object* v_pivot_2505_, lean_object* v_as_2506_, lean_object* v_i_2507_, lean_object* v_k_2508_){
_start:
{
lean_object* v_res_2509_; 
v_res_2509_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2_spec__3___redArg(v_hi_2504_, v_pivot_2505_, v_as_2506_, v_i_2507_, v_k_2508_);
lean_dec_ref(v_pivot_2505_);
lean_dec(v_hi_2504_);
return v_res_2509_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2___redArg___lam__0(lean_object* v_a_2510_, lean_object* v_b_2511_){
_start:
{
lean_object* v_fst_2512_; lean_object* v_fst_2513_; uint8_t v___x_2514_; 
v_fst_2512_ = lean_ctor_get(v_a_2510_, 0);
v_fst_2513_ = lean_ctor_get(v_b_2511_, 0);
v___x_2514_ = l_Lean_Name_quickLt(v_fst_2512_, v_fst_2513_);
return v___x_2514_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2___redArg___lam__0___boxed(lean_object* v_a_2515_, lean_object* v_b_2516_){
_start:
{
uint8_t v_res_2517_; lean_object* v_r_2518_; 
v_res_2517_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2___redArg___lam__0(v_a_2515_, v_b_2516_);
lean_dec_ref(v_b_2516_);
lean_dec_ref(v_a_2515_);
v_r_2518_ = lean_box(v_res_2517_);
return v_r_2518_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2___redArg(lean_object* v_n_2519_, lean_object* v_as_2520_, lean_object* v_lo_2521_, lean_object* v_hi_2522_){
_start:
{
lean_object* v___y_2524_; uint8_t v___x_2534_; 
v___x_2534_ = lean_nat_dec_lt(v_lo_2521_, v_hi_2522_);
if (v___x_2534_ == 0)
{
lean_dec(v_lo_2521_);
return v_as_2520_;
}
else
{
lean_object* v___x_2535_; lean_object* v___x_2536_; lean_object* v_mid_2537_; lean_object* v___y_2539_; lean_object* v___y_2545_; lean_object* v___x_2550_; lean_object* v___x_2551_; uint8_t v___x_2552_; 
v___x_2535_ = lean_nat_add(v_lo_2521_, v_hi_2522_);
v___x_2536_ = lean_unsigned_to_nat(1u);
v_mid_2537_ = lean_nat_shiftr(v___x_2535_, v___x_2536_);
lean_dec(v___x_2535_);
v___x_2550_ = lean_array_fget_borrowed(v_as_2520_, v_mid_2537_);
v___x_2551_ = lean_array_fget_borrowed(v_as_2520_, v_lo_2521_);
v___x_2552_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2___redArg___lam__0(v___x_2550_, v___x_2551_);
if (v___x_2552_ == 0)
{
v___y_2545_ = v_as_2520_;
goto v___jp_2544_;
}
else
{
lean_object* v___x_2553_; 
v___x_2553_ = lean_array_fswap(v_as_2520_, v_lo_2521_, v_mid_2537_);
v___y_2545_ = v___x_2553_;
goto v___jp_2544_;
}
v___jp_2538_:
{
lean_object* v___x_2540_; lean_object* v___x_2541_; uint8_t v___x_2542_; 
v___x_2540_ = lean_array_fget_borrowed(v___y_2539_, v_mid_2537_);
v___x_2541_ = lean_array_fget_borrowed(v___y_2539_, v_hi_2522_);
v___x_2542_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2___redArg___lam__0(v___x_2540_, v___x_2541_);
if (v___x_2542_ == 0)
{
lean_dec(v_mid_2537_);
v___y_2524_ = v___y_2539_;
goto v___jp_2523_;
}
else
{
lean_object* v___x_2543_; 
v___x_2543_ = lean_array_fswap(v___y_2539_, v_mid_2537_, v_hi_2522_);
lean_dec(v_mid_2537_);
v___y_2524_ = v___x_2543_;
goto v___jp_2523_;
}
}
v___jp_2544_:
{
lean_object* v___x_2546_; lean_object* v___x_2547_; uint8_t v___x_2548_; 
v___x_2546_ = lean_array_fget_borrowed(v___y_2545_, v_hi_2522_);
v___x_2547_ = lean_array_fget_borrowed(v___y_2545_, v_lo_2521_);
v___x_2548_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2___redArg___lam__0(v___x_2546_, v___x_2547_);
if (v___x_2548_ == 0)
{
v___y_2539_ = v___y_2545_;
goto v___jp_2538_;
}
else
{
lean_object* v___x_2549_; 
v___x_2549_ = lean_array_fswap(v___y_2545_, v_lo_2521_, v_hi_2522_);
v___y_2539_ = v___x_2549_;
goto v___jp_2538_;
}
}
}
v___jp_2523_:
{
lean_object* v_pivot_2525_; lean_object* v___x_2526_; lean_object* v_fst_2527_; lean_object* v_snd_2528_; uint8_t v___x_2529_; 
v_pivot_2525_ = lean_array_fget(v___y_2524_, v_hi_2522_);
lean_inc_n(v_lo_2521_, 2);
v___x_2526_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2_spec__3___redArg(v_hi_2522_, v_pivot_2525_, v___y_2524_, v_lo_2521_, v_lo_2521_);
lean_dec(v_pivot_2525_);
v_fst_2527_ = lean_ctor_get(v___x_2526_, 0);
lean_inc(v_fst_2527_);
v_snd_2528_ = lean_ctor_get(v___x_2526_, 1);
lean_inc(v_snd_2528_);
lean_dec_ref(v___x_2526_);
v___x_2529_ = lean_nat_dec_le(v_hi_2522_, v_fst_2527_);
if (v___x_2529_ == 0)
{
lean_object* v___x_2530_; lean_object* v___x_2531_; lean_object* v___x_2532_; 
v___x_2530_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2___redArg(v_n_2519_, v_snd_2528_, v_lo_2521_, v_fst_2527_);
v___x_2531_ = lean_unsigned_to_nat(1u);
v___x_2532_ = lean_nat_add(v_fst_2527_, v___x_2531_);
lean_dec(v_fst_2527_);
v_as_2520_ = v___x_2530_;
v_lo_2521_ = v___x_2532_;
goto _start;
}
else
{
lean_dec(v_fst_2527_);
lean_dec(v_lo_2521_);
return v_snd_2528_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2___redArg___boxed(lean_object* v_n_2554_, lean_object* v_as_2555_, lean_object* v_lo_2556_, lean_object* v_hi_2557_){
_start:
{
lean_object* v_res_2558_; 
v_res_2558_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2___redArg(v_n_2554_, v_as_2555_, v_lo_2556_, v_hi_2557_);
lean_dec(v_hi_2557_);
lean_dec(v_n_2554_);
return v_res_2558_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3_spec__5___redArg(lean_object* v_snd_2559_, lean_object* v_as_2560_, size_t v_i_2561_, size_t v_stop_2562_, lean_object* v_b_2563_){
_start:
{
lean_object* v___y_2565_; uint8_t v___x_2569_; 
v___x_2569_ = lean_usize_dec_eq(v_i_2561_, v_stop_2562_);
if (v___x_2569_ == 0)
{
lean_object* v___x_2570_; lean_object* v___x_2571_; 
v___x_2570_ = lean_array_uget_borrowed(v_as_2560_, v_i_2561_);
v___x_2571_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_snd_2559_, v___x_2570_);
if (lean_obj_tag(v___x_2571_) == 0)
{
v___y_2565_ = v_b_2563_;
goto v___jp_2564_;
}
else
{
lean_object* v_val_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; 
v_val_2572_ = lean_ctor_get(v___x_2571_, 0);
lean_inc(v_val_2572_);
lean_dec_ref_known(v___x_2571_, 1);
lean_inc(v___x_2570_);
v___x_2573_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2573_, 0, v___x_2570_);
lean_ctor_set(v___x_2573_, 1, v_val_2572_);
v___x_2574_ = lean_array_push(v_b_2563_, v___x_2573_);
v___y_2565_ = v___x_2574_;
goto v___jp_2564_;
}
}
else
{
return v_b_2563_;
}
v___jp_2564_:
{
size_t v___x_2566_; size_t v___x_2567_; 
v___x_2566_ = ((size_t)1ULL);
v___x_2567_ = lean_usize_add(v_i_2561_, v___x_2566_);
v_i_2561_ = v___x_2567_;
v_b_2563_ = v___y_2565_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3_spec__5___redArg___boxed(lean_object* v_snd_2575_, lean_object* v_as_2576_, lean_object* v_i_2577_, lean_object* v_stop_2578_, lean_object* v_b_2579_){
_start:
{
size_t v_i_boxed_2580_; size_t v_stop_boxed_2581_; lean_object* v_res_2582_; 
v_i_boxed_2580_ = lean_unbox_usize(v_i_2577_);
lean_dec(v_i_2577_);
v_stop_boxed_2581_ = lean_unbox_usize(v_stop_2578_);
lean_dec(v_stop_2578_);
v_res_2582_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3_spec__5___redArg(v_snd_2575_, v_as_2576_, v_i_boxed_2580_, v_stop_boxed_2581_, v_b_2579_);
lean_dec_ref(v_as_2576_);
lean_dec(v_snd_2575_);
return v_res_2582_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3___redArg(lean_object* v_snd_2583_, lean_object* v_as_2584_, lean_object* v_start_2585_, lean_object* v_stop_2586_){
_start:
{
lean_object* v___x_2587_; uint8_t v___x_2588_; 
v___x_2587_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___lam__2___closed__0));
v___x_2588_ = lean_nat_dec_lt(v_start_2585_, v_stop_2586_);
if (v___x_2588_ == 0)
{
return v___x_2587_;
}
else
{
lean_object* v___x_2589_; uint8_t v___x_2590_; 
v___x_2589_ = lean_array_get_size(v_as_2584_);
v___x_2590_ = lean_nat_dec_le(v_stop_2586_, v___x_2589_);
if (v___x_2590_ == 0)
{
uint8_t v___x_2591_; 
v___x_2591_ = lean_nat_dec_lt(v_start_2585_, v___x_2589_);
if (v___x_2591_ == 0)
{
return v___x_2587_;
}
else
{
size_t v___x_2592_; size_t v___x_2593_; lean_object* v___x_2594_; 
v___x_2592_ = lean_usize_of_nat(v_start_2585_);
v___x_2593_ = lean_usize_of_nat(v___x_2589_);
v___x_2594_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3_spec__5___redArg(v_snd_2583_, v_as_2584_, v___x_2592_, v___x_2593_, v___x_2587_);
return v___x_2594_;
}
}
else
{
size_t v___x_2595_; size_t v___x_2596_; lean_object* v___x_2597_; 
v___x_2595_ = lean_usize_of_nat(v_start_2585_);
v___x_2596_ = lean_usize_of_nat(v_stop_2586_);
v___x_2597_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3_spec__5___redArg(v_snd_2583_, v_as_2584_, v___x_2595_, v___x_2596_, v___x_2587_);
return v___x_2597_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3___redArg___boxed(lean_object* v_snd_2598_, lean_object* v_as_2599_, lean_object* v_start_2600_, lean_object* v_stop_2601_){
_start:
{
lean_object* v_res_2602_; 
v_res_2602_ = l_Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3___redArg(v_snd_2598_, v_as_2599_, v_start_2600_, v_stop_2601_);
lean_dec(v_stop_2601_);
lean_dec(v_start_2600_);
lean_dec_ref(v_as_2599_);
lean_dec(v_snd_2598_);
return v_res_2602_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttribute_spec__0___redArg(lean_object* v_impl_2603_, lean_object* v_env_2604_, lean_object* v_as_2605_, size_t v_i_2606_, size_t v_stop_2607_, lean_object* v_b_2608_){
_start:
{
lean_object* v___y_2610_; uint8_t v___x_2614_; 
v___x_2614_ = lean_usize_dec_eq(v_i_2606_, v_stop_2607_);
if (v___x_2614_ == 0)
{
lean_object* v___x_2615_; lean_object* v_fst_2616_; lean_object* v_snd_2617_; lean_object* v_filterExport_2618_; lean_object* v___x_2619_; uint8_t v___x_2620_; 
v___x_2615_ = lean_array_uget_borrowed(v_as_2605_, v_i_2606_);
v_fst_2616_ = lean_ctor_get(v___x_2615_, 0);
v_snd_2617_ = lean_ctor_get(v___x_2615_, 1);
v_filterExport_2618_ = lean_ctor_get(v_impl_2603_, 3);
lean_inc_ref(v_filterExport_2618_);
lean_inc(v_snd_2617_);
lean_inc(v_fst_2616_);
lean_inc_ref(v_env_2604_);
v___x_2619_ = lean_apply_3(v_filterExport_2618_, v_env_2604_, v_fst_2616_, v_snd_2617_);
v___x_2620_ = lean_unbox(v___x_2619_);
if (v___x_2620_ == 0)
{
v___y_2610_ = v_b_2608_;
goto v___jp_2609_;
}
else
{
lean_object* v___x_2621_; 
lean_inc(v___x_2615_);
v___x_2621_ = lean_array_push(v_b_2608_, v___x_2615_);
v___y_2610_ = v___x_2621_;
goto v___jp_2609_;
}
}
else
{
lean_dec_ref(v_env_2604_);
lean_dec_ref(v_impl_2603_);
return v_b_2608_;
}
v___jp_2609_:
{
size_t v___x_2611_; size_t v___x_2612_; 
v___x_2611_ = ((size_t)1ULL);
v___x_2612_ = lean_usize_add(v_i_2606_, v___x_2611_);
v_i_2606_ = v___x_2612_;
v_b_2608_ = v___y_2610_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttribute_spec__0___redArg___boxed(lean_object* v_impl_2622_, lean_object* v_env_2623_, lean_object* v_as_2624_, lean_object* v_i_2625_, lean_object* v_stop_2626_, lean_object* v_b_2627_){
_start:
{
size_t v_i_boxed_2628_; size_t v_stop_boxed_2629_; lean_object* v_res_2630_; 
v_i_boxed_2628_ = lean_unbox_usize(v_i_2625_);
lean_dec(v_i_2625_);
v_stop_boxed_2629_ = lean_unbox_usize(v_stop_2626_);
lean_dec(v_stop_2626_);
v_res_2630_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttribute_spec__0___redArg(v_impl_2622_, v_env_2623_, v_as_2624_, v_i_boxed_2628_, v_stop_boxed_2629_, v_b_2627_);
lean_dec_ref(v_as_2624_);
return v_res_2630_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___lam__1(lean_object* v_impl_2631_, uint8_t v_preserveOrder_2632_, lean_object* v_env_2633_, lean_object* v_x_2634_){
_start:
{
lean_object* v___y_2636_; 
if (v_preserveOrder_2632_ == 0)
{
lean_object* v_snd_2652_; lean_object* v___x_2653_; lean_object* v___x_2654_; lean_object* v_r_2655_; lean_object* v___x_2656_; lean_object* v___y_2658_; lean_object* v___y_2659_; uint8_t v___x_2661_; 
v_snd_2652_ = lean_ctor_get(v_x_2634_, 1);
lean_inc(v_snd_2652_);
lean_dec_ref(v_x_2634_);
v___x_2653_ = lean_unsigned_to_nat(0u);
v___x_2654_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___lam__2___closed__0));
v_r_2655_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1_spec__1___redArg(v___x_2654_, v_snd_2652_);
lean_dec(v_snd_2652_);
v___x_2656_ = lean_array_get_size(v_r_2655_);
v___x_2661_ = lean_nat_dec_eq(v___x_2656_, v___x_2653_);
if (v___x_2661_ == 0)
{
lean_object* v___x_2662_; lean_object* v___x_2663_; lean_object* v___y_2665_; uint8_t v___x_2667_; 
v___x_2662_ = lean_unsigned_to_nat(1u);
v___x_2663_ = lean_nat_sub(v___x_2656_, v___x_2662_);
v___x_2667_ = lean_nat_dec_le(v___x_2653_, v___x_2663_);
if (v___x_2667_ == 0)
{
lean_inc(v___x_2663_);
v___y_2665_ = v___x_2663_;
goto v___jp_2664_;
}
else
{
v___y_2665_ = v___x_2653_;
goto v___jp_2664_;
}
v___jp_2664_:
{
uint8_t v___x_2666_; 
v___x_2666_ = lean_nat_dec_le(v___y_2665_, v___x_2663_);
if (v___x_2666_ == 0)
{
lean_dec(v___x_2663_);
lean_inc(v___y_2665_);
v___y_2658_ = v___y_2665_;
v___y_2659_ = v___y_2665_;
goto v___jp_2657_;
}
else
{
v___y_2658_ = v___y_2665_;
v___y_2659_ = v___x_2663_;
goto v___jp_2657_;
}
}
}
else
{
v___y_2636_ = v_r_2655_;
goto v___jp_2635_;
}
v___jp_2657_:
{
lean_object* v___x_2660_; 
v___x_2660_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2___redArg(v___x_2656_, v_r_2655_, v___y_2658_, v___y_2659_);
lean_dec(v___y_2659_);
v___y_2636_ = v___x_2660_;
goto v___jp_2635_;
}
}
else
{
lean_object* v_fst_2668_; lean_object* v_snd_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; 
v_fst_2668_ = lean_ctor_get(v_x_2634_, 0);
lean_inc(v_fst_2668_);
v_snd_2669_ = lean_ctor_get(v_x_2634_, 1);
lean_inc(v_snd_2669_);
lean_dec_ref(v_x_2634_);
v___x_2670_ = lean_array_mk(v_fst_2668_);
v___x_2671_ = l_Array_reverse___redArg(v___x_2670_);
v___x_2672_ = lean_unsigned_to_nat(0u);
v___x_2673_ = lean_array_get_size(v___x_2671_);
v___x_2674_ = l_Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3___redArg(v_snd_2669_, v___x_2671_, v___x_2672_, v___x_2673_);
lean_dec_ref(v___x_2671_);
lean_dec(v_snd_2669_);
v___y_2636_ = v___x_2674_;
goto v___jp_2635_;
}
v___jp_2635_:
{
lean_object* v___x_2637_; lean_object* v___x_2638_; lean_object* v___x_2639_; uint8_t v___x_2640_; 
v___x_2637_ = lean_unsigned_to_nat(0u);
v___x_2638_ = lean_array_get_size(v___y_2636_);
v___x_2639_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___lam__2___closed__0));
v___x_2640_ = lean_nat_dec_lt(v___x_2637_, v___x_2638_);
if (v___x_2640_ == 0)
{
lean_object* v___x_2641_; 
lean_dec_ref(v_env_2633_);
lean_dec_ref(v_impl_2631_);
v___x_2641_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2641_, 0, v___x_2639_);
lean_ctor_set(v___x_2641_, 1, v___x_2639_);
lean_ctor_set(v___x_2641_, 2, v___y_2636_);
return v___x_2641_;
}
else
{
uint8_t v___x_2642_; 
v___x_2642_ = lean_nat_dec_le(v___x_2638_, v___x_2638_);
if (v___x_2642_ == 0)
{
if (v___x_2640_ == 0)
{
lean_object* v___x_2643_; 
lean_dec_ref(v_env_2633_);
lean_dec_ref(v_impl_2631_);
v___x_2643_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2643_, 0, v___x_2639_);
lean_ctor_set(v___x_2643_, 1, v___x_2639_);
lean_ctor_set(v___x_2643_, 2, v___y_2636_);
return v___x_2643_;
}
else
{
size_t v___x_2644_; size_t v___x_2645_; lean_object* v___x_2646_; lean_object* v___x_2647_; 
v___x_2644_ = ((size_t)0ULL);
v___x_2645_ = lean_usize_of_nat(v___x_2638_);
v___x_2646_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttribute_spec__0___redArg(v_impl_2631_, v_env_2633_, v___y_2636_, v___x_2644_, v___x_2645_, v___x_2639_);
lean_inc_ref(v___x_2646_);
v___x_2647_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2647_, 0, v___x_2646_);
lean_ctor_set(v___x_2647_, 1, v___x_2646_);
lean_ctor_set(v___x_2647_, 2, v___y_2636_);
return v___x_2647_;
}
}
else
{
size_t v___x_2648_; size_t v___x_2649_; lean_object* v___x_2650_; lean_object* v___x_2651_; 
v___x_2648_ = ((size_t)0ULL);
v___x_2649_ = lean_usize_of_nat(v___x_2638_);
v___x_2650_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttribute_spec__0___redArg(v_impl_2631_, v_env_2633_, v___y_2636_, v___x_2648_, v___x_2649_, v___x_2639_);
lean_inc_ref(v___x_2650_);
v___x_2651_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2651_, 0, v___x_2650_);
lean_ctor_set(v___x_2651_, 1, v___x_2650_);
lean_ctor_set(v___x_2651_, 2, v___y_2636_);
return v___x_2651_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___lam__1___boxed(lean_object* v_impl_2675_, lean_object* v_preserveOrder_2676_, lean_object* v_env_2677_, lean_object* v_x_2678_){
_start:
{
uint8_t v_preserveOrder_boxed_2679_; lean_object* v_res_2680_; 
v_preserveOrder_boxed_2679_ = lean_unbox(v_preserveOrder_2676_);
v_res_2680_ = l_Lean_registerParametricAttribute___redArg___lam__1(v_impl_2675_, v_preserveOrder_boxed_2679_, v_env_2677_, v_x_2678_);
return v_res_2680_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___lam__2(lean_object* v_x_2690_){
_start:
{
lean_object* v_snd_2691_; lean_object* v___x_2693_; uint8_t v_isShared_2694_; uint8_t v_isSharedCheck_2705_; 
v_snd_2691_ = lean_ctor_get(v_x_2690_, 1);
v_isSharedCheck_2705_ = !lean_is_exclusive(v_x_2690_);
if (v_isSharedCheck_2705_ == 0)
{
lean_object* v_unused_2706_; 
v_unused_2706_ = lean_ctor_get(v_x_2690_, 0);
lean_dec(v_unused_2706_);
v___x_2693_ = v_x_2690_;
v_isShared_2694_ = v_isSharedCheck_2705_;
goto v_resetjp_2692_;
}
else
{
lean_inc(v_snd_2691_);
lean_dec(v_x_2690_);
v___x_2693_ = lean_box(0);
v_isShared_2694_ = v_isSharedCheck_2705_;
goto v_resetjp_2692_;
}
v_resetjp_2692_:
{
lean_object* v___x_2695_; lean_object* v___y_2697_; 
v___x_2695_ = ((lean_object*)(l_Lean_registerParametricAttribute___redArg___lam__2___closed__3));
if (lean_obj_tag(v_snd_2691_) == 0)
{
lean_object* v_size_2703_; 
v_size_2703_ = lean_ctor_get(v_snd_2691_, 0);
lean_inc(v_size_2703_);
lean_dec_ref_known(v_snd_2691_, 5);
v___y_2697_ = v_size_2703_;
goto v___jp_2696_;
}
else
{
lean_object* v___x_2704_; 
v___x_2704_ = lean_unsigned_to_nat(0u);
v___y_2697_ = v___x_2704_;
goto v___jp_2696_;
}
v___jp_2696_:
{
lean_object* v___x_2698_; lean_object* v___x_2699_; lean_object* v___x_2701_; 
v___x_2698_ = l_Nat_reprFast(v___y_2697_);
v___x_2699_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2699_, 0, v___x_2698_);
if (v_isShared_2694_ == 0)
{
lean_ctor_set_tag(v___x_2693_, 5);
lean_ctor_set(v___x_2693_, 1, v___x_2699_);
lean_ctor_set(v___x_2693_, 0, v___x_2695_);
v___x_2701_ = v___x_2693_;
goto v_reusejp_2700_;
}
else
{
lean_object* v_reuseFailAlloc_2702_; 
v_reuseFailAlloc_2702_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2702_, 0, v___x_2695_);
lean_ctor_set(v_reuseFailAlloc_2702_, 1, v___x_2699_);
v___x_2701_ = v_reuseFailAlloc_2702_;
goto v_reusejp_2700_;
}
v_reusejp_2700_:
{
return v___x_2701_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___lam__3(lean_object* v_x_2707_){
_start:
{
lean_object* v___x_2708_; 
v___x_2708_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___lam__2___closed__0));
return v___x_2708_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___lam__3___boxed(lean_object* v_x_2709_){
_start:
{
lean_object* v_res_2710_; 
v_res_2710_ = l_Lean_registerParametricAttribute___redArg___lam__3(v_x_2709_);
lean_dec_ref(v_x_2709_);
return v_res_2710_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___lam__4(lean_object* v___x_2711_, lean_object* v_x_2712_, lean_object* v___y_2713_){
_start:
{
lean_object* v___x_2715_; 
v___x_2715_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2715_, 0, v___x_2711_);
return v___x_2715_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___lam__4___boxed(lean_object* v___x_2716_, lean_object* v_x_2717_, lean_object* v___y_2718_, lean_object* v___y_2719_){
_start:
{
lean_object* v_res_2720_; 
v_res_2720_ = l_Lean_registerParametricAttribute___redArg___lam__4(v___x_2716_, v_x_2717_, v___y_2718_);
lean_dec_ref(v___y_2718_);
lean_dec_ref(v_x_2717_);
return v_res_2720_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___lam__5(lean_object* v___x_2721_){
_start:
{
lean_object* v___x_2723_; 
v___x_2723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2723_, 0, v___x_2721_);
return v___x_2723_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___lam__5___boxed(lean_object* v___x_2724_, lean_object* v___y_2725_){
_start:
{
lean_object* v_res_2726_; 
v_res_2726_ = l_Lean_registerParametricAttribute___redArg___lam__5(v___x_2724_);
return v_res_2726_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___lam__7(lean_object* v_getParam_2727_, lean_object* v_a_2728_, lean_object* v_afterSet_2729_, lean_object* v_name_2730_, lean_object* v_decl_2731_, lean_object* v_stx_2732_, uint8_t v_kind_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_){
_start:
{
lean_object* v___y_2738_; lean_object* v___y_2739_; lean_object* v___y_2740_; lean_object* v___y_2741_; uint8_t v___y_2742_; lean_object* v___y_2745_; lean_object* v___y_2746_; lean_object* v___y_2747_; uint8_t v___x_2790_; uint8_t v___x_2791_; 
v___x_2790_ = 0;
v___x_2791_ = l_Lean_instBEqAttributeKind_beq(v_kind_2733_, v___x_2790_);
if (v___x_2791_ == 0)
{
lean_object* v___x_2792_; 
lean_dec(v_stx_2732_);
lean_dec(v_decl_2731_);
lean_dec_ref(v_afterSet_2729_);
lean_dec_ref(v_a_2728_);
lean_dec_ref(v_getParam_2727_);
v___x_2792_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg(v_name_2730_, v_kind_2733_, v___y_2734_, v___y_2735_);
return v___x_2792_;
}
else
{
goto v___jp_2785_;
}
v___jp_2737_:
{
if (v___y_2742_ == 0)
{
lean_object* v___x_2743_; 
lean_dec_ref(v___y_2740_);
v___x_2743_ = l_Lean_setEnv___at___00Lean_registerParametricAttribute_spec__4___redArg(v___y_2741_, v___y_2738_);
return v___x_2743_;
}
else
{
lean_dec_ref(v___y_2741_);
return v___y_2740_;
}
}
v___jp_2744_:
{
lean_object* v___x_2748_; 
lean_inc(v___y_2747_);
lean_inc_ref(v___y_2746_);
lean_inc(v_decl_2731_);
v___x_2748_ = lean_apply_5(v_getParam_2727_, v_decl_2731_, v_stx_2732_, v___y_2746_, v___y_2747_, lean_box(0));
if (lean_obj_tag(v___x_2748_) == 0)
{
lean_object* v_a_2749_; lean_object* v___x_2750_; lean_object* v_toEnvExtension_2751_; lean_object* v_env_2752_; lean_object* v_nextMacroScope_2753_; lean_object* v_ngen_2754_; lean_object* v_auxDeclNGen_2755_; lean_object* v_traceState_2756_; lean_object* v_messages_2757_; lean_object* v_infoState_2758_; lean_object* v_snapshotTasks_2759_; lean_object* v___x_2761_; uint8_t v_isShared_2762_; uint8_t v_isSharedCheck_2775_; 
v_a_2749_ = lean_ctor_get(v___x_2748_, 0);
lean_inc(v_a_2749_);
lean_dec_ref_known(v___x_2748_, 1);
v___x_2750_ = lean_st_ref_take(v___y_2747_);
v_toEnvExtension_2751_ = lean_ctor_get(v_a_2728_, 0);
v_env_2752_ = lean_ctor_get(v___x_2750_, 0);
v_nextMacroScope_2753_ = lean_ctor_get(v___x_2750_, 1);
v_ngen_2754_ = lean_ctor_get(v___x_2750_, 2);
v_auxDeclNGen_2755_ = lean_ctor_get(v___x_2750_, 3);
v_traceState_2756_ = lean_ctor_get(v___x_2750_, 4);
v_messages_2757_ = lean_ctor_get(v___x_2750_, 6);
v_infoState_2758_ = lean_ctor_get(v___x_2750_, 7);
v_snapshotTasks_2759_ = lean_ctor_get(v___x_2750_, 8);
v_isSharedCheck_2775_ = !lean_is_exclusive(v___x_2750_);
if (v_isSharedCheck_2775_ == 0)
{
lean_object* v_unused_2776_; 
v_unused_2776_ = lean_ctor_get(v___x_2750_, 5);
lean_dec(v_unused_2776_);
v___x_2761_ = v___x_2750_;
v_isShared_2762_ = v_isSharedCheck_2775_;
goto v_resetjp_2760_;
}
else
{
lean_inc(v_snapshotTasks_2759_);
lean_inc(v_infoState_2758_);
lean_inc(v_messages_2757_);
lean_inc(v_traceState_2756_);
lean_inc(v_auxDeclNGen_2755_);
lean_inc(v_ngen_2754_);
lean_inc(v_nextMacroScope_2753_);
lean_inc(v_env_2752_);
lean_dec(v___x_2750_);
v___x_2761_ = lean_box(0);
v_isShared_2762_ = v_isSharedCheck_2775_;
goto v_resetjp_2760_;
}
v_resetjp_2760_:
{
lean_object* v_asyncMode_2763_; lean_object* v___x_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; lean_object* v___x_2768_; 
v_asyncMode_2763_ = lean_ctor_get(v_toEnvExtension_2751_, 2);
lean_inc(v_asyncMode_2763_);
lean_inc(v_a_2749_);
lean_inc_n(v_decl_2731_, 2);
v___x_2764_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2764_, 0, v_decl_2731_);
lean_ctor_set(v___x_2764_, 1, v_a_2749_);
v___x_2765_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_a_2728_, v_env_2752_, v___x_2764_, v_asyncMode_2763_, v_decl_2731_);
lean_dec(v_asyncMode_2763_);
v___x_2766_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2);
if (v_isShared_2762_ == 0)
{
lean_ctor_set(v___x_2761_, 5, v___x_2766_);
lean_ctor_set(v___x_2761_, 0, v___x_2765_);
v___x_2768_ = v___x_2761_;
goto v_reusejp_2767_;
}
else
{
lean_object* v_reuseFailAlloc_2774_; 
v_reuseFailAlloc_2774_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2774_, 0, v___x_2765_);
lean_ctor_set(v_reuseFailAlloc_2774_, 1, v_nextMacroScope_2753_);
lean_ctor_set(v_reuseFailAlloc_2774_, 2, v_ngen_2754_);
lean_ctor_set(v_reuseFailAlloc_2774_, 3, v_auxDeclNGen_2755_);
lean_ctor_set(v_reuseFailAlloc_2774_, 4, v_traceState_2756_);
lean_ctor_set(v_reuseFailAlloc_2774_, 5, v___x_2766_);
lean_ctor_set(v_reuseFailAlloc_2774_, 6, v_messages_2757_);
lean_ctor_set(v_reuseFailAlloc_2774_, 7, v_infoState_2758_);
lean_ctor_set(v_reuseFailAlloc_2774_, 8, v_snapshotTasks_2759_);
v___x_2768_ = v_reuseFailAlloc_2774_;
goto v_reusejp_2767_;
}
v_reusejp_2767_:
{
lean_object* v___x_2769_; lean_object* v___x_2770_; 
v___x_2769_ = lean_st_ref_set(v___y_2747_, v___x_2768_);
lean_inc(v___y_2747_);
lean_inc_ref(v___y_2746_);
v___x_2770_ = lean_apply_5(v_afterSet_2729_, v_decl_2731_, v_a_2749_, v___y_2746_, v___y_2747_, lean_box(0));
if (lean_obj_tag(v___x_2770_) == 0)
{
lean_dec_ref(v___y_2745_);
return v___x_2770_;
}
else
{
lean_object* v_a_2771_; uint8_t v___x_2772_; 
v_a_2771_ = lean_ctor_get(v___x_2770_, 0);
lean_inc(v_a_2771_);
v___x_2772_ = l_Lean_Exception_isInterrupt(v_a_2771_);
if (v___x_2772_ == 0)
{
uint8_t v___x_2773_; 
v___x_2773_ = l_Lean_Exception_isRuntime(v_a_2771_);
v___y_2738_ = v___y_2747_;
v___y_2739_ = v___y_2746_;
v___y_2740_ = v___x_2770_;
v___y_2741_ = v___y_2745_;
v___y_2742_ = v___x_2773_;
goto v___jp_2737_;
}
else
{
lean_dec(v_a_2771_);
v___y_2738_ = v___y_2747_;
v___y_2739_ = v___y_2746_;
v___y_2740_ = v___x_2770_;
v___y_2741_ = v___y_2745_;
v___y_2742_ = v___x_2772_;
goto v___jp_2737_;
}
}
}
}
}
else
{
lean_object* v_a_2777_; lean_object* v___x_2779_; uint8_t v_isShared_2780_; uint8_t v_isSharedCheck_2784_; 
lean_dec_ref(v___y_2745_);
lean_dec(v_decl_2731_);
lean_dec_ref(v_afterSet_2729_);
lean_dec_ref(v_a_2728_);
v_a_2777_ = lean_ctor_get(v___x_2748_, 0);
v_isSharedCheck_2784_ = !lean_is_exclusive(v___x_2748_);
if (v_isSharedCheck_2784_ == 0)
{
v___x_2779_ = v___x_2748_;
v_isShared_2780_ = v_isSharedCheck_2784_;
goto v_resetjp_2778_;
}
else
{
lean_inc(v_a_2777_);
lean_dec(v___x_2748_);
v___x_2779_ = lean_box(0);
v_isShared_2780_ = v_isSharedCheck_2784_;
goto v_resetjp_2778_;
}
v_resetjp_2778_:
{
lean_object* v___x_2782_; 
if (v_isShared_2780_ == 0)
{
v___x_2782_ = v___x_2779_;
goto v_reusejp_2781_;
}
else
{
lean_object* v_reuseFailAlloc_2783_; 
v_reuseFailAlloc_2783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2783_, 0, v_a_2777_);
v___x_2782_ = v_reuseFailAlloc_2783_;
goto v_reusejp_2781_;
}
v_reusejp_2781_:
{
return v___x_2782_;
}
}
}
}
v___jp_2785_:
{
lean_object* v___x_2786_; lean_object* v_env_2787_; lean_object* v___x_2788_; 
v___x_2786_ = lean_st_ref_get(v___y_2735_);
v_env_2787_ = lean_ctor_get(v___x_2786_, 0);
lean_inc_ref(v_env_2787_);
lean_dec(v___x_2786_);
v___x_2788_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2787_, v_decl_2731_);
if (lean_obj_tag(v___x_2788_) == 0)
{
lean_dec(v_name_2730_);
v___y_2745_ = v_env_2787_;
v___y_2746_ = v___y_2734_;
v___y_2747_ = v___y_2735_;
goto v___jp_2744_;
}
else
{
lean_object* v___x_2789_; 
lean_dec_ref_known(v___x_2788_, 1);
lean_dec_ref(v_env_2787_);
lean_dec(v_stx_2732_);
lean_dec_ref(v_afterSet_2729_);
lean_dec_ref(v_a_2728_);
lean_dec_ref(v_getParam_2727_);
v___x_2789_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg(v_name_2730_, v_decl_2731_, v___y_2734_, v___y_2735_);
return v___x_2789_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___lam__7___boxed(lean_object* v_getParam_2793_, lean_object* v_a_2794_, lean_object* v_afterSet_2795_, lean_object* v_name_2796_, lean_object* v_decl_2797_, lean_object* v_stx_2798_, lean_object* v_kind_2799_, lean_object* v___y_2800_, lean_object* v___y_2801_, lean_object* v___y_2802_){
_start:
{
uint8_t v_kind_boxed_2803_; lean_object* v_res_2804_; 
v_kind_boxed_2803_ = lean_unbox(v_kind_2799_);
v_res_2804_ = l_Lean_registerParametricAttribute___redArg___lam__7(v_getParam_2793_, v_a_2794_, v_afterSet_2795_, v_name_2796_, v_decl_2797_, v_stx_2798_, v_kind_boxed_2803_, v___y_2800_, v___y_2801_);
lean_dec(v___y_2801_);
lean_dec_ref(v___y_2800_);
return v_res_2804_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg(lean_object* v_impl_2815_){
_start:
{
lean_object* v_toAttributeImplCore_2817_; lean_object* v_getParam_2818_; lean_object* v_afterSet_2819_; uint8_t v_preserveOrder_2820_; lean_object* v_ref_2821_; lean_object* v_name_2822_; lean_object* v___f_2823_; lean_object* v___x_2824_; lean_object* v___f_2825_; lean_object* v___f_2826_; lean_object* v___f_2827_; lean_object* v___f_2828_; lean_object* v___f_2829_; lean_object* v___x_2830_; lean_object* v___x_2831_; lean_object* v___x_2832_; lean_object* v___x_2833_; lean_object* v___x_2834_; 
v_toAttributeImplCore_2817_ = lean_ctor_get(v_impl_2815_, 0);
lean_inc_ref(v_toAttributeImplCore_2817_);
v_getParam_2818_ = lean_ctor_get(v_impl_2815_, 1);
lean_inc_ref(v_getParam_2818_);
v_afterSet_2819_ = lean_ctor_get(v_impl_2815_, 2);
lean_inc_ref(v_afterSet_2819_);
v_preserveOrder_2820_ = lean_ctor_get_uint8(v_impl_2815_, sizeof(void*)*4);
v_ref_2821_ = lean_ctor_get(v_toAttributeImplCore_2817_, 0);
v_name_2822_ = lean_ctor_get(v_toAttributeImplCore_2817_, 1);
v___f_2823_ = ((lean_object*)(l_Lean_registerParametricAttribute___redArg___closed__0));
v___x_2824_ = lean_box(v_preserveOrder_2820_);
v___f_2825_ = lean_alloc_closure((void*)(l_Lean_registerParametricAttribute___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_2825_, 0, v_impl_2815_);
lean_closure_set(v___f_2825_, 1, v___x_2824_);
v___f_2826_ = ((lean_object*)(l_Lean_registerParametricAttribute___redArg___closed__1));
v___f_2827_ = ((lean_object*)(l_Lean_registerParametricAttribute___redArg___closed__2));
v___f_2828_ = ((lean_object*)(l_Lean_registerParametricAttribute___redArg___closed__4));
v___f_2829_ = ((lean_object*)(l_Lean_registerParametricAttribute___redArg___closed__5));
v___x_2830_ = lean_box(2);
v___x_2831_ = lean_box(0);
lean_inc(v_ref_2821_);
v___x_2832_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_2832_, 0, v_ref_2821_);
lean_ctor_set(v___x_2832_, 1, v___f_2829_);
lean_ctor_set(v___x_2832_, 2, v___f_2828_);
lean_ctor_set(v___x_2832_, 3, v___f_2823_);
lean_ctor_set(v___x_2832_, 4, v___f_2825_);
lean_ctor_set(v___x_2832_, 5, v___f_2826_);
lean_ctor_set(v___x_2832_, 6, v___x_2830_);
lean_ctor_set(v___x_2832_, 7, v___x_2831_);
v___x_2833_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2833_, 0, v___x_2832_);
lean_ctor_set(v___x_2833_, 1, v___f_2827_);
v___x_2834_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_2833_);
if (lean_obj_tag(v___x_2834_) == 0)
{
lean_object* v_a_2835_; lean_object* v___f_2836_; lean_object* v___f_2837_; lean_object* v___x_2838_; lean_object* v___x_2839_; 
v_a_2835_ = lean_ctor_get(v___x_2834_, 0);
lean_inc_n(v_a_2835_, 2);
lean_dec_ref_known(v___x_2834_, 1);
lean_inc_n(v_name_2822_, 2);
v___f_2836_ = lean_alloc_closure((void*)(l_Lean_registerTagAttribute___lam__6___boxed), 5, 1);
lean_closure_set(v___f_2836_, 0, v_name_2822_);
v___f_2837_ = lean_alloc_closure((void*)(l_Lean_registerParametricAttribute___redArg___lam__7___boxed), 10, 4);
lean_closure_set(v___f_2837_, 0, v_getParam_2818_);
lean_closure_set(v___f_2837_, 1, v_a_2835_);
lean_closure_set(v___f_2837_, 2, v_afterSet_2819_);
lean_closure_set(v___f_2837_, 3, v_name_2822_);
v___x_2838_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2838_, 0, v_toAttributeImplCore_2817_);
lean_ctor_set(v___x_2838_, 1, v___f_2837_);
lean_ctor_set(v___x_2838_, 2, v___f_2836_);
lean_inc_ref(v___x_2838_);
v___x_2839_ = l_Lean_registerBuiltinAttribute(v___x_2838_);
if (lean_obj_tag(v___x_2839_) == 0)
{
lean_object* v___x_2841_; uint8_t v_isShared_2842_; uint8_t v_isSharedCheck_2847_; 
v_isSharedCheck_2847_ = !lean_is_exclusive(v___x_2839_);
if (v_isSharedCheck_2847_ == 0)
{
lean_object* v_unused_2848_; 
v_unused_2848_ = lean_ctor_get(v___x_2839_, 0);
lean_dec(v_unused_2848_);
v___x_2841_ = v___x_2839_;
v_isShared_2842_ = v_isSharedCheck_2847_;
goto v_resetjp_2840_;
}
else
{
lean_dec(v___x_2839_);
v___x_2841_ = lean_box(0);
v_isShared_2842_ = v_isSharedCheck_2847_;
goto v_resetjp_2840_;
}
v_resetjp_2840_:
{
lean_object* v___x_2843_; lean_object* v___x_2845_; 
v___x_2843_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2843_, 0, v___x_2838_);
lean_ctor_set(v___x_2843_, 1, v_a_2835_);
lean_ctor_set_uint8(v___x_2843_, sizeof(void*)*2, v_preserveOrder_2820_);
if (v_isShared_2842_ == 0)
{
lean_ctor_set(v___x_2841_, 0, v___x_2843_);
v___x_2845_ = v___x_2841_;
goto v_reusejp_2844_;
}
else
{
lean_object* v_reuseFailAlloc_2846_; 
v_reuseFailAlloc_2846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2846_, 0, v___x_2843_);
v___x_2845_ = v_reuseFailAlloc_2846_;
goto v_reusejp_2844_;
}
v_reusejp_2844_:
{
return v___x_2845_;
}
}
}
else
{
lean_object* v_a_2849_; lean_object* v___x_2851_; uint8_t v_isShared_2852_; uint8_t v_isSharedCheck_2856_; 
lean_dec_ref_known(v___x_2838_, 3);
lean_dec(v_a_2835_);
v_a_2849_ = lean_ctor_get(v___x_2839_, 0);
v_isSharedCheck_2856_ = !lean_is_exclusive(v___x_2839_);
if (v_isSharedCheck_2856_ == 0)
{
v___x_2851_ = v___x_2839_;
v_isShared_2852_ = v_isSharedCheck_2856_;
goto v_resetjp_2850_;
}
else
{
lean_inc(v_a_2849_);
lean_dec(v___x_2839_);
v___x_2851_ = lean_box(0);
v_isShared_2852_ = v_isSharedCheck_2856_;
goto v_resetjp_2850_;
}
v_resetjp_2850_:
{
lean_object* v___x_2854_; 
if (v_isShared_2852_ == 0)
{
v___x_2854_ = v___x_2851_;
goto v_reusejp_2853_;
}
else
{
lean_object* v_reuseFailAlloc_2855_; 
v_reuseFailAlloc_2855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2855_, 0, v_a_2849_);
v___x_2854_ = v_reuseFailAlloc_2855_;
goto v_reusejp_2853_;
}
v_reusejp_2853_:
{
return v___x_2854_;
}
}
}
}
else
{
lean_object* v_a_2857_; lean_object* v___x_2859_; uint8_t v_isShared_2860_; uint8_t v_isSharedCheck_2864_; 
lean_dec_ref(v_afterSet_2819_);
lean_dec_ref(v_getParam_2818_);
lean_dec_ref(v_toAttributeImplCore_2817_);
v_a_2857_ = lean_ctor_get(v___x_2834_, 0);
v_isSharedCheck_2864_ = !lean_is_exclusive(v___x_2834_);
if (v_isSharedCheck_2864_ == 0)
{
v___x_2859_ = v___x_2834_;
v_isShared_2860_ = v_isSharedCheck_2864_;
goto v_resetjp_2858_;
}
else
{
lean_inc(v_a_2857_);
lean_dec(v___x_2834_);
v___x_2859_ = lean_box(0);
v_isShared_2860_ = v_isSharedCheck_2864_;
goto v_resetjp_2858_;
}
v_resetjp_2858_:
{
lean_object* v___x_2862_; 
if (v_isShared_2860_ == 0)
{
v___x_2862_ = v___x_2859_;
goto v_reusejp_2861_;
}
else
{
lean_object* v_reuseFailAlloc_2863_; 
v_reuseFailAlloc_2863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2863_, 0, v_a_2857_);
v___x_2862_ = v_reuseFailAlloc_2863_;
goto v_reusejp_2861_;
}
v_reusejp_2861_:
{
return v___x_2862_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___boxed(lean_object* v_impl_2865_, lean_object* v_a_2866_){
_start:
{
lean_object* v_res_2867_; 
v_res_2867_ = l_Lean_registerParametricAttribute___redArg(v_impl_2865_);
return v_res_2867_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute(lean_object* v_00_u03b1_2868_, lean_object* v_impl_2869_){
_start:
{
lean_object* v___x_2871_; 
v___x_2871_ = l_Lean_registerParametricAttribute___redArg(v_impl_2869_);
return v___x_2871_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___boxed(lean_object* v_00_u03b1_2872_, lean_object* v_impl_2873_, lean_object* v_a_2874_){
_start:
{
lean_object* v_res_2875_; 
v_res_2875_ = l_Lean_registerParametricAttribute(v_00_u03b1_2872_, v_impl_2873_);
return v_res_2875_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttribute_spec__0(lean_object* v_00_u03b1_2876_, lean_object* v_impl_2877_, lean_object* v_env_2878_, lean_object* v_as_2879_, size_t v_i_2880_, size_t v_stop_2881_, lean_object* v_b_2882_){
_start:
{
lean_object* v___x_2883_; 
v___x_2883_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttribute_spec__0___redArg(v_impl_2877_, v_env_2878_, v_as_2879_, v_i_2880_, v_stop_2881_, v_b_2882_);
return v___x_2883_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttribute_spec__0___boxed(lean_object* v_00_u03b1_2884_, lean_object* v_impl_2885_, lean_object* v_env_2886_, lean_object* v_as_2887_, lean_object* v_i_2888_, lean_object* v_stop_2889_, lean_object* v_b_2890_){
_start:
{
size_t v_i_boxed_2891_; size_t v_stop_boxed_2892_; lean_object* v_res_2893_; 
v_i_boxed_2891_ = lean_unbox_usize(v_i_2888_);
lean_dec(v_i_2888_);
v_stop_boxed_2892_ = lean_unbox_usize(v_stop_2889_);
lean_dec(v_stop_2889_);
v_res_2893_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttribute_spec__0(v_00_u03b1_2884_, v_impl_2885_, v_env_2886_, v_as_2887_, v_i_boxed_2891_, v_stop_boxed_2892_, v_b_2890_);
lean_dec_ref(v_as_2887_);
return v_res_2893_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1___redArg(lean_object* v_init_2894_, lean_object* v_t_2895_){
_start:
{
lean_object* v___x_2896_; 
v___x_2896_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1_spec__1___redArg(v_init_2894_, v_t_2895_);
return v___x_2896_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1___redArg___boxed(lean_object* v_init_2897_, lean_object* v_t_2898_){
_start:
{
lean_object* v_res_2899_; 
v_res_2899_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1___redArg(v_init_2897_, v_t_2898_);
lean_dec(v_t_2898_);
return v_res_2899_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1(lean_object* v_00_u03b1_2900_, lean_object* v_init_2901_, lean_object* v_t_2902_){
_start:
{
lean_object* v___x_2903_; 
v___x_2903_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1_spec__1___redArg(v_init_2901_, v_t_2902_);
return v___x_2903_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1___boxed(lean_object* v_00_u03b1_2904_, lean_object* v_init_2905_, lean_object* v_t_2906_){
_start:
{
lean_object* v_res_2907_; 
v_res_2907_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1(v_00_u03b1_2904_, v_init_2905_, v_t_2906_);
lean_dec(v_t_2906_);
return v_res_2907_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2(lean_object* v_00_u03b1_2908_, lean_object* v_n_2909_, lean_object* v_as_2910_, lean_object* v_lo_2911_, lean_object* v_hi_2912_, lean_object* v_w_2913_, lean_object* v_hlo_2914_, lean_object* v_hhi_2915_){
_start:
{
lean_object* v___x_2916_; 
v___x_2916_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2___redArg(v_n_2909_, v_as_2910_, v_lo_2911_, v_hi_2912_);
return v___x_2916_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2___boxed(lean_object* v_00_u03b1_2917_, lean_object* v_n_2918_, lean_object* v_as_2919_, lean_object* v_lo_2920_, lean_object* v_hi_2921_, lean_object* v_w_2922_, lean_object* v_hlo_2923_, lean_object* v_hhi_2924_){
_start:
{
lean_object* v_res_2925_; 
v_res_2925_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2(v_00_u03b1_2917_, v_n_2918_, v_as_2919_, v_lo_2920_, v_hi_2921_, v_w_2922_, v_hlo_2923_, v_hhi_2924_);
lean_dec(v_hi_2921_);
lean_dec(v_n_2918_);
return v_res_2925_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3(lean_object* v_00_u03b1_2926_, lean_object* v_snd_2927_, lean_object* v_as_2928_, lean_object* v_start_2929_, lean_object* v_stop_2930_){
_start:
{
lean_object* v___x_2931_; 
v___x_2931_ = l_Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3___redArg(v_snd_2927_, v_as_2928_, v_start_2929_, v_stop_2930_);
return v___x_2931_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3___boxed(lean_object* v_00_u03b1_2932_, lean_object* v_snd_2933_, lean_object* v_as_2934_, lean_object* v_start_2935_, lean_object* v_stop_2936_){
_start:
{
lean_object* v_res_2937_; 
v_res_2937_ = l_Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3(v_00_u03b1_2932_, v_snd_2933_, v_as_2934_, v_start_2935_, v_stop_2936_);
lean_dec(v_stop_2936_);
lean_dec(v_start_2935_);
lean_dec_ref(v_as_2934_);
lean_dec(v_snd_2933_);
return v_res_2937_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1_spec__1(lean_object* v_00_u03b1_2938_, lean_object* v_init_2939_, lean_object* v_x_2940_){
_start:
{
lean_object* v___x_2941_; 
v___x_2941_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1_spec__1___redArg(v_init_2939_, v_x_2940_);
return v___x_2941_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1_spec__1___boxed(lean_object* v_00_u03b1_2942_, lean_object* v_init_2943_, lean_object* v_x_2944_){
_start:
{
lean_object* v_res_2945_; 
v_res_2945_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1_spec__1(v_00_u03b1_2942_, v_init_2943_, v_x_2944_);
lean_dec(v_x_2944_);
return v_res_2945_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2_spec__3(lean_object* v_00_u03b1_2946_, lean_object* v_n_2947_, lean_object* v_lo_2948_, lean_object* v_hi_2949_, lean_object* v_hhi_2950_, lean_object* v_pivot_2951_, lean_object* v_as_2952_, lean_object* v_i_2953_, lean_object* v_k_2954_, lean_object* v_ilo_2955_, lean_object* v_ik_2956_, lean_object* v_w_2957_){
_start:
{
lean_object* v___x_2958_; 
v___x_2958_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2_spec__3___redArg(v_hi_2949_, v_pivot_2951_, v_as_2952_, v_i_2953_, v_k_2954_);
return v___x_2958_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2_spec__3___boxed(lean_object* v_00_u03b1_2959_, lean_object* v_n_2960_, lean_object* v_lo_2961_, lean_object* v_hi_2962_, lean_object* v_hhi_2963_, lean_object* v_pivot_2964_, lean_object* v_as_2965_, lean_object* v_i_2966_, lean_object* v_k_2967_, lean_object* v_ilo_2968_, lean_object* v_ik_2969_, lean_object* v_w_2970_){
_start:
{
lean_object* v_res_2971_; 
v_res_2971_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2_spec__3(v_00_u03b1_2959_, v_n_2960_, v_lo_2961_, v_hi_2962_, v_hhi_2963_, v_pivot_2964_, v_as_2965_, v_i_2966_, v_k_2967_, v_ilo_2968_, v_ik_2969_, v_w_2970_);
lean_dec_ref(v_pivot_2964_);
lean_dec(v_hi_2962_);
lean_dec(v_lo_2961_);
lean_dec(v_n_2960_);
return v_res_2971_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3_spec__5(lean_object* v_00_u03b1_2972_, lean_object* v_snd_2973_, lean_object* v_as_2974_, size_t v_i_2975_, size_t v_stop_2976_, lean_object* v_b_2977_){
_start:
{
lean_object* v___x_2978_; 
v___x_2978_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3_spec__5___redArg(v_snd_2973_, v_as_2974_, v_i_2975_, v_stop_2976_, v_b_2977_);
return v___x_2978_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3_spec__5___boxed(lean_object* v_00_u03b1_2979_, lean_object* v_snd_2980_, lean_object* v_as_2981_, lean_object* v_i_2982_, lean_object* v_stop_2983_, lean_object* v_b_2984_){
_start:
{
size_t v_i_boxed_2985_; size_t v_stop_boxed_2986_; lean_object* v_res_2987_; 
v_i_boxed_2985_ = lean_unbox_usize(v_i_2982_);
lean_dec(v_i_2982_);
v_stop_boxed_2986_ = lean_unbox_usize(v_stop_2983_);
lean_dec(v_stop_2983_);
v_res_2987_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttribute_spec__3_spec__5(v_00_u03b1_2979_, v_snd_2980_, v_as_2981_, v_i_boxed_2985_, v_stop_boxed_2986_, v_b_2984_);
lean_dec_ref(v_as_2981_);
lean_dec(v_snd_2980_);
return v_res_2987_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParam_x3f___redArg___lam__1(lean_object* v_decl_2988_, lean_object* v___x_2989_, lean_object* v___x_2990_, lean_object* v_a_2991_, lean_object* v_x_2992_, lean_object* v___y_2993_){
_start:
{
lean_object* v_fst_2994_; uint8_t v___x_2995_; 
v_fst_2994_ = lean_ctor_get(v_a_2991_, 0);
v___x_2995_ = lean_name_eq(v_fst_2994_, v_decl_2988_);
if (v___x_2995_ == 0)
{
lean_object* v___x_2996_; 
lean_dec_ref(v_a_2991_);
v___x_2996_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2996_, 0, v___x_2989_);
return v___x_2996_;
}
else
{
lean_object* v___x_2997_; lean_object* v___x_2998_; lean_object* v___x_2999_; lean_object* v___x_3000_; 
lean_dec_ref(v___x_2989_);
v___x_2997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2997_, 0, v_a_2991_);
v___x_2998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2998_, 0, v___x_2997_);
v___x_2999_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2999_, 0, v___x_2998_);
lean_ctor_set(v___x_2999_, 1, v___x_2990_);
v___x_3000_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3000_, 0, v___x_2999_);
return v___x_3000_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParam_x3f___redArg___lam__1___boxed(lean_object* v_decl_3001_, lean_object* v___x_3002_, lean_object* v___x_3003_, lean_object* v_a_3004_, lean_object* v_x_3005_, lean_object* v___y_3006_){
_start:
{
lean_object* v_res_3007_; 
v_res_3007_ = l_Lean_ParametricAttribute_getParam_x3f___redArg___lam__1(v_decl_3001_, v___x_3002_, v___x_3003_, v_a_3004_, v_x_3005_, v___y_3006_);
lean_dec_ref(v___y_3006_);
lean_dec(v_decl_3001_);
return v_res_3007_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParam_x3f___redArg(lean_object* v_inst_3035_, lean_object* v_attr_3036_, lean_object* v_env_3037_, lean_object* v_decl_3038_){
_start:
{
lean_object* v___y_3040_; lean_object* v___x_3051_; lean_object* v___x_3052_; 
v___x_3051_ = ((lean_object*)(l_Lean_ParametricAttribute_getParam_x3f___redArg___closed__0));
v___x_3052_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3037_, v_decl_3038_);
if (lean_obj_tag(v___x_3052_) == 0)
{
lean_object* v_ext_3053_; lean_object* v_toEnvExtension_3054_; lean_object* v_asyncMode_3055_; lean_object* v___x_3056_; lean_object* v___x_3057_; lean_object* v_snd_3058_; lean_object* v___x_3059_; 
lean_dec(v_inst_3035_);
v_ext_3053_ = lean_ctor_get(v_attr_3036_, 1);
v_toEnvExtension_3054_ = lean_ctor_get(v_ext_3053_, 0);
v_asyncMode_3055_ = lean_ctor_get(v_toEnvExtension_3054_, 2);
v___x_3056_ = lean_box(0);
v___x_3057_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3051_, v_ext_3053_, v_env_3037_, v_asyncMode_3055_, v___x_3056_);
v_snd_3058_ = lean_ctor_get(v___x_3057_, 1);
lean_inc(v_snd_3058_);
lean_dec(v___x_3057_);
v___x_3059_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_snd_3058_, v_decl_3038_);
lean_dec(v_decl_3038_);
lean_dec(v_snd_3058_);
return v___x_3059_;
}
else
{
uint8_t v_preserveOrder_3060_; 
v_preserveOrder_3060_ = lean_ctor_get_uint8(v_attr_3036_, sizeof(void*)*2);
if (v_preserveOrder_3060_ == 0)
{
lean_object* v_val_3061_; lean_object* v_ext_3062_; uint8_t v___x_3063_; lean_object* v___x_3064_; lean_object* v___x_3065_; lean_object* v___x_3066_; uint8_t v___x_3067_; 
v_val_3061_ = lean_ctor_get(v___x_3052_, 0);
lean_inc(v_val_3061_);
lean_dec_ref_known(v___x_3052_, 1);
v_ext_3062_ = lean_ctor_get(v_attr_3036_, 1);
v___x_3063_ = 0;
v___x_3064_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_3051_, v_ext_3062_, v_env_3037_, v_val_3061_, v___x_3063_);
lean_dec(v_val_3061_);
lean_dec_ref(v_env_3037_);
v___x_3065_ = lean_unsigned_to_nat(0u);
v___x_3066_ = lean_array_get_size(v___x_3064_);
v___x_3067_ = lean_nat_dec_lt(v___x_3065_, v___x_3066_);
if (v___x_3067_ == 0)
{
lean_object* v___x_3068_; 
lean_dec_ref(v___x_3064_);
lean_dec(v_decl_3038_);
lean_dec(v_inst_3035_);
v___x_3068_ = lean_box(0);
return v___x_3068_;
}
else
{
lean_object* v___x_3069_; lean_object* v___x_3070_; uint8_t v___x_3071_; 
v___x_3069_ = lean_unsigned_to_nat(1u);
v___x_3070_ = lean_nat_sub(v___x_3066_, v___x_3069_);
v___x_3071_ = lean_nat_dec_le(v___x_3065_, v___x_3070_);
if (v___x_3071_ == 0)
{
lean_object* v___x_3072_; 
lean_dec(v___x_3070_);
lean_dec_ref(v___x_3064_);
lean_dec(v_decl_3038_);
lean_dec(v_inst_3035_);
v___x_3072_ = lean_box(0);
return v___x_3072_;
}
else
{
lean_object* v___f_3073_; lean_object* v___x_3074_; lean_object* v___x_3075_; lean_object* v___x_3076_; 
v___f_3073_ = ((lean_object*)(l_Lean_ParametricAttribute_getParam_x3f___redArg___closed__1));
v___x_3074_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3074_, 0, v_decl_3038_);
lean_ctor_set(v___x_3074_, 1, v_inst_3035_);
v___x_3075_ = ((lean_object*)(l_Lean_ParametricAttribute_getParam_x3f___redArg___closed__2));
v___x_3076_ = l_Array_binSearchAux___redArg(v___f_3073_, v___x_3075_, v___x_3064_, v___x_3074_, v___x_3065_, v___x_3070_);
lean_dec_ref(v___x_3064_);
v___y_3040_ = v___x_3076_;
goto v___jp_3039_;
}
}
}
else
{
lean_object* v_val_3077_; lean_object* v_ext_3078_; uint8_t v___x_3079_; lean_object* v___x_3080_; lean_object* v___x_3081_; lean_object* v___x_3082_; lean_object* v___x_3083_; lean_object* v___x_3084_; lean_object* v___f_3085_; size_t v_sz_3086_; size_t v___x_3087_; lean_object* v___x_3088_; lean_object* v_fst_3089_; 
lean_dec(v_inst_3035_);
v_val_3077_ = lean_ctor_get(v___x_3052_, 0);
lean_inc(v_val_3077_);
lean_dec_ref_known(v___x_3052_, 1);
v_ext_3078_ = lean_ctor_get(v_attr_3036_, 1);
v___x_3079_ = 0;
v___x_3080_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_3051_, v_ext_3078_, v_env_3037_, v_val_3077_, v___x_3079_);
lean_dec(v_val_3077_);
lean_dec_ref(v_env_3037_);
v___x_3081_ = ((lean_object*)(l_Lean_ParametricAttribute_getParam_x3f___redArg___closed__12));
v___x_3082_ = lean_box(0);
v___x_3083_ = lean_box(0);
v___x_3084_ = ((lean_object*)(l_Lean_ParametricAttribute_getParam_x3f___redArg___closed__13));
v___f_3085_ = lean_alloc_closure((void*)(l_Lean_ParametricAttribute_getParam_x3f___redArg___lam__1___boxed), 6, 3);
lean_closure_set(v___f_3085_, 0, v_decl_3038_);
lean_closure_set(v___f_3085_, 1, v___x_3084_);
lean_closure_set(v___f_3085_, 2, v___x_3083_);
v_sz_3086_ = lean_array_size(v___x_3080_);
v___x_3087_ = ((size_t)0ULL);
v___x_3088_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_3081_, v___x_3080_, v___f_3085_, v_sz_3086_, v___x_3087_, v___x_3084_);
v_fst_3089_ = lean_ctor_get(v___x_3088_, 0);
lean_inc(v_fst_3089_);
lean_dec(v___x_3088_);
if (lean_obj_tag(v_fst_3089_) == 0)
{
return v___x_3082_;
}
else
{
lean_object* v_val_3090_; 
v_val_3090_ = lean_ctor_get(v_fst_3089_, 0);
lean_inc(v_val_3090_);
lean_dec_ref_known(v_fst_3089_, 1);
v___y_3040_ = v_val_3090_;
goto v___jp_3039_;
}
}
}
v___jp_3039_:
{
if (lean_obj_tag(v___y_3040_) == 0)
{
lean_object* v___x_3041_; 
v___x_3041_ = lean_box(0);
return v___x_3041_;
}
else
{
lean_object* v_val_3042_; lean_object* v___x_3044_; uint8_t v_isShared_3045_; uint8_t v_isSharedCheck_3050_; 
v_val_3042_ = lean_ctor_get(v___y_3040_, 0);
v_isSharedCheck_3050_ = !lean_is_exclusive(v___y_3040_);
if (v_isSharedCheck_3050_ == 0)
{
v___x_3044_ = v___y_3040_;
v_isShared_3045_ = v_isSharedCheck_3050_;
goto v_resetjp_3043_;
}
else
{
lean_inc(v_val_3042_);
lean_dec(v___y_3040_);
v___x_3044_ = lean_box(0);
v_isShared_3045_ = v_isSharedCheck_3050_;
goto v_resetjp_3043_;
}
v_resetjp_3043_:
{
lean_object* v_snd_3046_; lean_object* v___x_3048_; 
v_snd_3046_ = lean_ctor_get(v_val_3042_, 1);
lean_inc(v_snd_3046_);
lean_dec(v_val_3042_);
if (v_isShared_3045_ == 0)
{
lean_ctor_set(v___x_3044_, 0, v_snd_3046_);
v___x_3048_ = v___x_3044_;
goto v_reusejp_3047_;
}
else
{
lean_object* v_reuseFailAlloc_3049_; 
v_reuseFailAlloc_3049_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3049_, 0, v_snd_3046_);
v___x_3048_ = v_reuseFailAlloc_3049_;
goto v_reusejp_3047_;
}
v_reusejp_3047_:
{
return v___x_3048_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParam_x3f___redArg___boxed(lean_object* v_inst_3091_, lean_object* v_attr_3092_, lean_object* v_env_3093_, lean_object* v_decl_3094_){
_start:
{
lean_object* v_res_3095_; 
v_res_3095_ = l_Lean_ParametricAttribute_getParam_x3f___redArg(v_inst_3091_, v_attr_3092_, v_env_3093_, v_decl_3094_);
lean_dec_ref(v_attr_3092_);
return v_res_3095_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParam_x3f(lean_object* v_00_u03b1_3096_, lean_object* v_inst_3097_, lean_object* v_attr_3098_, lean_object* v_env_3099_, lean_object* v_decl_3100_){
_start:
{
lean_object* v___x_3101_; 
v___x_3101_ = l_Lean_ParametricAttribute_getParam_x3f___redArg(v_inst_3097_, v_attr_3098_, v_env_3099_, v_decl_3100_);
return v___x_3101_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParam_x3f___boxed(lean_object* v_00_u03b1_3102_, lean_object* v_inst_3103_, lean_object* v_attr_3104_, lean_object* v_env_3105_, lean_object* v_decl_3106_){
_start:
{
lean_object* v_res_3107_; 
v_res_3107_ = l_Lean_ParametricAttribute_getParam_x3f(v_00_u03b1_3102_, v_inst_3103_, v_attr_3104_, v_env_3105_, v_decl_3106_);
lean_dec_ref(v_attr_3104_);
return v_res_3107_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_setParam___redArg(lean_object* v_attr_3112_, lean_object* v_env_3113_, lean_object* v_decl_3114_, lean_object* v_param_3115_){
_start:
{
lean_object* v___x_3116_; 
v___x_3116_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3113_, v_decl_3114_);
if (lean_obj_tag(v___x_3116_) == 0)
{
lean_object* v_ext_3117_; lean_object* v_toEnvExtension_3118_; lean_object* v_attr_3119_; lean_object* v_asyncMode_3120_; lean_object* v___x_3121_; lean_object* v___x_3122_; lean_object* v___x_3123_; lean_object* v_snd_3124_; lean_object* v___x_3126_; uint8_t v_isShared_3127_; uint8_t v_isSharedCheck_3154_; 
v_ext_3117_ = lean_ctor_get(v_attr_3112_, 1);
lean_inc_ref(v_ext_3117_);
v_toEnvExtension_3118_ = lean_ctor_get(v_ext_3117_, 0);
v_attr_3119_ = lean_ctor_get(v_attr_3112_, 0);
lean_inc_ref(v_attr_3119_);
lean_dec_ref(v_attr_3112_);
v_asyncMode_3120_ = lean_ctor_get(v_toEnvExtension_3118_, 2);
lean_inc(v_asyncMode_3120_);
v___x_3121_ = ((lean_object*)(l_Lean_ParametricAttribute_getParam_x3f___redArg___closed__0));
v___x_3122_ = lean_box(0);
lean_inc_ref(v_env_3113_);
v___x_3123_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3121_, v_ext_3117_, v_env_3113_, v_asyncMode_3120_, v___x_3122_);
v_snd_3124_ = lean_ctor_get(v___x_3123_, 1);
v_isSharedCheck_3154_ = !lean_is_exclusive(v___x_3123_);
if (v_isSharedCheck_3154_ == 0)
{
lean_object* v_unused_3155_; 
v_unused_3155_ = lean_ctor_get(v___x_3123_, 0);
lean_dec(v_unused_3155_);
v___x_3126_ = v___x_3123_;
v_isShared_3127_ = v_isSharedCheck_3154_;
goto v_resetjp_3125_;
}
else
{
lean_inc(v_snd_3124_);
lean_dec(v___x_3123_);
v___x_3126_ = lean_box(0);
v_isShared_3127_ = v_isSharedCheck_3154_;
goto v_resetjp_3125_;
}
v_resetjp_3125_:
{
lean_object* v___x_3128_; 
v___x_3128_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_snd_3124_, v_decl_3114_);
lean_dec(v_snd_3124_);
if (lean_obj_tag(v___x_3128_) == 0)
{
lean_object* v___x_3130_; 
lean_dec_ref(v_attr_3119_);
if (v_isShared_3127_ == 0)
{
lean_ctor_set(v___x_3126_, 1, v_param_3115_);
lean_ctor_set(v___x_3126_, 0, v_decl_3114_);
v___x_3130_ = v___x_3126_;
goto v_reusejp_3129_;
}
else
{
lean_object* v_reuseFailAlloc_3133_; 
v_reuseFailAlloc_3133_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3133_, 0, v_decl_3114_);
lean_ctor_set(v_reuseFailAlloc_3133_, 1, v_param_3115_);
v___x_3130_ = v_reuseFailAlloc_3133_;
goto v_reusejp_3129_;
}
v_reusejp_3129_:
{
lean_object* v___x_3131_; lean_object* v___x_3132_; 
v___x_3131_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_ext_3117_, v_env_3113_, v___x_3130_, v_asyncMode_3120_, v___x_3122_);
lean_dec(v_asyncMode_3120_);
v___x_3132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3132_, 0, v___x_3131_);
return v___x_3132_;
}
}
else
{
lean_object* v___x_3135_; uint8_t v_isShared_3136_; uint8_t v_isSharedCheck_3152_; 
lean_del_object(v___x_3126_);
lean_dec(v_asyncMode_3120_);
lean_dec_ref(v_ext_3117_);
lean_dec(v_param_3115_);
lean_dec_ref(v_env_3113_);
v_isSharedCheck_3152_ = !lean_is_exclusive(v___x_3128_);
if (v_isSharedCheck_3152_ == 0)
{
lean_object* v_unused_3153_; 
v_unused_3153_ = lean_ctor_get(v___x_3128_, 0);
lean_dec(v_unused_3153_);
v___x_3135_ = v___x_3128_;
v_isShared_3136_ = v_isSharedCheck_3152_;
goto v_resetjp_3134_;
}
else
{
lean_dec(v___x_3128_);
v___x_3135_ = lean_box(0);
v_isShared_3136_ = v_isSharedCheck_3152_;
goto v_resetjp_3134_;
}
v_resetjp_3134_:
{
lean_object* v_toAttributeImplCore_3137_; lean_object* v_name_3138_; uint8_t v___x_3139_; lean_object* v___x_3140_; lean_object* v___x_3141_; lean_object* v___x_3142_; lean_object* v___x_3143_; lean_object* v___x_3144_; lean_object* v___x_3145_; lean_object* v___x_3146_; lean_object* v___x_3147_; lean_object* v___x_3148_; lean_object* v___x_3150_; 
v_toAttributeImplCore_3137_ = lean_ctor_get(v_attr_3119_, 0);
lean_inc_ref(v_toAttributeImplCore_3137_);
lean_dec_ref(v_attr_3119_);
v_name_3138_ = lean_ctor_get(v_toAttributeImplCore_3137_, 1);
lean_inc(v_name_3138_);
lean_dec_ref(v_toAttributeImplCore_3137_);
v___x_3139_ = 1;
v___x_3140_ = ((lean_object*)(l_Lean_ParametricAttribute_setParam___redArg___closed__0));
v___x_3141_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_3138_, v___x_3139_);
v___x_3142_ = lean_string_append(v___x_3140_, v___x_3141_);
lean_dec_ref(v___x_3141_);
v___x_3143_ = ((lean_object*)(l_Lean_ParametricAttribute_setParam___redArg___closed__1));
v___x_3144_ = lean_string_append(v___x_3142_, v___x_3143_);
v___x_3145_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_decl_3114_, v___x_3139_);
v___x_3146_ = lean_string_append(v___x_3144_, v___x_3145_);
lean_dec_ref(v___x_3145_);
v___x_3147_ = ((lean_object*)(l_Lean_ParametricAttribute_setParam___redArg___closed__2));
v___x_3148_ = lean_string_append(v___x_3146_, v___x_3147_);
if (v_isShared_3136_ == 0)
{
lean_ctor_set_tag(v___x_3135_, 0);
lean_ctor_set(v___x_3135_, 0, v___x_3148_);
v___x_3150_ = v___x_3135_;
goto v_reusejp_3149_;
}
else
{
lean_object* v_reuseFailAlloc_3151_; 
v_reuseFailAlloc_3151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3151_, 0, v___x_3148_);
v___x_3150_ = v_reuseFailAlloc_3151_;
goto v_reusejp_3149_;
}
v_reusejp_3149_:
{
return v___x_3150_;
}
}
}
}
}
else
{
lean_object* v___x_3157_; uint8_t v_isShared_3158_; uint8_t v_isSharedCheck_3175_; 
lean_dec(v_param_3115_);
lean_dec_ref(v_env_3113_);
v_isSharedCheck_3175_ = !lean_is_exclusive(v___x_3116_);
if (v_isSharedCheck_3175_ == 0)
{
lean_object* v_unused_3176_; 
v_unused_3176_ = lean_ctor_get(v___x_3116_, 0);
lean_dec(v_unused_3176_);
v___x_3157_ = v___x_3116_;
v_isShared_3158_ = v_isSharedCheck_3175_;
goto v_resetjp_3156_;
}
else
{
lean_dec(v___x_3116_);
v___x_3157_ = lean_box(0);
v_isShared_3158_ = v_isSharedCheck_3175_;
goto v_resetjp_3156_;
}
v_resetjp_3156_:
{
lean_object* v_attr_3159_; lean_object* v_toAttributeImplCore_3160_; lean_object* v_name_3161_; uint8_t v___x_3162_; lean_object* v___x_3163_; lean_object* v___x_3164_; lean_object* v___x_3165_; lean_object* v___x_3166_; lean_object* v___x_3167_; lean_object* v___x_3168_; lean_object* v___x_3169_; lean_object* v___x_3170_; lean_object* v___x_3171_; lean_object* v___x_3173_; 
v_attr_3159_ = lean_ctor_get(v_attr_3112_, 0);
lean_inc_ref(v_attr_3159_);
lean_dec_ref(v_attr_3112_);
v_toAttributeImplCore_3160_ = lean_ctor_get(v_attr_3159_, 0);
lean_inc_ref(v_toAttributeImplCore_3160_);
lean_dec_ref(v_attr_3159_);
v_name_3161_ = lean_ctor_get(v_toAttributeImplCore_3160_, 1);
lean_inc(v_name_3161_);
lean_dec_ref(v_toAttributeImplCore_3160_);
v___x_3162_ = 1;
v___x_3163_ = ((lean_object*)(l_Lean_ParametricAttribute_setParam___redArg___closed__0));
v___x_3164_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_3161_, v___x_3162_);
v___x_3165_ = lean_string_append(v___x_3163_, v___x_3164_);
lean_dec_ref(v___x_3164_);
v___x_3166_ = ((lean_object*)(l_Lean_ParametricAttribute_setParam___redArg___closed__1));
v___x_3167_ = lean_string_append(v___x_3165_, v___x_3166_);
v___x_3168_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_decl_3114_, v___x_3162_);
v___x_3169_ = lean_string_append(v___x_3167_, v___x_3168_);
lean_dec_ref(v___x_3168_);
v___x_3170_ = ((lean_object*)(l_Lean_ParametricAttribute_setParam___redArg___closed__3));
v___x_3171_ = lean_string_append(v___x_3169_, v___x_3170_);
if (v_isShared_3158_ == 0)
{
lean_ctor_set_tag(v___x_3157_, 0);
lean_ctor_set(v___x_3157_, 0, v___x_3171_);
v___x_3173_ = v___x_3157_;
goto v_reusejp_3172_;
}
else
{
lean_object* v_reuseFailAlloc_3174_; 
v_reuseFailAlloc_3174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3174_, 0, v___x_3171_);
v___x_3173_ = v_reuseFailAlloc_3174_;
goto v_reusejp_3172_;
}
v_reusejp_3172_:
{
return v___x_3173_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_setParam(lean_object* v_00_u03b1_3177_, lean_object* v_attr_3178_, lean_object* v_env_3179_, lean_object* v_decl_3180_, lean_object* v_param_3181_){
_start:
{
lean_object* v___x_3182_; 
v___x_3182_ = l_Lean_ParametricAttribute_setParam___redArg(v_attr_3178_, v_env_3179_, v_decl_3180_, v_param_3181_);
return v___x_3182_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___lam__0(lean_object* v_x_3183_, lean_object* v___y_3184_){
_start:
{
lean_object* v___x_3186_; lean_object* v___x_3187_; 
v___x_3186_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___lam__0___closed__1));
v___x_3187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3187_, 0, v___x_3186_);
return v___x_3187_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___lam__0___boxed(lean_object* v_x_3188_, lean_object* v___y_3189_, lean_object* v___y_3190_){
_start:
{
lean_object* v_res_3191_; 
v_res_3191_ = l_Lean_instInhabitedEnumAttributes_default___lam__0(v_x_3188_, v___y_3189_);
lean_dec_ref(v___y_3189_);
lean_dec_ref(v_x_3188_);
return v_res_3191_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___lam__1(lean_object* v_s_3192_, lean_object* v_x_3193_){
_start:
{
lean_inc(v_s_3192_);
return v_s_3192_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___lam__1___boxed(lean_object* v_s_3194_, lean_object* v_x_3195_){
_start:
{
lean_object* v_res_3196_; 
v_res_3196_ = l_Lean_instInhabitedEnumAttributes_default___lam__1(v_s_3194_, v_x_3195_);
lean_dec_ref(v_x_3195_);
lean_dec(v_s_3194_);
return v_res_3196_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___lam__2(lean_object* v_x_3197_, lean_object* v_x_3198_){
_start:
{
lean_object* v___x_3199_; 
v___x_3199_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___lam__2___closed__1));
return v___x_3199_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___lam__2___boxed(lean_object* v_x_3200_, lean_object* v_x_3201_){
_start:
{
lean_object* v_res_3202_; 
v_res_3202_ = l_Lean_instInhabitedEnumAttributes_default___lam__2(v_x_3200_, v_x_3201_);
lean_dec(v_x_3201_);
lean_dec_ref(v_x_3200_);
return v_res_3202_;
}
}
static lean_object* _init_l_Lean_instInhabitedEnumAttributes_default___closed__3(void){
_start:
{
lean_object* v___x_3206_; 
v___x_3206_ = l_Lean_instInhabitedEnvExtension_default(lean_box(0));
return v___x_3206_;
}
}
static lean_object* _init_l_Lean_instInhabitedEnumAttributes_default___closed__4(void){
_start:
{
lean_object* v___f_3207_; lean_object* v___f_3208_; lean_object* v___f_3209_; lean_object* v___f_3210_; lean_object* v___x_3211_; lean_object* v___x_3212_; lean_object* v___x_3213_; 
v___f_3207_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___closed__3));
v___f_3208_ = ((lean_object*)(l_Lean_instInhabitedEnumAttributes_default___closed__2));
v___f_3209_ = ((lean_object*)(l_Lean_instInhabitedEnumAttributes_default___closed__1));
v___f_3210_ = ((lean_object*)(l_Lean_instInhabitedEnumAttributes_default___closed__0));
v___x_3211_ = lean_box(0);
v___x_3212_ = lean_obj_once(&l_Lean_instInhabitedEnumAttributes_default___closed__3, &l_Lean_instInhabitedEnumAttributes_default___closed__3_once, _init_l_Lean_instInhabitedEnumAttributes_default___closed__3);
v___x_3213_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3213_, 0, v___x_3212_);
lean_ctor_set(v___x_3213_, 1, v___x_3211_);
lean_ctor_set(v___x_3213_, 2, v___f_3210_);
lean_ctor_set(v___x_3213_, 3, v___f_3209_);
lean_ctor_set(v___x_3213_, 4, v___f_3208_);
lean_ctor_set(v___x_3213_, 5, v___f_3207_);
return v___x_3213_;
}
}
static lean_object* _init_l_Lean_instInhabitedEnumAttributes_default___closed__5(void){
_start:
{
lean_object* v___x_3214_; lean_object* v___x_3215_; lean_object* v___x_3216_; 
v___x_3214_ = lean_obj_once(&l_Lean_instInhabitedEnumAttributes_default___closed__4, &l_Lean_instInhabitedEnumAttributes_default___closed__4_once, _init_l_Lean_instInhabitedEnumAttributes_default___closed__4);
v___x_3215_ = lean_box(0);
v___x_3216_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3216_, 0, v___x_3215_);
lean_ctor_set(v___x_3216_, 1, v___x_3214_);
return v___x_3216_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default(lean_object* v_00_u03b1_3217_){
_start:
{
lean_object* v___x_3218_; 
v___x_3218_ = lean_obj_once(&l_Lean_instInhabitedEnumAttributes_default___closed__5, &l_Lean_instInhabitedEnumAttributes_default___closed__5_once, _init_l_Lean_instInhabitedEnumAttributes_default___closed__5);
return v___x_3218_;
}
}
static lean_object* _init_l_Lean_instInhabitedEnumAttributes___closed__0(void){
_start:
{
lean_object* v___x_3219_; 
v___x_3219_ = l_Lean_instInhabitedEnumAttributes_default(lean_box(0));
return v___x_3219_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes(lean_object* v_a_3220_){
_start:
{
lean_object* v___x_3221_; 
v___x_3221_ = lean_obj_once(&l_Lean_instInhabitedEnumAttributes___closed__0, &l_Lean_instInhabitedEnumAttributes___closed__0_once, _init_l_Lean_instInhabitedEnumAttributes___closed__0);
return v___x_3221_;
}
}
static lean_object* _init_l_Lean_registerEnumAttributes___auto__1(void){
_start:
{
lean_object* v___x_3222_; 
v___x_3222_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__28, &l_Lean_AttributeImplCore_ref___autoParam___closed__28_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__28);
return v___x_3222_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__0(lean_object* v_x_3223_){
_start:
{
lean_object* v___x_3224_; 
v___x_3224_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___lam__2___closed__0));
return v___x_3224_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__0___boxed(lean_object* v_x_3225_){
_start:
{
lean_object* v_res_3226_; 
v_res_3226_ = l_Lean_registerEnumAttributes___redArg___lam__0(v_x_3225_);
lean_dec(v_x_3225_);
return v_res_3226_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___redArg(lean_object* v_newState_3227_, lean_object* v_x_3228_, lean_object* v_x_3229_){
_start:
{
if (lean_obj_tag(v_x_3229_) == 0)
{
return v_x_3228_;
}
else
{
lean_object* v_head_3230_; lean_object* v_tail_3231_; lean_object* v___x_3232_; 
v_head_3230_ = lean_ctor_get(v_x_3229_, 0);
lean_inc(v_head_3230_);
v_tail_3231_ = lean_ctor_get(v_x_3229_, 1);
lean_inc(v_tail_3231_);
lean_dec_ref_known(v_x_3229_, 2);
v___x_3232_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_newState_3227_, v_head_3230_);
if (lean_obj_tag(v___x_3232_) == 1)
{
lean_object* v_val_3233_; lean_object* v___x_3234_; 
v_val_3233_ = lean_ctor_get(v___x_3232_, 0);
lean_inc(v_val_3233_);
lean_dec_ref_known(v___x_3232_, 1);
v___x_3234_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_head_3230_, v_val_3233_, v_x_3228_);
v_x_3228_ = v___x_3234_;
v_x_3229_ = v_tail_3231_;
goto _start;
}
else
{
lean_dec(v___x_3232_);
lean_dec(v_head_3230_);
v_x_3229_ = v_tail_3231_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___redArg___boxed(lean_object* v_newState_3237_, lean_object* v_x_3238_, lean_object* v_x_3239_){
_start:
{
lean_object* v_res_3240_; 
v_res_3240_ = l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___redArg(v_newState_3237_, v_x_3238_, v_x_3239_);
lean_dec(v_newState_3237_);
return v_res_3240_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__1(lean_object* v_x_3241_, lean_object* v_newState_3242_, lean_object* v_consts_3243_, lean_object* v_st_3244_){
_start:
{
lean_object* v___x_3245_; 
v___x_3245_ = l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___redArg(v_newState_3242_, v_st_3244_, v_consts_3243_);
return v___x_3245_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__1___boxed(lean_object* v_x_3246_, lean_object* v_newState_3247_, lean_object* v_consts_3248_, lean_object* v_st_3249_){
_start:
{
lean_object* v_res_3250_; 
v_res_3250_ = l_Lean_registerEnumAttributes___redArg___lam__1(v_x_3246_, v_newState_3247_, v_consts_3248_, v_st_3249_);
lean_dec(v_newState_3247_);
lean_dec(v_x_3246_);
return v_res_3250_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__2(lean_object* v_s_3260_){
_start:
{
lean_object* v___x_3261_; lean_object* v___y_3263_; 
v___x_3261_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___lam__2___closed__3));
if (lean_obj_tag(v_s_3260_) == 0)
{
lean_object* v_size_3267_; 
v_size_3267_ = lean_ctor_get(v_s_3260_, 0);
lean_inc(v_size_3267_);
lean_dec_ref_known(v_s_3260_, 5);
v___y_3263_ = v_size_3267_;
goto v___jp_3262_;
}
else
{
lean_object* v___x_3268_; 
v___x_3268_ = lean_unsigned_to_nat(0u);
v___y_3263_ = v___x_3268_;
goto v___jp_3262_;
}
v___jp_3262_:
{
lean_object* v___x_3264_; lean_object* v___x_3265_; lean_object* v___x_3266_; 
v___x_3264_ = l_Nat_reprFast(v___y_3263_);
v___x_3265_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3265_, 0, v___x_3264_);
v___x_3266_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3266_, 0, v___x_3261_);
lean_ctor_set(v___x_3266_, 1, v___x_3265_);
return v___x_3266_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg(lean_object* v_env_3269_, lean_object* v_as_3270_, size_t v_i_3271_, size_t v_stop_3272_, lean_object* v_b_3273_){
_start:
{
lean_object* v___y_3275_; uint8_t v___x_3279_; 
v___x_3279_ = lean_usize_dec_eq(v_i_3271_, v_stop_3272_);
if (v___x_3279_ == 0)
{
lean_object* v___x_3280_; lean_object* v_fst_3281_; uint8_t v___x_3282_; lean_object* v___x_3283_; uint8_t v___x_3284_; 
v___x_3280_ = lean_array_uget_borrowed(v_as_3270_, v_i_3271_);
v_fst_3281_ = lean_ctor_get(v___x_3280_, 0);
v___x_3282_ = 1;
lean_inc_ref(v_env_3269_);
v___x_3283_ = l_Lean_Environment_setExporting(v_env_3269_, v___x_3282_);
lean_inc(v_fst_3281_);
v___x_3284_ = l_Lean_Environment_contains(v___x_3283_, v_fst_3281_, v___x_3279_);
if (v___x_3284_ == 0)
{
v___y_3275_ = v_b_3273_;
goto v___jp_3274_;
}
else
{
lean_object* v___x_3285_; 
lean_inc(v___x_3280_);
v___x_3285_ = lean_array_push(v_b_3273_, v___x_3280_);
v___y_3275_ = v___x_3285_;
goto v___jp_3274_;
}
}
else
{
lean_dec_ref(v_env_3269_);
return v_b_3273_;
}
v___jp_3274_:
{
size_t v___x_3276_; size_t v___x_3277_; 
v___x_3276_ = ((size_t)1ULL);
v___x_3277_ = lean_usize_add(v_i_3271_, v___x_3276_);
v_i_3271_ = v___x_3277_;
v_b_3273_ = v___y_3275_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg___boxed(lean_object* v_env_3286_, lean_object* v_as_3287_, lean_object* v_i_3288_, lean_object* v_stop_3289_, lean_object* v_b_3290_){
_start:
{
size_t v_i_boxed_3291_; size_t v_stop_boxed_3292_; lean_object* v_res_3293_; 
v_i_boxed_3291_ = lean_unbox_usize(v_i_3288_);
lean_dec(v_i_3288_);
v_stop_boxed_3292_ = lean_unbox_usize(v_stop_3289_);
lean_dec(v_stop_3289_);
v_res_3293_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg(v_env_3286_, v_as_3287_, v_i_boxed_3291_, v_stop_boxed_3292_, v_b_3290_);
lean_dec_ref(v_as_3287_);
return v_res_3293_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__3(lean_object* v_env_3294_, lean_object* v_m_3295_){
_start:
{
lean_object* v___x_3296_; lean_object* v___x_3297_; lean_object* v___y_3299_; lean_object* v___x_3313_; lean_object* v___x_3314_; lean_object* v___y_3316_; lean_object* v___y_3317_; uint8_t v___x_3319_; 
v___x_3296_ = lean_unsigned_to_nat(0u);
v___x_3297_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___lam__2___closed__0));
v___x_3313_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttribute_spec__1_spec__1___redArg(v___x_3297_, v_m_3295_);
v___x_3314_ = lean_array_get_size(v___x_3313_);
v___x_3319_ = lean_nat_dec_eq(v___x_3314_, v___x_3296_);
if (v___x_3319_ == 0)
{
lean_object* v___x_3320_; lean_object* v___x_3321_; lean_object* v___y_3323_; uint8_t v___x_3325_; 
v___x_3320_ = lean_unsigned_to_nat(1u);
v___x_3321_ = lean_nat_sub(v___x_3314_, v___x_3320_);
v___x_3325_ = lean_nat_dec_le(v___x_3296_, v___x_3321_);
if (v___x_3325_ == 0)
{
lean_inc(v___x_3321_);
v___y_3323_ = v___x_3321_;
goto v___jp_3322_;
}
else
{
v___y_3323_ = v___x_3296_;
goto v___jp_3322_;
}
v___jp_3322_:
{
uint8_t v___x_3324_; 
v___x_3324_ = lean_nat_dec_le(v___y_3323_, v___x_3321_);
if (v___x_3324_ == 0)
{
lean_dec(v___x_3321_);
lean_inc(v___y_3323_);
v___y_3316_ = v___y_3323_;
v___y_3317_ = v___y_3323_;
goto v___jp_3315_;
}
else
{
v___y_3316_ = v___y_3323_;
v___y_3317_ = v___x_3321_;
goto v___jp_3315_;
}
}
}
else
{
v___y_3299_ = v___x_3313_;
goto v___jp_3298_;
}
v___jp_3298_:
{
lean_object* v___x_3300_; uint8_t v___x_3301_; 
v___x_3300_ = lean_array_get_size(v___y_3299_);
v___x_3301_ = lean_nat_dec_lt(v___x_3296_, v___x_3300_);
if (v___x_3301_ == 0)
{
lean_object* v___x_3302_; 
lean_dec_ref(v_env_3294_);
v___x_3302_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3302_, 0, v___x_3297_);
lean_ctor_set(v___x_3302_, 1, v___x_3297_);
lean_ctor_set(v___x_3302_, 2, v___y_3299_);
return v___x_3302_;
}
else
{
uint8_t v___x_3303_; 
v___x_3303_ = lean_nat_dec_le(v___x_3300_, v___x_3300_);
if (v___x_3303_ == 0)
{
if (v___x_3301_ == 0)
{
lean_object* v___x_3304_; 
lean_dec_ref(v_env_3294_);
v___x_3304_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3304_, 0, v___x_3297_);
lean_ctor_set(v___x_3304_, 1, v___x_3297_);
lean_ctor_set(v___x_3304_, 2, v___y_3299_);
return v___x_3304_;
}
else
{
size_t v___x_3305_; size_t v___x_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; 
v___x_3305_ = ((size_t)0ULL);
v___x_3306_ = lean_usize_of_nat(v___x_3300_);
v___x_3307_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg(v_env_3294_, v___y_3299_, v___x_3305_, v___x_3306_, v___x_3297_);
lean_inc_ref(v___x_3307_);
v___x_3308_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3308_, 0, v___x_3307_);
lean_ctor_set(v___x_3308_, 1, v___x_3307_);
lean_ctor_set(v___x_3308_, 2, v___y_3299_);
return v___x_3308_;
}
}
else
{
size_t v___x_3309_; size_t v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; 
v___x_3309_ = ((size_t)0ULL);
v___x_3310_ = lean_usize_of_nat(v___x_3300_);
v___x_3311_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg(v_env_3294_, v___y_3299_, v___x_3309_, v___x_3310_, v___x_3297_);
lean_inc_ref(v___x_3311_);
v___x_3312_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3312_, 0, v___x_3311_);
lean_ctor_set(v___x_3312_, 1, v___x_3311_);
lean_ctor_set(v___x_3312_, 2, v___y_3299_);
return v___x_3312_;
}
}
}
v___jp_3315_:
{
lean_object* v___x_3318_; 
v___x_3318_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttribute_spec__2___redArg(v___x_3314_, v___x_3313_, v___y_3316_, v___y_3317_);
lean_dec(v___y_3317_);
v___y_3299_ = v___x_3318_;
goto v___jp_3298_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__3___boxed(lean_object* v_env_3326_, lean_object* v_m_3327_){
_start:
{
lean_object* v_res_3328_; 
v_res_3328_ = l_Lean_registerEnumAttributes___redArg___lam__3(v_env_3326_, v_m_3327_);
lean_dec(v_m_3327_);
return v_res_3328_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__4(lean_object* v_s_3329_, lean_object* v_p_3330_){
_start:
{
lean_object* v_fst_3331_; lean_object* v_snd_3332_; lean_object* v___x_3333_; 
v_fst_3331_ = lean_ctor_get(v_p_3330_, 0);
lean_inc(v_fst_3331_);
v_snd_3332_ = lean_ctor_get(v_p_3330_, 1);
lean_inc(v_snd_3332_);
lean_dec_ref(v_p_3330_);
v___x_3333_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_3331_, v_snd_3332_, v_s_3329_);
return v___x_3333_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__6(lean_object* v___x_3334_, lean_object* v_x_3335_, lean_object* v_x_3336_){
_start:
{
lean_object* v___x_3338_; 
v___x_3338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3338_, 0, v___x_3334_);
return v___x_3338_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__6___boxed(lean_object* v___x_3339_, lean_object* v_x_3340_, lean_object* v_x_3341_, lean_object* v___y_3342_){
_start:
{
lean_object* v_res_3343_; 
v_res_3343_ = l_Lean_registerEnumAttributes___redArg___lam__6(v___x_3339_, v_x_3340_, v_x_3341_);
lean_dec_ref(v_x_3341_);
lean_dec_ref(v_x_3340_);
return v_res_3343_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_registerEnumAttributes_spec__3(lean_object* v_as_3344_){
_start:
{
if (lean_obj_tag(v_as_3344_) == 0)
{
lean_object* v___x_3346_; lean_object* v___x_3347_; 
v___x_3346_ = lean_box(0);
v___x_3347_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3347_, 0, v___x_3346_);
return v___x_3347_;
}
else
{
lean_object* v_head_3348_; lean_object* v_tail_3349_; lean_object* v___x_3350_; 
v_head_3348_ = lean_ctor_get(v_as_3344_, 0);
lean_inc(v_head_3348_);
v_tail_3349_ = lean_ctor_get(v_as_3344_, 1);
lean_inc(v_tail_3349_);
lean_dec_ref_known(v_as_3344_, 2);
v___x_3350_ = l_Lean_registerBuiltinAttribute(v_head_3348_);
if (lean_obj_tag(v___x_3350_) == 0)
{
lean_dec_ref_known(v___x_3350_, 1);
v_as_3344_ = v_tail_3349_;
goto _start;
}
else
{
lean_dec(v_tail_3349_);
return v___x_3350_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_registerEnumAttributes_spec__3___boxed(lean_object* v_as_3352_, lean_object* v___y_3353_){
_start:
{
lean_object* v_res_3354_; 
v_res_3354_ = l_List_forM___at___00Lean_registerEnumAttributes_spec__3(v_as_3352_);
return v_res_3354_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__1(lean_object* v_validate_3355_, lean_object* v_snd_3356_, lean_object* v_a_3357_, lean_object* v_fst_3358_, lean_object* v_decl_3359_, lean_object* v_stx_3360_, uint8_t v_kind_3361_, lean_object* v___y_3362_, lean_object* v___y_3363_){
_start:
{
lean_object* v___y_3366_; lean_object* v___y_3367_; lean_object* v___y_3402_; lean_object* v___y_3403_; lean_object* v___x_3408_; 
v___x_3408_ = l_Lean_Attribute_Builtin_ensureNoArgs(v_stx_3360_, v___y_3362_, v___y_3363_);
if (lean_obj_tag(v___x_3408_) == 0)
{
uint8_t v___x_3409_; uint8_t v___x_3410_; 
lean_dec_ref_known(v___x_3408_, 1);
v___x_3409_ = 0;
v___x_3410_ = l_Lean_instBEqAttributeKind_beq(v_kind_3361_, v___x_3409_);
if (v___x_3410_ == 0)
{
lean_object* v___x_3411_; 
lean_dec(v_decl_3359_);
lean_dec_ref(v_a_3357_);
lean_dec(v_snd_3356_);
lean_dec_ref(v_validate_3355_);
v___x_3411_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg(v_fst_3358_, v_kind_3361_, v___y_3362_, v___y_3363_);
return v___x_3411_;
}
else
{
v___y_3402_ = v___y_3362_;
v___y_3403_ = v___y_3363_;
goto v___jp_3401_;
}
}
else
{
lean_dec(v_decl_3359_);
lean_dec(v_fst_3358_);
lean_dec_ref(v_a_3357_);
lean_dec(v_snd_3356_);
lean_dec_ref(v_validate_3355_);
return v___x_3408_;
}
v___jp_3365_:
{
lean_object* v___x_3368_; 
lean_inc(v___y_3367_);
lean_inc_ref(v___y_3366_);
lean_inc(v_snd_3356_);
lean_inc(v_decl_3359_);
v___x_3368_ = lean_apply_5(v_validate_3355_, v_decl_3359_, v_snd_3356_, v___y_3366_, v___y_3367_, lean_box(0));
if (lean_obj_tag(v___x_3368_) == 0)
{
lean_object* v___x_3370_; uint8_t v_isShared_3371_; uint8_t v_isSharedCheck_3399_; 
v_isSharedCheck_3399_ = !lean_is_exclusive(v___x_3368_);
if (v_isSharedCheck_3399_ == 0)
{
lean_object* v_unused_3400_; 
v_unused_3400_ = lean_ctor_get(v___x_3368_, 0);
lean_dec(v_unused_3400_);
v___x_3370_ = v___x_3368_;
v_isShared_3371_ = v_isSharedCheck_3399_;
goto v_resetjp_3369_;
}
else
{
lean_dec(v___x_3368_);
v___x_3370_ = lean_box(0);
v_isShared_3371_ = v_isSharedCheck_3399_;
goto v_resetjp_3369_;
}
v_resetjp_3369_:
{
lean_object* v___x_3372_; lean_object* v_toEnvExtension_3373_; lean_object* v_env_3374_; lean_object* v_nextMacroScope_3375_; lean_object* v_ngen_3376_; lean_object* v_auxDeclNGen_3377_; lean_object* v_traceState_3378_; lean_object* v_messages_3379_; lean_object* v_infoState_3380_; lean_object* v_snapshotTasks_3381_; lean_object* v___x_3383_; uint8_t v_isShared_3384_; uint8_t v_isSharedCheck_3397_; 
v___x_3372_ = lean_st_ref_take(v___y_3367_);
v_toEnvExtension_3373_ = lean_ctor_get(v_a_3357_, 0);
v_env_3374_ = lean_ctor_get(v___x_3372_, 0);
v_nextMacroScope_3375_ = lean_ctor_get(v___x_3372_, 1);
v_ngen_3376_ = lean_ctor_get(v___x_3372_, 2);
v_auxDeclNGen_3377_ = lean_ctor_get(v___x_3372_, 3);
v_traceState_3378_ = lean_ctor_get(v___x_3372_, 4);
v_messages_3379_ = lean_ctor_get(v___x_3372_, 6);
v_infoState_3380_ = lean_ctor_get(v___x_3372_, 7);
v_snapshotTasks_3381_ = lean_ctor_get(v___x_3372_, 8);
v_isSharedCheck_3397_ = !lean_is_exclusive(v___x_3372_);
if (v_isSharedCheck_3397_ == 0)
{
lean_object* v_unused_3398_; 
v_unused_3398_ = lean_ctor_get(v___x_3372_, 5);
lean_dec(v_unused_3398_);
v___x_3383_ = v___x_3372_;
v_isShared_3384_ = v_isSharedCheck_3397_;
goto v_resetjp_3382_;
}
else
{
lean_inc(v_snapshotTasks_3381_);
lean_inc(v_infoState_3380_);
lean_inc(v_messages_3379_);
lean_inc(v_traceState_3378_);
lean_inc(v_auxDeclNGen_3377_);
lean_inc(v_ngen_3376_);
lean_inc(v_nextMacroScope_3375_);
lean_inc(v_env_3374_);
lean_dec(v___x_3372_);
v___x_3383_ = lean_box(0);
v_isShared_3384_ = v_isSharedCheck_3397_;
goto v_resetjp_3382_;
}
v_resetjp_3382_:
{
lean_object* v_asyncMode_3385_; lean_object* v___x_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; lean_object* v___x_3390_; 
v_asyncMode_3385_ = lean_ctor_get(v_toEnvExtension_3373_, 2);
lean_inc(v_asyncMode_3385_);
lean_inc(v_decl_3359_);
v___x_3386_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3386_, 0, v_decl_3359_);
lean_ctor_set(v___x_3386_, 1, v_snd_3356_);
v___x_3387_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_a_3357_, v_env_3374_, v___x_3386_, v_asyncMode_3385_, v_decl_3359_);
lean_dec(v_asyncMode_3385_);
v___x_3388_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2);
if (v_isShared_3384_ == 0)
{
lean_ctor_set(v___x_3383_, 5, v___x_3388_);
lean_ctor_set(v___x_3383_, 0, v___x_3387_);
v___x_3390_ = v___x_3383_;
goto v_reusejp_3389_;
}
else
{
lean_object* v_reuseFailAlloc_3396_; 
v_reuseFailAlloc_3396_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3396_, 0, v___x_3387_);
lean_ctor_set(v_reuseFailAlloc_3396_, 1, v_nextMacroScope_3375_);
lean_ctor_set(v_reuseFailAlloc_3396_, 2, v_ngen_3376_);
lean_ctor_set(v_reuseFailAlloc_3396_, 3, v_auxDeclNGen_3377_);
lean_ctor_set(v_reuseFailAlloc_3396_, 4, v_traceState_3378_);
lean_ctor_set(v_reuseFailAlloc_3396_, 5, v___x_3388_);
lean_ctor_set(v_reuseFailAlloc_3396_, 6, v_messages_3379_);
lean_ctor_set(v_reuseFailAlloc_3396_, 7, v_infoState_3380_);
lean_ctor_set(v_reuseFailAlloc_3396_, 8, v_snapshotTasks_3381_);
v___x_3390_ = v_reuseFailAlloc_3396_;
goto v_reusejp_3389_;
}
v_reusejp_3389_:
{
lean_object* v___x_3391_; lean_object* v___x_3392_; lean_object* v___x_3394_; 
v___x_3391_ = lean_st_ref_set(v___y_3367_, v___x_3390_);
v___x_3392_ = lean_box(0);
if (v_isShared_3371_ == 0)
{
lean_ctor_set(v___x_3370_, 0, v___x_3392_);
v___x_3394_ = v___x_3370_;
goto v_reusejp_3393_;
}
else
{
lean_object* v_reuseFailAlloc_3395_; 
v_reuseFailAlloc_3395_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3395_, 0, v___x_3392_);
v___x_3394_ = v_reuseFailAlloc_3395_;
goto v_reusejp_3393_;
}
v_reusejp_3393_:
{
return v___x_3394_;
}
}
}
}
}
else
{
lean_dec(v_decl_3359_);
lean_dec_ref(v_a_3357_);
lean_dec(v_snd_3356_);
return v___x_3368_;
}
}
v___jp_3401_:
{
lean_object* v___x_3404_; lean_object* v_env_3405_; lean_object* v___x_3406_; 
v___x_3404_ = lean_st_ref_get(v___y_3403_);
v_env_3405_ = lean_ctor_get(v___x_3404_, 0);
lean_inc_ref(v_env_3405_);
lean_dec(v___x_3404_);
v___x_3406_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3405_, v_decl_3359_);
lean_dec_ref(v_env_3405_);
if (lean_obj_tag(v___x_3406_) == 0)
{
lean_dec(v_fst_3358_);
v___y_3366_ = v___y_3402_;
v___y_3367_ = v___y_3403_;
goto v___jp_3365_;
}
else
{
lean_object* v___x_3407_; 
lean_dec_ref_known(v___x_3406_, 1);
lean_dec_ref(v_a_3357_);
lean_dec(v_snd_3356_);
lean_dec_ref(v_validate_3355_);
v___x_3407_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg(v_fst_3358_, v_decl_3359_, v___y_3402_, v___y_3403_);
return v___x_3407_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__1___boxed(lean_object* v_validate_3412_, lean_object* v_snd_3413_, lean_object* v_a_3414_, lean_object* v_fst_3415_, lean_object* v_decl_3416_, lean_object* v_stx_3417_, lean_object* v_kind_3418_, lean_object* v___y_3419_, lean_object* v___y_3420_, lean_object* v___y_3421_){
_start:
{
uint8_t v_kind_boxed_3422_; lean_object* v_res_3423_; 
v_kind_boxed_3422_ = lean_unbox(v_kind_3418_);
v_res_3423_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__1(v_validate_3412_, v_snd_3413_, v_a_3414_, v_fst_3415_, v_decl_3416_, v_stx_3417_, v_kind_boxed_3422_, v___y_3419_, v___y_3420_);
lean_dec(v___y_3420_);
lean_dec_ref(v___y_3419_);
return v_res_3423_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__0(lean_object* v_fst_3424_, lean_object* v_decl_3425_, lean_object* v___y_3426_, lean_object* v___y_3427_){
_start:
{
lean_object* v___x_3429_; lean_object* v___x_3430_; lean_object* v___x_3431_; lean_object* v___x_3432_; lean_object* v___x_3433_; lean_object* v___x_3434_; 
v___x_3429_ = lean_obj_once(&l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1, &l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1_once, _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1);
v___x_3430_ = l_Lean_MessageData_ofName(v_fst_3424_);
v___x_3431_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3431_, 0, v___x_3429_);
lean_ctor_set(v___x_3431_, 1, v___x_3430_);
v___x_3432_ = lean_obj_once(&l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3, &l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3_once, _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3);
v___x_3433_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3433_, 0, v___x_3431_);
lean_ctor_set(v___x_3433_, 1, v___x_3432_);
v___x_3434_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_3433_, v___y_3426_, v___y_3427_);
return v___x_3434_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__0___boxed(lean_object* v_fst_3435_, lean_object* v_decl_3436_, lean_object* v___y_3437_, lean_object* v___y_3438_, lean_object* v___y_3439_){
_start:
{
lean_object* v_res_3440_; 
v_res_3440_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__0(v_fst_3435_, v_decl_3436_, v___y_3437_, v___y_3438_);
lean_dec(v___y_3438_);
lean_dec_ref(v___y_3437_);
lean_dec(v_decl_3436_);
return v_res_3440_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg(lean_object* v_validate_3441_, lean_object* v_a_3442_, lean_object* v_ref_3443_, uint8_t v_applicationTime_3444_, lean_object* v_a_3445_, lean_object* v_a_3446_){
_start:
{
if (lean_obj_tag(v_a_3445_) == 0)
{
lean_object* v___x_3447_; 
lean_dec(v_ref_3443_);
lean_dec_ref(v_a_3442_);
lean_dec_ref(v_validate_3441_);
v___x_3447_ = l_List_reverse___redArg(v_a_3446_);
return v___x_3447_;
}
else
{
lean_object* v_head_3448_; lean_object* v_snd_3449_; lean_object* v_tail_3450_; lean_object* v___x_3452_; uint8_t v_isShared_3453_; uint8_t v_isSharedCheck_3465_; 
v_head_3448_ = lean_ctor_get(v_a_3445_, 0);
lean_inc(v_head_3448_);
v_snd_3449_ = lean_ctor_get(v_head_3448_, 1);
lean_inc(v_snd_3449_);
v_tail_3450_ = lean_ctor_get(v_a_3445_, 1);
v_isSharedCheck_3465_ = !lean_is_exclusive(v_a_3445_);
if (v_isSharedCheck_3465_ == 0)
{
lean_object* v_unused_3466_; 
v_unused_3466_ = lean_ctor_get(v_a_3445_, 0);
lean_dec(v_unused_3466_);
v___x_3452_ = v_a_3445_;
v_isShared_3453_ = v_isSharedCheck_3465_;
goto v_resetjp_3451_;
}
else
{
lean_inc(v_tail_3450_);
lean_dec(v_a_3445_);
v___x_3452_ = lean_box(0);
v_isShared_3453_ = v_isSharedCheck_3465_;
goto v_resetjp_3451_;
}
v_resetjp_3451_:
{
lean_object* v_fst_3454_; lean_object* v_fst_3455_; lean_object* v_snd_3456_; lean_object* v___f_3457_; lean_object* v___f_3458_; lean_object* v___x_3459_; lean_object* v___x_3460_; lean_object* v___x_3462_; 
v_fst_3454_ = lean_ctor_get(v_head_3448_, 0);
lean_inc_n(v_fst_3454_, 3);
lean_dec(v_head_3448_);
v_fst_3455_ = lean_ctor_get(v_snd_3449_, 0);
lean_inc(v_fst_3455_);
v_snd_3456_ = lean_ctor_get(v_snd_3449_, 1);
lean_inc(v_snd_3456_);
lean_dec(v_snd_3449_);
v___f_3457_ = lean_alloc_closure((void*)(l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__0___boxed), 5, 1);
lean_closure_set(v___f_3457_, 0, v_fst_3454_);
lean_inc_ref(v_a_3442_);
lean_inc_ref(v_validate_3441_);
v___f_3458_ = lean_alloc_closure((void*)(l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__1___boxed), 10, 4);
lean_closure_set(v___f_3458_, 0, v_validate_3441_);
lean_closure_set(v___f_3458_, 1, v_snd_3456_);
lean_closure_set(v___f_3458_, 2, v_a_3442_);
lean_closure_set(v___f_3458_, 3, v_fst_3454_);
lean_inc(v_ref_3443_);
v___x_3459_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_3459_, 0, v_ref_3443_);
lean_ctor_set(v___x_3459_, 1, v_fst_3454_);
lean_ctor_set(v___x_3459_, 2, v_fst_3455_);
lean_ctor_set_uint8(v___x_3459_, sizeof(void*)*3, v_applicationTime_3444_);
v___x_3460_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3460_, 0, v___x_3459_);
lean_ctor_set(v___x_3460_, 1, v___f_3458_);
lean_ctor_set(v___x_3460_, 2, v___f_3457_);
if (v_isShared_3453_ == 0)
{
lean_ctor_set(v___x_3452_, 1, v_a_3446_);
lean_ctor_set(v___x_3452_, 0, v___x_3460_);
v___x_3462_ = v___x_3452_;
goto v_reusejp_3461_;
}
else
{
lean_object* v_reuseFailAlloc_3464_; 
v_reuseFailAlloc_3464_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3464_, 0, v___x_3460_);
lean_ctor_set(v_reuseFailAlloc_3464_, 1, v_a_3446_);
v___x_3462_ = v_reuseFailAlloc_3464_;
goto v_reusejp_3461_;
}
v_reusejp_3461_:
{
v_a_3445_ = v_tail_3450_;
v_a_3446_ = v___x_3462_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___boxed(lean_object* v_validate_3467_, lean_object* v_a_3468_, lean_object* v_ref_3469_, lean_object* v_applicationTime_3470_, lean_object* v_a_3471_, lean_object* v_a_3472_){
_start:
{
uint8_t v_applicationTime_boxed_3473_; lean_object* v_res_3474_; 
v_applicationTime_boxed_3473_ = lean_unbox(v_applicationTime_3470_);
v_res_3474_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg(v_validate_3467_, v_a_3468_, v_ref_3469_, v_applicationTime_boxed_3473_, v_a_3471_, v_a_3472_);
return v_res_3474_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg(lean_object* v_attrDescrs_3488_, lean_object* v_validate_3489_, uint8_t v_applicationTime_3490_, lean_object* v_ref_3491_){
_start:
{
lean_object* v___f_3493_; lean_object* v___f_3494_; lean_object* v___f_3495_; lean_object* v___f_3496_; lean_object* v___f_3497_; lean_object* v___f_3498_; lean_object* v___x_3499_; lean_object* v___x_3500_; lean_object* v___x_3501_; lean_object* v___x_3502_; lean_object* v___x_3503_; 
v___f_3493_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__0));
v___f_3494_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__2));
v___f_3495_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__3));
v___f_3496_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__4));
v___f_3497_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__5));
v___f_3498_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__6));
v___x_3499_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__7));
v___x_3500_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__8));
lean_inc(v_ref_3491_);
v___x_3501_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_3501_, 0, v_ref_3491_);
lean_ctor_set(v___x_3501_, 1, v___f_3497_);
lean_ctor_set(v___x_3501_, 2, v___f_3498_);
lean_ctor_set(v___x_3501_, 3, v___f_3496_);
lean_ctor_set(v___x_3501_, 4, v___f_3495_);
lean_ctor_set(v___x_3501_, 5, v___f_3494_);
lean_ctor_set(v___x_3501_, 6, v___x_3499_);
lean_ctor_set(v___x_3501_, 7, v___x_3500_);
v___x_3502_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3502_, 0, v___x_3501_);
lean_ctor_set(v___x_3502_, 1, v___f_3493_);
v___x_3503_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_3502_);
if (lean_obj_tag(v___x_3503_) == 0)
{
lean_object* v_a_3504_; lean_object* v___x_3505_; lean_object* v___x_3506_; lean_object* v___x_3507_; 
v_a_3504_ = lean_ctor_get(v___x_3503_, 0);
lean_inc_n(v_a_3504_, 2);
lean_dec_ref_known(v___x_3503_, 1);
v___x_3505_ = lean_box(0);
v___x_3506_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg(v_validate_3489_, v_a_3504_, v_ref_3491_, v_applicationTime_3490_, v_attrDescrs_3488_, v___x_3505_);
lean_inc(v___x_3506_);
v___x_3507_ = l_List_forM___at___00Lean_registerEnumAttributes_spec__3(v___x_3506_);
if (lean_obj_tag(v___x_3507_) == 0)
{
lean_object* v___x_3509_; uint8_t v_isShared_3510_; uint8_t v_isSharedCheck_3515_; 
v_isSharedCheck_3515_ = !lean_is_exclusive(v___x_3507_);
if (v_isSharedCheck_3515_ == 0)
{
lean_object* v_unused_3516_; 
v_unused_3516_ = lean_ctor_get(v___x_3507_, 0);
lean_dec(v_unused_3516_);
v___x_3509_ = v___x_3507_;
v_isShared_3510_ = v_isSharedCheck_3515_;
goto v_resetjp_3508_;
}
else
{
lean_dec(v___x_3507_);
v___x_3509_ = lean_box(0);
v_isShared_3510_ = v_isSharedCheck_3515_;
goto v_resetjp_3508_;
}
v_resetjp_3508_:
{
lean_object* v___x_3511_; lean_object* v___x_3513_; 
v___x_3511_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3511_, 0, v___x_3506_);
lean_ctor_set(v___x_3511_, 1, v_a_3504_);
if (v_isShared_3510_ == 0)
{
lean_ctor_set(v___x_3509_, 0, v___x_3511_);
v___x_3513_ = v___x_3509_;
goto v_reusejp_3512_;
}
else
{
lean_object* v_reuseFailAlloc_3514_; 
v_reuseFailAlloc_3514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3514_, 0, v___x_3511_);
v___x_3513_ = v_reuseFailAlloc_3514_;
goto v_reusejp_3512_;
}
v_reusejp_3512_:
{
return v___x_3513_;
}
}
}
else
{
lean_object* v_a_3517_; lean_object* v___x_3519_; uint8_t v_isShared_3520_; uint8_t v_isSharedCheck_3524_; 
lean_dec(v___x_3506_);
lean_dec(v_a_3504_);
v_a_3517_ = lean_ctor_get(v___x_3507_, 0);
v_isSharedCheck_3524_ = !lean_is_exclusive(v___x_3507_);
if (v_isSharedCheck_3524_ == 0)
{
v___x_3519_ = v___x_3507_;
v_isShared_3520_ = v_isSharedCheck_3524_;
goto v_resetjp_3518_;
}
else
{
lean_inc(v_a_3517_);
lean_dec(v___x_3507_);
v___x_3519_ = lean_box(0);
v_isShared_3520_ = v_isSharedCheck_3524_;
goto v_resetjp_3518_;
}
v_resetjp_3518_:
{
lean_object* v___x_3522_; 
if (v_isShared_3520_ == 0)
{
v___x_3522_ = v___x_3519_;
goto v_reusejp_3521_;
}
else
{
lean_object* v_reuseFailAlloc_3523_; 
v_reuseFailAlloc_3523_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3523_, 0, v_a_3517_);
v___x_3522_ = v_reuseFailAlloc_3523_;
goto v_reusejp_3521_;
}
v_reusejp_3521_:
{
return v___x_3522_;
}
}
}
}
else
{
lean_object* v_a_3525_; lean_object* v___x_3527_; uint8_t v_isShared_3528_; uint8_t v_isSharedCheck_3532_; 
lean_dec(v_ref_3491_);
lean_dec_ref(v_validate_3489_);
lean_dec(v_attrDescrs_3488_);
v_a_3525_ = lean_ctor_get(v___x_3503_, 0);
v_isSharedCheck_3532_ = !lean_is_exclusive(v___x_3503_);
if (v_isSharedCheck_3532_ == 0)
{
v___x_3527_ = v___x_3503_;
v_isShared_3528_ = v_isSharedCheck_3532_;
goto v_resetjp_3526_;
}
else
{
lean_inc(v_a_3525_);
lean_dec(v___x_3503_);
v___x_3527_ = lean_box(0);
v_isShared_3528_ = v_isSharedCheck_3532_;
goto v_resetjp_3526_;
}
v_resetjp_3526_:
{
lean_object* v___x_3530_; 
if (v_isShared_3528_ == 0)
{
v___x_3530_ = v___x_3527_;
goto v_reusejp_3529_;
}
else
{
lean_object* v_reuseFailAlloc_3531_; 
v_reuseFailAlloc_3531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3531_, 0, v_a_3525_);
v___x_3530_ = v_reuseFailAlloc_3531_;
goto v_reusejp_3529_;
}
v_reusejp_3529_:
{
return v___x_3530_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___boxed(lean_object* v_attrDescrs_3533_, lean_object* v_validate_3534_, lean_object* v_applicationTime_3535_, lean_object* v_ref_3536_, lean_object* v_a_3537_){
_start:
{
uint8_t v_applicationTime_boxed_3538_; lean_object* v_res_3539_; 
v_applicationTime_boxed_3538_ = lean_unbox(v_applicationTime_3535_);
v_res_3539_ = l_Lean_registerEnumAttributes___redArg(v_attrDescrs_3533_, v_validate_3534_, v_applicationTime_boxed_3538_, v_ref_3536_);
return v_res_3539_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes(lean_object* v_00_u03b1_3540_, lean_object* v_attrDescrs_3541_, lean_object* v_validate_3542_, uint8_t v_applicationTime_3543_, lean_object* v_ref_3544_){
_start:
{
lean_object* v___x_3546_; 
v___x_3546_ = l_Lean_registerEnumAttributes___redArg(v_attrDescrs_3541_, v_validate_3542_, v_applicationTime_3543_, v_ref_3544_);
return v___x_3546_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___boxed(lean_object* v_00_u03b1_3547_, lean_object* v_attrDescrs_3548_, lean_object* v_validate_3549_, lean_object* v_applicationTime_3550_, lean_object* v_ref_3551_, lean_object* v_a_3552_){
_start:
{
uint8_t v_applicationTime_boxed_3553_; lean_object* v_res_3554_; 
v_applicationTime_boxed_3553_ = lean_unbox(v_applicationTime_3550_);
v_res_3554_ = l_Lean_registerEnumAttributes(v_00_u03b1_3547_, v_attrDescrs_3548_, v_validate_3549_, v_applicationTime_boxed_3553_, v_ref_3551_);
return v_res_3554_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0(lean_object* v_00_u03b1_3555_, lean_object* v_env_3556_, lean_object* v_as_3557_, size_t v_i_3558_, size_t v_stop_3559_, lean_object* v_b_3560_){
_start:
{
lean_object* v___x_3561_; 
v___x_3561_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg(v_env_3556_, v_as_3557_, v_i_3558_, v_stop_3559_, v_b_3560_);
return v___x_3561_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___boxed(lean_object* v_00_u03b1_3562_, lean_object* v_env_3563_, lean_object* v_as_3564_, lean_object* v_i_3565_, lean_object* v_stop_3566_, lean_object* v_b_3567_){
_start:
{
size_t v_i_boxed_3568_; size_t v_stop_boxed_3569_; lean_object* v_res_3570_; 
v_i_boxed_3568_ = lean_unbox_usize(v_i_3565_);
lean_dec(v_i_3565_);
v_stop_boxed_3569_ = lean_unbox_usize(v_stop_3566_);
lean_dec(v_stop_3566_);
v_res_3570_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0(v_00_u03b1_3562_, v_env_3563_, v_as_3564_, v_i_boxed_3568_, v_stop_boxed_3569_, v_b_3567_);
lean_dec_ref(v_as_3564_);
return v_res_3570_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerEnumAttributes_spec__1(lean_object* v_00_u03b1_3571_, lean_object* v_newState_3572_, lean_object* v_x_3573_, lean_object* v_x_3574_){
_start:
{
lean_object* v___x_3575_; 
v___x_3575_ = l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___redArg(v_newState_3572_, v_x_3573_, v_x_3574_);
return v___x_3575_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___boxed(lean_object* v_00_u03b1_3576_, lean_object* v_newState_3577_, lean_object* v_x_3578_, lean_object* v_x_3579_){
_start:
{
lean_object* v_res_3580_; 
v_res_3580_ = l_List_foldl___at___00Lean_registerEnumAttributes_spec__1(v_00_u03b1_3576_, v_newState_3577_, v_x_3578_, v_x_3579_);
lean_dec(v_newState_3577_);
return v_res_3580_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2(lean_object* v_00_u03b1_3581_, lean_object* v_validate_3582_, lean_object* v_a_3583_, lean_object* v_ref_3584_, uint8_t v_applicationTime_3585_, lean_object* v_a_3586_, lean_object* v_a_3587_){
_start:
{
lean_object* v___x_3588_; 
v___x_3588_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg(v_validate_3582_, v_a_3583_, v_ref_3584_, v_applicationTime_3585_, v_a_3586_, v_a_3587_);
return v___x_3588_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___boxed(lean_object* v_00_u03b1_3589_, lean_object* v_validate_3590_, lean_object* v_a_3591_, lean_object* v_ref_3592_, lean_object* v_applicationTime_3593_, lean_object* v_a_3594_, lean_object* v_a_3595_){
_start:
{
uint8_t v_applicationTime_boxed_3596_; lean_object* v_res_3597_; 
v_applicationTime_boxed_3596_ = lean_unbox(v_applicationTime_3593_);
v_res_3597_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2(v_00_u03b1_3589_, v_validate_3590_, v_a_3591_, v_ref_3592_, v_applicationTime_boxed_3596_, v_a_3594_, v_a_3595_);
return v_res_3597_;
}
}
LEAN_EXPORT lean_object* l_Lean_EnumAttributes_getValue___redArg(lean_object* v_inst_3598_, lean_object* v_attr_3599_, lean_object* v_env_3600_, lean_object* v_decl_3601_){
_start:
{
lean_object* v___x_3602_; lean_object* v___x_3603_; 
v___x_3602_ = lean_box(1);
v___x_3603_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3600_, v_decl_3601_);
if (lean_obj_tag(v___x_3603_) == 0)
{
lean_object* v_ext_3604_; lean_object* v_toEnvExtension_3605_; lean_object* v_asyncMode_3606_; lean_object* v___x_3607_; lean_object* v___x_3608_; 
lean_dec(v_inst_3598_);
v_ext_3604_ = lean_ctor_get(v_attr_3599_, 1);
lean_inc_ref(v_ext_3604_);
lean_dec_ref(v_attr_3599_);
v_toEnvExtension_3605_ = lean_ctor_get(v_ext_3604_, 0);
v_asyncMode_3606_ = lean_ctor_get(v_toEnvExtension_3605_, 2);
lean_inc(v_asyncMode_3606_);
lean_inc(v_decl_3601_);
v___x_3607_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3602_, v_ext_3604_, v_env_3600_, v_asyncMode_3606_, v_decl_3601_);
lean_dec(v_asyncMode_3606_);
lean_dec_ref(v_ext_3604_);
v___x_3608_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_3607_, v_decl_3601_);
lean_dec(v_decl_3601_);
lean_dec(v___x_3607_);
return v___x_3608_;
}
else
{
lean_object* v_val_3609_; lean_object* v_ext_3610_; lean_object* v___x_3612_; uint8_t v_isShared_3613_; uint8_t v_isSharedCheck_3640_; 
v_val_3609_ = lean_ctor_get(v___x_3603_, 0);
lean_inc(v_val_3609_);
lean_dec_ref_known(v___x_3603_, 1);
v_ext_3610_ = lean_ctor_get(v_attr_3599_, 1);
v_isSharedCheck_3640_ = !lean_is_exclusive(v_attr_3599_);
if (v_isSharedCheck_3640_ == 0)
{
lean_object* v_unused_3641_; 
v_unused_3641_ = lean_ctor_get(v_attr_3599_, 0);
lean_dec(v_unused_3641_);
v___x_3612_ = v_attr_3599_;
v_isShared_3613_ = v_isSharedCheck_3640_;
goto v_resetjp_3611_;
}
else
{
lean_inc(v_ext_3610_);
lean_dec(v_attr_3599_);
v___x_3612_ = lean_box(0);
v_isShared_3613_ = v_isSharedCheck_3640_;
goto v_resetjp_3611_;
}
v_resetjp_3611_:
{
uint8_t v___x_3614_; lean_object* v___x_3615_; lean_object* v___x_3616_; lean_object* v___x_3617_; uint8_t v___x_3618_; 
v___x_3614_ = 0;
v___x_3615_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_3602_, v_ext_3610_, v_env_3600_, v_val_3609_, v___x_3614_);
lean_dec(v_val_3609_);
lean_dec_ref(v_env_3600_);
lean_dec_ref(v_ext_3610_);
v___x_3616_ = lean_unsigned_to_nat(0u);
v___x_3617_ = lean_array_get_size(v___x_3615_);
v___x_3618_ = lean_nat_dec_lt(v___x_3616_, v___x_3617_);
if (v___x_3618_ == 0)
{
lean_object* v___x_3619_; 
lean_dec_ref(v___x_3615_);
lean_del_object(v___x_3612_);
lean_dec(v_decl_3601_);
lean_dec(v_inst_3598_);
v___x_3619_ = lean_box(0);
return v___x_3619_;
}
else
{
lean_object* v___x_3620_; lean_object* v___x_3621_; uint8_t v___x_3622_; 
v___x_3620_ = lean_unsigned_to_nat(1u);
v___x_3621_ = lean_nat_sub(v___x_3617_, v___x_3620_);
v___x_3622_ = lean_nat_dec_le(v___x_3616_, v___x_3621_);
if (v___x_3622_ == 0)
{
lean_object* v___x_3623_; 
lean_dec(v___x_3621_);
lean_dec_ref(v___x_3615_);
lean_del_object(v___x_3612_);
lean_dec(v_decl_3601_);
lean_dec(v_inst_3598_);
v___x_3623_ = lean_box(0);
return v___x_3623_;
}
else
{
lean_object* v___f_3624_; lean_object* v___x_3626_; 
v___f_3624_ = ((lean_object*)(l_Lean_ParametricAttribute_getParam_x3f___redArg___closed__1));
if (v_isShared_3613_ == 0)
{
lean_ctor_set(v___x_3612_, 1, v_inst_3598_);
lean_ctor_set(v___x_3612_, 0, v_decl_3601_);
v___x_3626_ = v___x_3612_;
goto v_reusejp_3625_;
}
else
{
lean_object* v_reuseFailAlloc_3639_; 
v_reuseFailAlloc_3639_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3639_, 0, v_decl_3601_);
lean_ctor_set(v_reuseFailAlloc_3639_, 1, v_inst_3598_);
v___x_3626_ = v_reuseFailAlloc_3639_;
goto v_reusejp_3625_;
}
v_reusejp_3625_:
{
lean_object* v___x_3627_; lean_object* v___x_3628_; 
v___x_3627_ = ((lean_object*)(l_Lean_ParametricAttribute_getParam_x3f___redArg___closed__2));
v___x_3628_ = l_Array_binSearchAux___redArg(v___f_3624_, v___x_3627_, v___x_3615_, v___x_3626_, v___x_3616_, v___x_3621_);
lean_dec_ref(v___x_3615_);
if (lean_obj_tag(v___x_3628_) == 0)
{
lean_object* v___x_3629_; 
v___x_3629_ = lean_box(0);
return v___x_3629_;
}
else
{
lean_object* v_val_3630_; lean_object* v___x_3632_; uint8_t v_isShared_3633_; uint8_t v_isSharedCheck_3638_; 
v_val_3630_ = lean_ctor_get(v___x_3628_, 0);
v_isSharedCheck_3638_ = !lean_is_exclusive(v___x_3628_);
if (v_isSharedCheck_3638_ == 0)
{
v___x_3632_ = v___x_3628_;
v_isShared_3633_ = v_isSharedCheck_3638_;
goto v_resetjp_3631_;
}
else
{
lean_inc(v_val_3630_);
lean_dec(v___x_3628_);
v___x_3632_ = lean_box(0);
v_isShared_3633_ = v_isSharedCheck_3638_;
goto v_resetjp_3631_;
}
v_resetjp_3631_:
{
lean_object* v_snd_3634_; lean_object* v___x_3636_; 
v_snd_3634_ = lean_ctor_get(v_val_3630_, 1);
lean_inc(v_snd_3634_);
lean_dec(v_val_3630_);
if (v_isShared_3633_ == 0)
{
lean_ctor_set(v___x_3632_, 0, v_snd_3634_);
v___x_3636_ = v___x_3632_;
goto v_reusejp_3635_;
}
else
{
lean_object* v_reuseFailAlloc_3637_; 
v_reuseFailAlloc_3637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3637_, 0, v_snd_3634_);
v___x_3636_ = v_reuseFailAlloc_3637_;
goto v_reusejp_3635_;
}
v_reusejp_3635_:
{
return v___x_3636_;
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
LEAN_EXPORT lean_object* l_Lean_EnumAttributes_getValue(lean_object* v_00_u03b1_3642_, lean_object* v_inst_3643_, lean_object* v_attr_3644_, lean_object* v_env_3645_, lean_object* v_decl_3646_){
_start:
{
lean_object* v___x_3647_; 
v___x_3647_ = l_Lean_EnumAttributes_getValue___redArg(v_inst_3643_, v_attr_3644_, v_env_3645_, v_decl_3646_);
return v___x_3647_;
}
}
LEAN_EXPORT lean_object* l_Lean_EnumAttributes_setValue___redArg(lean_object* v_attrs_3656_, lean_object* v_env_3657_, lean_object* v_decl_3658_, lean_object* v_val_3659_){
_start:
{
lean_object* v_ext_3660_; lean_object* v___x_3662_; uint8_t v_isShared_3663_; uint8_t v_isSharedCheck_3724_; 
v_ext_3660_ = lean_ctor_get(v_attrs_3656_, 1);
v_isSharedCheck_3724_ = !lean_is_exclusive(v_attrs_3656_);
if (v_isSharedCheck_3724_ == 0)
{
lean_object* v_unused_3725_; 
v_unused_3725_ = lean_ctor_get(v_attrs_3656_, 0);
lean_dec(v_unused_3725_);
v___x_3662_ = v_attrs_3656_;
v_isShared_3663_ = v_isSharedCheck_3724_;
goto v_resetjp_3661_;
}
else
{
lean_inc(v_ext_3660_);
lean_dec(v_attrs_3656_);
v___x_3662_ = lean_box(0);
v_isShared_3663_ = v_isSharedCheck_3724_;
goto v_resetjp_3661_;
}
v_resetjp_3661_:
{
lean_object* v_toEnvExtension_3664_; lean_object* v_name_3665_; lean_object* v___x_3666_; uint8_t v___x_3667_; lean_object* v___x_3668_; lean_object* v___x_3669_; lean_object* v___x_3670_; lean_object* v___x_3671_; lean_object* v___x_3672_; lean_object* v___x_3673_; lean_object* v___x_3674_; lean_object* v_pfx_3675_; lean_object* v___x_3676_; 
v_toEnvExtension_3664_ = lean_ctor_get(v_ext_3660_, 0);
v_name_3665_ = lean_ctor_get(v_ext_3660_, 1);
v___x_3666_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__0));
v___x_3667_ = 1;
lean_inc(v_name_3665_);
v___x_3668_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_3665_, v___x_3667_);
v___x_3669_ = lean_string_append(v___x_3666_, v___x_3668_);
lean_dec_ref(v___x_3668_);
v___x_3670_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__1));
v___x_3671_ = lean_string_append(v___x_3669_, v___x_3670_);
lean_inc(v_decl_3658_);
v___x_3672_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_decl_3658_, v___x_3667_);
v___x_3673_ = lean_string_append(v___x_3671_, v___x_3672_);
lean_dec_ref(v___x_3672_);
v___x_3674_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__4));
v_pfx_3675_ = lean_string_append(v___x_3673_, v___x_3674_);
v___x_3676_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3657_, v_decl_3658_);
if (lean_obj_tag(v___x_3676_) == 0)
{
lean_object* v_asyncMode_3677_; uint8_t v___x_3684_; 
v_asyncMode_3677_ = lean_ctor_get(v_toEnvExtension_3664_, 2);
lean_inc(v_asyncMode_3677_);
lean_inc(v_decl_3658_);
lean_inc_ref(v_env_3657_);
v___x_3684_ = l_Lean_EnvExtension_asyncMayModify___redArg(v_env_3657_, v_decl_3658_, v_asyncMode_3677_);
if (v___x_3684_ == 0)
{
lean_object* v___x_3685_; lean_object* v___x_3686_; lean_object* v___y_3688_; lean_object* v___x_3692_; 
lean_dec(v_asyncMode_3677_);
lean_del_object(v___x_3662_);
lean_dec_ref(v_ext_3660_);
lean_dec(v_val_3659_);
lean_dec(v_decl_3658_);
v___x_3685_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__2));
v___x_3686_ = lean_string_append(v_pfx_3675_, v___x_3685_);
v___x_3692_ = l_Lean_Environment_asyncPrefix_x3f(v_env_3657_);
if (lean_obj_tag(v___x_3692_) == 0)
{
lean_object* v___x_3693_; 
v___x_3693_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__3));
v___y_3688_ = v___x_3693_;
goto v___jp_3687_;
}
else
{
lean_object* v_val_3694_; lean_object* v___x_3695_; lean_object* v___x_3696_; lean_object* v___x_3697_; lean_object* v___x_3698_; lean_object* v___x_3699_; lean_object* v___x_3700_; 
v_val_3694_ = lean_ctor_get(v___x_3692_, 0);
lean_inc(v_val_3694_);
lean_dec_ref_known(v___x_3692_, 1);
v___x_3695_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__4));
v___x_3696_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_val_3694_, v___x_3667_);
v___x_3697_ = l_addParenHeuristic(v___x_3696_);
v___x_3698_ = lean_string_append(v___x_3695_, v___x_3697_);
lean_dec_ref(v___x_3697_);
v___x_3699_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__5));
v___x_3700_ = lean_string_append(v___x_3698_, v___x_3699_);
v___y_3688_ = v___x_3700_;
goto v___jp_3687_;
}
v___jp_3687_:
{
lean_object* v___x_3689_; lean_object* v___x_3690_; lean_object* v___x_3691_; 
v___x_3689_ = lean_string_append(v___x_3686_, v___y_3688_);
lean_dec_ref(v___y_3688_);
v___x_3690_ = lean_string_append(v___x_3689_, v___x_3674_);
v___x_3691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3691_, 0, v___x_3690_);
return v___x_3691_;
}
}
else
{
lean_object* v___x_3701_; lean_object* v___x_3702_; lean_object* v___x_3703_; 
v___x_3701_ = lean_box(1);
lean_inc(v_decl_3658_);
lean_inc_ref(v_env_3657_);
v___x_3702_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3701_, v_ext_3660_, v_env_3657_, v_asyncMode_3677_, v_decl_3658_);
v___x_3703_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_3702_, v_decl_3658_);
lean_dec(v___x_3702_);
if (lean_obj_tag(v___x_3703_) == 0)
{
lean_dec_ref(v_pfx_3675_);
goto v___jp_3678_;
}
else
{
lean_object* v___x_3705_; uint8_t v_isShared_3706_; uint8_t v_isSharedCheck_3712_; 
v_isSharedCheck_3712_ = !lean_is_exclusive(v___x_3703_);
if (v_isSharedCheck_3712_ == 0)
{
lean_object* v_unused_3713_; 
v_unused_3713_ = lean_ctor_get(v___x_3703_, 0);
lean_dec(v_unused_3713_);
v___x_3705_ = v___x_3703_;
v_isShared_3706_ = v_isSharedCheck_3712_;
goto v_resetjp_3704_;
}
else
{
lean_dec(v___x_3703_);
v___x_3705_ = lean_box(0);
v_isShared_3706_ = v_isSharedCheck_3712_;
goto v_resetjp_3704_;
}
v_resetjp_3704_:
{
if (v___x_3684_ == 0)
{
lean_del_object(v___x_3705_);
lean_dec_ref(v_pfx_3675_);
goto v___jp_3678_;
}
else
{
lean_object* v___x_3707_; lean_object* v___x_3708_; lean_object* v___x_3710_; 
lean_dec(v_asyncMode_3677_);
lean_del_object(v___x_3662_);
lean_dec_ref(v_ext_3660_);
lean_dec(v_val_3659_);
lean_dec(v_decl_3658_);
lean_dec_ref(v_env_3657_);
v___x_3707_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__6));
v___x_3708_ = lean_string_append(v_pfx_3675_, v___x_3707_);
if (v_isShared_3706_ == 0)
{
lean_ctor_set_tag(v___x_3705_, 0);
lean_ctor_set(v___x_3705_, 0, v___x_3708_);
v___x_3710_ = v___x_3705_;
goto v_reusejp_3709_;
}
else
{
lean_object* v_reuseFailAlloc_3711_; 
v_reuseFailAlloc_3711_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3711_, 0, v___x_3708_);
v___x_3710_ = v_reuseFailAlloc_3711_;
goto v_reusejp_3709_;
}
v_reusejp_3709_:
{
return v___x_3710_;
}
}
}
}
}
v___jp_3678_:
{
lean_object* v___x_3680_; 
lean_inc(v_decl_3658_);
if (v_isShared_3663_ == 0)
{
lean_ctor_set(v___x_3662_, 1, v_val_3659_);
lean_ctor_set(v___x_3662_, 0, v_decl_3658_);
v___x_3680_ = v___x_3662_;
goto v_reusejp_3679_;
}
else
{
lean_object* v_reuseFailAlloc_3683_; 
v_reuseFailAlloc_3683_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3683_, 0, v_decl_3658_);
lean_ctor_set(v_reuseFailAlloc_3683_, 1, v_val_3659_);
v___x_3680_ = v_reuseFailAlloc_3683_;
goto v_reusejp_3679_;
}
v_reusejp_3679_:
{
lean_object* v___x_3681_; lean_object* v___x_3682_; 
v___x_3681_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_ext_3660_, v_env_3657_, v___x_3680_, v_asyncMode_3677_, v_decl_3658_);
lean_dec(v_asyncMode_3677_);
v___x_3682_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3682_, 0, v___x_3681_);
return v___x_3682_;
}
}
}
else
{
lean_object* v___x_3715_; uint8_t v_isShared_3716_; uint8_t v_isSharedCheck_3722_; 
lean_del_object(v___x_3662_);
lean_dec_ref(v_ext_3660_);
lean_dec(v_val_3659_);
lean_dec(v_decl_3658_);
lean_dec_ref(v_env_3657_);
v_isSharedCheck_3722_ = !lean_is_exclusive(v___x_3676_);
if (v_isSharedCheck_3722_ == 0)
{
lean_object* v_unused_3723_; 
v_unused_3723_ = lean_ctor_get(v___x_3676_, 0);
lean_dec(v_unused_3723_);
v___x_3715_ = v___x_3676_;
v_isShared_3716_ = v_isSharedCheck_3722_;
goto v_resetjp_3714_;
}
else
{
lean_dec(v___x_3676_);
v___x_3715_ = lean_box(0);
v_isShared_3716_ = v_isSharedCheck_3722_;
goto v_resetjp_3714_;
}
v_resetjp_3714_:
{
lean_object* v___x_3717_; lean_object* v___x_3718_; lean_object* v___x_3720_; 
v___x_3717_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__7));
v___x_3718_ = lean_string_append(v_pfx_3675_, v___x_3717_);
if (v_isShared_3716_ == 0)
{
lean_ctor_set_tag(v___x_3715_, 0);
lean_ctor_set(v___x_3715_, 0, v___x_3718_);
v___x_3720_ = v___x_3715_;
goto v_reusejp_3719_;
}
else
{
lean_object* v_reuseFailAlloc_3721_; 
v_reuseFailAlloc_3721_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3721_, 0, v___x_3718_);
v___x_3720_ = v_reuseFailAlloc_3721_;
goto v_reusejp_3719_;
}
v_reusejp_3719_:
{
return v___x_3720_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_EnumAttributes_setValue(lean_object* v_00_u03b1_3726_, lean_object* v_attrs_3727_, lean_object* v_env_3728_, lean_object* v_decl_3729_, lean_object* v_val_3730_){
_start:
{
lean_object* v___x_3731_; 
v___x_3731_ = l_Lean_EnumAttributes_setValue___redArg(v_attrs_3727_, v_env_3728_, v_decl_3729_, v_val_3730_);
return v___x_3731_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_2990505691____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3733_; lean_object* v___x_3734_; lean_object* v___x_3735_; 
v___x_3733_ = lean_obj_once(&l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_, &l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2__once, _init_l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_);
v___x_3734_ = lean_st_mk_ref(v___x_3733_);
v___x_3735_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3735_, 0, v___x_3734_);
return v___x_3735_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_2990505691____hygCtx___hyg_2____boxed(lean_object* v_a_3736_){
_start:
{
lean_object* v_res_3737_; 
v_res_3737_ = l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_2990505691____hygCtx___hyg_2_();
return v_res_3737_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerAttributeImplBuilder(lean_object* v_builderId_3740_, lean_object* v_builder_3741_){
_start:
{
lean_object* v___x_3743_; lean_object* v___x_3744_; uint8_t v___x_3745_; 
v___x_3743_ = l_Lean_attributeImplBuilderTableRef;
v___x_3744_ = lean_st_ref_get(v___x_3743_);
v___x_3745_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(v___x_3744_, v_builderId_3740_);
lean_dec(v___x_3744_);
if (v___x_3745_ == 0)
{
lean_object* v___x_3746_; lean_object* v___x_3747_; lean_object* v___x_3748_; lean_object* v___x_3749_; 
v___x_3746_ = lean_st_ref_take(v___x_3743_);
v___x_3747_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1___redArg(v___x_3746_, v_builderId_3740_, v_builder_3741_);
v___x_3748_ = lean_st_ref_set(v___x_3743_, v___x_3747_);
v___x_3749_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3749_, 0, v___x_3748_);
return v___x_3749_;
}
else
{
lean_object* v___x_3750_; lean_object* v___x_3751_; lean_object* v___x_3752_; lean_object* v___x_3753_; lean_object* v___x_3754_; lean_object* v___x_3755_; lean_object* v___x_3756_; 
lean_dec_ref(v_builder_3741_);
v___x_3750_ = ((lean_object*)(l_Lean_registerAttributeImplBuilder___closed__0));
v___x_3751_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_builderId_3740_, v___x_3745_);
v___x_3752_ = lean_string_append(v___x_3750_, v___x_3751_);
lean_dec_ref(v___x_3751_);
v___x_3753_ = ((lean_object*)(l_Lean_registerAttributeImplBuilder___closed__1));
v___x_3754_ = lean_string_append(v___x_3752_, v___x_3753_);
v___x_3755_ = lean_mk_io_user_error(v___x_3754_);
v___x_3756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3756_, 0, v___x_3755_);
return v___x_3756_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerAttributeImplBuilder___boxed(lean_object* v_builderId_3757_, lean_object* v_builder_3758_, lean_object* v_a_3759_){
_start:
{
lean_object* v_res_3760_; 
v_res_3760_ = l_Lean_registerAttributeImplBuilder(v_builderId_3757_, v_builder_3758_);
return v_res_3760_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___redArg(lean_object* v_e_3761_){
_start:
{
if (lean_obj_tag(v_e_3761_) == 0)
{
lean_object* v_a_3763_; lean_object* v___x_3765_; uint8_t v_isShared_3766_; uint8_t v_isSharedCheck_3771_; 
v_a_3763_ = lean_ctor_get(v_e_3761_, 0);
v_isSharedCheck_3771_ = !lean_is_exclusive(v_e_3761_);
if (v_isSharedCheck_3771_ == 0)
{
v___x_3765_ = v_e_3761_;
v_isShared_3766_ = v_isSharedCheck_3771_;
goto v_resetjp_3764_;
}
else
{
lean_inc(v_a_3763_);
lean_dec(v_e_3761_);
v___x_3765_ = lean_box(0);
v_isShared_3766_ = v_isSharedCheck_3771_;
goto v_resetjp_3764_;
}
v_resetjp_3764_:
{
lean_object* v___x_3767_; lean_object* v___x_3769_; 
v___x_3767_ = lean_mk_io_user_error(v_a_3763_);
if (v_isShared_3766_ == 0)
{
lean_ctor_set_tag(v___x_3765_, 1);
lean_ctor_set(v___x_3765_, 0, v___x_3767_);
v___x_3769_ = v___x_3765_;
goto v_reusejp_3768_;
}
else
{
lean_object* v_reuseFailAlloc_3770_; 
v_reuseFailAlloc_3770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3770_, 0, v___x_3767_);
v___x_3769_ = v_reuseFailAlloc_3770_;
goto v_reusejp_3768_;
}
v_reusejp_3768_:
{
return v___x_3769_;
}
}
}
else
{
lean_object* v_a_3772_; lean_object* v___x_3774_; uint8_t v_isShared_3775_; uint8_t v_isSharedCheck_3779_; 
v_a_3772_ = lean_ctor_get(v_e_3761_, 0);
v_isSharedCheck_3779_ = !lean_is_exclusive(v_e_3761_);
if (v_isSharedCheck_3779_ == 0)
{
v___x_3774_ = v_e_3761_;
v_isShared_3775_ = v_isSharedCheck_3779_;
goto v_resetjp_3773_;
}
else
{
lean_inc(v_a_3772_);
lean_dec(v_e_3761_);
v___x_3774_ = lean_box(0);
v_isShared_3775_ = v_isSharedCheck_3779_;
goto v_resetjp_3773_;
}
v_resetjp_3773_:
{
lean_object* v___x_3777_; 
if (v_isShared_3775_ == 0)
{
lean_ctor_set_tag(v___x_3774_, 0);
v___x_3777_ = v___x_3774_;
goto v_reusejp_3776_;
}
else
{
lean_object* v_reuseFailAlloc_3778_; 
v_reuseFailAlloc_3778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3778_, 0, v_a_3772_);
v___x_3777_ = v_reuseFailAlloc_3778_;
goto v_reusejp_3776_;
}
v_reusejp_3776_:
{
return v___x_3777_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___redArg___boxed(lean_object* v_e_3780_, lean_object* v_a_3781_){
_start:
{
lean_object* v_res_3782_; 
v_res_3782_ = l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___redArg(v_e_3780_);
return v_res_3782_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1(lean_object* v_00_u03b1_3783_, lean_object* v_e_3784_){
_start:
{
lean_object* v___x_3786_; 
v___x_3786_ = l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___redArg(v_e_3784_);
return v___x_3786_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___boxed(lean_object* v_00_u03b1_3787_, lean_object* v_e_3788_, lean_object* v_a_3789_){
_start:
{
lean_object* v_res_3790_; 
v_res_3790_ = l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1(v_00_u03b1_3787_, v_e_3788_);
return v_res_3790_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___redArg(lean_object* v_a_3791_, lean_object* v_x_3792_){
_start:
{
if (lean_obj_tag(v_x_3792_) == 0)
{
lean_object* v___x_3793_; 
v___x_3793_ = lean_box(0);
return v___x_3793_;
}
else
{
lean_object* v_key_3794_; lean_object* v_value_3795_; lean_object* v_tail_3796_; uint8_t v___x_3797_; 
v_key_3794_ = lean_ctor_get(v_x_3792_, 0);
v_value_3795_ = lean_ctor_get(v_x_3792_, 1);
v_tail_3796_ = lean_ctor_get(v_x_3792_, 2);
v___x_3797_ = lean_name_eq(v_key_3794_, v_a_3791_);
if (v___x_3797_ == 0)
{
v_x_3792_ = v_tail_3796_;
goto _start;
}
else
{
lean_object* v___x_3799_; 
lean_inc(v_value_3795_);
v___x_3799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3799_, 0, v_value_3795_);
return v___x_3799_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___redArg___boxed(lean_object* v_a_3800_, lean_object* v_x_3801_){
_start:
{
lean_object* v_res_3802_; 
v_res_3802_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___redArg(v_a_3800_, v_x_3801_);
lean_dec(v_x_3801_);
lean_dec(v_a_3800_);
return v_res_3802_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(lean_object* v_m_3803_, lean_object* v_a_3804_){
_start:
{
lean_object* v_buckets_3805_; lean_object* v___x_3806_; uint64_t v___y_3808_; 
v_buckets_3805_ = lean_ctor_get(v_m_3803_, 1);
v___x_3806_ = lean_array_get_size(v_buckets_3805_);
if (lean_obj_tag(v_a_3804_) == 0)
{
uint64_t v___x_3822_; 
v___x_3822_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg___closed__0);
v___y_3808_ = v___x_3822_;
goto v___jp_3807_;
}
else
{
uint64_t v_hash_3823_; 
v_hash_3823_ = lean_ctor_get_uint64(v_a_3804_, sizeof(void*)*2);
v___y_3808_ = v_hash_3823_;
goto v___jp_3807_;
}
v___jp_3807_:
{
uint64_t v___x_3809_; uint64_t v___x_3810_; uint64_t v_fold_3811_; uint64_t v___x_3812_; uint64_t v___x_3813_; uint64_t v___x_3814_; size_t v___x_3815_; size_t v___x_3816_; size_t v___x_3817_; size_t v___x_3818_; size_t v___x_3819_; lean_object* v___x_3820_; lean_object* v___x_3821_; 
v___x_3809_ = 32ULL;
v___x_3810_ = lean_uint64_shift_right(v___y_3808_, v___x_3809_);
v_fold_3811_ = lean_uint64_xor(v___y_3808_, v___x_3810_);
v___x_3812_ = 16ULL;
v___x_3813_ = lean_uint64_shift_right(v_fold_3811_, v___x_3812_);
v___x_3814_ = lean_uint64_xor(v_fold_3811_, v___x_3813_);
v___x_3815_ = lean_uint64_to_usize(v___x_3814_);
v___x_3816_ = lean_usize_of_nat(v___x_3806_);
v___x_3817_ = ((size_t)1ULL);
v___x_3818_ = lean_usize_sub(v___x_3816_, v___x_3817_);
v___x_3819_ = lean_usize_land(v___x_3815_, v___x_3818_);
v___x_3820_ = lean_array_uget_borrowed(v_buckets_3805_, v___x_3819_);
v___x_3821_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___redArg(v_a_3804_, v___x_3820_);
return v___x_3821_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg___boxed(lean_object* v_m_3824_, lean_object* v_a_3825_){
_start:
{
lean_object* v_res_3826_; 
v_res_3826_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(v_m_3824_, v_a_3825_);
lean_dec(v_a_3825_);
lean_dec_ref(v_m_3824_);
return v_res_3826_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAttributeImplOfEntry(lean_object* v_e_3828_){
_start:
{
lean_object* v___x_3830_; lean_object* v___x_3831_; lean_object* v_builderId_3832_; lean_object* v_ref_3833_; lean_object* v_args_3834_; lean_object* v___x_3835_; 
v___x_3830_ = l_Lean_attributeImplBuilderTableRef;
v___x_3831_ = lean_st_ref_get(v___x_3830_);
v_builderId_3832_ = lean_ctor_get(v_e_3828_, 0);
lean_inc(v_builderId_3832_);
v_ref_3833_ = lean_ctor_get(v_e_3828_, 1);
lean_inc(v_ref_3833_);
v_args_3834_ = lean_ctor_get(v_e_3828_, 2);
lean_inc(v_args_3834_);
lean_dec_ref(v_e_3828_);
v___x_3835_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(v___x_3831_, v_builderId_3832_);
lean_dec(v___x_3831_);
if (lean_obj_tag(v___x_3835_) == 0)
{
lean_object* v___x_3836_; uint8_t v___x_3837_; lean_object* v___x_3838_; lean_object* v___x_3839_; lean_object* v___x_3840_; lean_object* v___x_3841_; lean_object* v___x_3842_; lean_object* v___x_3843_; 
lean_dec(v_args_3834_);
lean_dec(v_ref_3833_);
v___x_3836_ = ((lean_object*)(l_Lean_mkAttributeImplOfEntry___closed__0));
v___x_3837_ = 1;
v___x_3838_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_builderId_3832_, v___x_3837_);
v___x_3839_ = lean_string_append(v___x_3836_, v___x_3838_);
lean_dec_ref(v___x_3838_);
v___x_3840_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__4));
v___x_3841_ = lean_string_append(v___x_3839_, v___x_3840_);
v___x_3842_ = lean_mk_io_user_error(v___x_3841_);
v___x_3843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3843_, 0, v___x_3842_);
return v___x_3843_;
}
else
{
lean_object* v_val_3844_; lean_object* v___x_3845_; lean_object* v___x_3846_; 
lean_dec(v_builderId_3832_);
v_val_3844_ = lean_ctor_get(v___x_3835_, 0);
lean_inc(v_val_3844_);
lean_dec_ref_known(v___x_3835_, 1);
v___x_3845_ = lean_apply_2(v_val_3844_, v_ref_3833_, v_args_3834_);
v___x_3846_ = l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___redArg(v___x_3845_);
return v___x_3846_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkAttributeImplOfEntry___boxed(lean_object* v_e_3847_, lean_object* v_a_3848_){
_start:
{
lean_object* v_res_3849_; 
v_res_3849_ = l_Lean_mkAttributeImplOfEntry(v_e_3847_);
return v_res_3849_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0(lean_object* v_00_u03b2_3850_, lean_object* v_m_3851_, lean_object* v_a_3852_){
_start:
{
lean_object* v___x_3853_; 
v___x_3853_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(v_m_3851_, v_a_3852_);
return v___x_3853_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___boxed(lean_object* v_00_u03b2_3854_, lean_object* v_m_3855_, lean_object* v_a_3856_){
_start:
{
lean_object* v_res_3857_; 
v_res_3857_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0(v_00_u03b2_3854_, v_m_3855_, v_a_3856_);
lean_dec(v_a_3856_);
lean_dec_ref(v_m_3855_);
return v_res_3857_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0(lean_object* v_00_u03b2_3858_, lean_object* v_a_3859_, lean_object* v_x_3860_){
_start:
{
lean_object* v___x_3861_; 
v___x_3861_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___redArg(v_a_3859_, v_x_3860_);
return v___x_3861_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3862_, lean_object* v_a_3863_, lean_object* v_x_3864_){
_start:
{
lean_object* v_res_3865_; 
v_res_3865_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0(v_00_u03b2_3862_, v_a_3863_, v_x_3864_);
lean_dec(v_x_3864_);
lean_dec(v_a_3863_);
return v_res_3865_;
}
}
static lean_object* _init_l_Lean_instInhabitedAttributeExtensionState_default___closed__0(void){
_start:
{
lean_object* v___x_3866_; lean_object* v___x_3867_; lean_object* v___x_3868_; 
v___x_3866_ = lean_obj_once(&l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_, &l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2__once, _init_l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_);
v___x_3867_ = lean_box(0);
v___x_3868_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3868_, 0, v___x_3867_);
lean_ctor_set(v___x_3868_, 1, v___x_3866_);
return v___x_3868_;
}
}
static lean_object* _init_l_Lean_instInhabitedAttributeExtensionState_default(void){
_start:
{
lean_object* v___x_3869_; 
v___x_3869_ = lean_obj_once(&l_Lean_instInhabitedAttributeExtensionState_default___closed__0, &l_Lean_instInhabitedAttributeExtensionState_default___closed__0_once, _init_l_Lean_instInhabitedAttributeExtensionState_default___closed__0);
return v___x_3869_;
}
}
static lean_object* _init_l_Lean_instInhabitedAttributeExtensionState(void){
_start:
{
lean_object* v___x_3870_; 
v___x_3870_ = l_Lean_instInhabitedAttributeExtensionState_default;
return v___x_3870_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_AttributeExtension_mkInitial(){
_start:
{
lean_object* v___x_3872_; lean_object* v___x_3873_; lean_object* v___x_3874_; lean_object* v___x_3875_; lean_object* v___x_3876_; 
v___x_3872_ = l_Lean_attributeMapRef;
v___x_3873_ = lean_st_ref_get(v___x_3872_);
v___x_3874_ = lean_box(0);
v___x_3875_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3875_, 0, v___x_3874_);
lean_ctor_set(v___x_3875_, 1, v___x_3873_);
v___x_3876_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3876_, 0, v___x_3875_);
return v___x_3876_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_AttributeExtension_mkInitial___boxed(lean_object* v_a_3877_){
_start:
{
lean_object* v_res_3878_; 
v_res_3878_ = l___private_Lean_Attributes_0__Lean_AttributeExtension_mkInitial();
return v_res_3878_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAttributeImplOfConstantUnsafe(lean_object* v_env_3884_, lean_object* v_opts_3885_, lean_object* v_declName_3886_){
_start:
{
uint8_t v___x_3889_; lean_object* v___x_3890_; 
v___x_3889_ = 0;
lean_inc(v_declName_3886_);
lean_inc_ref(v_env_3884_);
v___x_3890_ = l_Lean_Environment_find_x3f(v_env_3884_, v_declName_3886_, v___x_3889_);
if (lean_obj_tag(v___x_3890_) == 0)
{
lean_object* v___x_3891_; uint8_t v___x_3892_; lean_object* v___x_3893_; lean_object* v___x_3894_; lean_object* v___x_3895_; lean_object* v___x_3896_; lean_object* v___x_3897_; 
lean_dec_ref(v_env_3884_);
v___x_3891_ = ((lean_object*)(l_Lean_mkAttributeImplOfConstantUnsafe___closed__2));
v___x_3892_ = 1;
v___x_3893_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_declName_3886_, v___x_3892_);
v___x_3894_ = lean_string_append(v___x_3891_, v___x_3893_);
lean_dec_ref(v___x_3893_);
v___x_3895_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__4));
v___x_3896_ = lean_string_append(v___x_3894_, v___x_3895_);
v___x_3897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3897_, 0, v___x_3896_);
return v___x_3897_;
}
else
{
lean_object* v_val_3898_; lean_object* v___x_3899_; 
v_val_3898_ = lean_ctor_get(v___x_3890_, 0);
lean_inc(v_val_3898_);
lean_dec_ref_known(v___x_3890_, 1);
v___x_3899_ = l_Lean_ConstantInfo_type(v_val_3898_);
lean_dec(v_val_3898_);
if (lean_obj_tag(v___x_3899_) == 4)
{
lean_object* v_declName_3900_; 
v_declName_3900_ = lean_ctor_get(v___x_3899_, 0);
lean_inc(v_declName_3900_);
lean_dec_ref_known(v___x_3899_, 2);
if (lean_obj_tag(v_declName_3900_) == 1)
{
lean_object* v_pre_3901_; 
v_pre_3901_ = lean_ctor_get(v_declName_3900_, 0);
lean_inc(v_pre_3901_);
if (lean_obj_tag(v_pre_3901_) == 1)
{
lean_object* v_pre_3902_; 
v_pre_3902_ = lean_ctor_get(v_pre_3901_, 0);
if (lean_obj_tag(v_pre_3902_) == 0)
{
lean_object* v_str_3903_; lean_object* v_str_3904_; lean_object* v___x_3905_; uint8_t v___x_3906_; 
v_str_3903_ = lean_ctor_get(v_declName_3900_, 1);
lean_inc_ref(v_str_3903_);
lean_dec_ref_known(v_declName_3900_, 2);
v_str_3904_ = lean_ctor_get(v_pre_3901_, 1);
lean_inc_ref(v_str_3904_);
lean_dec_ref_known(v_pre_3901_, 2);
v___x_3905_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__0));
v___x_3906_ = lean_string_dec_eq(v_str_3904_, v___x_3905_);
lean_dec_ref(v_str_3904_);
if (v___x_3906_ == 0)
{
lean_dec_ref(v_str_3903_);
lean_dec(v_declName_3886_);
lean_dec_ref(v_env_3884_);
goto v___jp_3887_;
}
else
{
lean_object* v___x_3907_; uint8_t v___x_3908_; 
v___x_3907_ = ((lean_object*)(l_Lean_mkAttributeImplOfConstantUnsafe___closed__3));
v___x_3908_ = lean_string_dec_eq(v_str_3903_, v___x_3907_);
lean_dec_ref(v_str_3903_);
if (v___x_3908_ == 0)
{
lean_dec(v_declName_3886_);
lean_dec_ref(v_env_3884_);
goto v___jp_3887_;
}
else
{
lean_object* v___x_3909_; 
v___x_3909_ = l_Lean_Environment_evalConst___redArg(v_env_3884_, v_opts_3885_, v_declName_3886_, v___x_3908_);
lean_dec(v_declName_3886_);
lean_dec_ref(v_env_3884_);
return v___x_3909_;
}
}
}
else
{
lean_dec_ref_known(v_pre_3901_, 2);
lean_dec_ref_known(v_declName_3900_, 2);
lean_dec(v_declName_3886_);
lean_dec_ref(v_env_3884_);
goto v___jp_3887_;
}
}
else
{
lean_dec_ref_known(v_declName_3900_, 2);
lean_dec(v_pre_3901_);
lean_dec(v_declName_3886_);
lean_dec_ref(v_env_3884_);
goto v___jp_3887_;
}
}
else
{
lean_dec(v_declName_3900_);
lean_dec(v_declName_3886_);
lean_dec_ref(v_env_3884_);
goto v___jp_3887_;
}
}
else
{
lean_dec_ref(v___x_3899_);
lean_dec(v_declName_3886_);
lean_dec_ref(v_env_3884_);
goto v___jp_3887_;
}
}
v___jp_3887_:
{
lean_object* v___x_3888_; 
v___x_3888_ = ((lean_object*)(l_Lean_mkAttributeImplOfConstantUnsafe___closed__1));
return v___x_3888_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkAttributeImplOfConstantUnsafe___boxed(lean_object* v_env_3910_, lean_object* v_opts_3911_, lean_object* v_declName_3912_){
_start:
{
lean_object* v_res_3913_; 
v_res_3913_ = l_Lean_mkAttributeImplOfConstantUnsafe(v_env_3910_, v_opts_3911_, v_declName_3912_);
lean_dec_ref(v_opts_3911_);
return v_res_3913_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg(lean_object* v_as_3914_, size_t v_i_3915_, size_t v_stop_3916_, lean_object* v_b_3917_){
_start:
{
uint8_t v___x_3919_; 
v___x_3919_ = lean_usize_dec_eq(v_i_3915_, v_stop_3916_);
if (v___x_3919_ == 0)
{
lean_object* v___x_3920_; lean_object* v___x_3921_; 
v___x_3920_ = lean_array_uget_borrowed(v_as_3914_, v_i_3915_);
lean_inc(v___x_3920_);
v___x_3921_ = l_Lean_mkAttributeImplOfEntry(v___x_3920_);
if (lean_obj_tag(v___x_3921_) == 0)
{
lean_object* v_a_3922_; lean_object* v_toAttributeImplCore_3923_; lean_object* v_name_3924_; lean_object* v___x_3925_; size_t v___x_3926_; size_t v___x_3927_; 
v_a_3922_ = lean_ctor_get(v___x_3921_, 0);
lean_inc(v_a_3922_);
lean_dec_ref_known(v___x_3921_, 1);
v_toAttributeImplCore_3923_ = lean_ctor_get(v_a_3922_, 0);
v_name_3924_ = lean_ctor_get(v_toAttributeImplCore_3923_, 1);
lean_inc(v_name_3924_);
v___x_3925_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1___redArg(v_b_3917_, v_name_3924_, v_a_3922_);
v___x_3926_ = ((size_t)1ULL);
v___x_3927_ = lean_usize_add(v_i_3915_, v___x_3926_);
v_i_3915_ = v___x_3927_;
v_b_3917_ = v___x_3925_;
goto _start;
}
else
{
lean_object* v_a_3929_; lean_object* v___x_3931_; uint8_t v_isShared_3932_; uint8_t v_isSharedCheck_3936_; 
lean_dec_ref(v_b_3917_);
v_a_3929_ = lean_ctor_get(v___x_3921_, 0);
v_isSharedCheck_3936_ = !lean_is_exclusive(v___x_3921_);
if (v_isSharedCheck_3936_ == 0)
{
v___x_3931_ = v___x_3921_;
v_isShared_3932_ = v_isSharedCheck_3936_;
goto v_resetjp_3930_;
}
else
{
lean_inc(v_a_3929_);
lean_dec(v___x_3921_);
v___x_3931_ = lean_box(0);
v_isShared_3932_ = v_isSharedCheck_3936_;
goto v_resetjp_3930_;
}
v_resetjp_3930_:
{
lean_object* v___x_3934_; 
if (v_isShared_3932_ == 0)
{
v___x_3934_ = v___x_3931_;
goto v_reusejp_3933_;
}
else
{
lean_object* v_reuseFailAlloc_3935_; 
v_reuseFailAlloc_3935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3935_, 0, v_a_3929_);
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
else
{
lean_object* v___x_3937_; 
v___x_3937_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3937_, 0, v_b_3917_);
return v___x_3937_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg___boxed(lean_object* v_as_3938_, lean_object* v_i_3939_, lean_object* v_stop_3940_, lean_object* v_b_3941_, lean_object* v___y_3942_){
_start:
{
size_t v_i_boxed_3943_; size_t v_stop_boxed_3944_; lean_object* v_res_3945_; 
v_i_boxed_3943_ = lean_unbox_usize(v_i_3939_);
lean_dec(v_i_3939_);
v_stop_boxed_3944_ = lean_unbox_usize(v_stop_3940_);
lean_dec(v_stop_3940_);
v_res_3945_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg(v_as_3938_, v_i_boxed_3943_, v_stop_boxed_3944_, v_b_3941_);
lean_dec_ref(v_as_3938_);
return v_res_3945_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__1(lean_object* v_as_3946_, size_t v_i_3947_, size_t v_stop_3948_, lean_object* v_b_3949_, lean_object* v___y_3950_){
_start:
{
lean_object* v_a_3953_; lean_object* v___y_3958_; uint8_t v___x_3960_; 
v___x_3960_ = lean_usize_dec_eq(v_i_3947_, v_stop_3948_);
if (v___x_3960_ == 0)
{
lean_object* v___x_3961_; lean_object* v___x_3962_; lean_object* v___x_3963_; uint8_t v___x_3964_; 
v___x_3961_ = lean_array_uget_borrowed(v_as_3946_, v_i_3947_);
v___x_3962_ = lean_unsigned_to_nat(0u);
v___x_3963_ = lean_array_get_size(v___x_3961_);
v___x_3964_ = lean_nat_dec_lt(v___x_3962_, v___x_3963_);
if (v___x_3964_ == 0)
{
v_a_3953_ = v_b_3949_;
goto v___jp_3952_;
}
else
{
uint8_t v___x_3965_; 
v___x_3965_ = lean_nat_dec_le(v___x_3963_, v___x_3963_);
if (v___x_3965_ == 0)
{
if (v___x_3964_ == 0)
{
v_a_3953_ = v_b_3949_;
goto v___jp_3952_;
}
else
{
size_t v___x_3966_; size_t v___x_3967_; lean_object* v___x_3968_; 
v___x_3966_ = ((size_t)0ULL);
v___x_3967_ = lean_usize_of_nat(v___x_3963_);
v___x_3968_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg(v___x_3961_, v___x_3966_, v___x_3967_, v_b_3949_);
v___y_3958_ = v___x_3968_;
goto v___jp_3957_;
}
}
else
{
size_t v___x_3969_; size_t v___x_3970_; lean_object* v___x_3971_; 
v___x_3969_ = ((size_t)0ULL);
v___x_3970_ = lean_usize_of_nat(v___x_3963_);
v___x_3971_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg(v___x_3961_, v___x_3969_, v___x_3970_, v_b_3949_);
v___y_3958_ = v___x_3971_;
goto v___jp_3957_;
}
}
}
else
{
lean_object* v___x_3972_; 
v___x_3972_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3972_, 0, v_b_3949_);
return v___x_3972_;
}
v___jp_3952_:
{
size_t v___x_3954_; size_t v___x_3955_; 
v___x_3954_ = ((size_t)1ULL);
v___x_3955_ = lean_usize_add(v_i_3947_, v___x_3954_);
v_i_3947_ = v___x_3955_;
v_b_3949_ = v_a_3953_;
goto _start;
}
v___jp_3957_:
{
if (lean_obj_tag(v___y_3958_) == 0)
{
lean_object* v_a_3959_; 
v_a_3959_ = lean_ctor_get(v___y_3958_, 0);
lean_inc(v_a_3959_);
lean_dec_ref_known(v___y_3958_, 1);
v_a_3953_ = v_a_3959_;
goto v___jp_3952_;
}
else
{
return v___y_3958_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__1___boxed(lean_object* v_as_3973_, lean_object* v_i_3974_, lean_object* v_stop_3975_, lean_object* v_b_3976_, lean_object* v___y_3977_, lean_object* v___y_3978_){
_start:
{
size_t v_i_boxed_3979_; size_t v_stop_boxed_3980_; lean_object* v_res_3981_; 
v_i_boxed_3979_ = lean_unbox_usize(v_i_3974_);
lean_dec(v_i_3974_);
v_stop_boxed_3980_ = lean_unbox_usize(v_stop_3975_);
lean_dec(v_stop_3975_);
v_res_3981_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__1(v_as_3973_, v_i_boxed_3979_, v_stop_boxed_3980_, v_b_3976_, v___y_3977_);
lean_dec_ref(v___y_3977_);
lean_dec_ref(v_as_3973_);
return v_res_3981_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_AttributeExtension_addImported(lean_object* v_es_3982_, lean_object* v_a_3983_){
_start:
{
lean_object* v_a_3986_; lean_object* v___y_3991_; lean_object* v___x_4001_; lean_object* v___x_4002_; lean_object* v___x_4003_; lean_object* v___x_4004_; uint8_t v___x_4005_; 
v___x_4001_ = l_Lean_attributeMapRef;
v___x_4002_ = lean_st_ref_get(v___x_4001_);
v___x_4003_ = lean_unsigned_to_nat(0u);
v___x_4004_ = lean_array_get_size(v_es_3982_);
v___x_4005_ = lean_nat_dec_lt(v___x_4003_, v___x_4004_);
if (v___x_4005_ == 0)
{
v_a_3986_ = v___x_4002_;
goto v___jp_3985_;
}
else
{
uint8_t v___x_4006_; 
v___x_4006_ = lean_nat_dec_le(v___x_4004_, v___x_4004_);
if (v___x_4006_ == 0)
{
if (v___x_4005_ == 0)
{
v_a_3986_ = v___x_4002_;
goto v___jp_3985_;
}
else
{
size_t v___x_4007_; size_t v___x_4008_; lean_object* v___x_4009_; 
v___x_4007_ = ((size_t)0ULL);
v___x_4008_ = lean_usize_of_nat(v___x_4004_);
v___x_4009_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__1(v_es_3982_, v___x_4007_, v___x_4008_, v___x_4002_, v_a_3983_);
v___y_3991_ = v___x_4009_;
goto v___jp_3990_;
}
}
else
{
size_t v___x_4010_; size_t v___x_4011_; lean_object* v___x_4012_; 
v___x_4010_ = ((size_t)0ULL);
v___x_4011_ = lean_usize_of_nat(v___x_4004_);
v___x_4012_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__1(v_es_3982_, v___x_4010_, v___x_4011_, v___x_4002_, v_a_3983_);
v___y_3991_ = v___x_4012_;
goto v___jp_3990_;
}
}
v___jp_3985_:
{
lean_object* v___x_3987_; lean_object* v___x_3988_; lean_object* v___x_3989_; 
v___x_3987_ = lean_box(0);
v___x_3988_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3988_, 0, v___x_3987_);
lean_ctor_set(v___x_3988_, 1, v_a_3986_);
v___x_3989_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3989_, 0, v___x_3988_);
return v___x_3989_;
}
v___jp_3990_:
{
if (lean_obj_tag(v___y_3991_) == 0)
{
lean_object* v_a_3992_; 
v_a_3992_ = lean_ctor_get(v___y_3991_, 0);
lean_inc(v_a_3992_);
lean_dec_ref_known(v___y_3991_, 1);
v_a_3986_ = v_a_3992_;
goto v___jp_3985_;
}
else
{
lean_object* v_a_3993_; lean_object* v___x_3995_; uint8_t v_isShared_3996_; uint8_t v_isSharedCheck_4000_; 
v_a_3993_ = lean_ctor_get(v___y_3991_, 0);
v_isSharedCheck_4000_ = !lean_is_exclusive(v___y_3991_);
if (v_isSharedCheck_4000_ == 0)
{
v___x_3995_ = v___y_3991_;
v_isShared_3996_ = v_isSharedCheck_4000_;
goto v_resetjp_3994_;
}
else
{
lean_inc(v_a_3993_);
lean_dec(v___y_3991_);
v___x_3995_ = lean_box(0);
v_isShared_3996_ = v_isSharedCheck_4000_;
goto v_resetjp_3994_;
}
v_resetjp_3994_:
{
lean_object* v___x_3998_; 
if (v_isShared_3996_ == 0)
{
v___x_3998_ = v___x_3995_;
goto v_reusejp_3997_;
}
else
{
lean_object* v_reuseFailAlloc_3999_; 
v_reuseFailAlloc_3999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3999_, 0, v_a_3993_);
v___x_3998_ = v_reuseFailAlloc_3999_;
goto v_reusejp_3997_;
}
v_reusejp_3997_:
{
return v___x_3998_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_AttributeExtension_addImported___boxed(lean_object* v_es_4013_, lean_object* v_a_4014_, lean_object* v_a_4015_){
_start:
{
lean_object* v_res_4016_; 
v_res_4016_ = l___private_Lean_Attributes_0__Lean_AttributeExtension_addImported(v_es_4013_, v_a_4014_);
lean_dec_ref(v_a_4014_);
lean_dec_ref(v_es_4013_);
return v_res_4016_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0(lean_object* v_as_4017_, size_t v_i_4018_, size_t v_stop_4019_, lean_object* v_b_4020_, lean_object* v___y_4021_){
_start:
{
lean_object* v___x_4023_; 
v___x_4023_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg(v_as_4017_, v_i_4018_, v_stop_4019_, v_b_4020_);
return v___x_4023_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___boxed(lean_object* v_as_4024_, lean_object* v_i_4025_, lean_object* v_stop_4026_, lean_object* v_b_4027_, lean_object* v___y_4028_, lean_object* v___y_4029_){
_start:
{
size_t v_i_boxed_4030_; size_t v_stop_boxed_4031_; lean_object* v_res_4032_; 
v_i_boxed_4030_ = lean_unbox_usize(v_i_4025_);
lean_dec(v_i_4025_);
v_stop_boxed_4031_ = lean_unbox_usize(v_stop_4026_);
lean_dec(v_stop_4026_);
v_res_4032_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0(v_as_4024_, v_i_boxed_4030_, v_stop_boxed_4031_, v_b_4027_, v___y_4028_);
lean_dec_ref(v___y_4028_);
lean_dec_ref(v_as_4024_);
return v_res_4032_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_addAttrEntry(lean_object* v_s_4033_, lean_object* v_e_4034_){
_start:
{
lean_object* v_snd_4035_; lean_object* v_toAttributeImplCore_4036_; lean_object* v_fst_4037_; lean_object* v___x_4039_; uint8_t v_isShared_4040_; uint8_t v_isSharedCheck_4055_; 
v_snd_4035_ = lean_ctor_get(v_e_4034_, 1);
lean_inc(v_snd_4035_);
v_toAttributeImplCore_4036_ = lean_ctor_get(v_snd_4035_, 0);
v_fst_4037_ = lean_ctor_get(v_e_4034_, 0);
v_isSharedCheck_4055_ = !lean_is_exclusive(v_e_4034_);
if (v_isSharedCheck_4055_ == 0)
{
lean_object* v_unused_4056_; 
v_unused_4056_ = lean_ctor_get(v_e_4034_, 1);
lean_dec(v_unused_4056_);
v___x_4039_ = v_e_4034_;
v_isShared_4040_ = v_isSharedCheck_4055_;
goto v_resetjp_4038_;
}
else
{
lean_inc(v_fst_4037_);
lean_dec(v_e_4034_);
v___x_4039_ = lean_box(0);
v_isShared_4040_ = v_isSharedCheck_4055_;
goto v_resetjp_4038_;
}
v_resetjp_4038_:
{
lean_object* v_newEntries_4041_; lean_object* v_map_4042_; lean_object* v___x_4044_; uint8_t v_isShared_4045_; uint8_t v_isSharedCheck_4054_; 
v_newEntries_4041_ = lean_ctor_get(v_s_4033_, 0);
v_map_4042_ = lean_ctor_get(v_s_4033_, 1);
v_isSharedCheck_4054_ = !lean_is_exclusive(v_s_4033_);
if (v_isSharedCheck_4054_ == 0)
{
v___x_4044_ = v_s_4033_;
v_isShared_4045_ = v_isSharedCheck_4054_;
goto v_resetjp_4043_;
}
else
{
lean_inc(v_map_4042_);
lean_inc(v_newEntries_4041_);
lean_dec(v_s_4033_);
v___x_4044_ = lean_box(0);
v_isShared_4045_ = v_isSharedCheck_4054_;
goto v_resetjp_4043_;
}
v_resetjp_4043_:
{
lean_object* v_name_4046_; lean_object* v___x_4048_; 
v_name_4046_ = lean_ctor_get(v_toAttributeImplCore_4036_, 1);
lean_inc(v_name_4046_);
if (v_isShared_4040_ == 0)
{
lean_ctor_set_tag(v___x_4039_, 1);
lean_ctor_set(v___x_4039_, 1, v_newEntries_4041_);
v___x_4048_ = v___x_4039_;
goto v_reusejp_4047_;
}
else
{
lean_object* v_reuseFailAlloc_4053_; 
v_reuseFailAlloc_4053_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4053_, 0, v_fst_4037_);
lean_ctor_set(v_reuseFailAlloc_4053_, 1, v_newEntries_4041_);
v___x_4048_ = v_reuseFailAlloc_4053_;
goto v_reusejp_4047_;
}
v_reusejp_4047_:
{
lean_object* v___x_4049_; lean_object* v___x_4051_; 
v___x_4049_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1___redArg(v_map_4042_, v_name_4046_, v_snd_4035_);
if (v_isShared_4045_ == 0)
{
lean_ctor_set(v___x_4044_, 1, v___x_4049_);
lean_ctor_set(v___x_4044_, 0, v___x_4048_);
v___x_4051_ = v___x_4044_;
goto v_reusejp_4050_;
}
else
{
lean_object* v_reuseFailAlloc_4052_; 
v_reuseFailAlloc_4052_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4052_, 0, v___x_4048_);
lean_ctor_set(v_reuseFailAlloc_4052_, 1, v___x_4049_);
v___x_4051_ = v_reuseFailAlloc_4052_;
goto v_reusejp_4050_;
}
v_reusejp_4050_:
{
return v___x_4051_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn___lam__0_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(lean_object* v_x_4057_, lean_object* v_s_4058_){
_start:
{
lean_object* v_newEntries_4059_; lean_object* v___x_4060_; lean_object* v___x_4061_; lean_object* v___x_4062_; 
v_newEntries_4059_ = lean_ctor_get(v_s_4058_, 0);
lean_inc(v_newEntries_4059_);
lean_dec_ref(v_s_4058_);
v___x_4060_ = l_List_reverse___redArg(v_newEntries_4059_);
v___x_4061_ = lean_array_mk(v___x_4060_);
lean_inc_ref_n(v___x_4061_, 2);
v___x_4062_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4062_, 0, v___x_4061_);
lean_ctor_set(v___x_4062_, 1, v___x_4061_);
lean_ctor_set(v___x_4062_, 2, v___x_4061_);
return v___x_4062_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn___lam__0_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2____boxed(lean_object* v_x_4063_, lean_object* v_s_4064_){
_start:
{
lean_object* v_res_4065_; 
v_res_4065_ = l___private_Lean_Attributes_0__Lean_initFn___lam__0_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(v_x_4063_, v_s_4064_);
lean_dec_ref(v_x_4063_);
return v_res_4065_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn___lam__1_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(lean_object* v_s_4066_){
_start:
{
lean_object* v_newEntries_4067_; lean_object* v___x_4069_; uint8_t v_isShared_4070_; uint8_t v_isSharedCheck_4078_; 
v_newEntries_4067_ = lean_ctor_get(v_s_4066_, 0);
v_isSharedCheck_4078_ = !lean_is_exclusive(v_s_4066_);
if (v_isSharedCheck_4078_ == 0)
{
lean_object* v_unused_4079_; 
v_unused_4079_ = lean_ctor_get(v_s_4066_, 1);
lean_dec(v_unused_4079_);
v___x_4069_ = v_s_4066_;
v_isShared_4070_ = v_isSharedCheck_4078_;
goto v_resetjp_4068_;
}
else
{
lean_inc(v_newEntries_4067_);
lean_dec(v_s_4066_);
v___x_4069_ = lean_box(0);
v_isShared_4070_ = v_isSharedCheck_4078_;
goto v_resetjp_4068_;
}
v_resetjp_4068_:
{
lean_object* v___x_4071_; lean_object* v___x_4072_; lean_object* v___x_4073_; lean_object* v___x_4074_; lean_object* v___x_4076_; 
v___x_4071_ = ((lean_object*)(l_Lean_registerTagAttribute___lam__2___closed__4));
v___x_4072_ = l_List_lengthTR___redArg(v_newEntries_4067_);
lean_dec(v_newEntries_4067_);
v___x_4073_ = l_Nat_reprFast(v___x_4072_);
v___x_4074_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4074_, 0, v___x_4073_);
if (v_isShared_4070_ == 0)
{
lean_ctor_set_tag(v___x_4069_, 5);
lean_ctor_set(v___x_4069_, 1, v___x_4074_);
lean_ctor_set(v___x_4069_, 0, v___x_4071_);
v___x_4076_ = v___x_4069_;
goto v_reusejp_4075_;
}
else
{
lean_object* v_reuseFailAlloc_4077_; 
v_reuseFailAlloc_4077_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4077_, 0, v___x_4071_);
lean_ctor_set(v_reuseFailAlloc_4077_, 1, v___x_4074_);
v___x_4076_ = v_reuseFailAlloc_4077_;
goto v_reusejp_4075_;
}
v_reusejp_4075_:
{
return v___x_4076_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn___lam__2_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(lean_object* v_s_4080_){
_start:
{
lean_object* v_newEntries_4081_; lean_object* v___x_4082_; lean_object* v___x_4083_; 
v_newEntries_4081_ = lean_ctor_get(v_s_4080_, 0);
lean_inc(v_newEntries_4081_);
lean_dec_ref(v_s_4080_);
v___x_4082_ = l_List_reverse___redArg(v_newEntries_4081_);
v___x_4083_ = lean_array_mk(v___x_4082_);
return v___x_4083_;
}
}
static lean_object* _init_l___private_Lean_Attributes_0__Lean_initFn___closed__7_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4093_; lean_object* v___x_4094_; lean_object* v___f_4095_; lean_object* v___f_4096_; lean_object* v___x_4097_; lean_object* v___x_4098_; lean_object* v___x_4099_; lean_object* v___x_4100_; lean_object* v___x_4101_; 
v___x_4093_ = lean_box(0);
v___x_4094_ = lean_box(2);
v___f_4095_ = ((lean_object*)(l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___f_4096_ = ((lean_object*)(l___private_Lean_Attributes_0__Lean_initFn___closed__0_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___x_4097_ = ((lean_object*)(l___private_Lean_Attributes_0__Lean_initFn___closed__6_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___x_4098_ = ((lean_object*)(l___private_Lean_Attributes_0__Lean_initFn___closed__5_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___x_4099_ = lean_alloc_closure((void*)(l___private_Lean_Attributes_0__Lean_AttributeExtension_mkInitial___boxed), 1, 0);
v___x_4100_ = ((lean_object*)(l___private_Lean_Attributes_0__Lean_initFn___closed__4_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___x_4101_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_4101_, 0, v___x_4100_);
lean_ctor_set(v___x_4101_, 1, v___x_4099_);
lean_ctor_set(v___x_4101_, 2, v___x_4098_);
lean_ctor_set(v___x_4101_, 3, v___x_4097_);
lean_ctor_set(v___x_4101_, 4, v___f_4096_);
lean_ctor_set(v___x_4101_, 5, v___f_4095_);
lean_ctor_set(v___x_4101_, 6, v___x_4094_);
lean_ctor_set(v___x_4101_, 7, v___x_4093_);
return v___x_4101_;
}
}
static lean_object* _init_l___private_Lean_Attributes_0__Lean_initFn___closed__8_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_4102_; lean_object* v___x_4103_; lean_object* v___x_4104_; 
v___f_4102_ = ((lean_object*)(l___private_Lean_Attributes_0__Lean_initFn___closed__2_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___x_4103_ = lean_obj_once(&l___private_Lean_Attributes_0__Lean_initFn___closed__7_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_, &l___private_Lean_Attributes_0__Lean_initFn___closed__7_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2__once, _init_l___private_Lean_Attributes_0__Lean_initFn___closed__7_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_);
v___x_4104_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4104_, 0, v___x_4103_);
lean_ctor_set(v___x_4104_, 1, v___f_4102_);
return v___x_4104_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4106_; lean_object* v___x_4107_; 
v___x_4106_ = lean_obj_once(&l___private_Lean_Attributes_0__Lean_initFn___closed__8_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_, &l___private_Lean_Attributes_0__Lean_initFn___closed__8_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2__once, _init_l___private_Lean_Attributes_0__Lean_initFn___closed__8_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_);
v___x_4107_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_4106_);
return v___x_4107_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2____boxed(lean_object* v_a_4108_){
_start:
{
lean_object* v_res_4109_; 
v_res_4109_ = l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_();
return v_res_4109_;
}
}
LEAN_EXPORT lean_object* l_Lean_isBuiltinAttribute(lean_object* v_n_4110_){
_start:
{
lean_object* v___x_4112_; lean_object* v___x_4113_; uint8_t v___x_4114_; lean_object* v___x_4115_; lean_object* v___x_4116_; 
v___x_4112_ = l_Lean_attributeMapRef;
v___x_4113_ = lean_st_ref_get(v___x_4112_);
v___x_4114_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(v___x_4113_, v_n_4110_);
lean_dec(v___x_4113_);
v___x_4115_ = lean_box(v___x_4114_);
v___x_4116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4116_, 0, v___x_4115_);
return v___x_4116_;
}
}
LEAN_EXPORT lean_object* l_Lean_isBuiltinAttribute___boxed(lean_object* v_n_4117_, lean_object* v_a_4118_){
_start:
{
lean_object* v_res_4119_; 
v_res_4119_ = l_Lean_isBuiltinAttribute(v_n_4117_);
lean_dec(v_n_4117_);
return v_res_4119_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_getBuiltinAttributeNames_spec__0(lean_object* v_x_4120_, lean_object* v_x_4121_){
_start:
{
if (lean_obj_tag(v_x_4121_) == 0)
{
return v_x_4120_;
}
else
{
lean_object* v_key_4122_; lean_object* v_tail_4123_; lean_object* v___x_4124_; 
v_key_4122_ = lean_ctor_get(v_x_4121_, 0);
v_tail_4123_ = lean_ctor_get(v_x_4121_, 2);
lean_inc(v_key_4122_);
v___x_4124_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4124_, 0, v_key_4122_);
lean_ctor_set(v___x_4124_, 1, v_x_4120_);
v_x_4120_ = v___x_4124_;
v_x_4121_ = v_tail_4123_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_getBuiltinAttributeNames_spec__0___boxed(lean_object* v_x_4126_, lean_object* v_x_4127_){
_start:
{
lean_object* v_res_4128_; 
v_res_4128_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_getBuiltinAttributeNames_spec__0(v_x_4126_, v_x_4127_);
lean_dec(v_x_4127_);
return v_res_4128_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1(lean_object* v_as_4129_, size_t v_i_4130_, size_t v_stop_4131_, lean_object* v_b_4132_){
_start:
{
uint8_t v___x_4133_; 
v___x_4133_ = lean_usize_dec_eq(v_i_4130_, v_stop_4131_);
if (v___x_4133_ == 0)
{
lean_object* v___x_4134_; lean_object* v___x_4135_; size_t v___x_4136_; size_t v___x_4137_; 
v___x_4134_ = lean_array_uget_borrowed(v_as_4129_, v_i_4130_);
v___x_4135_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_getBuiltinAttributeNames_spec__0(v_b_4132_, v___x_4134_);
v___x_4136_ = ((size_t)1ULL);
v___x_4137_ = lean_usize_add(v_i_4130_, v___x_4136_);
v_i_4130_ = v___x_4137_;
v_b_4132_ = v___x_4135_;
goto _start;
}
else
{
return v_b_4132_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1___boxed(lean_object* v_as_4139_, lean_object* v_i_4140_, lean_object* v_stop_4141_, lean_object* v_b_4142_){
_start:
{
size_t v_i_boxed_4143_; size_t v_stop_boxed_4144_; lean_object* v_res_4145_; 
v_i_boxed_4143_ = lean_unbox_usize(v_i_4140_);
lean_dec(v_i_4140_);
v_stop_boxed_4144_ = lean_unbox_usize(v_stop_4141_);
lean_dec(v_stop_4141_);
v_res_4145_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1(v_as_4139_, v_i_boxed_4143_, v_stop_boxed_4144_, v_b_4142_);
lean_dec_ref(v_as_4139_);
return v_res_4145_;
}
}
LEAN_EXPORT lean_object* l_Lean_getBuiltinAttributeNames(){
_start:
{
lean_object* v___x_4147_; lean_object* v___x_4148_; lean_object* v_buckets_4149_; lean_object* v___x_4150_; lean_object* v___x_4151_; lean_object* v___x_4152_; uint8_t v___x_4153_; 
v___x_4147_ = l_Lean_attributeMapRef;
v___x_4148_ = lean_st_ref_get(v___x_4147_);
v_buckets_4149_ = lean_ctor_get(v___x_4148_, 1);
lean_inc_ref(v_buckets_4149_);
lean_dec(v___x_4148_);
v___x_4150_ = lean_box(0);
v___x_4151_ = lean_unsigned_to_nat(0u);
v___x_4152_ = lean_array_get_size(v_buckets_4149_);
v___x_4153_ = lean_nat_dec_lt(v___x_4151_, v___x_4152_);
if (v___x_4153_ == 0)
{
lean_object* v___x_4154_; 
lean_dec_ref(v_buckets_4149_);
v___x_4154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4154_, 0, v___x_4150_);
return v___x_4154_;
}
else
{
uint8_t v___x_4155_; 
v___x_4155_ = lean_nat_dec_le(v___x_4152_, v___x_4152_);
if (v___x_4155_ == 0)
{
if (v___x_4153_ == 0)
{
lean_object* v___x_4156_; 
lean_dec_ref(v_buckets_4149_);
v___x_4156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4156_, 0, v___x_4150_);
return v___x_4156_;
}
else
{
size_t v___x_4157_; size_t v___x_4158_; lean_object* v___x_4159_; lean_object* v___x_4160_; 
v___x_4157_ = ((size_t)0ULL);
v___x_4158_ = lean_usize_of_nat(v___x_4152_);
v___x_4159_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1(v_buckets_4149_, v___x_4157_, v___x_4158_, v___x_4150_);
lean_dec_ref(v_buckets_4149_);
v___x_4160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4160_, 0, v___x_4159_);
return v___x_4160_;
}
}
else
{
size_t v___x_4161_; size_t v___x_4162_; lean_object* v___x_4163_; lean_object* v___x_4164_; 
v___x_4161_ = ((size_t)0ULL);
v___x_4162_ = lean_usize_of_nat(v___x_4152_);
v___x_4163_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1(v_buckets_4149_, v___x_4161_, v___x_4162_, v___x_4150_);
lean_dec_ref(v_buckets_4149_);
v___x_4164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4164_, 0, v___x_4163_);
return v___x_4164_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getBuiltinAttributeNames___boxed(lean_object* v_a_4165_){
_start:
{
lean_object* v_res_4166_; 
v_res_4166_ = l_Lean_getBuiltinAttributeNames();
return v_res_4166_;
}
}
LEAN_EXPORT lean_object* l_Lean_getBuiltinAttributeImpl(lean_object* v_attrName_4168_){
_start:
{
lean_object* v___x_4170_; lean_object* v___x_4171_; lean_object* v___x_4172_; 
v___x_4170_ = l_Lean_attributeMapRef;
v___x_4171_ = lean_st_ref_get(v___x_4170_);
v___x_4172_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(v___x_4171_, v_attrName_4168_);
lean_dec(v___x_4171_);
if (lean_obj_tag(v___x_4172_) == 0)
{
lean_object* v___x_4173_; uint8_t v___x_4174_; lean_object* v___x_4175_; lean_object* v___x_4176_; lean_object* v___x_4177_; lean_object* v___x_4178_; lean_object* v___x_4179_; lean_object* v___x_4180_; 
v___x_4173_ = ((lean_object*)(l_Lean_getBuiltinAttributeImpl___closed__0));
v___x_4174_ = 1;
v___x_4175_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_attrName_4168_, v___x_4174_);
v___x_4176_ = lean_string_append(v___x_4173_, v___x_4175_);
lean_dec_ref(v___x_4175_);
v___x_4177_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__4));
v___x_4178_ = lean_string_append(v___x_4176_, v___x_4177_);
v___x_4179_ = lean_mk_io_user_error(v___x_4178_);
v___x_4180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4180_, 0, v___x_4179_);
return v___x_4180_;
}
else
{
lean_object* v_val_4181_; lean_object* v___x_4183_; uint8_t v_isShared_4184_; uint8_t v_isSharedCheck_4188_; 
lean_dec(v_attrName_4168_);
v_val_4181_ = lean_ctor_get(v___x_4172_, 0);
v_isSharedCheck_4188_ = !lean_is_exclusive(v___x_4172_);
if (v_isSharedCheck_4188_ == 0)
{
v___x_4183_ = v___x_4172_;
v_isShared_4184_ = v_isSharedCheck_4188_;
goto v_resetjp_4182_;
}
else
{
lean_inc(v_val_4181_);
lean_dec(v___x_4172_);
v___x_4183_ = lean_box(0);
v_isShared_4184_ = v_isSharedCheck_4188_;
goto v_resetjp_4182_;
}
v_resetjp_4182_:
{
lean_object* v___x_4186_; 
if (v_isShared_4184_ == 0)
{
lean_ctor_set_tag(v___x_4183_, 0);
v___x_4186_ = v___x_4183_;
goto v_reusejp_4185_;
}
else
{
lean_object* v_reuseFailAlloc_4187_; 
v_reuseFailAlloc_4187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4187_, 0, v_val_4181_);
v___x_4186_ = v_reuseFailAlloc_4187_;
goto v_reusejp_4185_;
}
v_reusejp_4185_:
{
return v___x_4186_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getBuiltinAttributeImpl___boxed(lean_object* v_attrName_4189_, lean_object* v_a_4190_){
_start:
{
lean_object* v_res_4191_; 
v_res_4191_ = l_Lean_getBuiltinAttributeImpl(v_attrName_4189_);
return v_res_4191_;
}
}
LEAN_EXPORT uint8_t l_Lean_isAttribute(lean_object* v_env_4192_, lean_object* v_attrName_4193_){
_start:
{
lean_object* v___x_4194_; lean_object* v_toEnvExtension_4195_; lean_object* v_asyncMode_4196_; lean_object* v___x_4197_; lean_object* v___x_4198_; lean_object* v___x_4199_; lean_object* v_map_4200_; uint8_t v___x_4201_; 
v___x_4194_ = l_Lean_attributeExtension;
v_toEnvExtension_4195_ = lean_ctor_get(v___x_4194_, 0);
v_asyncMode_4196_ = lean_ctor_get(v_toEnvExtension_4195_, 2);
v___x_4197_ = l_Lean_instInhabitedAttributeExtensionState_default;
v___x_4198_ = lean_box(0);
v___x_4199_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_4197_, v___x_4194_, v_env_4192_, v_asyncMode_4196_, v___x_4198_);
v_map_4200_ = lean_ctor_get(v___x_4199_, 1);
lean_inc_ref(v_map_4200_);
lean_dec(v___x_4199_);
v___x_4201_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(v_map_4200_, v_attrName_4193_);
lean_dec_ref(v_map_4200_);
return v___x_4201_;
}
}
LEAN_EXPORT lean_object* l_Lean_isAttribute___boxed(lean_object* v_env_4202_, lean_object* v_attrName_4203_){
_start:
{
uint8_t v_res_4204_; lean_object* v_r_4205_; 
v_res_4204_ = l_Lean_isAttribute(v_env_4202_, v_attrName_4203_);
lean_dec(v_attrName_4203_);
v_r_4205_ = lean_box(v_res_4204_);
return v_r_4205_;
}
}
LEAN_EXPORT lean_object* l_Lean_getAttributeNames(lean_object* v_env_4206_){
_start:
{
lean_object* v___x_4207_; lean_object* v_toEnvExtension_4208_; lean_object* v_asyncMode_4209_; lean_object* v___x_4210_; lean_object* v___x_4211_; lean_object* v___x_4212_; lean_object* v_map_4213_; lean_object* v_buckets_4214_; lean_object* v___x_4215_; lean_object* v___x_4216_; lean_object* v___x_4217_; uint8_t v___x_4218_; 
v___x_4207_ = l_Lean_attributeExtension;
v_toEnvExtension_4208_ = lean_ctor_get(v___x_4207_, 0);
v_asyncMode_4209_ = lean_ctor_get(v_toEnvExtension_4208_, 2);
v___x_4210_ = l_Lean_instInhabitedAttributeExtensionState_default;
v___x_4211_ = lean_box(0);
v___x_4212_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_4210_, v___x_4207_, v_env_4206_, v_asyncMode_4209_, v___x_4211_);
v_map_4213_ = lean_ctor_get(v___x_4212_, 1);
lean_inc_ref(v_map_4213_);
lean_dec(v___x_4212_);
v_buckets_4214_ = lean_ctor_get(v_map_4213_, 1);
lean_inc_ref(v_buckets_4214_);
lean_dec_ref(v_map_4213_);
v___x_4215_ = lean_box(0);
v___x_4216_ = lean_unsigned_to_nat(0u);
v___x_4217_ = lean_array_get_size(v_buckets_4214_);
v___x_4218_ = lean_nat_dec_lt(v___x_4216_, v___x_4217_);
if (v___x_4218_ == 0)
{
lean_dec_ref(v_buckets_4214_);
return v___x_4215_;
}
else
{
uint8_t v___x_4219_; 
v___x_4219_ = lean_nat_dec_le(v___x_4217_, v___x_4217_);
if (v___x_4219_ == 0)
{
if (v___x_4218_ == 0)
{
lean_dec_ref(v_buckets_4214_);
return v___x_4215_;
}
else
{
size_t v___x_4220_; size_t v___x_4221_; lean_object* v___x_4222_; 
v___x_4220_ = ((size_t)0ULL);
v___x_4221_ = lean_usize_of_nat(v___x_4217_);
v___x_4222_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1(v_buckets_4214_, v___x_4220_, v___x_4221_, v___x_4215_);
lean_dec_ref(v_buckets_4214_);
return v___x_4222_;
}
}
else
{
size_t v___x_4223_; size_t v___x_4224_; lean_object* v___x_4225_; 
v___x_4223_ = ((size_t)0ULL);
v___x_4224_ = lean_usize_of_nat(v___x_4217_);
v___x_4225_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1(v_buckets_4214_, v___x_4223_, v___x_4224_, v___x_4215_);
lean_dec_ref(v_buckets_4214_);
return v___x_4225_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getAttributeImpl(lean_object* v_env_4226_, lean_object* v_attrName_4227_){
_start:
{
lean_object* v___x_4228_; lean_object* v_toEnvExtension_4229_; lean_object* v_asyncMode_4230_; lean_object* v___x_4231_; lean_object* v___x_4232_; lean_object* v___x_4233_; lean_object* v_map_4234_; lean_object* v___x_4235_; 
v___x_4228_ = l_Lean_attributeExtension;
v_toEnvExtension_4229_ = lean_ctor_get(v___x_4228_, 0);
v_asyncMode_4230_ = lean_ctor_get(v_toEnvExtension_4229_, 2);
v___x_4231_ = l_Lean_instInhabitedAttributeExtensionState_default;
v___x_4232_ = lean_box(0);
v___x_4233_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_4231_, v___x_4228_, v_env_4226_, v_asyncMode_4230_, v___x_4232_);
v_map_4234_ = lean_ctor_get(v___x_4233_, 1);
lean_inc_ref(v_map_4234_);
lean_dec(v___x_4233_);
v___x_4235_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(v_map_4234_, v_attrName_4227_);
lean_dec_ref(v_map_4234_);
if (lean_obj_tag(v___x_4235_) == 0)
{
lean_object* v___x_4236_; uint8_t v___x_4237_; lean_object* v___x_4238_; lean_object* v___x_4239_; lean_object* v___x_4240_; lean_object* v___x_4241_; lean_object* v___x_4242_; 
v___x_4236_ = ((lean_object*)(l_Lean_getBuiltinAttributeImpl___closed__0));
v___x_4237_ = 1;
v___x_4238_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_attrName_4227_, v___x_4237_);
v___x_4239_ = lean_string_append(v___x_4236_, v___x_4238_);
lean_dec_ref(v___x_4238_);
v___x_4240_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__4));
v___x_4241_ = lean_string_append(v___x_4239_, v___x_4240_);
v___x_4242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4242_, 0, v___x_4241_);
return v___x_4242_;
}
else
{
lean_object* v_val_4243_; lean_object* v___x_4245_; uint8_t v_isShared_4246_; uint8_t v_isSharedCheck_4250_; 
lean_dec(v_attrName_4227_);
v_val_4243_ = lean_ctor_get(v___x_4235_, 0);
v_isSharedCheck_4250_ = !lean_is_exclusive(v___x_4235_);
if (v_isSharedCheck_4250_ == 0)
{
v___x_4245_ = v___x_4235_;
v_isShared_4246_ = v_isSharedCheck_4250_;
goto v_resetjp_4244_;
}
else
{
lean_inc(v_val_4243_);
lean_dec(v___x_4235_);
v___x_4245_ = lean_box(0);
v_isShared_4246_ = v_isSharedCheck_4250_;
goto v_resetjp_4244_;
}
v_resetjp_4244_:
{
lean_object* v___x_4248_; 
if (v_isShared_4246_ == 0)
{
v___x_4248_ = v___x_4245_;
goto v_reusejp_4247_;
}
else
{
lean_object* v_reuseFailAlloc_4249_; 
v_reuseFailAlloc_4249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4249_, 0, v_val_4243_);
v___x_4248_ = v_reuseFailAlloc_4249_;
goto v_reusejp_4247_;
}
v_reusejp_4247_:
{
return v___x_4248_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerAttributeOfBuilder(lean_object* v_env_4251_, lean_object* v_builderId_4252_, lean_object* v_ref_4253_, lean_object* v_args_4254_){
_start:
{
lean_object* v_entry_4256_; lean_object* v___x_4257_; 
v_entry_4256_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_entry_4256_, 0, v_builderId_4252_);
lean_ctor_set(v_entry_4256_, 1, v_ref_4253_);
lean_ctor_set(v_entry_4256_, 2, v_args_4254_);
lean_inc_ref(v_entry_4256_);
v___x_4257_ = l_Lean_mkAttributeImplOfEntry(v_entry_4256_);
if (lean_obj_tag(v___x_4257_) == 0)
{
lean_object* v_a_4258_; lean_object* v___x_4260_; uint8_t v_isShared_4261_; uint8_t v_isSharedCheck_4283_; 
v_a_4258_ = lean_ctor_get(v___x_4257_, 0);
v_isSharedCheck_4283_ = !lean_is_exclusive(v___x_4257_);
if (v_isSharedCheck_4283_ == 0)
{
v___x_4260_ = v___x_4257_;
v_isShared_4261_ = v_isSharedCheck_4283_;
goto v_resetjp_4259_;
}
else
{
lean_inc(v_a_4258_);
lean_dec(v___x_4257_);
v___x_4260_ = lean_box(0);
v_isShared_4261_ = v_isSharedCheck_4283_;
goto v_resetjp_4259_;
}
v_resetjp_4259_:
{
lean_object* v_toAttributeImplCore_4262_; lean_object* v_name_4263_; uint8_t v___x_4264_; 
v_toAttributeImplCore_4262_ = lean_ctor_get(v_a_4258_, 0);
v_name_4263_ = lean_ctor_get(v_toAttributeImplCore_4262_, 1);
lean_inc_ref(v_env_4251_);
v___x_4264_ = l_Lean_isAttribute(v_env_4251_, v_name_4263_);
if (v___x_4264_ == 0)
{
lean_object* v___x_4265_; lean_object* v_toEnvExtension_4266_; lean_object* v_asyncMode_4267_; lean_object* v___x_4268_; lean_object* v___x_4269_; lean_object* v___x_4270_; lean_object* v___x_4272_; 
v___x_4265_ = l_Lean_attributeExtension;
v_toEnvExtension_4266_ = lean_ctor_get(v___x_4265_, 0);
v_asyncMode_4267_ = lean_ctor_get(v_toEnvExtension_4266_, 2);
v___x_4268_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4268_, 0, v_entry_4256_);
lean_ctor_set(v___x_4268_, 1, v_a_4258_);
v___x_4269_ = lean_box(0);
v___x_4270_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_4265_, v_env_4251_, v___x_4268_, v_asyncMode_4267_, v___x_4269_);
if (v_isShared_4261_ == 0)
{
lean_ctor_set(v___x_4260_, 0, v___x_4270_);
v___x_4272_ = v___x_4260_;
goto v_reusejp_4271_;
}
else
{
lean_object* v_reuseFailAlloc_4273_; 
v_reuseFailAlloc_4273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4273_, 0, v___x_4270_);
v___x_4272_ = v_reuseFailAlloc_4273_;
goto v_reusejp_4271_;
}
v_reusejp_4271_:
{
return v___x_4272_;
}
}
else
{
lean_object* v___x_4274_; lean_object* v___x_4275_; lean_object* v___x_4276_; lean_object* v___x_4277_; lean_object* v___x_4278_; lean_object* v___x_4279_; lean_object* v___x_4281_; 
lean_inc(v_name_4263_);
lean_dec(v_a_4258_);
lean_dec_ref_known(v_entry_4256_, 3);
lean_dec_ref(v_env_4251_);
v___x_4274_ = ((lean_object*)(l_Lean_registerBuiltinAttribute___closed__2));
v___x_4275_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_4263_, v___x_4264_);
v___x_4276_ = lean_string_append(v___x_4274_, v___x_4275_);
lean_dec_ref(v___x_4275_);
v___x_4277_ = ((lean_object*)(l_Lean_registerBuiltinAttribute___closed__3));
v___x_4278_ = lean_string_append(v___x_4276_, v___x_4277_);
v___x_4279_ = lean_mk_io_user_error(v___x_4278_);
if (v_isShared_4261_ == 0)
{
lean_ctor_set_tag(v___x_4260_, 1);
lean_ctor_set(v___x_4260_, 0, v___x_4279_);
v___x_4281_ = v___x_4260_;
goto v_reusejp_4280_;
}
else
{
lean_object* v_reuseFailAlloc_4282_; 
v_reuseFailAlloc_4282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4282_, 0, v___x_4279_);
v___x_4281_ = v_reuseFailAlloc_4282_;
goto v_reusejp_4280_;
}
v_reusejp_4280_:
{
return v___x_4281_;
}
}
}
}
else
{
lean_object* v_a_4284_; lean_object* v___x_4286_; uint8_t v_isShared_4287_; uint8_t v_isSharedCheck_4291_; 
lean_dec_ref_known(v_entry_4256_, 3);
lean_dec_ref(v_env_4251_);
v_a_4284_ = lean_ctor_get(v___x_4257_, 0);
v_isSharedCheck_4291_ = !lean_is_exclusive(v___x_4257_);
if (v_isSharedCheck_4291_ == 0)
{
v___x_4286_ = v___x_4257_;
v_isShared_4287_ = v_isSharedCheck_4291_;
goto v_resetjp_4285_;
}
else
{
lean_inc(v_a_4284_);
lean_dec(v___x_4257_);
v___x_4286_ = lean_box(0);
v_isShared_4287_ = v_isSharedCheck_4291_;
goto v_resetjp_4285_;
}
v_resetjp_4285_:
{
lean_object* v___x_4289_; 
if (v_isShared_4287_ == 0)
{
v___x_4289_ = v___x_4286_;
goto v_reusejp_4288_;
}
else
{
lean_object* v_reuseFailAlloc_4290_; 
v_reuseFailAlloc_4290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4290_, 0, v_a_4284_);
v___x_4289_ = v_reuseFailAlloc_4290_;
goto v_reusejp_4288_;
}
v_reusejp_4288_:
{
return v___x_4289_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerAttributeOfBuilder___boxed(lean_object* v_env_4292_, lean_object* v_builderId_4293_, lean_object* v_ref_4294_, lean_object* v_args_4295_, lean_object* v_a_4296_){
_start:
{
lean_object* v_res_4297_; 
v_res_4297_ = l_Lean_registerAttributeOfBuilder(v_env_4292_, v_builderId_4293_, v_ref_4294_, v_args_4295_);
return v_res_4297_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg(lean_object* v_x_4298_, lean_object* v___y_4299_, lean_object* v___y_4300_){
_start:
{
if (lean_obj_tag(v_x_4298_) == 0)
{
lean_object* v_a_4302_; lean_object* v___x_4303_; lean_object* v___x_4304_; 
v_a_4302_ = lean_ctor_get(v_x_4298_, 0);
lean_inc(v_a_4302_);
lean_dec_ref_known(v_x_4298_, 1);
v___x_4303_ = l_Lean_stringToMessageData(v_a_4302_);
v___x_4304_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_4303_, v___y_4299_, v___y_4300_);
return v___x_4304_;
}
else
{
lean_object* v_a_4305_; lean_object* v___x_4307_; uint8_t v_isShared_4308_; uint8_t v_isSharedCheck_4312_; 
v_a_4305_ = lean_ctor_get(v_x_4298_, 0);
v_isSharedCheck_4312_ = !lean_is_exclusive(v_x_4298_);
if (v_isSharedCheck_4312_ == 0)
{
v___x_4307_ = v_x_4298_;
v_isShared_4308_ = v_isSharedCheck_4312_;
goto v_resetjp_4306_;
}
else
{
lean_inc(v_a_4305_);
lean_dec(v_x_4298_);
v___x_4307_ = lean_box(0);
v_isShared_4308_ = v_isSharedCheck_4312_;
goto v_resetjp_4306_;
}
v_resetjp_4306_:
{
lean_object* v___x_4310_; 
if (v_isShared_4308_ == 0)
{
lean_ctor_set_tag(v___x_4307_, 0);
v___x_4310_ = v___x_4307_;
goto v_reusejp_4309_;
}
else
{
lean_object* v_reuseFailAlloc_4311_; 
v_reuseFailAlloc_4311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4311_, 0, v_a_4305_);
v___x_4310_ = v_reuseFailAlloc_4311_;
goto v_reusejp_4309_;
}
v_reusejp_4309_:
{
return v___x_4310_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg___boxed(lean_object* v_x_4313_, lean_object* v___y_4314_, lean_object* v___y_4315_, lean_object* v___y_4316_){
_start:
{
lean_object* v_res_4317_; 
v_res_4317_ = l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg(v_x_4313_, v___y_4314_, v___y_4315_);
lean_dec(v___y_4315_);
lean_dec_ref(v___y_4314_);
return v_res_4317_;
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_add(lean_object* v_declName_4318_, lean_object* v_attrName_4319_, lean_object* v_stx_4320_, uint8_t v_kind_4321_, lean_object* v_a_4322_, lean_object* v_a_4323_){
_start:
{
lean_object* v___x_4325_; lean_object* v_env_4326_; lean_object* v___x_4327_; lean_object* v___x_4328_; 
v___x_4325_ = lean_st_ref_get(v_a_4323_);
v_env_4326_ = lean_ctor_get(v___x_4325_, 0);
lean_inc_ref(v_env_4326_);
lean_dec(v___x_4325_);
v___x_4327_ = l_Lean_getAttributeImpl(v_env_4326_, v_attrName_4319_);
v___x_4328_ = l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg(v___x_4327_, v_a_4322_, v_a_4323_);
if (lean_obj_tag(v___x_4328_) == 0)
{
lean_object* v_a_4329_; lean_object* v_add_4330_; lean_object* v___x_4331_; lean_object* v___x_4332_; 
v_a_4329_ = lean_ctor_get(v___x_4328_, 0);
lean_inc(v_a_4329_);
lean_dec_ref_known(v___x_4328_, 1);
v_add_4330_ = lean_ctor_get(v_a_4329_, 1);
lean_inc_ref(v_add_4330_);
lean_dec(v_a_4329_);
v___x_4331_ = lean_box(v_kind_4321_);
lean_inc(v_a_4323_);
lean_inc_ref(v_a_4322_);
v___x_4332_ = lean_apply_6(v_add_4330_, v_declName_4318_, v_stx_4320_, v___x_4331_, v_a_4322_, v_a_4323_, lean_box(0));
return v___x_4332_;
}
else
{
lean_object* v_a_4333_; lean_object* v___x_4335_; uint8_t v_isShared_4336_; uint8_t v_isSharedCheck_4340_; 
lean_dec(v_stx_4320_);
lean_dec(v_declName_4318_);
v_a_4333_ = lean_ctor_get(v___x_4328_, 0);
v_isSharedCheck_4340_ = !lean_is_exclusive(v___x_4328_);
if (v_isSharedCheck_4340_ == 0)
{
v___x_4335_ = v___x_4328_;
v_isShared_4336_ = v_isSharedCheck_4340_;
goto v_resetjp_4334_;
}
else
{
lean_inc(v_a_4333_);
lean_dec(v___x_4328_);
v___x_4335_ = lean_box(0);
v_isShared_4336_ = v_isSharedCheck_4340_;
goto v_resetjp_4334_;
}
v_resetjp_4334_:
{
lean_object* v___x_4338_; 
if (v_isShared_4336_ == 0)
{
v___x_4338_ = v___x_4335_;
goto v_reusejp_4337_;
}
else
{
lean_object* v_reuseFailAlloc_4339_; 
v_reuseFailAlloc_4339_ = lean_alloc_ctor(1, 1, 0);
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
LEAN_EXPORT lean_object* l_Lean_Attribute_add___boxed(lean_object* v_declName_4341_, lean_object* v_attrName_4342_, lean_object* v_stx_4343_, lean_object* v_kind_4344_, lean_object* v_a_4345_, lean_object* v_a_4346_, lean_object* v_a_4347_){
_start:
{
uint8_t v_kind_boxed_4348_; lean_object* v_res_4349_; 
v_kind_boxed_4348_ = lean_unbox(v_kind_4344_);
v_res_4349_ = l_Lean_Attribute_add(v_declName_4341_, v_attrName_4342_, v_stx_4343_, v_kind_boxed_4348_, v_a_4345_, v_a_4346_);
lean_dec(v_a_4346_);
lean_dec_ref(v_a_4345_);
return v_res_4349_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0(lean_object* v_00_u03b1_4350_, lean_object* v_x_4351_, lean_object* v___y_4352_, lean_object* v___y_4353_){
_start:
{
lean_object* v___x_4355_; 
v___x_4355_ = l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg(v_x_4351_, v___y_4352_, v___y_4353_);
return v___x_4355_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___boxed(lean_object* v_00_u03b1_4356_, lean_object* v_x_4357_, lean_object* v___y_4358_, lean_object* v___y_4359_, lean_object* v___y_4360_){
_start:
{
lean_object* v_res_4361_; 
v_res_4361_ = l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0(v_00_u03b1_4356_, v_x_4357_, v___y_4358_, v___y_4359_);
lean_dec(v___y_4359_);
lean_dec_ref(v___y_4358_);
return v_res_4361_;
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_erase(lean_object* v_declName_4362_, lean_object* v_attrName_4363_, lean_object* v_a_4364_, lean_object* v_a_4365_){
_start:
{
lean_object* v___x_4367_; lean_object* v_env_4368_; lean_object* v___x_4369_; lean_object* v___x_4370_; 
v___x_4367_ = lean_st_ref_get(v_a_4365_);
v_env_4368_ = lean_ctor_get(v___x_4367_, 0);
lean_inc_ref(v_env_4368_);
lean_dec(v___x_4367_);
v___x_4369_ = l_Lean_getAttributeImpl(v_env_4368_, v_attrName_4363_);
v___x_4370_ = l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg(v___x_4369_, v_a_4364_, v_a_4365_);
if (lean_obj_tag(v___x_4370_) == 0)
{
lean_object* v_a_4371_; lean_object* v_erase_4372_; lean_object* v___x_4373_; 
v_a_4371_ = lean_ctor_get(v___x_4370_, 0);
lean_inc(v_a_4371_);
lean_dec_ref_known(v___x_4370_, 1);
v_erase_4372_ = lean_ctor_get(v_a_4371_, 2);
lean_inc_ref(v_erase_4372_);
lean_dec(v_a_4371_);
lean_inc(v_a_4365_);
lean_inc_ref(v_a_4364_);
v___x_4373_ = lean_apply_4(v_erase_4372_, v_declName_4362_, v_a_4364_, v_a_4365_, lean_box(0));
return v___x_4373_;
}
else
{
lean_object* v_a_4374_; lean_object* v___x_4376_; uint8_t v_isShared_4377_; uint8_t v_isSharedCheck_4381_; 
lean_dec(v_declName_4362_);
v_a_4374_ = lean_ctor_get(v___x_4370_, 0);
v_isSharedCheck_4381_ = !lean_is_exclusive(v___x_4370_);
if (v_isSharedCheck_4381_ == 0)
{
v___x_4376_ = v___x_4370_;
v_isShared_4377_ = v_isSharedCheck_4381_;
goto v_resetjp_4375_;
}
else
{
lean_inc(v_a_4374_);
lean_dec(v___x_4370_);
v___x_4376_ = lean_box(0);
v_isShared_4377_ = v_isSharedCheck_4381_;
goto v_resetjp_4375_;
}
v_resetjp_4375_:
{
lean_object* v___x_4379_; 
if (v_isShared_4377_ == 0)
{
v___x_4379_ = v___x_4376_;
goto v_reusejp_4378_;
}
else
{
lean_object* v_reuseFailAlloc_4380_; 
v_reuseFailAlloc_4380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4380_, 0, v_a_4374_);
v___x_4379_ = v_reuseFailAlloc_4380_;
goto v_reusejp_4378_;
}
v_reusejp_4378_:
{
return v___x_4379_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_erase___boxed(lean_object* v_declName_4382_, lean_object* v_attrName_4383_, lean_object* v_a_4384_, lean_object* v_a_4385_, lean_object* v_a_4386_){
_start:
{
lean_object* v_res_4387_; 
v_res_4387_ = l_Lean_Attribute_erase(v_declName_4382_, v_attrName_4383_, v_a_4384_, v_a_4385_);
lean_dec(v_a_4385_);
lean_dec_ref(v_a_4384_);
return v_res_4387_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_updateEnvAttributesImpl_spec__0(lean_object* v_x_4388_, lean_object* v_x_4389_){
_start:
{
if (lean_obj_tag(v_x_4389_) == 0)
{
return v_x_4388_;
}
else
{
lean_object* v_key_4390_; lean_object* v_value_4391_; lean_object* v_tail_4392_; lean_object* v_newEntries_4393_; lean_object* v_map_4394_; uint8_t v___x_4395_; 
v_key_4390_ = lean_ctor_get(v_x_4389_, 0);
lean_inc(v_key_4390_);
v_value_4391_ = lean_ctor_get(v_x_4389_, 1);
lean_inc(v_value_4391_);
v_tail_4392_ = lean_ctor_get(v_x_4389_, 2);
lean_inc(v_tail_4392_);
lean_dec_ref_known(v_x_4389_, 3);
v_newEntries_4393_ = lean_ctor_get(v_x_4388_, 0);
v_map_4394_ = lean_ctor_get(v_x_4388_, 1);
v___x_4395_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(v_map_4394_, v_key_4390_);
if (v___x_4395_ == 0)
{
lean_object* v___x_4397_; uint8_t v_isShared_4398_; uint8_t v_isSharedCheck_4404_; 
lean_inc_ref(v_map_4394_);
lean_inc(v_newEntries_4393_);
v_isSharedCheck_4404_ = !lean_is_exclusive(v_x_4388_);
if (v_isSharedCheck_4404_ == 0)
{
lean_object* v_unused_4405_; lean_object* v_unused_4406_; 
v_unused_4405_ = lean_ctor_get(v_x_4388_, 1);
lean_dec(v_unused_4405_);
v_unused_4406_ = lean_ctor_get(v_x_4388_, 0);
lean_dec(v_unused_4406_);
v___x_4397_ = v_x_4388_;
v_isShared_4398_ = v_isSharedCheck_4404_;
goto v_resetjp_4396_;
}
else
{
lean_dec(v_x_4388_);
v___x_4397_ = lean_box(0);
v_isShared_4398_ = v_isSharedCheck_4404_;
goto v_resetjp_4396_;
}
v_resetjp_4396_:
{
lean_object* v___x_4399_; lean_object* v___x_4401_; 
v___x_4399_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1___redArg(v_map_4394_, v_key_4390_, v_value_4391_);
if (v_isShared_4398_ == 0)
{
lean_ctor_set(v___x_4397_, 1, v___x_4399_);
v___x_4401_ = v___x_4397_;
goto v_reusejp_4400_;
}
else
{
lean_object* v_reuseFailAlloc_4403_; 
v_reuseFailAlloc_4403_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4403_, 0, v_newEntries_4393_);
lean_ctor_set(v_reuseFailAlloc_4403_, 1, v___x_4399_);
v___x_4401_ = v_reuseFailAlloc_4403_;
goto v_reusejp_4400_;
}
v_reusejp_4400_:
{
v_x_4388_ = v___x_4401_;
v_x_4389_ = v_tail_4392_;
goto _start;
}
}
}
else
{
lean_dec(v_value_4391_);
lean_dec(v_key_4390_);
v_x_4389_ = v_tail_4392_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_updateEnvAttributesImpl_spec__1(lean_object* v_as_4408_, size_t v_i_4409_, size_t v_stop_4410_, lean_object* v_b_4411_){
_start:
{
uint8_t v___x_4412_; 
v___x_4412_ = lean_usize_dec_eq(v_i_4409_, v_stop_4410_);
if (v___x_4412_ == 0)
{
lean_object* v___x_4413_; lean_object* v___x_4414_; size_t v___x_4415_; size_t v___x_4416_; 
v___x_4413_ = lean_array_uget_borrowed(v_as_4408_, v_i_4409_);
lean_inc(v___x_4413_);
v___x_4414_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_updateEnvAttributesImpl_spec__0(v_b_4411_, v___x_4413_);
v___x_4415_ = ((size_t)1ULL);
v___x_4416_ = lean_usize_add(v_i_4409_, v___x_4415_);
v_i_4409_ = v___x_4416_;
v_b_4411_ = v___x_4414_;
goto _start;
}
else
{
return v_b_4411_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_updateEnvAttributesImpl_spec__1___boxed(lean_object* v_as_4418_, lean_object* v_i_4419_, lean_object* v_stop_4420_, lean_object* v_b_4421_){
_start:
{
size_t v_i_boxed_4422_; size_t v_stop_boxed_4423_; lean_object* v_res_4424_; 
v_i_boxed_4422_ = lean_unbox_usize(v_i_4419_);
lean_dec(v_i_4419_);
v_stop_boxed_4423_ = lean_unbox_usize(v_stop_4420_);
lean_dec(v_stop_4420_);
v_res_4424_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_updateEnvAttributesImpl_spec__1(v_as_4418_, v_i_boxed_4422_, v_stop_boxed_4423_, v_b_4421_);
lean_dec_ref(v_as_4418_);
return v_res_4424_;
}
}
LEAN_EXPORT lean_object* lean_update_env_attributes(lean_object* v_env_4425_){
_start:
{
lean_object* v___x_4427_; lean_object* v___x_4428_; lean_object* v___x_4429_; lean_object* v___y_4431_; lean_object* v_toEnvExtension_4434_; lean_object* v_asyncMode_4435_; lean_object* v_buckets_4436_; lean_object* v___x_4437_; lean_object* v___x_4438_; lean_object* v___x_4439_; lean_object* v___x_4440_; lean_object* v___x_4441_; uint8_t v___x_4442_; 
v___x_4427_ = l_Lean_attributeMapRef;
v___x_4428_ = lean_st_ref_get(v___x_4427_);
v___x_4429_ = l_Lean_attributeExtension;
v_toEnvExtension_4434_ = lean_ctor_get(v___x_4429_, 0);
v_asyncMode_4435_ = lean_ctor_get(v_toEnvExtension_4434_, 2);
v_buckets_4436_ = lean_ctor_get(v___x_4428_, 1);
lean_inc_ref(v_buckets_4436_);
lean_dec(v___x_4428_);
v___x_4437_ = l_Lean_instInhabitedAttributeExtensionState_default;
v___x_4438_ = lean_box(0);
lean_inc_ref(v_env_4425_);
v___x_4439_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_4437_, v___x_4429_, v_env_4425_, v_asyncMode_4435_, v___x_4438_);
v___x_4440_ = lean_unsigned_to_nat(0u);
v___x_4441_ = lean_array_get_size(v_buckets_4436_);
v___x_4442_ = lean_nat_dec_lt(v___x_4440_, v___x_4441_);
if (v___x_4442_ == 0)
{
lean_dec_ref(v_buckets_4436_);
v___y_4431_ = v___x_4439_;
goto v___jp_4430_;
}
else
{
uint8_t v___x_4443_; 
v___x_4443_ = lean_nat_dec_le(v___x_4441_, v___x_4441_);
if (v___x_4443_ == 0)
{
if (v___x_4442_ == 0)
{
lean_dec_ref(v_buckets_4436_);
v___y_4431_ = v___x_4439_;
goto v___jp_4430_;
}
else
{
size_t v___x_4444_; size_t v___x_4445_; lean_object* v___x_4446_; 
v___x_4444_ = ((size_t)0ULL);
v___x_4445_ = lean_usize_of_nat(v___x_4441_);
v___x_4446_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_updateEnvAttributesImpl_spec__1(v_buckets_4436_, v___x_4444_, v___x_4445_, v___x_4439_);
lean_dec_ref(v_buckets_4436_);
v___y_4431_ = v___x_4446_;
goto v___jp_4430_;
}
}
else
{
size_t v___x_4447_; size_t v___x_4448_; lean_object* v___x_4449_; 
v___x_4447_ = ((size_t)0ULL);
v___x_4448_ = lean_usize_of_nat(v___x_4441_);
v___x_4449_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_updateEnvAttributesImpl_spec__1(v_buckets_4436_, v___x_4447_, v___x_4448_, v___x_4439_);
lean_dec_ref(v_buckets_4436_);
v___y_4431_ = v___x_4449_;
goto v___jp_4430_;
}
}
v___jp_4430_:
{
lean_object* v___x_4432_; lean_object* v___x_4433_; 
v___x_4432_ = l_Lean_PersistentEnvExtension_setState___redArg(v___x_4429_, v_env_4425_, v___y_4431_);
v___x_4433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4433_, 0, v___x_4432_);
return v___x_4433_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_updateEnvAttributesImpl___boxed(lean_object* v_env_4450_, lean_object* v_a_4451_){
_start:
{
lean_object* v_res_4452_; 
v_res_4452_ = lean_update_env_attributes(v_env_4450_);
return v_res_4452_;
}
}
LEAN_EXPORT lean_object* lean_get_num_attributes(){
_start:
{
lean_object* v___x_4454_; lean_object* v___x_4455_; lean_object* v_size_4456_; lean_object* v___x_4457_; 
v___x_4454_ = l_Lean_attributeMapRef;
v___x_4455_ = lean_st_ref_get(v___x_4454_);
v_size_4456_ = lean_ctor_get(v___x_4455_, 0);
lean_inc(v_size_4456_);
lean_dec(v___x_4455_);
v___x_4457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4457_, 0, v_size_4456_);
return v___x_4457_;
}
}
LEAN_EXPORT lean_object* l_Lean_getNumBuiltinAttributesImpl___boxed(lean_object* v_a_4458_){
_start:
{
lean_object* v_res_4459_; 
v_res_4459_ = lean_get_num_attributes();
return v_res_4459_;
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
