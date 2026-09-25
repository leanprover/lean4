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
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
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
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
uint8_t l_Lean_EnvExtension_asyncMayModify___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_asyncPrefix_x3f(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_throwError___redArg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_MessageData_nil;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* l_Lean_instInhabitedEnvExtension_default___redArg();
extern lean_object* l_Lean_instInhabitedMessageData_default;
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
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Environment_evalConst___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Array_reverse___redArg(lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__6(lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__6___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_TagAttribute_hasTag(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TagAttribute_hasTag___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg___lam__1___boxed(lean_object*, lean_object*);
static const lean_array_object l_Lean_instInhabitedParametricAttribute_default___redArg___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg___lam__2___closed__0 = (const lean_object*)&l_Lean_instInhabitedParametricAttribute_default___redArg___lam__2___closed__0_value;
static const lean_ctor_object l_Lean_instInhabitedParametricAttribute_default___redArg___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_instInhabitedParametricAttribute_default___redArg___lam__2___closed__0_value),((lean_object*)&l_Lean_instInhabitedParametricAttribute_default___redArg___lam__2___closed__0_value),((lean_object*)&l_Lean_instInhabitedParametricAttribute_default___redArg___lam__2___closed__0_value)}};
static const lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg___lam__2___closed__1 = (const lean_object*)&l_Lean_instInhabitedParametricAttribute_default___redArg___lam__2___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg___lam__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg___lam__3(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg___lam__3___boxed(lean_object*);
static const lean_closure_object l_Lean_instInhabitedParametricAttribute_default___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instInhabitedParametricAttribute_default___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg___closed__0 = (const lean_object*)&l_Lean_instInhabitedParametricAttribute_default___redArg___closed__0_value;
static const lean_closure_object l_Lean_instInhabitedParametricAttribute_default___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instInhabitedParametricAttribute_default___redArg___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg___closed__1 = (const lean_object*)&l_Lean_instInhabitedParametricAttribute_default___redArg___closed__1_value;
static const lean_closure_object l_Lean_instInhabitedParametricAttribute_default___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instInhabitedParametricAttribute_default___redArg___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg___closed__2 = (const lean_object*)&l_Lean_instInhabitedParametricAttribute_default___redArg___closed__2_value;
static const lean_closure_object l_Lean_instInhabitedParametricAttribute_default___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instInhabitedParametricAttribute_default___redArg___lam__3___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg___closed__3 = (const lean_object*)&l_Lean_instInhabitedParametricAttribute_default___redArg___closed__3_value;
static lean_once_cell_t l_Lean_instInhabitedParametricAttribute_default___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg___closed__4;
static lean_once_cell_t l_Lean_instInhabitedParametricAttribute_default___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg();
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lean_instInhabitedParametricAttribute_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedParametricAttribute_default___closed__0;
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute___redArg();
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute___redArg___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___redArg___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___redArg___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___redArg___lam__2___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_instInhabitedEnumAttributes_default___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instInhabitedEnumAttributes_default___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instInhabitedEnumAttributes_default___redArg___closed__0 = (const lean_object*)&l_Lean_instInhabitedEnumAttributes_default___redArg___closed__0_value;
static const lean_closure_object l_Lean_instInhabitedEnumAttributes_default___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instInhabitedEnumAttributes_default___redArg___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instInhabitedEnumAttributes_default___redArg___closed__1 = (const lean_object*)&l_Lean_instInhabitedEnumAttributes_default___redArg___closed__1_value;
static const lean_closure_object l_Lean_instInhabitedEnumAttributes_default___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instInhabitedEnumAttributes_default___redArg___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instInhabitedEnumAttributes_default___redArg___closed__2 = (const lean_object*)&l_Lean_instInhabitedEnumAttributes_default___redArg___closed__2_value;
static lean_once_cell_t l_Lean_instInhabitedEnumAttributes_default___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedEnumAttributes_default___redArg___closed__3;
static lean_once_cell_t l_Lean_instInhabitedEnumAttributes_default___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedEnumAttributes_default___redArg___closed__4;
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___redArg();
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lean_instInhabitedEnumAttributes_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedEnumAttributes_default___closed__0;
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes___redArg();
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes___redArg___boxed(lean_object*);
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
static const lean_closure_object l_Lean_registerEnumAttributes___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_registerTagAttribute___lam__6___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))} };
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
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_ctorElim___redArg(lean_object* v_k_8_){
_start:
{
lean_inc(v_k_8_);
return v_k_8_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_ctorElim___redArg___boxed(lean_object* v_k_9_){
_start:
{
lean_object* v_res_10_; 
v_res_10_ = l_Lean_AttributeApplicationTime_ctorElim___redArg(v_k_9_);
lean_dec(v_k_9_);
return v_res_10_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_ctorElim(lean_object* v_motive_11_, lean_object* v_ctorIdx_12_, uint8_t v_t_13_, lean_object* v_h_14_, lean_object* v_k_15_){
_start:
{
lean_inc(v_k_15_);
return v_k_15_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_ctorElim___boxed(lean_object* v_motive_16_, lean_object* v_ctorIdx_17_, lean_object* v_t_18_, lean_object* v_h_19_, lean_object* v_k_20_){
_start:
{
uint8_t v_t_boxed_21_; lean_object* v_res_22_; 
v_t_boxed_21_ = lean_unbox(v_t_18_);
v_res_22_ = l_Lean_AttributeApplicationTime_ctorElim(v_motive_16_, v_ctorIdx_17_, v_t_boxed_21_, v_h_19_, v_k_20_);
lean_dec(v_k_20_);
lean_dec(v_ctorIdx_17_);
return v_res_22_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_afterTypeChecking_elim___redArg(lean_object* v_afterTypeChecking_23_){
_start:
{
lean_inc(v_afterTypeChecking_23_);
return v_afterTypeChecking_23_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_afterTypeChecking_elim___redArg___boxed(lean_object* v_afterTypeChecking_24_){
_start:
{
lean_object* v_res_25_; 
v_res_25_ = l_Lean_AttributeApplicationTime_afterTypeChecking_elim___redArg(v_afterTypeChecking_24_);
lean_dec(v_afterTypeChecking_24_);
return v_res_25_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_afterTypeChecking_elim(lean_object* v_motive_26_, uint8_t v_t_27_, lean_object* v_h_28_, lean_object* v_afterTypeChecking_29_){
_start:
{
lean_inc(v_afterTypeChecking_29_);
return v_afterTypeChecking_29_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_afterTypeChecking_elim___boxed(lean_object* v_motive_30_, lean_object* v_t_31_, lean_object* v_h_32_, lean_object* v_afterTypeChecking_33_){
_start:
{
uint8_t v_t_boxed_34_; lean_object* v_res_35_; 
v_t_boxed_34_ = lean_unbox(v_t_31_);
v_res_35_ = l_Lean_AttributeApplicationTime_afterTypeChecking_elim(v_motive_30_, v_t_boxed_34_, v_h_32_, v_afterTypeChecking_33_);
lean_dec(v_afterTypeChecking_33_);
return v_res_35_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_afterCompilation_elim___redArg(lean_object* v_afterCompilation_36_){
_start:
{
lean_inc(v_afterCompilation_36_);
return v_afterCompilation_36_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_afterCompilation_elim___redArg___boxed(lean_object* v_afterCompilation_37_){
_start:
{
lean_object* v_res_38_; 
v_res_38_ = l_Lean_AttributeApplicationTime_afterCompilation_elim___redArg(v_afterCompilation_37_);
lean_dec(v_afterCompilation_37_);
return v_res_38_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_afterCompilation_elim(lean_object* v_motive_39_, uint8_t v_t_40_, lean_object* v_h_41_, lean_object* v_afterCompilation_42_){
_start:
{
lean_inc(v_afterCompilation_42_);
return v_afterCompilation_42_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_afterCompilation_elim___boxed(lean_object* v_motive_43_, lean_object* v_t_44_, lean_object* v_h_45_, lean_object* v_afterCompilation_46_){
_start:
{
uint8_t v_t_boxed_47_; lean_object* v_res_48_; 
v_t_boxed_47_ = lean_unbox(v_t_44_);
v_res_48_ = l_Lean_AttributeApplicationTime_afterCompilation_elim(v_motive_43_, v_t_boxed_47_, v_h_45_, v_afterCompilation_46_);
lean_dec(v_afterCompilation_46_);
return v_res_48_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_beforeElaboration_elim___redArg(lean_object* v_beforeElaboration_49_){
_start:
{
lean_inc(v_beforeElaboration_49_);
return v_beforeElaboration_49_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_beforeElaboration_elim___redArg___boxed(lean_object* v_beforeElaboration_50_){
_start:
{
lean_object* v_res_51_; 
v_res_51_ = l_Lean_AttributeApplicationTime_beforeElaboration_elim___redArg(v_beforeElaboration_50_);
lean_dec(v_beforeElaboration_50_);
return v_res_51_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_beforeElaboration_elim(lean_object* v_motive_52_, uint8_t v_t_53_, lean_object* v_h_54_, lean_object* v_beforeElaboration_55_){
_start:
{
lean_inc(v_beforeElaboration_55_);
return v_beforeElaboration_55_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeApplicationTime_beforeElaboration_elim___boxed(lean_object* v_motive_56_, lean_object* v_t_57_, lean_object* v_h_58_, lean_object* v_beforeElaboration_59_){
_start:
{
uint8_t v_t_boxed_60_; lean_object* v_res_61_; 
v_t_boxed_60_ = lean_unbox(v_t_57_);
v_res_61_ = l_Lean_AttributeApplicationTime_beforeElaboration_elim(v_motive_56_, v_t_boxed_60_, v_h_58_, v_beforeElaboration_59_);
lean_dec(v_beforeElaboration_59_);
return v_res_61_;
}
}
static uint8_t _init_l_Lean_instInhabitedAttributeApplicationTime_default(void){
_start:
{
uint8_t v___x_62_; 
v___x_62_ = 0;
return v___x_62_;
}
}
static uint8_t _init_l_Lean_instInhabitedAttributeApplicationTime(void){
_start:
{
uint8_t v___x_63_; 
v___x_63_ = 0;
return v___x_63_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqAttributeApplicationTime_beq(uint8_t v_x_64_, uint8_t v_y_65_){
_start:
{
lean_object* v___x_66_; lean_object* v___x_67_; uint8_t v___x_68_; 
v___x_66_ = l_Lean_AttributeApplicationTime_ctorIdx(v_x_64_);
v___x_67_ = l_Lean_AttributeApplicationTime_ctorIdx(v_y_65_);
v___x_68_ = lean_nat_dec_eq(v___x_66_, v___x_67_);
lean_dec(v___x_67_);
lean_dec(v___x_66_);
return v___x_68_;
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqAttributeApplicationTime_beq___boxed(lean_object* v_x_69_, lean_object* v_y_70_){
_start:
{
uint8_t v_x_21__boxed_71_; uint8_t v_y_22__boxed_72_; uint8_t v_res_73_; lean_object* v_r_74_; 
v_x_21__boxed_71_ = lean_unbox(v_x_69_);
v_y_22__boxed_72_ = lean_unbox(v_y_70_);
v_res_73_ = l_Lean_instBEqAttributeApplicationTime_beq(v_x_21__boxed_71_, v_y_22__boxed_72_);
v_r_74_ = lean_box(v_res_73_);
return v_r_74_;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadLiftImportMAttrM___lam__0(lean_object* v_00_u03b1_77_, lean_object* v_x_78_, lean_object* v___y_79_, lean_object* v___y_80_){
_start:
{
lean_object* v___x_82_; lean_object* v_env_83_; lean_object* v_ref_84_; lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; 
v___x_82_ = lean_st_ref_get(v___y_80_);
v_env_83_ = lean_ctor_get(v___x_82_, 0);
lean_inc_ref(v_env_83_);
lean_dec(v___x_82_);
v_ref_84_ = lean_ctor_get(v___y_79_, 2);
v___x_85_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_79_);
v___x_86_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_86_, 0, v_env_83_);
lean_ctor_set(v___x_86_, 1, v___x_85_);
v___x_87_ = lean_apply_2(v_x_78_, v___x_86_, lean_box(0));
if (lean_obj_tag(v___x_87_) == 0)
{
lean_object* v_a_88_; lean_object* v___x_90_; uint8_t v_isShared_91_; uint8_t v_isSharedCheck_95_; 
v_a_88_ = lean_ctor_get(v___x_87_, 0);
v_isSharedCheck_95_ = !lean_is_exclusive(v___x_87_);
if (v_isSharedCheck_95_ == 0)
{
v___x_90_ = v___x_87_;
v_isShared_91_ = v_isSharedCheck_95_;
goto v_resetjp_89_;
}
else
{
lean_inc(v_a_88_);
lean_dec(v___x_87_);
v___x_90_ = lean_box(0);
v_isShared_91_ = v_isSharedCheck_95_;
goto v_resetjp_89_;
}
v_resetjp_89_:
{
lean_object* v___x_93_; 
if (v_isShared_91_ == 0)
{
v___x_93_ = v___x_90_;
goto v_reusejp_92_;
}
else
{
lean_object* v_reuseFailAlloc_94_; 
v_reuseFailAlloc_94_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_94_, 0, v_a_88_);
v___x_93_ = v_reuseFailAlloc_94_;
goto v_reusejp_92_;
}
v_reusejp_92_:
{
return v___x_93_;
}
}
}
else
{
lean_object* v_a_96_; lean_object* v___x_98_; uint8_t v_isShared_99_; uint8_t v_isSharedCheck_107_; 
v_a_96_ = lean_ctor_get(v___x_87_, 0);
v_isSharedCheck_107_ = !lean_is_exclusive(v___x_87_);
if (v_isSharedCheck_107_ == 0)
{
v___x_98_ = v___x_87_;
v_isShared_99_ = v_isSharedCheck_107_;
goto v_resetjp_97_;
}
else
{
lean_inc(v_a_96_);
lean_dec(v___x_87_);
v___x_98_ = lean_box(0);
v_isShared_99_ = v_isSharedCheck_107_;
goto v_resetjp_97_;
}
v_resetjp_97_:
{
lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_105_; 
v___x_100_ = lean_io_error_to_string(v_a_96_);
v___x_101_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_101_, 0, v___x_100_);
v___x_102_ = l_Lean_MessageData_ofFormat(v___x_101_);
lean_inc(v_ref_84_);
v___x_103_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_103_, 0, v_ref_84_);
lean_ctor_set(v___x_103_, 1, v___x_102_);
if (v_isShared_99_ == 0)
{
lean_ctor_set(v___x_98_, 0, v___x_103_);
v___x_105_ = v___x_98_;
goto v_reusejp_104_;
}
else
{
lean_object* v_reuseFailAlloc_106_; 
v_reuseFailAlloc_106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_106_, 0, v___x_103_);
v___x_105_ = v_reuseFailAlloc_106_;
goto v_reusejp_104_;
}
v_reusejp_104_:
{
return v___x_105_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadLiftImportMAttrM___lam__0___boxed(lean_object* v_00_u03b1_108_, lean_object* v_x_109_, lean_object* v___y_110_, lean_object* v___y_111_, lean_object* v___y_112_){
_start:
{
lean_object* v_res_113_; 
v_res_113_ = l_Lean_instMonadLiftImportMAttrM___lam__0(v_00_u03b1_108_, v_x_109_, v___y_110_, v___y_111_);
lean_dec(v___y_111_);
lean_dec_ref(v___y_110_);
return v_res_113_;
}
}
static lean_object* _init_l_Lean_AttributeImplCore_ref___autoParam___closed__12(void){
_start:
{
lean_object* v___x_142_; lean_object* v___x_143_; 
v___x_142_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__10));
v___x_143_ = l_Lean_mkAtom(v___x_142_);
return v___x_143_;
}
}
static lean_object* _init_l_Lean_AttributeImplCore_ref___autoParam___closed__13(void){
_start:
{
lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; 
v___x_144_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__12, &l_Lean_AttributeImplCore_ref___autoParam___closed__12_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__12);
v___x_145_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__5));
v___x_146_ = lean_array_push(v___x_145_, v___x_144_);
return v___x_146_;
}
}
static lean_object* _init_l_Lean_AttributeImplCore_ref___autoParam___closed__18(void){
_start:
{
lean_object* v___x_155_; lean_object* v___x_156_; 
v___x_155_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__17));
v___x_156_ = l_Lean_mkAtom(v___x_155_);
return v___x_156_;
}
}
static lean_object* _init_l_Lean_AttributeImplCore_ref___autoParam___closed__19(void){
_start:
{
lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; 
v___x_157_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__18, &l_Lean_AttributeImplCore_ref___autoParam___closed__18_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__18);
v___x_158_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__5));
v___x_159_ = lean_array_push(v___x_158_, v___x_157_);
return v___x_159_;
}
}
static lean_object* _init_l_Lean_AttributeImplCore_ref___autoParam___closed__20(void){
_start:
{
lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; 
v___x_160_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__19, &l_Lean_AttributeImplCore_ref___autoParam___closed__19_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__19);
v___x_161_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__16));
v___x_162_ = lean_box(2);
v___x_163_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_163_, 0, v___x_162_);
lean_ctor_set(v___x_163_, 1, v___x_161_);
lean_ctor_set(v___x_163_, 2, v___x_160_);
return v___x_163_;
}
}
static lean_object* _init_l_Lean_AttributeImplCore_ref___autoParam___closed__21(void){
_start:
{
lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; 
v___x_164_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__20, &l_Lean_AttributeImplCore_ref___autoParam___closed__20_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__20);
v___x_165_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__13, &l_Lean_AttributeImplCore_ref___autoParam___closed__13_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__13);
v___x_166_ = lean_array_push(v___x_165_, v___x_164_);
return v___x_166_;
}
}
static lean_object* _init_l_Lean_AttributeImplCore_ref___autoParam___closed__22(void){
_start:
{
lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; 
v___x_167_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__21, &l_Lean_AttributeImplCore_ref___autoParam___closed__21_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__21);
v___x_168_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__11));
v___x_169_ = lean_box(2);
v___x_170_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_170_, 0, v___x_169_);
lean_ctor_set(v___x_170_, 1, v___x_168_);
lean_ctor_set(v___x_170_, 2, v___x_167_);
return v___x_170_;
}
}
static lean_object* _init_l_Lean_AttributeImplCore_ref___autoParam___closed__23(void){
_start:
{
lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; 
v___x_171_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__22, &l_Lean_AttributeImplCore_ref___autoParam___closed__22_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__22);
v___x_172_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__5));
v___x_173_ = lean_array_push(v___x_172_, v___x_171_);
return v___x_173_;
}
}
static lean_object* _init_l_Lean_AttributeImplCore_ref___autoParam___closed__24(void){
_start:
{
lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; 
v___x_174_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__23, &l_Lean_AttributeImplCore_ref___autoParam___closed__23_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__23);
v___x_175_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__9));
v___x_176_ = lean_box(2);
v___x_177_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_177_, 0, v___x_176_);
lean_ctor_set(v___x_177_, 1, v___x_175_);
lean_ctor_set(v___x_177_, 2, v___x_174_);
return v___x_177_;
}
}
static lean_object* _init_l_Lean_AttributeImplCore_ref___autoParam___closed__25(void){
_start:
{
lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; 
v___x_178_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__24, &l_Lean_AttributeImplCore_ref___autoParam___closed__24_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__24);
v___x_179_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__5));
v___x_180_ = lean_array_push(v___x_179_, v___x_178_);
return v___x_180_;
}
}
static lean_object* _init_l_Lean_AttributeImplCore_ref___autoParam___closed__26(void){
_start:
{
lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; 
v___x_181_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__25, &l_Lean_AttributeImplCore_ref___autoParam___closed__25_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__25);
v___x_182_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__7));
v___x_183_ = lean_box(2);
v___x_184_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_184_, 0, v___x_183_);
lean_ctor_set(v___x_184_, 1, v___x_182_);
lean_ctor_set(v___x_184_, 2, v___x_181_);
return v___x_184_;
}
}
static lean_object* _init_l_Lean_AttributeImplCore_ref___autoParam___closed__27(void){
_start:
{
lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; 
v___x_185_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__26, &l_Lean_AttributeImplCore_ref___autoParam___closed__26_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__26);
v___x_186_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__5));
v___x_187_ = lean_array_push(v___x_186_, v___x_185_);
return v___x_187_;
}
}
static lean_object* _init_l_Lean_AttributeImplCore_ref___autoParam___closed__28(void){
_start:
{
lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; 
v___x_188_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__27, &l_Lean_AttributeImplCore_ref___autoParam___closed__27_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__27);
v___x_189_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__4));
v___x_190_ = lean_box(2);
v___x_191_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_191_, 0, v___x_190_);
lean_ctor_set(v___x_191_, 1, v___x_189_);
lean_ctor_set(v___x_191_, 2, v___x_188_);
return v___x_191_;
}
}
static lean_object* _init_l_Lean_AttributeImplCore_ref___autoParam(void){
_start:
{
lean_object* v___x_192_; 
v___x_192_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__28, &l_Lean_AttributeImplCore_ref___autoParam___closed__28_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__28);
return v___x_192_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_ctorIdx(uint8_t v_x_207_){
_start:
{
switch(v_x_207_)
{
case 0:
{
lean_object* v___x_208_; 
v___x_208_ = lean_unsigned_to_nat(0u);
return v___x_208_;
}
case 1:
{
lean_object* v___x_209_; 
v___x_209_ = lean_unsigned_to_nat(1u);
return v___x_209_;
}
default: 
{
lean_object* v___x_210_; 
v___x_210_ = lean_unsigned_to_nat(2u);
return v___x_210_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_ctorIdx___boxed(lean_object* v_x_211_){
_start:
{
uint8_t v_x_boxed_212_; lean_object* v_res_213_; 
v_x_boxed_212_ = lean_unbox(v_x_211_);
v_res_213_ = l_Lean_AttributeKind_ctorIdx(v_x_boxed_212_);
return v_res_213_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_ctorElim___redArg(lean_object* v_k_214_){
_start:
{
lean_inc(v_k_214_);
return v_k_214_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_ctorElim___redArg___boxed(lean_object* v_k_215_){
_start:
{
lean_object* v_res_216_; 
v_res_216_ = l_Lean_AttributeKind_ctorElim___redArg(v_k_215_);
lean_dec(v_k_215_);
return v_res_216_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_ctorElim(lean_object* v_motive_217_, lean_object* v_ctorIdx_218_, uint8_t v_t_219_, lean_object* v_h_220_, lean_object* v_k_221_){
_start:
{
lean_inc(v_k_221_);
return v_k_221_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_ctorElim___boxed(lean_object* v_motive_222_, lean_object* v_ctorIdx_223_, lean_object* v_t_224_, lean_object* v_h_225_, lean_object* v_k_226_){
_start:
{
uint8_t v_t_boxed_227_; lean_object* v_res_228_; 
v_t_boxed_227_ = lean_unbox(v_t_224_);
v_res_228_ = l_Lean_AttributeKind_ctorElim(v_motive_222_, v_ctorIdx_223_, v_t_boxed_227_, v_h_225_, v_k_226_);
lean_dec(v_k_226_);
lean_dec(v_ctorIdx_223_);
return v_res_228_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_global_elim___redArg(lean_object* v_global_229_){
_start:
{
lean_inc(v_global_229_);
return v_global_229_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_global_elim___redArg___boxed(lean_object* v_global_230_){
_start:
{
lean_object* v_res_231_; 
v_res_231_ = l_Lean_AttributeKind_global_elim___redArg(v_global_230_);
lean_dec(v_global_230_);
return v_res_231_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_global_elim(lean_object* v_motive_232_, uint8_t v_t_233_, lean_object* v_h_234_, lean_object* v_global_235_){
_start:
{
lean_inc(v_global_235_);
return v_global_235_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_global_elim___boxed(lean_object* v_motive_236_, lean_object* v_t_237_, lean_object* v_h_238_, lean_object* v_global_239_){
_start:
{
uint8_t v_t_boxed_240_; lean_object* v_res_241_; 
v_t_boxed_240_ = lean_unbox(v_t_237_);
v_res_241_ = l_Lean_AttributeKind_global_elim(v_motive_236_, v_t_boxed_240_, v_h_238_, v_global_239_);
lean_dec(v_global_239_);
return v_res_241_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_local_elim___redArg(lean_object* v_local_242_){
_start:
{
lean_inc(v_local_242_);
return v_local_242_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_local_elim___redArg___boxed(lean_object* v_local_243_){
_start:
{
lean_object* v_res_244_; 
v_res_244_ = l_Lean_AttributeKind_local_elim___redArg(v_local_243_);
lean_dec(v_local_243_);
return v_res_244_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_local_elim(lean_object* v_motive_245_, uint8_t v_t_246_, lean_object* v_h_247_, lean_object* v_local_248_){
_start:
{
lean_inc(v_local_248_);
return v_local_248_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_local_elim___boxed(lean_object* v_motive_249_, lean_object* v_t_250_, lean_object* v_h_251_, lean_object* v_local_252_){
_start:
{
uint8_t v_t_boxed_253_; lean_object* v_res_254_; 
v_t_boxed_253_ = lean_unbox(v_t_250_);
v_res_254_ = l_Lean_AttributeKind_local_elim(v_motive_249_, v_t_boxed_253_, v_h_251_, v_local_252_);
lean_dec(v_local_252_);
return v_res_254_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_scoped_elim___redArg(lean_object* v_scoped_255_){
_start:
{
lean_inc(v_scoped_255_);
return v_scoped_255_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_scoped_elim___redArg___boxed(lean_object* v_scoped_256_){
_start:
{
lean_object* v_res_257_; 
v_res_257_ = l_Lean_AttributeKind_scoped_elim___redArg(v_scoped_256_);
lean_dec(v_scoped_256_);
return v_res_257_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_scoped_elim(lean_object* v_motive_258_, uint8_t v_t_259_, lean_object* v_h_260_, lean_object* v_scoped_261_){
_start:
{
lean_inc(v_scoped_261_);
return v_scoped_261_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_scoped_elim___boxed(lean_object* v_motive_262_, lean_object* v_t_263_, lean_object* v_h_264_, lean_object* v_scoped_265_){
_start:
{
uint8_t v_t_boxed_266_; lean_object* v_res_267_; 
v_t_boxed_266_ = lean_unbox(v_t_263_);
v_res_267_ = l_Lean_AttributeKind_scoped_elim(v_motive_262_, v_t_boxed_266_, v_h_264_, v_scoped_265_);
lean_dec(v_scoped_265_);
return v_res_267_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqAttributeKind_beq(uint8_t v_x_268_, uint8_t v_y_269_){
_start:
{
lean_object* v___x_270_; lean_object* v___x_271_; uint8_t v___x_272_; 
v___x_270_ = l_Lean_AttributeKind_ctorIdx(v_x_268_);
v___x_271_ = l_Lean_AttributeKind_ctorIdx(v_y_269_);
v___x_272_ = lean_nat_dec_eq(v___x_270_, v___x_271_);
lean_dec(v___x_271_);
lean_dec(v___x_270_);
return v___x_272_;
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqAttributeKind_beq___boxed(lean_object* v_x_273_, lean_object* v_y_274_){
_start:
{
uint8_t v_x_21__boxed_275_; uint8_t v_y_22__boxed_276_; uint8_t v_res_277_; lean_object* v_r_278_; 
v_x_21__boxed_275_ = lean_unbox(v_x_273_);
v_y_22__boxed_276_ = lean_unbox(v_y_274_);
v_res_277_ = l_Lean_instBEqAttributeKind_beq(v_x_21__boxed_275_, v_y_22__boxed_276_);
v_r_278_ = lean_box(v_res_277_);
return v_r_278_;
}
}
static uint8_t _init_l_Lean_instInhabitedAttributeKind_default(void){
_start:
{
uint8_t v___x_281_; 
v___x_281_ = 0;
return v___x_281_;
}
}
static uint8_t _init_l_Lean_instInhabitedAttributeKind(void){
_start:
{
uint8_t v___x_282_; 
v___x_282_ = 0;
return v___x_282_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToStringAttributeKind___lam__0(uint8_t v_x_286_){
_start:
{
switch(v_x_286_)
{
case 0:
{
lean_object* v___x_287_; 
v___x_287_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__0));
return v___x_287_;
}
case 1:
{
lean_object* v___x_288_; 
v___x_288_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__1));
return v___x_288_;
}
default: 
{
lean_object* v___x_289_; 
v___x_289_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__2));
return v___x_289_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToStringAttributeKind___lam__0___boxed(lean_object* v_x_290_){
_start:
{
uint8_t v_x_36__boxed_291_; lean_object* v_res_292_; 
v_x_36__boxed_291_ = lean_unbox(v_x_290_);
v_res_292_ = l_Lean_instToStringAttributeKind___lam__0(v_x_36__boxed_291_);
return v_res_292_;
}
}
static lean_object* _init_l_Lean_instInhabitedAttributeImpl_default___lam__0___closed__0(void){
_start:
{
lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; 
v___x_295_ = l_Lean_instInhabitedMessageData_default;
v___x_296_ = lean_box(0);
v___x_297_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_297_, 0, v___x_296_);
lean_ctor_set(v___x_297_, 1, v___x_295_);
return v___x_297_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedAttributeImpl_default___lam__0(lean_object* v_x_298_, lean_object* v___y_299_, uint8_t v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_){
_start:
{
lean_object* v___x_304_; lean_object* v___x_305_; 
v___x_304_ = lean_obj_once(&l_Lean_instInhabitedAttributeImpl_default___lam__0___closed__0, &l_Lean_instInhabitedAttributeImpl_default___lam__0___closed__0_once, _init_l_Lean_instInhabitedAttributeImpl_default___lam__0___closed__0);
v___x_305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_305_, 0, v___x_304_);
return v___x_305_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedAttributeImpl_default___lam__0___boxed(lean_object* v_x_306_, lean_object* v___y_307_, lean_object* v___y_308_, lean_object* v___y_309_, lean_object* v___y_310_, lean_object* v___y_311_){
_start:
{
uint8_t v___y_1022__boxed_312_; lean_object* v_res_313_; 
v___y_1022__boxed_312_ = lean_unbox(v___y_308_);
v_res_313_ = l_Lean_instInhabitedAttributeImpl_default___lam__0(v_x_306_, v___y_307_, v___y_1022__boxed_312_, v___y_309_, v___y_310_);
lean_dec(v___y_310_);
lean_dec_ref(v___y_309_);
lean_dec(v___y_307_);
lean_dec(v_x_306_);
return v_res_313_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_314_; 
v___x_314_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_314_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_315_; lean_object* v___x_316_; 
v___x_315_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__0);
v___x_316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_316_, 0, v___x_315_);
return v___x_316_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; 
v___x_317_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__1);
v___x_318_ = lean_unsigned_to_nat(0u);
v___x_319_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_319_, 0, v___x_318_);
lean_ctor_set(v___x_319_, 1, v___x_318_);
lean_ctor_set(v___x_319_, 2, v___x_318_);
lean_ctor_set(v___x_319_, 3, v___x_318_);
lean_ctor_set(v___x_319_, 4, v___x_317_);
lean_ctor_set(v___x_319_, 5, v___x_317_);
lean_ctor_set(v___x_319_, 6, v___x_317_);
lean_ctor_set(v___x_319_, 7, v___x_317_);
lean_ctor_set(v___x_319_, 8, v___x_317_);
lean_ctor_set(v___x_319_, 9, v___x_317_);
lean_ctor_set(v___x_319_, 10, v___x_317_);
return v___x_319_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; 
v___x_320_ = lean_unsigned_to_nat(32u);
v___x_321_ = lean_mk_empty_array_with_capacity(v___x_320_);
v___x_322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_322_, 0, v___x_321_);
return v___x_322_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__4(void){
_start:
{
size_t v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; 
v___x_323_ = ((size_t)5ULL);
v___x_324_ = lean_unsigned_to_nat(0u);
v___x_325_ = lean_unsigned_to_nat(32u);
v___x_326_ = lean_mk_empty_array_with_capacity(v___x_325_);
v___x_327_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__3);
v___x_328_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_328_, 0, v___x_327_);
lean_ctor_set(v___x_328_, 1, v___x_326_);
lean_ctor_set(v___x_328_, 2, v___x_324_);
lean_ctor_set(v___x_328_, 3, v___x_324_);
lean_ctor_set_usize(v___x_328_, 4, v___x_323_);
return v___x_328_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; 
v___x_329_ = lean_box(1);
v___x_330_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__4);
v___x_331_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__1);
v___x_332_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_332_, 0, v___x_331_);
lean_ctor_set(v___x_332_, 1, v___x_330_);
lean_ctor_set(v___x_332_, 2, v___x_329_);
return v___x_332_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0(lean_object* v_msgData_333_, lean_object* v___y_334_, lean_object* v___y_335_){
_start:
{
lean_object* v___x_337_; lean_object* v_toCold_338_; lean_object* v_env_339_; lean_object* v_options_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; 
v___x_337_ = lean_st_ref_get(v___y_335_);
v_toCold_338_ = lean_ctor_get(v___y_334_, 0);
v_env_339_ = lean_ctor_get(v___x_337_, 0);
lean_inc_ref(v_env_339_);
lean_dec(v___x_337_);
v_options_340_ = lean_ctor_get(v_toCold_338_, 2);
v___x_341_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__2);
v___x_342_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__5);
lean_inc_ref(v_options_340_);
v___x_343_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_343_, 0, v_env_339_);
lean_ctor_set(v___x_343_, 1, v___x_341_);
lean_ctor_set(v___x_343_, 2, v___x_342_);
lean_ctor_set(v___x_343_, 3, v_options_340_);
v___x_344_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_344_, 0, v___x_343_);
lean_ctor_set(v___x_344_, 1, v_msgData_333_);
v___x_345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_345_, 0, v___x_344_);
return v___x_345_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___boxed(lean_object* v_msgData_346_, lean_object* v___y_347_, lean_object* v___y_348_, lean_object* v___y_349_){
_start:
{
lean_object* v_res_350_; 
v_res_350_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0(v_msgData_346_, v___y_347_, v___y_348_);
lean_dec(v___y_348_);
lean_dec_ref(v___y_347_);
return v_res_350_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(lean_object* v_msg_351_, lean_object* v___y_352_, lean_object* v___y_353_){
_start:
{
lean_object* v_ref_355_; lean_object* v___x_356_; lean_object* v_a_357_; lean_object* v___x_359_; uint8_t v_isShared_360_; uint8_t v_isSharedCheck_365_; 
v_ref_355_ = lean_ctor_get(v___y_352_, 2);
v___x_356_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0(v_msg_351_, v___y_352_, v___y_353_);
v_a_357_ = lean_ctor_get(v___x_356_, 0);
v_isSharedCheck_365_ = !lean_is_exclusive(v___x_356_);
if (v_isSharedCheck_365_ == 0)
{
v___x_359_ = v___x_356_;
v_isShared_360_ = v_isSharedCheck_365_;
goto v_resetjp_358_;
}
else
{
lean_inc(v_a_357_);
lean_dec(v___x_356_);
v___x_359_ = lean_box(0);
v_isShared_360_ = v_isSharedCheck_365_;
goto v_resetjp_358_;
}
v_resetjp_358_:
{
lean_object* v___x_361_; lean_object* v___x_363_; 
lean_inc(v_ref_355_);
v___x_361_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_361_, 0, v_ref_355_);
lean_ctor_set(v___x_361_, 1, v_a_357_);
if (v_isShared_360_ == 0)
{
lean_ctor_set_tag(v___x_359_, 1);
lean_ctor_set(v___x_359_, 0, v___x_361_);
v___x_363_ = v___x_359_;
goto v_reusejp_362_;
}
else
{
lean_object* v_reuseFailAlloc_364_; 
v_reuseFailAlloc_364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_364_, 0, v___x_361_);
v___x_363_ = v_reuseFailAlloc_364_;
goto v_reusejp_362_;
}
v_reusejp_362_:
{
return v___x_363_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg___boxed(lean_object* v_msg_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_){
_start:
{
lean_object* v_res_370_; 
v_res_370_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v_msg_366_, v___y_367_, v___y_368_);
lean_dec(v___y_368_);
lean_dec_ref(v___y_367_);
return v_res_370_;
}
}
static lean_object* _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1(void){
_start:
{
lean_object* v___x_372_; lean_object* v___x_373_; 
v___x_372_ = ((lean_object*)(l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__0));
v___x_373_ = l_Lean_stringToMessageData(v___x_372_);
return v___x_373_;
}
}
static lean_object* _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3(void){
_start:
{
lean_object* v___x_375_; lean_object* v___x_376_; 
v___x_375_ = ((lean_object*)(l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__2));
v___x_376_ = l_Lean_stringToMessageData(v___x_375_);
return v___x_376_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedAttributeImpl_default___lam__1(lean_object* v___x_377_, lean_object* v_decl_378_, lean_object* v___y_379_, lean_object* v___y_380_){
_start:
{
lean_object* v_name_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; 
v_name_382_ = lean_ctor_get(v___x_377_, 1);
lean_inc(v_name_382_);
lean_dec_ref(v___x_377_);
v___x_383_ = lean_obj_once(&l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1, &l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1_once, _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1);
v___x_384_ = l_Lean_MessageData_ofName(v_name_382_);
v___x_385_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_385_, 0, v___x_383_);
lean_ctor_set(v___x_385_, 1, v___x_384_);
v___x_386_ = lean_obj_once(&l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3, &l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3_once, _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3);
v___x_387_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_387_, 0, v___x_385_);
lean_ctor_set(v___x_387_, 1, v___x_386_);
v___x_388_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_387_, v___y_379_, v___y_380_);
return v___x_388_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedAttributeImpl_default___lam__1___boxed(lean_object* v___x_389_, lean_object* v_decl_390_, lean_object* v___y_391_, lean_object* v___y_392_, lean_object* v___y_393_){
_start:
{
lean_object* v_res_394_; 
v_res_394_ = l_Lean_instInhabitedAttributeImpl_default___lam__1(v___x_389_, v_decl_390_, v___y_391_, v___y_392_);
lean_dec(v___y_392_);
lean_dec_ref(v___y_391_);
lean_dec(v_decl_390_);
return v_res_394_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0(lean_object* v_00_u03b1_403_, lean_object* v_msg_404_, lean_object* v___y_405_, lean_object* v___y_406_){
_start:
{
lean_object* v___x_408_; 
v___x_408_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v_msg_404_, v___y_405_, v___y_406_);
return v___x_408_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___boxed(lean_object* v_00_u03b1_409_, lean_object* v_msg_410_, lean_object* v___y_411_, lean_object* v___y_412_, lean_object* v___y_413_){
_start:
{
lean_object* v_res_414_; 
v_res_414_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0(v_00_u03b1_409_, v_msg_410_, v___y_411_, v___y_412_);
lean_dec(v___y_412_);
lean_dec_ref(v___y_411_);
return v_res_414_;
}
}
static lean_object* _init_l___private_Lean_Attributes_0__Lean_initFn___closed__0_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; 
v___x_416_ = lean_box(0);
v___x_417_ = lean_unsigned_to_nat(16u);
v___x_418_ = lean_mk_array(v___x_417_, v___x_416_);
return v___x_418_;
}
}
static lean_object* _init_l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; 
v___x_419_ = lean_obj_once(&l___private_Lean_Attributes_0__Lean_initFn___closed__0_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_, &l___private_Lean_Attributes_0__Lean_initFn___closed__0_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2__once, _init_l___private_Lean_Attributes_0__Lean_initFn___closed__0_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_);
v___x_420_ = lean_unsigned_to_nat(0u);
v___x_421_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_421_, 0, v___x_420_);
lean_ctor_set(v___x_421_, 1, v___x_419_);
return v___x_421_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; 
v___x_423_ = lean_obj_once(&l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_, &l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2__once, _init_l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_);
v___x_424_ = lean_st_mk_ref(v___x_423_);
v___x_425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_425_, 0, v___x_424_);
return v___x_425_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2____boxed(lean_object* v_a_426_){
_start:
{
lean_object* v_res_427_; 
v_res_427_ = l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_();
return v_res_427_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0_spec__0___redArg(lean_object* v_a_428_, lean_object* v_x_429_){
_start:
{
if (lean_obj_tag(v_x_429_) == 0)
{
uint8_t v___x_430_; 
v___x_430_ = 0;
return v___x_430_;
}
else
{
lean_object* v_key_431_; lean_object* v_tail_432_; uint8_t v___x_433_; 
v_key_431_ = lean_ctor_get(v_x_429_, 0);
v_tail_432_ = lean_ctor_get(v_x_429_, 2);
v___x_433_ = lean_name_eq(v_key_431_, v_a_428_);
if (v___x_433_ == 0)
{
v_x_429_ = v_tail_432_;
goto _start;
}
else
{
return v___x_433_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0_spec__0___redArg___boxed(lean_object* v_a_435_, lean_object* v_x_436_){
_start:
{
uint8_t v_res_437_; lean_object* v_r_438_; 
v_res_437_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0_spec__0___redArg(v_a_435_, v_x_436_);
lean_dec(v_x_436_);
lean_dec(v_a_435_);
v_r_438_ = lean_box(v_res_437_);
return v_r_438_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(lean_object* v_m_439_, lean_object* v_a_440_){
_start:
{
lean_object* v_buckets_441_; lean_object* v___x_442_; uint64_t v___y_444_; 
v_buckets_441_ = lean_ctor_get(v_m_439_, 1);
v___x_442_ = lean_array_get_size(v_buckets_441_);
if (lean_obj_tag(v_a_440_) == 0)
{
uint64_t v___x_458_; 
v___x_458_ = 1723ULL;
v___y_444_ = v___x_458_;
goto v___jp_443_;
}
else
{
uint64_t v_hash_459_; 
v_hash_459_ = lean_ctor_get_uint64(v_a_440_, sizeof(void*)*2);
v___y_444_ = v_hash_459_;
goto v___jp_443_;
}
v___jp_443_:
{
uint64_t v___x_445_; uint64_t v___x_446_; uint64_t v_fold_447_; uint64_t v___x_448_; uint64_t v___x_449_; uint64_t v___x_450_; size_t v___x_451_; size_t v___x_452_; size_t v___x_453_; size_t v___x_454_; size_t v___x_455_; lean_object* v___x_456_; uint8_t v___x_457_; 
v___x_445_ = 32ULL;
v___x_446_ = lean_uint64_shift_right(v___y_444_, v___x_445_);
v_fold_447_ = lean_uint64_xor(v___y_444_, v___x_446_);
v___x_448_ = 16ULL;
v___x_449_ = lean_uint64_shift_right(v_fold_447_, v___x_448_);
v___x_450_ = lean_uint64_xor(v_fold_447_, v___x_449_);
v___x_451_ = lean_uint64_to_usize(v___x_450_);
v___x_452_ = lean_usize_of_nat(v___x_442_);
v___x_453_ = ((size_t)1ULL);
v___x_454_ = lean_usize_sub(v___x_452_, v___x_453_);
v___x_455_ = lean_usize_land(v___x_451_, v___x_454_);
v___x_456_ = lean_array_uget_borrowed(v_buckets_441_, v___x_455_);
v___x_457_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0_spec__0___redArg(v_a_440_, v___x_456_);
return v___x_457_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg___boxed(lean_object* v_m_460_, lean_object* v_a_461_){
_start:
{
uint8_t v_res_462_; lean_object* v_r_463_; 
v_res_462_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(v_m_460_, v_a_461_);
lean_dec(v_a_461_);
lean_dec_ref(v_m_460_);
v_r_463_ = lean_box(v_res_462_);
return v_r_463_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__3___redArg(lean_object* v_a_464_, lean_object* v_b_465_, lean_object* v_x_466_){
_start:
{
if (lean_obj_tag(v_x_466_) == 0)
{
lean_dec(v_b_465_);
lean_dec(v_a_464_);
return v_x_466_;
}
else
{
lean_object* v_key_467_; lean_object* v_value_468_; lean_object* v_tail_469_; lean_object* v___x_471_; uint8_t v_isShared_472_; uint8_t v_isSharedCheck_481_; 
v_key_467_ = lean_ctor_get(v_x_466_, 0);
v_value_468_ = lean_ctor_get(v_x_466_, 1);
v_tail_469_ = lean_ctor_get(v_x_466_, 2);
v_isSharedCheck_481_ = !lean_is_exclusive(v_x_466_);
if (v_isSharedCheck_481_ == 0)
{
v___x_471_ = v_x_466_;
v_isShared_472_ = v_isSharedCheck_481_;
goto v_resetjp_470_;
}
else
{
lean_inc(v_tail_469_);
lean_inc(v_value_468_);
lean_inc(v_key_467_);
lean_dec(v_x_466_);
v___x_471_ = lean_box(0);
v_isShared_472_ = v_isSharedCheck_481_;
goto v_resetjp_470_;
}
v_resetjp_470_:
{
uint8_t v___x_473_; 
v___x_473_ = lean_name_eq(v_key_467_, v_a_464_);
if (v___x_473_ == 0)
{
lean_object* v___x_474_; lean_object* v___x_476_; 
v___x_474_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__3___redArg(v_a_464_, v_b_465_, v_tail_469_);
if (v_isShared_472_ == 0)
{
lean_ctor_set(v___x_471_, 2, v___x_474_);
v___x_476_ = v___x_471_;
goto v_reusejp_475_;
}
else
{
lean_object* v_reuseFailAlloc_477_; 
v_reuseFailAlloc_477_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_477_, 0, v_key_467_);
lean_ctor_set(v_reuseFailAlloc_477_, 1, v_value_468_);
lean_ctor_set(v_reuseFailAlloc_477_, 2, v___x_474_);
v___x_476_ = v_reuseFailAlloc_477_;
goto v_reusejp_475_;
}
v_reusejp_475_:
{
return v___x_476_;
}
}
else
{
lean_object* v___x_479_; 
lean_dec(v_value_468_);
lean_dec(v_key_467_);
if (v_isShared_472_ == 0)
{
lean_ctor_set(v___x_471_, 1, v_b_465_);
lean_ctor_set(v___x_471_, 0, v_a_464_);
v___x_479_ = v___x_471_;
goto v_reusejp_478_;
}
else
{
lean_object* v_reuseFailAlloc_480_; 
v_reuseFailAlloc_480_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_480_, 0, v_a_464_);
lean_ctor_set(v_reuseFailAlloc_480_, 1, v_b_465_);
lean_ctor_set(v_reuseFailAlloc_480_, 2, v_tail_469_);
v___x_479_ = v_reuseFailAlloc_480_;
goto v_reusejp_478_;
}
v_reusejp_478_:
{
return v___x_479_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2_spec__3_spec__4___redArg(lean_object* v_x_482_, lean_object* v_x_483_){
_start:
{
if (lean_obj_tag(v_x_483_) == 0)
{
return v_x_482_;
}
else
{
lean_object* v_key_484_; lean_object* v_value_485_; lean_object* v_tail_486_; lean_object* v___x_488_; uint8_t v_isShared_489_; uint8_t v_isSharedCheck_512_; 
v_key_484_ = lean_ctor_get(v_x_483_, 0);
v_value_485_ = lean_ctor_get(v_x_483_, 1);
v_tail_486_ = lean_ctor_get(v_x_483_, 2);
v_isSharedCheck_512_ = !lean_is_exclusive(v_x_483_);
if (v_isSharedCheck_512_ == 0)
{
v___x_488_ = v_x_483_;
v_isShared_489_ = v_isSharedCheck_512_;
goto v_resetjp_487_;
}
else
{
lean_inc(v_tail_486_);
lean_inc(v_value_485_);
lean_inc(v_key_484_);
lean_dec(v_x_483_);
v___x_488_ = lean_box(0);
v_isShared_489_ = v_isSharedCheck_512_;
goto v_resetjp_487_;
}
v_resetjp_487_:
{
lean_object* v___x_490_; uint64_t v___y_492_; 
v___x_490_ = lean_array_get_size(v_x_482_);
if (lean_obj_tag(v_key_484_) == 0)
{
uint64_t v___x_510_; 
v___x_510_ = 1723ULL;
v___y_492_ = v___x_510_;
goto v___jp_491_;
}
else
{
uint64_t v_hash_511_; 
v_hash_511_ = lean_ctor_get_uint64(v_key_484_, sizeof(void*)*2);
v___y_492_ = v_hash_511_;
goto v___jp_491_;
}
v___jp_491_:
{
uint64_t v___x_493_; uint64_t v___x_494_; uint64_t v_fold_495_; uint64_t v___x_496_; uint64_t v___x_497_; uint64_t v___x_498_; size_t v___x_499_; size_t v___x_500_; size_t v___x_501_; size_t v___x_502_; size_t v___x_503_; lean_object* v___x_504_; lean_object* v___x_506_; 
v___x_493_ = 32ULL;
v___x_494_ = lean_uint64_shift_right(v___y_492_, v___x_493_);
v_fold_495_ = lean_uint64_xor(v___y_492_, v___x_494_);
v___x_496_ = 16ULL;
v___x_497_ = lean_uint64_shift_right(v_fold_495_, v___x_496_);
v___x_498_ = lean_uint64_xor(v_fold_495_, v___x_497_);
v___x_499_ = lean_uint64_to_usize(v___x_498_);
v___x_500_ = lean_usize_of_nat(v___x_490_);
v___x_501_ = ((size_t)1ULL);
v___x_502_ = lean_usize_sub(v___x_500_, v___x_501_);
v___x_503_ = lean_usize_land(v___x_499_, v___x_502_);
v___x_504_ = lean_array_uget_borrowed(v_x_482_, v___x_503_);
lean_inc(v___x_504_);
if (v_isShared_489_ == 0)
{
lean_ctor_set(v___x_488_, 2, v___x_504_);
v___x_506_ = v___x_488_;
goto v_reusejp_505_;
}
else
{
lean_object* v_reuseFailAlloc_509_; 
v_reuseFailAlloc_509_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_509_, 0, v_key_484_);
lean_ctor_set(v_reuseFailAlloc_509_, 1, v_value_485_);
lean_ctor_set(v_reuseFailAlloc_509_, 2, v___x_504_);
v___x_506_ = v_reuseFailAlloc_509_;
goto v_reusejp_505_;
}
v_reusejp_505_:
{
lean_object* v___x_507_; 
v___x_507_ = lean_array_uset(v_x_482_, v___x_503_, v___x_506_);
v_x_482_ = v___x_507_;
v_x_483_ = v_tail_486_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2_spec__3___redArg(lean_object* v_i_513_, lean_object* v_source_514_, lean_object* v_target_515_){
_start:
{
lean_object* v___x_516_; uint8_t v___x_517_; 
v___x_516_ = lean_array_get_size(v_source_514_);
v___x_517_ = lean_nat_dec_lt(v_i_513_, v___x_516_);
if (v___x_517_ == 0)
{
lean_dec_ref(v_source_514_);
lean_dec(v_i_513_);
return v_target_515_;
}
else
{
lean_object* v_es_518_; lean_object* v___x_519_; lean_object* v_source_520_; lean_object* v_target_521_; lean_object* v___x_522_; lean_object* v___x_523_; 
v_es_518_ = lean_array_fget(v_source_514_, v_i_513_);
v___x_519_ = lean_box(0);
v_source_520_ = lean_array_fset(v_source_514_, v_i_513_, v___x_519_);
v_target_521_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2_spec__3_spec__4___redArg(v_target_515_, v_es_518_);
v___x_522_ = lean_unsigned_to_nat(1u);
v___x_523_ = lean_nat_add(v_i_513_, v___x_522_);
lean_dec(v_i_513_);
v_i_513_ = v___x_523_;
v_source_514_ = v_source_520_;
v_target_515_ = v_target_521_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2___redArg(lean_object* v_data_525_){
_start:
{
lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v_nbuckets_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; 
v___x_526_ = lean_array_get_size(v_data_525_);
v___x_527_ = lean_unsigned_to_nat(2u);
v_nbuckets_528_ = lean_nat_mul(v___x_526_, v___x_527_);
v___x_529_ = lean_unsigned_to_nat(0u);
v___x_530_ = lean_box(0);
v___x_531_ = lean_mk_array(v_nbuckets_528_, v___x_530_);
v___x_532_ = lean_array_propagate_mark(v_data_525_, v___x_531_);
v___x_533_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2_spec__3___redArg(v___x_529_, v_data_525_, v___x_532_);
return v___x_533_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1___redArg(lean_object* v_m_534_, lean_object* v_a_535_, lean_object* v_b_536_){
_start:
{
lean_object* v_size_537_; lean_object* v_buckets_538_; lean_object* v___x_540_; uint8_t v_isShared_541_; uint8_t v_isSharedCheck_584_; 
v_size_537_ = lean_ctor_get(v_m_534_, 0);
v_buckets_538_ = lean_ctor_get(v_m_534_, 1);
v_isSharedCheck_584_ = !lean_is_exclusive(v_m_534_);
if (v_isSharedCheck_584_ == 0)
{
v___x_540_ = v_m_534_;
v_isShared_541_ = v_isSharedCheck_584_;
goto v_resetjp_539_;
}
else
{
lean_inc(v_buckets_538_);
lean_inc(v_size_537_);
lean_dec(v_m_534_);
v___x_540_ = lean_box(0);
v_isShared_541_ = v_isSharedCheck_584_;
goto v_resetjp_539_;
}
v_resetjp_539_:
{
lean_object* v___x_542_; uint64_t v___y_544_; 
v___x_542_ = lean_array_get_size(v_buckets_538_);
if (lean_obj_tag(v_a_535_) == 0)
{
uint64_t v___x_582_; 
v___x_582_ = 1723ULL;
v___y_544_ = v___x_582_;
goto v___jp_543_;
}
else
{
uint64_t v_hash_583_; 
v_hash_583_ = lean_ctor_get_uint64(v_a_535_, sizeof(void*)*2);
v___y_544_ = v_hash_583_;
goto v___jp_543_;
}
v___jp_543_:
{
uint64_t v___x_545_; uint64_t v___x_546_; uint64_t v_fold_547_; uint64_t v___x_548_; uint64_t v___x_549_; uint64_t v___x_550_; size_t v___x_551_; size_t v___x_552_; size_t v___x_553_; size_t v___x_554_; size_t v___x_555_; lean_object* v_bkt_556_; uint8_t v___x_557_; 
v___x_545_ = 32ULL;
v___x_546_ = lean_uint64_shift_right(v___y_544_, v___x_545_);
v_fold_547_ = lean_uint64_xor(v___y_544_, v___x_546_);
v___x_548_ = 16ULL;
v___x_549_ = lean_uint64_shift_right(v_fold_547_, v___x_548_);
v___x_550_ = lean_uint64_xor(v_fold_547_, v___x_549_);
v___x_551_ = lean_uint64_to_usize(v___x_550_);
v___x_552_ = lean_usize_of_nat(v___x_542_);
v___x_553_ = ((size_t)1ULL);
v___x_554_ = lean_usize_sub(v___x_552_, v___x_553_);
v___x_555_ = lean_usize_land(v___x_551_, v___x_554_);
v_bkt_556_ = lean_array_uget_borrowed(v_buckets_538_, v___x_555_);
v___x_557_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0_spec__0___redArg(v_a_535_, v_bkt_556_);
if (v___x_557_ == 0)
{
lean_object* v___x_558_; lean_object* v_size_x27_559_; lean_object* v___x_560_; lean_object* v_buckets_x27_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; uint8_t v___x_567_; 
v___x_558_ = lean_unsigned_to_nat(1u);
v_size_x27_559_ = lean_nat_add(v_size_537_, v___x_558_);
lean_dec(v_size_537_);
lean_inc(v_bkt_556_);
v___x_560_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_560_, 0, v_a_535_);
lean_ctor_set(v___x_560_, 1, v_b_536_);
lean_ctor_set(v___x_560_, 2, v_bkt_556_);
v_buckets_x27_561_ = lean_array_uset(v_buckets_538_, v___x_555_, v___x_560_);
v___x_562_ = lean_unsigned_to_nat(4u);
v___x_563_ = lean_nat_mul(v_size_x27_559_, v___x_562_);
v___x_564_ = lean_unsigned_to_nat(3u);
v___x_565_ = lean_nat_div(v___x_563_, v___x_564_);
lean_dec(v___x_563_);
v___x_566_ = lean_array_get_size(v_buckets_x27_561_);
v___x_567_ = lean_nat_dec_le(v___x_565_, v___x_566_);
lean_dec(v___x_565_);
if (v___x_567_ == 0)
{
lean_object* v_val_568_; lean_object* v___x_570_; 
v_val_568_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2___redArg(v_buckets_x27_561_);
if (v_isShared_541_ == 0)
{
lean_ctor_set(v___x_540_, 1, v_val_568_);
lean_ctor_set(v___x_540_, 0, v_size_x27_559_);
v___x_570_ = v___x_540_;
goto v_reusejp_569_;
}
else
{
lean_object* v_reuseFailAlloc_571_; 
v_reuseFailAlloc_571_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_571_, 0, v_size_x27_559_);
lean_ctor_set(v_reuseFailAlloc_571_, 1, v_val_568_);
v___x_570_ = v_reuseFailAlloc_571_;
goto v_reusejp_569_;
}
v_reusejp_569_:
{
return v___x_570_;
}
}
else
{
lean_object* v___x_573_; 
if (v_isShared_541_ == 0)
{
lean_ctor_set(v___x_540_, 1, v_buckets_x27_561_);
lean_ctor_set(v___x_540_, 0, v_size_x27_559_);
v___x_573_ = v___x_540_;
goto v_reusejp_572_;
}
else
{
lean_object* v_reuseFailAlloc_574_; 
v_reuseFailAlloc_574_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_574_, 0, v_size_x27_559_);
lean_ctor_set(v_reuseFailAlloc_574_, 1, v_buckets_x27_561_);
v___x_573_ = v_reuseFailAlloc_574_;
goto v_reusejp_572_;
}
v_reusejp_572_:
{
return v___x_573_;
}
}
}
else
{
lean_object* v___x_575_; lean_object* v_buckets_x27_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_580_; 
lean_inc(v_bkt_556_);
v___x_575_ = lean_box(0);
v_buckets_x27_576_ = lean_array_uset(v_buckets_538_, v___x_555_, v___x_575_);
v___x_577_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__3___redArg(v_a_535_, v_b_536_, v_bkt_556_);
v___x_578_ = lean_array_uset(v_buckets_x27_576_, v___x_555_, v___x_577_);
if (v_isShared_541_ == 0)
{
lean_ctor_set(v___x_540_, 1, v___x_578_);
v___x_580_ = v___x_540_;
goto v_reusejp_579_;
}
else
{
lean_object* v_reuseFailAlloc_581_; 
v_reuseFailAlloc_581_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_581_, 0, v_size_537_);
lean_ctor_set(v_reuseFailAlloc_581_, 1, v___x_578_);
v___x_580_ = v_reuseFailAlloc_581_;
goto v_reusejp_579_;
}
v_reusejp_579_:
{
return v___x_580_;
}
}
}
}
}
}
static lean_object* _init_l_Lean_registerBuiltinAttribute___closed__1(void){
_start:
{
lean_object* v___x_586_; lean_object* v___x_587_; 
v___x_586_ = ((lean_object*)(l_Lean_registerBuiltinAttribute___closed__0));
v___x_587_ = lean_mk_io_user_error(v___x_586_);
return v___x_587_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerBuiltinAttribute(lean_object* v_attr_590_){
_start:
{
lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v_toAttributeImplCore_594_; lean_object* v_name_595_; uint8_t v___x_596_; 
v___x_592_ = l_Lean_attributeMapRef;
v___x_593_ = lean_st_ref_get(v___x_592_);
v_toAttributeImplCore_594_ = lean_ctor_get(v_attr_590_, 0);
v_name_595_ = lean_ctor_get(v_toAttributeImplCore_594_, 1);
lean_inc(v_name_595_);
v___x_596_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(v___x_593_, v_name_595_);
lean_dec(v___x_593_);
if (v___x_596_ == 0)
{
uint8_t v___x_597_; 
v___x_597_ = l_Lean_initializing();
if (v___x_597_ == 0)
{
lean_object* v___x_598_; lean_object* v___x_599_; 
lean_dec(v_name_595_);
lean_dec_ref(v_attr_590_);
v___x_598_ = lean_obj_once(&l_Lean_registerBuiltinAttribute___closed__1, &l_Lean_registerBuiltinAttribute___closed__1_once, _init_l_Lean_registerBuiltinAttribute___closed__1);
v___x_599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_599_, 0, v___x_598_);
return v___x_599_;
}
else
{
lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; 
v___x_600_ = lean_st_ref_take(v___x_592_);
v___x_601_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1___redArg(v___x_600_, v_name_595_, v_attr_590_);
v___x_602_ = lean_st_ref_put(v___x_592_, v___x_601_);
v___x_603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_603_, 0, v___x_602_);
return v___x_603_;
}
}
else
{
lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; 
lean_dec_ref(v_attr_590_);
v___x_604_ = ((lean_object*)(l_Lean_registerBuiltinAttribute___closed__2));
v___x_605_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_595_, v___x_596_);
v___x_606_ = lean_string_append(v___x_604_, v___x_605_);
lean_dec_ref(v___x_605_);
v___x_607_ = ((lean_object*)(l_Lean_registerBuiltinAttribute___closed__3));
v___x_608_ = lean_string_append(v___x_606_, v___x_607_);
v___x_609_ = lean_mk_io_user_error(v___x_608_);
v___x_610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_610_, 0, v___x_609_);
return v___x_610_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerBuiltinAttribute___boxed(lean_object* v_attr_611_, lean_object* v_a_612_){
_start:
{
lean_object* v_res_613_; 
v_res_613_ = l_Lean_registerBuiltinAttribute(v_attr_611_);
return v_res_613_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0(lean_object* v_00_u03b2_614_, lean_object* v_m_615_, lean_object* v_a_616_){
_start:
{
uint8_t v___x_617_; 
v___x_617_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(v_m_615_, v_a_616_);
return v___x_617_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___boxed(lean_object* v_00_u03b2_618_, lean_object* v_m_619_, lean_object* v_a_620_){
_start:
{
uint8_t v_res_621_; lean_object* v_r_622_; 
v_res_621_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0(v_00_u03b2_618_, v_m_619_, v_a_620_);
lean_dec(v_a_620_);
lean_dec_ref(v_m_619_);
v_r_622_ = lean_box(v_res_621_);
return v_r_622_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1(lean_object* v_00_u03b2_623_, lean_object* v_m_624_, lean_object* v_a_625_, lean_object* v_b_626_){
_start:
{
lean_object* v___x_627_; 
v___x_627_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1___redArg(v_m_624_, v_a_625_, v_b_626_);
return v___x_627_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0_spec__0(lean_object* v_00_u03b2_628_, lean_object* v_a_629_, lean_object* v_x_630_){
_start:
{
uint8_t v___x_631_; 
v___x_631_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0_spec__0___redArg(v_a_629_, v_x_630_);
return v___x_631_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0_spec__0___boxed(lean_object* v_00_u03b2_632_, lean_object* v_a_633_, lean_object* v_x_634_){
_start:
{
uint8_t v_res_635_; lean_object* v_r_636_; 
v_res_635_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0_spec__0(v_00_u03b2_632_, v_a_633_, v_x_634_);
lean_dec(v_x_634_);
lean_dec(v_a_633_);
v_r_636_ = lean_box(v_res_635_);
return v_r_636_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2(lean_object* v_00_u03b2_637_, lean_object* v_data_638_){
_start:
{
lean_object* v___x_639_; 
v___x_639_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2___redArg(v_data_638_);
return v___x_639_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__3(lean_object* v_00_u03b2_640_, lean_object* v_a_641_, lean_object* v_b_642_, lean_object* v_x_643_){
_start:
{
lean_object* v___x_644_; 
v___x_644_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__3___redArg(v_a_641_, v_b_642_, v_x_643_);
return v___x_644_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_645_, lean_object* v_i_646_, lean_object* v_source_647_, lean_object* v_target_648_){
_start:
{
lean_object* v___x_649_; 
v___x_649_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2_spec__3___redArg(v_i_646_, v_source_647_, v_target_648_);
return v___x_649_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_650_, lean_object* v_x_651_, lean_object* v_x_652_){
_start:
{
lean_object* v___x_653_; 
v___x_653_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2_spec__3_spec__4___redArg(v_x_651_, v_x_652_);
return v___x_653_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg(lean_object* v_ref_654_, lean_object* v_msg_655_, lean_object* v___y_656_, lean_object* v___y_657_){
_start:
{
lean_object* v_toCold_659_; lean_object* v_currRecDepth_660_; lean_object* v_ref_661_; uint16_t v_optionFlags_662_; uint8_t v_suppressElabErrors_663_; uint8_t v_isRecordingDeps_664_; lean_object* v_ref_665_; lean_object* v___x_666_; lean_object* v___x_667_; 
v_toCold_659_ = lean_ctor_get(v___y_656_, 0);
v_currRecDepth_660_ = lean_ctor_get(v___y_656_, 1);
v_ref_661_ = lean_ctor_get(v___y_656_, 2);
v_optionFlags_662_ = lean_ctor_get_uint16(v___y_656_, sizeof(void*)*3);
v_suppressElabErrors_663_ = lean_ctor_get_uint8(v___y_656_, sizeof(void*)*3 + 2);
v_isRecordingDeps_664_ = lean_ctor_get_uint8(v___y_656_, sizeof(void*)*3 + 3);
v_ref_665_ = l_Lean_replaceRef(v_ref_654_, v_ref_661_);
lean_inc(v_currRecDepth_660_);
lean_inc_ref(v_toCold_659_);
v___x_666_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_666_, 0, v_toCold_659_);
lean_ctor_set(v___x_666_, 1, v_currRecDepth_660_);
lean_ctor_set(v___x_666_, 2, v_ref_665_);
lean_ctor_set_uint16(v___x_666_, sizeof(void*)*3, v_optionFlags_662_);
lean_ctor_set_uint8(v___x_666_, sizeof(void*)*3 + 2, v_suppressElabErrors_663_);
lean_ctor_set_uint8(v___x_666_, sizeof(void*)*3 + 3, v_isRecordingDeps_664_);
v___x_667_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v_msg_655_, v___x_666_, v___y_657_);
lean_dec_ref_known(v___x_666_, 3);
return v___x_667_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg___boxed(lean_object* v_ref_668_, lean_object* v_msg_669_, lean_object* v___y_670_, lean_object* v___y_671_, lean_object* v___y_672_){
_start:
{
lean_object* v_res_673_; 
v_res_673_ = l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg(v_ref_668_, v_msg_669_, v___y_670_, v___y_671_);
lean_dec(v___y_671_);
lean_dec_ref(v___y_670_);
lean_dec(v_ref_668_);
return v_res_673_;
}
}
static lean_object* _init_l_Lean_Attribute_Builtin_ensureNoArgs___closed__4(void){
_start:
{
lean_object* v___x_682_; lean_object* v___x_683_; 
v___x_682_ = ((lean_object*)(l_Lean_Attribute_Builtin_ensureNoArgs___closed__3));
v___x_683_ = l_Lean_stringToMessageData(v___x_682_);
return v___x_683_;
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_ensureNoArgs(lean_object* v_stx_690_, lean_object* v_a_691_, lean_object* v_a_692_){
_start:
{
lean_object* v___x_694_; uint8_t v___y_705_; lean_object* v___x_711_; uint8_t v___x_712_; 
lean_inc(v_stx_690_);
v___x_694_ = l_Lean_Syntax_getKind(v_stx_690_);
v___x_711_ = ((lean_object*)(l_Lean_Attribute_Builtin_ensureNoArgs___closed__6));
v___x_712_ = lean_name_eq(v___x_694_, v___x_711_);
if (v___x_712_ == 0)
{
v___y_705_ = v___x_712_;
goto v___jp_704_;
}
else
{
lean_object* v___x_713_; lean_object* v___x_714_; uint8_t v___x_715_; 
v___x_713_ = lean_unsigned_to_nat(1u);
v___x_714_ = l_Lean_Syntax_getArg(v_stx_690_, v___x_713_);
v___x_715_ = l_Lean_Syntax_isNone(v___x_714_);
lean_dec(v___x_714_);
v___y_705_ = v___x_715_;
goto v___jp_704_;
}
v___jp_695_:
{
lean_object* v___x_696_; uint8_t v___x_697_; 
v___x_696_ = ((lean_object*)(l_Lean_Attribute_Builtin_ensureNoArgs___closed__2));
v___x_697_ = lean_name_eq(v___x_694_, v___x_696_);
lean_dec(v___x_694_);
if (v___x_697_ == 0)
{
if (lean_obj_tag(v_stx_690_) == 0)
{
lean_object* v___x_698_; lean_object* v___x_699_; 
v___x_698_ = lean_box(0);
v___x_699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_699_, 0, v___x_698_);
return v___x_699_;
}
else
{
lean_object* v___x_700_; lean_object* v___x_701_; 
v___x_700_ = lean_obj_once(&l_Lean_Attribute_Builtin_ensureNoArgs___closed__4, &l_Lean_Attribute_Builtin_ensureNoArgs___closed__4_once, _init_l_Lean_Attribute_Builtin_ensureNoArgs___closed__4);
v___x_701_ = l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg(v_stx_690_, v___x_700_, v_a_691_, v_a_692_);
lean_dec(v_stx_690_);
return v___x_701_;
}
}
else
{
lean_object* v___x_702_; lean_object* v___x_703_; 
lean_dec(v_stx_690_);
v___x_702_ = lean_box(0);
v___x_703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_703_, 0, v___x_702_);
return v___x_703_;
}
}
v___jp_704_:
{
if (v___y_705_ == 0)
{
goto v___jp_695_;
}
else
{
lean_object* v___x_706_; lean_object* v___x_707_; uint8_t v___x_708_; 
v___x_706_ = lean_unsigned_to_nat(2u);
v___x_707_ = l_Lean_Syntax_getArg(v_stx_690_, v___x_706_);
v___x_708_ = l_Lean_Syntax_isNone(v___x_707_);
lean_dec(v___x_707_);
if (v___x_708_ == 0)
{
goto v___jp_695_;
}
else
{
lean_object* v___x_709_; lean_object* v___x_710_; 
lean_dec(v___x_694_);
lean_dec(v_stx_690_);
v___x_709_ = lean_box(0);
v___x_710_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_710_, 0, v___x_709_);
return v___x_710_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_ensureNoArgs___boxed(lean_object* v_stx_716_, lean_object* v_a_717_, lean_object* v_a_718_, lean_object* v_a_719_){
_start:
{
lean_object* v_res_720_; 
v_res_720_ = l_Lean_Attribute_Builtin_ensureNoArgs(v_stx_716_, v_a_717_, v_a_718_);
lean_dec(v_a_718_);
lean_dec_ref(v_a_717_);
return v_res_720_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0(lean_object* v_00_u03b1_721_, lean_object* v_ref_722_, lean_object* v_msg_723_, lean_object* v___y_724_, lean_object* v___y_725_){
_start:
{
lean_object* v___x_727_; 
v___x_727_ = l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg(v_ref_722_, v_msg_723_, v___y_724_, v___y_725_);
return v___x_727_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___boxed(lean_object* v_00_u03b1_728_, lean_object* v_ref_729_, lean_object* v_msg_730_, lean_object* v___y_731_, lean_object* v___y_732_, lean_object* v___y_733_){
_start:
{
lean_object* v_res_734_; 
v_res_734_ = l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0(v_00_u03b1_728_, v_ref_729_, v_msg_730_, v___y_731_, v___y_732_);
lean_dec(v___y_732_);
lean_dec_ref(v___y_731_);
lean_dec(v_ref_729_);
return v_res_734_;
}
}
static lean_object* _init_l_Lean_Attribute_Builtin_getIdent_x3f___closed__5(void){
_start:
{
lean_object* v___x_748_; lean_object* v___x_749_; 
v___x_748_ = ((lean_object*)(l_Lean_Attribute_Builtin_getIdent_x3f___closed__4));
v___x_749_ = l_Lean_stringToMessageData(v___x_748_);
return v___x_749_;
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getIdent_x3f(lean_object* v_stx_750_, lean_object* v_a_751_, lean_object* v_a_752_){
_start:
{
lean_object* v___x_762_; lean_object* v___x_763_; uint8_t v___x_764_; 
lean_inc(v_stx_750_);
v___x_762_ = l_Lean_Syntax_getKind(v_stx_750_);
v___x_763_ = ((lean_object*)(l_Lean_Attribute_Builtin_ensureNoArgs___closed__6));
v___x_764_ = lean_name_eq(v___x_762_, v___x_763_);
if (v___x_764_ == 0)
{
lean_object* v___x_765_; uint8_t v___x_766_; 
v___x_765_ = ((lean_object*)(l_Lean_Attribute_Builtin_getIdent_x3f___closed__1));
v___x_766_ = lean_name_eq(v___x_762_, v___x_765_);
if (v___x_766_ == 0)
{
lean_object* v___x_767_; uint8_t v___x_768_; 
v___x_767_ = ((lean_object*)(l_Lean_Attribute_Builtin_getIdent_x3f___closed__3));
v___x_768_ = lean_name_eq(v___x_762_, v___x_767_);
lean_dec(v___x_762_);
if (v___x_768_ == 0)
{
lean_object* v___x_769_; lean_object* v___x_770_; 
v___x_769_ = lean_obj_once(&l_Lean_Attribute_Builtin_getIdent_x3f___closed__5, &l_Lean_Attribute_Builtin_getIdent_x3f___closed__5_once, _init_l_Lean_Attribute_Builtin_getIdent_x3f___closed__5);
v___x_770_ = l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg(v_stx_750_, v___x_769_, v_a_751_, v_a_752_);
lean_dec(v_stx_750_);
return v___x_770_;
}
else
{
goto v___jp_754_;
}
}
else
{
lean_dec(v___x_762_);
goto v___jp_754_;
}
}
else
{
lean_object* v___x_771_; lean_object* v___x_772_; uint8_t v___x_773_; 
lean_dec(v___x_762_);
v___x_771_ = lean_unsigned_to_nat(1u);
v___x_772_ = l_Lean_Syntax_getArg(v_stx_750_, v___x_771_);
lean_dec(v_stx_750_);
v___x_773_ = l_Lean_Syntax_isNone(v___x_772_);
if (v___x_773_ == 0)
{
if (v___x_764_ == 0)
{
lean_dec(v___x_772_);
goto v___jp_759_;
}
else
{
lean_object* v___x_774_; lean_object* v___x_775_; uint8_t v___x_776_; 
v___x_774_ = lean_unsigned_to_nat(0u);
v___x_775_ = l_Lean_Syntax_getArg(v___x_772_, v___x_774_);
lean_dec(v___x_772_);
v___x_776_ = l_Lean_Syntax_isIdent(v___x_775_);
if (v___x_776_ == 0)
{
lean_dec(v___x_775_);
goto v___jp_759_;
}
else
{
lean_object* v___x_777_; lean_object* v___x_778_; 
v___x_777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_777_, 0, v___x_775_);
v___x_778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_778_, 0, v___x_777_);
return v___x_778_;
}
}
}
else
{
lean_dec(v___x_772_);
goto v___jp_759_;
}
}
v___jp_754_:
{
lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; 
v___x_755_ = lean_unsigned_to_nat(1u);
v___x_756_ = l_Lean_Syntax_getArg(v_stx_750_, v___x_755_);
lean_dec(v_stx_750_);
v___x_757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_757_, 0, v___x_756_);
v___x_758_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_758_, 0, v___x_757_);
return v___x_758_;
}
v___jp_759_:
{
lean_object* v___x_760_; lean_object* v___x_761_; 
v___x_760_ = lean_box(0);
v___x_761_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_761_, 0, v___x_760_);
return v___x_761_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getIdent_x3f___boxed(lean_object* v_stx_779_, lean_object* v_a_780_, lean_object* v_a_781_, lean_object* v_a_782_){
_start:
{
lean_object* v_res_783_; 
v_res_783_ = l_Lean_Attribute_Builtin_getIdent_x3f(v_stx_779_, v_a_780_, v_a_781_);
lean_dec(v_a_781_);
lean_dec_ref(v_a_780_);
return v_res_783_;
}
}
static lean_object* _init_l_Lean_Attribute_Builtin_getIdent___closed__1(void){
_start:
{
lean_object* v___x_785_; lean_object* v___x_786_; 
v___x_785_ = ((lean_object*)(l_Lean_Attribute_Builtin_getIdent___closed__0));
v___x_786_ = l_Lean_stringToMessageData(v___x_785_);
return v___x_786_;
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getIdent(lean_object* v_stx_787_, lean_object* v_a_788_, lean_object* v_a_789_){
_start:
{
lean_object* v___x_791_; 
lean_inc(v_stx_787_);
v___x_791_ = l_Lean_Attribute_Builtin_getIdent_x3f(v_stx_787_, v_a_788_, v_a_789_);
if (lean_obj_tag(v___x_791_) == 0)
{
lean_object* v_a_792_; lean_object* v___x_794_; uint8_t v_isShared_795_; uint8_t v_isSharedCheck_805_; 
v_a_792_ = lean_ctor_get(v___x_791_, 0);
v_isSharedCheck_805_ = !lean_is_exclusive(v___x_791_);
if (v_isSharedCheck_805_ == 0)
{
v___x_794_ = v___x_791_;
v_isShared_795_ = v_isSharedCheck_805_;
goto v_resetjp_793_;
}
else
{
lean_inc(v_a_792_);
lean_dec(v___x_791_);
v___x_794_ = lean_box(0);
v_isShared_795_ = v_isSharedCheck_805_;
goto v_resetjp_793_;
}
v_resetjp_793_:
{
if (lean_obj_tag(v_a_792_) == 0)
{
lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; 
lean_del_object(v___x_794_);
v___x_796_ = lean_obj_once(&l_Lean_Attribute_Builtin_getIdent___closed__1, &l_Lean_Attribute_Builtin_getIdent___closed__1_once, _init_l_Lean_Attribute_Builtin_getIdent___closed__1);
lean_inc(v_stx_787_);
v___x_797_ = l_Lean_MessageData_ofSyntax(v_stx_787_);
v___x_798_ = l_Lean_indentD(v___x_797_);
v___x_799_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_799_, 0, v___x_796_);
lean_ctor_set(v___x_799_, 1, v___x_798_);
v___x_800_ = l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg(v_stx_787_, v___x_799_, v_a_788_, v_a_789_);
lean_dec(v_stx_787_);
return v___x_800_;
}
else
{
lean_object* v_val_801_; lean_object* v___x_803_; 
lean_dec(v_stx_787_);
v_val_801_ = lean_ctor_get(v_a_792_, 0);
lean_inc(v_val_801_);
lean_dec_ref_known(v_a_792_, 1);
if (v_isShared_795_ == 0)
{
lean_ctor_set(v___x_794_, 0, v_val_801_);
v___x_803_ = v___x_794_;
goto v_reusejp_802_;
}
else
{
lean_object* v_reuseFailAlloc_804_; 
v_reuseFailAlloc_804_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_804_, 0, v_val_801_);
v___x_803_ = v_reuseFailAlloc_804_;
goto v_reusejp_802_;
}
v_reusejp_802_:
{
return v___x_803_;
}
}
}
}
else
{
lean_object* v_a_806_; lean_object* v___x_808_; uint8_t v_isShared_809_; uint8_t v_isSharedCheck_813_; 
lean_dec(v_stx_787_);
v_a_806_ = lean_ctor_get(v___x_791_, 0);
v_isSharedCheck_813_ = !lean_is_exclusive(v___x_791_);
if (v_isSharedCheck_813_ == 0)
{
v___x_808_ = v___x_791_;
v_isShared_809_ = v_isSharedCheck_813_;
goto v_resetjp_807_;
}
else
{
lean_inc(v_a_806_);
lean_dec(v___x_791_);
v___x_808_ = lean_box(0);
v_isShared_809_ = v_isSharedCheck_813_;
goto v_resetjp_807_;
}
v_resetjp_807_:
{
lean_object* v___x_811_; 
if (v_isShared_809_ == 0)
{
v___x_811_ = v___x_808_;
goto v_reusejp_810_;
}
else
{
lean_object* v_reuseFailAlloc_812_; 
v_reuseFailAlloc_812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_812_, 0, v_a_806_);
v___x_811_ = v_reuseFailAlloc_812_;
goto v_reusejp_810_;
}
v_reusejp_810_:
{
return v___x_811_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getIdent___boxed(lean_object* v_stx_814_, lean_object* v_a_815_, lean_object* v_a_816_, lean_object* v_a_817_){
_start:
{
lean_object* v_res_818_; 
v_res_818_ = l_Lean_Attribute_Builtin_getIdent(v_stx_814_, v_a_815_, v_a_816_);
lean_dec(v_a_816_);
lean_dec_ref(v_a_815_);
return v_res_818_;
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getId_x3f(lean_object* v_stx_819_, lean_object* v_a_820_, lean_object* v_a_821_){
_start:
{
lean_object* v___x_823_; 
v___x_823_ = l_Lean_Attribute_Builtin_getIdent_x3f(v_stx_819_, v_a_820_, v_a_821_);
if (lean_obj_tag(v___x_823_) == 0)
{
lean_object* v_a_824_; lean_object* v___x_826_; uint8_t v_isShared_827_; uint8_t v_isSharedCheck_844_; 
v_a_824_ = lean_ctor_get(v___x_823_, 0);
v_isSharedCheck_844_ = !lean_is_exclusive(v___x_823_);
if (v_isSharedCheck_844_ == 0)
{
v___x_826_ = v___x_823_;
v_isShared_827_ = v_isSharedCheck_844_;
goto v_resetjp_825_;
}
else
{
lean_inc(v_a_824_);
lean_dec(v___x_823_);
v___x_826_ = lean_box(0);
v_isShared_827_ = v_isSharedCheck_844_;
goto v_resetjp_825_;
}
v_resetjp_825_:
{
if (lean_obj_tag(v_a_824_) == 0)
{
lean_object* v___x_828_; lean_object* v___x_830_; 
v___x_828_ = lean_box(0);
if (v_isShared_827_ == 0)
{
lean_ctor_set(v___x_826_, 0, v___x_828_);
v___x_830_ = v___x_826_;
goto v_reusejp_829_;
}
else
{
lean_object* v_reuseFailAlloc_831_; 
v_reuseFailAlloc_831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_831_, 0, v___x_828_);
v___x_830_ = v_reuseFailAlloc_831_;
goto v_reusejp_829_;
}
v_reusejp_829_:
{
return v___x_830_;
}
}
else
{
lean_object* v_val_832_; lean_object* v___x_834_; uint8_t v_isShared_835_; uint8_t v_isSharedCheck_843_; 
v_val_832_ = lean_ctor_get(v_a_824_, 0);
v_isSharedCheck_843_ = !lean_is_exclusive(v_a_824_);
if (v_isSharedCheck_843_ == 0)
{
v___x_834_ = v_a_824_;
v_isShared_835_ = v_isSharedCheck_843_;
goto v_resetjp_833_;
}
else
{
lean_inc(v_val_832_);
lean_dec(v_a_824_);
v___x_834_ = lean_box(0);
v_isShared_835_ = v_isSharedCheck_843_;
goto v_resetjp_833_;
}
v_resetjp_833_:
{
lean_object* v___x_836_; lean_object* v___x_838_; 
v___x_836_ = l_Lean_Syntax_getId(v_val_832_);
lean_dec(v_val_832_);
if (v_isShared_835_ == 0)
{
lean_ctor_set(v___x_834_, 0, v___x_836_);
v___x_838_ = v___x_834_;
goto v_reusejp_837_;
}
else
{
lean_object* v_reuseFailAlloc_842_; 
v_reuseFailAlloc_842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_842_, 0, v___x_836_);
v___x_838_ = v_reuseFailAlloc_842_;
goto v_reusejp_837_;
}
v_reusejp_837_:
{
lean_object* v___x_840_; 
if (v_isShared_827_ == 0)
{
lean_ctor_set(v___x_826_, 0, v___x_838_);
v___x_840_ = v___x_826_;
goto v_reusejp_839_;
}
else
{
lean_object* v_reuseFailAlloc_841_; 
v_reuseFailAlloc_841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_841_, 0, v___x_838_);
v___x_840_ = v_reuseFailAlloc_841_;
goto v_reusejp_839_;
}
v_reusejp_839_:
{
return v___x_840_;
}
}
}
}
}
}
else
{
lean_object* v_a_845_; lean_object* v___x_847_; uint8_t v_isShared_848_; uint8_t v_isSharedCheck_852_; 
v_a_845_ = lean_ctor_get(v___x_823_, 0);
v_isSharedCheck_852_ = !lean_is_exclusive(v___x_823_);
if (v_isSharedCheck_852_ == 0)
{
v___x_847_ = v___x_823_;
v_isShared_848_ = v_isSharedCheck_852_;
goto v_resetjp_846_;
}
else
{
lean_inc(v_a_845_);
lean_dec(v___x_823_);
v___x_847_ = lean_box(0);
v_isShared_848_ = v_isSharedCheck_852_;
goto v_resetjp_846_;
}
v_resetjp_846_:
{
lean_object* v___x_850_; 
if (v_isShared_848_ == 0)
{
v___x_850_ = v___x_847_;
goto v_reusejp_849_;
}
else
{
lean_object* v_reuseFailAlloc_851_; 
v_reuseFailAlloc_851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_851_, 0, v_a_845_);
v___x_850_ = v_reuseFailAlloc_851_;
goto v_reusejp_849_;
}
v_reusejp_849_:
{
return v___x_850_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getId_x3f___boxed(lean_object* v_stx_853_, lean_object* v_a_854_, lean_object* v_a_855_, lean_object* v_a_856_){
_start:
{
lean_object* v_res_857_; 
v_res_857_ = l_Lean_Attribute_Builtin_getId_x3f(v_stx_853_, v_a_854_, v_a_855_);
lean_dec(v_a_855_);
lean_dec_ref(v_a_854_);
return v_res_857_;
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getId(lean_object* v_stx_858_, lean_object* v_a_859_, lean_object* v_a_860_){
_start:
{
lean_object* v___x_862_; 
v___x_862_ = l_Lean_Attribute_Builtin_getIdent(v_stx_858_, v_a_859_, v_a_860_);
if (lean_obj_tag(v___x_862_) == 0)
{
lean_object* v_a_863_; lean_object* v___x_865_; uint8_t v_isShared_866_; uint8_t v_isSharedCheck_871_; 
v_a_863_ = lean_ctor_get(v___x_862_, 0);
v_isSharedCheck_871_ = !lean_is_exclusive(v___x_862_);
if (v_isSharedCheck_871_ == 0)
{
v___x_865_ = v___x_862_;
v_isShared_866_ = v_isSharedCheck_871_;
goto v_resetjp_864_;
}
else
{
lean_inc(v_a_863_);
lean_dec(v___x_862_);
v___x_865_ = lean_box(0);
v_isShared_866_ = v_isSharedCheck_871_;
goto v_resetjp_864_;
}
v_resetjp_864_:
{
lean_object* v___x_867_; lean_object* v___x_869_; 
v___x_867_ = l_Lean_Syntax_getId(v_a_863_);
lean_dec(v_a_863_);
if (v_isShared_866_ == 0)
{
lean_ctor_set(v___x_865_, 0, v___x_867_);
v___x_869_ = v___x_865_;
goto v_reusejp_868_;
}
else
{
lean_object* v_reuseFailAlloc_870_; 
v_reuseFailAlloc_870_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_870_, 0, v___x_867_);
v___x_869_ = v_reuseFailAlloc_870_;
goto v_reusejp_868_;
}
v_reusejp_868_:
{
return v___x_869_;
}
}
}
else
{
lean_object* v_a_872_; lean_object* v___x_874_; uint8_t v_isShared_875_; uint8_t v_isSharedCheck_879_; 
v_a_872_ = lean_ctor_get(v___x_862_, 0);
v_isSharedCheck_879_ = !lean_is_exclusive(v___x_862_);
if (v_isSharedCheck_879_ == 0)
{
v___x_874_ = v___x_862_;
v_isShared_875_ = v_isSharedCheck_879_;
goto v_resetjp_873_;
}
else
{
lean_inc(v_a_872_);
lean_dec(v___x_862_);
v___x_874_ = lean_box(0);
v_isShared_875_ = v_isSharedCheck_879_;
goto v_resetjp_873_;
}
v_resetjp_873_:
{
lean_object* v___x_877_; 
if (v_isShared_875_ == 0)
{
v___x_877_ = v___x_874_;
goto v_reusejp_876_;
}
else
{
lean_object* v_reuseFailAlloc_878_; 
v_reuseFailAlloc_878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_878_, 0, v_a_872_);
v___x_877_ = v_reuseFailAlloc_878_;
goto v_reusejp_876_;
}
v_reusejp_876_:
{
return v___x_877_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getId___boxed(lean_object* v_stx_880_, lean_object* v_a_881_, lean_object* v_a_882_, lean_object* v_a_883_){
_start:
{
lean_object* v_res_884_; 
v_res_884_ = l_Lean_Attribute_Builtin_getId(v_stx_880_, v_a_881_, v_a_882_);
lean_dec(v_a_882_);
lean_dec_ref(v_a_881_);
return v_res_884_;
}
}
static lean_object* _init_l_Lean_getAttrParamOptPrio___closed__1(void){
_start:
{
lean_object* v___x_886_; lean_object* v___x_887_; 
v___x_886_ = ((lean_object*)(l_Lean_getAttrParamOptPrio___closed__0));
v___x_887_ = l_Lean_stringToMessageData(v___x_886_);
return v___x_887_;
}
}
LEAN_EXPORT lean_object* l_Lean_getAttrParamOptPrio(lean_object* v_optPrioStx_888_, lean_object* v_a_889_, lean_object* v_a_890_){
_start:
{
uint8_t v___x_892_; 
v___x_892_ = l_Lean_Syntax_isNone(v_optPrioStx_888_);
if (v___x_892_ == 0)
{
lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; 
v___x_893_ = lean_unsigned_to_nat(0u);
v___x_894_ = l_Lean_Syntax_getArg(v_optPrioStx_888_, v___x_893_);
v___x_895_ = l_Lean_Syntax_isNatLit_x3f(v___x_894_);
lean_dec(v___x_894_);
if (lean_obj_tag(v___x_895_) == 0)
{
lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; 
v___x_896_ = lean_obj_once(&l_Lean_getAttrParamOptPrio___closed__1, &l_Lean_getAttrParamOptPrio___closed__1_once, _init_l_Lean_getAttrParamOptPrio___closed__1);
lean_inc(v_optPrioStx_888_);
v___x_897_ = l_Lean_MessageData_ofSyntax(v_optPrioStx_888_);
v___x_898_ = l_Lean_indentD(v___x_897_);
v___x_899_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_899_, 0, v___x_896_);
lean_ctor_set(v___x_899_, 1, v___x_898_);
v___x_900_ = l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg(v_optPrioStx_888_, v___x_899_, v_a_889_, v_a_890_);
lean_dec(v_optPrioStx_888_);
return v___x_900_;
}
else
{
lean_object* v_val_901_; lean_object* v___x_903_; uint8_t v_isShared_904_; uint8_t v_isSharedCheck_908_; 
lean_dec(v_optPrioStx_888_);
v_val_901_ = lean_ctor_get(v___x_895_, 0);
v_isSharedCheck_908_ = !lean_is_exclusive(v___x_895_);
if (v_isSharedCheck_908_ == 0)
{
v___x_903_ = v___x_895_;
v_isShared_904_ = v_isSharedCheck_908_;
goto v_resetjp_902_;
}
else
{
lean_inc(v_val_901_);
lean_dec(v___x_895_);
v___x_903_ = lean_box(0);
v_isShared_904_ = v_isSharedCheck_908_;
goto v_resetjp_902_;
}
v_resetjp_902_:
{
lean_object* v___x_906_; 
if (v_isShared_904_ == 0)
{
lean_ctor_set_tag(v___x_903_, 0);
v___x_906_ = v___x_903_;
goto v_reusejp_905_;
}
else
{
lean_object* v_reuseFailAlloc_907_; 
v_reuseFailAlloc_907_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_907_, 0, v_val_901_);
v___x_906_ = v_reuseFailAlloc_907_;
goto v_reusejp_905_;
}
v_reusejp_905_:
{
return v___x_906_;
}
}
}
}
else
{
lean_object* v___x_909_; lean_object* v___x_910_; 
lean_dec(v_optPrioStx_888_);
v___x_909_ = lean_unsigned_to_nat(1000u);
v___x_910_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_910_, 0, v___x_909_);
return v___x_910_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getAttrParamOptPrio___boxed(lean_object* v_optPrioStx_911_, lean_object* v_a_912_, lean_object* v_a_913_, lean_object* v_a_914_){
_start:
{
lean_object* v_res_915_; 
v_res_915_ = l_Lean_getAttrParamOptPrio(v_optPrioStx_911_, v_a_912_, v_a_913_);
lean_dec(v_a_913_);
lean_dec_ref(v_a_912_);
return v_res_915_;
}
}
static lean_object* _init_l_Lean_Attribute_Builtin_getPrio___closed__1(void){
_start:
{
lean_object* v___x_917_; lean_object* v___x_918_; 
v___x_917_ = ((lean_object*)(l_Lean_Attribute_Builtin_getPrio___closed__0));
v___x_918_ = l_Lean_stringToMessageData(v___x_917_);
return v___x_918_;
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getPrio(lean_object* v_stx_919_, lean_object* v_a_920_, lean_object* v_a_921_){
_start:
{
lean_object* v___x_923_; lean_object* v___x_924_; uint8_t v___x_925_; 
lean_inc(v_stx_919_);
v___x_923_ = l_Lean_Syntax_getKind(v_stx_919_);
v___x_924_ = ((lean_object*)(l_Lean_Attribute_Builtin_ensureNoArgs___closed__6));
v___x_925_ = lean_name_eq(v___x_923_, v___x_924_);
lean_dec(v___x_923_);
if (v___x_925_ == 0)
{
lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; 
v___x_926_ = lean_obj_once(&l_Lean_Attribute_Builtin_getPrio___closed__1, &l_Lean_Attribute_Builtin_getPrio___closed__1_once, _init_l_Lean_Attribute_Builtin_getPrio___closed__1);
lean_inc(v_stx_919_);
v___x_927_ = l_Lean_MessageData_ofSyntax(v_stx_919_);
v___x_928_ = l_Lean_indentD(v___x_927_);
v___x_929_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_929_, 0, v___x_926_);
lean_ctor_set(v___x_929_, 1, v___x_928_);
v___x_930_ = l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg(v_stx_919_, v___x_929_, v_a_920_, v_a_921_);
lean_dec(v_stx_919_);
return v___x_930_;
}
else
{
lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; 
v___x_931_ = lean_unsigned_to_nat(1u);
v___x_932_ = l_Lean_Syntax_getArg(v_stx_919_, v___x_931_);
lean_dec(v_stx_919_);
v___x_933_ = l_Lean_getAttrParamOptPrio(v___x_932_, v_a_920_, v_a_921_);
return v___x_933_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getPrio___boxed(lean_object* v_stx_934_, lean_object* v_a_935_, lean_object* v_a_936_, lean_object* v_a_937_){
_start:
{
lean_object* v_res_938_; 
v_res_938_ = l_Lean_Attribute_Builtin_getPrio(v_stx_934_, v_a_935_, v_a_936_);
lean_dec(v_a_936_);
lean_dec_ref(v_a_935_);
return v_res_938_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__1(void){
_start:
{
lean_object* v___x_940_; lean_object* v___x_941_; 
v___x_940_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__0));
v___x_941_ = l_Lean_stringToMessageData(v___x_940_);
return v___x_941_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__3(void){
_start:
{
lean_object* v___x_943_; lean_object* v___x_944_; 
v___x_943_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__2));
v___x_944_ = l_Lean_stringToMessageData(v___x_943_);
return v___x_944_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__5(void){
_start:
{
lean_object* v___x_946_; lean_object* v___x_947_; 
v___x_946_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__4));
v___x_947_ = l_Lean_stringToMessageData(v___x_946_);
return v___x_947_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___redArg(lean_object* v_inst_948_, lean_object* v_inst_949_, lean_object* v_name_950_, uint8_t v_kind_951_){
_start:
{
lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___y_958_; 
v___x_952_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__1, &l_Lean_throwAttrMustBeGlobal___redArg___closed__1_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__1);
v___x_953_ = l_Lean_MessageData_ofName(v_name_950_);
v___x_954_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_954_, 0, v___x_952_);
lean_ctor_set(v___x_954_, 1, v___x_953_);
v___x_955_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__3, &l_Lean_throwAttrMustBeGlobal___redArg___closed__3_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__3);
v___x_956_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_956_, 0, v___x_954_);
lean_ctor_set(v___x_956_, 1, v___x_955_);
switch(v_kind_951_)
{
case 0:
{
lean_object* v___x_965_; 
v___x_965_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__0));
v___y_958_ = v___x_965_;
goto v___jp_957_;
}
case 1:
{
lean_object* v___x_966_; 
v___x_966_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__1));
v___y_958_ = v___x_966_;
goto v___jp_957_;
}
default: 
{
lean_object* v___x_967_; 
v___x_967_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__2));
v___y_958_ = v___x_967_;
goto v___jp_957_;
}
}
v___jp_957_:
{
lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; 
lean_inc_ref(v___y_958_);
v___x_959_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_959_, 0, v___y_958_);
v___x_960_ = l_Lean_MessageData_ofFormat(v___x_959_);
v___x_961_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_961_, 0, v___x_956_);
lean_ctor_set(v___x_961_, 1, v___x_960_);
v___x_962_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__5, &l_Lean_throwAttrMustBeGlobal___redArg___closed__5_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__5);
v___x_963_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_963_, 0, v___x_961_);
lean_ctor_set(v___x_963_, 1, v___x_962_);
v___x_964_ = l_Lean_throwError___redArg(v_inst_948_, v_inst_949_, v___x_963_);
return v___x_964_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___redArg___boxed(lean_object* v_inst_968_, lean_object* v_inst_969_, lean_object* v_name_970_, lean_object* v_kind_971_){
_start:
{
uint8_t v_kind_boxed_972_; lean_object* v_res_973_; 
v_kind_boxed_972_ = lean_unbox(v_kind_971_);
v_res_973_ = l_Lean_throwAttrMustBeGlobal___redArg(v_inst_968_, v_inst_969_, v_name_970_, v_kind_boxed_972_);
return v_res_973_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal(lean_object* v_m_974_, lean_object* v_inst_975_, lean_object* v_inst_976_, lean_object* v_00_u03b1_977_, lean_object* v_name_978_, uint8_t v_kind_979_){
_start:
{
lean_object* v___x_980_; 
v___x_980_ = l_Lean_throwAttrMustBeGlobal___redArg(v_inst_975_, v_inst_976_, v_name_978_, v_kind_979_);
return v___x_980_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___boxed(lean_object* v_m_981_, lean_object* v_inst_982_, lean_object* v_inst_983_, lean_object* v_00_u03b1_984_, lean_object* v_name_985_, lean_object* v_kind_986_){
_start:
{
uint8_t v_kind_boxed_987_; lean_object* v_res_988_; 
v_kind_boxed_987_ = lean_unbox(v_kind_986_);
v_res_988_ = l_Lean_throwAttrMustBeGlobal(v_m_981_, v_inst_982_, v_inst_983_, v_00_u03b1_984_, v_name_985_, v_kind_boxed_987_);
return v_res_988_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1(void){
_start:
{
lean_object* v___x_990_; lean_object* v___x_991_; 
v___x_990_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___redArg___closed__0));
v___x_991_ = l_Lean_stringToMessageData(v___x_990_);
return v___x_991_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__3(void){
_start:
{
lean_object* v___x_993_; lean_object* v___x_994_; 
v___x_993_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___redArg___closed__2));
v___x_994_ = l_Lean_stringToMessageData(v___x_993_);
return v___x_994_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__5(void){
_start:
{
lean_object* v___x_996_; lean_object* v___x_997_; 
v___x_996_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___redArg___closed__4));
v___x_997_ = l_Lean_stringToMessageData(v___x_996_);
return v___x_997_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___redArg(lean_object* v_inst_998_, lean_object* v_inst_999_, lean_object* v_attrName_1000_, lean_object* v_declName_1001_){
_start:
{
lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; uint8_t v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; 
v___x_1002_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1);
v___x_1003_ = l_Lean_MessageData_ofName(v_attrName_1000_);
v___x_1004_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1004_, 0, v___x_1002_);
lean_ctor_set(v___x_1004_, 1, v___x_1003_);
v___x_1005_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__3, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__3_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__3);
v___x_1006_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1006_, 0, v___x_1004_);
lean_ctor_set(v___x_1006_, 1, v___x_1005_);
v___x_1007_ = 0;
v___x_1008_ = l_Lean_MessageData_ofConstName(v_declName_1001_, v___x_1007_);
v___x_1009_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1009_, 0, v___x_1006_);
lean_ctor_set(v___x_1009_, 1, v___x_1008_);
v___x_1010_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__5, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__5_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__5);
v___x_1011_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1011_, 0, v___x_1009_);
lean_ctor_set(v___x_1011_, 1, v___x_1010_);
v___x_1012_ = l_Lean_throwError___redArg(v_inst_998_, v_inst_999_, v___x_1011_);
return v___x_1012_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule(lean_object* v_m_1013_, lean_object* v_inst_1014_, lean_object* v_inst_1015_, lean_object* v_00_u03b1_1016_, lean_object* v_attrName_1017_, lean_object* v_declName_1018_){
_start:
{
lean_object* v___x_1019_; 
v___x_1019_ = l_Lean_throwAttrDeclInImportedModule___redArg(v_inst_1014_, v_inst_1015_, v_attrName_1017_, v_declName_1018_);
return v___x_1019_;
}
}
static lean_object* _init_l_Lean_throwAttrNotInAsyncCtx___redArg___closed__1(void){
_start:
{
lean_object* v___x_1021_; lean_object* v___x_1022_; 
v___x_1021_ = ((lean_object*)(l_Lean_throwAttrNotInAsyncCtx___redArg___closed__0));
v___x_1022_ = l_Lean_stringToMessageData(v___x_1021_);
return v___x_1022_;
}
}
static lean_object* _init_l_Lean_throwAttrNotInAsyncCtx___redArg___closed__3(void){
_start:
{
lean_object* v___x_1024_; lean_object* v___x_1025_; 
v___x_1024_ = ((lean_object*)(l_Lean_throwAttrNotInAsyncCtx___redArg___closed__2));
v___x_1025_ = l_Lean_stringToMessageData(v___x_1024_);
return v___x_1025_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___redArg(lean_object* v_inst_1026_, lean_object* v_inst_1027_, lean_object* v_attrName_1028_, lean_object* v_declName_1029_, lean_object* v_asyncPrefix_x3f_1030_){
_start:
{
lean_object* v___y_1032_; 
if (lean_obj_tag(v_asyncPrefix_x3f_1030_) == 0)
{
lean_object* v___x_1045_; 
v___x_1045_ = l_Lean_MessageData_nil;
v___y_1032_ = v___x_1045_;
goto v___jp_1031_;
}
else
{
lean_object* v_val_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; 
v_val_1046_ = lean_ctor_get(v_asyncPrefix_x3f_1030_, 0);
lean_inc(v_val_1046_);
lean_dec_ref_known(v_asyncPrefix_x3f_1030_, 1);
v___x_1047_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___redArg___closed__3, &l_Lean_throwAttrNotInAsyncCtx___redArg___closed__3_once, _init_l_Lean_throwAttrNotInAsyncCtx___redArg___closed__3);
v___x_1048_ = l_Lean_MessageData_ofName(v_val_1046_);
v___x_1049_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1049_, 0, v___x_1047_);
lean_ctor_set(v___x_1049_, 1, v___x_1048_);
v___x_1050_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__5, &l_Lean_throwAttrMustBeGlobal___redArg___closed__5_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__5);
v___x_1051_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1051_, 0, v___x_1049_);
lean_ctor_set(v___x_1051_, 1, v___x_1050_);
v___y_1032_ = v___x_1051_;
goto v___jp_1031_;
}
v___jp_1031_:
{
lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; uint8_t v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; 
v___x_1033_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1);
v___x_1034_ = l_Lean_MessageData_ofName(v_attrName_1028_);
v___x_1035_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1035_, 0, v___x_1033_);
lean_ctor_set(v___x_1035_, 1, v___x_1034_);
v___x_1036_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__3, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__3_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__3);
v___x_1037_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1037_, 0, v___x_1035_);
lean_ctor_set(v___x_1037_, 1, v___x_1036_);
v___x_1038_ = 0;
v___x_1039_ = l_Lean_MessageData_ofConstName(v_declName_1029_, v___x_1038_);
v___x_1040_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1040_, 0, v___x_1037_);
lean_ctor_set(v___x_1040_, 1, v___x_1039_);
v___x_1041_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___redArg___closed__1, &l_Lean_throwAttrNotInAsyncCtx___redArg___closed__1_once, _init_l_Lean_throwAttrNotInAsyncCtx___redArg___closed__1);
v___x_1042_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1042_, 0, v___x_1040_);
lean_ctor_set(v___x_1042_, 1, v___x_1041_);
v___x_1043_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1043_, 0, v___x_1042_);
lean_ctor_set(v___x_1043_, 1, v___y_1032_);
v___x_1044_ = l_Lean_throwError___redArg(v_inst_1026_, v_inst_1027_, v___x_1043_);
return v___x_1044_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx(lean_object* v_m_1052_, lean_object* v_inst_1053_, lean_object* v_inst_1054_, lean_object* v_00_u03b1_1055_, lean_object* v_attrName_1056_, lean_object* v_declName_1057_, lean_object* v_asyncPrefix_x3f_1058_){
_start:
{
lean_object* v___x_1059_; 
v___x_1059_ = l_Lean_throwAttrNotInAsyncCtx___redArg(v_inst_1053_, v_inst_1054_, v_attrName_1056_, v_declName_1057_, v_asyncPrefix_x3f_1058_);
return v___x_1059_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1(void){
_start:
{
lean_object* v___x_1061_; lean_object* v___x_1062_; 
v___x_1061_ = ((lean_object*)(l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__0));
v___x_1062_ = l_Lean_stringToMessageData(v___x_1061_);
return v___x_1062_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__3(void){
_start:
{
lean_object* v___x_1064_; lean_object* v___x_1065_; 
v___x_1064_ = ((lean_object*)(l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__2));
v___x_1065_ = l_Lean_stringToMessageData(v___x_1064_);
return v___x_1065_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__5(void){
_start:
{
lean_object* v___x_1067_; lean_object* v___x_1068_; 
v___x_1067_ = ((lean_object*)(l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__4));
v___x_1068_ = l_Lean_stringToMessageData(v___x_1067_);
return v___x_1068_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__7(void){
_start:
{
lean_object* v___x_1070_; lean_object* v___x_1071_; 
v___x_1070_ = ((lean_object*)(l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__6));
v___x_1071_ = l_Lean_stringToMessageData(v___x_1070_);
return v___x_1071_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclNotOfExpectedType___redArg(lean_object* v_inst_1072_, lean_object* v_inst_1073_, lean_object* v_attrName_1074_, lean_object* v_declName_1075_, lean_object* v_givenType_1076_, lean_object* v_expectedType_1077_){
_start:
{
lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; uint8_t v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; 
v___x_1078_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1);
v___x_1079_ = l_Lean_MessageData_ofName(v_attrName_1074_);
lean_inc_ref(v___x_1079_);
v___x_1080_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1080_, 0, v___x_1078_);
lean_ctor_set(v___x_1080_, 1, v___x_1079_);
v___x_1081_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1, &l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1);
v___x_1082_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1082_, 0, v___x_1080_);
lean_ctor_set(v___x_1082_, 1, v___x_1081_);
v___x_1083_ = 0;
v___x_1084_ = l_Lean_MessageData_ofConstName(v_declName_1075_, v___x_1083_);
v___x_1085_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1085_, 0, v___x_1082_);
lean_ctor_set(v___x_1085_, 1, v___x_1084_);
v___x_1086_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__3, &l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__3_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__3);
v___x_1087_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1087_, 0, v___x_1085_);
lean_ctor_set(v___x_1087_, 1, v___x_1086_);
v___x_1088_ = l_Lean_indentExpr(v_givenType_1076_);
v___x_1089_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1089_, 0, v___x_1087_);
lean_ctor_set(v___x_1089_, 1, v___x_1088_);
v___x_1090_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__5, &l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__5_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__5);
v___x_1091_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1091_, 0, v___x_1089_);
lean_ctor_set(v___x_1091_, 1, v___x_1090_);
v___x_1092_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1092_, 0, v___x_1091_);
lean_ctor_set(v___x_1092_, 1, v___x_1079_);
v___x_1093_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__7, &l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__7_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__7);
v___x_1094_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1094_, 0, v___x_1092_);
lean_ctor_set(v___x_1094_, 1, v___x_1093_);
v___x_1095_ = l_Lean_indentExpr(v_expectedType_1077_);
v___x_1096_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1096_, 0, v___x_1094_);
lean_ctor_set(v___x_1096_, 1, v___x_1095_);
v___x_1097_ = l_Lean_throwError___redArg(v_inst_1072_, v_inst_1073_, v___x_1096_);
return v___x_1097_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclNotOfExpectedType(lean_object* v_m_1098_, lean_object* v_inst_1099_, lean_object* v_inst_1100_, lean_object* v_00_u03b1_1101_, lean_object* v_attrName_1102_, lean_object* v_declName_1103_, lean_object* v_givenType_1104_, lean_object* v_expectedType_1105_){
_start:
{
lean_object* v___x_1106_; 
v___x_1106_ = l_Lean_throwAttrDeclNotOfExpectedType___redArg(v_inst_1099_, v_inst_1100_, v_attrName_1102_, v_declName_1103_, v_givenType_1104_, v_expectedType_1105_);
return v___x_1106_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1___redArg(lean_object* v_constName_1107_, uint8_t v_skipRealize_1108_, lean_object* v___y_1109_){
_start:
{
lean_object* v___x_1111_; lean_object* v_env_1112_; uint8_t v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; 
v___x_1111_ = lean_st_ref_get(v___y_1109_);
v_env_1112_ = lean_ctor_get(v___x_1111_, 0);
lean_inc_ref(v_env_1112_);
lean_dec(v___x_1111_);
v___x_1113_ = l_Lean_Environment_contains(v_env_1112_, v_constName_1107_, v_skipRealize_1108_);
v___x_1114_ = lean_box(v___x_1113_);
v___x_1115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1115_, 0, v___x_1114_);
return v___x_1115_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1___redArg___boxed(lean_object* v_constName_1116_, lean_object* v_skipRealize_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_){
_start:
{
uint8_t v_skipRealize_boxed_1120_; lean_object* v_res_1121_; 
v_skipRealize_boxed_1120_ = lean_unbox(v_skipRealize_1117_);
v_res_1121_ = l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1___redArg(v_constName_1116_, v_skipRealize_boxed_1120_, v___y_1118_);
lean_dec(v___y_1118_);
return v_res_1121_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1(lean_object* v_constName_1122_, uint8_t v_skipRealize_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_){
_start:
{
lean_object* v___x_1127_; 
v___x_1127_ = l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1___redArg(v_constName_1122_, v_skipRealize_1123_, v___y_1125_);
return v___x_1127_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1___boxed(lean_object* v_constName_1128_, lean_object* v_skipRealize_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_){
_start:
{
uint8_t v_skipRealize_boxed_1133_; lean_object* v_res_1134_; 
v_skipRealize_boxed_1133_ = lean_unbox(v_skipRealize_1129_);
v_res_1134_ = l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1(v_constName_1128_, v_skipRealize_boxed_1133_, v___y_1130_, v___y_1131_);
lean_dec(v___y_1131_);
lean_dec_ref(v___y_1130_);
return v_res_1134_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___lam__0(lean_object* v___y_1135_, uint8_t v_isExporting_1136_, lean_object* v___x_1137_, lean_object* v_a_x3f_1138_){
_start:
{
lean_object* v___x_1140_; lean_object* v_env_1141_; lean_object* v_nextMacroScope_1142_; lean_object* v_ngen_1143_; lean_object* v_auxDeclNGen_1144_; lean_object* v_traceState_1145_; lean_object* v_recordedDeps_1146_; lean_object* v_messages_1147_; lean_object* v_infoState_1148_; lean_object* v_snapshotTasks_1149_; lean_object* v___x_1151_; uint8_t v_isShared_1152_; uint8_t v_isSharedCheck_1160_; 
v___x_1140_ = lean_st_ref_take(v___y_1135_);
v_env_1141_ = lean_ctor_get(v___x_1140_, 0);
v_nextMacroScope_1142_ = lean_ctor_get(v___x_1140_, 1);
v_ngen_1143_ = lean_ctor_get(v___x_1140_, 2);
v_auxDeclNGen_1144_ = lean_ctor_get(v___x_1140_, 3);
v_traceState_1145_ = lean_ctor_get(v___x_1140_, 4);
v_recordedDeps_1146_ = lean_ctor_get(v___x_1140_, 6);
v_messages_1147_ = lean_ctor_get(v___x_1140_, 7);
v_infoState_1148_ = lean_ctor_get(v___x_1140_, 8);
v_snapshotTasks_1149_ = lean_ctor_get(v___x_1140_, 9);
v_isSharedCheck_1160_ = !lean_is_exclusive(v___x_1140_);
if (v_isSharedCheck_1160_ == 0)
{
lean_object* v_unused_1161_; 
v_unused_1161_ = lean_ctor_get(v___x_1140_, 5);
lean_dec(v_unused_1161_);
v___x_1151_ = v___x_1140_;
v_isShared_1152_ = v_isSharedCheck_1160_;
goto v_resetjp_1150_;
}
else
{
lean_inc(v_snapshotTasks_1149_);
lean_inc(v_infoState_1148_);
lean_inc(v_messages_1147_);
lean_inc(v_recordedDeps_1146_);
lean_inc(v_traceState_1145_);
lean_inc(v_auxDeclNGen_1144_);
lean_inc(v_ngen_1143_);
lean_inc(v_nextMacroScope_1142_);
lean_inc(v_env_1141_);
lean_dec(v___x_1140_);
v___x_1151_ = lean_box(0);
v_isShared_1152_ = v_isSharedCheck_1160_;
goto v_resetjp_1150_;
}
v_resetjp_1150_:
{
lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1156_; 
v___x_1153_ = lean_box(0);
v___x_1154_ = l_Lean_Environment_setExporting(v_env_1141_, v_isExporting_1136_);
if (v_isShared_1152_ == 0)
{
lean_ctor_set(v___x_1151_, 5, v___x_1137_);
lean_ctor_set(v___x_1151_, 0, v___x_1154_);
v___x_1156_ = v___x_1151_;
goto v_reusejp_1155_;
}
else
{
lean_object* v_reuseFailAlloc_1159_; 
v_reuseFailAlloc_1159_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1159_, 0, v___x_1154_);
lean_ctor_set(v_reuseFailAlloc_1159_, 1, v_nextMacroScope_1142_);
lean_ctor_set(v_reuseFailAlloc_1159_, 2, v_ngen_1143_);
lean_ctor_set(v_reuseFailAlloc_1159_, 3, v_auxDeclNGen_1144_);
lean_ctor_set(v_reuseFailAlloc_1159_, 4, v_traceState_1145_);
lean_ctor_set(v_reuseFailAlloc_1159_, 5, v___x_1137_);
lean_ctor_set(v_reuseFailAlloc_1159_, 6, v_recordedDeps_1146_);
lean_ctor_set(v_reuseFailAlloc_1159_, 7, v_messages_1147_);
lean_ctor_set(v_reuseFailAlloc_1159_, 8, v_infoState_1148_);
lean_ctor_set(v_reuseFailAlloc_1159_, 9, v_snapshotTasks_1149_);
v___x_1156_ = v_reuseFailAlloc_1159_;
goto v_reusejp_1155_;
}
v_reusejp_1155_:
{
lean_object* v___x_1157_; lean_object* v___x_1158_; 
v___x_1157_ = lean_st_ref_put(v___y_1135_, v___x_1156_);
v___x_1158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1158_, 0, v___x_1153_);
return v___x_1158_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___lam__0___boxed(lean_object* v___y_1162_, lean_object* v_isExporting_1163_, lean_object* v___x_1164_, lean_object* v_a_x3f_1165_, lean_object* v___y_1166_){
_start:
{
uint8_t v_isExporting_boxed_1167_; lean_object* v_res_1168_; 
v_isExporting_boxed_1167_ = lean_unbox(v_isExporting_1163_);
v_res_1168_ = l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___lam__0(v___y_1162_, v_isExporting_boxed_1167_, v___x_1164_, v_a_x3f_1165_);
lean_dec(v_a_x3f_1165_);
lean_dec(v___y_1162_);
return v_res_1168_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_1169_; lean_object* v___x_1170_; 
v___x_1169_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__0);
v___x_1170_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1170_, 0, v___x_1169_);
return v___x_1170_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_1171_; lean_object* v___x_1172_; 
v___x_1171_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__0, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__0);
v___x_1172_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1172_, 0, v___x_1171_);
lean_ctor_set(v___x_1172_, 1, v___x_1171_);
return v___x_1172_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg(lean_object* v_x_1173_, uint8_t v_isExporting_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_){
_start:
{
lean_object* v___x_1178_; lean_object* v_env_1179_; lean_object* v___x_1180_; uint8_t v_isModule_1181_; 
v___x_1178_ = lean_st_ref_get(v___y_1176_);
v_env_1179_ = lean_ctor_get(v___x_1178_, 0);
lean_inc_ref(v_env_1179_);
lean_dec(v___x_1178_);
v___x_1180_ = l_Lean_Environment_header(v_env_1179_);
v_isModule_1181_ = lean_ctor_get_uint8(v___x_1180_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_1180_);
if (v_isModule_1181_ == 0)
{
lean_object* v___x_1182_; 
lean_dec_ref(v_env_1179_);
lean_inc(v___y_1176_);
lean_inc_ref(v___y_1175_);
v___x_1182_ = lean_apply_3(v_x_1173_, v___y_1175_, v___y_1176_, lean_box(0));
return v___x_1182_;
}
else
{
uint8_t v_isExporting_1183_; 
v_isExporting_1183_ = lean_ctor_get_uint8(v_env_1179_, sizeof(void*)*8);
lean_dec_ref(v_env_1179_);
if (v_isExporting_1174_ == 0)
{
if (v_isExporting_1183_ == 0)
{
lean_object* v___x_1235_; 
lean_inc(v___y_1176_);
lean_inc_ref(v___y_1175_);
v___x_1235_ = lean_apply_3(v_x_1173_, v___y_1175_, v___y_1176_, lean_box(0));
return v___x_1235_;
}
else
{
goto v___jp_1184_;
}
}
else
{
if (v_isExporting_1183_ == 0)
{
goto v___jp_1184_;
}
else
{
lean_object* v___x_1236_; 
lean_inc(v___y_1176_);
lean_inc_ref(v___y_1175_);
v___x_1236_ = lean_apply_3(v_x_1173_, v___y_1175_, v___y_1176_, lean_box(0));
return v___x_1236_;
}
}
v___jp_1184_:
{
lean_object* v___x_1185_; lean_object* v_env_1186_; lean_object* v_nextMacroScope_1187_; lean_object* v_ngen_1188_; lean_object* v_auxDeclNGen_1189_; lean_object* v_traceState_1190_; lean_object* v_recordedDeps_1191_; lean_object* v_messages_1192_; lean_object* v_infoState_1193_; lean_object* v_snapshotTasks_1194_; lean_object* v___x_1196_; uint8_t v_isShared_1197_; uint8_t v_isSharedCheck_1233_; 
v___x_1185_ = lean_st_ref_take(v___y_1176_);
v_env_1186_ = lean_ctor_get(v___x_1185_, 0);
v_nextMacroScope_1187_ = lean_ctor_get(v___x_1185_, 1);
v_ngen_1188_ = lean_ctor_get(v___x_1185_, 2);
v_auxDeclNGen_1189_ = lean_ctor_get(v___x_1185_, 3);
v_traceState_1190_ = lean_ctor_get(v___x_1185_, 4);
v_recordedDeps_1191_ = lean_ctor_get(v___x_1185_, 6);
v_messages_1192_ = lean_ctor_get(v___x_1185_, 7);
v_infoState_1193_ = lean_ctor_get(v___x_1185_, 8);
v_snapshotTasks_1194_ = lean_ctor_get(v___x_1185_, 9);
v_isSharedCheck_1233_ = !lean_is_exclusive(v___x_1185_);
if (v_isSharedCheck_1233_ == 0)
{
lean_object* v_unused_1234_; 
v_unused_1234_ = lean_ctor_get(v___x_1185_, 5);
lean_dec(v_unused_1234_);
v___x_1196_ = v___x_1185_;
v_isShared_1197_ = v_isSharedCheck_1233_;
goto v_resetjp_1195_;
}
else
{
lean_inc(v_snapshotTasks_1194_);
lean_inc(v_infoState_1193_);
lean_inc(v_messages_1192_);
lean_inc(v_recordedDeps_1191_);
lean_inc(v_traceState_1190_);
lean_inc(v_auxDeclNGen_1189_);
lean_inc(v_ngen_1188_);
lean_inc(v_nextMacroScope_1187_);
lean_inc(v_env_1186_);
lean_dec(v___x_1185_);
v___x_1196_ = lean_box(0);
v_isShared_1197_ = v_isSharedCheck_1233_;
goto v_resetjp_1195_;
}
v_resetjp_1195_:
{
lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1201_; 
v___x_1198_ = l_Lean_Environment_setExporting(v_env_1186_, v_isExporting_1174_);
v___x_1199_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1);
if (v_isShared_1197_ == 0)
{
lean_ctor_set(v___x_1196_, 5, v___x_1199_);
lean_ctor_set(v___x_1196_, 0, v___x_1198_);
v___x_1201_ = v___x_1196_;
goto v_reusejp_1200_;
}
else
{
lean_object* v_reuseFailAlloc_1232_; 
v_reuseFailAlloc_1232_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1232_, 0, v___x_1198_);
lean_ctor_set(v_reuseFailAlloc_1232_, 1, v_nextMacroScope_1187_);
lean_ctor_set(v_reuseFailAlloc_1232_, 2, v_ngen_1188_);
lean_ctor_set(v_reuseFailAlloc_1232_, 3, v_auxDeclNGen_1189_);
lean_ctor_set(v_reuseFailAlloc_1232_, 4, v_traceState_1190_);
lean_ctor_set(v_reuseFailAlloc_1232_, 5, v___x_1199_);
lean_ctor_set(v_reuseFailAlloc_1232_, 6, v_recordedDeps_1191_);
lean_ctor_set(v_reuseFailAlloc_1232_, 7, v_messages_1192_);
lean_ctor_set(v_reuseFailAlloc_1232_, 8, v_infoState_1193_);
lean_ctor_set(v_reuseFailAlloc_1232_, 9, v_snapshotTasks_1194_);
v___x_1201_ = v_reuseFailAlloc_1232_;
goto v_reusejp_1200_;
}
v_reusejp_1200_:
{
lean_object* v___x_1202_; lean_object* v_r_1203_; 
v___x_1202_ = lean_st_ref_put(v___y_1176_, v___x_1201_);
lean_inc(v___y_1176_);
lean_inc_ref(v___y_1175_);
v_r_1203_ = lean_apply_3(v_x_1173_, v___y_1175_, v___y_1176_, lean_box(0));
if (lean_obj_tag(v_r_1203_) == 0)
{
lean_object* v_a_1204_; lean_object* v___x_1206_; uint8_t v_isShared_1207_; uint8_t v_isSharedCheck_1220_; 
v_a_1204_ = lean_ctor_get(v_r_1203_, 0);
v_isSharedCheck_1220_ = !lean_is_exclusive(v_r_1203_);
if (v_isSharedCheck_1220_ == 0)
{
v___x_1206_ = v_r_1203_;
v_isShared_1207_ = v_isSharedCheck_1220_;
goto v_resetjp_1205_;
}
else
{
lean_inc(v_a_1204_);
lean_dec(v_r_1203_);
v___x_1206_ = lean_box(0);
v_isShared_1207_ = v_isSharedCheck_1220_;
goto v_resetjp_1205_;
}
v_resetjp_1205_:
{
lean_object* v___x_1209_; 
lean_inc(v_a_1204_);
if (v_isShared_1207_ == 0)
{
lean_ctor_set_tag(v___x_1206_, 1);
v___x_1209_ = v___x_1206_;
goto v_reusejp_1208_;
}
else
{
lean_object* v_reuseFailAlloc_1219_; 
v_reuseFailAlloc_1219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1219_, 0, v_a_1204_);
v___x_1209_ = v_reuseFailAlloc_1219_;
goto v_reusejp_1208_;
}
v_reusejp_1208_:
{
lean_object* v___x_1210_; lean_object* v___x_1212_; uint8_t v_isShared_1213_; uint8_t v_isSharedCheck_1217_; 
v___x_1210_ = l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___lam__0(v___y_1176_, v_isExporting_1183_, v___x_1199_, v___x_1209_);
lean_dec_ref(v___x_1209_);
v_isSharedCheck_1217_ = !lean_is_exclusive(v___x_1210_);
if (v_isSharedCheck_1217_ == 0)
{
lean_object* v_unused_1218_; 
v_unused_1218_ = lean_ctor_get(v___x_1210_, 0);
lean_dec(v_unused_1218_);
v___x_1212_ = v___x_1210_;
v_isShared_1213_ = v_isSharedCheck_1217_;
goto v_resetjp_1211_;
}
else
{
lean_dec(v___x_1210_);
v___x_1212_ = lean_box(0);
v_isShared_1213_ = v_isSharedCheck_1217_;
goto v_resetjp_1211_;
}
v_resetjp_1211_:
{
lean_object* v___x_1215_; 
if (v_isShared_1213_ == 0)
{
lean_ctor_set(v___x_1212_, 0, v_a_1204_);
v___x_1215_ = v___x_1212_;
goto v_reusejp_1214_;
}
else
{
lean_object* v_reuseFailAlloc_1216_; 
v_reuseFailAlloc_1216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1216_, 0, v_a_1204_);
v___x_1215_ = v_reuseFailAlloc_1216_;
goto v_reusejp_1214_;
}
v_reusejp_1214_:
{
return v___x_1215_;
}
}
}
}
}
else
{
lean_object* v_a_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1225_; uint8_t v_isShared_1226_; uint8_t v_isSharedCheck_1230_; 
v_a_1221_ = lean_ctor_get(v_r_1203_, 0);
lean_inc(v_a_1221_);
lean_dec_ref_known(v_r_1203_, 1);
v___x_1222_ = lean_box(0);
v___x_1223_ = l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___lam__0(v___y_1176_, v_isExporting_1183_, v___x_1199_, v___x_1222_);
v_isSharedCheck_1230_ = !lean_is_exclusive(v___x_1223_);
if (v_isSharedCheck_1230_ == 0)
{
lean_object* v_unused_1231_; 
v_unused_1231_ = lean_ctor_get(v___x_1223_, 0);
lean_dec(v_unused_1231_);
v___x_1225_ = v___x_1223_;
v_isShared_1226_ = v_isSharedCheck_1230_;
goto v_resetjp_1224_;
}
else
{
lean_dec(v___x_1223_);
v___x_1225_ = lean_box(0);
v_isShared_1226_ = v_isSharedCheck_1230_;
goto v_resetjp_1224_;
}
v_resetjp_1224_:
{
lean_object* v___x_1228_; 
if (v_isShared_1226_ == 0)
{
lean_ctor_set_tag(v___x_1225_, 1);
lean_ctor_set(v___x_1225_, 0, v_a_1221_);
v___x_1228_ = v___x_1225_;
goto v_reusejp_1227_;
}
else
{
lean_object* v_reuseFailAlloc_1229_; 
v_reuseFailAlloc_1229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1229_, 0, v_a_1221_);
v___x_1228_ = v_reuseFailAlloc_1229_;
goto v_reusejp_1227_;
}
v_reusejp_1227_:
{
return v___x_1228_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___boxed(lean_object* v_x_1237_, lean_object* v_isExporting_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_){
_start:
{
uint8_t v_isExporting_boxed_1242_; lean_object* v_res_1243_; 
v_isExporting_boxed_1242_ = lean_unbox(v_isExporting_1238_);
v_res_1243_ = l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg(v_x_1237_, v_isExporting_boxed_1242_, v___y_1239_, v___y_1240_);
lean_dec(v___y_1240_);
lean_dec_ref(v___y_1239_);
return v_res_1243_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2(lean_object* v_00_u03b1_1244_, lean_object* v_x_1245_, uint8_t v_isExporting_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_){
_start:
{
lean_object* v___x_1250_; 
v___x_1250_ = l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg(v_x_1245_, v_isExporting_1246_, v___y_1247_, v___y_1248_);
return v___x_1250_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___boxed(lean_object* v_00_u03b1_1251_, lean_object* v_x_1252_, lean_object* v_isExporting_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_){
_start:
{
uint8_t v_isExporting_boxed_1257_; lean_object* v_res_1258_; 
v_isExporting_boxed_1257_ = lean_unbox(v_isExporting_1253_);
v_res_1258_ = l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2(v_00_u03b1_1251_, v_x_1252_, v_isExporting_boxed_1257_, v___y_1254_, v___y_1255_);
lean_dec(v___y_1255_);
lean_dec_ref(v___y_1254_);
return v_res_1258_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0_spec__3(lean_object* v_opts_1259_, lean_object* v_opt_1260_){
_start:
{
lean_object* v_name_1261_; lean_object* v_defValue_1262_; lean_object* v_map_1263_; lean_object* v___x_1264_; 
v_name_1261_ = lean_ctor_get(v_opt_1260_, 0);
v_defValue_1262_ = lean_ctor_get(v_opt_1260_, 1);
v_map_1263_ = lean_ctor_get(v_opts_1259_, 0);
v___x_1264_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1263_, v_name_1261_);
if (lean_obj_tag(v___x_1264_) == 0)
{
uint8_t v___x_1265_; 
v___x_1265_ = lean_unbox(v_defValue_1262_);
return v___x_1265_;
}
else
{
lean_object* v_val_1266_; 
v_val_1266_ = lean_ctor_get(v___x_1264_, 0);
lean_inc(v_val_1266_);
lean_dec_ref_known(v___x_1264_, 1);
if (lean_obj_tag(v_val_1266_) == 1)
{
uint8_t v_v_1267_; 
v_v_1267_ = lean_ctor_get_uint8(v_val_1266_, 0);
lean_dec_ref_known(v_val_1266_, 0);
return v_v_1267_;
}
else
{
uint8_t v___x_1268_; 
lean_dec(v_val_1266_);
v___x_1268_ = lean_unbox(v_defValue_1262_);
return v___x_1268_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0_spec__3___boxed(lean_object* v_opts_1269_, lean_object* v_opt_1270_){
_start:
{
uint8_t v_res_1271_; lean_object* v_r_1272_; 
v_res_1271_ = l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0_spec__3(v_opts_1269_, v_opt_1270_);
lean_dec_ref(v_opt_1270_);
lean_dec_ref(v_opts_1269_);
v_r_1272_ = lean_box(v_res_1271_);
return v_r_1272_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0(uint8_t v_suppressElabErrors_1280_, uint8_t v___y_1281_, lean_object* v_x_1282_){
_start:
{
if (lean_obj_tag(v_x_1282_) == 1)
{
lean_object* v_pre_1283_; 
v_pre_1283_ = lean_ctor_get(v_x_1282_, 0);
switch(lean_obj_tag(v_pre_1283_))
{
case 1:
{
lean_object* v_pre_1284_; 
v_pre_1284_ = lean_ctor_get(v_pre_1283_, 0);
switch(lean_obj_tag(v_pre_1284_))
{
case 0:
{
lean_object* v_str_1285_; lean_object* v_str_1286_; lean_object* v___x_1287_; uint8_t v___x_1288_; 
v_str_1285_ = lean_ctor_get(v_x_1282_, 1);
v_str_1286_ = lean_ctor_get(v_pre_1283_, 1);
v___x_1287_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__0));
v___x_1288_ = lean_string_dec_eq(v_str_1286_, v___x_1287_);
if (v___x_1288_ == 0)
{
lean_object* v___x_1289_; uint8_t v___x_1290_; 
v___x_1289_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__2));
v___x_1290_ = lean_string_dec_eq(v_str_1286_, v___x_1289_);
if (v___x_1290_ == 0)
{
return v___x_1290_;
}
else
{
lean_object* v___x_1291_; uint8_t v___x_1292_; 
v___x_1291_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__1));
v___x_1292_ = lean_string_dec_eq(v_str_1285_, v___x_1291_);
if (v___x_1292_ == 0)
{
return v___x_1292_;
}
else
{
return v_suppressElabErrors_1280_;
}
}
}
else
{
lean_object* v___x_1293_; uint8_t v___x_1294_; 
v___x_1293_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__2));
v___x_1294_ = lean_string_dec_eq(v_str_1285_, v___x_1293_);
if (v___x_1294_ == 0)
{
return v___x_1294_;
}
else
{
return v_suppressElabErrors_1280_;
}
}
}
case 1:
{
lean_object* v_pre_1295_; 
v_pre_1295_ = lean_ctor_get(v_pre_1284_, 0);
if (lean_obj_tag(v_pre_1295_) == 0)
{
lean_object* v_str_1296_; lean_object* v_str_1297_; lean_object* v_str_1298_; lean_object* v___x_1299_; uint8_t v___x_1300_; 
v_str_1296_ = lean_ctor_get(v_x_1282_, 1);
v_str_1297_ = lean_ctor_get(v_pre_1283_, 1);
v_str_1298_ = lean_ctor_get(v_pre_1284_, 1);
v___x_1299_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__3));
v___x_1300_ = lean_string_dec_eq(v_str_1298_, v___x_1299_);
if (v___x_1300_ == 0)
{
return v___x_1300_;
}
else
{
lean_object* v___x_1301_; uint8_t v___x_1302_; 
v___x_1301_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__4));
v___x_1302_ = lean_string_dec_eq(v_str_1297_, v___x_1301_);
if (v___x_1302_ == 0)
{
return v___x_1302_;
}
else
{
lean_object* v___x_1303_; uint8_t v___x_1304_; 
v___x_1303_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__5));
v___x_1304_ = lean_string_dec_eq(v_str_1296_, v___x_1303_);
if (v___x_1304_ == 0)
{
return v___x_1304_;
}
else
{
return v_suppressElabErrors_1280_;
}
}
}
}
else
{
return v___y_1281_;
}
}
default: 
{
return v___y_1281_;
}
}
}
case 0:
{
lean_object* v_str_1305_; lean_object* v___x_1306_; uint8_t v___x_1307_; 
v_str_1305_ = lean_ctor_get(v_x_1282_, 1);
v___x_1306_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__6));
v___x_1307_ = lean_string_dec_eq(v_str_1305_, v___x_1306_);
if (v___x_1307_ == 0)
{
return v___x_1307_;
}
else
{
return v_suppressElabErrors_1280_;
}
}
default: 
{
return v___y_1281_;
}
}
}
else
{
return v___y_1281_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___boxed(lean_object* v_suppressElabErrors_1308_, lean_object* v___y_1309_, lean_object* v_x_1310_){
_start:
{
uint8_t v_suppressElabErrors_boxed_1311_; uint8_t v___y_5082__boxed_1312_; uint8_t v_res_1313_; lean_object* v_r_1314_; 
v_suppressElabErrors_boxed_1311_ = lean_unbox(v_suppressElabErrors_1308_);
v___y_5082__boxed_1312_ = lean_unbox(v___y_1309_);
v_res_1313_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0(v_suppressElabErrors_boxed_1311_, v___y_5082__boxed_1312_, v_x_1310_);
lean_dec(v_x_1310_);
v_r_1314_ = lean_box(v_res_1313_);
return v_r_1314_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6(lean_object* v_ref_1315_, lean_object* v_msgData_1316_, uint8_t v_severity_1317_, uint8_t v_isSilent_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_){
_start:
{
lean_object* v___y_1323_; uint8_t v___y_1324_; lean_object* v___y_1325_; uint8_t v___y_1326_; lean_object* v___y_1327_; lean_object* v___y_1328_; lean_object* v___y_1329_; lean_object* v_toCold_1330_; lean_object* v___y_1331_; lean_object* v___y_1360_; lean_object* v___y_1361_; uint8_t v___y_1362_; lean_object* v___y_1363_; lean_object* v___y_1364_; uint8_t v___y_1365_; uint8_t v___y_1366_; lean_object* v___y_1367_; lean_object* v___y_1387_; lean_object* v___y_1388_; uint8_t v___y_1389_; uint8_t v___y_1390_; lean_object* v___y_1391_; uint8_t v___y_1392_; lean_object* v___y_1393_; uint8_t v___y_1397_; uint8_t v___y_1398_; uint8_t v___y_1399_; uint8_t v___x_1410_; uint8_t v___y_1412_; uint8_t v___y_1413_; uint8_t v___y_1414_; uint8_t v___y_1416_; uint8_t v___x_1424_; 
v___x_1410_ = 2;
v___x_1424_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1317_, v___x_1410_);
if (v___x_1424_ == 0)
{
v___y_1416_ = v___x_1424_;
goto v___jp_1415_;
}
else
{
uint8_t v___x_1425_; 
lean_inc_ref(v_msgData_1316_);
v___x_1425_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_1316_);
v___y_1416_ = v___x_1425_;
goto v___jp_1415_;
}
v___jp_1322_:
{
lean_object* v_currNamespace_1332_; lean_object* v_openDecls_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v_env_1338_; lean_object* v_nextMacroScope_1339_; lean_object* v_ngen_1340_; lean_object* v_auxDeclNGen_1341_; lean_object* v_traceState_1342_; lean_object* v_cache_1343_; lean_object* v_recordedDeps_1344_; lean_object* v_messages_1345_; lean_object* v_infoState_1346_; lean_object* v_snapshotTasks_1347_; lean_object* v___x_1349_; uint8_t v_isShared_1350_; uint8_t v_isSharedCheck_1358_; 
v_currNamespace_1332_ = lean_ctor_get(v_toCold_1330_, 4);
v_openDecls_1333_ = lean_ctor_get(v_toCold_1330_, 5);
lean_inc(v_openDecls_1333_);
lean_inc(v_currNamespace_1332_);
v___x_1334_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1334_, 0, v_currNamespace_1332_);
lean_ctor_set(v___x_1334_, 1, v_openDecls_1333_);
v___x_1335_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1335_, 0, v___x_1334_);
lean_ctor_set(v___x_1335_, 1, v___y_1327_);
lean_inc_ref(v___y_1323_);
lean_inc_ref(v___y_1328_);
v___x_1336_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1336_, 0, v___y_1328_);
lean_ctor_set(v___x_1336_, 1, v___y_1325_);
lean_ctor_set(v___x_1336_, 2, v___y_1329_);
lean_ctor_set(v___x_1336_, 3, v___y_1323_);
lean_ctor_set(v___x_1336_, 4, v___x_1335_);
lean_ctor_set_uint8(v___x_1336_, sizeof(void*)*5, v___y_1324_);
lean_ctor_set_uint8(v___x_1336_, sizeof(void*)*5 + 1, v___y_1326_);
lean_ctor_set_uint8(v___x_1336_, sizeof(void*)*5 + 2, v_isSilent_1318_);
v___x_1337_ = lean_st_ref_take(v___y_1331_);
v_env_1338_ = lean_ctor_get(v___x_1337_, 0);
v_nextMacroScope_1339_ = lean_ctor_get(v___x_1337_, 1);
v_ngen_1340_ = lean_ctor_get(v___x_1337_, 2);
v_auxDeclNGen_1341_ = lean_ctor_get(v___x_1337_, 3);
v_traceState_1342_ = lean_ctor_get(v___x_1337_, 4);
v_cache_1343_ = lean_ctor_get(v___x_1337_, 5);
v_recordedDeps_1344_ = lean_ctor_get(v___x_1337_, 6);
v_messages_1345_ = lean_ctor_get(v___x_1337_, 7);
v_infoState_1346_ = lean_ctor_get(v___x_1337_, 8);
v_snapshotTasks_1347_ = lean_ctor_get(v___x_1337_, 9);
v_isSharedCheck_1358_ = !lean_is_exclusive(v___x_1337_);
if (v_isSharedCheck_1358_ == 0)
{
v___x_1349_ = v___x_1337_;
v_isShared_1350_ = v_isSharedCheck_1358_;
goto v_resetjp_1348_;
}
else
{
lean_inc(v_snapshotTasks_1347_);
lean_inc(v_infoState_1346_);
lean_inc(v_messages_1345_);
lean_inc(v_recordedDeps_1344_);
lean_inc(v_cache_1343_);
lean_inc(v_traceState_1342_);
lean_inc(v_auxDeclNGen_1341_);
lean_inc(v_ngen_1340_);
lean_inc(v_nextMacroScope_1339_);
lean_inc(v_env_1338_);
lean_dec(v___x_1337_);
v___x_1349_ = lean_box(0);
v_isShared_1350_ = v_isSharedCheck_1358_;
goto v_resetjp_1348_;
}
v_resetjp_1348_:
{
lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1354_; 
v___x_1351_ = lean_box(0);
v___x_1352_ = l_Lean_MessageLog_add(v___x_1336_, v_messages_1345_);
if (v_isShared_1350_ == 0)
{
lean_ctor_set(v___x_1349_, 7, v___x_1352_);
v___x_1354_ = v___x_1349_;
goto v_reusejp_1353_;
}
else
{
lean_object* v_reuseFailAlloc_1357_; 
v_reuseFailAlloc_1357_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1357_, 0, v_env_1338_);
lean_ctor_set(v_reuseFailAlloc_1357_, 1, v_nextMacroScope_1339_);
lean_ctor_set(v_reuseFailAlloc_1357_, 2, v_ngen_1340_);
lean_ctor_set(v_reuseFailAlloc_1357_, 3, v_auxDeclNGen_1341_);
lean_ctor_set(v_reuseFailAlloc_1357_, 4, v_traceState_1342_);
lean_ctor_set(v_reuseFailAlloc_1357_, 5, v_cache_1343_);
lean_ctor_set(v_reuseFailAlloc_1357_, 6, v_recordedDeps_1344_);
lean_ctor_set(v_reuseFailAlloc_1357_, 7, v___x_1352_);
lean_ctor_set(v_reuseFailAlloc_1357_, 8, v_infoState_1346_);
lean_ctor_set(v_reuseFailAlloc_1357_, 9, v_snapshotTasks_1347_);
v___x_1354_ = v_reuseFailAlloc_1357_;
goto v_reusejp_1353_;
}
v_reusejp_1353_:
{
lean_object* v___x_1355_; lean_object* v___x_1356_; 
v___x_1355_ = lean_st_ref_put(v___y_1331_, v___x_1354_);
v___x_1356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1356_, 0, v___x_1351_);
return v___x_1356_;
}
}
}
v___jp_1359_:
{
lean_object* v_fileName_1368_; lean_object* v_fileMap_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v_a_1372_; lean_object* v___x_1374_; uint8_t v_isShared_1375_; uint8_t v_isSharedCheck_1385_; 
v_fileName_1368_ = lean_ctor_get(v___y_1363_, 0);
v_fileMap_1369_ = lean_ctor_get(v___y_1363_, 1);
v___x_1370_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_1316_);
v___x_1371_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0(v___x_1370_, v___y_1319_, v___y_1320_);
v_a_1372_ = lean_ctor_get(v___x_1371_, 0);
v_isSharedCheck_1385_ = !lean_is_exclusive(v___x_1371_);
if (v_isSharedCheck_1385_ == 0)
{
v___x_1374_ = v___x_1371_;
v_isShared_1375_ = v_isSharedCheck_1385_;
goto v_resetjp_1373_;
}
else
{
lean_inc(v_a_1372_);
lean_dec(v___x_1371_);
v___x_1374_ = lean_box(0);
v_isShared_1375_ = v_isSharedCheck_1385_;
goto v_resetjp_1373_;
}
v_resetjp_1373_:
{
lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; 
lean_inc_ref_n(v_fileMap_1369_, 2);
v___x_1376_ = l_Lean_FileMap_toPosition(v_fileMap_1369_, v___y_1364_);
lean_dec(v___y_1364_);
v___x_1377_ = l_Lean_FileMap_toPosition(v_fileMap_1369_, v___y_1367_);
lean_dec(v___y_1367_);
v___x_1378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1378_, 0, v___x_1377_);
v___x_1379_ = ((lean_object*)(l_Lean_instInhabitedAttributeImplCore_default___closed__3));
if (v___y_1366_ == 0)
{
lean_del_object(v___x_1374_);
lean_dec_ref(v___y_1361_);
v___y_1323_ = v___x_1379_;
v___y_1324_ = v___y_1362_;
v___y_1325_ = v___x_1376_;
v___y_1326_ = v___y_1365_;
v___y_1327_ = v_a_1372_;
v___y_1328_ = v_fileName_1368_;
v___y_1329_ = v___x_1378_;
v_toCold_1330_ = v___y_1360_;
v___y_1331_ = v___y_1320_;
goto v___jp_1322_;
}
else
{
uint8_t v___x_1380_; 
lean_inc(v_a_1372_);
v___x_1380_ = l_Lean_MessageData_hasTag(v___y_1361_, v_a_1372_);
if (v___x_1380_ == 0)
{
lean_object* v___x_1381_; lean_object* v___x_1383_; 
lean_dec_ref_known(v___x_1378_, 1);
lean_dec_ref(v___x_1376_);
lean_dec(v_a_1372_);
v___x_1381_ = lean_box(0);
if (v_isShared_1375_ == 0)
{
lean_ctor_set(v___x_1374_, 0, v___x_1381_);
v___x_1383_ = v___x_1374_;
goto v_reusejp_1382_;
}
else
{
lean_object* v_reuseFailAlloc_1384_; 
v_reuseFailAlloc_1384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1384_, 0, v___x_1381_);
v___x_1383_ = v_reuseFailAlloc_1384_;
goto v_reusejp_1382_;
}
v_reusejp_1382_:
{
return v___x_1383_;
}
}
else
{
lean_del_object(v___x_1374_);
v___y_1323_ = v___x_1379_;
v___y_1324_ = v___y_1362_;
v___y_1325_ = v___x_1376_;
v___y_1326_ = v___y_1365_;
v___y_1327_ = v_a_1372_;
v___y_1328_ = v_fileName_1368_;
v___y_1329_ = v___x_1378_;
v_toCold_1330_ = v___y_1360_;
v___y_1331_ = v___y_1320_;
goto v___jp_1322_;
}
}
}
}
v___jp_1386_:
{
lean_object* v___x_1394_; 
v___x_1394_ = l_Lean_Syntax_getTailPos_x3f(v___y_1391_, v___y_1390_);
lean_dec(v___y_1391_);
if (lean_obj_tag(v___x_1394_) == 0)
{
lean_inc(v___y_1393_);
v___y_1360_ = v___y_1387_;
v___y_1361_ = v___y_1388_;
v___y_1362_ = v___y_1390_;
v___y_1363_ = v___y_1387_;
v___y_1364_ = v___y_1393_;
v___y_1365_ = v___y_1392_;
v___y_1366_ = v___y_1389_;
v___y_1367_ = v___y_1393_;
goto v___jp_1359_;
}
else
{
lean_object* v_val_1395_; 
v_val_1395_ = lean_ctor_get(v___x_1394_, 0);
lean_inc(v_val_1395_);
lean_dec_ref_known(v___x_1394_, 1);
v___y_1360_ = v___y_1387_;
v___y_1361_ = v___y_1388_;
v___y_1362_ = v___y_1390_;
v___y_1363_ = v___y_1387_;
v___y_1364_ = v___y_1393_;
v___y_1365_ = v___y_1392_;
v___y_1366_ = v___y_1389_;
v___y_1367_ = v_val_1395_;
goto v___jp_1359_;
}
}
v___jp_1396_:
{
lean_object* v_toCold_1400_; lean_object* v_ref_1401_; uint8_t v_suppressElabErrors_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___f_1405_; lean_object* v_ref_1406_; lean_object* v___x_1407_; 
v_toCold_1400_ = lean_ctor_get(v___y_1319_, 0);
v_ref_1401_ = lean_ctor_get(v___y_1319_, 2);
v_suppressElabErrors_1402_ = lean_ctor_get_uint8(v___y_1319_, sizeof(void*)*3 + 2);
v___x_1403_ = lean_box(v_suppressElabErrors_1402_);
v___x_1404_ = lean_box(v___y_1397_);
v___f_1405_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1405_, 0, v___x_1403_);
lean_closure_set(v___f_1405_, 1, v___x_1404_);
v_ref_1406_ = l_Lean_replaceRef(v_ref_1315_, v_ref_1401_);
v___x_1407_ = l_Lean_Syntax_getPos_x3f(v_ref_1406_, v___y_1398_);
if (lean_obj_tag(v___x_1407_) == 0)
{
lean_object* v___x_1408_; 
v___x_1408_ = lean_unsigned_to_nat(0u);
v___y_1387_ = v_toCold_1400_;
v___y_1388_ = v___f_1405_;
v___y_1389_ = v_suppressElabErrors_1402_;
v___y_1390_ = v___y_1398_;
v___y_1391_ = v_ref_1406_;
v___y_1392_ = v___y_1399_;
v___y_1393_ = v___x_1408_;
goto v___jp_1386_;
}
else
{
lean_object* v_val_1409_; 
v_val_1409_ = lean_ctor_get(v___x_1407_, 0);
lean_inc(v_val_1409_);
lean_dec_ref_known(v___x_1407_, 1);
v___y_1387_ = v_toCold_1400_;
v___y_1388_ = v___f_1405_;
v___y_1389_ = v_suppressElabErrors_1402_;
v___y_1390_ = v___y_1398_;
v___y_1391_ = v_ref_1406_;
v___y_1392_ = v___y_1399_;
v___y_1393_ = v_val_1409_;
goto v___jp_1386_;
}
}
v___jp_1411_:
{
if (v___y_1414_ == 0)
{
v___y_1397_ = v___y_1412_;
v___y_1398_ = v___y_1413_;
v___y_1399_ = v_severity_1317_;
goto v___jp_1396_;
}
else
{
v___y_1397_ = v___y_1412_;
v___y_1398_ = v___y_1413_;
v___y_1399_ = v___x_1410_;
goto v___jp_1396_;
}
}
v___jp_1415_:
{
if (v___y_1416_ == 0)
{
uint8_t v___x_1417_; uint8_t v___x_1418_; 
v___x_1417_ = 1;
v___x_1418_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1317_, v___x_1417_);
if (v___x_1418_ == 0)
{
v___y_1412_ = v___y_1416_;
v___y_1413_ = v___y_1416_;
v___y_1414_ = v___x_1418_;
goto v___jp_1411_;
}
else
{
lean_object* v___x_1419_; lean_object* v___x_1420_; uint8_t v___x_1421_; 
v___x_1419_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1319_);
v___x_1420_ = l_Lean_warningAsError;
v___x_1421_ = l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0_spec__3(v___x_1419_, v___x_1420_);
lean_dec_ref(v___x_1419_);
v___y_1412_ = v___y_1416_;
v___y_1413_ = v___y_1416_;
v___y_1414_ = v___x_1421_;
goto v___jp_1411_;
}
}
else
{
lean_object* v___x_1422_; lean_object* v___x_1423_; 
lean_dec_ref(v_msgData_1316_);
v___x_1422_ = lean_box(0);
v___x_1423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1423_, 0, v___x_1422_);
return v___x_1423_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___boxed(lean_object* v_ref_1426_, lean_object* v_msgData_1427_, lean_object* v_severity_1428_, lean_object* v_isSilent_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_){
_start:
{
uint8_t v_severity_boxed_1433_; uint8_t v_isSilent_boxed_1434_; lean_object* v_res_1435_; 
v_severity_boxed_1433_ = lean_unbox(v_severity_1428_);
v_isSilent_boxed_1434_ = lean_unbox(v_isSilent_1429_);
v_res_1435_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6(v_ref_1426_, v_msgData_1427_, v_severity_boxed_1433_, v_isSilent_boxed_1434_, v___y_1430_, v___y_1431_);
lean_dec(v___y_1431_);
lean_dec_ref(v___y_1430_);
lean_dec(v_ref_1426_);
return v_res_1435_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5(lean_object* v_msgData_1436_, uint8_t v_severity_1437_, uint8_t v_isSilent_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_){
_start:
{
lean_object* v_ref_1442_; lean_object* v___x_1443_; 
v_ref_1442_ = lean_ctor_get(v___y_1439_, 2);
v___x_1443_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6(v_ref_1442_, v_msgData_1436_, v_severity_1437_, v_isSilent_1438_, v___y_1439_, v___y_1440_);
return v___x_1443_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5___boxed(lean_object* v_msgData_1444_, lean_object* v_severity_1445_, lean_object* v_isSilent_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_){
_start:
{
uint8_t v_severity_boxed_1450_; uint8_t v_isSilent_boxed_1451_; lean_object* v_res_1452_; 
v_severity_boxed_1450_ = lean_unbox(v_severity_1445_);
v_isSilent_boxed_1451_ = lean_unbox(v_isSilent_1446_);
v_res_1452_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5(v_msgData_1444_, v_severity_boxed_1450_, v_isSilent_boxed_1451_, v___y_1447_, v___y_1448_);
lean_dec(v___y_1448_);
lean_dec_ref(v___y_1447_);
return v_res_1452_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1(lean_object* v_msgData_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_){
_start:
{
uint8_t v___x_1457_; uint8_t v___x_1458_; lean_object* v___x_1459_; 
v___x_1457_ = 1;
v___x_1458_ = 0;
v___x_1459_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5(v_msgData_1453_, v___x_1457_, v___x_1458_, v___y_1454_, v___y_1455_);
return v___x_1459_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1___boxed(lean_object* v_msgData_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_){
_start:
{
lean_object* v_res_1464_; 
v_res_1464_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1(v_msgData_1460_, v___y_1461_, v___y_1462_);
lean_dec(v___y_1462_);
lean_dec_ref(v___y_1461_);
return v_res_1464_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0___redArg(lean_object* v_opt_1465_, lean_object* v___y_1466_){
_start:
{
lean_object* v___x_1468_; uint8_t v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; 
v___x_1468_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1466_);
v___x_1469_ = l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0_spec__3(v___x_1468_, v_opt_1465_);
lean_dec_ref(v___x_1468_);
v___x_1470_ = lean_box(v___x_1469_);
v___x_1471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1471_, 0, v___x_1470_);
return v___x_1471_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0___redArg___boxed(lean_object* v_opt_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_){
_start:
{
lean_object* v_res_1475_; 
v_res_1475_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0___redArg(v_opt_1472_, v___y_1473_);
lean_dec_ref(v___y_1473_);
lean_dec_ref(v_opt_1472_);
return v_res_1475_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1477_; lean_object* v___x_1478_; 
v___x_1477_ = ((lean_object*)(l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__0));
v___x_1478_ = l_Lean_stringToMessageData(v___x_1477_);
return v___x_1478_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__3(void){
_start:
{
lean_object* v___x_1480_; lean_object* v___x_1481_; 
v___x_1480_ = ((lean_object*)(l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__2));
v___x_1481_ = l_Lean_stringToMessageData(v___x_1480_);
return v___x_1481_;
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0(lean_object* v_id_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_){
_start:
{
lean_object* v___x_1486_; lean_object* v_env_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v_a_1490_; lean_object* v___x_1492_; uint8_t v_isShared_1493_; uint8_t v_isSharedCheck_1509_; 
v___x_1486_ = lean_st_ref_get(v___y_1484_);
v_env_1487_ = lean_ctor_get(v___x_1486_, 0);
lean_inc_ref(v_env_1487_);
lean_dec(v___x_1486_);
v___x_1488_ = l_Lean_ResolveName_backward_privateInPublic_warn;
v___x_1489_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0___redArg(v___x_1488_, v___y_1483_);
v_a_1490_ = lean_ctor_get(v___x_1489_, 0);
v_isSharedCheck_1509_ = !lean_is_exclusive(v___x_1489_);
if (v_isSharedCheck_1509_ == 0)
{
v___x_1492_ = v___x_1489_;
v_isShared_1493_ = v_isSharedCheck_1509_;
goto v_resetjp_1491_;
}
else
{
lean_inc(v_a_1490_);
lean_dec(v___x_1489_);
v___x_1492_ = lean_box(0);
v_isShared_1493_ = v_isSharedCheck_1509_;
goto v_resetjp_1491_;
}
v_resetjp_1491_:
{
uint8_t v_isExporting_1499_; 
v_isExporting_1499_ = lean_ctor_get_uint8(v_env_1487_, sizeof(void*)*8);
lean_dec_ref(v_env_1487_);
if (v_isExporting_1499_ == 0)
{
lean_dec(v_a_1490_);
lean_dec(v_id_1482_);
goto v___jp_1494_;
}
else
{
uint8_t v___x_1500_; 
v___x_1500_ = l_Lean_isPrivateName(v_id_1482_);
if (v___x_1500_ == 0)
{
lean_dec(v_a_1490_);
lean_dec(v_id_1482_);
goto v___jp_1494_;
}
else
{
uint8_t v___x_1501_; 
v___x_1501_ = lean_unbox(v_a_1490_);
lean_dec(v_a_1490_);
if (v___x_1501_ == 0)
{
lean_dec(v_id_1482_);
goto v___jp_1494_;
}
else
{
lean_object* v___x_1502_; uint8_t v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; 
lean_del_object(v___x_1492_);
v___x_1502_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__1, &l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__1_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__1);
v___x_1503_ = 0;
v___x_1504_ = l_Lean_MessageData_ofConstName(v_id_1482_, v___x_1503_);
v___x_1505_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1505_, 0, v___x_1502_);
lean_ctor_set(v___x_1505_, 1, v___x_1504_);
v___x_1506_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__3, &l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__3_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__3);
v___x_1507_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1507_, 0, v___x_1505_);
lean_ctor_set(v___x_1507_, 1, v___x_1506_);
v___x_1508_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1(v___x_1507_, v___y_1483_, v___y_1484_);
return v___x_1508_;
}
}
}
v___jp_1494_:
{
lean_object* v___x_1495_; lean_object* v___x_1497_; 
v___x_1495_ = lean_box(0);
if (v_isShared_1493_ == 0)
{
lean_ctor_set(v___x_1492_, 0, v___x_1495_);
v___x_1497_ = v___x_1492_;
goto v_reusejp_1496_;
}
else
{
lean_object* v_reuseFailAlloc_1498_; 
v_reuseFailAlloc_1498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1498_, 0, v___x_1495_);
v___x_1497_ = v_reuseFailAlloc_1498_;
goto v_reusejp_1496_;
}
v_reusejp_1496_:
{
return v___x_1497_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___boxed(lean_object* v_id_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_){
_start:
{
lean_object* v_res_1514_; 
v_res_1514_ = l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0(v_id_1510_, v___y_1511_, v___y_1512_);
lean_dec(v___y_1512_);
lean_dec_ref(v___y_1511_);
return v_res_1514_;
}
}
static lean_object* _init_l_Lean_ensureAttrDeclIsPublic___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1516_; lean_object* v___x_1517_; 
v___x_1516_ = ((lean_object*)(l_Lean_ensureAttrDeclIsPublic___lam__0___closed__0));
v___x_1517_ = l_Lean_stringToMessageData(v___x_1516_);
return v___x_1517_;
}
}
LEAN_EXPORT lean_object* l_Lean_ensureAttrDeclIsPublic___lam__0(lean_object* v_declName_1518_, uint8_t v_isModule_1519_, lean_object* v_attrName_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_){
_start:
{
lean_object* v___x_1524_; 
lean_inc(v_declName_1518_);
v___x_1524_ = l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0(v_declName_1518_, v___y_1521_, v___y_1522_);
if (lean_obj_tag(v___x_1524_) == 0)
{
lean_object* v___x_1525_; lean_object* v_a_1526_; lean_object* v___x_1528_; uint8_t v_isShared_1529_; uint8_t v_isSharedCheck_1546_; 
lean_dec_ref_known(v___x_1524_, 1);
lean_inc(v_declName_1518_);
v___x_1525_ = l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1___redArg(v_declName_1518_, v_isModule_1519_, v___y_1522_);
v_a_1526_ = lean_ctor_get(v___x_1525_, 0);
v_isSharedCheck_1546_ = !lean_is_exclusive(v___x_1525_);
if (v_isSharedCheck_1546_ == 0)
{
v___x_1528_ = v___x_1525_;
v_isShared_1529_ = v_isSharedCheck_1546_;
goto v_resetjp_1527_;
}
else
{
lean_inc(v_a_1526_);
lean_dec(v___x_1525_);
v___x_1528_ = lean_box(0);
v_isShared_1529_ = v_isSharedCheck_1546_;
goto v_resetjp_1527_;
}
v_resetjp_1527_:
{
uint8_t v___x_1530_; 
v___x_1530_ = lean_unbox(v_a_1526_);
if (v___x_1530_ == 0)
{
lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; uint8_t v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; 
lean_del_object(v___x_1528_);
v___x_1531_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1);
v___x_1532_ = l_Lean_MessageData_ofName(v_attrName_1520_);
v___x_1533_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1533_, 0, v___x_1531_);
lean_ctor_set(v___x_1533_, 1, v___x_1532_);
v___x_1534_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1, &l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1);
v___x_1535_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1535_, 0, v___x_1533_);
lean_ctor_set(v___x_1535_, 1, v___x_1534_);
v___x_1536_ = lean_unbox(v_a_1526_);
lean_dec(v_a_1526_);
v___x_1537_ = l_Lean_MessageData_ofConstName(v_declName_1518_, v___x_1536_);
v___x_1538_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1538_, 0, v___x_1535_);
lean_ctor_set(v___x_1538_, 1, v___x_1537_);
v___x_1539_ = lean_obj_once(&l_Lean_ensureAttrDeclIsPublic___lam__0___closed__1, &l_Lean_ensureAttrDeclIsPublic___lam__0___closed__1_once, _init_l_Lean_ensureAttrDeclIsPublic___lam__0___closed__1);
v___x_1540_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1540_, 0, v___x_1538_);
lean_ctor_set(v___x_1540_, 1, v___x_1539_);
v___x_1541_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_1540_, v___y_1521_, v___y_1522_);
return v___x_1541_;
}
else
{
lean_object* v___x_1542_; lean_object* v___x_1544_; 
lean_dec(v_a_1526_);
lean_dec(v_attrName_1520_);
lean_dec(v_declName_1518_);
v___x_1542_ = lean_box(0);
if (v_isShared_1529_ == 0)
{
lean_ctor_set(v___x_1528_, 0, v___x_1542_);
v___x_1544_ = v___x_1528_;
goto v_reusejp_1543_;
}
else
{
lean_object* v_reuseFailAlloc_1545_; 
v_reuseFailAlloc_1545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1545_, 0, v___x_1542_);
v___x_1544_ = v_reuseFailAlloc_1545_;
goto v_reusejp_1543_;
}
v_reusejp_1543_:
{
return v___x_1544_;
}
}
}
}
else
{
lean_dec(v_attrName_1520_);
lean_dec(v_declName_1518_);
return v___x_1524_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ensureAttrDeclIsPublic___lam__0___boxed(lean_object* v_declName_1547_, lean_object* v_isModule_1548_, lean_object* v_attrName_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_){
_start:
{
uint8_t v_isModule_boxed_1553_; lean_object* v_res_1554_; 
v_isModule_boxed_1553_ = lean_unbox(v_isModule_1548_);
v_res_1554_ = l_Lean_ensureAttrDeclIsPublic___lam__0(v_declName_1547_, v_isModule_boxed_1553_, v_attrName_1549_, v___y_1550_, v___y_1551_);
lean_dec(v___y_1551_);
lean_dec_ref(v___y_1550_);
return v_res_1554_;
}
}
LEAN_EXPORT lean_object* l_Lean_ensureAttrDeclIsPublic(lean_object* v_attrName_1555_, lean_object* v_declName_1556_, uint8_t v_attrKind_1557_, lean_object* v_a_1558_, lean_object* v_a_1559_){
_start:
{
lean_object* v___x_1561_; lean_object* v_env_1565_; lean_object* v___x_1566_; uint8_t v_isModule_1567_; 
v___x_1561_ = lean_st_ref_get(v_a_1559_);
v_env_1565_ = lean_ctor_get(v___x_1561_, 0);
lean_inc_ref(v_env_1565_);
lean_dec(v___x_1561_);
v___x_1566_ = l_Lean_Environment_header(v_env_1565_);
lean_dec_ref(v_env_1565_);
v_isModule_1567_ = lean_ctor_get_uint8(v___x_1566_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_1566_);
if (v_isModule_1567_ == 0)
{
lean_dec(v_declName_1556_);
lean_dec(v_attrName_1555_);
goto v___jp_1562_;
}
else
{
uint8_t v___x_1568_; uint8_t v___x_1569_; 
v___x_1568_ = 1;
v___x_1569_ = l_Lean_instBEqAttributeKind_beq(v_attrKind_1557_, v___x_1568_);
if (v___x_1569_ == 0)
{
lean_object* v___x_1570_; lean_object* v___f_1571_; lean_object* v___x_1572_; 
v___x_1570_ = lean_box(v_isModule_1567_);
v___f_1571_ = lean_alloc_closure((void*)(l_Lean_ensureAttrDeclIsPublic___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1571_, 0, v_declName_1556_);
lean_closure_set(v___f_1571_, 1, v___x_1570_);
lean_closure_set(v___f_1571_, 2, v_attrName_1555_);
v___x_1572_ = l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg(v___f_1571_, v_isModule_1567_, v_a_1558_, v_a_1559_);
return v___x_1572_;
}
else
{
lean_dec(v_declName_1556_);
lean_dec(v_attrName_1555_);
goto v___jp_1562_;
}
}
v___jp_1562_:
{
lean_object* v___x_1563_; lean_object* v___x_1564_; 
v___x_1563_ = lean_box(0);
v___x_1564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1564_, 0, v___x_1563_);
return v___x_1564_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ensureAttrDeclIsPublic___boxed(lean_object* v_attrName_1573_, lean_object* v_declName_1574_, lean_object* v_attrKind_1575_, lean_object* v_a_1576_, lean_object* v_a_1577_, lean_object* v_a_1578_){
_start:
{
uint8_t v_attrKind_boxed_1579_; lean_object* v_res_1580_; 
v_attrKind_boxed_1579_ = lean_unbox(v_attrKind_1575_);
v_res_1580_ = l_Lean_ensureAttrDeclIsPublic(v_attrName_1573_, v_declName_1574_, v_attrKind_boxed_1579_, v_a_1576_, v_a_1577_);
lean_dec(v_a_1577_);
lean_dec_ref(v_a_1576_);
return v_res_1580_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0(lean_object* v_opt_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_){
_start:
{
lean_object* v___x_1585_; 
v___x_1585_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0___redArg(v_opt_1581_, v___y_1582_);
return v___x_1585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0___boxed(lean_object* v_opt_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_){
_start:
{
lean_object* v_res_1590_; 
v_res_1590_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0(v_opt_1586_, v___y_1587_, v___y_1588_);
lean_dec(v___y_1588_);
lean_dec_ref(v___y_1587_);
lean_dec_ref(v_opt_1586_);
return v_res_1590_;
}
}
static lean_object* _init_l_Lean_ensureAttrDeclIsMeta___closed__1(void){
_start:
{
lean_object* v___x_1592_; lean_object* v___x_1593_; 
v___x_1592_ = ((lean_object*)(l_Lean_ensureAttrDeclIsMeta___closed__0));
v___x_1593_ = l_Lean_stringToMessageData(v___x_1592_);
return v___x_1593_;
}
}
LEAN_EXPORT lean_object* l_Lean_ensureAttrDeclIsMeta(lean_object* v_attrName_1594_, lean_object* v_declName_1595_, uint8_t v_attrKind_1596_, lean_object* v_a_1597_, lean_object* v_a_1598_){
_start:
{
lean_object* v___x_1600_; lean_object* v_env_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; uint8_t v_isModule_1604_; 
v___x_1600_ = lean_st_ref_get(v_a_1598_);
v_env_1601_ = lean_ctor_get(v___x_1600_, 0);
lean_inc_ref(v_env_1601_);
lean_dec(v___x_1600_);
v___x_1602_ = lean_st_ref_get(v_a_1598_);
v___x_1603_ = l_Lean_Environment_header(v_env_1601_);
lean_dec_ref(v_env_1601_);
v_isModule_1604_ = lean_ctor_get_uint8(v___x_1603_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_1603_);
if (v_isModule_1604_ == 0)
{
lean_object* v___x_1605_; 
lean_dec(v___x_1602_);
v___x_1605_ = l_Lean_ensureAttrDeclIsPublic(v_attrName_1594_, v_declName_1595_, v_attrKind_1596_, v_a_1597_, v_a_1598_);
return v___x_1605_;
}
else
{
lean_object* v_env_1606_; uint8_t v___x_1607_; 
v_env_1606_ = lean_ctor_get(v___x_1602_, 0);
lean_inc_ref(v_env_1606_);
lean_dec(v___x_1602_);
lean_inc(v_declName_1595_);
v___x_1607_ = l_Lean_isMarkedMeta(v_env_1606_, v_declName_1595_);
if (v___x_1607_ == 0)
{
lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; 
v___x_1608_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1);
v___x_1609_ = l_Lean_MessageData_ofName(v_attrName_1594_);
v___x_1610_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1610_, 0, v___x_1608_);
lean_ctor_set(v___x_1610_, 1, v___x_1609_);
v___x_1611_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1, &l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1);
v___x_1612_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1612_, 0, v___x_1610_);
lean_ctor_set(v___x_1612_, 1, v___x_1611_);
v___x_1613_ = l_Lean_MessageData_ofConstName(v_declName_1595_, v___x_1607_);
v___x_1614_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1614_, 0, v___x_1612_);
lean_ctor_set(v___x_1614_, 1, v___x_1613_);
v___x_1615_ = lean_obj_once(&l_Lean_ensureAttrDeclIsMeta___closed__1, &l_Lean_ensureAttrDeclIsMeta___closed__1_once, _init_l_Lean_ensureAttrDeclIsMeta___closed__1);
v___x_1616_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1616_, 0, v___x_1614_);
lean_ctor_set(v___x_1616_, 1, v___x_1615_);
v___x_1617_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_1616_, v_a_1597_, v_a_1598_);
return v___x_1617_;
}
else
{
lean_object* v___x_1618_; 
v___x_1618_ = l_Lean_ensureAttrDeclIsPublic(v_attrName_1594_, v_declName_1595_, v_attrKind_1596_, v_a_1597_, v_a_1598_);
return v___x_1618_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ensureAttrDeclIsMeta___boxed(lean_object* v_attrName_1619_, lean_object* v_declName_1620_, lean_object* v_attrKind_1621_, lean_object* v_a_1622_, lean_object* v_a_1623_, lean_object* v_a_1624_){
_start:
{
uint8_t v_attrKind_boxed_1625_; lean_object* v_res_1626_; 
v_attrKind_boxed_1625_ = lean_unbox(v_attrKind_1621_);
v_res_1626_ = l_Lean_ensureAttrDeclIsMeta(v_attrName_1619_, v_declName_1620_, v_attrKind_boxed_1625_, v_a_1622_, v_a_1623_);
lean_dec(v_a_1623_);
lean_dec_ref(v_a_1622_);
return v_res_1626_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__0(lean_object* v_x_1630_, lean_object* v___y_1631_){
_start:
{
lean_object* v___x_1633_; lean_object* v___x_1634_; 
v___x_1633_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___lam__0___closed__1));
v___x_1634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1634_, 0, v___x_1633_);
return v___x_1634_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__0___boxed(lean_object* v_x_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_){
_start:
{
lean_object* v_res_1638_; 
v_res_1638_ = l_Lean_instInhabitedTagAttribute_default___lam__0(v_x_1635_, v___y_1636_);
lean_dec_ref(v___y_1636_);
lean_dec_ref(v_x_1635_);
return v_res_1638_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__1(lean_object* v_s_1639_, lean_object* v_x_1640_){
_start:
{
lean_inc(v_s_1639_);
return v_s_1639_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__1___boxed(lean_object* v_s_1641_, lean_object* v_x_1642_){
_start:
{
lean_object* v_res_1643_; 
v_res_1643_ = l_Lean_instInhabitedTagAttribute_default___lam__1(v_s_1641_, v_x_1642_);
lean_dec(v_x_1642_);
lean_dec(v_s_1641_);
return v_res_1643_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__2(lean_object* v_x_1648_, lean_object* v_x_1649_){
_start:
{
lean_object* v___x_1650_; 
v___x_1650_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___lam__2___closed__1));
return v___x_1650_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__2___boxed(lean_object* v_x_1651_, lean_object* v_x_1652_){
_start:
{
lean_object* v_res_1653_; 
v_res_1653_ = l_Lean_instInhabitedTagAttribute_default___lam__2(v_x_1651_, v_x_1652_);
lean_dec(v_x_1652_);
lean_dec_ref(v_x_1651_);
return v_res_1653_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__3(lean_object* v_x_1654_){
_start:
{
lean_object* v___x_1655_; 
v___x_1655_ = lean_box(0);
return v___x_1655_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__3___boxed(lean_object* v_x_1656_){
_start:
{
lean_object* v_res_1657_; 
v_res_1657_ = l_Lean_instInhabitedTagAttribute_default___lam__3(v_x_1656_);
lean_dec(v_x_1656_);
return v_res_1657_;
}
}
static lean_object* _init_l_Lean_instInhabitedTagAttribute_default___closed__4(void){
_start:
{
lean_object* v___x_1662_; 
v___x_1662_ = l_Lean_instInhabitedEnvExtension_default___redArg();
return v___x_1662_;
}
}
static lean_object* _init_l_Lean_instInhabitedTagAttribute_default___closed__5(void){
_start:
{
lean_object* v___f_1663_; lean_object* v___f_1664_; lean_object* v___f_1665_; lean_object* v___f_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; 
v___f_1663_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___closed__3));
v___f_1664_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___closed__2));
v___f_1665_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___closed__1));
v___f_1666_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___closed__0));
v___x_1667_ = lean_box(0);
v___x_1668_ = lean_obj_once(&l_Lean_instInhabitedTagAttribute_default___closed__4, &l_Lean_instInhabitedTagAttribute_default___closed__4_once, _init_l_Lean_instInhabitedTagAttribute_default___closed__4);
v___x_1669_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1669_, 0, v___x_1668_);
lean_ctor_set(v___x_1669_, 1, v___x_1667_);
lean_ctor_set(v___x_1669_, 2, v___f_1666_);
lean_ctor_set(v___x_1669_, 3, v___f_1665_);
lean_ctor_set(v___x_1669_, 4, v___f_1664_);
lean_ctor_set(v___x_1669_, 5, v___f_1663_);
return v___x_1669_;
}
}
static lean_object* _init_l_Lean_instInhabitedTagAttribute_default___closed__6(void){
_start:
{
lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; 
v___x_1670_ = lean_obj_once(&l_Lean_instInhabitedTagAttribute_default___closed__5, &l_Lean_instInhabitedTagAttribute_default___closed__5_once, _init_l_Lean_instInhabitedTagAttribute_default___closed__5);
v___x_1671_ = ((lean_object*)(l_Lean_instInhabitedAttributeImpl_default));
v___x_1672_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1672_, 0, v___x_1671_);
lean_ctor_set(v___x_1672_, 1, v___x_1670_);
return v___x_1672_;
}
}
static lean_object* _init_l_Lean_instInhabitedTagAttribute_default(void){
_start:
{
lean_object* v___x_1673_; 
v___x_1673_ = lean_obj_once(&l_Lean_instInhabitedTagAttribute_default___closed__6, &l_Lean_instInhabitedTagAttribute_default___closed__6_once, _init_l_Lean_instInhabitedTagAttribute_default___closed__6);
return v___x_1673_;
}
}
static lean_object* _init_l_Lean_instInhabitedTagAttribute(void){
_start:
{
lean_object* v___x_1674_; 
v___x_1674_ = l_Lean_instInhabitedTagAttribute_default;
return v___x_1674_;
}
}
static lean_object* _init_l_Lean_registerTagAttribute___auto__1(void){
_start:
{
lean_object* v___x_1675_; 
v___x_1675_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__28, &l_Lean_AttributeImplCore_ref___autoParam___closed__28_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__28);
return v___x_1675_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__0(lean_object* v_x_1676_){
_start:
{
lean_object* v___x_1677_; 
v___x_1677_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___lam__2___closed__0));
return v___x_1677_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__0___boxed(lean_object* v_x_1678_){
_start:
{
lean_object* v_res_1679_; 
v_res_1679_ = l_Lean_registerTagAttribute___lam__0(v_x_1678_);
lean_dec(v_x_1678_);
return v_res_1679_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerTagAttribute_spec__0(lean_object* v_newState_1680_, lean_object* v_x_1681_, lean_object* v_x_1682_){
_start:
{
if (lean_obj_tag(v_x_1682_) == 0)
{
return v_x_1681_;
}
else
{
lean_object* v_head_1683_; lean_object* v_tail_1684_; uint8_t v___x_1685_; 
v_head_1683_ = lean_ctor_get(v_x_1682_, 0);
lean_inc(v_head_1683_);
v_tail_1684_ = lean_ctor_get(v_x_1682_, 1);
lean_inc(v_tail_1684_);
lean_dec_ref_known(v_x_1682_, 2);
v___x_1685_ = l_Lean_NameSet_contains(v_newState_1680_, v_head_1683_);
if (v___x_1685_ == 0)
{
lean_dec(v_head_1683_);
v_x_1682_ = v_tail_1684_;
goto _start;
}
else
{
lean_object* v___x_1687_; 
v___x_1687_ = l_Lean_NameSet_insert(v_x_1681_, v_head_1683_);
v_x_1681_ = v___x_1687_;
v_x_1682_ = v_tail_1684_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerTagAttribute_spec__0___boxed(lean_object* v_newState_1689_, lean_object* v_x_1690_, lean_object* v_x_1691_){
_start:
{
lean_object* v_res_1692_; 
v_res_1692_ = l_List_foldl___at___00Lean_registerTagAttribute_spec__0(v_newState_1689_, v_x_1690_, v_x_1691_);
lean_dec(v_newState_1689_);
return v_res_1692_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__1(lean_object* v_x_1693_, lean_object* v_newState_1694_, lean_object* v_newConsts_1695_, lean_object* v_s_1696_){
_start:
{
lean_object* v___x_1697_; 
v___x_1697_ = l_List_foldl___at___00Lean_registerTagAttribute_spec__0(v_newState_1694_, v_s_1696_, v_newConsts_1695_);
return v___x_1697_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__1___boxed(lean_object* v_x_1698_, lean_object* v_newState_1699_, lean_object* v_newConsts_1700_, lean_object* v_s_1701_){
_start:
{
lean_object* v_res_1702_; 
v_res_1702_ = l_Lean_registerTagAttribute___lam__1(v_x_1698_, v_newState_1699_, v_newConsts_1700_, v_s_1701_);
lean_dec(v_newState_1699_);
lean_dec(v_x_1698_);
return v_res_1702_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__2(lean_object* v_s_1715_){
_start:
{
lean_object* v___x_1716_; lean_object* v___y_1718_; 
v___x_1716_ = ((lean_object*)(l_Lean_registerTagAttribute___lam__2___closed__5));
if (lean_obj_tag(v_s_1715_) == 0)
{
lean_object* v_size_1722_; 
v_size_1722_ = lean_ctor_get(v_s_1715_, 0);
lean_inc(v_size_1722_);
lean_dec_ref_known(v_s_1715_, 5);
v___y_1718_ = v_size_1722_;
goto v___jp_1717_;
}
else
{
lean_object* v___x_1723_; 
v___x_1723_ = lean_unsigned_to_nat(0u);
v___y_1718_ = v___x_1723_;
goto v___jp_1717_;
}
v___jp_1717_:
{
lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; 
v___x_1719_ = l_Nat_reprFast(v___y_1718_);
v___x_1720_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1720_, 0, v___x_1719_);
v___x_1721_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1721_, 0, v___x_1716_);
lean_ctor_set(v___x_1721_, 1, v___x_1720_);
return v___x_1721_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4___redArg(lean_object* v_hi_1724_, lean_object* v_pivot_1725_, lean_object* v_as_1726_, lean_object* v_i_1727_, lean_object* v_k_1728_){
_start:
{
uint8_t v___x_1729_; 
v___x_1729_ = lean_nat_dec_lt(v_k_1728_, v_hi_1724_);
if (v___x_1729_ == 0)
{
lean_object* v___x_1730_; lean_object* v___x_1731_; 
lean_dec(v_k_1728_);
v___x_1730_ = lean_array_fswap(v_as_1726_, v_i_1727_, v_hi_1724_);
v___x_1731_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1731_, 0, v_i_1727_);
lean_ctor_set(v___x_1731_, 1, v___x_1730_);
return v___x_1731_;
}
else
{
lean_object* v___x_1732_; uint8_t v___x_1733_; 
v___x_1732_ = lean_array_fget_borrowed(v_as_1726_, v_k_1728_);
v___x_1733_ = l_Lean_Name_quickLt(v___x_1732_, v_pivot_1725_);
if (v___x_1733_ == 0)
{
lean_object* v___x_1734_; lean_object* v___x_1735_; 
v___x_1734_ = lean_unsigned_to_nat(1u);
v___x_1735_ = lean_nat_add(v_k_1728_, v___x_1734_);
lean_dec(v_k_1728_);
v_k_1728_ = v___x_1735_;
goto _start;
}
else
{
lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; 
v___x_1737_ = lean_array_fswap(v_as_1726_, v_i_1727_, v_k_1728_);
v___x_1738_ = lean_unsigned_to_nat(1u);
v___x_1739_ = lean_nat_add(v_i_1727_, v___x_1738_);
lean_dec(v_i_1727_);
v___x_1740_ = lean_nat_add(v_k_1728_, v___x_1738_);
lean_dec(v_k_1728_);
v_as_1726_ = v___x_1737_;
v_i_1727_ = v___x_1739_;
v_k_1728_ = v___x_1740_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4___redArg___boxed(lean_object* v_hi_1742_, lean_object* v_pivot_1743_, lean_object* v_as_1744_, lean_object* v_i_1745_, lean_object* v_k_1746_){
_start:
{
lean_object* v_res_1747_; 
v_res_1747_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4___redArg(v_hi_1742_, v_pivot_1743_, v_as_1744_, v_i_1745_, v_k_1746_);
lean_dec(v_pivot_1743_);
lean_dec(v_hi_1742_);
return v_res_1747_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___redArg(lean_object* v_n_1748_, lean_object* v_as_1749_, lean_object* v_lo_1750_, lean_object* v_hi_1751_){
_start:
{
lean_object* v___y_1753_; uint8_t v___x_1763_; 
v___x_1763_ = lean_nat_dec_lt(v_lo_1750_, v_hi_1751_);
if (v___x_1763_ == 0)
{
lean_dec(v_lo_1750_);
return v_as_1749_;
}
else
{
lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v_mid_1766_; lean_object* v___y_1768_; lean_object* v___y_1774_; lean_object* v___x_1779_; lean_object* v___x_1780_; uint8_t v___x_1781_; 
v___x_1764_ = lean_nat_add(v_lo_1750_, v_hi_1751_);
v___x_1765_ = lean_unsigned_to_nat(1u);
v_mid_1766_ = lean_nat_shiftr(v___x_1764_, v___x_1765_);
lean_dec(v___x_1764_);
v___x_1779_ = lean_array_fget_borrowed(v_as_1749_, v_mid_1766_);
v___x_1780_ = lean_array_fget_borrowed(v_as_1749_, v_lo_1750_);
v___x_1781_ = l_Lean_Name_quickLt(v___x_1779_, v___x_1780_);
if (v___x_1781_ == 0)
{
v___y_1774_ = v_as_1749_;
goto v___jp_1773_;
}
else
{
lean_object* v___x_1782_; 
v___x_1782_ = lean_array_fswap(v_as_1749_, v_lo_1750_, v_mid_1766_);
v___y_1774_ = v___x_1782_;
goto v___jp_1773_;
}
v___jp_1767_:
{
lean_object* v___x_1769_; lean_object* v___x_1770_; uint8_t v___x_1771_; 
v___x_1769_ = lean_array_fget_borrowed(v___y_1768_, v_mid_1766_);
v___x_1770_ = lean_array_fget_borrowed(v___y_1768_, v_hi_1751_);
v___x_1771_ = l_Lean_Name_quickLt(v___x_1769_, v___x_1770_);
if (v___x_1771_ == 0)
{
lean_dec(v_mid_1766_);
v___y_1753_ = v___y_1768_;
goto v___jp_1752_;
}
else
{
lean_object* v___x_1772_; 
v___x_1772_ = lean_array_fswap(v___y_1768_, v_mid_1766_, v_hi_1751_);
lean_dec(v_mid_1766_);
v___y_1753_ = v___x_1772_;
goto v___jp_1752_;
}
}
v___jp_1773_:
{
lean_object* v___x_1775_; lean_object* v___x_1776_; uint8_t v___x_1777_; 
v___x_1775_ = lean_array_fget_borrowed(v___y_1774_, v_hi_1751_);
v___x_1776_ = lean_array_fget_borrowed(v___y_1774_, v_lo_1750_);
v___x_1777_ = l_Lean_Name_quickLt(v___x_1775_, v___x_1776_);
if (v___x_1777_ == 0)
{
v___y_1768_ = v___y_1774_;
goto v___jp_1767_;
}
else
{
lean_object* v___x_1778_; 
v___x_1778_ = lean_array_fswap(v___y_1774_, v_lo_1750_, v_hi_1751_);
v___y_1768_ = v___x_1778_;
goto v___jp_1767_;
}
}
}
v___jp_1752_:
{
lean_object* v_pivot_1754_; lean_object* v___x_1755_; lean_object* v_fst_1756_; lean_object* v_snd_1757_; uint8_t v___x_1758_; 
v_pivot_1754_ = lean_array_fget(v___y_1753_, v_hi_1751_);
lean_inc_n(v_lo_1750_, 2);
v___x_1755_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4___redArg(v_hi_1751_, v_pivot_1754_, v___y_1753_, v_lo_1750_, v_lo_1750_);
lean_dec(v_pivot_1754_);
v_fst_1756_ = lean_ctor_get(v___x_1755_, 0);
lean_inc(v_fst_1756_);
v_snd_1757_ = lean_ctor_get(v___x_1755_, 1);
lean_inc(v_snd_1757_);
lean_dec_ref(v___x_1755_);
v___x_1758_ = lean_nat_dec_le(v_hi_1751_, v_fst_1756_);
if (v___x_1758_ == 0)
{
lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; 
v___x_1759_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___redArg(v_n_1748_, v_snd_1757_, v_lo_1750_, v_fst_1756_);
v___x_1760_ = lean_unsigned_to_nat(1u);
v___x_1761_ = lean_nat_add(v_fst_1756_, v___x_1760_);
lean_dec(v_fst_1756_);
v_as_1749_ = v___x_1759_;
v_lo_1750_ = v___x_1761_;
goto _start;
}
else
{
lean_dec(v_fst_1756_);
lean_dec(v_lo_1750_);
return v_snd_1757_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___redArg___boxed(lean_object* v_n_1783_, lean_object* v_as_1784_, lean_object* v_lo_1785_, lean_object* v_hi_1786_){
_start:
{
lean_object* v_res_1787_; 
v_res_1787_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___redArg(v_n_1783_, v_as_1784_, v_lo_1785_, v_hi_1786_);
lean_dec(v_hi_1786_);
lean_dec(v_n_1783_);
return v_res_1787_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerTagAttribute_spec__2(lean_object* v_env_1788_, lean_object* v_as_1789_, size_t v_i_1790_, size_t v_stop_1791_, lean_object* v_b_1792_){
_start:
{
lean_object* v___y_1794_; uint8_t v___x_1798_; 
v___x_1798_ = lean_usize_dec_eq(v_i_1790_, v_stop_1791_);
if (v___x_1798_ == 0)
{
lean_object* v___x_1799_; uint8_t v___x_1800_; lean_object* v___x_1801_; uint8_t v___x_1802_; 
v___x_1799_ = lean_array_uget_borrowed(v_as_1789_, v_i_1790_);
v___x_1800_ = 1;
lean_inc_ref(v_env_1788_);
v___x_1801_ = l_Lean_Environment_setExporting(v_env_1788_, v___x_1800_);
lean_inc(v___x_1799_);
v___x_1802_ = l_Lean_Environment_contains(v___x_1801_, v___x_1799_, v___x_1798_);
if (v___x_1802_ == 0)
{
v___y_1794_ = v_b_1792_;
goto v___jp_1793_;
}
else
{
lean_object* v___x_1803_; 
lean_inc(v___x_1799_);
v___x_1803_ = lean_array_push(v_b_1792_, v___x_1799_);
v___y_1794_ = v___x_1803_;
goto v___jp_1793_;
}
}
else
{
lean_dec_ref(v_env_1788_);
return v_b_1792_;
}
v___jp_1793_:
{
size_t v___x_1795_; size_t v___x_1796_; 
v___x_1795_ = ((size_t)1ULL);
v___x_1796_ = lean_usize_add(v_i_1790_, v___x_1795_);
v_i_1790_ = v___x_1796_;
v_b_1792_ = v___y_1794_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerTagAttribute_spec__2___boxed(lean_object* v_env_1804_, lean_object* v_as_1805_, lean_object* v_i_1806_, lean_object* v_stop_1807_, lean_object* v_b_1808_){
_start:
{
size_t v_i_boxed_1809_; size_t v_stop_boxed_1810_; lean_object* v_res_1811_; 
v_i_boxed_1809_ = lean_unbox_usize(v_i_1806_);
lean_dec(v_i_1806_);
v_stop_boxed_1810_ = lean_unbox_usize(v_stop_1807_);
lean_dec(v_stop_1807_);
v_res_1811_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerTagAttribute_spec__2(v_env_1804_, v_as_1805_, v_i_boxed_1809_, v_stop_boxed_1810_, v_b_1808_);
lean_dec_ref(v_as_1805_);
return v_res_1811_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerTagAttribute_spec__1_spec__1(lean_object* v_init_1812_, lean_object* v_x_1813_){
_start:
{
if (lean_obj_tag(v_x_1813_) == 0)
{
lean_object* v_k_1814_; lean_object* v_l_1815_; lean_object* v_r_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; 
v_k_1814_ = lean_ctor_get(v_x_1813_, 1);
lean_inc(v_k_1814_);
v_l_1815_ = lean_ctor_get(v_x_1813_, 3);
lean_inc(v_l_1815_);
v_r_1816_ = lean_ctor_get(v_x_1813_, 4);
lean_inc(v_r_1816_);
lean_dec_ref_known(v_x_1813_, 5);
v___x_1817_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerTagAttribute_spec__1_spec__1(v_init_1812_, v_l_1815_);
v___x_1818_ = lean_array_push(v___x_1817_, v_k_1814_);
v_init_1812_ = v___x_1818_;
v_x_1813_ = v_r_1816_;
goto _start;
}
else
{
return v_init_1812_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__3(lean_object* v_env_1820_, lean_object* v_es_1821_){
_start:
{
lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___y_1825_; lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___y_1842_; lean_object* v___y_1843_; uint8_t v___x_1845_; 
v___x_1822_ = lean_unsigned_to_nat(0u);
v___x_1823_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___lam__2___closed__0));
v___x_1839_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerTagAttribute_spec__1_spec__1(v___x_1823_, v_es_1821_);
v___x_1840_ = lean_array_get_size(v___x_1839_);
v___x_1845_ = lean_nat_dec_eq(v___x_1840_, v___x_1822_);
if (v___x_1845_ == 0)
{
lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___y_1849_; uint8_t v___x_1851_; 
v___x_1846_ = lean_unsigned_to_nat(1u);
v___x_1847_ = lean_nat_sub(v___x_1840_, v___x_1846_);
v___x_1851_ = lean_nat_dec_le(v___x_1822_, v___x_1847_);
if (v___x_1851_ == 0)
{
lean_inc(v___x_1847_);
v___y_1849_ = v___x_1847_;
goto v___jp_1848_;
}
else
{
v___y_1849_ = v___x_1822_;
goto v___jp_1848_;
}
v___jp_1848_:
{
uint8_t v___x_1850_; 
v___x_1850_ = lean_nat_dec_le(v___y_1849_, v___x_1847_);
if (v___x_1850_ == 0)
{
lean_dec(v___x_1847_);
lean_inc(v___y_1849_);
v___y_1842_ = v___y_1849_;
v___y_1843_ = v___y_1849_;
goto v___jp_1841_;
}
else
{
v___y_1842_ = v___y_1849_;
v___y_1843_ = v___x_1847_;
goto v___jp_1841_;
}
}
}
else
{
v___y_1825_ = v___x_1839_;
goto v___jp_1824_;
}
v___jp_1824_:
{
lean_object* v___x_1826_; uint8_t v___x_1827_; 
v___x_1826_ = lean_array_get_size(v___y_1825_);
v___x_1827_ = lean_nat_dec_lt(v___x_1822_, v___x_1826_);
if (v___x_1827_ == 0)
{
lean_object* v___x_1828_; 
lean_dec_ref(v_env_1820_);
v___x_1828_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1828_, 0, v___x_1823_);
lean_ctor_set(v___x_1828_, 1, v___x_1823_);
lean_ctor_set(v___x_1828_, 2, v___y_1825_);
return v___x_1828_;
}
else
{
uint8_t v___x_1829_; 
v___x_1829_ = lean_nat_dec_le(v___x_1826_, v___x_1826_);
if (v___x_1829_ == 0)
{
if (v___x_1827_ == 0)
{
lean_object* v___x_1830_; 
lean_dec_ref(v_env_1820_);
v___x_1830_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1830_, 0, v___x_1823_);
lean_ctor_set(v___x_1830_, 1, v___x_1823_);
lean_ctor_set(v___x_1830_, 2, v___y_1825_);
return v___x_1830_;
}
else
{
size_t v___x_1831_; size_t v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; 
v___x_1831_ = ((size_t)0ULL);
v___x_1832_ = lean_usize_of_nat(v___x_1826_);
v___x_1833_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerTagAttribute_spec__2(v_env_1820_, v___y_1825_, v___x_1831_, v___x_1832_, v___x_1823_);
lean_inc_ref(v___x_1833_);
v___x_1834_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1834_, 0, v___x_1833_);
lean_ctor_set(v___x_1834_, 1, v___x_1833_);
lean_ctor_set(v___x_1834_, 2, v___y_1825_);
return v___x_1834_;
}
}
else
{
size_t v___x_1835_; size_t v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; 
v___x_1835_ = ((size_t)0ULL);
v___x_1836_ = lean_usize_of_nat(v___x_1826_);
v___x_1837_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerTagAttribute_spec__2(v_env_1820_, v___y_1825_, v___x_1835_, v___x_1836_, v___x_1823_);
lean_inc_ref(v___x_1837_);
v___x_1838_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1838_, 0, v___x_1837_);
lean_ctor_set(v___x_1838_, 1, v___x_1837_);
lean_ctor_set(v___x_1838_, 2, v___y_1825_);
return v___x_1838_;
}
}
}
v___jp_1841_:
{
lean_object* v___x_1844_; 
v___x_1844_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___redArg(v___x_1840_, v___x_1839_, v___y_1842_, v___y_1843_);
lean_dec(v___y_1843_);
v___y_1825_ = v___x_1844_;
goto v___jp_1824_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__4(lean_object* v_name_1852_, lean_object* v_decl_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_){
_start:
{
lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; 
v___x_1857_ = lean_obj_once(&l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1, &l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1_once, _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1);
v___x_1858_ = l_Lean_MessageData_ofName(v_name_1852_);
v___x_1859_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1859_, 0, v___x_1857_);
lean_ctor_set(v___x_1859_, 1, v___x_1858_);
v___x_1860_ = lean_obj_once(&l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3, &l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3_once, _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3);
v___x_1861_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1861_, 0, v___x_1859_);
lean_ctor_set(v___x_1861_, 1, v___x_1860_);
v___x_1862_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_1861_, v___y_1854_, v___y_1855_);
return v___x_1862_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__4___boxed(lean_object* v_name_1863_, lean_object* v_decl_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_){
_start:
{
lean_object* v_res_1868_; 
v_res_1868_ = l_Lean_registerTagAttribute___lam__4(v_name_1863_, v_decl_1864_, v___y_1865_, v___y_1866_);
lean_dec(v___y_1866_);
lean_dec_ref(v___y_1865_);
lean_dec(v_decl_1864_);
return v_res_1868_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__5(lean_object* v___x_1869_, lean_object* v_x_1870_, lean_object* v_x_1871_){
_start:
{
lean_object* v___x_1873_; 
v___x_1873_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1873_, 0, v___x_1869_);
return v___x_1873_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__5___boxed(lean_object* v___x_1874_, lean_object* v_x_1875_, lean_object* v_x_1876_, lean_object* v___y_1877_){
_start:
{
lean_object* v_res_1878_; 
v_res_1878_ = l_Lean_registerTagAttribute___lam__5(v___x_1874_, v_x_1875_, v_x_1876_);
lean_dec_ref(v_x_1876_);
lean_dec_ref(v_x_1875_);
return v_res_1878_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__6(lean_object* v___x_1879_){
_start:
{
lean_object* v___x_1881_; 
v___x_1881_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1881_, 0, v___x_1879_);
return v___x_1881_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__6___boxed(lean_object* v___x_1882_, lean_object* v___y_1883_){
_start:
{
lean_object* v_res_1884_; 
v_res_1884_ = l_Lean_registerTagAttribute___lam__6(v___x_1882_);
return v_res_1884_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg(lean_object* v_attrName_1885_, lean_object* v_declName_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_){
_start:
{
lean_object* v___x_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; uint8_t v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; 
v___x_1890_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1);
v___x_1891_ = l_Lean_MessageData_ofName(v_attrName_1885_);
v___x_1892_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1892_, 0, v___x_1890_);
lean_ctor_set(v___x_1892_, 1, v___x_1891_);
v___x_1893_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__3, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__3_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__3);
v___x_1894_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1894_, 0, v___x_1892_);
lean_ctor_set(v___x_1894_, 1, v___x_1893_);
v___x_1895_ = 0;
v___x_1896_ = l_Lean_MessageData_ofConstName(v_declName_1886_, v___x_1895_);
v___x_1897_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1897_, 0, v___x_1894_);
lean_ctor_set(v___x_1897_, 1, v___x_1896_);
v___x_1898_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__5, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__5_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__5);
v___x_1899_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1899_, 0, v___x_1897_);
lean_ctor_set(v___x_1899_, 1, v___x_1898_);
v___x_1900_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_1899_, v___y_1887_, v___y_1888_);
return v___x_1900_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg___boxed(lean_object* v_attrName_1901_, lean_object* v_declName_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_){
_start:
{
lean_object* v_res_1906_; 
v_res_1906_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg(v_attrName_1901_, v_declName_1902_, v___y_1903_, v___y_1904_);
lean_dec(v___y_1904_);
lean_dec_ref(v___y_1903_);
return v_res_1906_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___redArg(lean_object* v_attrName_1907_, lean_object* v_declName_1908_, lean_object* v_asyncPrefix_x3f_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_){
_start:
{
lean_object* v___y_1914_; 
if (lean_obj_tag(v_asyncPrefix_x3f_1909_) == 0)
{
lean_object* v___x_1927_; 
v___x_1927_ = l_Lean_MessageData_nil;
v___y_1914_ = v___x_1927_;
goto v___jp_1913_;
}
else
{
lean_object* v_val_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; 
v_val_1928_ = lean_ctor_get(v_asyncPrefix_x3f_1909_, 0);
lean_inc(v_val_1928_);
lean_dec_ref_known(v_asyncPrefix_x3f_1909_, 1);
v___x_1929_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___redArg___closed__3, &l_Lean_throwAttrNotInAsyncCtx___redArg___closed__3_once, _init_l_Lean_throwAttrNotInAsyncCtx___redArg___closed__3);
v___x_1930_ = l_Lean_MessageData_ofName(v_val_1928_);
v___x_1931_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1931_, 0, v___x_1929_);
lean_ctor_set(v___x_1931_, 1, v___x_1930_);
v___x_1932_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__5, &l_Lean_throwAttrMustBeGlobal___redArg___closed__5_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__5);
v___x_1933_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1933_, 0, v___x_1931_);
lean_ctor_set(v___x_1933_, 1, v___x_1932_);
v___y_1914_ = v___x_1933_;
goto v___jp_1913_;
}
v___jp_1913_:
{
lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; uint8_t v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; 
v___x_1915_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1);
v___x_1916_ = l_Lean_MessageData_ofName(v_attrName_1907_);
v___x_1917_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1917_, 0, v___x_1915_);
lean_ctor_set(v___x_1917_, 1, v___x_1916_);
v___x_1918_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__3, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__3_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__3);
v___x_1919_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1919_, 0, v___x_1917_);
lean_ctor_set(v___x_1919_, 1, v___x_1918_);
v___x_1920_ = 0;
v___x_1921_ = l_Lean_MessageData_ofConstName(v_declName_1908_, v___x_1920_);
v___x_1922_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1922_, 0, v___x_1919_);
lean_ctor_set(v___x_1922_, 1, v___x_1921_);
v___x_1923_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___redArg___closed__1, &l_Lean_throwAttrNotInAsyncCtx___redArg___closed__1_once, _init_l_Lean_throwAttrNotInAsyncCtx___redArg___closed__1);
v___x_1924_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1924_, 0, v___x_1922_);
lean_ctor_set(v___x_1924_, 1, v___x_1923_);
v___x_1925_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1925_, 0, v___x_1924_);
lean_ctor_set(v___x_1925_, 1, v___y_1914_);
v___x_1926_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_1925_, v___y_1910_, v___y_1911_);
return v___x_1926_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___redArg___boxed(lean_object* v_attrName_1934_, lean_object* v_declName_1935_, lean_object* v_asyncPrefix_x3f_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_){
_start:
{
lean_object* v_res_1940_; 
v_res_1940_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___redArg(v_attrName_1934_, v_declName_1935_, v_asyncPrefix_x3f_1936_, v___y_1937_, v___y_1938_);
lean_dec(v___y_1938_);
lean_dec_ref(v___y_1937_);
return v_res_1940_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg(lean_object* v_name_1941_, uint8_t v_kind_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_){
_start:
{
lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v___y_1952_; 
v___x_1946_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__1, &l_Lean_throwAttrMustBeGlobal___redArg___closed__1_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__1);
v___x_1947_ = l_Lean_MessageData_ofName(v_name_1941_);
v___x_1948_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1948_, 0, v___x_1946_);
lean_ctor_set(v___x_1948_, 1, v___x_1947_);
v___x_1949_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__3, &l_Lean_throwAttrMustBeGlobal___redArg___closed__3_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__3);
v___x_1950_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1950_, 0, v___x_1948_);
lean_ctor_set(v___x_1950_, 1, v___x_1949_);
switch(v_kind_1942_)
{
case 0:
{
lean_object* v___x_1959_; 
v___x_1959_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__0));
v___y_1952_ = v___x_1959_;
goto v___jp_1951_;
}
case 1:
{
lean_object* v___x_1960_; 
v___x_1960_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__1));
v___y_1952_ = v___x_1960_;
goto v___jp_1951_;
}
default: 
{
lean_object* v___x_1961_; 
v___x_1961_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__2));
v___y_1952_ = v___x_1961_;
goto v___jp_1951_;
}
}
v___jp_1951_:
{
lean_object* v___x_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; 
lean_inc_ref(v___y_1952_);
v___x_1953_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1953_, 0, v___y_1952_);
v___x_1954_ = l_Lean_MessageData_ofFormat(v___x_1953_);
v___x_1955_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1955_, 0, v___x_1950_);
lean_ctor_set(v___x_1955_, 1, v___x_1954_);
v___x_1956_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__5, &l_Lean_throwAttrMustBeGlobal___redArg___closed__5_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__5);
v___x_1957_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1957_, 0, v___x_1955_);
lean_ctor_set(v___x_1957_, 1, v___x_1956_);
v___x_1958_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_1957_, v___y_1943_, v___y_1944_);
return v___x_1958_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg___boxed(lean_object* v_name_1962_, lean_object* v_kind_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_){
_start:
{
uint8_t v_kind_boxed_1967_; lean_object* v_res_1968_; 
v_kind_boxed_1967_ = lean_unbox(v_kind_1963_);
v_res_1968_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg(v_name_1962_, v_kind_boxed_1967_, v___y_1964_, v___y_1965_);
lean_dec(v___y_1965_);
lean_dec_ref(v___y_1964_);
return v_res_1968_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__7(lean_object* v_validate_1969_, lean_object* v_a_1970_, lean_object* v_name_1971_, lean_object* v_decl_1972_, lean_object* v_stx_1973_, uint8_t v_kind_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_){
_start:
{
lean_object* v___y_1979_; lean_object* v___y_1980_; lean_object* v___y_2015_; lean_object* v___y_2016_; lean_object* v___y_2017_; lean_object* v___x_2028_; 
v___x_2028_ = l_Lean_Attribute_Builtin_ensureNoArgs(v_stx_1973_, v___y_1975_, v___y_1976_);
if (lean_obj_tag(v___x_2028_) == 0)
{
uint8_t v___x_2029_; uint8_t v___x_2030_; 
lean_dec_ref_known(v___x_2028_, 1);
v___x_2029_ = 0;
v___x_2030_ = l_Lean_instBEqAttributeKind_beq(v_kind_1974_, v___x_2029_);
if (v___x_2030_ == 0)
{
lean_object* v___x_2031_; 
lean_dec(v_decl_1972_);
lean_dec_ref(v_a_1970_);
lean_dec_ref(v_validate_1969_);
v___x_2031_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg(v_name_1971_, v_kind_1974_, v___y_1975_, v___y_1976_);
return v___x_2031_;
}
else
{
goto v___jp_2023_;
}
}
else
{
lean_dec(v_decl_1972_);
lean_dec(v_name_1971_);
lean_dec_ref(v_a_1970_);
lean_dec_ref(v_validate_1969_);
return v___x_2028_;
}
v___jp_1978_:
{
lean_object* v___x_1981_; 
lean_inc(v___y_1980_);
lean_inc_ref(v___y_1979_);
lean_inc(v_decl_1972_);
v___x_1981_ = lean_apply_4(v_validate_1969_, v_decl_1972_, v___y_1979_, v___y_1980_, lean_box(0));
if (lean_obj_tag(v___x_1981_) == 0)
{
lean_object* v___x_1983_; uint8_t v_isShared_1984_; uint8_t v_isSharedCheck_2012_; 
v_isSharedCheck_2012_ = !lean_is_exclusive(v___x_1981_);
if (v_isSharedCheck_2012_ == 0)
{
lean_object* v_unused_2013_; 
v_unused_2013_ = lean_ctor_get(v___x_1981_, 0);
lean_dec(v_unused_2013_);
v___x_1983_ = v___x_1981_;
v_isShared_1984_ = v_isSharedCheck_2012_;
goto v_resetjp_1982_;
}
else
{
lean_dec(v___x_1981_);
v___x_1983_ = lean_box(0);
v_isShared_1984_ = v_isSharedCheck_2012_;
goto v_resetjp_1982_;
}
v_resetjp_1982_:
{
lean_object* v___x_1985_; lean_object* v_toEnvExtension_1986_; lean_object* v_env_1987_; lean_object* v_nextMacroScope_1988_; lean_object* v_ngen_1989_; lean_object* v_auxDeclNGen_1990_; lean_object* v_traceState_1991_; lean_object* v_recordedDeps_1992_; lean_object* v_messages_1993_; lean_object* v_infoState_1994_; lean_object* v_snapshotTasks_1995_; lean_object* v___x_1997_; uint8_t v_isShared_1998_; uint8_t v_isSharedCheck_2010_; 
v___x_1985_ = lean_st_ref_take(v___y_1980_);
v_toEnvExtension_1986_ = lean_ctor_get(v_a_1970_, 0);
v_env_1987_ = lean_ctor_get(v___x_1985_, 0);
v_nextMacroScope_1988_ = lean_ctor_get(v___x_1985_, 1);
v_ngen_1989_ = lean_ctor_get(v___x_1985_, 2);
v_auxDeclNGen_1990_ = lean_ctor_get(v___x_1985_, 3);
v_traceState_1991_ = lean_ctor_get(v___x_1985_, 4);
v_recordedDeps_1992_ = lean_ctor_get(v___x_1985_, 6);
v_messages_1993_ = lean_ctor_get(v___x_1985_, 7);
v_infoState_1994_ = lean_ctor_get(v___x_1985_, 8);
v_snapshotTasks_1995_ = lean_ctor_get(v___x_1985_, 9);
v_isSharedCheck_2010_ = !lean_is_exclusive(v___x_1985_);
if (v_isSharedCheck_2010_ == 0)
{
lean_object* v_unused_2011_; 
v_unused_2011_ = lean_ctor_get(v___x_1985_, 5);
lean_dec(v_unused_2011_);
v___x_1997_ = v___x_1985_;
v_isShared_1998_ = v_isSharedCheck_2010_;
goto v_resetjp_1996_;
}
else
{
lean_inc(v_snapshotTasks_1995_);
lean_inc(v_infoState_1994_);
lean_inc(v_messages_1993_);
lean_inc(v_recordedDeps_1992_);
lean_inc(v_traceState_1991_);
lean_inc(v_auxDeclNGen_1990_);
lean_inc(v_ngen_1989_);
lean_inc(v_nextMacroScope_1988_);
lean_inc(v_env_1987_);
lean_dec(v___x_1985_);
v___x_1997_ = lean_box(0);
v_isShared_1998_ = v_isSharedCheck_2010_;
goto v_resetjp_1996_;
}
v_resetjp_1996_:
{
lean_object* v_asyncMode_1999_; lean_object* v___x_2000_; lean_object* v___x_2001_; lean_object* v___x_2002_; lean_object* v___x_2004_; 
v_asyncMode_1999_ = lean_ctor_get(v_toEnvExtension_1986_, 2);
lean_inc(v_asyncMode_1999_);
v___x_2000_ = lean_box(0);
lean_inc(v_decl_1972_);
v___x_2001_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_a_1970_, v_env_1987_, v_decl_1972_, v_asyncMode_1999_, v_decl_1972_);
lean_dec(v_asyncMode_1999_);
v___x_2002_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1);
if (v_isShared_1998_ == 0)
{
lean_ctor_set(v___x_1997_, 5, v___x_2002_);
lean_ctor_set(v___x_1997_, 0, v___x_2001_);
v___x_2004_ = v___x_1997_;
goto v_reusejp_2003_;
}
else
{
lean_object* v_reuseFailAlloc_2009_; 
v_reuseFailAlloc_2009_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2009_, 0, v___x_2001_);
lean_ctor_set(v_reuseFailAlloc_2009_, 1, v_nextMacroScope_1988_);
lean_ctor_set(v_reuseFailAlloc_2009_, 2, v_ngen_1989_);
lean_ctor_set(v_reuseFailAlloc_2009_, 3, v_auxDeclNGen_1990_);
lean_ctor_set(v_reuseFailAlloc_2009_, 4, v_traceState_1991_);
lean_ctor_set(v_reuseFailAlloc_2009_, 5, v___x_2002_);
lean_ctor_set(v_reuseFailAlloc_2009_, 6, v_recordedDeps_1992_);
lean_ctor_set(v_reuseFailAlloc_2009_, 7, v_messages_1993_);
lean_ctor_set(v_reuseFailAlloc_2009_, 8, v_infoState_1994_);
lean_ctor_set(v_reuseFailAlloc_2009_, 9, v_snapshotTasks_1995_);
v___x_2004_ = v_reuseFailAlloc_2009_;
goto v_reusejp_2003_;
}
v_reusejp_2003_:
{
lean_object* v___x_2005_; lean_object* v___x_2007_; 
v___x_2005_ = lean_st_ref_put(v___y_1980_, v___x_2004_);
if (v_isShared_1984_ == 0)
{
lean_ctor_set(v___x_1983_, 0, v___x_2000_);
v___x_2007_ = v___x_1983_;
goto v_reusejp_2006_;
}
else
{
lean_object* v_reuseFailAlloc_2008_; 
v_reuseFailAlloc_2008_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2008_, 0, v___x_2000_);
v___x_2007_ = v_reuseFailAlloc_2008_;
goto v_reusejp_2006_;
}
v_reusejp_2006_:
{
return v___x_2007_;
}
}
}
}
}
else
{
lean_dec(v_decl_1972_);
lean_dec_ref(v_a_1970_);
return v___x_1981_;
}
}
v___jp_2014_:
{
lean_object* v_toEnvExtension_2018_; lean_object* v_asyncMode_2019_; uint8_t v___x_2020_; 
v_toEnvExtension_2018_ = lean_ctor_get(v_a_1970_, 0);
v_asyncMode_2019_ = lean_ctor_get(v_toEnvExtension_2018_, 2);
lean_inc(v_decl_1972_);
lean_inc_ref(v___y_2015_);
v___x_2020_ = l_Lean_EnvExtension_asyncMayModify___redArg(v___y_2015_, v_decl_1972_, v_asyncMode_2019_);
if (v___x_2020_ == 0)
{
lean_object* v___x_2021_; lean_object* v___x_2022_; 
lean_dec_ref(v_a_1970_);
lean_dec_ref(v_validate_1969_);
v___x_2021_ = l_Lean_Environment_asyncPrefix_x3f(v___y_2015_);
v___x_2022_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___redArg(v_name_1971_, v_decl_1972_, v___x_2021_, v___y_2016_, v___y_2017_);
return v___x_2022_;
}
else
{
lean_dec_ref(v___y_2015_);
lean_dec(v_name_1971_);
v___y_1979_ = v___y_2016_;
v___y_1980_ = v___y_2017_;
goto v___jp_1978_;
}
}
v___jp_2023_:
{
lean_object* v___x_2024_; lean_object* v_env_2025_; lean_object* v___x_2026_; 
v___x_2024_ = lean_st_ref_get(v___y_1976_);
v_env_2025_ = lean_ctor_get(v___x_2024_, 0);
lean_inc_ref(v_env_2025_);
lean_dec(v___x_2024_);
v___x_2026_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2025_, v_decl_1972_);
if (lean_obj_tag(v___x_2026_) == 0)
{
v___y_2015_ = v_env_2025_;
v___y_2016_ = v___y_1975_;
v___y_2017_ = v___y_1976_;
goto v___jp_2014_;
}
else
{
lean_object* v___x_2027_; 
lean_dec_ref_known(v___x_2026_, 1);
lean_dec_ref(v_env_2025_);
lean_dec_ref(v_a_1970_);
lean_dec_ref(v_validate_1969_);
v___x_2027_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg(v_name_1971_, v_decl_1972_, v___y_1975_, v___y_1976_);
return v___x_2027_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__7___boxed(lean_object* v_validate_2032_, lean_object* v_a_2033_, lean_object* v_name_2034_, lean_object* v_decl_2035_, lean_object* v_stx_2036_, lean_object* v_kind_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_){
_start:
{
uint8_t v_kind_boxed_2041_; lean_object* v_res_2042_; 
v_kind_boxed_2041_ = lean_unbox(v_kind_2037_);
v_res_2042_ = l_Lean_registerTagAttribute___lam__7(v_validate_2032_, v_a_2033_, v_name_2034_, v_decl_2035_, v_stx_2036_, v_kind_boxed_2041_, v___y_2038_, v___y_2039_);
lean_dec(v___y_2039_);
lean_dec_ref(v___y_2038_);
return v_res_2042_;
}
}
static lean_object* _init_l_Lean_registerTagAttribute___closed__5(void){
_start:
{
lean_object* v___x_2048_; lean_object* v___f_2049_; 
v___x_2048_ = l_Lean_NameSet_empty;
v___f_2049_ = lean_alloc_closure((void*)(l_Lean_registerTagAttribute___lam__5___boxed), 4, 1);
lean_closure_set(v___f_2049_, 0, v___x_2048_);
return v___f_2049_;
}
}
static lean_object* _init_l_Lean_registerTagAttribute___closed__6(void){
_start:
{
lean_object* v___x_2050_; lean_object* v___f_2051_; 
v___x_2050_ = l_Lean_NameSet_empty;
v___f_2051_ = lean_alloc_closure((void*)(l_Lean_registerTagAttribute___lam__6___boxed), 2, 1);
lean_closure_set(v___f_2051_, 0, v___x_2050_);
return v___f_2051_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute(lean_object* v_name_2054_, lean_object* v_descr_2055_, lean_object* v_validate_2056_, lean_object* v_ref_2057_, uint8_t v_applicationTime_2058_, lean_object* v_asyncMode_2059_){
_start:
{
lean_object* v___f_2061_; lean_object* v___f_2062_; lean_object* v___f_2063_; lean_object* v___f_2064_; lean_object* v___f_2065_; lean_object* v___f_2066_; lean_object* v___f_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; 
v___f_2061_ = ((lean_object*)(l_Lean_registerTagAttribute___closed__0));
v___f_2062_ = ((lean_object*)(l_Lean_registerTagAttribute___closed__2));
v___f_2063_ = ((lean_object*)(l_Lean_registerTagAttribute___closed__3));
v___f_2064_ = ((lean_object*)(l_Lean_registerTagAttribute___closed__4));
lean_inc(v_name_2054_);
v___f_2065_ = lean_alloc_closure((void*)(l_Lean_registerTagAttribute___lam__4___boxed), 5, 1);
lean_closure_set(v___f_2065_, 0, v_name_2054_);
v___f_2066_ = lean_obj_once(&l_Lean_registerTagAttribute___closed__5, &l_Lean_registerTagAttribute___closed__5_once, _init_l_Lean_registerTagAttribute___closed__5);
v___f_2067_ = lean_obj_once(&l_Lean_registerTagAttribute___closed__6, &l_Lean_registerTagAttribute___closed__6_once, _init_l_Lean_registerTagAttribute___closed__6);
v___x_2068_ = ((lean_object*)(l_Lean_registerTagAttribute___closed__7));
lean_inc(v_ref_2057_);
v___x_2069_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_2069_, 0, v_ref_2057_);
lean_ctor_set(v___x_2069_, 1, v___f_2067_);
lean_ctor_set(v___x_2069_, 2, v___f_2066_);
lean_ctor_set(v___x_2069_, 3, v___f_2064_);
lean_ctor_set(v___x_2069_, 4, v___f_2063_);
lean_ctor_set(v___x_2069_, 5, v___f_2062_);
lean_ctor_set(v___x_2069_, 6, v_asyncMode_2059_);
lean_ctor_set(v___x_2069_, 7, v___x_2068_);
v___x_2070_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2070_, 0, v___x_2069_);
lean_ctor_set(v___x_2070_, 1, v___f_2061_);
v___x_2071_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_2070_);
if (lean_obj_tag(v___x_2071_) == 0)
{
lean_object* v_a_2072_; lean_object* v___f_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; 
v_a_2072_ = lean_ctor_get(v___x_2071_, 0);
lean_inc_n(v_a_2072_, 2);
lean_dec_ref_known(v___x_2071_, 1);
lean_inc(v_name_2054_);
v___f_2073_ = lean_alloc_closure((void*)(l_Lean_registerTagAttribute___lam__7___boxed), 9, 3);
lean_closure_set(v___f_2073_, 0, v_validate_2056_);
lean_closure_set(v___f_2073_, 1, v_a_2072_);
lean_closure_set(v___f_2073_, 2, v_name_2054_);
v___x_2074_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2074_, 0, v_ref_2057_);
lean_ctor_set(v___x_2074_, 1, v_name_2054_);
lean_ctor_set(v___x_2074_, 2, v_descr_2055_);
lean_ctor_set_uint8(v___x_2074_, sizeof(void*)*3, v_applicationTime_2058_);
v___x_2075_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2075_, 0, v___x_2074_);
lean_ctor_set(v___x_2075_, 1, v___f_2073_);
lean_ctor_set(v___x_2075_, 2, v___f_2065_);
lean_inc_ref(v___x_2075_);
v___x_2076_ = l_Lean_registerBuiltinAttribute(v___x_2075_);
if (lean_obj_tag(v___x_2076_) == 0)
{
lean_object* v___x_2078_; uint8_t v_isShared_2079_; uint8_t v_isSharedCheck_2084_; 
v_isSharedCheck_2084_ = !lean_is_exclusive(v___x_2076_);
if (v_isSharedCheck_2084_ == 0)
{
lean_object* v_unused_2085_; 
v_unused_2085_ = lean_ctor_get(v___x_2076_, 0);
lean_dec(v_unused_2085_);
v___x_2078_ = v___x_2076_;
v_isShared_2079_ = v_isSharedCheck_2084_;
goto v_resetjp_2077_;
}
else
{
lean_dec(v___x_2076_);
v___x_2078_ = lean_box(0);
v_isShared_2079_ = v_isSharedCheck_2084_;
goto v_resetjp_2077_;
}
v_resetjp_2077_:
{
lean_object* v___x_2080_; lean_object* v___x_2082_; 
v___x_2080_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2080_, 0, v___x_2075_);
lean_ctor_set(v___x_2080_, 1, v_a_2072_);
if (v_isShared_2079_ == 0)
{
lean_ctor_set(v___x_2078_, 0, v___x_2080_);
v___x_2082_ = v___x_2078_;
goto v_reusejp_2081_;
}
else
{
lean_object* v_reuseFailAlloc_2083_; 
v_reuseFailAlloc_2083_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2083_, 0, v___x_2080_);
v___x_2082_ = v_reuseFailAlloc_2083_;
goto v_reusejp_2081_;
}
v_reusejp_2081_:
{
return v___x_2082_;
}
}
}
else
{
lean_object* v_a_2086_; lean_object* v___x_2088_; uint8_t v_isShared_2089_; uint8_t v_isSharedCheck_2093_; 
lean_dec_ref_known(v___x_2075_, 3);
lean_dec(v_a_2072_);
v_a_2086_ = lean_ctor_get(v___x_2076_, 0);
v_isSharedCheck_2093_ = !lean_is_exclusive(v___x_2076_);
if (v_isSharedCheck_2093_ == 0)
{
v___x_2088_ = v___x_2076_;
v_isShared_2089_ = v_isSharedCheck_2093_;
goto v_resetjp_2087_;
}
else
{
lean_inc(v_a_2086_);
lean_dec(v___x_2076_);
v___x_2088_ = lean_box(0);
v_isShared_2089_ = v_isSharedCheck_2093_;
goto v_resetjp_2087_;
}
v_resetjp_2087_:
{
lean_object* v___x_2091_; 
if (v_isShared_2089_ == 0)
{
v___x_2091_ = v___x_2088_;
goto v_reusejp_2090_;
}
else
{
lean_object* v_reuseFailAlloc_2092_; 
v_reuseFailAlloc_2092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2092_, 0, v_a_2086_);
v___x_2091_ = v_reuseFailAlloc_2092_;
goto v_reusejp_2090_;
}
v_reusejp_2090_:
{
return v___x_2091_;
}
}
}
}
else
{
lean_object* v_a_2094_; lean_object* v___x_2096_; uint8_t v_isShared_2097_; uint8_t v_isSharedCheck_2101_; 
lean_dec_ref(v___f_2065_);
lean_dec(v_ref_2057_);
lean_dec_ref(v_validate_2056_);
lean_dec_ref(v_descr_2055_);
lean_dec(v_name_2054_);
v_a_2094_ = lean_ctor_get(v___x_2071_, 0);
v_isSharedCheck_2101_ = !lean_is_exclusive(v___x_2071_);
if (v_isSharedCheck_2101_ == 0)
{
v___x_2096_ = v___x_2071_;
v_isShared_2097_ = v_isSharedCheck_2101_;
goto v_resetjp_2095_;
}
else
{
lean_inc(v_a_2094_);
lean_dec(v___x_2071_);
v___x_2096_ = lean_box(0);
v_isShared_2097_ = v_isSharedCheck_2101_;
goto v_resetjp_2095_;
}
v_resetjp_2095_:
{
lean_object* v___x_2099_; 
if (v_isShared_2097_ == 0)
{
v___x_2099_ = v___x_2096_;
goto v_reusejp_2098_;
}
else
{
lean_object* v_reuseFailAlloc_2100_; 
v_reuseFailAlloc_2100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2100_, 0, v_a_2094_);
v___x_2099_ = v_reuseFailAlloc_2100_;
goto v_reusejp_2098_;
}
v_reusejp_2098_:
{
return v___x_2099_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___boxed(lean_object* v_name_2102_, lean_object* v_descr_2103_, lean_object* v_validate_2104_, lean_object* v_ref_2105_, lean_object* v_applicationTime_2106_, lean_object* v_asyncMode_2107_, lean_object* v_a_2108_){
_start:
{
uint8_t v_applicationTime_boxed_2109_; lean_object* v_res_2110_; 
v_applicationTime_boxed_2109_ = lean_unbox(v_applicationTime_2106_);
v_res_2110_ = l_Lean_registerTagAttribute(v_name_2102_, v_descr_2103_, v_validate_2104_, v_ref_2105_, v_applicationTime_boxed_2109_, v_asyncMode_2107_);
return v_res_2110_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerTagAttribute_spec__1(lean_object* v_init_2111_, lean_object* v_t_2112_){
_start:
{
lean_object* v___x_2113_; 
v___x_2113_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerTagAttribute_spec__1_spec__1(v_init_2111_, v_t_2112_);
return v___x_2113_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3(lean_object* v_n_2114_, lean_object* v_as_2115_, lean_object* v_lo_2116_, lean_object* v_hi_2117_, lean_object* v_w_2118_, lean_object* v_hlo_2119_, lean_object* v_hhi_2120_){
_start:
{
lean_object* v___x_2121_; 
v___x_2121_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___redArg(v_n_2114_, v_as_2115_, v_lo_2116_, v_hi_2117_);
return v___x_2121_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___boxed(lean_object* v_n_2122_, lean_object* v_as_2123_, lean_object* v_lo_2124_, lean_object* v_hi_2125_, lean_object* v_w_2126_, lean_object* v_hlo_2127_, lean_object* v_hhi_2128_){
_start:
{
lean_object* v_res_2129_; 
v_res_2129_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3(v_n_2122_, v_as_2123_, v_lo_2124_, v_hi_2125_, v_w_2126_, v_hlo_2127_, v_hhi_2128_);
lean_dec(v_hi_2125_);
lean_dec(v_n_2122_);
return v_res_2129_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4(lean_object* v_00_u03b1_2130_, lean_object* v_attrName_2131_, lean_object* v_declName_2132_, lean_object* v_asyncPrefix_x3f_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_){
_start:
{
lean_object* v___x_2137_; 
v___x_2137_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___redArg(v_attrName_2131_, v_declName_2132_, v_asyncPrefix_x3f_2133_, v___y_2134_, v___y_2135_);
return v___x_2137_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___boxed(lean_object* v_00_u03b1_2138_, lean_object* v_attrName_2139_, lean_object* v_declName_2140_, lean_object* v_asyncPrefix_x3f_2141_, lean_object* v___y_2142_, lean_object* v___y_2143_, lean_object* v___y_2144_){
_start:
{
lean_object* v_res_2145_; 
v_res_2145_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4(v_00_u03b1_2138_, v_attrName_2139_, v_declName_2140_, v_asyncPrefix_x3f_2141_, v___y_2142_, v___y_2143_);
lean_dec(v___y_2143_);
lean_dec_ref(v___y_2142_);
return v_res_2145_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5(lean_object* v_00_u03b1_2146_, lean_object* v_attrName_2147_, lean_object* v_declName_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_){
_start:
{
lean_object* v___x_2152_; 
v___x_2152_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg(v_attrName_2147_, v_declName_2148_, v___y_2149_, v___y_2150_);
return v___x_2152_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___boxed(lean_object* v_00_u03b1_2153_, lean_object* v_attrName_2154_, lean_object* v_declName_2155_, lean_object* v___y_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_){
_start:
{
lean_object* v_res_2159_; 
v_res_2159_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5(v_00_u03b1_2153_, v_attrName_2154_, v_declName_2155_, v___y_2156_, v___y_2157_);
lean_dec(v___y_2157_);
lean_dec_ref(v___y_2156_);
return v_res_2159_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6(lean_object* v_00_u03b1_2160_, lean_object* v_name_2161_, uint8_t v_kind_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_){
_start:
{
lean_object* v___x_2166_; 
v___x_2166_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg(v_name_2161_, v_kind_2162_, v___y_2163_, v___y_2164_);
return v___x_2166_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___boxed(lean_object* v_00_u03b1_2167_, lean_object* v_name_2168_, lean_object* v_kind_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_){
_start:
{
uint8_t v_kind_boxed_2173_; lean_object* v_res_2174_; 
v_kind_boxed_2173_ = lean_unbox(v_kind_2169_);
v_res_2174_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6(v_00_u03b1_2167_, v_name_2168_, v_kind_boxed_2173_, v___y_2170_, v___y_2171_);
lean_dec(v___y_2171_);
lean_dec_ref(v___y_2170_);
return v_res_2174_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4(lean_object* v_n_2175_, lean_object* v_lo_2176_, lean_object* v_hi_2177_, lean_object* v_hhi_2178_, lean_object* v_pivot_2179_, lean_object* v_as_2180_, lean_object* v_i_2181_, lean_object* v_k_2182_, lean_object* v_ilo_2183_, lean_object* v_ik_2184_, lean_object* v_w_2185_){
_start:
{
lean_object* v___x_2186_; 
v___x_2186_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4___redArg(v_hi_2177_, v_pivot_2179_, v_as_2180_, v_i_2181_, v_k_2182_);
return v___x_2186_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4___boxed(lean_object* v_n_2187_, lean_object* v_lo_2188_, lean_object* v_hi_2189_, lean_object* v_hhi_2190_, lean_object* v_pivot_2191_, lean_object* v_as_2192_, lean_object* v_i_2193_, lean_object* v_k_2194_, lean_object* v_ilo_2195_, lean_object* v_ik_2196_, lean_object* v_w_2197_){
_start:
{
lean_object* v_res_2198_; 
v_res_2198_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4(v_n_2187_, v_lo_2188_, v_hi_2189_, v_hhi_2190_, v_pivot_2191_, v_as_2192_, v_i_2193_, v_k_2194_, v_ilo_2195_, v_ik_2196_, v_w_2197_);
lean_dec(v_pivot_2191_);
lean_dec(v_hi_2189_);
lean_dec(v_lo_2188_);
lean_dec(v_n_2187_);
return v_res_2198_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg___lam__0(lean_object* v_attr_2199_, lean_object* v_decl_2200_, lean_object* v_env_2201_){
_start:
{
lean_object* v_ext_2202_; lean_object* v_toEnvExtension_2203_; lean_object* v_asyncMode_2204_; lean_object* v___x_2205_; 
v_ext_2202_ = lean_ctor_get(v_attr_2199_, 1);
lean_inc_ref(v_ext_2202_);
lean_dec_ref(v_attr_2199_);
v_toEnvExtension_2203_ = lean_ctor_get(v_ext_2202_, 0);
v_asyncMode_2204_ = lean_ctor_get(v_toEnvExtension_2203_, 2);
lean_inc(v_asyncMode_2204_);
lean_inc(v_decl_2200_);
v___x_2205_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_ext_2202_, v_env_2201_, v_decl_2200_, v_asyncMode_2204_, v_decl_2200_);
lean_dec(v_asyncMode_2204_);
return v___x_2205_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg___lam__1(lean_object* v_modifyEnv_2206_, lean_object* v___f_2207_, lean_object* v_____r_2208_){
_start:
{
lean_object* v___x_2209_; 
v___x_2209_ = lean_apply_1(v_modifyEnv_2206_, v___f_2207_);
return v___x_2209_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg___lam__2(lean_object* v_attr_2210_, lean_object* v_env_2211_, lean_object* v_decl_2212_, lean_object* v_inst_2213_, lean_object* v_inst_2214_, lean_object* v_toBind_2215_, lean_object* v___f_2216_, lean_object* v_modifyEnv_2217_, lean_object* v___f_2218_, lean_object* v_____r_2219_){
_start:
{
lean_object* v_ext_2220_; lean_object* v_toEnvExtension_2221_; lean_object* v_attr_2222_; lean_object* v_asyncMode_2223_; uint8_t v___x_2224_; 
v_ext_2220_ = lean_ctor_get(v_attr_2210_, 1);
v_toEnvExtension_2221_ = lean_ctor_get(v_ext_2220_, 0);
lean_inc_ref(v_toEnvExtension_2221_);
v_attr_2222_ = lean_ctor_get(v_attr_2210_, 0);
lean_inc_ref(v_attr_2222_);
lean_dec_ref(v_attr_2210_);
v_asyncMode_2223_ = lean_ctor_get(v_toEnvExtension_2221_, 2);
lean_inc(v_asyncMode_2223_);
lean_dec_ref(v_toEnvExtension_2221_);
lean_inc(v_decl_2212_);
lean_inc_ref(v_env_2211_);
v___x_2224_ = l_Lean_EnvExtension_asyncMayModify___redArg(v_env_2211_, v_decl_2212_, v_asyncMode_2223_);
lean_dec(v_asyncMode_2223_);
if (v___x_2224_ == 0)
{
lean_object* v_toAttributeImplCore_2225_; lean_object* v_name_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; 
lean_dec_ref(v___f_2218_);
lean_dec(v_modifyEnv_2217_);
v_toAttributeImplCore_2225_ = lean_ctor_get(v_attr_2222_, 0);
lean_inc_ref(v_toAttributeImplCore_2225_);
lean_dec_ref(v_attr_2222_);
v_name_2226_ = lean_ctor_get(v_toAttributeImplCore_2225_, 1);
lean_inc(v_name_2226_);
lean_dec_ref(v_toAttributeImplCore_2225_);
v___x_2227_ = l_Lean_Environment_asyncPrefix_x3f(v_env_2211_);
v___x_2228_ = l_Lean_throwAttrNotInAsyncCtx___redArg(v_inst_2213_, v_inst_2214_, v_name_2226_, v_decl_2212_, v___x_2227_);
v___x_2229_ = lean_apply_4(v_toBind_2215_, lean_box(0), lean_box(0), v___x_2228_, v___f_2216_);
return v___x_2229_;
}
else
{
lean_object* v___x_2230_; 
lean_dec_ref(v_attr_2222_);
lean_dec(v___f_2216_);
lean_dec(v_toBind_2215_);
lean_dec_ref(v_inst_2214_);
lean_dec_ref(v_inst_2213_);
lean_dec(v_decl_2212_);
lean_dec_ref(v_env_2211_);
v___x_2230_ = lean_apply_1(v_modifyEnv_2217_, v___f_2218_);
return v___x_2230_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg___lam__3(lean_object* v___f_2231_, lean_object* v_____r_2232_){
_start:
{
lean_object* v___x_2233_; 
v___x_2233_ = lean_apply_1(v___f_2231_, v_____r_2232_);
return v___x_2233_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg___lam__4(lean_object* v_attr_2234_, lean_object* v_decl_2235_, lean_object* v_inst_2236_, lean_object* v_inst_2237_, lean_object* v_toBind_2238_, lean_object* v___f_2239_, lean_object* v_modifyEnv_2240_, lean_object* v___f_2241_, lean_object* v_env_2242_){
_start:
{
lean_object* v___f_2243_; lean_object* v___x_2244_; 
lean_inc_ref(v___f_2241_);
lean_inc(v_modifyEnv_2240_);
lean_inc(v___f_2239_);
lean_inc(v_toBind_2238_);
lean_inc_ref(v_inst_2237_);
lean_inc_ref(v_inst_2236_);
lean_inc(v_decl_2235_);
lean_inc_ref(v_env_2242_);
lean_inc_ref(v_attr_2234_);
v___f_2243_ = lean_alloc_closure((void*)(l_Lean_TagAttribute_setTag___redArg___lam__2), 10, 9);
lean_closure_set(v___f_2243_, 0, v_attr_2234_);
lean_closure_set(v___f_2243_, 1, v_env_2242_);
lean_closure_set(v___f_2243_, 2, v_decl_2235_);
lean_closure_set(v___f_2243_, 3, v_inst_2236_);
lean_closure_set(v___f_2243_, 4, v_inst_2237_);
lean_closure_set(v___f_2243_, 5, v_toBind_2238_);
lean_closure_set(v___f_2243_, 6, v___f_2239_);
lean_closure_set(v___f_2243_, 7, v_modifyEnv_2240_);
lean_closure_set(v___f_2243_, 8, v___f_2241_);
v___x_2244_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2242_, v_decl_2235_);
if (lean_obj_tag(v___x_2244_) == 0)
{
lean_object* v___x_2245_; lean_object* v___x_2246_; 
lean_dec_ref(v___f_2243_);
v___x_2245_ = lean_box(0);
v___x_2246_ = l_Lean_TagAttribute_setTag___redArg___lam__2(v_attr_2234_, v_env_2242_, v_decl_2235_, v_inst_2236_, v_inst_2237_, v_toBind_2238_, v___f_2239_, v_modifyEnv_2240_, v___f_2241_, v___x_2245_);
return v___x_2246_;
}
else
{
lean_object* v_attr_2247_; lean_object* v_toAttributeImplCore_2248_; lean_object* v_name_2249_; lean_object* v___f_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; 
lean_dec_ref_known(v___x_2244_, 1);
lean_dec_ref(v_env_2242_);
lean_dec_ref(v___f_2241_);
lean_dec(v_modifyEnv_2240_);
lean_dec(v___f_2239_);
v_attr_2247_ = lean_ctor_get(v_attr_2234_, 0);
lean_inc_ref(v_attr_2247_);
lean_dec_ref(v_attr_2234_);
v_toAttributeImplCore_2248_ = lean_ctor_get(v_attr_2247_, 0);
lean_inc_ref(v_toAttributeImplCore_2248_);
lean_dec_ref(v_attr_2247_);
v_name_2249_ = lean_ctor_get(v_toAttributeImplCore_2248_, 1);
lean_inc(v_name_2249_);
lean_dec_ref(v_toAttributeImplCore_2248_);
v___f_2250_ = lean_alloc_closure((void*)(l_Lean_TagAttribute_setTag___redArg___lam__3), 2, 1);
lean_closure_set(v___f_2250_, 0, v___f_2243_);
v___x_2251_ = l_Lean_throwAttrDeclInImportedModule___redArg(v_inst_2236_, v_inst_2237_, v_name_2249_, v_decl_2235_);
v___x_2252_ = lean_apply_4(v_toBind_2238_, lean_box(0), lean_box(0), v___x_2251_, v___f_2250_);
return v___x_2252_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg(lean_object* v_inst_2253_, lean_object* v_inst_2254_, lean_object* v_inst_2255_, lean_object* v_attr_2256_, lean_object* v_decl_2257_){
_start:
{
lean_object* v_toBind_2258_; lean_object* v_getEnv_2259_; lean_object* v_modifyEnv_2260_; lean_object* v___f_2261_; lean_object* v___f_2262_; lean_object* v___f_2263_; lean_object* v___x_2264_; 
v_toBind_2258_ = lean_ctor_get(v_inst_2253_, 1);
lean_inc_n(v_toBind_2258_, 2);
v_getEnv_2259_ = lean_ctor_get(v_inst_2255_, 0);
lean_inc(v_getEnv_2259_);
v_modifyEnv_2260_ = lean_ctor_get(v_inst_2255_, 1);
lean_inc_n(v_modifyEnv_2260_, 2);
lean_dec_ref(v_inst_2255_);
lean_inc(v_decl_2257_);
lean_inc_ref(v_attr_2256_);
v___f_2261_ = lean_alloc_closure((void*)(l_Lean_TagAttribute_setTag___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2261_, 0, v_attr_2256_);
lean_closure_set(v___f_2261_, 1, v_decl_2257_);
lean_inc_ref(v___f_2261_);
v___f_2262_ = lean_alloc_closure((void*)(l_Lean_TagAttribute_setTag___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2262_, 0, v_modifyEnv_2260_);
lean_closure_set(v___f_2262_, 1, v___f_2261_);
v___f_2263_ = lean_alloc_closure((void*)(l_Lean_TagAttribute_setTag___redArg___lam__4), 9, 8);
lean_closure_set(v___f_2263_, 0, v_attr_2256_);
lean_closure_set(v___f_2263_, 1, v_decl_2257_);
lean_closure_set(v___f_2263_, 2, v_inst_2253_);
lean_closure_set(v___f_2263_, 3, v_inst_2254_);
lean_closure_set(v___f_2263_, 4, v_toBind_2258_);
lean_closure_set(v___f_2263_, 5, v___f_2262_);
lean_closure_set(v___f_2263_, 6, v_modifyEnv_2260_);
lean_closure_set(v___f_2263_, 7, v___f_2261_);
v___x_2264_ = lean_apply_4(v_toBind_2258_, lean_box(0), lean_box(0), v_getEnv_2259_, v___f_2263_);
return v___x_2264_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag(lean_object* v_m_2265_, lean_object* v_inst_2266_, lean_object* v_inst_2267_, lean_object* v_inst_2268_, lean_object* v_attr_2269_, lean_object* v_decl_2270_){
_start:
{
lean_object* v___x_2271_; 
v___x_2271_ = l_Lean_TagAttribute_setTag___redArg(v_inst_2266_, v_inst_2267_, v_inst_2268_, v_attr_2269_, v_decl_2270_);
return v___x_2271_;
}
}
LEAN_EXPORT uint8_t l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___redArg(lean_object* v___y_2272_, lean_object* v_as_2273_, lean_object* v_k_2274_, lean_object* v_x_2275_, lean_object* v_x_2276_){
_start:
{
lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v_m_2279_; lean_object* v_a_2280_; uint8_t v___x_2281_; 
v___x_2277_ = lean_nat_add(v_x_2275_, v_x_2276_);
v___x_2278_ = lean_unsigned_to_nat(1u);
v_m_2279_ = lean_nat_shiftr(v___x_2277_, v___x_2278_);
lean_dec(v___x_2277_);
v_a_2280_ = lean_array_fget_borrowed(v_as_2273_, v_m_2279_);
v___x_2281_ = l_Lean_Name_quickLt(v_a_2280_, v_k_2274_);
if (v___x_2281_ == 0)
{
lean_object* v___x_2282_; uint8_t v___x_2283_; 
lean_dec(v_x_2276_);
v___x_2282_ = lean_unsigned_to_nat(0u);
v___x_2283_ = l_Lean_Name_quickLt(v_k_2274_, v_a_2280_);
if (v___x_2283_ == 0)
{
uint8_t v___x_2284_; 
lean_dec(v_m_2279_);
lean_dec(v_x_2275_);
v___x_2284_ = lean_nat_dec_le(v___x_2282_, v___y_2272_);
return v___x_2284_;
}
else
{
uint8_t v___x_2285_; lean_object* v___x_2286_; uint8_t v___y_2288_; 
v___x_2285_ = lean_nat_dec_eq(v_m_2279_, v___x_2282_);
v___x_2286_ = lean_nat_sub(v_m_2279_, v___x_2278_);
lean_dec(v_m_2279_);
if (v___x_2285_ == 0)
{
uint8_t v___x_2290_; 
v___x_2290_ = lean_nat_dec_lt(v___x_2286_, v_x_2275_);
v___y_2288_ = v___x_2290_;
goto v___jp_2287_;
}
else
{
v___y_2288_ = v___x_2285_;
goto v___jp_2287_;
}
v___jp_2287_:
{
if (v___y_2288_ == 0)
{
v_x_2276_ = v___x_2286_;
goto _start;
}
else
{
lean_dec(v___x_2286_);
lean_dec(v_x_2275_);
return v___x_2281_;
}
}
}
}
else
{
lean_object* v___x_2291_; uint8_t v___x_2292_; 
lean_dec(v_x_2275_);
v___x_2291_ = lean_nat_add(v_m_2279_, v___x_2278_);
lean_dec(v_m_2279_);
v___x_2292_ = lean_nat_dec_le(v___x_2291_, v_x_2276_);
if (v___x_2292_ == 0)
{
lean_dec(v___x_2291_);
lean_dec(v_x_2276_);
return v___x_2292_;
}
else
{
v_x_2275_ = v___x_2291_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___redArg___boxed(lean_object* v___y_2294_, lean_object* v_as_2295_, lean_object* v_k_2296_, lean_object* v_x_2297_, lean_object* v_x_2298_){
_start:
{
uint8_t v_res_2299_; lean_object* v_r_2300_; 
v_res_2299_ = l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___redArg(v___y_2294_, v_as_2295_, v_k_2296_, v_x_2297_, v_x_2298_);
lean_dec(v_k_2296_);
lean_dec_ref(v_as_2295_);
lean_dec(v___y_2294_);
v_r_2300_ = lean_box(v_res_2299_);
return v_r_2300_;
}
}
LEAN_EXPORT uint8_t l_Lean_TagAttribute_hasTag(lean_object* v_attr_2301_, lean_object* v_env_2302_, lean_object* v_decl_2303_){
_start:
{
lean_object* v___x_2304_; lean_object* v___x_2305_; 
v___x_2304_ = lean_box(1);
v___x_2305_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2302_, v_decl_2303_);
if (lean_obj_tag(v___x_2305_) == 0)
{
lean_object* v_ext_2306_; lean_object* v_toEnvExtension_2307_; lean_object* v_asyncMode_2308_; lean_object* v___x_2309_; uint8_t v___x_2310_; 
v_ext_2306_ = lean_ctor_get(v_attr_2301_, 1);
v_toEnvExtension_2307_ = lean_ctor_get(v_ext_2306_, 0);
v_asyncMode_2308_ = lean_ctor_get(v_toEnvExtension_2307_, 2);
lean_inc(v_decl_2303_);
v___x_2309_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2304_, v_ext_2306_, v_env_2302_, v_asyncMode_2308_, v_decl_2303_);
v___x_2310_ = l_Lean_NameSet_contains(v___x_2309_, v_decl_2303_);
lean_dec(v_decl_2303_);
lean_dec(v___x_2309_);
return v___x_2310_;
}
else
{
lean_object* v_val_2311_; lean_object* v_ext_2312_; uint8_t v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; uint8_t v___x_2317_; 
v_val_2311_ = lean_ctor_get(v___x_2305_, 0);
lean_inc(v_val_2311_);
lean_dec_ref_known(v___x_2305_, 1);
v_ext_2312_ = lean_ctor_get(v_attr_2301_, 1);
v___x_2313_ = 0;
v___x_2314_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_2304_, v_ext_2312_, v_env_2302_, v_val_2311_, v___x_2313_);
lean_dec(v_val_2311_);
lean_dec_ref(v_env_2302_);
v___x_2315_ = lean_unsigned_to_nat(0u);
v___x_2316_ = lean_array_get_size(v___x_2314_);
v___x_2317_ = lean_nat_dec_lt(v___x_2315_, v___x_2316_);
if (v___x_2317_ == 0)
{
lean_dec_ref(v___x_2314_);
lean_dec(v_decl_2303_);
return v___x_2317_;
}
else
{
lean_object* v___x_2318_; lean_object* v___x_2319_; uint8_t v___x_2320_; 
v___x_2318_ = lean_unsigned_to_nat(1u);
v___x_2319_ = lean_nat_sub(v___x_2316_, v___x_2318_);
v___x_2320_ = lean_nat_dec_le(v___x_2315_, v___x_2319_);
if (v___x_2320_ == 0)
{
lean_dec(v___x_2319_);
lean_dec_ref(v___x_2314_);
lean_dec(v_decl_2303_);
return v___x_2320_;
}
else
{
uint8_t v___x_2321_; 
lean_inc(v___x_2319_);
v___x_2321_ = l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___redArg(v___x_2319_, v___x_2314_, v_decl_2303_, v___x_2315_, v___x_2319_);
lean_dec(v_decl_2303_);
lean_dec_ref(v___x_2314_);
lean_dec(v___x_2319_);
return v___x_2321_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_hasTag___boxed(lean_object* v_attr_2322_, lean_object* v_env_2323_, lean_object* v_decl_2324_){
_start:
{
uint8_t v_res_2325_; lean_object* v_r_2326_; 
v_res_2325_ = l_Lean_TagAttribute_hasTag(v_attr_2322_, v_env_2323_, v_decl_2324_);
lean_dec_ref(v_attr_2322_);
v_r_2326_ = lean_box(v_res_2325_);
return v_r_2326_;
}
}
LEAN_EXPORT uint8_t l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0(lean_object* v___y_2327_, lean_object* v_as_2328_, lean_object* v_k_2329_, lean_object* v_x_2330_, lean_object* v_x_2331_, lean_object* v_x_2332_){
_start:
{
uint8_t v___x_2333_; 
v___x_2333_ = l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___redArg(v___y_2327_, v_as_2328_, v_k_2329_, v_x_2330_, v_x_2331_);
return v___x_2333_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___boxed(lean_object* v___y_2334_, lean_object* v_as_2335_, lean_object* v_k_2336_, lean_object* v_x_2337_, lean_object* v_x_2338_, lean_object* v_x_2339_){
_start:
{
uint8_t v_res_2340_; lean_object* v_r_2341_; 
v_res_2340_ = l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0(v___y_2334_, v_as_2335_, v_k_2336_, v_x_2337_, v_x_2338_, v_x_2339_);
lean_dec(v_k_2336_);
lean_dec_ref(v_as_2335_);
lean_dec(v___y_2334_);
v_r_2341_ = lean_box(v_res_2340_);
return v_r_2341_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg___lam__0(lean_object* v_x_2342_, lean_object* v___y_2343_){
_start:
{
lean_object* v___x_2345_; lean_object* v___x_2346_; 
v___x_2345_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___lam__0___closed__1));
v___x_2346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2346_, 0, v___x_2345_);
return v___x_2346_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg___lam__0___boxed(lean_object* v_x_2347_, lean_object* v___y_2348_, lean_object* v___y_2349_){
_start:
{
lean_object* v_res_2350_; 
v_res_2350_ = l_Lean_instInhabitedParametricAttribute_default___redArg___lam__0(v_x_2347_, v___y_2348_);
lean_dec_ref(v___y_2348_);
lean_dec_ref(v_x_2347_);
return v_res_2350_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg___lam__1(lean_object* v_s_2351_, lean_object* v_x_2352_){
_start:
{
lean_inc_ref(v_s_2351_);
return v_s_2351_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg___lam__1___boxed(lean_object* v_s_2353_, lean_object* v_x_2354_){
_start:
{
lean_object* v_res_2355_; 
v_res_2355_ = l_Lean_instInhabitedParametricAttribute_default___redArg___lam__1(v_s_2353_, v_x_2354_);
lean_dec_ref(v_x_2354_);
lean_dec_ref(v_s_2353_);
return v_res_2355_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg___lam__2(lean_object* v_x_2360_, lean_object* v_x_2361_){
_start:
{
lean_object* v___x_2362_; 
v___x_2362_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___redArg___lam__2___closed__1));
return v___x_2362_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg___lam__2___boxed(lean_object* v_x_2363_, lean_object* v_x_2364_){
_start:
{
lean_object* v_res_2365_; 
v_res_2365_ = l_Lean_instInhabitedParametricAttribute_default___redArg___lam__2(v_x_2363_, v_x_2364_);
lean_dec_ref(v_x_2364_);
lean_dec_ref(v_x_2363_);
return v_res_2365_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg___lam__3(lean_object* v_x_2366_){
_start:
{
lean_object* v___x_2367_; 
v___x_2367_ = lean_box(0);
return v___x_2367_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg___lam__3___boxed(lean_object* v_x_2368_){
_start:
{
lean_object* v_res_2369_; 
v_res_2369_ = l_Lean_instInhabitedParametricAttribute_default___redArg___lam__3(v_x_2368_);
lean_dec_ref(v_x_2368_);
return v_res_2369_;
}
}
static lean_object* _init_l_Lean_instInhabitedParametricAttribute_default___redArg___closed__4(void){
_start:
{
lean_object* v___f_2374_; lean_object* v___f_2375_; lean_object* v___f_2376_; lean_object* v___f_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; 
v___f_2374_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___redArg___closed__3));
v___f_2375_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___redArg___closed__2));
v___f_2376_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___redArg___closed__1));
v___f_2377_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___redArg___closed__0));
v___x_2378_ = lean_box(0);
v___x_2379_ = lean_obj_once(&l_Lean_instInhabitedTagAttribute_default___closed__4, &l_Lean_instInhabitedTagAttribute_default___closed__4_once, _init_l_Lean_instInhabitedTagAttribute_default___closed__4);
v___x_2380_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2380_, 0, v___x_2379_);
lean_ctor_set(v___x_2380_, 1, v___x_2378_);
lean_ctor_set(v___x_2380_, 2, v___f_2377_);
lean_ctor_set(v___x_2380_, 3, v___f_2376_);
lean_ctor_set(v___x_2380_, 4, v___f_2375_);
lean_ctor_set(v___x_2380_, 5, v___f_2374_);
return v___x_2380_;
}
}
static lean_object* _init_l_Lean_instInhabitedParametricAttribute_default___redArg___closed__5(void){
_start:
{
uint8_t v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; 
v___x_2381_ = 0;
v___x_2382_ = lean_obj_once(&l_Lean_instInhabitedParametricAttribute_default___redArg___closed__4, &l_Lean_instInhabitedParametricAttribute_default___redArg___closed__4_once, _init_l_Lean_instInhabitedParametricAttribute_default___redArg___closed__4);
v___x_2383_ = ((lean_object*)(l_Lean_instInhabitedAttributeImpl_default));
v___x_2384_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2384_, 0, v___x_2383_);
lean_ctor_set(v___x_2384_, 1, v___x_2382_);
lean_ctor_set_uint8(v___x_2384_, sizeof(void*)*2, v___x_2381_);
return v___x_2384_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg(){
_start:
{
lean_object* v___x_2386_; 
v___x_2386_ = lean_obj_once(&l_Lean_instInhabitedParametricAttribute_default___redArg___closed__5, &l_Lean_instInhabitedParametricAttribute_default___redArg___closed__5_once, _init_l_Lean_instInhabitedParametricAttribute_default___redArg___closed__5);
return v___x_2386_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___redArg___boxed(lean_object* v___dummy_2387_){
_start:
{
lean_object* v_res_2388_; 
v_res_2388_ = l_Lean_instInhabitedParametricAttribute_default___redArg();
return v_res_2388_;
}
}
static lean_object* _init_l_Lean_instInhabitedParametricAttribute_default___closed__0(void){
_start:
{
lean_object* v___x_2389_; 
v___x_2389_ = l_Lean_instInhabitedParametricAttribute_default___redArg();
return v___x_2389_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default(lean_object* v_00_u03b1_2390_){
_start:
{
lean_object* v___x_2391_; 
v___x_2391_ = lean_obj_once(&l_Lean_instInhabitedParametricAttribute_default___closed__0, &l_Lean_instInhabitedParametricAttribute_default___closed__0_once, _init_l_Lean_instInhabitedParametricAttribute_default___closed__0);
return v___x_2391_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute___redArg(){
_start:
{
lean_object* v___x_2393_; 
v___x_2393_ = lean_obj_once(&l_Lean_instInhabitedParametricAttribute_default___closed__0, &l_Lean_instInhabitedParametricAttribute_default___closed__0_once, _init_l_Lean_instInhabitedParametricAttribute_default___closed__0);
return v___x_2393_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute___redArg___boxed(lean_object* v___dummy_2394_){
_start:
{
lean_object* v_res_2395_; 
v_res_2395_ = l_Lean_instInhabitedParametricAttribute___redArg();
return v_res_2395_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute(lean_object* v_a_2396_){
_start:
{
lean_object* v___x_2397_; 
v___x_2397_ = lean_obj_once(&l_Lean_instInhabitedParametricAttribute_default___closed__0, &l_Lean_instInhabitedParametricAttribute_default___closed__0_once, _init_l_Lean_instInhabitedParametricAttribute_default___closed__0);
return v___x_2397_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__0(lean_object* v_x_2398_, lean_object* v_p_2399_){
_start:
{
lean_object* v_fst_2400_; lean_object* v_snd_2401_; lean_object* v___x_2403_; uint8_t v_isShared_2404_; uint8_t v_isSharedCheck_2418_; 
v_fst_2400_ = lean_ctor_get(v_x_2398_, 0);
v_snd_2401_ = lean_ctor_get(v_x_2398_, 1);
v_isSharedCheck_2418_ = !lean_is_exclusive(v_x_2398_);
if (v_isSharedCheck_2418_ == 0)
{
v___x_2403_ = v_x_2398_;
v_isShared_2404_ = v_isSharedCheck_2418_;
goto v_resetjp_2402_;
}
else
{
lean_inc(v_snd_2401_);
lean_inc(v_fst_2400_);
lean_dec(v_x_2398_);
v___x_2403_ = lean_box(0);
v_isShared_2404_ = v_isSharedCheck_2418_;
goto v_resetjp_2402_;
}
v_resetjp_2402_:
{
lean_object* v_fst_2405_; lean_object* v_snd_2406_; lean_object* v___x_2408_; uint8_t v_isShared_2409_; uint8_t v_isSharedCheck_2417_; 
v_fst_2405_ = lean_ctor_get(v_p_2399_, 0);
v_snd_2406_ = lean_ctor_get(v_p_2399_, 1);
v_isSharedCheck_2417_ = !lean_is_exclusive(v_p_2399_);
if (v_isSharedCheck_2417_ == 0)
{
v___x_2408_ = v_p_2399_;
v_isShared_2409_ = v_isSharedCheck_2417_;
goto v_resetjp_2407_;
}
else
{
lean_inc(v_snd_2406_);
lean_inc(v_fst_2405_);
lean_dec(v_p_2399_);
v___x_2408_ = lean_box(0);
v_isShared_2409_ = v_isSharedCheck_2417_;
goto v_resetjp_2407_;
}
v_resetjp_2407_:
{
lean_object* v___x_2411_; 
lean_inc(v_fst_2405_);
if (v_isShared_2404_ == 0)
{
lean_ctor_set_tag(v___x_2403_, 1);
lean_ctor_set(v___x_2403_, 1, v_fst_2400_);
lean_ctor_set(v___x_2403_, 0, v_fst_2405_);
v___x_2411_ = v___x_2403_;
goto v_reusejp_2410_;
}
else
{
lean_object* v_reuseFailAlloc_2416_; 
v_reuseFailAlloc_2416_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2416_, 0, v_fst_2405_);
lean_ctor_set(v_reuseFailAlloc_2416_, 1, v_fst_2400_);
v___x_2411_ = v_reuseFailAlloc_2416_;
goto v_reusejp_2410_;
}
v_reusejp_2410_:
{
lean_object* v___x_2412_; lean_object* v___x_2414_; 
v___x_2412_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_2405_, v_snd_2406_, v_snd_2401_);
if (v_isShared_2409_ == 0)
{
lean_ctor_set(v___x_2408_, 1, v___x_2412_);
lean_ctor_set(v___x_2408_, 0, v___x_2411_);
v___x_2414_ = v___x_2408_;
goto v_reusejp_2413_;
}
else
{
lean_object* v_reuseFailAlloc_2415_; 
v_reuseFailAlloc_2415_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2415_, 0, v___x_2411_);
lean_ctor_set(v_reuseFailAlloc_2415_, 1, v___x_2412_);
v___x_2414_ = v_reuseFailAlloc_2415_;
goto v_reusejp_2413_;
}
v_reusejp_2413_:
{
return v___x_2414_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg(lean_object* v_init_2419_, lean_object* v_x_2420_){
_start:
{
if (lean_obj_tag(v_x_2420_) == 0)
{
lean_object* v_k_2421_; lean_object* v_v_2422_; lean_object* v_l_2423_; lean_object* v_r_2424_; lean_object* v___x_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; 
v_k_2421_ = lean_ctor_get(v_x_2420_, 1);
v_v_2422_ = lean_ctor_get(v_x_2420_, 2);
v_l_2423_ = lean_ctor_get(v_x_2420_, 3);
v_r_2424_ = lean_ctor_get(v_x_2420_, 4);
v___x_2425_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg(v_init_2419_, v_l_2423_);
lean_inc(v_v_2422_);
lean_inc(v_k_2421_);
v___x_2426_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2426_, 0, v_k_2421_);
lean_ctor_set(v___x_2426_, 1, v_v_2422_);
v___x_2427_ = lean_array_push(v___x_2425_, v___x_2426_);
v_init_2419_ = v___x_2427_;
v_x_2420_ = v_r_2424_;
goto _start;
}
else
{
return v_init_2419_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg___boxed(lean_object* v_init_2429_, lean_object* v_x_2430_){
_start:
{
lean_object* v_res_2431_; 
v_res_2431_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg(v_init_2429_, v_x_2430_);
lean_dec(v_x_2430_);
return v_res_2431_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5___redArg(lean_object* v_snd_2432_, lean_object* v_as_2433_, size_t v_i_2434_, size_t v_stop_2435_, lean_object* v_b_2436_){
_start:
{
lean_object* v___y_2438_; uint8_t v___x_2442_; 
v___x_2442_ = lean_usize_dec_eq(v_i_2434_, v_stop_2435_);
if (v___x_2442_ == 0)
{
lean_object* v___x_2443_; lean_object* v___x_2444_; 
v___x_2443_ = lean_array_uget_borrowed(v_as_2433_, v_i_2434_);
v___x_2444_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_snd_2432_, v___x_2443_);
if (lean_obj_tag(v___x_2444_) == 0)
{
v___y_2438_ = v_b_2436_;
goto v___jp_2437_;
}
else
{
lean_object* v_val_2445_; lean_object* v___x_2446_; lean_object* v___x_2447_; 
v_val_2445_ = lean_ctor_get(v___x_2444_, 0);
lean_inc(v_val_2445_);
lean_dec_ref_known(v___x_2444_, 1);
lean_inc(v___x_2443_);
v___x_2446_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2446_, 0, v___x_2443_);
lean_ctor_set(v___x_2446_, 1, v_val_2445_);
v___x_2447_ = lean_array_push(v_b_2436_, v___x_2446_);
v___y_2438_ = v___x_2447_;
goto v___jp_2437_;
}
}
else
{
return v_b_2436_;
}
v___jp_2437_:
{
size_t v___x_2439_; size_t v___x_2440_; 
v___x_2439_ = ((size_t)1ULL);
v___x_2440_ = lean_usize_add(v_i_2434_, v___x_2439_);
v_i_2434_ = v___x_2440_;
v_b_2436_ = v___y_2438_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5___redArg___boxed(lean_object* v_snd_2448_, lean_object* v_as_2449_, lean_object* v_i_2450_, lean_object* v_stop_2451_, lean_object* v_b_2452_){
_start:
{
size_t v_i_boxed_2453_; size_t v_stop_boxed_2454_; lean_object* v_res_2455_; 
v_i_boxed_2453_ = lean_unbox_usize(v_i_2450_);
lean_dec(v_i_2450_);
v_stop_boxed_2454_ = lean_unbox_usize(v_stop_2451_);
lean_dec(v_stop_2451_);
v_res_2455_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5___redArg(v_snd_2448_, v_as_2449_, v_i_boxed_2453_, v_stop_boxed_2454_, v_b_2452_);
lean_dec_ref(v_as_2449_);
lean_dec(v_snd_2448_);
return v_res_2455_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3___redArg(lean_object* v_snd_2456_, lean_object* v_as_2457_, lean_object* v_start_2458_, lean_object* v_stop_2459_){
_start:
{
lean_object* v___x_2460_; uint8_t v___x_2461_; 
v___x_2460_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___redArg___lam__2___closed__0));
v___x_2461_ = lean_nat_dec_lt(v_start_2458_, v_stop_2459_);
if (v___x_2461_ == 0)
{
return v___x_2460_;
}
else
{
lean_object* v___x_2462_; uint8_t v___x_2463_; 
v___x_2462_ = lean_array_get_size(v_as_2457_);
v___x_2463_ = lean_nat_dec_le(v_stop_2459_, v___x_2462_);
if (v___x_2463_ == 0)
{
uint8_t v___x_2464_; 
v___x_2464_ = lean_nat_dec_lt(v_start_2458_, v___x_2462_);
if (v___x_2464_ == 0)
{
return v___x_2460_;
}
else
{
size_t v___x_2465_; size_t v___x_2466_; lean_object* v___x_2467_; 
v___x_2465_ = lean_usize_of_nat(v_start_2458_);
v___x_2466_ = lean_usize_of_nat(v___x_2462_);
v___x_2467_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5___redArg(v_snd_2456_, v_as_2457_, v___x_2465_, v___x_2466_, v___x_2460_);
return v___x_2467_;
}
}
else
{
size_t v___x_2468_; size_t v___x_2469_; lean_object* v___x_2470_; 
v___x_2468_ = lean_usize_of_nat(v_start_2458_);
v___x_2469_ = lean_usize_of_nat(v_stop_2459_);
v___x_2470_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5___redArg(v_snd_2456_, v_as_2457_, v___x_2468_, v___x_2469_, v___x_2460_);
return v___x_2470_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3___redArg___boxed(lean_object* v_snd_2471_, lean_object* v_as_2472_, lean_object* v_start_2473_, lean_object* v_stop_2474_){
_start:
{
lean_object* v_res_2475_; 
v_res_2475_ = l_Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3___redArg(v_snd_2471_, v_as_2472_, v_start_2473_, v_stop_2474_);
lean_dec(v_stop_2474_);
lean_dec(v_start_2473_);
lean_dec_ref(v_as_2472_);
lean_dec(v_snd_2471_);
return v_res_2475_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2_spec__3___redArg(lean_object* v_hi_2476_, lean_object* v_pivot_2477_, lean_object* v_as_2478_, lean_object* v_i_2479_, lean_object* v_k_2480_){
_start:
{
uint8_t v___x_2481_; 
v___x_2481_ = lean_nat_dec_lt(v_k_2480_, v_hi_2476_);
if (v___x_2481_ == 0)
{
lean_object* v___x_2482_; lean_object* v___x_2483_; 
lean_dec(v_k_2480_);
v___x_2482_ = lean_array_fswap(v_as_2478_, v_i_2479_, v_hi_2476_);
v___x_2483_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2483_, 0, v_i_2479_);
lean_ctor_set(v___x_2483_, 1, v___x_2482_);
return v___x_2483_;
}
else
{
lean_object* v___x_2484_; lean_object* v_fst_2485_; lean_object* v_fst_2486_; uint8_t v___x_2487_; 
v___x_2484_ = lean_array_fget_borrowed(v_as_2478_, v_k_2480_);
v_fst_2485_ = lean_ctor_get(v___x_2484_, 0);
v_fst_2486_ = lean_ctor_get(v_pivot_2477_, 0);
v___x_2487_ = l_Lean_Name_quickLt(v_fst_2485_, v_fst_2486_);
if (v___x_2487_ == 0)
{
lean_object* v___x_2488_; lean_object* v___x_2489_; 
v___x_2488_ = lean_unsigned_to_nat(1u);
v___x_2489_ = lean_nat_add(v_k_2480_, v___x_2488_);
lean_dec(v_k_2480_);
v_k_2480_ = v___x_2489_;
goto _start;
}
else
{
lean_object* v___x_2491_; lean_object* v___x_2492_; lean_object* v___x_2493_; lean_object* v___x_2494_; 
v___x_2491_ = lean_array_fswap(v_as_2478_, v_i_2479_, v_k_2480_);
v___x_2492_ = lean_unsigned_to_nat(1u);
v___x_2493_ = lean_nat_add(v_i_2479_, v___x_2492_);
lean_dec(v_i_2479_);
v___x_2494_ = lean_nat_add(v_k_2480_, v___x_2492_);
lean_dec(v_k_2480_);
v_as_2478_ = v___x_2491_;
v_i_2479_ = v___x_2493_;
v_k_2480_ = v___x_2494_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2_spec__3___redArg___boxed(lean_object* v_hi_2496_, lean_object* v_pivot_2497_, lean_object* v_as_2498_, lean_object* v_i_2499_, lean_object* v_k_2500_){
_start:
{
lean_object* v_res_2501_; 
v_res_2501_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2_spec__3___redArg(v_hi_2496_, v_pivot_2497_, v_as_2498_, v_i_2499_, v_k_2500_);
lean_dec_ref(v_pivot_2497_);
lean_dec(v_hi_2496_);
return v_res_2501_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg___lam__0(lean_object* v_a_2502_, lean_object* v_b_2503_){
_start:
{
lean_object* v_fst_2504_; lean_object* v_fst_2505_; uint8_t v___x_2506_; 
v_fst_2504_ = lean_ctor_get(v_a_2502_, 0);
v_fst_2505_ = lean_ctor_get(v_b_2503_, 0);
v___x_2506_ = l_Lean_Name_quickLt(v_fst_2504_, v_fst_2505_);
return v___x_2506_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg___lam__0___boxed(lean_object* v_a_2507_, lean_object* v_b_2508_){
_start:
{
uint8_t v_res_2509_; lean_object* v_r_2510_; 
v_res_2509_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg___lam__0(v_a_2507_, v_b_2508_);
lean_dec_ref(v_b_2508_);
lean_dec_ref(v_a_2507_);
v_r_2510_ = lean_box(v_res_2509_);
return v_r_2510_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg(lean_object* v_n_2511_, lean_object* v_as_2512_, lean_object* v_lo_2513_, lean_object* v_hi_2514_){
_start:
{
lean_object* v___y_2516_; uint8_t v___x_2526_; 
v___x_2526_ = lean_nat_dec_lt(v_lo_2513_, v_hi_2514_);
if (v___x_2526_ == 0)
{
lean_dec(v_lo_2513_);
return v_as_2512_;
}
else
{
lean_object* v___x_2527_; lean_object* v___x_2528_; lean_object* v_mid_2529_; lean_object* v___y_2531_; lean_object* v___y_2537_; lean_object* v___x_2542_; lean_object* v___x_2543_; uint8_t v___x_2544_; 
v___x_2527_ = lean_nat_add(v_lo_2513_, v_hi_2514_);
v___x_2528_ = lean_unsigned_to_nat(1u);
v_mid_2529_ = lean_nat_shiftr(v___x_2527_, v___x_2528_);
lean_dec(v___x_2527_);
v___x_2542_ = lean_array_fget_borrowed(v_as_2512_, v_mid_2529_);
v___x_2543_ = lean_array_fget_borrowed(v_as_2512_, v_lo_2513_);
v___x_2544_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg___lam__0(v___x_2542_, v___x_2543_);
if (v___x_2544_ == 0)
{
v___y_2537_ = v_as_2512_;
goto v___jp_2536_;
}
else
{
lean_object* v___x_2545_; 
v___x_2545_ = lean_array_fswap(v_as_2512_, v_lo_2513_, v_mid_2529_);
v___y_2537_ = v___x_2545_;
goto v___jp_2536_;
}
v___jp_2530_:
{
lean_object* v___x_2532_; lean_object* v___x_2533_; uint8_t v___x_2534_; 
v___x_2532_ = lean_array_fget_borrowed(v___y_2531_, v_mid_2529_);
v___x_2533_ = lean_array_fget_borrowed(v___y_2531_, v_hi_2514_);
v___x_2534_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg___lam__0(v___x_2532_, v___x_2533_);
if (v___x_2534_ == 0)
{
lean_dec(v_mid_2529_);
v___y_2516_ = v___y_2531_;
goto v___jp_2515_;
}
else
{
lean_object* v___x_2535_; 
v___x_2535_ = lean_array_fswap(v___y_2531_, v_mid_2529_, v_hi_2514_);
lean_dec(v_mid_2529_);
v___y_2516_ = v___x_2535_;
goto v___jp_2515_;
}
}
v___jp_2536_:
{
lean_object* v___x_2538_; lean_object* v___x_2539_; uint8_t v___x_2540_; 
v___x_2538_ = lean_array_fget_borrowed(v___y_2537_, v_hi_2514_);
v___x_2539_ = lean_array_fget_borrowed(v___y_2537_, v_lo_2513_);
v___x_2540_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg___lam__0(v___x_2538_, v___x_2539_);
if (v___x_2540_ == 0)
{
v___y_2531_ = v___y_2537_;
goto v___jp_2530_;
}
else
{
lean_object* v___x_2541_; 
v___x_2541_ = lean_array_fswap(v___y_2537_, v_lo_2513_, v_hi_2514_);
v___y_2531_ = v___x_2541_;
goto v___jp_2530_;
}
}
}
v___jp_2515_:
{
lean_object* v_pivot_2517_; lean_object* v___x_2518_; lean_object* v_fst_2519_; lean_object* v_snd_2520_; uint8_t v___x_2521_; 
v_pivot_2517_ = lean_array_fget(v___y_2516_, v_hi_2514_);
lean_inc_n(v_lo_2513_, 2);
v___x_2518_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2_spec__3___redArg(v_hi_2514_, v_pivot_2517_, v___y_2516_, v_lo_2513_, v_lo_2513_);
lean_dec(v_pivot_2517_);
v_fst_2519_ = lean_ctor_get(v___x_2518_, 0);
lean_inc(v_fst_2519_);
v_snd_2520_ = lean_ctor_get(v___x_2518_, 1);
lean_inc(v_snd_2520_);
lean_dec_ref(v___x_2518_);
v___x_2521_ = lean_nat_dec_le(v_hi_2514_, v_fst_2519_);
if (v___x_2521_ == 0)
{
lean_object* v___x_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; 
v___x_2522_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg(v_n_2511_, v_snd_2520_, v_lo_2513_, v_fst_2519_);
v___x_2523_ = lean_unsigned_to_nat(1u);
v___x_2524_ = lean_nat_add(v_fst_2519_, v___x_2523_);
lean_dec(v_fst_2519_);
v_as_2512_ = v___x_2522_;
v_lo_2513_ = v___x_2524_;
goto _start;
}
else
{
lean_dec(v_fst_2519_);
lean_dec(v_lo_2513_);
return v_snd_2520_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg___boxed(lean_object* v_n_2546_, lean_object* v_as_2547_, lean_object* v_lo_2548_, lean_object* v_hi_2549_){
_start:
{
lean_object* v_res_2550_; 
v_res_2550_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg(v_n_2546_, v_as_2547_, v_lo_2548_, v_hi_2549_);
lean_dec(v_hi_2549_);
lean_dec(v_n_2546_);
return v_res_2550_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0___redArg(lean_object* v_filterExport_2551_, lean_object* v_env_2552_, lean_object* v_as_2553_, size_t v_i_2554_, size_t v_stop_2555_, lean_object* v_b_2556_){
_start:
{
lean_object* v___y_2558_; uint8_t v___x_2562_; 
v___x_2562_ = lean_usize_dec_eq(v_i_2554_, v_stop_2555_);
if (v___x_2562_ == 0)
{
lean_object* v___x_2563_; lean_object* v_fst_2564_; lean_object* v_snd_2565_; lean_object* v___x_2566_; uint8_t v___x_2567_; 
v___x_2563_ = lean_array_uget_borrowed(v_as_2553_, v_i_2554_);
v_fst_2564_ = lean_ctor_get(v___x_2563_, 0);
v_snd_2565_ = lean_ctor_get(v___x_2563_, 1);
lean_inc_ref(v_filterExport_2551_);
lean_inc(v_snd_2565_);
lean_inc(v_fst_2564_);
lean_inc_ref(v_env_2552_);
v___x_2566_ = lean_apply_3(v_filterExport_2551_, v_env_2552_, v_fst_2564_, v_snd_2565_);
v___x_2567_ = lean_unbox(v___x_2566_);
if (v___x_2567_ == 0)
{
v___y_2558_ = v_b_2556_;
goto v___jp_2557_;
}
else
{
lean_object* v___x_2568_; 
lean_inc(v___x_2563_);
v___x_2568_ = lean_array_push(v_b_2556_, v___x_2563_);
v___y_2558_ = v___x_2568_;
goto v___jp_2557_;
}
}
else
{
lean_dec_ref(v_env_2552_);
lean_dec_ref(v_filterExport_2551_);
return v_b_2556_;
}
v___jp_2557_:
{
size_t v___x_2559_; size_t v___x_2560_; 
v___x_2559_ = ((size_t)1ULL);
v___x_2560_ = lean_usize_add(v_i_2554_, v___x_2559_);
v_i_2554_ = v___x_2560_;
v_b_2556_ = v___y_2558_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0___redArg___boxed(lean_object* v_filterExport_2569_, lean_object* v_env_2570_, lean_object* v_as_2571_, lean_object* v_i_2572_, lean_object* v_stop_2573_, lean_object* v_b_2574_){
_start:
{
size_t v_i_boxed_2575_; size_t v_stop_boxed_2576_; lean_object* v_res_2577_; 
v_i_boxed_2575_ = lean_unbox_usize(v_i_2572_);
lean_dec(v_i_2572_);
v_stop_boxed_2576_ = lean_unbox_usize(v_stop_2573_);
lean_dec(v_stop_2573_);
v_res_2577_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0___redArg(v_filterExport_2569_, v_env_2570_, v_as_2571_, v_i_boxed_2575_, v_stop_boxed_2576_, v_b_2574_);
lean_dec_ref(v_as_2571_);
return v_res_2577_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__1(lean_object* v_filterExport_2578_, uint8_t v_preserveOrder_2579_, lean_object* v_env_2580_, lean_object* v_x_2581_){
_start:
{
lean_object* v___y_2583_; 
if (v_preserveOrder_2579_ == 0)
{
lean_object* v_snd_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; lean_object* v_r_2602_; lean_object* v___x_2603_; lean_object* v___y_2605_; lean_object* v___y_2606_; uint8_t v___x_2608_; 
v_snd_2599_ = lean_ctor_get(v_x_2581_, 1);
lean_inc(v_snd_2599_);
lean_dec_ref(v_x_2581_);
v___x_2600_ = lean_unsigned_to_nat(0u);
v___x_2601_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___redArg___lam__2___closed__0));
v_r_2602_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg(v___x_2601_, v_snd_2599_);
lean_dec(v_snd_2599_);
v___x_2603_ = lean_array_get_size(v_r_2602_);
v___x_2608_ = lean_nat_dec_eq(v___x_2603_, v___x_2600_);
if (v___x_2608_ == 0)
{
lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v___y_2612_; uint8_t v___x_2614_; 
v___x_2609_ = lean_unsigned_to_nat(1u);
v___x_2610_ = lean_nat_sub(v___x_2603_, v___x_2609_);
v___x_2614_ = lean_nat_dec_le(v___x_2600_, v___x_2610_);
if (v___x_2614_ == 0)
{
lean_inc(v___x_2610_);
v___y_2612_ = v___x_2610_;
goto v___jp_2611_;
}
else
{
v___y_2612_ = v___x_2600_;
goto v___jp_2611_;
}
v___jp_2611_:
{
uint8_t v___x_2613_; 
v___x_2613_ = lean_nat_dec_le(v___y_2612_, v___x_2610_);
if (v___x_2613_ == 0)
{
lean_dec(v___x_2610_);
lean_inc(v___y_2612_);
v___y_2605_ = v___y_2612_;
v___y_2606_ = v___y_2612_;
goto v___jp_2604_;
}
else
{
v___y_2605_ = v___y_2612_;
v___y_2606_ = v___x_2610_;
goto v___jp_2604_;
}
}
}
else
{
v___y_2583_ = v_r_2602_;
goto v___jp_2582_;
}
v___jp_2604_:
{
lean_object* v___x_2607_; 
v___x_2607_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg(v___x_2603_, v_r_2602_, v___y_2605_, v___y_2606_);
lean_dec(v___y_2606_);
v___y_2583_ = v___x_2607_;
goto v___jp_2582_;
}
}
else
{
lean_object* v_fst_2615_; lean_object* v_snd_2616_; lean_object* v___x_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; 
v_fst_2615_ = lean_ctor_get(v_x_2581_, 0);
lean_inc(v_fst_2615_);
v_snd_2616_ = lean_ctor_get(v_x_2581_, 1);
lean_inc(v_snd_2616_);
lean_dec_ref(v_x_2581_);
v___x_2617_ = lean_array_mk(v_fst_2615_);
v___x_2618_ = l_Array_reverse___redArg(v___x_2617_);
v___x_2619_ = lean_unsigned_to_nat(0u);
v___x_2620_ = lean_array_get_size(v___x_2618_);
v___x_2621_ = l_Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3___redArg(v_snd_2616_, v___x_2618_, v___x_2619_, v___x_2620_);
lean_dec_ref(v___x_2618_);
lean_dec(v_snd_2616_);
v___y_2583_ = v___x_2621_;
goto v___jp_2582_;
}
v___jp_2582_:
{
lean_object* v___x_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; uint8_t v___x_2587_; 
v___x_2584_ = lean_unsigned_to_nat(0u);
v___x_2585_ = lean_array_get_size(v___y_2583_);
v___x_2586_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___redArg___lam__2___closed__0));
v___x_2587_ = lean_nat_dec_lt(v___x_2584_, v___x_2585_);
if (v___x_2587_ == 0)
{
lean_object* v___x_2588_; 
lean_dec_ref(v_env_2580_);
lean_dec_ref(v_filterExport_2578_);
v___x_2588_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2588_, 0, v___x_2586_);
lean_ctor_set(v___x_2588_, 1, v___x_2586_);
lean_ctor_set(v___x_2588_, 2, v___y_2583_);
return v___x_2588_;
}
else
{
uint8_t v___x_2589_; 
v___x_2589_ = lean_nat_dec_le(v___x_2585_, v___x_2585_);
if (v___x_2589_ == 0)
{
if (v___x_2587_ == 0)
{
lean_object* v___x_2590_; 
lean_dec_ref(v_env_2580_);
lean_dec_ref(v_filterExport_2578_);
v___x_2590_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2590_, 0, v___x_2586_);
lean_ctor_set(v___x_2590_, 1, v___x_2586_);
lean_ctor_set(v___x_2590_, 2, v___y_2583_);
return v___x_2590_;
}
else
{
size_t v___x_2591_; size_t v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; 
v___x_2591_ = ((size_t)0ULL);
v___x_2592_ = lean_usize_of_nat(v___x_2585_);
v___x_2593_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0___redArg(v_filterExport_2578_, v_env_2580_, v___y_2583_, v___x_2591_, v___x_2592_, v___x_2586_);
lean_inc_ref(v___x_2593_);
v___x_2594_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2594_, 0, v___x_2593_);
lean_ctor_set(v___x_2594_, 1, v___x_2593_);
lean_ctor_set(v___x_2594_, 2, v___y_2583_);
return v___x_2594_;
}
}
else
{
size_t v___x_2595_; size_t v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; 
v___x_2595_ = ((size_t)0ULL);
v___x_2596_ = lean_usize_of_nat(v___x_2585_);
v___x_2597_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0___redArg(v_filterExport_2578_, v_env_2580_, v___y_2583_, v___x_2595_, v___x_2596_, v___x_2586_);
lean_inc_ref(v___x_2597_);
v___x_2598_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2598_, 0, v___x_2597_);
lean_ctor_set(v___x_2598_, 1, v___x_2597_);
lean_ctor_set(v___x_2598_, 2, v___y_2583_);
return v___x_2598_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__1___boxed(lean_object* v_filterExport_2622_, lean_object* v_preserveOrder_2623_, lean_object* v_env_2624_, lean_object* v_x_2625_){
_start:
{
uint8_t v_preserveOrder_boxed_2626_; lean_object* v_res_2627_; 
v_preserveOrder_boxed_2626_ = lean_unbox(v_preserveOrder_2623_);
v_res_2627_ = l_Lean_registerParametricAttributeExt___redArg___lam__1(v_filterExport_2622_, v_preserveOrder_boxed_2626_, v_env_2624_, v_x_2625_);
return v_res_2627_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__2(lean_object* v_x_2637_){
_start:
{
lean_object* v_snd_2638_; lean_object* v___x_2640_; uint8_t v_isShared_2641_; uint8_t v_isSharedCheck_2652_; 
v_snd_2638_ = lean_ctor_get(v_x_2637_, 1);
v_isSharedCheck_2652_ = !lean_is_exclusive(v_x_2637_);
if (v_isSharedCheck_2652_ == 0)
{
lean_object* v_unused_2653_; 
v_unused_2653_ = lean_ctor_get(v_x_2637_, 0);
lean_dec(v_unused_2653_);
v___x_2640_ = v_x_2637_;
v_isShared_2641_ = v_isSharedCheck_2652_;
goto v_resetjp_2639_;
}
else
{
lean_inc(v_snd_2638_);
lean_dec(v_x_2637_);
v___x_2640_ = lean_box(0);
v_isShared_2641_ = v_isSharedCheck_2652_;
goto v_resetjp_2639_;
}
v_resetjp_2639_:
{
lean_object* v___x_2642_; lean_object* v___y_2644_; 
v___x_2642_ = ((lean_object*)(l_Lean_registerParametricAttributeExt___redArg___lam__2___closed__3));
if (lean_obj_tag(v_snd_2638_) == 0)
{
lean_object* v_size_2650_; 
v_size_2650_ = lean_ctor_get(v_snd_2638_, 0);
lean_inc(v_size_2650_);
lean_dec_ref_known(v_snd_2638_, 5);
v___y_2644_ = v_size_2650_;
goto v___jp_2643_;
}
else
{
lean_object* v___x_2651_; 
v___x_2651_ = lean_unsigned_to_nat(0u);
v___y_2644_ = v___x_2651_;
goto v___jp_2643_;
}
v___jp_2643_:
{
lean_object* v___x_2645_; lean_object* v___x_2646_; lean_object* v___x_2648_; 
v___x_2645_ = l_Nat_reprFast(v___y_2644_);
v___x_2646_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2646_, 0, v___x_2645_);
if (v_isShared_2641_ == 0)
{
lean_ctor_set_tag(v___x_2640_, 5);
lean_ctor_set(v___x_2640_, 1, v___x_2646_);
lean_ctor_set(v___x_2640_, 0, v___x_2642_);
v___x_2648_ = v___x_2640_;
goto v_reusejp_2647_;
}
else
{
lean_object* v_reuseFailAlloc_2649_; 
v_reuseFailAlloc_2649_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2649_, 0, v___x_2642_);
lean_ctor_set(v_reuseFailAlloc_2649_, 1, v___x_2646_);
v___x_2648_ = v_reuseFailAlloc_2649_;
goto v_reusejp_2647_;
}
v_reusejp_2647_:
{
return v___x_2648_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__3(lean_object* v_x_2654_){
_start:
{
lean_object* v___x_2655_; 
v___x_2655_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___redArg___lam__2___closed__0));
return v___x_2655_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__3___boxed(lean_object* v_x_2656_){
_start:
{
lean_object* v_res_2657_; 
v_res_2657_ = l_Lean_registerParametricAttributeExt___redArg___lam__3(v_x_2656_);
lean_dec_ref(v_x_2656_);
return v_res_2657_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__4(lean_object* v___x_2658_){
_start:
{
lean_object* v___x_2660_; 
v___x_2660_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2660_, 0, v___x_2658_);
return v___x_2660_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__4___boxed(lean_object* v___x_2661_, lean_object* v___y_2662_){
_start:
{
lean_object* v_res_2663_; 
v_res_2663_ = l_Lean_registerParametricAttributeExt___redArg___lam__4(v___x_2661_);
return v_res_2663_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__5(lean_object* v___x_2664_, lean_object* v_x_2665_, lean_object* v___y_2666_){
_start:
{
lean_object* v___x_2668_; 
v___x_2668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2668_, 0, v___x_2664_);
return v___x_2668_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__5___boxed(lean_object* v___x_2669_, lean_object* v_x_2670_, lean_object* v___y_2671_, lean_object* v___y_2672_){
_start:
{
lean_object* v_res_2673_; 
v_res_2673_ = l_Lean_registerParametricAttributeExt___redArg___lam__5(v___x_2669_, v_x_2670_, v___y_2671_);
lean_dec_ref(v___y_2671_);
lean_dec_ref(v_x_2670_);
return v_res_2673_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg(lean_object* v_ref_2684_, uint8_t v_preserveOrder_2685_, lean_object* v_filterExport_2686_){
_start:
{
lean_object* v___f_2688_; lean_object* v___x_2689_; lean_object* v___f_2690_; lean_object* v___f_2691_; lean_object* v___f_2692_; lean_object* v___f_2693_; lean_object* v___f_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; lean_object* v___x_2699_; 
v___f_2688_ = ((lean_object*)(l_Lean_registerParametricAttributeExt___redArg___closed__0));
v___x_2689_ = lean_box(v_preserveOrder_2685_);
v___f_2690_ = lean_alloc_closure((void*)(l_Lean_registerParametricAttributeExt___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_2690_, 0, v_filterExport_2686_);
lean_closure_set(v___f_2690_, 1, v___x_2689_);
v___f_2691_ = ((lean_object*)(l_Lean_registerParametricAttributeExt___redArg___closed__1));
v___f_2692_ = ((lean_object*)(l_Lean_registerParametricAttributeExt___redArg___closed__2));
v___f_2693_ = ((lean_object*)(l_Lean_registerParametricAttributeExt___redArg___closed__4));
v___f_2694_ = ((lean_object*)(l_Lean_registerParametricAttributeExt___redArg___closed__5));
v___x_2695_ = lean_box(2);
v___x_2696_ = lean_box(0);
v___x_2697_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_2697_, 0, v_ref_2684_);
lean_ctor_set(v___x_2697_, 1, v___f_2693_);
lean_ctor_set(v___x_2697_, 2, v___f_2694_);
lean_ctor_set(v___x_2697_, 3, v___f_2688_);
lean_ctor_set(v___x_2697_, 4, v___f_2690_);
lean_ctor_set(v___x_2697_, 5, v___f_2691_);
lean_ctor_set(v___x_2697_, 6, v___x_2695_);
lean_ctor_set(v___x_2697_, 7, v___x_2696_);
v___x_2698_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2698_, 0, v___x_2697_);
lean_ctor_set(v___x_2698_, 1, v___f_2692_);
v___x_2699_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_2698_);
return v___x_2699_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___boxed(lean_object* v_ref_2700_, lean_object* v_preserveOrder_2701_, lean_object* v_filterExport_2702_, lean_object* v_a_2703_){
_start:
{
uint8_t v_preserveOrder_boxed_2704_; lean_object* v_res_2705_; 
v_preserveOrder_boxed_2704_ = lean_unbox(v_preserveOrder_2701_);
v_res_2705_ = l_Lean_registerParametricAttributeExt___redArg(v_ref_2700_, v_preserveOrder_boxed_2704_, v_filterExport_2702_);
return v_res_2705_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt(lean_object* v_00_u03b1_2706_, lean_object* v_ref_2707_, uint8_t v_preserveOrder_2708_, lean_object* v_filterExport_2709_){
_start:
{
lean_object* v___x_2711_; 
v___x_2711_ = l_Lean_registerParametricAttributeExt___redArg(v_ref_2707_, v_preserveOrder_2708_, v_filterExport_2709_);
return v___x_2711_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___boxed(lean_object* v_00_u03b1_2712_, lean_object* v_ref_2713_, lean_object* v_preserveOrder_2714_, lean_object* v_filterExport_2715_, lean_object* v_a_2716_){
_start:
{
uint8_t v_preserveOrder_boxed_2717_; lean_object* v_res_2718_; 
v_preserveOrder_boxed_2717_ = lean_unbox(v_preserveOrder_2714_);
v_res_2718_ = l_Lean_registerParametricAttributeExt(v_00_u03b1_2712_, v_ref_2713_, v_preserveOrder_boxed_2717_, v_filterExport_2715_);
return v_res_2718_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0(lean_object* v_00_u03b1_2719_, lean_object* v_filterExport_2720_, lean_object* v_env_2721_, lean_object* v_as_2722_, size_t v_i_2723_, size_t v_stop_2724_, lean_object* v_b_2725_){
_start:
{
lean_object* v___x_2726_; 
v___x_2726_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0___redArg(v_filterExport_2720_, v_env_2721_, v_as_2722_, v_i_2723_, v_stop_2724_, v_b_2725_);
return v___x_2726_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0___boxed(lean_object* v_00_u03b1_2727_, lean_object* v_filterExport_2728_, lean_object* v_env_2729_, lean_object* v_as_2730_, lean_object* v_i_2731_, lean_object* v_stop_2732_, lean_object* v_b_2733_){
_start:
{
size_t v_i_boxed_2734_; size_t v_stop_boxed_2735_; lean_object* v_res_2736_; 
v_i_boxed_2734_ = lean_unbox_usize(v_i_2731_);
lean_dec(v_i_2731_);
v_stop_boxed_2735_ = lean_unbox_usize(v_stop_2732_);
lean_dec(v_stop_2732_);
v_res_2736_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0(v_00_u03b1_2727_, v_filterExport_2728_, v_env_2729_, v_as_2730_, v_i_boxed_2734_, v_stop_boxed_2735_, v_b_2733_);
lean_dec_ref(v_as_2730_);
return v_res_2736_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1___redArg(lean_object* v_init_2737_, lean_object* v_t_2738_){
_start:
{
lean_object* v___x_2739_; 
v___x_2739_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg(v_init_2737_, v_t_2738_);
return v___x_2739_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1___redArg___boxed(lean_object* v_init_2740_, lean_object* v_t_2741_){
_start:
{
lean_object* v_res_2742_; 
v_res_2742_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1___redArg(v_init_2740_, v_t_2741_);
lean_dec(v_t_2741_);
return v_res_2742_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1(lean_object* v_00_u03b1_2743_, lean_object* v_init_2744_, lean_object* v_t_2745_){
_start:
{
lean_object* v___x_2746_; 
v___x_2746_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg(v_init_2744_, v_t_2745_);
return v___x_2746_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1___boxed(lean_object* v_00_u03b1_2747_, lean_object* v_init_2748_, lean_object* v_t_2749_){
_start:
{
lean_object* v_res_2750_; 
v_res_2750_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1(v_00_u03b1_2747_, v_init_2748_, v_t_2749_);
lean_dec(v_t_2749_);
return v_res_2750_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2(lean_object* v_00_u03b1_2751_, lean_object* v_n_2752_, lean_object* v_as_2753_, lean_object* v_lo_2754_, lean_object* v_hi_2755_, lean_object* v_w_2756_, lean_object* v_hlo_2757_, lean_object* v_hhi_2758_){
_start:
{
lean_object* v___x_2759_; 
v___x_2759_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg(v_n_2752_, v_as_2753_, v_lo_2754_, v_hi_2755_);
return v___x_2759_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___boxed(lean_object* v_00_u03b1_2760_, lean_object* v_n_2761_, lean_object* v_as_2762_, lean_object* v_lo_2763_, lean_object* v_hi_2764_, lean_object* v_w_2765_, lean_object* v_hlo_2766_, lean_object* v_hhi_2767_){
_start:
{
lean_object* v_res_2768_; 
v_res_2768_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2(v_00_u03b1_2760_, v_n_2761_, v_as_2762_, v_lo_2763_, v_hi_2764_, v_w_2765_, v_hlo_2766_, v_hhi_2767_);
lean_dec(v_hi_2764_);
lean_dec(v_n_2761_);
return v_res_2768_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3(lean_object* v_00_u03b1_2769_, lean_object* v_snd_2770_, lean_object* v_as_2771_, lean_object* v_start_2772_, lean_object* v_stop_2773_){
_start:
{
lean_object* v___x_2774_; 
v___x_2774_ = l_Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3___redArg(v_snd_2770_, v_as_2771_, v_start_2772_, v_stop_2773_);
return v___x_2774_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3___boxed(lean_object* v_00_u03b1_2775_, lean_object* v_snd_2776_, lean_object* v_as_2777_, lean_object* v_start_2778_, lean_object* v_stop_2779_){
_start:
{
lean_object* v_res_2780_; 
v_res_2780_ = l_Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3(v_00_u03b1_2775_, v_snd_2776_, v_as_2777_, v_start_2778_, v_stop_2779_);
lean_dec(v_stop_2779_);
lean_dec(v_start_2778_);
lean_dec_ref(v_as_2777_);
lean_dec(v_snd_2776_);
return v_res_2780_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1(lean_object* v_00_u03b1_2781_, lean_object* v_init_2782_, lean_object* v_x_2783_){
_start:
{
lean_object* v___x_2784_; 
v___x_2784_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg(v_init_2782_, v_x_2783_);
return v___x_2784_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___boxed(lean_object* v_00_u03b1_2785_, lean_object* v_init_2786_, lean_object* v_x_2787_){
_start:
{
lean_object* v_res_2788_; 
v_res_2788_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1(v_00_u03b1_2785_, v_init_2786_, v_x_2787_);
lean_dec(v_x_2787_);
return v_res_2788_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2_spec__3(lean_object* v_00_u03b1_2789_, lean_object* v_n_2790_, lean_object* v_lo_2791_, lean_object* v_hi_2792_, lean_object* v_hhi_2793_, lean_object* v_pivot_2794_, lean_object* v_as_2795_, lean_object* v_i_2796_, lean_object* v_k_2797_, lean_object* v_ilo_2798_, lean_object* v_ik_2799_, lean_object* v_w_2800_){
_start:
{
lean_object* v___x_2801_; 
v___x_2801_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2_spec__3___redArg(v_hi_2792_, v_pivot_2794_, v_as_2795_, v_i_2796_, v_k_2797_);
return v___x_2801_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2_spec__3___boxed(lean_object* v_00_u03b1_2802_, lean_object* v_n_2803_, lean_object* v_lo_2804_, lean_object* v_hi_2805_, lean_object* v_hhi_2806_, lean_object* v_pivot_2807_, lean_object* v_as_2808_, lean_object* v_i_2809_, lean_object* v_k_2810_, lean_object* v_ilo_2811_, lean_object* v_ik_2812_, lean_object* v_w_2813_){
_start:
{
lean_object* v_res_2814_; 
v_res_2814_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2_spec__3(v_00_u03b1_2802_, v_n_2803_, v_lo_2804_, v_hi_2805_, v_hhi_2806_, v_pivot_2807_, v_as_2808_, v_i_2809_, v_k_2810_, v_ilo_2811_, v_ik_2812_, v_w_2813_);
lean_dec_ref(v_pivot_2807_);
lean_dec(v_hi_2805_);
lean_dec(v_lo_2804_);
lean_dec(v_n_2803_);
return v_res_2814_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5(lean_object* v_00_u03b1_2815_, lean_object* v_snd_2816_, lean_object* v_as_2817_, size_t v_i_2818_, size_t v_stop_2819_, lean_object* v_b_2820_){
_start:
{
lean_object* v___x_2821_; 
v___x_2821_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5___redArg(v_snd_2816_, v_as_2817_, v_i_2818_, v_stop_2819_, v_b_2820_);
return v___x_2821_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5___boxed(lean_object* v_00_u03b1_2822_, lean_object* v_snd_2823_, lean_object* v_as_2824_, lean_object* v_i_2825_, lean_object* v_stop_2826_, lean_object* v_b_2827_){
_start:
{
size_t v_i_boxed_2828_; size_t v_stop_boxed_2829_; lean_object* v_res_2830_; 
v_i_boxed_2828_ = lean_unbox_usize(v_i_2825_);
lean_dec(v_i_2825_);
v_stop_boxed_2829_ = lean_unbox_usize(v_stop_2826_);
lean_dec(v_stop_2826_);
v_res_2830_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5(v_00_u03b1_2822_, v_snd_2823_, v_as_2824_, v_i_boxed_2828_, v_stop_boxed_2829_, v_b_2827_);
lean_dec_ref(v_as_2824_);
lean_dec(v_snd_2823_);
return v_res_2830_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_registerParametricAttributeForExt_spec__0___redArg(lean_object* v_env_2831_, lean_object* v___y_2832_){
_start:
{
lean_object* v___x_2834_; lean_object* v_nextMacroScope_2835_; lean_object* v_ngen_2836_; lean_object* v_auxDeclNGen_2837_; lean_object* v_traceState_2838_; lean_object* v_recordedDeps_2839_; lean_object* v_messages_2840_; lean_object* v_infoState_2841_; lean_object* v_snapshotTasks_2842_; lean_object* v___x_2844_; uint8_t v_isShared_2845_; uint8_t v_isSharedCheck_2853_; 
v___x_2834_ = lean_st_ref_take(v___y_2832_);
v_nextMacroScope_2835_ = lean_ctor_get(v___x_2834_, 1);
v_ngen_2836_ = lean_ctor_get(v___x_2834_, 2);
v_auxDeclNGen_2837_ = lean_ctor_get(v___x_2834_, 3);
v_traceState_2838_ = lean_ctor_get(v___x_2834_, 4);
v_recordedDeps_2839_ = lean_ctor_get(v___x_2834_, 6);
v_messages_2840_ = lean_ctor_get(v___x_2834_, 7);
v_infoState_2841_ = lean_ctor_get(v___x_2834_, 8);
v_snapshotTasks_2842_ = lean_ctor_get(v___x_2834_, 9);
v_isSharedCheck_2853_ = !lean_is_exclusive(v___x_2834_);
if (v_isSharedCheck_2853_ == 0)
{
lean_object* v_unused_2854_; lean_object* v_unused_2855_; 
v_unused_2854_ = lean_ctor_get(v___x_2834_, 5);
lean_dec(v_unused_2854_);
v_unused_2855_ = lean_ctor_get(v___x_2834_, 0);
lean_dec(v_unused_2855_);
v___x_2844_ = v___x_2834_;
v_isShared_2845_ = v_isSharedCheck_2853_;
goto v_resetjp_2843_;
}
else
{
lean_inc(v_snapshotTasks_2842_);
lean_inc(v_infoState_2841_);
lean_inc(v_messages_2840_);
lean_inc(v_recordedDeps_2839_);
lean_inc(v_traceState_2838_);
lean_inc(v_auxDeclNGen_2837_);
lean_inc(v_ngen_2836_);
lean_inc(v_nextMacroScope_2835_);
lean_dec(v___x_2834_);
v___x_2844_ = lean_box(0);
v_isShared_2845_ = v_isSharedCheck_2853_;
goto v_resetjp_2843_;
}
v_resetjp_2843_:
{
lean_object* v___x_2846_; lean_object* v___x_2847_; lean_object* v___x_2849_; 
v___x_2846_ = lean_box(0);
v___x_2847_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1);
if (v_isShared_2845_ == 0)
{
lean_ctor_set(v___x_2844_, 5, v___x_2847_);
lean_ctor_set(v___x_2844_, 0, v_env_2831_);
v___x_2849_ = v___x_2844_;
goto v_reusejp_2848_;
}
else
{
lean_object* v_reuseFailAlloc_2852_; 
v_reuseFailAlloc_2852_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2852_, 0, v_env_2831_);
lean_ctor_set(v_reuseFailAlloc_2852_, 1, v_nextMacroScope_2835_);
lean_ctor_set(v_reuseFailAlloc_2852_, 2, v_ngen_2836_);
lean_ctor_set(v_reuseFailAlloc_2852_, 3, v_auxDeclNGen_2837_);
lean_ctor_set(v_reuseFailAlloc_2852_, 4, v_traceState_2838_);
lean_ctor_set(v_reuseFailAlloc_2852_, 5, v___x_2847_);
lean_ctor_set(v_reuseFailAlloc_2852_, 6, v_recordedDeps_2839_);
lean_ctor_set(v_reuseFailAlloc_2852_, 7, v_messages_2840_);
lean_ctor_set(v_reuseFailAlloc_2852_, 8, v_infoState_2841_);
lean_ctor_set(v_reuseFailAlloc_2852_, 9, v_snapshotTasks_2842_);
v___x_2849_ = v_reuseFailAlloc_2852_;
goto v_reusejp_2848_;
}
v_reusejp_2848_:
{
lean_object* v___x_2850_; lean_object* v___x_2851_; 
v___x_2850_ = lean_st_ref_put(v___y_2832_, v___x_2849_);
v___x_2851_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2851_, 0, v___x_2846_);
return v___x_2851_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_registerParametricAttributeForExt_spec__0___redArg___boxed(lean_object* v_env_2856_, lean_object* v___y_2857_, lean_object* v___y_2858_){
_start:
{
lean_object* v_res_2859_; 
v_res_2859_ = l_Lean_setEnv___at___00Lean_registerParametricAttributeForExt_spec__0___redArg(v_env_2856_, v___y_2857_);
lean_dec(v___y_2857_);
return v_res_2859_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_registerParametricAttributeForExt_spec__0(lean_object* v_env_2860_, lean_object* v___y_2861_, lean_object* v___y_2862_){
_start:
{
lean_object* v___x_2864_; 
v___x_2864_ = l_Lean_setEnv___at___00Lean_registerParametricAttributeForExt_spec__0___redArg(v_env_2860_, v___y_2862_);
return v___x_2864_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_registerParametricAttributeForExt_spec__0___boxed(lean_object* v_env_2865_, lean_object* v___y_2866_, lean_object* v___y_2867_, lean_object* v___y_2868_){
_start:
{
lean_object* v_res_2869_; 
v_res_2869_ = l_Lean_setEnv___at___00Lean_registerParametricAttributeForExt_spec__0(v_env_2865_, v___y_2866_, v___y_2867_);
lean_dec(v___y_2867_);
lean_dec_ref(v___y_2866_);
return v_res_2869_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___redArg___lam__0(lean_object* v_getParam_2870_, lean_object* v_ext_2871_, lean_object* v_afterSet_2872_, lean_object* v_toAttributeImplCore_2873_, lean_object* v_decl_2874_, lean_object* v_stx_2875_, uint8_t v_kind_2876_, lean_object* v___y_2877_, lean_object* v___y_2878_){
_start:
{
lean_object* v___y_2881_; lean_object* v___y_2882_; lean_object* v___y_2883_; lean_object* v___y_2884_; uint8_t v___y_2885_; lean_object* v___y_2888_; lean_object* v___y_2889_; lean_object* v___y_2890_; uint8_t v___x_2935_; uint8_t v___x_2936_; 
v___x_2935_ = 0;
v___x_2936_ = l_Lean_instBEqAttributeKind_beq(v_kind_2876_, v___x_2935_);
if (v___x_2936_ == 0)
{
lean_object* v_name_2937_; lean_object* v___x_2938_; 
lean_dec(v_stx_2875_);
lean_dec(v_decl_2874_);
lean_dec_ref(v_afterSet_2872_);
lean_dec_ref(v_ext_2871_);
lean_dec_ref(v_getParam_2870_);
v_name_2937_ = lean_ctor_get(v_toAttributeImplCore_2873_, 1);
lean_inc(v_name_2937_);
lean_dec_ref(v_toAttributeImplCore_2873_);
v___x_2938_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg(v_name_2937_, v_kind_2876_, v___y_2877_, v___y_2878_);
return v___x_2938_;
}
else
{
goto v___jp_2929_;
}
v___jp_2880_:
{
if (v___y_2885_ == 0)
{
lean_object* v___x_2886_; 
lean_dec_ref(v___y_2881_);
v___x_2886_ = l_Lean_setEnv___at___00Lean_registerParametricAttributeForExt_spec__0___redArg(v___y_2884_, v___y_2883_);
return v___x_2886_;
}
else
{
lean_dec_ref(v___y_2884_);
return v___y_2881_;
}
}
v___jp_2887_:
{
lean_object* v___x_2891_; 
lean_inc(v___y_2890_);
lean_inc_ref(v___y_2889_);
lean_inc(v_decl_2874_);
v___x_2891_ = lean_apply_5(v_getParam_2870_, v_decl_2874_, v_stx_2875_, v___y_2889_, v___y_2890_, lean_box(0));
if (lean_obj_tag(v___x_2891_) == 0)
{
lean_object* v_a_2892_; lean_object* v___x_2893_; lean_object* v_toEnvExtension_2894_; lean_object* v_env_2895_; lean_object* v_nextMacroScope_2896_; lean_object* v_ngen_2897_; lean_object* v_auxDeclNGen_2898_; lean_object* v_traceState_2899_; lean_object* v_recordedDeps_2900_; lean_object* v_messages_2901_; lean_object* v_infoState_2902_; lean_object* v_snapshotTasks_2903_; lean_object* v___x_2905_; uint8_t v_isShared_2906_; uint8_t v_isSharedCheck_2919_; 
v_a_2892_ = lean_ctor_get(v___x_2891_, 0);
lean_inc(v_a_2892_);
lean_dec_ref_known(v___x_2891_, 1);
v___x_2893_ = lean_st_ref_take(v___y_2890_);
v_toEnvExtension_2894_ = lean_ctor_get(v_ext_2871_, 0);
v_env_2895_ = lean_ctor_get(v___x_2893_, 0);
v_nextMacroScope_2896_ = lean_ctor_get(v___x_2893_, 1);
v_ngen_2897_ = lean_ctor_get(v___x_2893_, 2);
v_auxDeclNGen_2898_ = lean_ctor_get(v___x_2893_, 3);
v_traceState_2899_ = lean_ctor_get(v___x_2893_, 4);
v_recordedDeps_2900_ = lean_ctor_get(v___x_2893_, 6);
v_messages_2901_ = lean_ctor_get(v___x_2893_, 7);
v_infoState_2902_ = lean_ctor_get(v___x_2893_, 8);
v_snapshotTasks_2903_ = lean_ctor_get(v___x_2893_, 9);
v_isSharedCheck_2919_ = !lean_is_exclusive(v___x_2893_);
if (v_isSharedCheck_2919_ == 0)
{
lean_object* v_unused_2920_; 
v_unused_2920_ = lean_ctor_get(v___x_2893_, 5);
lean_dec(v_unused_2920_);
v___x_2905_ = v___x_2893_;
v_isShared_2906_ = v_isSharedCheck_2919_;
goto v_resetjp_2904_;
}
else
{
lean_inc(v_snapshotTasks_2903_);
lean_inc(v_infoState_2902_);
lean_inc(v_messages_2901_);
lean_inc(v_recordedDeps_2900_);
lean_inc(v_traceState_2899_);
lean_inc(v_auxDeclNGen_2898_);
lean_inc(v_ngen_2897_);
lean_inc(v_nextMacroScope_2896_);
lean_inc(v_env_2895_);
lean_dec(v___x_2893_);
v___x_2905_ = lean_box(0);
v_isShared_2906_ = v_isSharedCheck_2919_;
goto v_resetjp_2904_;
}
v_resetjp_2904_:
{
lean_object* v_asyncMode_2907_; lean_object* v___x_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; lean_object* v___x_2912_; 
v_asyncMode_2907_ = lean_ctor_get(v_toEnvExtension_2894_, 2);
lean_inc(v_asyncMode_2907_);
lean_inc(v_a_2892_);
lean_inc_n(v_decl_2874_, 2);
v___x_2908_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2908_, 0, v_decl_2874_);
lean_ctor_set(v___x_2908_, 1, v_a_2892_);
v___x_2909_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_ext_2871_, v_env_2895_, v___x_2908_, v_asyncMode_2907_, v_decl_2874_);
lean_dec(v_asyncMode_2907_);
v___x_2910_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1);
if (v_isShared_2906_ == 0)
{
lean_ctor_set(v___x_2905_, 5, v___x_2910_);
lean_ctor_set(v___x_2905_, 0, v___x_2909_);
v___x_2912_ = v___x_2905_;
goto v_reusejp_2911_;
}
else
{
lean_object* v_reuseFailAlloc_2918_; 
v_reuseFailAlloc_2918_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2918_, 0, v___x_2909_);
lean_ctor_set(v_reuseFailAlloc_2918_, 1, v_nextMacroScope_2896_);
lean_ctor_set(v_reuseFailAlloc_2918_, 2, v_ngen_2897_);
lean_ctor_set(v_reuseFailAlloc_2918_, 3, v_auxDeclNGen_2898_);
lean_ctor_set(v_reuseFailAlloc_2918_, 4, v_traceState_2899_);
lean_ctor_set(v_reuseFailAlloc_2918_, 5, v___x_2910_);
lean_ctor_set(v_reuseFailAlloc_2918_, 6, v_recordedDeps_2900_);
lean_ctor_set(v_reuseFailAlloc_2918_, 7, v_messages_2901_);
lean_ctor_set(v_reuseFailAlloc_2918_, 8, v_infoState_2902_);
lean_ctor_set(v_reuseFailAlloc_2918_, 9, v_snapshotTasks_2903_);
v___x_2912_ = v_reuseFailAlloc_2918_;
goto v_reusejp_2911_;
}
v_reusejp_2911_:
{
lean_object* v___x_2913_; lean_object* v___x_2914_; 
v___x_2913_ = lean_st_ref_put(v___y_2890_, v___x_2912_);
lean_inc(v___y_2890_);
lean_inc_ref(v___y_2889_);
v___x_2914_ = lean_apply_5(v_afterSet_2872_, v_decl_2874_, v_a_2892_, v___y_2889_, v___y_2890_, lean_box(0));
if (lean_obj_tag(v___x_2914_) == 0)
{
lean_dec_ref(v___y_2888_);
return v___x_2914_;
}
else
{
lean_object* v_a_2915_; uint8_t v___x_2916_; 
v_a_2915_ = lean_ctor_get(v___x_2914_, 0);
lean_inc(v_a_2915_);
v___x_2916_ = l_Lean_Exception_isInterrupt(v_a_2915_);
if (v___x_2916_ == 0)
{
uint8_t v___x_2917_; 
v___x_2917_ = l_Lean_Exception_isRuntime(v_a_2915_);
v___y_2881_ = v___x_2914_;
v___y_2882_ = v___y_2889_;
v___y_2883_ = v___y_2890_;
v___y_2884_ = v___y_2888_;
v___y_2885_ = v___x_2917_;
goto v___jp_2880_;
}
else
{
lean_dec(v_a_2915_);
v___y_2881_ = v___x_2914_;
v___y_2882_ = v___y_2889_;
v___y_2883_ = v___y_2890_;
v___y_2884_ = v___y_2888_;
v___y_2885_ = v___x_2916_;
goto v___jp_2880_;
}
}
}
}
}
else
{
lean_object* v_a_2921_; lean_object* v___x_2923_; uint8_t v_isShared_2924_; uint8_t v_isSharedCheck_2928_; 
lean_dec_ref(v___y_2888_);
lean_dec(v_decl_2874_);
lean_dec_ref(v_afterSet_2872_);
lean_dec_ref(v_ext_2871_);
v_a_2921_ = lean_ctor_get(v___x_2891_, 0);
v_isSharedCheck_2928_ = !lean_is_exclusive(v___x_2891_);
if (v_isSharedCheck_2928_ == 0)
{
v___x_2923_ = v___x_2891_;
v_isShared_2924_ = v_isSharedCheck_2928_;
goto v_resetjp_2922_;
}
else
{
lean_inc(v_a_2921_);
lean_dec(v___x_2891_);
v___x_2923_ = lean_box(0);
v_isShared_2924_ = v_isSharedCheck_2928_;
goto v_resetjp_2922_;
}
v_resetjp_2922_:
{
lean_object* v___x_2926_; 
if (v_isShared_2924_ == 0)
{
v___x_2926_ = v___x_2923_;
goto v_reusejp_2925_;
}
else
{
lean_object* v_reuseFailAlloc_2927_; 
v_reuseFailAlloc_2927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2927_, 0, v_a_2921_);
v___x_2926_ = v_reuseFailAlloc_2927_;
goto v_reusejp_2925_;
}
v_reusejp_2925_:
{
return v___x_2926_;
}
}
}
}
v___jp_2929_:
{
lean_object* v___x_2930_; lean_object* v_env_2931_; lean_object* v___x_2932_; 
v___x_2930_ = lean_st_ref_get(v___y_2878_);
v_env_2931_ = lean_ctor_get(v___x_2930_, 0);
lean_inc_ref(v_env_2931_);
lean_dec(v___x_2930_);
v___x_2932_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2931_, v_decl_2874_);
if (lean_obj_tag(v___x_2932_) == 0)
{
lean_dec_ref(v_toAttributeImplCore_2873_);
v___y_2888_ = v_env_2931_;
v___y_2889_ = v___y_2877_;
v___y_2890_ = v___y_2878_;
goto v___jp_2887_;
}
else
{
lean_object* v_name_2933_; lean_object* v___x_2934_; 
lean_dec_ref_known(v___x_2932_, 1);
lean_dec_ref(v_env_2931_);
lean_dec(v_stx_2875_);
lean_dec_ref(v_afterSet_2872_);
lean_dec_ref(v_ext_2871_);
lean_dec_ref(v_getParam_2870_);
v_name_2933_ = lean_ctor_get(v_toAttributeImplCore_2873_, 1);
lean_inc(v_name_2933_);
lean_dec_ref(v_toAttributeImplCore_2873_);
v___x_2934_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg(v_name_2933_, v_decl_2874_, v___y_2877_, v___y_2878_);
return v___x_2934_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___redArg___lam__0___boxed(lean_object* v_getParam_2939_, lean_object* v_ext_2940_, lean_object* v_afterSet_2941_, lean_object* v_toAttributeImplCore_2942_, lean_object* v_decl_2943_, lean_object* v_stx_2944_, lean_object* v_kind_2945_, lean_object* v___y_2946_, lean_object* v___y_2947_, lean_object* v___y_2948_){
_start:
{
uint8_t v_kind_boxed_2949_; lean_object* v_res_2950_; 
v_kind_boxed_2949_ = lean_unbox(v_kind_2945_);
v_res_2950_ = l_Lean_registerParametricAttributeForExt___redArg___lam__0(v_getParam_2939_, v_ext_2940_, v_afterSet_2941_, v_toAttributeImplCore_2942_, v_decl_2943_, v_stx_2944_, v_kind_boxed_2949_, v___y_2946_, v___y_2947_);
lean_dec(v___y_2947_);
lean_dec_ref(v___y_2946_);
return v_res_2950_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___redArg___lam__1(lean_object* v_toAttributeImplCore_2951_, lean_object* v_decl_2952_, lean_object* v___y_2953_, lean_object* v___y_2954_){
_start:
{
lean_object* v_name_2956_; lean_object* v___x_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; lean_object* v___x_2962_; 
v_name_2956_ = lean_ctor_get(v_toAttributeImplCore_2951_, 1);
lean_inc(v_name_2956_);
lean_dec_ref(v_toAttributeImplCore_2951_);
v___x_2957_ = lean_obj_once(&l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1, &l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1_once, _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1);
v___x_2958_ = l_Lean_MessageData_ofName(v_name_2956_);
v___x_2959_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2959_, 0, v___x_2957_);
lean_ctor_set(v___x_2959_, 1, v___x_2958_);
v___x_2960_ = lean_obj_once(&l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3, &l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3_once, _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3);
v___x_2961_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2961_, 0, v___x_2959_);
lean_ctor_set(v___x_2961_, 1, v___x_2960_);
v___x_2962_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_2961_, v___y_2953_, v___y_2954_);
return v___x_2962_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___redArg___lam__1___boxed(lean_object* v_toAttributeImplCore_2963_, lean_object* v_decl_2964_, lean_object* v___y_2965_, lean_object* v___y_2966_, lean_object* v___y_2967_){
_start:
{
lean_object* v_res_2968_; 
v_res_2968_ = l_Lean_registerParametricAttributeForExt___redArg___lam__1(v_toAttributeImplCore_2963_, v_decl_2964_, v___y_2965_, v___y_2966_);
lean_dec(v___y_2966_);
lean_dec_ref(v___y_2965_);
lean_dec(v_decl_2964_);
return v_res_2968_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___redArg(lean_object* v_impl_2969_, lean_object* v_ext_2970_){
_start:
{
lean_object* v_toAttributeImplCore_2972_; lean_object* v_getParam_2973_; lean_object* v_afterSet_2974_; uint8_t v_preserveOrder_2975_; lean_object* v___f_2976_; lean_object* v___f_2977_; lean_object* v_attrImpl_2978_; lean_object* v___x_2979_; 
v_toAttributeImplCore_2972_ = lean_ctor_get(v_impl_2969_, 0);
lean_inc_ref_n(v_toAttributeImplCore_2972_, 3);
v_getParam_2973_ = lean_ctor_get(v_impl_2969_, 1);
lean_inc_ref(v_getParam_2973_);
v_afterSet_2974_ = lean_ctor_get(v_impl_2969_, 2);
lean_inc_ref(v_afterSet_2974_);
v_preserveOrder_2975_ = lean_ctor_get_uint8(v_impl_2969_, sizeof(void*)*4);
lean_dec_ref(v_impl_2969_);
lean_inc_ref(v_ext_2970_);
v___f_2976_ = lean_alloc_closure((void*)(l_Lean_registerParametricAttributeForExt___redArg___lam__0___boxed), 10, 4);
lean_closure_set(v___f_2976_, 0, v_getParam_2973_);
lean_closure_set(v___f_2976_, 1, v_ext_2970_);
lean_closure_set(v___f_2976_, 2, v_afterSet_2974_);
lean_closure_set(v___f_2976_, 3, v_toAttributeImplCore_2972_);
v___f_2977_ = lean_alloc_closure((void*)(l_Lean_registerParametricAttributeForExt___redArg___lam__1___boxed), 5, 1);
lean_closure_set(v___f_2977_, 0, v_toAttributeImplCore_2972_);
v_attrImpl_2978_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_attrImpl_2978_, 0, v_toAttributeImplCore_2972_);
lean_ctor_set(v_attrImpl_2978_, 1, v___f_2976_);
lean_ctor_set(v_attrImpl_2978_, 2, v___f_2977_);
lean_inc_ref(v_attrImpl_2978_);
v___x_2979_ = l_Lean_registerBuiltinAttribute(v_attrImpl_2978_);
if (lean_obj_tag(v___x_2979_) == 0)
{
lean_object* v___x_2981_; uint8_t v_isShared_2982_; uint8_t v_isSharedCheck_2987_; 
v_isSharedCheck_2987_ = !lean_is_exclusive(v___x_2979_);
if (v_isSharedCheck_2987_ == 0)
{
lean_object* v_unused_2988_; 
v_unused_2988_ = lean_ctor_get(v___x_2979_, 0);
lean_dec(v_unused_2988_);
v___x_2981_ = v___x_2979_;
v_isShared_2982_ = v_isSharedCheck_2987_;
goto v_resetjp_2980_;
}
else
{
lean_dec(v___x_2979_);
v___x_2981_ = lean_box(0);
v_isShared_2982_ = v_isSharedCheck_2987_;
goto v_resetjp_2980_;
}
v_resetjp_2980_:
{
lean_object* v___x_2983_; lean_object* v___x_2985_; 
v___x_2983_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2983_, 0, v_attrImpl_2978_);
lean_ctor_set(v___x_2983_, 1, v_ext_2970_);
lean_ctor_set_uint8(v___x_2983_, sizeof(void*)*2, v_preserveOrder_2975_);
if (v_isShared_2982_ == 0)
{
lean_ctor_set(v___x_2981_, 0, v___x_2983_);
v___x_2985_ = v___x_2981_;
goto v_reusejp_2984_;
}
else
{
lean_object* v_reuseFailAlloc_2986_; 
v_reuseFailAlloc_2986_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2986_, 0, v___x_2983_);
v___x_2985_ = v_reuseFailAlloc_2986_;
goto v_reusejp_2984_;
}
v_reusejp_2984_:
{
return v___x_2985_;
}
}
}
else
{
lean_object* v_a_2989_; lean_object* v___x_2991_; uint8_t v_isShared_2992_; uint8_t v_isSharedCheck_2996_; 
lean_dec_ref_known(v_attrImpl_2978_, 3);
lean_dec_ref(v_ext_2970_);
v_a_2989_ = lean_ctor_get(v___x_2979_, 0);
v_isSharedCheck_2996_ = !lean_is_exclusive(v___x_2979_);
if (v_isSharedCheck_2996_ == 0)
{
v___x_2991_ = v___x_2979_;
v_isShared_2992_ = v_isSharedCheck_2996_;
goto v_resetjp_2990_;
}
else
{
lean_inc(v_a_2989_);
lean_dec(v___x_2979_);
v___x_2991_ = lean_box(0);
v_isShared_2992_ = v_isSharedCheck_2996_;
goto v_resetjp_2990_;
}
v_resetjp_2990_:
{
lean_object* v___x_2994_; 
if (v_isShared_2992_ == 0)
{
v___x_2994_ = v___x_2991_;
goto v_reusejp_2993_;
}
else
{
lean_object* v_reuseFailAlloc_2995_; 
v_reuseFailAlloc_2995_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2995_, 0, v_a_2989_);
v___x_2994_ = v_reuseFailAlloc_2995_;
goto v_reusejp_2993_;
}
v_reusejp_2993_:
{
return v___x_2994_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___redArg___boxed(lean_object* v_impl_2997_, lean_object* v_ext_2998_, lean_object* v_a_2999_){
_start:
{
lean_object* v_res_3000_; 
v_res_3000_ = l_Lean_registerParametricAttributeForExt___redArg(v_impl_2997_, v_ext_2998_);
return v_res_3000_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt(lean_object* v_00_u03b1_3001_, lean_object* v_impl_3002_, lean_object* v_ext_3003_){
_start:
{
lean_object* v___x_3005_; 
v___x_3005_ = l_Lean_registerParametricAttributeForExt___redArg(v_impl_3002_, v_ext_3003_);
return v___x_3005_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___boxed(lean_object* v_00_u03b1_3006_, lean_object* v_impl_3007_, lean_object* v_ext_3008_, lean_object* v_a_3009_){
_start:
{
lean_object* v_res_3010_; 
v_res_3010_ = l_Lean_registerParametricAttributeForExt(v_00_u03b1_3006_, v_impl_3007_, v_ext_3008_);
return v_res_3010_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg(lean_object* v_impl_3011_){
_start:
{
lean_object* v_toAttributeImplCore_3013_; uint8_t v_preserveOrder_3014_; lean_object* v_filterExport_3015_; lean_object* v_ref_3016_; lean_object* v___x_3017_; 
v_toAttributeImplCore_3013_ = lean_ctor_get(v_impl_3011_, 0);
v_preserveOrder_3014_ = lean_ctor_get_uint8(v_impl_3011_, sizeof(void*)*4);
v_filterExport_3015_ = lean_ctor_get(v_impl_3011_, 3);
v_ref_3016_ = lean_ctor_get(v_toAttributeImplCore_3013_, 0);
lean_inc_ref(v_filterExport_3015_);
lean_inc(v_ref_3016_);
v___x_3017_ = l_Lean_registerParametricAttributeExt___redArg(v_ref_3016_, v_preserveOrder_3014_, v_filterExport_3015_);
if (lean_obj_tag(v___x_3017_) == 0)
{
lean_object* v_a_3018_; lean_object* v___x_3019_; 
v_a_3018_ = lean_ctor_get(v___x_3017_, 0);
lean_inc(v_a_3018_);
lean_dec_ref_known(v___x_3017_, 1);
v___x_3019_ = l_Lean_registerParametricAttributeForExt___redArg(v_impl_3011_, v_a_3018_);
return v___x_3019_;
}
else
{
lean_object* v_a_3020_; lean_object* v___x_3022_; uint8_t v_isShared_3023_; uint8_t v_isSharedCheck_3027_; 
lean_dec_ref(v_impl_3011_);
v_a_3020_ = lean_ctor_get(v___x_3017_, 0);
v_isSharedCheck_3027_ = !lean_is_exclusive(v___x_3017_);
if (v_isSharedCheck_3027_ == 0)
{
v___x_3022_ = v___x_3017_;
v_isShared_3023_ = v_isSharedCheck_3027_;
goto v_resetjp_3021_;
}
else
{
lean_inc(v_a_3020_);
lean_dec(v___x_3017_);
v___x_3022_ = lean_box(0);
v_isShared_3023_ = v_isSharedCheck_3027_;
goto v_resetjp_3021_;
}
v_resetjp_3021_:
{
lean_object* v___x_3025_; 
if (v_isShared_3023_ == 0)
{
v___x_3025_ = v___x_3022_;
goto v_reusejp_3024_;
}
else
{
lean_object* v_reuseFailAlloc_3026_; 
v_reuseFailAlloc_3026_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3026_, 0, v_a_3020_);
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
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___redArg___boxed(lean_object* v_impl_3028_, lean_object* v_a_3029_){
_start:
{
lean_object* v_res_3030_; 
v_res_3030_ = l_Lean_registerParametricAttribute___redArg(v_impl_3028_);
return v_res_3030_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute(lean_object* v_00_u03b1_3031_, lean_object* v_impl_3032_){
_start:
{
lean_object* v___x_3034_; 
v___x_3034_ = l_Lean_registerParametricAttribute___redArg(v_impl_3032_);
return v___x_3034_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttribute___boxed(lean_object* v_00_u03b1_3035_, lean_object* v_impl_3036_, lean_object* v_a_3037_){
_start:
{
lean_object* v_res_3038_; 
v_res_3038_ = l_Lean_registerParametricAttribute(v_00_u03b1_3035_, v_impl_3036_);
return v_res_3038_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___lam__1(lean_object* v_decl_3039_, lean_object* v___x_3040_, lean_object* v___x_3041_, lean_object* v_a_3042_, lean_object* v_x_3043_, lean_object* v___y_3044_){
_start:
{
lean_object* v_fst_3045_; uint8_t v___x_3046_; 
v_fst_3045_ = lean_ctor_get(v_a_3042_, 0);
v___x_3046_ = lean_name_eq(v_fst_3045_, v_decl_3039_);
if (v___x_3046_ == 0)
{
lean_object* v___x_3047_; 
lean_dec_ref(v_a_3042_);
v___x_3047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3047_, 0, v___x_3040_);
return v___x_3047_;
}
else
{
lean_object* v___x_3048_; lean_object* v___x_3049_; lean_object* v___x_3050_; lean_object* v___x_3051_; 
lean_dec_ref(v___x_3040_);
v___x_3048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3048_, 0, v_a_3042_);
v___x_3049_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3049_, 0, v___x_3048_);
v___x_3050_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3050_, 0, v___x_3049_);
lean_ctor_set(v___x_3050_, 1, v___x_3041_);
v___x_3051_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3051_, 0, v___x_3050_);
return v___x_3051_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___lam__1___boxed(lean_object* v_decl_3052_, lean_object* v___x_3053_, lean_object* v___x_3054_, lean_object* v_a_3055_, lean_object* v_x_3056_, lean_object* v___y_3057_){
_start:
{
lean_object* v_res_3058_; 
v_res_3058_ = l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___lam__1(v_decl_3052_, v___x_3053_, v___x_3054_, v_a_3055_, v_x_3056_, v___y_3057_);
lean_dec_ref(v___y_3057_);
lean_dec(v_decl_3052_);
return v_res_3058_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg(lean_object* v_inst_3086_, lean_object* v_ext_3087_, uint8_t v_preserveOrder_3088_, lean_object* v_env_3089_, lean_object* v_decl_3090_){
_start:
{
lean_object* v___y_3092_; lean_object* v___x_3103_; lean_object* v___x_3104_; 
v___x_3103_ = ((lean_object*)(l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__0));
v___x_3104_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3089_, v_decl_3090_);
if (lean_obj_tag(v___x_3104_) == 0)
{
lean_object* v_toEnvExtension_3105_; lean_object* v_asyncMode_3106_; lean_object* v___x_3107_; lean_object* v___x_3108_; lean_object* v_snd_3109_; lean_object* v___x_3110_; 
lean_dec(v_inst_3086_);
v_toEnvExtension_3105_ = lean_ctor_get(v_ext_3087_, 0);
v_asyncMode_3106_ = lean_ctor_get(v_toEnvExtension_3105_, 2);
v___x_3107_ = lean_box(0);
v___x_3108_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3103_, v_ext_3087_, v_env_3089_, v_asyncMode_3106_, v___x_3107_);
v_snd_3109_ = lean_ctor_get(v___x_3108_, 1);
lean_inc(v_snd_3109_);
lean_dec(v___x_3108_);
v___x_3110_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_snd_3109_, v_decl_3090_);
lean_dec(v_decl_3090_);
lean_dec(v_snd_3109_);
return v___x_3110_;
}
else
{
if (v_preserveOrder_3088_ == 0)
{
lean_object* v_val_3111_; uint8_t v___x_3112_; lean_object* v___x_3113_; lean_object* v___x_3114_; lean_object* v___x_3115_; uint8_t v___x_3116_; 
v_val_3111_ = lean_ctor_get(v___x_3104_, 0);
lean_inc(v_val_3111_);
lean_dec_ref_known(v___x_3104_, 1);
v___x_3112_ = 0;
v___x_3113_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_3103_, v_ext_3087_, v_env_3089_, v_val_3111_, v___x_3112_);
lean_dec(v_val_3111_);
lean_dec_ref(v_env_3089_);
v___x_3114_ = lean_unsigned_to_nat(0u);
v___x_3115_ = lean_array_get_size(v___x_3113_);
v___x_3116_ = lean_nat_dec_lt(v___x_3114_, v___x_3115_);
if (v___x_3116_ == 0)
{
lean_object* v___x_3117_; 
lean_dec_ref(v___x_3113_);
lean_dec(v_decl_3090_);
lean_dec(v_inst_3086_);
v___x_3117_ = lean_box(0);
return v___x_3117_;
}
else
{
lean_object* v___x_3118_; lean_object* v___x_3119_; uint8_t v___x_3120_; 
v___x_3118_ = lean_unsigned_to_nat(1u);
v___x_3119_ = lean_nat_sub(v___x_3115_, v___x_3118_);
v___x_3120_ = lean_nat_dec_le(v___x_3114_, v___x_3119_);
if (v___x_3120_ == 0)
{
lean_object* v___x_3121_; 
lean_dec(v___x_3119_);
lean_dec_ref(v___x_3113_);
lean_dec(v_decl_3090_);
lean_dec(v_inst_3086_);
v___x_3121_ = lean_box(0);
return v___x_3121_;
}
else
{
lean_object* v___f_3122_; lean_object* v___x_3123_; lean_object* v___x_3124_; lean_object* v___x_3125_; 
v___f_3122_ = ((lean_object*)(l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__1));
v___x_3123_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3123_, 0, v_decl_3090_);
lean_ctor_set(v___x_3123_, 1, v_inst_3086_);
v___x_3124_ = ((lean_object*)(l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__2));
v___x_3125_ = l_Array_binSearchAux___redArg(v___f_3122_, v___x_3124_, v___x_3113_, v___x_3123_, v___x_3114_, v___x_3119_);
lean_dec_ref(v___x_3113_);
v___y_3092_ = v___x_3125_;
goto v___jp_3091_;
}
}
}
else
{
lean_object* v_val_3126_; uint8_t v___x_3127_; lean_object* v___x_3128_; lean_object* v___x_3129_; lean_object* v___x_3130_; lean_object* v___x_3131_; lean_object* v___x_3132_; lean_object* v___f_3133_; size_t v_sz_3134_; size_t v___x_3135_; lean_object* v___x_3136_; lean_object* v_fst_3137_; 
lean_dec(v_inst_3086_);
v_val_3126_ = lean_ctor_get(v___x_3104_, 0);
lean_inc(v_val_3126_);
lean_dec_ref_known(v___x_3104_, 1);
v___x_3127_ = 0;
v___x_3128_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_3103_, v_ext_3087_, v_env_3089_, v_val_3126_, v___x_3127_);
lean_dec(v_val_3126_);
lean_dec_ref(v_env_3089_);
v___x_3129_ = ((lean_object*)(l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__12));
v___x_3130_ = lean_box(0);
v___x_3131_ = lean_box(0);
v___x_3132_ = ((lean_object*)(l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__13));
v___f_3133_ = lean_alloc_closure((void*)(l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___lam__1___boxed), 6, 3);
lean_closure_set(v___f_3133_, 0, v_decl_3090_);
lean_closure_set(v___f_3133_, 1, v___x_3132_);
lean_closure_set(v___f_3133_, 2, v___x_3131_);
v_sz_3134_ = lean_array_size(v___x_3128_);
v___x_3135_ = ((size_t)0ULL);
v___x_3136_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_3129_, v___x_3128_, v___f_3133_, v_sz_3134_, v___x_3135_, v___x_3132_);
v_fst_3137_ = lean_ctor_get(v___x_3136_, 0);
lean_inc(v_fst_3137_);
lean_dec(v___x_3136_);
if (lean_obj_tag(v_fst_3137_) == 0)
{
return v___x_3130_;
}
else
{
lean_object* v_val_3138_; 
v_val_3138_ = lean_ctor_get(v_fst_3137_, 0);
lean_inc(v_val_3138_);
lean_dec_ref_known(v_fst_3137_, 1);
v___y_3092_ = v_val_3138_;
goto v___jp_3091_;
}
}
}
v___jp_3091_:
{
if (lean_obj_tag(v___y_3092_) == 0)
{
lean_object* v___x_3093_; 
v___x_3093_ = lean_box(0);
return v___x_3093_;
}
else
{
lean_object* v_val_3094_; lean_object* v___x_3096_; uint8_t v_isShared_3097_; uint8_t v_isSharedCheck_3102_; 
v_val_3094_ = lean_ctor_get(v___y_3092_, 0);
v_isSharedCheck_3102_ = !lean_is_exclusive(v___y_3092_);
if (v_isSharedCheck_3102_ == 0)
{
v___x_3096_ = v___y_3092_;
v_isShared_3097_ = v_isSharedCheck_3102_;
goto v_resetjp_3095_;
}
else
{
lean_inc(v_val_3094_);
lean_dec(v___y_3092_);
v___x_3096_ = lean_box(0);
v_isShared_3097_ = v_isSharedCheck_3102_;
goto v_resetjp_3095_;
}
v_resetjp_3095_:
{
lean_object* v_snd_3098_; lean_object* v___x_3100_; 
v_snd_3098_ = lean_ctor_get(v_val_3094_, 1);
lean_inc(v_snd_3098_);
lean_dec(v_val_3094_);
if (v_isShared_3097_ == 0)
{
lean_ctor_set(v___x_3096_, 0, v_snd_3098_);
v___x_3100_ = v___x_3096_;
goto v_reusejp_3099_;
}
else
{
lean_object* v_reuseFailAlloc_3101_; 
v_reuseFailAlloc_3101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3101_, 0, v_snd_3098_);
v___x_3100_ = v_reuseFailAlloc_3101_;
goto v_reusejp_3099_;
}
v_reusejp_3099_:
{
return v___x_3100_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___boxed(lean_object* v_inst_3139_, lean_object* v_ext_3140_, lean_object* v_preserveOrder_3141_, lean_object* v_env_3142_, lean_object* v_decl_3143_){
_start:
{
uint8_t v_preserveOrder_boxed_3144_; lean_object* v_res_3145_; 
v_preserveOrder_boxed_3144_ = lean_unbox(v_preserveOrder_3141_);
v_res_3145_ = l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg(v_inst_3139_, v_ext_3140_, v_preserveOrder_boxed_3144_, v_env_3142_, v_decl_3143_);
lean_dec_ref(v_ext_3140_);
return v_res_3145_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f(lean_object* v_00_u03b1_3146_, lean_object* v_inst_3147_, lean_object* v_ext_3148_, uint8_t v_preserveOrder_3149_, lean_object* v_env_3150_, lean_object* v_decl_3151_){
_start:
{
lean_object* v___x_3152_; 
v___x_3152_ = l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg(v_inst_3147_, v_ext_3148_, v_preserveOrder_3149_, v_env_3150_, v_decl_3151_);
return v___x_3152_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParamFromExt_x3f___boxed(lean_object* v_00_u03b1_3153_, lean_object* v_inst_3154_, lean_object* v_ext_3155_, lean_object* v_preserveOrder_3156_, lean_object* v_env_3157_, lean_object* v_decl_3158_){
_start:
{
uint8_t v_preserveOrder_boxed_3159_; lean_object* v_res_3160_; 
v_preserveOrder_boxed_3159_ = lean_unbox(v_preserveOrder_3156_);
v_res_3160_ = l_Lean_ParametricAttribute_getParamFromExt_x3f(v_00_u03b1_3153_, v_inst_3154_, v_ext_3155_, v_preserveOrder_boxed_3159_, v_env_3157_, v_decl_3158_);
lean_dec_ref(v_ext_3155_);
return v_res_3160_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParam_x3f___redArg(lean_object* v_inst_3161_, lean_object* v_attr_3162_, lean_object* v_env_3163_, lean_object* v_decl_3164_){
_start:
{
lean_object* v_ext_3165_; uint8_t v_preserveOrder_3166_; lean_object* v___x_3167_; 
v_ext_3165_ = lean_ctor_get(v_attr_3162_, 1);
v_preserveOrder_3166_ = lean_ctor_get_uint8(v_attr_3162_, sizeof(void*)*2);
v___x_3167_ = l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg(v_inst_3161_, v_ext_3165_, v_preserveOrder_3166_, v_env_3163_, v_decl_3164_);
return v___x_3167_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParam_x3f___redArg___boxed(lean_object* v_inst_3168_, lean_object* v_attr_3169_, lean_object* v_env_3170_, lean_object* v_decl_3171_){
_start:
{
lean_object* v_res_3172_; 
v_res_3172_ = l_Lean_ParametricAttribute_getParam_x3f___redArg(v_inst_3168_, v_attr_3169_, v_env_3170_, v_decl_3171_);
lean_dec_ref(v_attr_3169_);
return v_res_3172_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParam_x3f(lean_object* v_00_u03b1_3173_, lean_object* v_inst_3174_, lean_object* v_attr_3175_, lean_object* v_env_3176_, lean_object* v_decl_3177_){
_start:
{
lean_object* v___x_3178_; 
v___x_3178_ = l_Lean_ParametricAttribute_getParam_x3f___redArg(v_inst_3174_, v_attr_3175_, v_env_3176_, v_decl_3177_);
return v___x_3178_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_getParam_x3f___boxed(lean_object* v_00_u03b1_3179_, lean_object* v_inst_3180_, lean_object* v_attr_3181_, lean_object* v_env_3182_, lean_object* v_decl_3183_){
_start:
{
lean_object* v_res_3184_; 
v_res_3184_ = l_Lean_ParametricAttribute_getParam_x3f(v_00_u03b1_3179_, v_inst_3180_, v_attr_3181_, v_env_3182_, v_decl_3183_);
lean_dec_ref(v_attr_3181_);
return v_res_3184_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_setParamFromExt___redArg(lean_object* v_ext_3189_, lean_object* v_attr_3190_, lean_object* v_env_3191_, lean_object* v_decl_3192_, lean_object* v_param_3193_){
_start:
{
lean_object* v___x_3194_; 
v___x_3194_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3191_, v_decl_3192_);
if (lean_obj_tag(v___x_3194_) == 0)
{
lean_object* v_toEnvExtension_3195_; lean_object* v_asyncMode_3196_; lean_object* v___x_3197_; lean_object* v___x_3198_; lean_object* v___x_3199_; lean_object* v_snd_3200_; lean_object* v___x_3202_; uint8_t v_isShared_3203_; uint8_t v_isSharedCheck_3230_; 
v_toEnvExtension_3195_ = lean_ctor_get(v_ext_3189_, 0);
v_asyncMode_3196_ = lean_ctor_get(v_toEnvExtension_3195_, 2);
lean_inc(v_asyncMode_3196_);
v___x_3197_ = ((lean_object*)(l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__0));
v___x_3198_ = lean_box(0);
lean_inc_ref(v_env_3191_);
v___x_3199_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3197_, v_ext_3189_, v_env_3191_, v_asyncMode_3196_, v___x_3198_);
v_snd_3200_ = lean_ctor_get(v___x_3199_, 1);
v_isSharedCheck_3230_ = !lean_is_exclusive(v___x_3199_);
if (v_isSharedCheck_3230_ == 0)
{
lean_object* v_unused_3231_; 
v_unused_3231_ = lean_ctor_get(v___x_3199_, 0);
lean_dec(v_unused_3231_);
v___x_3202_ = v___x_3199_;
v_isShared_3203_ = v_isSharedCheck_3230_;
goto v_resetjp_3201_;
}
else
{
lean_inc(v_snd_3200_);
lean_dec(v___x_3199_);
v___x_3202_ = lean_box(0);
v_isShared_3203_ = v_isSharedCheck_3230_;
goto v_resetjp_3201_;
}
v_resetjp_3201_:
{
lean_object* v___x_3204_; 
v___x_3204_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_snd_3200_, v_decl_3192_);
lean_dec(v_snd_3200_);
if (lean_obj_tag(v___x_3204_) == 0)
{
lean_object* v___x_3206_; 
lean_dec_ref(v_attr_3190_);
if (v_isShared_3203_ == 0)
{
lean_ctor_set(v___x_3202_, 1, v_param_3193_);
lean_ctor_set(v___x_3202_, 0, v_decl_3192_);
v___x_3206_ = v___x_3202_;
goto v_reusejp_3205_;
}
else
{
lean_object* v_reuseFailAlloc_3209_; 
v_reuseFailAlloc_3209_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3209_, 0, v_decl_3192_);
lean_ctor_set(v_reuseFailAlloc_3209_, 1, v_param_3193_);
v___x_3206_ = v_reuseFailAlloc_3209_;
goto v_reusejp_3205_;
}
v_reusejp_3205_:
{
lean_object* v___x_3207_; lean_object* v___x_3208_; 
v___x_3207_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_ext_3189_, v_env_3191_, v___x_3206_, v_asyncMode_3196_, v___x_3198_);
lean_dec(v_asyncMode_3196_);
v___x_3208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3208_, 0, v___x_3207_);
return v___x_3208_;
}
}
else
{
lean_object* v___x_3211_; uint8_t v_isShared_3212_; uint8_t v_isSharedCheck_3228_; 
lean_del_object(v___x_3202_);
lean_dec(v_asyncMode_3196_);
lean_dec(v_param_3193_);
lean_dec_ref(v_env_3191_);
lean_dec_ref(v_ext_3189_);
v_isSharedCheck_3228_ = !lean_is_exclusive(v___x_3204_);
if (v_isSharedCheck_3228_ == 0)
{
lean_object* v_unused_3229_; 
v_unused_3229_ = lean_ctor_get(v___x_3204_, 0);
lean_dec(v_unused_3229_);
v___x_3211_ = v___x_3204_;
v_isShared_3212_ = v_isSharedCheck_3228_;
goto v_resetjp_3210_;
}
else
{
lean_dec(v___x_3204_);
v___x_3211_ = lean_box(0);
v_isShared_3212_ = v_isSharedCheck_3228_;
goto v_resetjp_3210_;
}
v_resetjp_3210_:
{
lean_object* v_toAttributeImplCore_3213_; lean_object* v_name_3214_; uint8_t v___x_3215_; lean_object* v___x_3216_; lean_object* v___x_3217_; lean_object* v___x_3218_; lean_object* v___x_3219_; lean_object* v___x_3220_; lean_object* v___x_3221_; lean_object* v___x_3222_; lean_object* v___x_3223_; lean_object* v___x_3224_; lean_object* v___x_3226_; 
v_toAttributeImplCore_3213_ = lean_ctor_get(v_attr_3190_, 0);
lean_inc_ref(v_toAttributeImplCore_3213_);
lean_dec_ref(v_attr_3190_);
v_name_3214_ = lean_ctor_get(v_toAttributeImplCore_3213_, 1);
lean_inc(v_name_3214_);
lean_dec_ref(v_toAttributeImplCore_3213_);
v___x_3215_ = 1;
v___x_3216_ = ((lean_object*)(l_Lean_ParametricAttribute_setParamFromExt___redArg___closed__0));
v___x_3217_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_3214_, v___x_3215_);
v___x_3218_ = lean_string_append(v___x_3216_, v___x_3217_);
lean_dec_ref(v___x_3217_);
v___x_3219_ = ((lean_object*)(l_Lean_ParametricAttribute_setParamFromExt___redArg___closed__1));
v___x_3220_ = lean_string_append(v___x_3218_, v___x_3219_);
v___x_3221_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_decl_3192_, v___x_3215_);
v___x_3222_ = lean_string_append(v___x_3220_, v___x_3221_);
lean_dec_ref(v___x_3221_);
v___x_3223_ = ((lean_object*)(l_Lean_ParametricAttribute_setParamFromExt___redArg___closed__2));
v___x_3224_ = lean_string_append(v___x_3222_, v___x_3223_);
if (v_isShared_3212_ == 0)
{
lean_ctor_set_tag(v___x_3211_, 0);
lean_ctor_set(v___x_3211_, 0, v___x_3224_);
v___x_3226_ = v___x_3211_;
goto v_reusejp_3225_;
}
else
{
lean_object* v_reuseFailAlloc_3227_; 
v_reuseFailAlloc_3227_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3227_, 0, v___x_3224_);
v___x_3226_ = v_reuseFailAlloc_3227_;
goto v_reusejp_3225_;
}
v_reusejp_3225_:
{
return v___x_3226_;
}
}
}
}
}
else
{
lean_object* v___x_3233_; uint8_t v_isShared_3234_; uint8_t v_isSharedCheck_3250_; 
lean_dec(v_param_3193_);
lean_dec_ref(v_env_3191_);
lean_dec_ref(v_ext_3189_);
v_isSharedCheck_3250_ = !lean_is_exclusive(v___x_3194_);
if (v_isSharedCheck_3250_ == 0)
{
lean_object* v_unused_3251_; 
v_unused_3251_ = lean_ctor_get(v___x_3194_, 0);
lean_dec(v_unused_3251_);
v___x_3233_ = v___x_3194_;
v_isShared_3234_ = v_isSharedCheck_3250_;
goto v_resetjp_3232_;
}
else
{
lean_dec(v___x_3194_);
v___x_3233_ = lean_box(0);
v_isShared_3234_ = v_isSharedCheck_3250_;
goto v_resetjp_3232_;
}
v_resetjp_3232_:
{
lean_object* v_toAttributeImplCore_3235_; lean_object* v_name_3236_; uint8_t v___x_3237_; lean_object* v___x_3238_; lean_object* v___x_3239_; lean_object* v___x_3240_; lean_object* v___x_3241_; lean_object* v___x_3242_; lean_object* v___x_3243_; lean_object* v___x_3244_; lean_object* v___x_3245_; lean_object* v___x_3246_; lean_object* v___x_3248_; 
v_toAttributeImplCore_3235_ = lean_ctor_get(v_attr_3190_, 0);
lean_inc_ref(v_toAttributeImplCore_3235_);
lean_dec_ref(v_attr_3190_);
v_name_3236_ = lean_ctor_get(v_toAttributeImplCore_3235_, 1);
lean_inc(v_name_3236_);
lean_dec_ref(v_toAttributeImplCore_3235_);
v___x_3237_ = 1;
v___x_3238_ = ((lean_object*)(l_Lean_ParametricAttribute_setParamFromExt___redArg___closed__0));
v___x_3239_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_3236_, v___x_3237_);
v___x_3240_ = lean_string_append(v___x_3238_, v___x_3239_);
lean_dec_ref(v___x_3239_);
v___x_3241_ = ((lean_object*)(l_Lean_ParametricAttribute_setParamFromExt___redArg___closed__1));
v___x_3242_ = lean_string_append(v___x_3240_, v___x_3241_);
v___x_3243_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_decl_3192_, v___x_3237_);
v___x_3244_ = lean_string_append(v___x_3242_, v___x_3243_);
lean_dec_ref(v___x_3243_);
v___x_3245_ = ((lean_object*)(l_Lean_ParametricAttribute_setParamFromExt___redArg___closed__3));
v___x_3246_ = lean_string_append(v___x_3244_, v___x_3245_);
if (v_isShared_3234_ == 0)
{
lean_ctor_set_tag(v___x_3233_, 0);
lean_ctor_set(v___x_3233_, 0, v___x_3246_);
v___x_3248_ = v___x_3233_;
goto v_reusejp_3247_;
}
else
{
lean_object* v_reuseFailAlloc_3249_; 
v_reuseFailAlloc_3249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3249_, 0, v___x_3246_);
v___x_3248_ = v_reuseFailAlloc_3249_;
goto v_reusejp_3247_;
}
v_reusejp_3247_:
{
return v___x_3248_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_setParamFromExt(lean_object* v_00_u03b1_3252_, lean_object* v_ext_3253_, lean_object* v_attr_3254_, lean_object* v_env_3255_, lean_object* v_decl_3256_, lean_object* v_param_3257_){
_start:
{
lean_object* v___x_3258_; 
v___x_3258_ = l_Lean_ParametricAttribute_setParamFromExt___redArg(v_ext_3253_, v_attr_3254_, v_env_3255_, v_decl_3256_, v_param_3257_);
return v___x_3258_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_setParam___redArg(lean_object* v_attr_3259_, lean_object* v_env_3260_, lean_object* v_decl_3261_, lean_object* v_param_3262_){
_start:
{
lean_object* v_attr_3263_; lean_object* v_ext_3264_; lean_object* v___x_3265_; 
v_attr_3263_ = lean_ctor_get(v_attr_3259_, 0);
lean_inc_ref(v_attr_3263_);
v_ext_3264_ = lean_ctor_get(v_attr_3259_, 1);
lean_inc_ref(v_ext_3264_);
lean_dec_ref(v_attr_3259_);
v___x_3265_ = l_Lean_ParametricAttribute_setParamFromExt___redArg(v_ext_3264_, v_attr_3263_, v_env_3260_, v_decl_3261_, v_param_3262_);
return v___x_3265_;
}
}
LEAN_EXPORT lean_object* l_Lean_ParametricAttribute_setParam(lean_object* v_00_u03b1_3266_, lean_object* v_attr_3267_, lean_object* v_env_3268_, lean_object* v_decl_3269_, lean_object* v_param_3270_){
_start:
{
lean_object* v___x_3271_; 
v___x_3271_ = l_Lean_ParametricAttribute_setParam___redArg(v_attr_3267_, v_env_3268_, v_decl_3269_, v_param_3270_);
return v___x_3271_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___redArg___lam__0(lean_object* v_x_3272_, lean_object* v___y_3273_){
_start:
{
lean_object* v___x_3275_; lean_object* v___x_3276_; 
v___x_3275_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___lam__0___closed__1));
v___x_3276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3276_, 0, v___x_3275_);
return v___x_3276_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___redArg___lam__0___boxed(lean_object* v_x_3277_, lean_object* v___y_3278_, lean_object* v___y_3279_){
_start:
{
lean_object* v_res_3280_; 
v_res_3280_ = l_Lean_instInhabitedEnumAttributes_default___redArg___lam__0(v_x_3277_, v___y_3278_);
lean_dec_ref(v___y_3278_);
lean_dec_ref(v_x_3277_);
return v_res_3280_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___redArg___lam__1(lean_object* v_s_3281_, lean_object* v_x_3282_){
_start:
{
lean_inc(v_s_3281_);
return v_s_3281_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___redArg___lam__1___boxed(lean_object* v_s_3283_, lean_object* v_x_3284_){
_start:
{
lean_object* v_res_3285_; 
v_res_3285_ = l_Lean_instInhabitedEnumAttributes_default___redArg___lam__1(v_s_3283_, v_x_3284_);
lean_dec_ref(v_x_3284_);
lean_dec(v_s_3283_);
return v_res_3285_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___redArg___lam__2(lean_object* v_x_3286_, lean_object* v_x_3287_){
_start:
{
lean_object* v___x_3288_; 
v___x_3288_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___redArg___lam__2___closed__1));
return v___x_3288_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___redArg___lam__2___boxed(lean_object* v_x_3289_, lean_object* v_x_3290_){
_start:
{
lean_object* v_res_3291_; 
v_res_3291_ = l_Lean_instInhabitedEnumAttributes_default___redArg___lam__2(v_x_3289_, v_x_3290_);
lean_dec(v_x_3290_);
lean_dec_ref(v_x_3289_);
return v_res_3291_;
}
}
static lean_object* _init_l_Lean_instInhabitedEnumAttributes_default___redArg___closed__3(void){
_start:
{
lean_object* v___f_3295_; lean_object* v___f_3296_; lean_object* v___f_3297_; lean_object* v___f_3298_; lean_object* v___x_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; 
v___f_3295_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___closed__3));
v___f_3296_ = ((lean_object*)(l_Lean_instInhabitedEnumAttributes_default___redArg___closed__2));
v___f_3297_ = ((lean_object*)(l_Lean_instInhabitedEnumAttributes_default___redArg___closed__1));
v___f_3298_ = ((lean_object*)(l_Lean_instInhabitedEnumAttributes_default___redArg___closed__0));
v___x_3299_ = lean_box(0);
v___x_3300_ = lean_obj_once(&l_Lean_instInhabitedTagAttribute_default___closed__4, &l_Lean_instInhabitedTagAttribute_default___closed__4_once, _init_l_Lean_instInhabitedTagAttribute_default___closed__4);
v___x_3301_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3301_, 0, v___x_3300_);
lean_ctor_set(v___x_3301_, 1, v___x_3299_);
lean_ctor_set(v___x_3301_, 2, v___f_3298_);
lean_ctor_set(v___x_3301_, 3, v___f_3297_);
lean_ctor_set(v___x_3301_, 4, v___f_3296_);
lean_ctor_set(v___x_3301_, 5, v___f_3295_);
return v___x_3301_;
}
}
static lean_object* _init_l_Lean_instInhabitedEnumAttributes_default___redArg___closed__4(void){
_start:
{
lean_object* v___x_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; 
v___x_3302_ = lean_obj_once(&l_Lean_instInhabitedEnumAttributes_default___redArg___closed__3, &l_Lean_instInhabitedEnumAttributes_default___redArg___closed__3_once, _init_l_Lean_instInhabitedEnumAttributes_default___redArg___closed__3);
v___x_3303_ = lean_box(0);
v___x_3304_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3304_, 0, v___x_3303_);
lean_ctor_set(v___x_3304_, 1, v___x_3302_);
return v___x_3304_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___redArg(){
_start:
{
lean_object* v___x_3306_; 
v___x_3306_ = lean_obj_once(&l_Lean_instInhabitedEnumAttributes_default___redArg___closed__4, &l_Lean_instInhabitedEnumAttributes_default___redArg___closed__4_once, _init_l_Lean_instInhabitedEnumAttributes_default___redArg___closed__4);
return v___x_3306_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___redArg___boxed(lean_object* v___dummy_3307_){
_start:
{
lean_object* v_res_3308_; 
v_res_3308_ = l_Lean_instInhabitedEnumAttributes_default___redArg();
return v_res_3308_;
}
}
static lean_object* _init_l_Lean_instInhabitedEnumAttributes_default___closed__0(void){
_start:
{
lean_object* v___x_3309_; 
v___x_3309_ = l_Lean_instInhabitedEnumAttributes_default___redArg();
return v___x_3309_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default(lean_object* v_00_u03b1_3310_){
_start:
{
lean_object* v___x_3311_; 
v___x_3311_ = lean_obj_once(&l_Lean_instInhabitedEnumAttributes_default___closed__0, &l_Lean_instInhabitedEnumAttributes_default___closed__0_once, _init_l_Lean_instInhabitedEnumAttributes_default___closed__0);
return v___x_3311_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes___redArg(){
_start:
{
lean_object* v___x_3313_; 
v___x_3313_ = lean_obj_once(&l_Lean_instInhabitedEnumAttributes_default___closed__0, &l_Lean_instInhabitedEnumAttributes_default___closed__0_once, _init_l_Lean_instInhabitedEnumAttributes_default___closed__0);
return v___x_3313_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes___redArg___boxed(lean_object* v___dummy_3314_){
_start:
{
lean_object* v_res_3315_; 
v_res_3315_ = l_Lean_instInhabitedEnumAttributes___redArg();
return v_res_3315_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes(lean_object* v_a_3316_){
_start:
{
lean_object* v___x_3317_; 
v___x_3317_ = lean_obj_once(&l_Lean_instInhabitedEnumAttributes_default___closed__0, &l_Lean_instInhabitedEnumAttributes_default___closed__0_once, _init_l_Lean_instInhabitedEnumAttributes_default___closed__0);
return v___x_3317_;
}
}
static lean_object* _init_l_Lean_registerEnumAttributes___auto__1(void){
_start:
{
lean_object* v___x_3318_; 
v___x_3318_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__28, &l_Lean_AttributeImplCore_ref___autoParam___closed__28_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__28);
return v___x_3318_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__0(lean_object* v_x_3319_){
_start:
{
lean_object* v___x_3320_; 
v___x_3320_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___redArg___lam__2___closed__0));
return v___x_3320_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__0___boxed(lean_object* v_x_3321_){
_start:
{
lean_object* v_res_3322_; 
v_res_3322_ = l_Lean_registerEnumAttributes___redArg___lam__0(v_x_3321_);
lean_dec(v_x_3321_);
return v_res_3322_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___redArg(lean_object* v_newState_3323_, lean_object* v_x_3324_, lean_object* v_x_3325_){
_start:
{
if (lean_obj_tag(v_x_3325_) == 0)
{
return v_x_3324_;
}
else
{
lean_object* v_head_3326_; lean_object* v_tail_3327_; lean_object* v___x_3328_; 
v_head_3326_ = lean_ctor_get(v_x_3325_, 0);
lean_inc(v_head_3326_);
v_tail_3327_ = lean_ctor_get(v_x_3325_, 1);
lean_inc(v_tail_3327_);
lean_dec_ref_known(v_x_3325_, 2);
v___x_3328_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_newState_3323_, v_head_3326_);
if (lean_obj_tag(v___x_3328_) == 1)
{
lean_object* v_val_3329_; lean_object* v___x_3330_; 
v_val_3329_ = lean_ctor_get(v___x_3328_, 0);
lean_inc(v_val_3329_);
lean_dec_ref_known(v___x_3328_, 1);
v___x_3330_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_head_3326_, v_val_3329_, v_x_3324_);
v_x_3324_ = v___x_3330_;
v_x_3325_ = v_tail_3327_;
goto _start;
}
else
{
lean_dec(v___x_3328_);
lean_dec(v_head_3326_);
v_x_3325_ = v_tail_3327_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___redArg___boxed(lean_object* v_newState_3333_, lean_object* v_x_3334_, lean_object* v_x_3335_){
_start:
{
lean_object* v_res_3336_; 
v_res_3336_ = l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___redArg(v_newState_3333_, v_x_3334_, v_x_3335_);
lean_dec(v_newState_3333_);
return v_res_3336_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__1(lean_object* v_x_3337_, lean_object* v_newState_3338_, lean_object* v_consts_3339_, lean_object* v_st_3340_){
_start:
{
lean_object* v___x_3341_; 
v___x_3341_ = l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___redArg(v_newState_3338_, v_st_3340_, v_consts_3339_);
return v___x_3341_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__1___boxed(lean_object* v_x_3342_, lean_object* v_newState_3343_, lean_object* v_consts_3344_, lean_object* v_st_3345_){
_start:
{
lean_object* v_res_3346_; 
v_res_3346_ = l_Lean_registerEnumAttributes___redArg___lam__1(v_x_3342_, v_newState_3343_, v_consts_3344_, v_st_3345_);
lean_dec(v_newState_3343_);
lean_dec(v_x_3342_);
return v_res_3346_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__2(lean_object* v_s_3356_){
_start:
{
lean_object* v___x_3357_; lean_object* v___y_3359_; 
v___x_3357_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___lam__2___closed__3));
if (lean_obj_tag(v_s_3356_) == 0)
{
lean_object* v_size_3363_; 
v_size_3363_ = lean_ctor_get(v_s_3356_, 0);
lean_inc(v_size_3363_);
lean_dec_ref_known(v_s_3356_, 5);
v___y_3359_ = v_size_3363_;
goto v___jp_3358_;
}
else
{
lean_object* v___x_3364_; 
v___x_3364_ = lean_unsigned_to_nat(0u);
v___y_3359_ = v___x_3364_;
goto v___jp_3358_;
}
v___jp_3358_:
{
lean_object* v___x_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; 
v___x_3360_ = l_Nat_reprFast(v___y_3359_);
v___x_3361_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3361_, 0, v___x_3360_);
v___x_3362_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3362_, 0, v___x_3357_);
lean_ctor_set(v___x_3362_, 1, v___x_3361_);
return v___x_3362_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg(lean_object* v_env_3365_, lean_object* v_as_3366_, size_t v_i_3367_, size_t v_stop_3368_, lean_object* v_b_3369_){
_start:
{
lean_object* v___y_3371_; uint8_t v___x_3375_; 
v___x_3375_ = lean_usize_dec_eq(v_i_3367_, v_stop_3368_);
if (v___x_3375_ == 0)
{
lean_object* v___x_3376_; lean_object* v_fst_3377_; uint8_t v___x_3378_; lean_object* v___x_3379_; uint8_t v___x_3380_; 
v___x_3376_ = lean_array_uget_borrowed(v_as_3366_, v_i_3367_);
v_fst_3377_ = lean_ctor_get(v___x_3376_, 0);
v___x_3378_ = 1;
lean_inc_ref(v_env_3365_);
v___x_3379_ = l_Lean_Environment_setExporting(v_env_3365_, v___x_3378_);
lean_inc(v_fst_3377_);
v___x_3380_ = l_Lean_Environment_contains(v___x_3379_, v_fst_3377_, v___x_3375_);
if (v___x_3380_ == 0)
{
v___y_3371_ = v_b_3369_;
goto v___jp_3370_;
}
else
{
lean_object* v___x_3381_; 
lean_inc(v___x_3376_);
v___x_3381_ = lean_array_push(v_b_3369_, v___x_3376_);
v___y_3371_ = v___x_3381_;
goto v___jp_3370_;
}
}
else
{
lean_dec_ref(v_env_3365_);
return v_b_3369_;
}
v___jp_3370_:
{
size_t v___x_3372_; size_t v___x_3373_; 
v___x_3372_ = ((size_t)1ULL);
v___x_3373_ = lean_usize_add(v_i_3367_, v___x_3372_);
v_i_3367_ = v___x_3373_;
v_b_3369_ = v___y_3371_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg___boxed(lean_object* v_env_3382_, lean_object* v_as_3383_, lean_object* v_i_3384_, lean_object* v_stop_3385_, lean_object* v_b_3386_){
_start:
{
size_t v_i_boxed_3387_; size_t v_stop_boxed_3388_; lean_object* v_res_3389_; 
v_i_boxed_3387_ = lean_unbox_usize(v_i_3384_);
lean_dec(v_i_3384_);
v_stop_boxed_3388_ = lean_unbox_usize(v_stop_3385_);
lean_dec(v_stop_3385_);
v_res_3389_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg(v_env_3382_, v_as_3383_, v_i_boxed_3387_, v_stop_boxed_3388_, v_b_3386_);
lean_dec_ref(v_as_3383_);
return v_res_3389_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__3(lean_object* v_env_3390_, lean_object* v_m_3391_){
_start:
{
lean_object* v___x_3392_; lean_object* v___x_3393_; lean_object* v___y_3395_; lean_object* v___x_3409_; lean_object* v___x_3410_; lean_object* v___y_3412_; lean_object* v___y_3413_; uint8_t v___x_3415_; 
v___x_3392_ = lean_unsigned_to_nat(0u);
v___x_3393_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___redArg___lam__2___closed__0));
v___x_3409_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg(v___x_3393_, v_m_3391_);
v___x_3410_ = lean_array_get_size(v___x_3409_);
v___x_3415_ = lean_nat_dec_eq(v___x_3410_, v___x_3392_);
if (v___x_3415_ == 0)
{
lean_object* v___x_3416_; lean_object* v___x_3417_; lean_object* v___y_3419_; uint8_t v___x_3421_; 
v___x_3416_ = lean_unsigned_to_nat(1u);
v___x_3417_ = lean_nat_sub(v___x_3410_, v___x_3416_);
v___x_3421_ = lean_nat_dec_le(v___x_3392_, v___x_3417_);
if (v___x_3421_ == 0)
{
lean_inc(v___x_3417_);
v___y_3419_ = v___x_3417_;
goto v___jp_3418_;
}
else
{
v___y_3419_ = v___x_3392_;
goto v___jp_3418_;
}
v___jp_3418_:
{
uint8_t v___x_3420_; 
v___x_3420_ = lean_nat_dec_le(v___y_3419_, v___x_3417_);
if (v___x_3420_ == 0)
{
lean_dec(v___x_3417_);
lean_inc(v___y_3419_);
v___y_3412_ = v___y_3419_;
v___y_3413_ = v___y_3419_;
goto v___jp_3411_;
}
else
{
v___y_3412_ = v___y_3419_;
v___y_3413_ = v___x_3417_;
goto v___jp_3411_;
}
}
}
else
{
v___y_3395_ = v___x_3409_;
goto v___jp_3394_;
}
v___jp_3394_:
{
lean_object* v___x_3396_; uint8_t v___x_3397_; 
v___x_3396_ = lean_array_get_size(v___y_3395_);
v___x_3397_ = lean_nat_dec_lt(v___x_3392_, v___x_3396_);
if (v___x_3397_ == 0)
{
lean_object* v___x_3398_; 
lean_dec_ref(v_env_3390_);
v___x_3398_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3398_, 0, v___x_3393_);
lean_ctor_set(v___x_3398_, 1, v___x_3393_);
lean_ctor_set(v___x_3398_, 2, v___y_3395_);
return v___x_3398_;
}
else
{
uint8_t v___x_3399_; 
v___x_3399_ = lean_nat_dec_le(v___x_3396_, v___x_3396_);
if (v___x_3399_ == 0)
{
if (v___x_3397_ == 0)
{
lean_object* v___x_3400_; 
lean_dec_ref(v_env_3390_);
v___x_3400_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3400_, 0, v___x_3393_);
lean_ctor_set(v___x_3400_, 1, v___x_3393_);
lean_ctor_set(v___x_3400_, 2, v___y_3395_);
return v___x_3400_;
}
else
{
size_t v___x_3401_; size_t v___x_3402_; lean_object* v___x_3403_; lean_object* v___x_3404_; 
v___x_3401_ = ((size_t)0ULL);
v___x_3402_ = lean_usize_of_nat(v___x_3396_);
v___x_3403_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg(v_env_3390_, v___y_3395_, v___x_3401_, v___x_3402_, v___x_3393_);
lean_inc_ref(v___x_3403_);
v___x_3404_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3404_, 0, v___x_3403_);
lean_ctor_set(v___x_3404_, 1, v___x_3403_);
lean_ctor_set(v___x_3404_, 2, v___y_3395_);
return v___x_3404_;
}
}
else
{
size_t v___x_3405_; size_t v___x_3406_; lean_object* v___x_3407_; lean_object* v___x_3408_; 
v___x_3405_ = ((size_t)0ULL);
v___x_3406_ = lean_usize_of_nat(v___x_3396_);
v___x_3407_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg(v_env_3390_, v___y_3395_, v___x_3405_, v___x_3406_, v___x_3393_);
lean_inc_ref(v___x_3407_);
v___x_3408_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3408_, 0, v___x_3407_);
lean_ctor_set(v___x_3408_, 1, v___x_3407_);
lean_ctor_set(v___x_3408_, 2, v___y_3395_);
return v___x_3408_;
}
}
}
v___jp_3411_:
{
lean_object* v___x_3414_; 
v___x_3414_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg(v___x_3410_, v___x_3409_, v___y_3412_, v___y_3413_);
lean_dec(v___y_3413_);
v___y_3395_ = v___x_3414_;
goto v___jp_3394_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__3___boxed(lean_object* v_env_3422_, lean_object* v_m_3423_){
_start:
{
lean_object* v_res_3424_; 
v_res_3424_ = l_Lean_registerEnumAttributes___redArg___lam__3(v_env_3422_, v_m_3423_);
lean_dec(v_m_3423_);
return v_res_3424_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__4(lean_object* v_s_3425_, lean_object* v_p_3426_){
_start:
{
lean_object* v_fst_3427_; lean_object* v_snd_3428_; lean_object* v___x_3429_; 
v_fst_3427_ = lean_ctor_get(v_p_3426_, 0);
lean_inc(v_fst_3427_);
v_snd_3428_ = lean_ctor_get(v_p_3426_, 1);
lean_inc(v_snd_3428_);
lean_dec_ref(v_p_3426_);
v___x_3429_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_3427_, v_snd_3428_, v_s_3425_);
return v___x_3429_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__6(lean_object* v___x_3430_, lean_object* v_x_3431_, lean_object* v_x_3432_){
_start:
{
lean_object* v___x_3434_; 
v___x_3434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3434_, 0, v___x_3430_);
return v___x_3434_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__6___boxed(lean_object* v___x_3435_, lean_object* v_x_3436_, lean_object* v_x_3437_, lean_object* v___y_3438_){
_start:
{
lean_object* v_res_3439_; 
v_res_3439_ = l_Lean_registerEnumAttributes___redArg___lam__6(v___x_3435_, v_x_3436_, v_x_3437_);
lean_dec_ref(v_x_3437_);
lean_dec_ref(v_x_3436_);
return v_res_3439_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_registerEnumAttributes_spec__3(lean_object* v_as_3440_){
_start:
{
if (lean_obj_tag(v_as_3440_) == 0)
{
lean_object* v___x_3442_; lean_object* v___x_3443_; 
v___x_3442_ = lean_box(0);
v___x_3443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3443_, 0, v___x_3442_);
return v___x_3443_;
}
else
{
lean_object* v_head_3444_; lean_object* v_tail_3445_; lean_object* v___x_3446_; 
v_head_3444_ = lean_ctor_get(v_as_3440_, 0);
lean_inc(v_head_3444_);
v_tail_3445_ = lean_ctor_get(v_as_3440_, 1);
lean_inc(v_tail_3445_);
lean_dec_ref_known(v_as_3440_, 2);
v___x_3446_ = l_Lean_registerBuiltinAttribute(v_head_3444_);
if (lean_obj_tag(v___x_3446_) == 0)
{
lean_dec_ref_known(v___x_3446_, 1);
v_as_3440_ = v_tail_3445_;
goto _start;
}
else
{
lean_dec(v_tail_3445_);
return v___x_3446_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_registerEnumAttributes_spec__3___boxed(lean_object* v_as_3448_, lean_object* v___y_3449_){
_start:
{
lean_object* v_res_3450_; 
v_res_3450_ = l_List_forM___at___00Lean_registerEnumAttributes_spec__3(v_as_3448_);
return v_res_3450_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__1(lean_object* v_validate_3451_, lean_object* v_snd_3452_, lean_object* v_a_3453_, lean_object* v_fst_3454_, lean_object* v_decl_3455_, lean_object* v_stx_3456_, uint8_t v_kind_3457_, lean_object* v___y_3458_, lean_object* v___y_3459_){
_start:
{
lean_object* v___y_3462_; lean_object* v___y_3463_; lean_object* v___x_3503_; 
v___x_3503_ = l_Lean_Attribute_Builtin_ensureNoArgs(v_stx_3456_, v___y_3458_, v___y_3459_);
if (lean_obj_tag(v___x_3503_) == 0)
{
uint8_t v___x_3504_; uint8_t v___x_3505_; 
lean_dec_ref_known(v___x_3503_, 1);
v___x_3504_ = 0;
v___x_3505_ = l_Lean_instBEqAttributeKind_beq(v_kind_3457_, v___x_3504_);
if (v___x_3505_ == 0)
{
lean_object* v___x_3506_; 
lean_dec(v_decl_3455_);
lean_dec_ref(v_a_3453_);
lean_dec(v_snd_3452_);
lean_dec_ref(v_validate_3451_);
v___x_3506_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg(v_fst_3454_, v_kind_3457_, v___y_3458_, v___y_3459_);
return v___x_3506_;
}
else
{
goto v___jp_3498_;
}
}
else
{
lean_dec(v_decl_3455_);
lean_dec(v_fst_3454_);
lean_dec_ref(v_a_3453_);
lean_dec(v_snd_3452_);
lean_dec_ref(v_validate_3451_);
return v___x_3503_;
}
v___jp_3461_:
{
lean_object* v___x_3464_; 
lean_inc(v___y_3463_);
lean_inc_ref(v___y_3462_);
lean_inc(v_snd_3452_);
lean_inc(v_decl_3455_);
v___x_3464_ = lean_apply_5(v_validate_3451_, v_decl_3455_, v_snd_3452_, v___y_3462_, v___y_3463_, lean_box(0));
if (lean_obj_tag(v___x_3464_) == 0)
{
lean_object* v___x_3466_; uint8_t v_isShared_3467_; uint8_t v_isSharedCheck_3496_; 
v_isSharedCheck_3496_ = !lean_is_exclusive(v___x_3464_);
if (v_isSharedCheck_3496_ == 0)
{
lean_object* v_unused_3497_; 
v_unused_3497_ = lean_ctor_get(v___x_3464_, 0);
lean_dec(v_unused_3497_);
v___x_3466_ = v___x_3464_;
v_isShared_3467_ = v_isSharedCheck_3496_;
goto v_resetjp_3465_;
}
else
{
lean_dec(v___x_3464_);
v___x_3466_ = lean_box(0);
v_isShared_3467_ = v_isSharedCheck_3496_;
goto v_resetjp_3465_;
}
v_resetjp_3465_:
{
lean_object* v___x_3468_; lean_object* v_toEnvExtension_3469_; lean_object* v_env_3470_; lean_object* v_nextMacroScope_3471_; lean_object* v_ngen_3472_; lean_object* v_auxDeclNGen_3473_; lean_object* v_traceState_3474_; lean_object* v_recordedDeps_3475_; lean_object* v_messages_3476_; lean_object* v_infoState_3477_; lean_object* v_snapshotTasks_3478_; lean_object* v___x_3480_; uint8_t v_isShared_3481_; uint8_t v_isSharedCheck_3494_; 
v___x_3468_ = lean_st_ref_take(v___y_3463_);
v_toEnvExtension_3469_ = lean_ctor_get(v_a_3453_, 0);
v_env_3470_ = lean_ctor_get(v___x_3468_, 0);
v_nextMacroScope_3471_ = lean_ctor_get(v___x_3468_, 1);
v_ngen_3472_ = lean_ctor_get(v___x_3468_, 2);
v_auxDeclNGen_3473_ = lean_ctor_get(v___x_3468_, 3);
v_traceState_3474_ = lean_ctor_get(v___x_3468_, 4);
v_recordedDeps_3475_ = lean_ctor_get(v___x_3468_, 6);
v_messages_3476_ = lean_ctor_get(v___x_3468_, 7);
v_infoState_3477_ = lean_ctor_get(v___x_3468_, 8);
v_snapshotTasks_3478_ = lean_ctor_get(v___x_3468_, 9);
v_isSharedCheck_3494_ = !lean_is_exclusive(v___x_3468_);
if (v_isSharedCheck_3494_ == 0)
{
lean_object* v_unused_3495_; 
v_unused_3495_ = lean_ctor_get(v___x_3468_, 5);
lean_dec(v_unused_3495_);
v___x_3480_ = v___x_3468_;
v_isShared_3481_ = v_isSharedCheck_3494_;
goto v_resetjp_3479_;
}
else
{
lean_inc(v_snapshotTasks_3478_);
lean_inc(v_infoState_3477_);
lean_inc(v_messages_3476_);
lean_inc(v_recordedDeps_3475_);
lean_inc(v_traceState_3474_);
lean_inc(v_auxDeclNGen_3473_);
lean_inc(v_ngen_3472_);
lean_inc(v_nextMacroScope_3471_);
lean_inc(v_env_3470_);
lean_dec(v___x_3468_);
v___x_3480_ = lean_box(0);
v_isShared_3481_ = v_isSharedCheck_3494_;
goto v_resetjp_3479_;
}
v_resetjp_3479_:
{
lean_object* v_asyncMode_3482_; lean_object* v___x_3483_; lean_object* v___x_3484_; lean_object* v___x_3485_; lean_object* v___x_3486_; lean_object* v___x_3488_; 
v_asyncMode_3482_ = lean_ctor_get(v_toEnvExtension_3469_, 2);
lean_inc(v_asyncMode_3482_);
v___x_3483_ = lean_box(0);
lean_inc(v_decl_3455_);
v___x_3484_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3484_, 0, v_decl_3455_);
lean_ctor_set(v___x_3484_, 1, v_snd_3452_);
v___x_3485_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_a_3453_, v_env_3470_, v___x_3484_, v_asyncMode_3482_, v_decl_3455_);
lean_dec(v_asyncMode_3482_);
v___x_3486_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1);
if (v_isShared_3481_ == 0)
{
lean_ctor_set(v___x_3480_, 5, v___x_3486_);
lean_ctor_set(v___x_3480_, 0, v___x_3485_);
v___x_3488_ = v___x_3480_;
goto v_reusejp_3487_;
}
else
{
lean_object* v_reuseFailAlloc_3493_; 
v_reuseFailAlloc_3493_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3493_, 0, v___x_3485_);
lean_ctor_set(v_reuseFailAlloc_3493_, 1, v_nextMacroScope_3471_);
lean_ctor_set(v_reuseFailAlloc_3493_, 2, v_ngen_3472_);
lean_ctor_set(v_reuseFailAlloc_3493_, 3, v_auxDeclNGen_3473_);
lean_ctor_set(v_reuseFailAlloc_3493_, 4, v_traceState_3474_);
lean_ctor_set(v_reuseFailAlloc_3493_, 5, v___x_3486_);
lean_ctor_set(v_reuseFailAlloc_3493_, 6, v_recordedDeps_3475_);
lean_ctor_set(v_reuseFailAlloc_3493_, 7, v_messages_3476_);
lean_ctor_set(v_reuseFailAlloc_3493_, 8, v_infoState_3477_);
lean_ctor_set(v_reuseFailAlloc_3493_, 9, v_snapshotTasks_3478_);
v___x_3488_ = v_reuseFailAlloc_3493_;
goto v_reusejp_3487_;
}
v_reusejp_3487_:
{
lean_object* v___x_3489_; lean_object* v___x_3491_; 
v___x_3489_ = lean_st_ref_put(v___y_3463_, v___x_3488_);
if (v_isShared_3467_ == 0)
{
lean_ctor_set(v___x_3466_, 0, v___x_3483_);
v___x_3491_ = v___x_3466_;
goto v_reusejp_3490_;
}
else
{
lean_object* v_reuseFailAlloc_3492_; 
v_reuseFailAlloc_3492_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3492_, 0, v___x_3483_);
v___x_3491_ = v_reuseFailAlloc_3492_;
goto v_reusejp_3490_;
}
v_reusejp_3490_:
{
return v___x_3491_;
}
}
}
}
}
else
{
lean_dec(v_decl_3455_);
lean_dec_ref(v_a_3453_);
lean_dec(v_snd_3452_);
return v___x_3464_;
}
}
v___jp_3498_:
{
lean_object* v___x_3499_; lean_object* v_env_3500_; lean_object* v___x_3501_; 
v___x_3499_ = lean_st_ref_get(v___y_3459_);
v_env_3500_ = lean_ctor_get(v___x_3499_, 0);
lean_inc_ref(v_env_3500_);
lean_dec(v___x_3499_);
v___x_3501_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3500_, v_decl_3455_);
lean_dec_ref(v_env_3500_);
if (lean_obj_tag(v___x_3501_) == 0)
{
lean_dec(v_fst_3454_);
v___y_3462_ = v___y_3458_;
v___y_3463_ = v___y_3459_;
goto v___jp_3461_;
}
else
{
lean_object* v___x_3502_; 
lean_dec_ref_known(v___x_3501_, 1);
lean_dec_ref(v_a_3453_);
lean_dec(v_snd_3452_);
lean_dec_ref(v_validate_3451_);
v___x_3502_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg(v_fst_3454_, v_decl_3455_, v___y_3458_, v___y_3459_);
return v___x_3502_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__1___boxed(lean_object* v_validate_3507_, lean_object* v_snd_3508_, lean_object* v_a_3509_, lean_object* v_fst_3510_, lean_object* v_decl_3511_, lean_object* v_stx_3512_, lean_object* v_kind_3513_, lean_object* v___y_3514_, lean_object* v___y_3515_, lean_object* v___y_3516_){
_start:
{
uint8_t v_kind_boxed_3517_; lean_object* v_res_3518_; 
v_kind_boxed_3517_ = lean_unbox(v_kind_3513_);
v_res_3518_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__1(v_validate_3507_, v_snd_3508_, v_a_3509_, v_fst_3510_, v_decl_3511_, v_stx_3512_, v_kind_boxed_3517_, v___y_3514_, v___y_3515_);
lean_dec(v___y_3515_);
lean_dec_ref(v___y_3514_);
return v_res_3518_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__0(lean_object* v_fst_3519_, lean_object* v_decl_3520_, lean_object* v___y_3521_, lean_object* v___y_3522_){
_start:
{
lean_object* v___x_3524_; lean_object* v___x_3525_; lean_object* v___x_3526_; lean_object* v___x_3527_; lean_object* v___x_3528_; lean_object* v___x_3529_; 
v___x_3524_ = lean_obj_once(&l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1, &l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1_once, _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1);
v___x_3525_ = l_Lean_MessageData_ofName(v_fst_3519_);
v___x_3526_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3526_, 0, v___x_3524_);
lean_ctor_set(v___x_3526_, 1, v___x_3525_);
v___x_3527_ = lean_obj_once(&l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3, &l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3_once, _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3);
v___x_3528_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3528_, 0, v___x_3526_);
lean_ctor_set(v___x_3528_, 1, v___x_3527_);
v___x_3529_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_3528_, v___y_3521_, v___y_3522_);
return v___x_3529_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__0___boxed(lean_object* v_fst_3530_, lean_object* v_decl_3531_, lean_object* v___y_3532_, lean_object* v___y_3533_, lean_object* v___y_3534_){
_start:
{
lean_object* v_res_3535_; 
v_res_3535_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__0(v_fst_3530_, v_decl_3531_, v___y_3532_, v___y_3533_);
lean_dec(v___y_3533_);
lean_dec_ref(v___y_3532_);
lean_dec(v_decl_3531_);
return v_res_3535_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg(lean_object* v_validate_3536_, lean_object* v_a_3537_, lean_object* v_ref_3538_, uint8_t v_applicationTime_3539_, lean_object* v_a_3540_, lean_object* v_a_3541_){
_start:
{
if (lean_obj_tag(v_a_3540_) == 0)
{
lean_object* v___x_3542_; 
lean_dec(v_ref_3538_);
lean_dec_ref(v_a_3537_);
lean_dec_ref(v_validate_3536_);
v___x_3542_ = l_List_reverse___redArg(v_a_3541_);
return v___x_3542_;
}
else
{
lean_object* v_head_3543_; lean_object* v_snd_3544_; lean_object* v_tail_3545_; lean_object* v___x_3547_; uint8_t v_isShared_3548_; uint8_t v_isSharedCheck_3560_; 
v_head_3543_ = lean_ctor_get(v_a_3540_, 0);
lean_inc(v_head_3543_);
v_snd_3544_ = lean_ctor_get(v_head_3543_, 1);
lean_inc(v_snd_3544_);
v_tail_3545_ = lean_ctor_get(v_a_3540_, 1);
v_isSharedCheck_3560_ = !lean_is_exclusive(v_a_3540_);
if (v_isSharedCheck_3560_ == 0)
{
lean_object* v_unused_3561_; 
v_unused_3561_ = lean_ctor_get(v_a_3540_, 0);
lean_dec(v_unused_3561_);
v___x_3547_ = v_a_3540_;
v_isShared_3548_ = v_isSharedCheck_3560_;
goto v_resetjp_3546_;
}
else
{
lean_inc(v_tail_3545_);
lean_dec(v_a_3540_);
v___x_3547_ = lean_box(0);
v_isShared_3548_ = v_isSharedCheck_3560_;
goto v_resetjp_3546_;
}
v_resetjp_3546_:
{
lean_object* v_fst_3549_; lean_object* v_fst_3550_; lean_object* v_snd_3551_; lean_object* v___f_3552_; lean_object* v___f_3553_; lean_object* v___x_3554_; lean_object* v___x_3555_; lean_object* v___x_3557_; 
v_fst_3549_ = lean_ctor_get(v_head_3543_, 0);
lean_inc_n(v_fst_3549_, 3);
lean_dec(v_head_3543_);
v_fst_3550_ = lean_ctor_get(v_snd_3544_, 0);
lean_inc(v_fst_3550_);
v_snd_3551_ = lean_ctor_get(v_snd_3544_, 1);
lean_inc(v_snd_3551_);
lean_dec(v_snd_3544_);
v___f_3552_ = lean_alloc_closure((void*)(l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__0___boxed), 5, 1);
lean_closure_set(v___f_3552_, 0, v_fst_3549_);
lean_inc_ref(v_a_3537_);
lean_inc_ref(v_validate_3536_);
v___f_3553_ = lean_alloc_closure((void*)(l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__1___boxed), 10, 4);
lean_closure_set(v___f_3553_, 0, v_validate_3536_);
lean_closure_set(v___f_3553_, 1, v_snd_3551_);
lean_closure_set(v___f_3553_, 2, v_a_3537_);
lean_closure_set(v___f_3553_, 3, v_fst_3549_);
lean_inc(v_ref_3538_);
v___x_3554_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_3554_, 0, v_ref_3538_);
lean_ctor_set(v___x_3554_, 1, v_fst_3549_);
lean_ctor_set(v___x_3554_, 2, v_fst_3550_);
lean_ctor_set_uint8(v___x_3554_, sizeof(void*)*3, v_applicationTime_3539_);
v___x_3555_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3555_, 0, v___x_3554_);
lean_ctor_set(v___x_3555_, 1, v___f_3553_);
lean_ctor_set(v___x_3555_, 2, v___f_3552_);
if (v_isShared_3548_ == 0)
{
lean_ctor_set(v___x_3547_, 1, v_a_3541_);
lean_ctor_set(v___x_3547_, 0, v___x_3555_);
v___x_3557_ = v___x_3547_;
goto v_reusejp_3556_;
}
else
{
lean_object* v_reuseFailAlloc_3559_; 
v_reuseFailAlloc_3559_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3559_, 0, v___x_3555_);
lean_ctor_set(v_reuseFailAlloc_3559_, 1, v_a_3541_);
v___x_3557_ = v_reuseFailAlloc_3559_;
goto v_reusejp_3556_;
}
v_reusejp_3556_:
{
v_a_3540_ = v_tail_3545_;
v_a_3541_ = v___x_3557_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___boxed(lean_object* v_validate_3562_, lean_object* v_a_3563_, lean_object* v_ref_3564_, lean_object* v_applicationTime_3565_, lean_object* v_a_3566_, lean_object* v_a_3567_){
_start:
{
uint8_t v_applicationTime_boxed_3568_; lean_object* v_res_3569_; 
v_applicationTime_boxed_3568_ = lean_unbox(v_applicationTime_3565_);
v_res_3569_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg(v_validate_3562_, v_a_3563_, v_ref_3564_, v_applicationTime_boxed_3568_, v_a_3566_, v_a_3567_);
return v_res_3569_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg(lean_object* v_attrDescrs_3583_, lean_object* v_validate_3584_, uint8_t v_applicationTime_3585_, lean_object* v_ref_3586_){
_start:
{
lean_object* v___f_3588_; lean_object* v___f_3589_; lean_object* v___f_3590_; lean_object* v___f_3591_; lean_object* v___f_3592_; lean_object* v___f_3593_; lean_object* v___x_3594_; lean_object* v___x_3595_; lean_object* v___x_3596_; lean_object* v___x_3597_; lean_object* v___x_3598_; 
v___f_3588_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__0));
v___f_3589_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__2));
v___f_3590_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__3));
v___f_3591_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__4));
v___f_3592_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__5));
v___f_3593_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__6));
v___x_3594_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__7));
v___x_3595_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__8));
lean_inc(v_ref_3586_);
v___x_3596_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_3596_, 0, v_ref_3586_);
lean_ctor_set(v___x_3596_, 1, v___f_3592_);
lean_ctor_set(v___x_3596_, 2, v___f_3593_);
lean_ctor_set(v___x_3596_, 3, v___f_3591_);
lean_ctor_set(v___x_3596_, 4, v___f_3590_);
lean_ctor_set(v___x_3596_, 5, v___f_3589_);
lean_ctor_set(v___x_3596_, 6, v___x_3594_);
lean_ctor_set(v___x_3596_, 7, v___x_3595_);
v___x_3597_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3597_, 0, v___x_3596_);
lean_ctor_set(v___x_3597_, 1, v___f_3588_);
v___x_3598_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_3597_);
if (lean_obj_tag(v___x_3598_) == 0)
{
lean_object* v_a_3599_; lean_object* v___x_3600_; lean_object* v___x_3601_; lean_object* v___x_3602_; 
v_a_3599_ = lean_ctor_get(v___x_3598_, 0);
lean_inc_n(v_a_3599_, 2);
lean_dec_ref_known(v___x_3598_, 1);
v___x_3600_ = lean_box(0);
v___x_3601_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg(v_validate_3584_, v_a_3599_, v_ref_3586_, v_applicationTime_3585_, v_attrDescrs_3583_, v___x_3600_);
lean_inc(v___x_3601_);
v___x_3602_ = l_List_forM___at___00Lean_registerEnumAttributes_spec__3(v___x_3601_);
if (lean_obj_tag(v___x_3602_) == 0)
{
lean_object* v___x_3604_; uint8_t v_isShared_3605_; uint8_t v_isSharedCheck_3610_; 
v_isSharedCheck_3610_ = !lean_is_exclusive(v___x_3602_);
if (v_isSharedCheck_3610_ == 0)
{
lean_object* v_unused_3611_; 
v_unused_3611_ = lean_ctor_get(v___x_3602_, 0);
lean_dec(v_unused_3611_);
v___x_3604_ = v___x_3602_;
v_isShared_3605_ = v_isSharedCheck_3610_;
goto v_resetjp_3603_;
}
else
{
lean_dec(v___x_3602_);
v___x_3604_ = lean_box(0);
v_isShared_3605_ = v_isSharedCheck_3610_;
goto v_resetjp_3603_;
}
v_resetjp_3603_:
{
lean_object* v___x_3606_; lean_object* v___x_3608_; 
v___x_3606_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3606_, 0, v___x_3601_);
lean_ctor_set(v___x_3606_, 1, v_a_3599_);
if (v_isShared_3605_ == 0)
{
lean_ctor_set(v___x_3604_, 0, v___x_3606_);
v___x_3608_ = v___x_3604_;
goto v_reusejp_3607_;
}
else
{
lean_object* v_reuseFailAlloc_3609_; 
v_reuseFailAlloc_3609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3609_, 0, v___x_3606_);
v___x_3608_ = v_reuseFailAlloc_3609_;
goto v_reusejp_3607_;
}
v_reusejp_3607_:
{
return v___x_3608_;
}
}
}
else
{
lean_object* v_a_3612_; lean_object* v___x_3614_; uint8_t v_isShared_3615_; uint8_t v_isSharedCheck_3619_; 
lean_dec(v___x_3601_);
lean_dec(v_a_3599_);
v_a_3612_ = lean_ctor_get(v___x_3602_, 0);
v_isSharedCheck_3619_ = !lean_is_exclusive(v___x_3602_);
if (v_isSharedCheck_3619_ == 0)
{
v___x_3614_ = v___x_3602_;
v_isShared_3615_ = v_isSharedCheck_3619_;
goto v_resetjp_3613_;
}
else
{
lean_inc(v_a_3612_);
lean_dec(v___x_3602_);
v___x_3614_ = lean_box(0);
v_isShared_3615_ = v_isSharedCheck_3619_;
goto v_resetjp_3613_;
}
v_resetjp_3613_:
{
lean_object* v___x_3617_; 
if (v_isShared_3615_ == 0)
{
v___x_3617_ = v___x_3614_;
goto v_reusejp_3616_;
}
else
{
lean_object* v_reuseFailAlloc_3618_; 
v_reuseFailAlloc_3618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3618_, 0, v_a_3612_);
v___x_3617_ = v_reuseFailAlloc_3618_;
goto v_reusejp_3616_;
}
v_reusejp_3616_:
{
return v___x_3617_;
}
}
}
}
else
{
lean_object* v_a_3620_; lean_object* v___x_3622_; uint8_t v_isShared_3623_; uint8_t v_isSharedCheck_3627_; 
lean_dec(v_ref_3586_);
lean_dec_ref(v_validate_3584_);
lean_dec(v_attrDescrs_3583_);
v_a_3620_ = lean_ctor_get(v___x_3598_, 0);
v_isSharedCheck_3627_ = !lean_is_exclusive(v___x_3598_);
if (v_isSharedCheck_3627_ == 0)
{
v___x_3622_ = v___x_3598_;
v_isShared_3623_ = v_isSharedCheck_3627_;
goto v_resetjp_3621_;
}
else
{
lean_inc(v_a_3620_);
lean_dec(v___x_3598_);
v___x_3622_ = lean_box(0);
v_isShared_3623_ = v_isSharedCheck_3627_;
goto v_resetjp_3621_;
}
v_resetjp_3621_:
{
lean_object* v___x_3625_; 
if (v_isShared_3623_ == 0)
{
v___x_3625_ = v___x_3622_;
goto v_reusejp_3624_;
}
else
{
lean_object* v_reuseFailAlloc_3626_; 
v_reuseFailAlloc_3626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3626_, 0, v_a_3620_);
v___x_3625_ = v_reuseFailAlloc_3626_;
goto v_reusejp_3624_;
}
v_reusejp_3624_:
{
return v___x_3625_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___boxed(lean_object* v_attrDescrs_3628_, lean_object* v_validate_3629_, lean_object* v_applicationTime_3630_, lean_object* v_ref_3631_, lean_object* v_a_3632_){
_start:
{
uint8_t v_applicationTime_boxed_3633_; lean_object* v_res_3634_; 
v_applicationTime_boxed_3633_ = lean_unbox(v_applicationTime_3630_);
v_res_3634_ = l_Lean_registerEnumAttributes___redArg(v_attrDescrs_3628_, v_validate_3629_, v_applicationTime_boxed_3633_, v_ref_3631_);
return v_res_3634_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes(lean_object* v_00_u03b1_3635_, lean_object* v_attrDescrs_3636_, lean_object* v_validate_3637_, uint8_t v_applicationTime_3638_, lean_object* v_ref_3639_){
_start:
{
lean_object* v___x_3641_; 
v___x_3641_ = l_Lean_registerEnumAttributes___redArg(v_attrDescrs_3636_, v_validate_3637_, v_applicationTime_3638_, v_ref_3639_);
return v___x_3641_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___boxed(lean_object* v_00_u03b1_3642_, lean_object* v_attrDescrs_3643_, lean_object* v_validate_3644_, lean_object* v_applicationTime_3645_, lean_object* v_ref_3646_, lean_object* v_a_3647_){
_start:
{
uint8_t v_applicationTime_boxed_3648_; lean_object* v_res_3649_; 
v_applicationTime_boxed_3648_ = lean_unbox(v_applicationTime_3645_);
v_res_3649_ = l_Lean_registerEnumAttributes(v_00_u03b1_3642_, v_attrDescrs_3643_, v_validate_3644_, v_applicationTime_boxed_3648_, v_ref_3646_);
return v_res_3649_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0(lean_object* v_00_u03b1_3650_, lean_object* v_env_3651_, lean_object* v_as_3652_, size_t v_i_3653_, size_t v_stop_3654_, lean_object* v_b_3655_){
_start:
{
lean_object* v___x_3656_; 
v___x_3656_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg(v_env_3651_, v_as_3652_, v_i_3653_, v_stop_3654_, v_b_3655_);
return v___x_3656_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___boxed(lean_object* v_00_u03b1_3657_, lean_object* v_env_3658_, lean_object* v_as_3659_, lean_object* v_i_3660_, lean_object* v_stop_3661_, lean_object* v_b_3662_){
_start:
{
size_t v_i_boxed_3663_; size_t v_stop_boxed_3664_; lean_object* v_res_3665_; 
v_i_boxed_3663_ = lean_unbox_usize(v_i_3660_);
lean_dec(v_i_3660_);
v_stop_boxed_3664_ = lean_unbox_usize(v_stop_3661_);
lean_dec(v_stop_3661_);
v_res_3665_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0(v_00_u03b1_3657_, v_env_3658_, v_as_3659_, v_i_boxed_3663_, v_stop_boxed_3664_, v_b_3662_);
lean_dec_ref(v_as_3659_);
return v_res_3665_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerEnumAttributes_spec__1(lean_object* v_00_u03b1_3666_, lean_object* v_newState_3667_, lean_object* v_x_3668_, lean_object* v_x_3669_){
_start:
{
lean_object* v___x_3670_; 
v___x_3670_ = l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___redArg(v_newState_3667_, v_x_3668_, v_x_3669_);
return v___x_3670_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___boxed(lean_object* v_00_u03b1_3671_, lean_object* v_newState_3672_, lean_object* v_x_3673_, lean_object* v_x_3674_){
_start:
{
lean_object* v_res_3675_; 
v_res_3675_ = l_List_foldl___at___00Lean_registerEnumAttributes_spec__1(v_00_u03b1_3671_, v_newState_3672_, v_x_3673_, v_x_3674_);
lean_dec(v_newState_3672_);
return v_res_3675_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2(lean_object* v_00_u03b1_3676_, lean_object* v_validate_3677_, lean_object* v_a_3678_, lean_object* v_ref_3679_, uint8_t v_applicationTime_3680_, lean_object* v_a_3681_, lean_object* v_a_3682_){
_start:
{
lean_object* v___x_3683_; 
v___x_3683_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg(v_validate_3677_, v_a_3678_, v_ref_3679_, v_applicationTime_3680_, v_a_3681_, v_a_3682_);
return v___x_3683_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___boxed(lean_object* v_00_u03b1_3684_, lean_object* v_validate_3685_, lean_object* v_a_3686_, lean_object* v_ref_3687_, lean_object* v_applicationTime_3688_, lean_object* v_a_3689_, lean_object* v_a_3690_){
_start:
{
uint8_t v_applicationTime_boxed_3691_; lean_object* v_res_3692_; 
v_applicationTime_boxed_3691_ = lean_unbox(v_applicationTime_3688_);
v_res_3692_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2(v_00_u03b1_3684_, v_validate_3685_, v_a_3686_, v_ref_3687_, v_applicationTime_boxed_3691_, v_a_3689_, v_a_3690_);
return v_res_3692_;
}
}
LEAN_EXPORT lean_object* l_Lean_EnumAttributes_getValue___redArg(lean_object* v_inst_3693_, lean_object* v_attr_3694_, lean_object* v_env_3695_, lean_object* v_decl_3696_){
_start:
{
lean_object* v___x_3697_; lean_object* v___x_3698_; 
v___x_3697_ = lean_box(1);
v___x_3698_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3695_, v_decl_3696_);
if (lean_obj_tag(v___x_3698_) == 0)
{
lean_object* v_ext_3699_; lean_object* v_toEnvExtension_3700_; lean_object* v_asyncMode_3701_; lean_object* v___x_3702_; lean_object* v___x_3703_; 
lean_dec(v_inst_3693_);
v_ext_3699_ = lean_ctor_get(v_attr_3694_, 1);
lean_inc_ref(v_ext_3699_);
lean_dec_ref(v_attr_3694_);
v_toEnvExtension_3700_ = lean_ctor_get(v_ext_3699_, 0);
v_asyncMode_3701_ = lean_ctor_get(v_toEnvExtension_3700_, 2);
lean_inc(v_asyncMode_3701_);
lean_inc(v_decl_3696_);
v___x_3702_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3697_, v_ext_3699_, v_env_3695_, v_asyncMode_3701_, v_decl_3696_);
lean_dec(v_asyncMode_3701_);
lean_dec_ref(v_ext_3699_);
v___x_3703_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_3702_, v_decl_3696_);
lean_dec(v_decl_3696_);
lean_dec(v___x_3702_);
return v___x_3703_;
}
else
{
lean_object* v_val_3704_; lean_object* v_ext_3705_; lean_object* v___x_3707_; uint8_t v_isShared_3708_; uint8_t v_isSharedCheck_3735_; 
v_val_3704_ = lean_ctor_get(v___x_3698_, 0);
lean_inc(v_val_3704_);
lean_dec_ref_known(v___x_3698_, 1);
v_ext_3705_ = lean_ctor_get(v_attr_3694_, 1);
v_isSharedCheck_3735_ = !lean_is_exclusive(v_attr_3694_);
if (v_isSharedCheck_3735_ == 0)
{
lean_object* v_unused_3736_; 
v_unused_3736_ = lean_ctor_get(v_attr_3694_, 0);
lean_dec(v_unused_3736_);
v___x_3707_ = v_attr_3694_;
v_isShared_3708_ = v_isSharedCheck_3735_;
goto v_resetjp_3706_;
}
else
{
lean_inc(v_ext_3705_);
lean_dec(v_attr_3694_);
v___x_3707_ = lean_box(0);
v_isShared_3708_ = v_isSharedCheck_3735_;
goto v_resetjp_3706_;
}
v_resetjp_3706_:
{
uint8_t v___x_3709_; lean_object* v___x_3710_; lean_object* v___x_3711_; lean_object* v___x_3712_; uint8_t v___x_3713_; 
v___x_3709_ = 0;
v___x_3710_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_3697_, v_ext_3705_, v_env_3695_, v_val_3704_, v___x_3709_);
lean_dec(v_val_3704_);
lean_dec_ref(v_env_3695_);
lean_dec_ref(v_ext_3705_);
v___x_3711_ = lean_unsigned_to_nat(0u);
v___x_3712_ = lean_array_get_size(v___x_3710_);
v___x_3713_ = lean_nat_dec_lt(v___x_3711_, v___x_3712_);
if (v___x_3713_ == 0)
{
lean_object* v___x_3714_; 
lean_dec_ref(v___x_3710_);
lean_del_object(v___x_3707_);
lean_dec(v_decl_3696_);
lean_dec(v_inst_3693_);
v___x_3714_ = lean_box(0);
return v___x_3714_;
}
else
{
lean_object* v___x_3715_; lean_object* v___x_3716_; uint8_t v___x_3717_; 
v___x_3715_ = lean_unsigned_to_nat(1u);
v___x_3716_ = lean_nat_sub(v___x_3712_, v___x_3715_);
v___x_3717_ = lean_nat_dec_le(v___x_3711_, v___x_3716_);
if (v___x_3717_ == 0)
{
lean_object* v___x_3718_; 
lean_dec(v___x_3716_);
lean_dec_ref(v___x_3710_);
lean_del_object(v___x_3707_);
lean_dec(v_decl_3696_);
lean_dec(v_inst_3693_);
v___x_3718_ = lean_box(0);
return v___x_3718_;
}
else
{
lean_object* v___f_3719_; lean_object* v___x_3721_; 
v___f_3719_ = ((lean_object*)(l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__1));
if (v_isShared_3708_ == 0)
{
lean_ctor_set(v___x_3707_, 1, v_inst_3693_);
lean_ctor_set(v___x_3707_, 0, v_decl_3696_);
v___x_3721_ = v___x_3707_;
goto v_reusejp_3720_;
}
else
{
lean_object* v_reuseFailAlloc_3734_; 
v_reuseFailAlloc_3734_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3734_, 0, v_decl_3696_);
lean_ctor_set(v_reuseFailAlloc_3734_, 1, v_inst_3693_);
v___x_3721_ = v_reuseFailAlloc_3734_;
goto v_reusejp_3720_;
}
v_reusejp_3720_:
{
lean_object* v___x_3722_; lean_object* v___x_3723_; 
v___x_3722_ = ((lean_object*)(l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__2));
v___x_3723_ = l_Array_binSearchAux___redArg(v___f_3719_, v___x_3722_, v___x_3710_, v___x_3721_, v___x_3711_, v___x_3716_);
lean_dec_ref(v___x_3710_);
if (lean_obj_tag(v___x_3723_) == 0)
{
lean_object* v___x_3724_; 
v___x_3724_ = lean_box(0);
return v___x_3724_;
}
else
{
lean_object* v_val_3725_; lean_object* v___x_3727_; uint8_t v_isShared_3728_; uint8_t v_isSharedCheck_3733_; 
v_val_3725_ = lean_ctor_get(v___x_3723_, 0);
v_isSharedCheck_3733_ = !lean_is_exclusive(v___x_3723_);
if (v_isSharedCheck_3733_ == 0)
{
v___x_3727_ = v___x_3723_;
v_isShared_3728_ = v_isSharedCheck_3733_;
goto v_resetjp_3726_;
}
else
{
lean_inc(v_val_3725_);
lean_dec(v___x_3723_);
v___x_3727_ = lean_box(0);
v_isShared_3728_ = v_isSharedCheck_3733_;
goto v_resetjp_3726_;
}
v_resetjp_3726_:
{
lean_object* v_snd_3729_; lean_object* v___x_3731_; 
v_snd_3729_ = lean_ctor_get(v_val_3725_, 1);
lean_inc(v_snd_3729_);
lean_dec(v_val_3725_);
if (v_isShared_3728_ == 0)
{
lean_ctor_set(v___x_3727_, 0, v_snd_3729_);
v___x_3731_ = v___x_3727_;
goto v_reusejp_3730_;
}
else
{
lean_object* v_reuseFailAlloc_3732_; 
v_reuseFailAlloc_3732_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3732_, 0, v_snd_3729_);
v___x_3731_ = v_reuseFailAlloc_3732_;
goto v_reusejp_3730_;
}
v_reusejp_3730_:
{
return v___x_3731_;
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
LEAN_EXPORT lean_object* l_Lean_EnumAttributes_getValue(lean_object* v_00_u03b1_3737_, lean_object* v_inst_3738_, lean_object* v_attr_3739_, lean_object* v_env_3740_, lean_object* v_decl_3741_){
_start:
{
lean_object* v___x_3742_; 
v___x_3742_ = l_Lean_EnumAttributes_getValue___redArg(v_inst_3738_, v_attr_3739_, v_env_3740_, v_decl_3741_);
return v___x_3742_;
}
}
LEAN_EXPORT lean_object* l_Lean_EnumAttributes_setValue___redArg(lean_object* v_attrs_3751_, lean_object* v_env_3752_, lean_object* v_decl_3753_, lean_object* v_val_3754_){
_start:
{
lean_object* v_ext_3755_; lean_object* v___x_3757_; uint8_t v_isShared_3758_; uint8_t v_isSharedCheck_3818_; 
v_ext_3755_ = lean_ctor_get(v_attrs_3751_, 1);
v_isSharedCheck_3818_ = !lean_is_exclusive(v_attrs_3751_);
if (v_isSharedCheck_3818_ == 0)
{
lean_object* v_unused_3819_; 
v_unused_3819_ = lean_ctor_get(v_attrs_3751_, 0);
lean_dec(v_unused_3819_);
v___x_3757_ = v_attrs_3751_;
v_isShared_3758_ = v_isSharedCheck_3818_;
goto v_resetjp_3756_;
}
else
{
lean_inc(v_ext_3755_);
lean_dec(v_attrs_3751_);
v___x_3757_ = lean_box(0);
v_isShared_3758_ = v_isSharedCheck_3818_;
goto v_resetjp_3756_;
}
v_resetjp_3756_:
{
lean_object* v_toEnvExtension_3759_; lean_object* v_name_3760_; lean_object* v___x_3761_; uint8_t v___x_3762_; lean_object* v___x_3763_; lean_object* v___x_3764_; lean_object* v___x_3765_; lean_object* v___x_3766_; lean_object* v___x_3767_; lean_object* v___x_3768_; lean_object* v___x_3769_; lean_object* v_pfx_3770_; lean_object* v___x_3771_; 
v_toEnvExtension_3759_ = lean_ctor_get(v_ext_3755_, 0);
v_name_3760_ = lean_ctor_get(v_ext_3755_, 1);
v___x_3761_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__0));
v___x_3762_ = 1;
lean_inc(v_name_3760_);
v___x_3763_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_3760_, v___x_3762_);
v___x_3764_ = lean_string_append(v___x_3761_, v___x_3763_);
lean_dec_ref(v___x_3763_);
v___x_3765_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__1));
v___x_3766_ = lean_string_append(v___x_3764_, v___x_3765_);
lean_inc(v_decl_3753_);
v___x_3767_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_decl_3753_, v___x_3762_);
v___x_3768_ = lean_string_append(v___x_3766_, v___x_3767_);
lean_dec_ref(v___x_3767_);
v___x_3769_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__4));
v_pfx_3770_ = lean_string_append(v___x_3768_, v___x_3769_);
v___x_3771_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3752_, v_decl_3753_);
if (lean_obj_tag(v___x_3771_) == 0)
{
lean_object* v_asyncMode_3772_; uint8_t v___x_3773_; 
v_asyncMode_3772_ = lean_ctor_get(v_toEnvExtension_3759_, 2);
lean_inc(v_asyncMode_3772_);
lean_inc(v_decl_3753_);
lean_inc_ref(v_env_3752_);
v___x_3773_ = l_Lean_EnvExtension_asyncMayModify___redArg(v_env_3752_, v_decl_3753_, v_asyncMode_3772_);
if (v___x_3773_ == 0)
{
lean_object* v___x_3774_; lean_object* v___x_3775_; lean_object* v___y_3777_; lean_object* v___x_3781_; 
lean_dec(v_asyncMode_3772_);
lean_del_object(v___x_3757_);
lean_dec_ref(v_ext_3755_);
lean_dec(v_val_3754_);
lean_dec(v_decl_3753_);
v___x_3774_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__2));
v___x_3775_ = lean_string_append(v_pfx_3770_, v___x_3774_);
v___x_3781_ = l_Lean_Environment_asyncPrefix_x3f(v_env_3752_);
if (lean_obj_tag(v___x_3781_) == 0)
{
lean_object* v___x_3782_; 
v___x_3782_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__3));
v___y_3777_ = v___x_3782_;
goto v___jp_3776_;
}
else
{
lean_object* v_val_3783_; lean_object* v___x_3784_; lean_object* v___x_3785_; lean_object* v___x_3786_; lean_object* v___x_3787_; lean_object* v___x_3788_; lean_object* v___x_3789_; 
v_val_3783_ = lean_ctor_get(v___x_3781_, 0);
lean_inc(v_val_3783_);
lean_dec_ref_known(v___x_3781_, 1);
v___x_3784_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__4));
v___x_3785_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_val_3783_, v___x_3762_);
v___x_3786_ = l_addParenHeuristic(v___x_3785_);
v___x_3787_ = lean_string_append(v___x_3784_, v___x_3786_);
lean_dec_ref(v___x_3786_);
v___x_3788_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__5));
v___x_3789_ = lean_string_append(v___x_3787_, v___x_3788_);
v___y_3777_ = v___x_3789_;
goto v___jp_3776_;
}
v___jp_3776_:
{
lean_object* v___x_3778_; lean_object* v___x_3779_; lean_object* v___x_3780_; 
v___x_3778_ = lean_string_append(v___x_3775_, v___y_3777_);
lean_dec_ref(v___y_3777_);
v___x_3779_ = lean_string_append(v___x_3778_, v___x_3769_);
v___x_3780_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3780_, 0, v___x_3779_);
return v___x_3780_;
}
}
else
{
lean_object* v___x_3790_; lean_object* v___x_3791_; lean_object* v___x_3792_; 
v___x_3790_ = lean_box(1);
lean_inc(v_decl_3753_);
lean_inc_ref(v_env_3752_);
v___x_3791_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3790_, v_ext_3755_, v_env_3752_, v_asyncMode_3772_, v_decl_3753_);
v___x_3792_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_3791_, v_decl_3753_);
lean_dec(v___x_3791_);
if (lean_obj_tag(v___x_3792_) == 0)
{
lean_object* v___x_3794_; 
lean_dec_ref(v_pfx_3770_);
lean_inc(v_decl_3753_);
if (v_isShared_3758_ == 0)
{
lean_ctor_set(v___x_3757_, 1, v_val_3754_);
lean_ctor_set(v___x_3757_, 0, v_decl_3753_);
v___x_3794_ = v___x_3757_;
goto v_reusejp_3793_;
}
else
{
lean_object* v_reuseFailAlloc_3797_; 
v_reuseFailAlloc_3797_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3797_, 0, v_decl_3753_);
lean_ctor_set(v_reuseFailAlloc_3797_, 1, v_val_3754_);
v___x_3794_ = v_reuseFailAlloc_3797_;
goto v_reusejp_3793_;
}
v_reusejp_3793_:
{
lean_object* v___x_3795_; lean_object* v___x_3796_; 
v___x_3795_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_ext_3755_, v_env_3752_, v___x_3794_, v_asyncMode_3772_, v_decl_3753_);
lean_dec(v_asyncMode_3772_);
v___x_3796_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3796_, 0, v___x_3795_);
return v___x_3796_;
}
}
else
{
lean_object* v___x_3799_; uint8_t v_isShared_3800_; uint8_t v_isSharedCheck_3806_; 
lean_dec(v_asyncMode_3772_);
lean_del_object(v___x_3757_);
lean_dec_ref(v_ext_3755_);
lean_dec(v_val_3754_);
lean_dec(v_decl_3753_);
lean_dec_ref(v_env_3752_);
v_isSharedCheck_3806_ = !lean_is_exclusive(v___x_3792_);
if (v_isSharedCheck_3806_ == 0)
{
lean_object* v_unused_3807_; 
v_unused_3807_ = lean_ctor_get(v___x_3792_, 0);
lean_dec(v_unused_3807_);
v___x_3799_ = v___x_3792_;
v_isShared_3800_ = v_isSharedCheck_3806_;
goto v_resetjp_3798_;
}
else
{
lean_dec(v___x_3792_);
v___x_3799_ = lean_box(0);
v_isShared_3800_ = v_isSharedCheck_3806_;
goto v_resetjp_3798_;
}
v_resetjp_3798_:
{
lean_object* v___x_3801_; lean_object* v___x_3802_; lean_object* v___x_3804_; 
v___x_3801_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__6));
v___x_3802_ = lean_string_append(v_pfx_3770_, v___x_3801_);
if (v_isShared_3800_ == 0)
{
lean_ctor_set_tag(v___x_3799_, 0);
lean_ctor_set(v___x_3799_, 0, v___x_3802_);
v___x_3804_ = v___x_3799_;
goto v_reusejp_3803_;
}
else
{
lean_object* v_reuseFailAlloc_3805_; 
v_reuseFailAlloc_3805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3805_, 0, v___x_3802_);
v___x_3804_ = v_reuseFailAlloc_3805_;
goto v_reusejp_3803_;
}
v_reusejp_3803_:
{
return v___x_3804_;
}
}
}
}
}
else
{
lean_object* v___x_3809_; uint8_t v_isShared_3810_; uint8_t v_isSharedCheck_3816_; 
lean_del_object(v___x_3757_);
lean_dec_ref(v_ext_3755_);
lean_dec(v_val_3754_);
lean_dec(v_decl_3753_);
lean_dec_ref(v_env_3752_);
v_isSharedCheck_3816_ = !lean_is_exclusive(v___x_3771_);
if (v_isSharedCheck_3816_ == 0)
{
lean_object* v_unused_3817_; 
v_unused_3817_ = lean_ctor_get(v___x_3771_, 0);
lean_dec(v_unused_3817_);
v___x_3809_ = v___x_3771_;
v_isShared_3810_ = v_isSharedCheck_3816_;
goto v_resetjp_3808_;
}
else
{
lean_dec(v___x_3771_);
v___x_3809_ = lean_box(0);
v_isShared_3810_ = v_isSharedCheck_3816_;
goto v_resetjp_3808_;
}
v_resetjp_3808_:
{
lean_object* v___x_3811_; lean_object* v___x_3812_; lean_object* v___x_3814_; 
v___x_3811_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__7));
v___x_3812_ = lean_string_append(v_pfx_3770_, v___x_3811_);
if (v_isShared_3810_ == 0)
{
lean_ctor_set_tag(v___x_3809_, 0);
lean_ctor_set(v___x_3809_, 0, v___x_3812_);
v___x_3814_ = v___x_3809_;
goto v_reusejp_3813_;
}
else
{
lean_object* v_reuseFailAlloc_3815_; 
v_reuseFailAlloc_3815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3815_, 0, v___x_3812_);
v___x_3814_ = v_reuseFailAlloc_3815_;
goto v_reusejp_3813_;
}
v_reusejp_3813_:
{
return v___x_3814_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_EnumAttributes_setValue(lean_object* v_00_u03b1_3820_, lean_object* v_attrs_3821_, lean_object* v_env_3822_, lean_object* v_decl_3823_, lean_object* v_val_3824_){
_start:
{
lean_object* v___x_3825_; 
v___x_3825_ = l_Lean_EnumAttributes_setValue___redArg(v_attrs_3821_, v_env_3822_, v_decl_3823_, v_val_3824_);
return v___x_3825_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_2990505691____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3827_; lean_object* v___x_3828_; lean_object* v___x_3829_; 
v___x_3827_ = lean_obj_once(&l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_, &l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2__once, _init_l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_);
v___x_3828_ = lean_st_mk_ref(v___x_3827_);
v___x_3829_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3829_, 0, v___x_3828_);
return v___x_3829_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_2990505691____hygCtx___hyg_2____boxed(lean_object* v_a_3830_){
_start:
{
lean_object* v_res_3831_; 
v_res_3831_ = l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_2990505691____hygCtx___hyg_2_();
return v_res_3831_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerAttributeImplBuilder(lean_object* v_builderId_3834_, lean_object* v_builder_3835_){
_start:
{
lean_object* v___x_3837_; lean_object* v___x_3838_; uint8_t v___x_3839_; 
v___x_3837_ = l_Lean_attributeImplBuilderTableRef;
v___x_3838_ = lean_st_ref_get(v___x_3837_);
v___x_3839_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(v___x_3838_, v_builderId_3834_);
lean_dec(v___x_3838_);
if (v___x_3839_ == 0)
{
lean_object* v___x_3840_; lean_object* v___x_3841_; lean_object* v___x_3842_; lean_object* v___x_3843_; 
v___x_3840_ = lean_st_ref_take(v___x_3837_);
v___x_3841_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1___redArg(v___x_3840_, v_builderId_3834_, v_builder_3835_);
v___x_3842_ = lean_st_ref_put(v___x_3837_, v___x_3841_);
v___x_3843_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3843_, 0, v___x_3842_);
return v___x_3843_;
}
else
{
lean_object* v___x_3844_; lean_object* v___x_3845_; lean_object* v___x_3846_; lean_object* v___x_3847_; lean_object* v___x_3848_; lean_object* v___x_3849_; lean_object* v___x_3850_; 
lean_dec_ref(v_builder_3835_);
v___x_3844_ = ((lean_object*)(l_Lean_registerAttributeImplBuilder___closed__0));
v___x_3845_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_builderId_3834_, v___x_3839_);
v___x_3846_ = lean_string_append(v___x_3844_, v___x_3845_);
lean_dec_ref(v___x_3845_);
v___x_3847_ = ((lean_object*)(l_Lean_registerAttributeImplBuilder___closed__1));
v___x_3848_ = lean_string_append(v___x_3846_, v___x_3847_);
v___x_3849_ = lean_mk_io_user_error(v___x_3848_);
v___x_3850_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3850_, 0, v___x_3849_);
return v___x_3850_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerAttributeImplBuilder___boxed(lean_object* v_builderId_3851_, lean_object* v_builder_3852_, lean_object* v_a_3853_){
_start:
{
lean_object* v_res_3854_; 
v_res_3854_ = l_Lean_registerAttributeImplBuilder(v_builderId_3851_, v_builder_3852_);
return v_res_3854_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___redArg(lean_object* v_e_3855_){
_start:
{
if (lean_obj_tag(v_e_3855_) == 0)
{
lean_object* v_a_3857_; lean_object* v___x_3859_; uint8_t v_isShared_3860_; uint8_t v_isSharedCheck_3865_; 
v_a_3857_ = lean_ctor_get(v_e_3855_, 0);
v_isSharedCheck_3865_ = !lean_is_exclusive(v_e_3855_);
if (v_isSharedCheck_3865_ == 0)
{
v___x_3859_ = v_e_3855_;
v_isShared_3860_ = v_isSharedCheck_3865_;
goto v_resetjp_3858_;
}
else
{
lean_inc(v_a_3857_);
lean_dec(v_e_3855_);
v___x_3859_ = lean_box(0);
v_isShared_3860_ = v_isSharedCheck_3865_;
goto v_resetjp_3858_;
}
v_resetjp_3858_:
{
lean_object* v___x_3861_; lean_object* v___x_3863_; 
v___x_3861_ = lean_mk_io_user_error(v_a_3857_);
if (v_isShared_3860_ == 0)
{
lean_ctor_set_tag(v___x_3859_, 1);
lean_ctor_set(v___x_3859_, 0, v___x_3861_);
v___x_3863_ = v___x_3859_;
goto v_reusejp_3862_;
}
else
{
lean_object* v_reuseFailAlloc_3864_; 
v_reuseFailAlloc_3864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3864_, 0, v___x_3861_);
v___x_3863_ = v_reuseFailAlloc_3864_;
goto v_reusejp_3862_;
}
v_reusejp_3862_:
{
return v___x_3863_;
}
}
}
else
{
lean_object* v_a_3866_; lean_object* v___x_3868_; uint8_t v_isShared_3869_; uint8_t v_isSharedCheck_3873_; 
v_a_3866_ = lean_ctor_get(v_e_3855_, 0);
v_isSharedCheck_3873_ = !lean_is_exclusive(v_e_3855_);
if (v_isSharedCheck_3873_ == 0)
{
v___x_3868_ = v_e_3855_;
v_isShared_3869_ = v_isSharedCheck_3873_;
goto v_resetjp_3867_;
}
else
{
lean_inc(v_a_3866_);
lean_dec(v_e_3855_);
v___x_3868_ = lean_box(0);
v_isShared_3869_ = v_isSharedCheck_3873_;
goto v_resetjp_3867_;
}
v_resetjp_3867_:
{
lean_object* v___x_3871_; 
if (v_isShared_3869_ == 0)
{
lean_ctor_set_tag(v___x_3868_, 0);
v___x_3871_ = v___x_3868_;
goto v_reusejp_3870_;
}
else
{
lean_object* v_reuseFailAlloc_3872_; 
v_reuseFailAlloc_3872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3872_, 0, v_a_3866_);
v___x_3871_ = v_reuseFailAlloc_3872_;
goto v_reusejp_3870_;
}
v_reusejp_3870_:
{
return v___x_3871_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___redArg___boxed(lean_object* v_e_3874_, lean_object* v_a_3875_){
_start:
{
lean_object* v_res_3876_; 
v_res_3876_ = l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___redArg(v_e_3874_);
return v_res_3876_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1(lean_object* v_00_u03b1_3877_, lean_object* v_e_3878_){
_start:
{
lean_object* v___x_3880_; 
v___x_3880_ = l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___redArg(v_e_3878_);
return v___x_3880_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___boxed(lean_object* v_00_u03b1_3881_, lean_object* v_e_3882_, lean_object* v_a_3883_){
_start:
{
lean_object* v_res_3884_; 
v_res_3884_ = l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1(v_00_u03b1_3881_, v_e_3882_);
return v_res_3884_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___redArg(lean_object* v_a_3885_, lean_object* v_x_3886_){
_start:
{
if (lean_obj_tag(v_x_3886_) == 0)
{
lean_object* v___x_3887_; 
v___x_3887_ = lean_box(0);
return v___x_3887_;
}
else
{
lean_object* v_key_3888_; lean_object* v_value_3889_; lean_object* v_tail_3890_; uint8_t v___x_3891_; 
v_key_3888_ = lean_ctor_get(v_x_3886_, 0);
v_value_3889_ = lean_ctor_get(v_x_3886_, 1);
v_tail_3890_ = lean_ctor_get(v_x_3886_, 2);
v___x_3891_ = lean_name_eq(v_key_3888_, v_a_3885_);
if (v___x_3891_ == 0)
{
v_x_3886_ = v_tail_3890_;
goto _start;
}
else
{
lean_object* v___x_3893_; 
lean_inc(v_value_3889_);
v___x_3893_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3893_, 0, v_value_3889_);
return v___x_3893_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___redArg___boxed(lean_object* v_a_3894_, lean_object* v_x_3895_){
_start:
{
lean_object* v_res_3896_; 
v_res_3896_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___redArg(v_a_3894_, v_x_3895_);
lean_dec(v_x_3895_);
lean_dec(v_a_3894_);
return v_res_3896_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(lean_object* v_m_3897_, lean_object* v_a_3898_){
_start:
{
lean_object* v_buckets_3899_; lean_object* v___x_3900_; uint64_t v___y_3902_; 
v_buckets_3899_ = lean_ctor_get(v_m_3897_, 1);
v___x_3900_ = lean_array_get_size(v_buckets_3899_);
if (lean_obj_tag(v_a_3898_) == 0)
{
uint64_t v___x_3916_; 
v___x_3916_ = 1723ULL;
v___y_3902_ = v___x_3916_;
goto v___jp_3901_;
}
else
{
uint64_t v_hash_3917_; 
v_hash_3917_ = lean_ctor_get_uint64(v_a_3898_, sizeof(void*)*2);
v___y_3902_ = v_hash_3917_;
goto v___jp_3901_;
}
v___jp_3901_:
{
uint64_t v___x_3903_; uint64_t v___x_3904_; uint64_t v_fold_3905_; uint64_t v___x_3906_; uint64_t v___x_3907_; uint64_t v___x_3908_; size_t v___x_3909_; size_t v___x_3910_; size_t v___x_3911_; size_t v___x_3912_; size_t v___x_3913_; lean_object* v___x_3914_; lean_object* v___x_3915_; 
v___x_3903_ = 32ULL;
v___x_3904_ = lean_uint64_shift_right(v___y_3902_, v___x_3903_);
v_fold_3905_ = lean_uint64_xor(v___y_3902_, v___x_3904_);
v___x_3906_ = 16ULL;
v___x_3907_ = lean_uint64_shift_right(v_fold_3905_, v___x_3906_);
v___x_3908_ = lean_uint64_xor(v_fold_3905_, v___x_3907_);
v___x_3909_ = lean_uint64_to_usize(v___x_3908_);
v___x_3910_ = lean_usize_of_nat(v___x_3900_);
v___x_3911_ = ((size_t)1ULL);
v___x_3912_ = lean_usize_sub(v___x_3910_, v___x_3911_);
v___x_3913_ = lean_usize_land(v___x_3909_, v___x_3912_);
v___x_3914_ = lean_array_uget_borrowed(v_buckets_3899_, v___x_3913_);
v___x_3915_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___redArg(v_a_3898_, v___x_3914_);
return v___x_3915_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg___boxed(lean_object* v_m_3918_, lean_object* v_a_3919_){
_start:
{
lean_object* v_res_3920_; 
v_res_3920_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(v_m_3918_, v_a_3919_);
lean_dec(v_a_3919_);
lean_dec_ref(v_m_3918_);
return v_res_3920_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAttributeImplOfEntry(lean_object* v_e_3922_){
_start:
{
lean_object* v___x_3924_; lean_object* v___x_3925_; lean_object* v_builderId_3926_; lean_object* v_ref_3927_; lean_object* v_args_3928_; lean_object* v___x_3929_; 
v___x_3924_ = l_Lean_attributeImplBuilderTableRef;
v___x_3925_ = lean_st_ref_get(v___x_3924_);
v_builderId_3926_ = lean_ctor_get(v_e_3922_, 0);
lean_inc(v_builderId_3926_);
v_ref_3927_ = lean_ctor_get(v_e_3922_, 1);
lean_inc(v_ref_3927_);
v_args_3928_ = lean_ctor_get(v_e_3922_, 2);
lean_inc(v_args_3928_);
lean_dec_ref(v_e_3922_);
v___x_3929_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(v___x_3925_, v_builderId_3926_);
lean_dec(v___x_3925_);
if (lean_obj_tag(v___x_3929_) == 0)
{
lean_object* v___x_3930_; uint8_t v___x_3931_; lean_object* v___x_3932_; lean_object* v___x_3933_; lean_object* v___x_3934_; lean_object* v___x_3935_; lean_object* v___x_3936_; lean_object* v___x_3937_; 
lean_dec(v_args_3928_);
lean_dec(v_ref_3927_);
v___x_3930_ = ((lean_object*)(l_Lean_mkAttributeImplOfEntry___closed__0));
v___x_3931_ = 1;
v___x_3932_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_builderId_3926_, v___x_3931_);
v___x_3933_ = lean_string_append(v___x_3930_, v___x_3932_);
lean_dec_ref(v___x_3932_);
v___x_3934_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__4));
v___x_3935_ = lean_string_append(v___x_3933_, v___x_3934_);
v___x_3936_ = lean_mk_io_user_error(v___x_3935_);
v___x_3937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3937_, 0, v___x_3936_);
return v___x_3937_;
}
else
{
lean_object* v_val_3938_; lean_object* v___x_3939_; lean_object* v___x_3940_; 
lean_dec(v_builderId_3926_);
v_val_3938_ = lean_ctor_get(v___x_3929_, 0);
lean_inc(v_val_3938_);
lean_dec_ref_known(v___x_3929_, 1);
v___x_3939_ = lean_apply_2(v_val_3938_, v_ref_3927_, v_args_3928_);
v___x_3940_ = l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___redArg(v___x_3939_);
return v___x_3940_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkAttributeImplOfEntry___boxed(lean_object* v_e_3941_, lean_object* v_a_3942_){
_start:
{
lean_object* v_res_3943_; 
v_res_3943_ = l_Lean_mkAttributeImplOfEntry(v_e_3941_);
return v_res_3943_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0(lean_object* v_00_u03b2_3944_, lean_object* v_m_3945_, lean_object* v_a_3946_){
_start:
{
lean_object* v___x_3947_; 
v___x_3947_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(v_m_3945_, v_a_3946_);
return v___x_3947_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___boxed(lean_object* v_00_u03b2_3948_, lean_object* v_m_3949_, lean_object* v_a_3950_){
_start:
{
lean_object* v_res_3951_; 
v_res_3951_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0(v_00_u03b2_3948_, v_m_3949_, v_a_3950_);
lean_dec(v_a_3950_);
lean_dec_ref(v_m_3949_);
return v_res_3951_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0(lean_object* v_00_u03b2_3952_, lean_object* v_a_3953_, lean_object* v_x_3954_){
_start:
{
lean_object* v___x_3955_; 
v___x_3955_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___redArg(v_a_3953_, v_x_3954_);
return v___x_3955_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3956_, lean_object* v_a_3957_, lean_object* v_x_3958_){
_start:
{
lean_object* v_res_3959_; 
v_res_3959_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0(v_00_u03b2_3956_, v_a_3957_, v_x_3958_);
lean_dec(v_x_3958_);
lean_dec(v_a_3957_);
return v_res_3959_;
}
}
static lean_object* _init_l_Lean_instInhabitedAttributeExtensionState_default___closed__0(void){
_start:
{
lean_object* v___x_3960_; lean_object* v___x_3961_; lean_object* v___x_3962_; 
v___x_3960_ = lean_obj_once(&l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_, &l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2__once, _init_l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_);
v___x_3961_ = lean_box(0);
v___x_3962_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3962_, 0, v___x_3961_);
lean_ctor_set(v___x_3962_, 1, v___x_3960_);
return v___x_3962_;
}
}
static lean_object* _init_l_Lean_instInhabitedAttributeExtensionState_default(void){
_start:
{
lean_object* v___x_3963_; 
v___x_3963_ = lean_obj_once(&l_Lean_instInhabitedAttributeExtensionState_default___closed__0, &l_Lean_instInhabitedAttributeExtensionState_default___closed__0_once, _init_l_Lean_instInhabitedAttributeExtensionState_default___closed__0);
return v___x_3963_;
}
}
static lean_object* _init_l_Lean_instInhabitedAttributeExtensionState(void){
_start:
{
lean_object* v___x_3964_; 
v___x_3964_ = l_Lean_instInhabitedAttributeExtensionState_default;
return v___x_3964_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_AttributeExtension_mkInitial(){
_start:
{
lean_object* v___x_3966_; lean_object* v___x_3967_; lean_object* v___x_3968_; lean_object* v___x_3969_; lean_object* v___x_3970_; 
v___x_3966_ = l_Lean_attributeMapRef;
v___x_3967_ = lean_st_ref_get(v___x_3966_);
v___x_3968_ = lean_box(0);
v___x_3969_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3969_, 0, v___x_3968_);
lean_ctor_set(v___x_3969_, 1, v___x_3967_);
v___x_3970_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3970_, 0, v___x_3969_);
return v___x_3970_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_AttributeExtension_mkInitial___boxed(lean_object* v_a_3971_){
_start:
{
lean_object* v_res_3972_; 
v_res_3972_ = l___private_Lean_Attributes_0__Lean_AttributeExtension_mkInitial();
return v_res_3972_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAttributeImplOfConstantUnsafe(lean_object* v_env_3978_, lean_object* v_opts_3979_, lean_object* v_declName_3980_){
_start:
{
uint8_t v___x_3983_; lean_object* v___x_3984_; 
v___x_3983_ = 0;
lean_inc(v_declName_3980_);
lean_inc_ref(v_env_3978_);
v___x_3984_ = l_Lean_Environment_find_x3f(v_env_3978_, v_declName_3980_, v___x_3983_);
if (lean_obj_tag(v___x_3984_) == 0)
{
lean_object* v___x_3985_; uint8_t v___x_3986_; lean_object* v___x_3987_; lean_object* v___x_3988_; lean_object* v___x_3989_; lean_object* v___x_3990_; lean_object* v___x_3991_; 
lean_dec_ref(v_env_3978_);
v___x_3985_ = ((lean_object*)(l_Lean_mkAttributeImplOfConstantUnsafe___closed__2));
v___x_3986_ = 1;
v___x_3987_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_declName_3980_, v___x_3986_);
v___x_3988_ = lean_string_append(v___x_3985_, v___x_3987_);
lean_dec_ref(v___x_3987_);
v___x_3989_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__4));
v___x_3990_ = lean_string_append(v___x_3988_, v___x_3989_);
v___x_3991_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3991_, 0, v___x_3990_);
return v___x_3991_;
}
else
{
lean_object* v_val_3992_; lean_object* v___x_3993_; 
v_val_3992_ = lean_ctor_get(v___x_3984_, 0);
lean_inc(v_val_3992_);
lean_dec_ref_known(v___x_3984_, 1);
v___x_3993_ = l_Lean_ConstantInfo_type(v_val_3992_);
lean_dec(v_val_3992_);
if (lean_obj_tag(v___x_3993_) == 4)
{
lean_object* v_declName_3994_; 
v_declName_3994_ = lean_ctor_get(v___x_3993_, 0);
lean_inc(v_declName_3994_);
lean_dec_ref_known(v___x_3993_, 2);
if (lean_obj_tag(v_declName_3994_) == 1)
{
lean_object* v_pre_3995_; 
v_pre_3995_ = lean_ctor_get(v_declName_3994_, 0);
lean_inc(v_pre_3995_);
if (lean_obj_tag(v_pre_3995_) == 1)
{
lean_object* v_pre_3996_; 
v_pre_3996_ = lean_ctor_get(v_pre_3995_, 0);
if (lean_obj_tag(v_pre_3996_) == 0)
{
lean_object* v_str_3997_; lean_object* v_str_3998_; lean_object* v___x_3999_; uint8_t v___x_4000_; 
v_str_3997_ = lean_ctor_get(v_declName_3994_, 1);
lean_inc_ref(v_str_3997_);
lean_dec_ref_known(v_declName_3994_, 2);
v_str_3998_ = lean_ctor_get(v_pre_3995_, 1);
lean_inc_ref(v_str_3998_);
lean_dec_ref_known(v_pre_3995_, 2);
v___x_3999_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__0));
v___x_4000_ = lean_string_dec_eq(v_str_3998_, v___x_3999_);
lean_dec_ref(v_str_3998_);
if (v___x_4000_ == 0)
{
lean_dec_ref(v_str_3997_);
lean_dec(v_declName_3980_);
lean_dec_ref(v_env_3978_);
goto v___jp_3981_;
}
else
{
lean_object* v___x_4001_; uint8_t v___x_4002_; 
v___x_4001_ = ((lean_object*)(l_Lean_mkAttributeImplOfConstantUnsafe___closed__3));
v___x_4002_ = lean_string_dec_eq(v_str_3997_, v___x_4001_);
lean_dec_ref(v_str_3997_);
if (v___x_4002_ == 0)
{
lean_dec(v_declName_3980_);
lean_dec_ref(v_env_3978_);
goto v___jp_3981_;
}
else
{
lean_object* v___x_4003_; 
v___x_4003_ = l_Lean_Environment_evalConst___redArg(v_env_3978_, v_opts_3979_, v_declName_3980_, v___x_4002_);
lean_dec(v_declName_3980_);
lean_dec_ref(v_env_3978_);
return v___x_4003_;
}
}
}
else
{
lean_dec_ref_known(v_pre_3995_, 2);
lean_dec_ref_known(v_declName_3994_, 2);
lean_dec(v_declName_3980_);
lean_dec_ref(v_env_3978_);
goto v___jp_3981_;
}
}
else
{
lean_dec(v_pre_3995_);
lean_dec_ref_known(v_declName_3994_, 2);
lean_dec(v_declName_3980_);
lean_dec_ref(v_env_3978_);
goto v___jp_3981_;
}
}
else
{
lean_dec(v_declName_3994_);
lean_dec(v_declName_3980_);
lean_dec_ref(v_env_3978_);
goto v___jp_3981_;
}
}
else
{
lean_dec_ref(v___x_3993_);
lean_dec(v_declName_3980_);
lean_dec_ref(v_env_3978_);
goto v___jp_3981_;
}
}
v___jp_3981_:
{
lean_object* v___x_3982_; 
v___x_3982_ = ((lean_object*)(l_Lean_mkAttributeImplOfConstantUnsafe___closed__1));
return v___x_3982_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkAttributeImplOfConstantUnsafe___boxed(lean_object* v_env_4004_, lean_object* v_opts_4005_, lean_object* v_declName_4006_){
_start:
{
lean_object* v_res_4007_; 
v_res_4007_ = l_Lean_mkAttributeImplOfConstantUnsafe(v_env_4004_, v_opts_4005_, v_declName_4006_);
lean_dec_ref(v_opts_4005_);
return v_res_4007_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg(lean_object* v_as_4008_, size_t v_i_4009_, size_t v_stop_4010_, lean_object* v_b_4011_){
_start:
{
uint8_t v___x_4013_; 
v___x_4013_ = lean_usize_dec_eq(v_i_4009_, v_stop_4010_);
if (v___x_4013_ == 0)
{
lean_object* v___x_4014_; lean_object* v___x_4015_; 
v___x_4014_ = lean_array_uget_borrowed(v_as_4008_, v_i_4009_);
lean_inc(v___x_4014_);
v___x_4015_ = l_Lean_mkAttributeImplOfEntry(v___x_4014_);
if (lean_obj_tag(v___x_4015_) == 0)
{
lean_object* v_a_4016_; lean_object* v_toAttributeImplCore_4017_; lean_object* v_name_4018_; lean_object* v___x_4019_; size_t v___x_4020_; size_t v___x_4021_; 
v_a_4016_ = lean_ctor_get(v___x_4015_, 0);
lean_inc(v_a_4016_);
lean_dec_ref_known(v___x_4015_, 1);
v_toAttributeImplCore_4017_ = lean_ctor_get(v_a_4016_, 0);
v_name_4018_ = lean_ctor_get(v_toAttributeImplCore_4017_, 1);
lean_inc(v_name_4018_);
v___x_4019_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1___redArg(v_b_4011_, v_name_4018_, v_a_4016_);
v___x_4020_ = ((size_t)1ULL);
v___x_4021_ = lean_usize_add(v_i_4009_, v___x_4020_);
v_i_4009_ = v___x_4021_;
v_b_4011_ = v___x_4019_;
goto _start;
}
else
{
lean_object* v_a_4023_; lean_object* v___x_4025_; uint8_t v_isShared_4026_; uint8_t v_isSharedCheck_4030_; 
lean_dec_ref(v_b_4011_);
v_a_4023_ = lean_ctor_get(v___x_4015_, 0);
v_isSharedCheck_4030_ = !lean_is_exclusive(v___x_4015_);
if (v_isSharedCheck_4030_ == 0)
{
v___x_4025_ = v___x_4015_;
v_isShared_4026_ = v_isSharedCheck_4030_;
goto v_resetjp_4024_;
}
else
{
lean_inc(v_a_4023_);
lean_dec(v___x_4015_);
v___x_4025_ = lean_box(0);
v_isShared_4026_ = v_isSharedCheck_4030_;
goto v_resetjp_4024_;
}
v_resetjp_4024_:
{
lean_object* v___x_4028_; 
if (v_isShared_4026_ == 0)
{
v___x_4028_ = v___x_4025_;
goto v_reusejp_4027_;
}
else
{
lean_object* v_reuseFailAlloc_4029_; 
v_reuseFailAlloc_4029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4029_, 0, v_a_4023_);
v___x_4028_ = v_reuseFailAlloc_4029_;
goto v_reusejp_4027_;
}
v_reusejp_4027_:
{
return v___x_4028_;
}
}
}
}
else
{
lean_object* v___x_4031_; 
v___x_4031_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4031_, 0, v_b_4011_);
return v___x_4031_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg___boxed(lean_object* v_as_4032_, lean_object* v_i_4033_, lean_object* v_stop_4034_, lean_object* v_b_4035_, lean_object* v___y_4036_){
_start:
{
size_t v_i_boxed_4037_; size_t v_stop_boxed_4038_; lean_object* v_res_4039_; 
v_i_boxed_4037_ = lean_unbox_usize(v_i_4033_);
lean_dec(v_i_4033_);
v_stop_boxed_4038_ = lean_unbox_usize(v_stop_4034_);
lean_dec(v_stop_4034_);
v_res_4039_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg(v_as_4032_, v_i_boxed_4037_, v_stop_boxed_4038_, v_b_4035_);
lean_dec_ref(v_as_4032_);
return v_res_4039_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__1(lean_object* v_as_4040_, size_t v_i_4041_, size_t v_stop_4042_, lean_object* v_b_4043_, lean_object* v___y_4044_){
_start:
{
lean_object* v_a_4047_; lean_object* v___y_4052_; uint8_t v___x_4054_; 
v___x_4054_ = lean_usize_dec_eq(v_i_4041_, v_stop_4042_);
if (v___x_4054_ == 0)
{
lean_object* v___x_4055_; lean_object* v___x_4056_; lean_object* v___x_4057_; uint8_t v___x_4058_; 
v___x_4055_ = lean_array_uget_borrowed(v_as_4040_, v_i_4041_);
v___x_4056_ = lean_unsigned_to_nat(0u);
v___x_4057_ = lean_array_get_size(v___x_4055_);
v___x_4058_ = lean_nat_dec_lt(v___x_4056_, v___x_4057_);
if (v___x_4058_ == 0)
{
v_a_4047_ = v_b_4043_;
goto v___jp_4046_;
}
else
{
uint8_t v___x_4059_; 
v___x_4059_ = lean_nat_dec_le(v___x_4057_, v___x_4057_);
if (v___x_4059_ == 0)
{
if (v___x_4058_ == 0)
{
v_a_4047_ = v_b_4043_;
goto v___jp_4046_;
}
else
{
size_t v___x_4060_; size_t v___x_4061_; lean_object* v___x_4062_; 
v___x_4060_ = ((size_t)0ULL);
v___x_4061_ = lean_usize_of_nat(v___x_4057_);
v___x_4062_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg(v___x_4055_, v___x_4060_, v___x_4061_, v_b_4043_);
v___y_4052_ = v___x_4062_;
goto v___jp_4051_;
}
}
else
{
size_t v___x_4063_; size_t v___x_4064_; lean_object* v___x_4065_; 
v___x_4063_ = ((size_t)0ULL);
v___x_4064_ = lean_usize_of_nat(v___x_4057_);
v___x_4065_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg(v___x_4055_, v___x_4063_, v___x_4064_, v_b_4043_);
v___y_4052_ = v___x_4065_;
goto v___jp_4051_;
}
}
}
else
{
lean_object* v___x_4066_; 
v___x_4066_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4066_, 0, v_b_4043_);
return v___x_4066_;
}
v___jp_4046_:
{
size_t v___x_4048_; size_t v___x_4049_; 
v___x_4048_ = ((size_t)1ULL);
v___x_4049_ = lean_usize_add(v_i_4041_, v___x_4048_);
v_i_4041_ = v___x_4049_;
v_b_4043_ = v_a_4047_;
goto _start;
}
v___jp_4051_:
{
if (lean_obj_tag(v___y_4052_) == 0)
{
lean_object* v_a_4053_; 
v_a_4053_ = lean_ctor_get(v___y_4052_, 0);
lean_inc(v_a_4053_);
lean_dec_ref_known(v___y_4052_, 1);
v_a_4047_ = v_a_4053_;
goto v___jp_4046_;
}
else
{
return v___y_4052_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__1___boxed(lean_object* v_as_4067_, lean_object* v_i_4068_, lean_object* v_stop_4069_, lean_object* v_b_4070_, lean_object* v___y_4071_, lean_object* v___y_4072_){
_start:
{
size_t v_i_boxed_4073_; size_t v_stop_boxed_4074_; lean_object* v_res_4075_; 
v_i_boxed_4073_ = lean_unbox_usize(v_i_4068_);
lean_dec(v_i_4068_);
v_stop_boxed_4074_ = lean_unbox_usize(v_stop_4069_);
lean_dec(v_stop_4069_);
v_res_4075_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__1(v_as_4067_, v_i_boxed_4073_, v_stop_boxed_4074_, v_b_4070_, v___y_4071_);
lean_dec_ref(v___y_4071_);
lean_dec_ref(v_as_4067_);
return v_res_4075_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_AttributeExtension_addImported(lean_object* v_es_4076_, lean_object* v_a_4077_){
_start:
{
lean_object* v_a_4080_; lean_object* v___y_4085_; lean_object* v___x_4095_; lean_object* v___x_4096_; lean_object* v___x_4097_; lean_object* v___x_4098_; uint8_t v___x_4099_; 
v___x_4095_ = l_Lean_attributeMapRef;
v___x_4096_ = lean_st_ref_get(v___x_4095_);
v___x_4097_ = lean_unsigned_to_nat(0u);
v___x_4098_ = lean_array_get_size(v_es_4076_);
v___x_4099_ = lean_nat_dec_lt(v___x_4097_, v___x_4098_);
if (v___x_4099_ == 0)
{
v_a_4080_ = v___x_4096_;
goto v___jp_4079_;
}
else
{
uint8_t v___x_4100_; 
v___x_4100_ = lean_nat_dec_le(v___x_4098_, v___x_4098_);
if (v___x_4100_ == 0)
{
if (v___x_4099_ == 0)
{
v_a_4080_ = v___x_4096_;
goto v___jp_4079_;
}
else
{
size_t v___x_4101_; size_t v___x_4102_; lean_object* v___x_4103_; 
v___x_4101_ = ((size_t)0ULL);
v___x_4102_ = lean_usize_of_nat(v___x_4098_);
v___x_4103_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__1(v_es_4076_, v___x_4101_, v___x_4102_, v___x_4096_, v_a_4077_);
v___y_4085_ = v___x_4103_;
goto v___jp_4084_;
}
}
else
{
size_t v___x_4104_; size_t v___x_4105_; lean_object* v___x_4106_; 
v___x_4104_ = ((size_t)0ULL);
v___x_4105_ = lean_usize_of_nat(v___x_4098_);
v___x_4106_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__1(v_es_4076_, v___x_4104_, v___x_4105_, v___x_4096_, v_a_4077_);
v___y_4085_ = v___x_4106_;
goto v___jp_4084_;
}
}
v___jp_4079_:
{
lean_object* v___x_4081_; lean_object* v___x_4082_; lean_object* v___x_4083_; 
v___x_4081_ = lean_box(0);
v___x_4082_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4082_, 0, v___x_4081_);
lean_ctor_set(v___x_4082_, 1, v_a_4080_);
v___x_4083_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4083_, 0, v___x_4082_);
return v___x_4083_;
}
v___jp_4084_:
{
if (lean_obj_tag(v___y_4085_) == 0)
{
lean_object* v_a_4086_; 
v_a_4086_ = lean_ctor_get(v___y_4085_, 0);
lean_inc(v_a_4086_);
lean_dec_ref_known(v___y_4085_, 1);
v_a_4080_ = v_a_4086_;
goto v___jp_4079_;
}
else
{
lean_object* v_a_4087_; lean_object* v___x_4089_; uint8_t v_isShared_4090_; uint8_t v_isSharedCheck_4094_; 
v_a_4087_ = lean_ctor_get(v___y_4085_, 0);
v_isSharedCheck_4094_ = !lean_is_exclusive(v___y_4085_);
if (v_isSharedCheck_4094_ == 0)
{
v___x_4089_ = v___y_4085_;
v_isShared_4090_ = v_isSharedCheck_4094_;
goto v_resetjp_4088_;
}
else
{
lean_inc(v_a_4087_);
lean_dec(v___y_4085_);
v___x_4089_ = lean_box(0);
v_isShared_4090_ = v_isSharedCheck_4094_;
goto v_resetjp_4088_;
}
v_resetjp_4088_:
{
lean_object* v___x_4092_; 
if (v_isShared_4090_ == 0)
{
v___x_4092_ = v___x_4089_;
goto v_reusejp_4091_;
}
else
{
lean_object* v_reuseFailAlloc_4093_; 
v_reuseFailAlloc_4093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4093_, 0, v_a_4087_);
v___x_4092_ = v_reuseFailAlloc_4093_;
goto v_reusejp_4091_;
}
v_reusejp_4091_:
{
return v___x_4092_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_AttributeExtension_addImported___boxed(lean_object* v_es_4107_, lean_object* v_a_4108_, lean_object* v_a_4109_){
_start:
{
lean_object* v_res_4110_; 
v_res_4110_ = l___private_Lean_Attributes_0__Lean_AttributeExtension_addImported(v_es_4107_, v_a_4108_);
lean_dec_ref(v_a_4108_);
lean_dec_ref(v_es_4107_);
return v_res_4110_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0(lean_object* v_as_4111_, size_t v_i_4112_, size_t v_stop_4113_, lean_object* v_b_4114_, lean_object* v___y_4115_){
_start:
{
lean_object* v___x_4117_; 
v___x_4117_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg(v_as_4111_, v_i_4112_, v_stop_4113_, v_b_4114_);
return v___x_4117_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___boxed(lean_object* v_as_4118_, lean_object* v_i_4119_, lean_object* v_stop_4120_, lean_object* v_b_4121_, lean_object* v___y_4122_, lean_object* v___y_4123_){
_start:
{
size_t v_i_boxed_4124_; size_t v_stop_boxed_4125_; lean_object* v_res_4126_; 
v_i_boxed_4124_ = lean_unbox_usize(v_i_4119_);
lean_dec(v_i_4119_);
v_stop_boxed_4125_ = lean_unbox_usize(v_stop_4120_);
lean_dec(v_stop_4120_);
v_res_4126_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0(v_as_4118_, v_i_boxed_4124_, v_stop_boxed_4125_, v_b_4121_, v___y_4122_);
lean_dec_ref(v___y_4122_);
lean_dec_ref(v_as_4118_);
return v_res_4126_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_addAttrEntry(lean_object* v_s_4127_, lean_object* v_e_4128_){
_start:
{
lean_object* v_snd_4129_; lean_object* v_toAttributeImplCore_4130_; lean_object* v_fst_4131_; lean_object* v___x_4133_; uint8_t v_isShared_4134_; uint8_t v_isSharedCheck_4149_; 
v_snd_4129_ = lean_ctor_get(v_e_4128_, 1);
lean_inc(v_snd_4129_);
v_toAttributeImplCore_4130_ = lean_ctor_get(v_snd_4129_, 0);
v_fst_4131_ = lean_ctor_get(v_e_4128_, 0);
v_isSharedCheck_4149_ = !lean_is_exclusive(v_e_4128_);
if (v_isSharedCheck_4149_ == 0)
{
lean_object* v_unused_4150_; 
v_unused_4150_ = lean_ctor_get(v_e_4128_, 1);
lean_dec(v_unused_4150_);
v___x_4133_ = v_e_4128_;
v_isShared_4134_ = v_isSharedCheck_4149_;
goto v_resetjp_4132_;
}
else
{
lean_inc(v_fst_4131_);
lean_dec(v_e_4128_);
v___x_4133_ = lean_box(0);
v_isShared_4134_ = v_isSharedCheck_4149_;
goto v_resetjp_4132_;
}
v_resetjp_4132_:
{
lean_object* v_newEntries_4135_; lean_object* v_map_4136_; lean_object* v___x_4138_; uint8_t v_isShared_4139_; uint8_t v_isSharedCheck_4148_; 
v_newEntries_4135_ = lean_ctor_get(v_s_4127_, 0);
v_map_4136_ = lean_ctor_get(v_s_4127_, 1);
v_isSharedCheck_4148_ = !lean_is_exclusive(v_s_4127_);
if (v_isSharedCheck_4148_ == 0)
{
v___x_4138_ = v_s_4127_;
v_isShared_4139_ = v_isSharedCheck_4148_;
goto v_resetjp_4137_;
}
else
{
lean_inc(v_map_4136_);
lean_inc(v_newEntries_4135_);
lean_dec(v_s_4127_);
v___x_4138_ = lean_box(0);
v_isShared_4139_ = v_isSharedCheck_4148_;
goto v_resetjp_4137_;
}
v_resetjp_4137_:
{
lean_object* v_name_4140_; lean_object* v___x_4142_; 
v_name_4140_ = lean_ctor_get(v_toAttributeImplCore_4130_, 1);
lean_inc(v_name_4140_);
if (v_isShared_4134_ == 0)
{
lean_ctor_set_tag(v___x_4133_, 1);
lean_ctor_set(v___x_4133_, 1, v_newEntries_4135_);
v___x_4142_ = v___x_4133_;
goto v_reusejp_4141_;
}
else
{
lean_object* v_reuseFailAlloc_4147_; 
v_reuseFailAlloc_4147_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4147_, 0, v_fst_4131_);
lean_ctor_set(v_reuseFailAlloc_4147_, 1, v_newEntries_4135_);
v___x_4142_ = v_reuseFailAlloc_4147_;
goto v_reusejp_4141_;
}
v_reusejp_4141_:
{
lean_object* v___x_4143_; lean_object* v___x_4145_; 
v___x_4143_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1___redArg(v_map_4136_, v_name_4140_, v_snd_4129_);
if (v_isShared_4139_ == 0)
{
lean_ctor_set(v___x_4138_, 1, v___x_4143_);
lean_ctor_set(v___x_4138_, 0, v___x_4142_);
v___x_4145_ = v___x_4138_;
goto v_reusejp_4144_;
}
else
{
lean_object* v_reuseFailAlloc_4146_; 
v_reuseFailAlloc_4146_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4146_, 0, v___x_4142_);
lean_ctor_set(v_reuseFailAlloc_4146_, 1, v___x_4143_);
v___x_4145_ = v_reuseFailAlloc_4146_;
goto v_reusejp_4144_;
}
v_reusejp_4144_:
{
return v___x_4145_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn___lam__0_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(lean_object* v_x_4151_, lean_object* v_s_4152_){
_start:
{
lean_object* v_newEntries_4153_; lean_object* v___x_4154_; lean_object* v___x_4155_; lean_object* v___x_4156_; 
v_newEntries_4153_ = lean_ctor_get(v_s_4152_, 0);
lean_inc(v_newEntries_4153_);
lean_dec_ref(v_s_4152_);
v___x_4154_ = l_List_reverse___redArg(v_newEntries_4153_);
v___x_4155_ = lean_array_mk(v___x_4154_);
lean_inc_ref_n(v___x_4155_, 2);
v___x_4156_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4156_, 0, v___x_4155_);
lean_ctor_set(v___x_4156_, 1, v___x_4155_);
lean_ctor_set(v___x_4156_, 2, v___x_4155_);
return v___x_4156_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn___lam__0_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2____boxed(lean_object* v_x_4157_, lean_object* v_s_4158_){
_start:
{
lean_object* v_res_4159_; 
v_res_4159_ = l___private_Lean_Attributes_0__Lean_initFn___lam__0_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(v_x_4157_, v_s_4158_);
lean_dec_ref(v_x_4157_);
return v_res_4159_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn___lam__1_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(lean_object* v_s_4160_){
_start:
{
lean_object* v_newEntries_4161_; lean_object* v___x_4163_; uint8_t v_isShared_4164_; uint8_t v_isSharedCheck_4172_; 
v_newEntries_4161_ = lean_ctor_get(v_s_4160_, 0);
v_isSharedCheck_4172_ = !lean_is_exclusive(v_s_4160_);
if (v_isSharedCheck_4172_ == 0)
{
lean_object* v_unused_4173_; 
v_unused_4173_ = lean_ctor_get(v_s_4160_, 1);
lean_dec(v_unused_4173_);
v___x_4163_ = v_s_4160_;
v_isShared_4164_ = v_isSharedCheck_4172_;
goto v_resetjp_4162_;
}
else
{
lean_inc(v_newEntries_4161_);
lean_dec(v_s_4160_);
v___x_4163_ = lean_box(0);
v_isShared_4164_ = v_isSharedCheck_4172_;
goto v_resetjp_4162_;
}
v_resetjp_4162_:
{
lean_object* v___x_4165_; lean_object* v___x_4166_; lean_object* v___x_4167_; lean_object* v___x_4168_; lean_object* v___x_4170_; 
v___x_4165_ = ((lean_object*)(l_Lean_registerTagAttribute___lam__2___closed__4));
v___x_4166_ = l_List_lengthTR___redArg(v_newEntries_4161_);
lean_dec(v_newEntries_4161_);
v___x_4167_ = l_Nat_reprFast(v___x_4166_);
v___x_4168_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4168_, 0, v___x_4167_);
if (v_isShared_4164_ == 0)
{
lean_ctor_set_tag(v___x_4163_, 5);
lean_ctor_set(v___x_4163_, 1, v___x_4168_);
lean_ctor_set(v___x_4163_, 0, v___x_4165_);
v___x_4170_ = v___x_4163_;
goto v_reusejp_4169_;
}
else
{
lean_object* v_reuseFailAlloc_4171_; 
v_reuseFailAlloc_4171_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4171_, 0, v___x_4165_);
lean_ctor_set(v_reuseFailAlloc_4171_, 1, v___x_4168_);
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
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn___lam__2_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(lean_object* v_s_4174_){
_start:
{
lean_object* v_newEntries_4175_; lean_object* v___x_4176_; lean_object* v___x_4177_; 
v_newEntries_4175_ = lean_ctor_get(v_s_4174_, 0);
lean_inc(v_newEntries_4175_);
lean_dec_ref(v_s_4174_);
v___x_4176_ = l_List_reverse___redArg(v_newEntries_4175_);
v___x_4177_ = lean_array_mk(v___x_4176_);
return v___x_4177_;
}
}
static lean_object* _init_l___private_Lean_Attributes_0__Lean_initFn___closed__7_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4187_; lean_object* v___x_4188_; lean_object* v___f_4189_; lean_object* v___f_4190_; lean_object* v___x_4191_; lean_object* v___x_4192_; lean_object* v___x_4193_; lean_object* v___x_4194_; lean_object* v___x_4195_; 
v___x_4187_ = lean_box(0);
v___x_4188_ = lean_box(2);
v___f_4189_ = ((lean_object*)(l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___f_4190_ = ((lean_object*)(l___private_Lean_Attributes_0__Lean_initFn___closed__0_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___x_4191_ = ((lean_object*)(l___private_Lean_Attributes_0__Lean_initFn___closed__6_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___x_4192_ = ((lean_object*)(l___private_Lean_Attributes_0__Lean_initFn___closed__5_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___x_4193_ = lean_alloc_closure((void*)(l___private_Lean_Attributes_0__Lean_AttributeExtension_mkInitial___boxed), 1, 0);
v___x_4194_ = ((lean_object*)(l___private_Lean_Attributes_0__Lean_initFn___closed__4_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___x_4195_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_4195_, 0, v___x_4194_);
lean_ctor_set(v___x_4195_, 1, v___x_4193_);
lean_ctor_set(v___x_4195_, 2, v___x_4192_);
lean_ctor_set(v___x_4195_, 3, v___x_4191_);
lean_ctor_set(v___x_4195_, 4, v___f_4190_);
lean_ctor_set(v___x_4195_, 5, v___f_4189_);
lean_ctor_set(v___x_4195_, 6, v___x_4188_);
lean_ctor_set(v___x_4195_, 7, v___x_4187_);
return v___x_4195_;
}
}
static lean_object* _init_l___private_Lean_Attributes_0__Lean_initFn___closed__8_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_4196_; lean_object* v___x_4197_; lean_object* v___x_4198_; 
v___f_4196_ = ((lean_object*)(l___private_Lean_Attributes_0__Lean_initFn___closed__2_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___x_4197_ = lean_obj_once(&l___private_Lean_Attributes_0__Lean_initFn___closed__7_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_, &l___private_Lean_Attributes_0__Lean_initFn___closed__7_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2__once, _init_l___private_Lean_Attributes_0__Lean_initFn___closed__7_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_);
v___x_4198_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4198_, 0, v___x_4197_);
lean_ctor_set(v___x_4198_, 1, v___f_4196_);
return v___x_4198_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4200_; lean_object* v___x_4201_; 
v___x_4200_ = lean_obj_once(&l___private_Lean_Attributes_0__Lean_initFn___closed__8_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_, &l___private_Lean_Attributes_0__Lean_initFn___closed__8_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2__once, _init_l___private_Lean_Attributes_0__Lean_initFn___closed__8_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_);
v___x_4201_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_4200_);
return v___x_4201_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2____boxed(lean_object* v_a_4202_){
_start:
{
lean_object* v_res_4203_; 
v_res_4203_ = l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_();
return v_res_4203_;
}
}
LEAN_EXPORT lean_object* l_Lean_isBuiltinAttribute(lean_object* v_n_4204_){
_start:
{
lean_object* v___x_4206_; lean_object* v___x_4207_; uint8_t v___x_4208_; lean_object* v___x_4209_; lean_object* v___x_4210_; 
v___x_4206_ = l_Lean_attributeMapRef;
v___x_4207_ = lean_st_ref_get(v___x_4206_);
v___x_4208_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(v___x_4207_, v_n_4204_);
lean_dec(v___x_4207_);
v___x_4209_ = lean_box(v___x_4208_);
v___x_4210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4210_, 0, v___x_4209_);
return v___x_4210_;
}
}
LEAN_EXPORT lean_object* l_Lean_isBuiltinAttribute___boxed(lean_object* v_n_4211_, lean_object* v_a_4212_){
_start:
{
lean_object* v_res_4213_; 
v_res_4213_ = l_Lean_isBuiltinAttribute(v_n_4211_);
lean_dec(v_n_4211_);
return v_res_4213_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_getBuiltinAttributeNames_spec__0(lean_object* v_x_4214_, lean_object* v_x_4215_){
_start:
{
if (lean_obj_tag(v_x_4215_) == 0)
{
return v_x_4214_;
}
else
{
lean_object* v_key_4216_; lean_object* v_tail_4217_; lean_object* v___x_4218_; 
v_key_4216_ = lean_ctor_get(v_x_4215_, 0);
v_tail_4217_ = lean_ctor_get(v_x_4215_, 2);
lean_inc(v_key_4216_);
v___x_4218_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4218_, 0, v_key_4216_);
lean_ctor_set(v___x_4218_, 1, v_x_4214_);
v_x_4214_ = v___x_4218_;
v_x_4215_ = v_tail_4217_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_getBuiltinAttributeNames_spec__0___boxed(lean_object* v_x_4220_, lean_object* v_x_4221_){
_start:
{
lean_object* v_res_4222_; 
v_res_4222_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_getBuiltinAttributeNames_spec__0(v_x_4220_, v_x_4221_);
lean_dec(v_x_4221_);
return v_res_4222_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1(lean_object* v_as_4223_, size_t v_i_4224_, size_t v_stop_4225_, lean_object* v_b_4226_){
_start:
{
uint8_t v___x_4227_; 
v___x_4227_ = lean_usize_dec_eq(v_i_4224_, v_stop_4225_);
if (v___x_4227_ == 0)
{
lean_object* v___x_4228_; lean_object* v___x_4229_; size_t v___x_4230_; size_t v___x_4231_; 
v___x_4228_ = lean_array_uget_borrowed(v_as_4223_, v_i_4224_);
v___x_4229_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_getBuiltinAttributeNames_spec__0(v_b_4226_, v___x_4228_);
v___x_4230_ = ((size_t)1ULL);
v___x_4231_ = lean_usize_add(v_i_4224_, v___x_4230_);
v_i_4224_ = v___x_4231_;
v_b_4226_ = v___x_4229_;
goto _start;
}
else
{
return v_b_4226_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1___boxed(lean_object* v_as_4233_, lean_object* v_i_4234_, lean_object* v_stop_4235_, lean_object* v_b_4236_){
_start:
{
size_t v_i_boxed_4237_; size_t v_stop_boxed_4238_; lean_object* v_res_4239_; 
v_i_boxed_4237_ = lean_unbox_usize(v_i_4234_);
lean_dec(v_i_4234_);
v_stop_boxed_4238_ = lean_unbox_usize(v_stop_4235_);
lean_dec(v_stop_4235_);
v_res_4239_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1(v_as_4233_, v_i_boxed_4237_, v_stop_boxed_4238_, v_b_4236_);
lean_dec_ref(v_as_4233_);
return v_res_4239_;
}
}
LEAN_EXPORT lean_object* l_Lean_getBuiltinAttributeNames(){
_start:
{
lean_object* v___x_4241_; lean_object* v___x_4242_; lean_object* v_buckets_4243_; lean_object* v___x_4244_; lean_object* v___x_4245_; lean_object* v___x_4246_; uint8_t v___x_4247_; 
v___x_4241_ = l_Lean_attributeMapRef;
v___x_4242_ = lean_st_ref_get(v___x_4241_);
v_buckets_4243_ = lean_ctor_get(v___x_4242_, 1);
lean_inc_ref(v_buckets_4243_);
lean_dec(v___x_4242_);
v___x_4244_ = lean_box(0);
v___x_4245_ = lean_unsigned_to_nat(0u);
v___x_4246_ = lean_array_get_size(v_buckets_4243_);
v___x_4247_ = lean_nat_dec_lt(v___x_4245_, v___x_4246_);
if (v___x_4247_ == 0)
{
lean_object* v___x_4248_; 
lean_dec_ref(v_buckets_4243_);
v___x_4248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4248_, 0, v___x_4244_);
return v___x_4248_;
}
else
{
size_t v___x_4249_; size_t v___x_4250_; lean_object* v___x_4251_; lean_object* v___x_4252_; 
v___x_4249_ = ((size_t)0ULL);
v___x_4250_ = lean_usize_of_nat(v___x_4246_);
v___x_4251_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1(v_buckets_4243_, v___x_4249_, v___x_4250_, v___x_4244_);
lean_dec_ref(v_buckets_4243_);
v___x_4252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4252_, 0, v___x_4251_);
return v___x_4252_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getBuiltinAttributeNames___boxed(lean_object* v_a_4253_){
_start:
{
lean_object* v_res_4254_; 
v_res_4254_ = l_Lean_getBuiltinAttributeNames();
return v_res_4254_;
}
}
LEAN_EXPORT lean_object* l_Lean_getBuiltinAttributeImpl(lean_object* v_attrName_4256_){
_start:
{
lean_object* v___x_4258_; lean_object* v___x_4259_; lean_object* v___x_4260_; 
v___x_4258_ = l_Lean_attributeMapRef;
v___x_4259_ = lean_st_ref_get(v___x_4258_);
v___x_4260_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(v___x_4259_, v_attrName_4256_);
lean_dec(v___x_4259_);
if (lean_obj_tag(v___x_4260_) == 0)
{
lean_object* v___x_4261_; uint8_t v___x_4262_; lean_object* v___x_4263_; lean_object* v___x_4264_; lean_object* v___x_4265_; lean_object* v___x_4266_; lean_object* v___x_4267_; lean_object* v___x_4268_; 
v___x_4261_ = ((lean_object*)(l_Lean_getBuiltinAttributeImpl___closed__0));
v___x_4262_ = 1;
v___x_4263_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_attrName_4256_, v___x_4262_);
v___x_4264_ = lean_string_append(v___x_4261_, v___x_4263_);
lean_dec_ref(v___x_4263_);
v___x_4265_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__4));
v___x_4266_ = lean_string_append(v___x_4264_, v___x_4265_);
v___x_4267_ = lean_mk_io_user_error(v___x_4266_);
v___x_4268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4268_, 0, v___x_4267_);
return v___x_4268_;
}
else
{
lean_object* v_val_4269_; lean_object* v___x_4271_; uint8_t v_isShared_4272_; uint8_t v_isSharedCheck_4276_; 
lean_dec(v_attrName_4256_);
v_val_4269_ = lean_ctor_get(v___x_4260_, 0);
v_isSharedCheck_4276_ = !lean_is_exclusive(v___x_4260_);
if (v_isSharedCheck_4276_ == 0)
{
v___x_4271_ = v___x_4260_;
v_isShared_4272_ = v_isSharedCheck_4276_;
goto v_resetjp_4270_;
}
else
{
lean_inc(v_val_4269_);
lean_dec(v___x_4260_);
v___x_4271_ = lean_box(0);
v_isShared_4272_ = v_isSharedCheck_4276_;
goto v_resetjp_4270_;
}
v_resetjp_4270_:
{
lean_object* v___x_4274_; 
if (v_isShared_4272_ == 0)
{
lean_ctor_set_tag(v___x_4271_, 0);
v___x_4274_ = v___x_4271_;
goto v_reusejp_4273_;
}
else
{
lean_object* v_reuseFailAlloc_4275_; 
v_reuseFailAlloc_4275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4275_, 0, v_val_4269_);
v___x_4274_ = v_reuseFailAlloc_4275_;
goto v_reusejp_4273_;
}
v_reusejp_4273_:
{
return v___x_4274_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getBuiltinAttributeImpl___boxed(lean_object* v_attrName_4277_, lean_object* v_a_4278_){
_start:
{
lean_object* v_res_4279_; 
v_res_4279_ = l_Lean_getBuiltinAttributeImpl(v_attrName_4277_);
return v_res_4279_;
}
}
LEAN_EXPORT uint8_t l_Lean_isAttribute(lean_object* v_env_4280_, lean_object* v_attrName_4281_){
_start:
{
lean_object* v___x_4282_; lean_object* v_toEnvExtension_4283_; lean_object* v_asyncMode_4284_; lean_object* v___x_4285_; lean_object* v___x_4286_; lean_object* v___x_4287_; lean_object* v_map_4288_; uint8_t v___x_4289_; 
v___x_4282_ = l_Lean_attributeExtension;
v_toEnvExtension_4283_ = lean_ctor_get(v___x_4282_, 0);
v_asyncMode_4284_ = lean_ctor_get(v_toEnvExtension_4283_, 2);
v___x_4285_ = l_Lean_instInhabitedAttributeExtensionState_default;
v___x_4286_ = lean_box(0);
v___x_4287_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_4285_, v___x_4282_, v_env_4280_, v_asyncMode_4284_, v___x_4286_);
v_map_4288_ = lean_ctor_get(v___x_4287_, 1);
lean_inc_ref(v_map_4288_);
lean_dec(v___x_4287_);
v___x_4289_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(v_map_4288_, v_attrName_4281_);
lean_dec_ref(v_map_4288_);
return v___x_4289_;
}
}
LEAN_EXPORT lean_object* l_Lean_isAttribute___boxed(lean_object* v_env_4290_, lean_object* v_attrName_4291_){
_start:
{
uint8_t v_res_4292_; lean_object* v_r_4293_; 
v_res_4292_ = l_Lean_isAttribute(v_env_4290_, v_attrName_4291_);
lean_dec(v_attrName_4291_);
v_r_4293_ = lean_box(v_res_4292_);
return v_r_4293_;
}
}
LEAN_EXPORT lean_object* l_Lean_getAttributeNames(lean_object* v_env_4294_){
_start:
{
lean_object* v___x_4295_; lean_object* v_toEnvExtension_4296_; lean_object* v_asyncMode_4297_; lean_object* v___x_4298_; lean_object* v___x_4299_; lean_object* v___x_4300_; lean_object* v_map_4301_; lean_object* v_buckets_4302_; lean_object* v___x_4303_; lean_object* v___x_4304_; lean_object* v___x_4305_; uint8_t v___x_4306_; 
v___x_4295_ = l_Lean_attributeExtension;
v_toEnvExtension_4296_ = lean_ctor_get(v___x_4295_, 0);
v_asyncMode_4297_ = lean_ctor_get(v_toEnvExtension_4296_, 2);
v___x_4298_ = l_Lean_instInhabitedAttributeExtensionState_default;
v___x_4299_ = lean_box(0);
v___x_4300_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_4298_, v___x_4295_, v_env_4294_, v_asyncMode_4297_, v___x_4299_);
v_map_4301_ = lean_ctor_get(v___x_4300_, 1);
lean_inc_ref(v_map_4301_);
lean_dec(v___x_4300_);
v_buckets_4302_ = lean_ctor_get(v_map_4301_, 1);
lean_inc_ref(v_buckets_4302_);
lean_dec_ref(v_map_4301_);
v___x_4303_ = lean_box(0);
v___x_4304_ = lean_unsigned_to_nat(0u);
v___x_4305_ = lean_array_get_size(v_buckets_4302_);
v___x_4306_ = lean_nat_dec_lt(v___x_4304_, v___x_4305_);
if (v___x_4306_ == 0)
{
lean_dec_ref(v_buckets_4302_);
return v___x_4303_;
}
else
{
size_t v___x_4307_; size_t v___x_4308_; lean_object* v___x_4309_; 
v___x_4307_ = ((size_t)0ULL);
v___x_4308_ = lean_usize_of_nat(v___x_4305_);
v___x_4309_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1(v_buckets_4302_, v___x_4307_, v___x_4308_, v___x_4303_);
lean_dec_ref(v_buckets_4302_);
return v___x_4309_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getAttributeImpl(lean_object* v_env_4310_, lean_object* v_attrName_4311_){
_start:
{
lean_object* v___x_4312_; lean_object* v_toEnvExtension_4313_; lean_object* v_asyncMode_4314_; lean_object* v___x_4315_; lean_object* v___x_4316_; lean_object* v___x_4317_; lean_object* v_map_4318_; lean_object* v___x_4319_; 
v___x_4312_ = l_Lean_attributeExtension;
v_toEnvExtension_4313_ = lean_ctor_get(v___x_4312_, 0);
v_asyncMode_4314_ = lean_ctor_get(v_toEnvExtension_4313_, 2);
v___x_4315_ = l_Lean_instInhabitedAttributeExtensionState_default;
v___x_4316_ = lean_box(0);
v___x_4317_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_4315_, v___x_4312_, v_env_4310_, v_asyncMode_4314_, v___x_4316_);
v_map_4318_ = lean_ctor_get(v___x_4317_, 1);
lean_inc_ref(v_map_4318_);
lean_dec(v___x_4317_);
v___x_4319_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(v_map_4318_, v_attrName_4311_);
lean_dec_ref(v_map_4318_);
if (lean_obj_tag(v___x_4319_) == 0)
{
lean_object* v___x_4320_; uint8_t v___x_4321_; lean_object* v___x_4322_; lean_object* v___x_4323_; lean_object* v___x_4324_; lean_object* v___x_4325_; lean_object* v___x_4326_; 
v___x_4320_ = ((lean_object*)(l_Lean_getBuiltinAttributeImpl___closed__0));
v___x_4321_ = 1;
v___x_4322_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_attrName_4311_, v___x_4321_);
v___x_4323_ = lean_string_append(v___x_4320_, v___x_4322_);
lean_dec_ref(v___x_4322_);
v___x_4324_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__4));
v___x_4325_ = lean_string_append(v___x_4323_, v___x_4324_);
v___x_4326_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4326_, 0, v___x_4325_);
return v___x_4326_;
}
else
{
lean_object* v_val_4327_; lean_object* v___x_4329_; uint8_t v_isShared_4330_; uint8_t v_isSharedCheck_4334_; 
lean_dec(v_attrName_4311_);
v_val_4327_ = lean_ctor_get(v___x_4319_, 0);
v_isSharedCheck_4334_ = !lean_is_exclusive(v___x_4319_);
if (v_isSharedCheck_4334_ == 0)
{
v___x_4329_ = v___x_4319_;
v_isShared_4330_ = v_isSharedCheck_4334_;
goto v_resetjp_4328_;
}
else
{
lean_inc(v_val_4327_);
lean_dec(v___x_4319_);
v___x_4329_ = lean_box(0);
v_isShared_4330_ = v_isSharedCheck_4334_;
goto v_resetjp_4328_;
}
v_resetjp_4328_:
{
lean_object* v___x_4332_; 
if (v_isShared_4330_ == 0)
{
v___x_4332_ = v___x_4329_;
goto v_reusejp_4331_;
}
else
{
lean_object* v_reuseFailAlloc_4333_; 
v_reuseFailAlloc_4333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4333_, 0, v_val_4327_);
v___x_4332_ = v_reuseFailAlloc_4333_;
goto v_reusejp_4331_;
}
v_reusejp_4331_:
{
return v___x_4332_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerAttributeOfBuilder(lean_object* v_env_4335_, lean_object* v_builderId_4336_, lean_object* v_ref_4337_, lean_object* v_args_4338_){
_start:
{
lean_object* v_entry_4340_; lean_object* v___x_4341_; 
v_entry_4340_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_entry_4340_, 0, v_builderId_4336_);
lean_ctor_set(v_entry_4340_, 1, v_ref_4337_);
lean_ctor_set(v_entry_4340_, 2, v_args_4338_);
lean_inc_ref(v_entry_4340_);
v___x_4341_ = l_Lean_mkAttributeImplOfEntry(v_entry_4340_);
if (lean_obj_tag(v___x_4341_) == 0)
{
lean_object* v_a_4342_; lean_object* v___x_4344_; uint8_t v_isShared_4345_; uint8_t v_isSharedCheck_4367_; 
v_a_4342_ = lean_ctor_get(v___x_4341_, 0);
v_isSharedCheck_4367_ = !lean_is_exclusive(v___x_4341_);
if (v_isSharedCheck_4367_ == 0)
{
v___x_4344_ = v___x_4341_;
v_isShared_4345_ = v_isSharedCheck_4367_;
goto v_resetjp_4343_;
}
else
{
lean_inc(v_a_4342_);
lean_dec(v___x_4341_);
v___x_4344_ = lean_box(0);
v_isShared_4345_ = v_isSharedCheck_4367_;
goto v_resetjp_4343_;
}
v_resetjp_4343_:
{
lean_object* v_toAttributeImplCore_4346_; lean_object* v_name_4347_; uint8_t v___x_4348_; 
v_toAttributeImplCore_4346_ = lean_ctor_get(v_a_4342_, 0);
v_name_4347_ = lean_ctor_get(v_toAttributeImplCore_4346_, 1);
lean_inc_ref(v_env_4335_);
v___x_4348_ = l_Lean_isAttribute(v_env_4335_, v_name_4347_);
if (v___x_4348_ == 0)
{
lean_object* v___x_4349_; lean_object* v_toEnvExtension_4350_; lean_object* v_asyncMode_4351_; lean_object* v___x_4352_; lean_object* v___x_4353_; lean_object* v___x_4354_; lean_object* v___x_4356_; 
v___x_4349_ = l_Lean_attributeExtension;
v_toEnvExtension_4350_ = lean_ctor_get(v___x_4349_, 0);
v_asyncMode_4351_ = lean_ctor_get(v_toEnvExtension_4350_, 2);
v___x_4352_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4352_, 0, v_entry_4340_);
lean_ctor_set(v___x_4352_, 1, v_a_4342_);
v___x_4353_ = lean_box(0);
v___x_4354_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_4349_, v_env_4335_, v___x_4352_, v_asyncMode_4351_, v___x_4353_);
if (v_isShared_4345_ == 0)
{
lean_ctor_set(v___x_4344_, 0, v___x_4354_);
v___x_4356_ = v___x_4344_;
goto v_reusejp_4355_;
}
else
{
lean_object* v_reuseFailAlloc_4357_; 
v_reuseFailAlloc_4357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4357_, 0, v___x_4354_);
v___x_4356_ = v_reuseFailAlloc_4357_;
goto v_reusejp_4355_;
}
v_reusejp_4355_:
{
return v___x_4356_;
}
}
else
{
lean_object* v___x_4358_; lean_object* v___x_4359_; lean_object* v___x_4360_; lean_object* v___x_4361_; lean_object* v___x_4362_; lean_object* v___x_4363_; lean_object* v___x_4365_; 
lean_inc(v_name_4347_);
lean_dec(v_a_4342_);
lean_dec_ref_known(v_entry_4340_, 3);
lean_dec_ref(v_env_4335_);
v___x_4358_ = ((lean_object*)(l_Lean_registerBuiltinAttribute___closed__2));
v___x_4359_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_4347_, v___x_4348_);
v___x_4360_ = lean_string_append(v___x_4358_, v___x_4359_);
lean_dec_ref(v___x_4359_);
v___x_4361_ = ((lean_object*)(l_Lean_registerBuiltinAttribute___closed__3));
v___x_4362_ = lean_string_append(v___x_4360_, v___x_4361_);
v___x_4363_ = lean_mk_io_user_error(v___x_4362_);
if (v_isShared_4345_ == 0)
{
lean_ctor_set_tag(v___x_4344_, 1);
lean_ctor_set(v___x_4344_, 0, v___x_4363_);
v___x_4365_ = v___x_4344_;
goto v_reusejp_4364_;
}
else
{
lean_object* v_reuseFailAlloc_4366_; 
v_reuseFailAlloc_4366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4366_, 0, v___x_4363_);
v___x_4365_ = v_reuseFailAlloc_4366_;
goto v_reusejp_4364_;
}
v_reusejp_4364_:
{
return v___x_4365_;
}
}
}
}
else
{
lean_object* v_a_4368_; lean_object* v___x_4370_; uint8_t v_isShared_4371_; uint8_t v_isSharedCheck_4375_; 
lean_dec_ref_known(v_entry_4340_, 3);
lean_dec_ref(v_env_4335_);
v_a_4368_ = lean_ctor_get(v___x_4341_, 0);
v_isSharedCheck_4375_ = !lean_is_exclusive(v___x_4341_);
if (v_isSharedCheck_4375_ == 0)
{
v___x_4370_ = v___x_4341_;
v_isShared_4371_ = v_isSharedCheck_4375_;
goto v_resetjp_4369_;
}
else
{
lean_inc(v_a_4368_);
lean_dec(v___x_4341_);
v___x_4370_ = lean_box(0);
v_isShared_4371_ = v_isSharedCheck_4375_;
goto v_resetjp_4369_;
}
v_resetjp_4369_:
{
lean_object* v___x_4373_; 
if (v_isShared_4371_ == 0)
{
v___x_4373_ = v___x_4370_;
goto v_reusejp_4372_;
}
else
{
lean_object* v_reuseFailAlloc_4374_; 
v_reuseFailAlloc_4374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4374_, 0, v_a_4368_);
v___x_4373_ = v_reuseFailAlloc_4374_;
goto v_reusejp_4372_;
}
v_reusejp_4372_:
{
return v___x_4373_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerAttributeOfBuilder___boxed(lean_object* v_env_4376_, lean_object* v_builderId_4377_, lean_object* v_ref_4378_, lean_object* v_args_4379_, lean_object* v_a_4380_){
_start:
{
lean_object* v_res_4381_; 
v_res_4381_ = l_Lean_registerAttributeOfBuilder(v_env_4376_, v_builderId_4377_, v_ref_4378_, v_args_4379_);
return v_res_4381_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg(lean_object* v_x_4382_, lean_object* v___y_4383_, lean_object* v___y_4384_){
_start:
{
if (lean_obj_tag(v_x_4382_) == 0)
{
lean_object* v_a_4386_; lean_object* v___x_4387_; lean_object* v___x_4388_; 
v_a_4386_ = lean_ctor_get(v_x_4382_, 0);
lean_inc(v_a_4386_);
lean_dec_ref_known(v_x_4382_, 1);
v___x_4387_ = l_Lean_stringToMessageData(v_a_4386_);
v___x_4388_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_4387_, v___y_4383_, v___y_4384_);
return v___x_4388_;
}
else
{
lean_object* v_a_4389_; lean_object* v___x_4391_; uint8_t v_isShared_4392_; uint8_t v_isSharedCheck_4396_; 
v_a_4389_ = lean_ctor_get(v_x_4382_, 0);
v_isSharedCheck_4396_ = !lean_is_exclusive(v_x_4382_);
if (v_isSharedCheck_4396_ == 0)
{
v___x_4391_ = v_x_4382_;
v_isShared_4392_ = v_isSharedCheck_4396_;
goto v_resetjp_4390_;
}
else
{
lean_inc(v_a_4389_);
lean_dec(v_x_4382_);
v___x_4391_ = lean_box(0);
v_isShared_4392_ = v_isSharedCheck_4396_;
goto v_resetjp_4390_;
}
v_resetjp_4390_:
{
lean_object* v___x_4394_; 
if (v_isShared_4392_ == 0)
{
lean_ctor_set_tag(v___x_4391_, 0);
v___x_4394_ = v___x_4391_;
goto v_reusejp_4393_;
}
else
{
lean_object* v_reuseFailAlloc_4395_; 
v_reuseFailAlloc_4395_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4395_, 0, v_a_4389_);
v___x_4394_ = v_reuseFailAlloc_4395_;
goto v_reusejp_4393_;
}
v_reusejp_4393_:
{
return v___x_4394_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg___boxed(lean_object* v_x_4397_, lean_object* v___y_4398_, lean_object* v___y_4399_, lean_object* v___y_4400_){
_start:
{
lean_object* v_res_4401_; 
v_res_4401_ = l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg(v_x_4397_, v___y_4398_, v___y_4399_);
lean_dec(v___y_4399_);
lean_dec_ref(v___y_4398_);
return v_res_4401_;
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_add(lean_object* v_declName_4402_, lean_object* v_attrName_4403_, lean_object* v_stx_4404_, uint8_t v_kind_4405_, lean_object* v_a_4406_, lean_object* v_a_4407_){
_start:
{
lean_object* v___x_4409_; lean_object* v_env_4410_; lean_object* v___x_4411_; lean_object* v___x_4412_; 
v___x_4409_ = lean_st_ref_get(v_a_4407_);
v_env_4410_ = lean_ctor_get(v___x_4409_, 0);
lean_inc_ref(v_env_4410_);
lean_dec(v___x_4409_);
v___x_4411_ = l_Lean_getAttributeImpl(v_env_4410_, v_attrName_4403_);
v___x_4412_ = l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg(v___x_4411_, v_a_4406_, v_a_4407_);
if (lean_obj_tag(v___x_4412_) == 0)
{
lean_object* v_a_4413_; lean_object* v_add_4414_; lean_object* v___x_4415_; lean_object* v___x_4416_; 
v_a_4413_ = lean_ctor_get(v___x_4412_, 0);
lean_inc(v_a_4413_);
lean_dec_ref_known(v___x_4412_, 1);
v_add_4414_ = lean_ctor_get(v_a_4413_, 1);
lean_inc_ref(v_add_4414_);
lean_dec(v_a_4413_);
v___x_4415_ = lean_box(v_kind_4405_);
lean_inc(v_a_4407_);
lean_inc_ref(v_a_4406_);
v___x_4416_ = lean_apply_6(v_add_4414_, v_declName_4402_, v_stx_4404_, v___x_4415_, v_a_4406_, v_a_4407_, lean_box(0));
return v___x_4416_;
}
else
{
lean_object* v_a_4417_; lean_object* v___x_4419_; uint8_t v_isShared_4420_; uint8_t v_isSharedCheck_4424_; 
lean_dec(v_stx_4404_);
lean_dec(v_declName_4402_);
v_a_4417_ = lean_ctor_get(v___x_4412_, 0);
v_isSharedCheck_4424_ = !lean_is_exclusive(v___x_4412_);
if (v_isSharedCheck_4424_ == 0)
{
v___x_4419_ = v___x_4412_;
v_isShared_4420_ = v_isSharedCheck_4424_;
goto v_resetjp_4418_;
}
else
{
lean_inc(v_a_4417_);
lean_dec(v___x_4412_);
v___x_4419_ = lean_box(0);
v_isShared_4420_ = v_isSharedCheck_4424_;
goto v_resetjp_4418_;
}
v_resetjp_4418_:
{
lean_object* v___x_4422_; 
if (v_isShared_4420_ == 0)
{
v___x_4422_ = v___x_4419_;
goto v_reusejp_4421_;
}
else
{
lean_object* v_reuseFailAlloc_4423_; 
v_reuseFailAlloc_4423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4423_, 0, v_a_4417_);
v___x_4422_ = v_reuseFailAlloc_4423_;
goto v_reusejp_4421_;
}
v_reusejp_4421_:
{
return v___x_4422_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_add___boxed(lean_object* v_declName_4425_, lean_object* v_attrName_4426_, lean_object* v_stx_4427_, lean_object* v_kind_4428_, lean_object* v_a_4429_, lean_object* v_a_4430_, lean_object* v_a_4431_){
_start:
{
uint8_t v_kind_boxed_4432_; lean_object* v_res_4433_; 
v_kind_boxed_4432_ = lean_unbox(v_kind_4428_);
v_res_4433_ = l_Lean_Attribute_add(v_declName_4425_, v_attrName_4426_, v_stx_4427_, v_kind_boxed_4432_, v_a_4429_, v_a_4430_);
lean_dec(v_a_4430_);
lean_dec_ref(v_a_4429_);
return v_res_4433_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0(lean_object* v_00_u03b1_4434_, lean_object* v_x_4435_, lean_object* v___y_4436_, lean_object* v___y_4437_){
_start:
{
lean_object* v___x_4439_; 
v___x_4439_ = l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg(v_x_4435_, v___y_4436_, v___y_4437_);
return v___x_4439_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___boxed(lean_object* v_00_u03b1_4440_, lean_object* v_x_4441_, lean_object* v___y_4442_, lean_object* v___y_4443_, lean_object* v___y_4444_){
_start:
{
lean_object* v_res_4445_; 
v_res_4445_ = l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0(v_00_u03b1_4440_, v_x_4441_, v___y_4442_, v___y_4443_);
lean_dec(v___y_4443_);
lean_dec_ref(v___y_4442_);
return v_res_4445_;
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_erase(lean_object* v_declName_4446_, lean_object* v_attrName_4447_, lean_object* v_a_4448_, lean_object* v_a_4449_){
_start:
{
lean_object* v___x_4451_; lean_object* v_env_4452_; lean_object* v___x_4453_; lean_object* v___x_4454_; 
v___x_4451_ = lean_st_ref_get(v_a_4449_);
v_env_4452_ = lean_ctor_get(v___x_4451_, 0);
lean_inc_ref(v_env_4452_);
lean_dec(v___x_4451_);
v___x_4453_ = l_Lean_getAttributeImpl(v_env_4452_, v_attrName_4447_);
v___x_4454_ = l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg(v___x_4453_, v_a_4448_, v_a_4449_);
if (lean_obj_tag(v___x_4454_) == 0)
{
lean_object* v_a_4455_; lean_object* v_erase_4456_; lean_object* v___x_4457_; 
v_a_4455_ = lean_ctor_get(v___x_4454_, 0);
lean_inc(v_a_4455_);
lean_dec_ref_known(v___x_4454_, 1);
v_erase_4456_ = lean_ctor_get(v_a_4455_, 2);
lean_inc_ref(v_erase_4456_);
lean_dec(v_a_4455_);
lean_inc(v_a_4449_);
lean_inc_ref(v_a_4448_);
v___x_4457_ = lean_apply_4(v_erase_4456_, v_declName_4446_, v_a_4448_, v_a_4449_, lean_box(0));
return v___x_4457_;
}
else
{
lean_object* v_a_4458_; lean_object* v___x_4460_; uint8_t v_isShared_4461_; uint8_t v_isSharedCheck_4465_; 
lean_dec(v_declName_4446_);
v_a_4458_ = lean_ctor_get(v___x_4454_, 0);
v_isSharedCheck_4465_ = !lean_is_exclusive(v___x_4454_);
if (v_isSharedCheck_4465_ == 0)
{
v___x_4460_ = v___x_4454_;
v_isShared_4461_ = v_isSharedCheck_4465_;
goto v_resetjp_4459_;
}
else
{
lean_inc(v_a_4458_);
lean_dec(v___x_4454_);
v___x_4460_ = lean_box(0);
v_isShared_4461_ = v_isSharedCheck_4465_;
goto v_resetjp_4459_;
}
v_resetjp_4459_:
{
lean_object* v___x_4463_; 
if (v_isShared_4461_ == 0)
{
v___x_4463_ = v___x_4460_;
goto v_reusejp_4462_;
}
else
{
lean_object* v_reuseFailAlloc_4464_; 
v_reuseFailAlloc_4464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4464_, 0, v_a_4458_);
v___x_4463_ = v_reuseFailAlloc_4464_;
goto v_reusejp_4462_;
}
v_reusejp_4462_:
{
return v___x_4463_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_erase___boxed(lean_object* v_declName_4466_, lean_object* v_attrName_4467_, lean_object* v_a_4468_, lean_object* v_a_4469_, lean_object* v_a_4470_){
_start:
{
lean_object* v_res_4471_; 
v_res_4471_ = l_Lean_Attribute_erase(v_declName_4466_, v_attrName_4467_, v_a_4468_, v_a_4469_);
lean_dec(v_a_4469_);
lean_dec_ref(v_a_4468_);
return v_res_4471_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_updateEnvAttributesImpl_spec__0(lean_object* v_x_4472_, lean_object* v_x_4473_){
_start:
{
if (lean_obj_tag(v_x_4473_) == 0)
{
return v_x_4472_;
}
else
{
lean_object* v_key_4474_; lean_object* v_value_4475_; lean_object* v_tail_4476_; lean_object* v_newEntries_4477_; lean_object* v_map_4478_; uint8_t v___x_4479_; 
v_key_4474_ = lean_ctor_get(v_x_4473_, 0);
lean_inc(v_key_4474_);
v_value_4475_ = lean_ctor_get(v_x_4473_, 1);
lean_inc(v_value_4475_);
v_tail_4476_ = lean_ctor_get(v_x_4473_, 2);
lean_inc(v_tail_4476_);
lean_dec_ref_known(v_x_4473_, 3);
v_newEntries_4477_ = lean_ctor_get(v_x_4472_, 0);
v_map_4478_ = lean_ctor_get(v_x_4472_, 1);
v___x_4479_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(v_map_4478_, v_key_4474_);
if (v___x_4479_ == 0)
{
lean_object* v___x_4481_; uint8_t v_isShared_4482_; uint8_t v_isSharedCheck_4488_; 
lean_inc_ref(v_map_4478_);
lean_inc(v_newEntries_4477_);
v_isSharedCheck_4488_ = !lean_is_exclusive(v_x_4472_);
if (v_isSharedCheck_4488_ == 0)
{
lean_object* v_unused_4489_; lean_object* v_unused_4490_; 
v_unused_4489_ = lean_ctor_get(v_x_4472_, 1);
lean_dec(v_unused_4489_);
v_unused_4490_ = lean_ctor_get(v_x_4472_, 0);
lean_dec(v_unused_4490_);
v___x_4481_ = v_x_4472_;
v_isShared_4482_ = v_isSharedCheck_4488_;
goto v_resetjp_4480_;
}
else
{
lean_dec(v_x_4472_);
v___x_4481_ = lean_box(0);
v_isShared_4482_ = v_isSharedCheck_4488_;
goto v_resetjp_4480_;
}
v_resetjp_4480_:
{
lean_object* v___x_4483_; lean_object* v___x_4485_; 
v___x_4483_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1___redArg(v_map_4478_, v_key_4474_, v_value_4475_);
if (v_isShared_4482_ == 0)
{
lean_ctor_set(v___x_4481_, 1, v___x_4483_);
v___x_4485_ = v___x_4481_;
goto v_reusejp_4484_;
}
else
{
lean_object* v_reuseFailAlloc_4487_; 
v_reuseFailAlloc_4487_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4487_, 0, v_newEntries_4477_);
lean_ctor_set(v_reuseFailAlloc_4487_, 1, v___x_4483_);
v___x_4485_ = v_reuseFailAlloc_4487_;
goto v_reusejp_4484_;
}
v_reusejp_4484_:
{
v_x_4472_ = v___x_4485_;
v_x_4473_ = v_tail_4476_;
goto _start;
}
}
}
else
{
lean_dec(v_value_4475_);
lean_dec(v_key_4474_);
v_x_4473_ = v_tail_4476_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_updateEnvAttributesImpl_spec__1(lean_object* v_as_4492_, size_t v_i_4493_, size_t v_stop_4494_, lean_object* v_b_4495_){
_start:
{
uint8_t v___x_4496_; 
v___x_4496_ = lean_usize_dec_eq(v_i_4493_, v_stop_4494_);
if (v___x_4496_ == 0)
{
lean_object* v___x_4497_; lean_object* v___x_4498_; size_t v___x_4499_; size_t v___x_4500_; 
v___x_4497_ = lean_array_uget_borrowed(v_as_4492_, v_i_4493_);
lean_inc(v___x_4497_);
v___x_4498_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_updateEnvAttributesImpl_spec__0(v_b_4495_, v___x_4497_);
v___x_4499_ = ((size_t)1ULL);
v___x_4500_ = lean_usize_add(v_i_4493_, v___x_4499_);
v_i_4493_ = v___x_4500_;
v_b_4495_ = v___x_4498_;
goto _start;
}
else
{
return v_b_4495_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_updateEnvAttributesImpl_spec__1___boxed(lean_object* v_as_4502_, lean_object* v_i_4503_, lean_object* v_stop_4504_, lean_object* v_b_4505_){
_start:
{
size_t v_i_boxed_4506_; size_t v_stop_boxed_4507_; lean_object* v_res_4508_; 
v_i_boxed_4506_ = lean_unbox_usize(v_i_4503_);
lean_dec(v_i_4503_);
v_stop_boxed_4507_ = lean_unbox_usize(v_stop_4504_);
lean_dec(v_stop_4504_);
v_res_4508_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_updateEnvAttributesImpl_spec__1(v_as_4502_, v_i_boxed_4506_, v_stop_boxed_4507_, v_b_4505_);
lean_dec_ref(v_as_4502_);
return v_res_4508_;
}
}
LEAN_EXPORT lean_object* lean_update_env_attributes(lean_object* v_env_4509_){
_start:
{
lean_object* v___x_4511_; lean_object* v___x_4512_; lean_object* v___x_4513_; lean_object* v___x_4514_; lean_object* v___y_4516_; lean_object* v_toEnvExtension_4519_; lean_object* v_asyncMode_4520_; lean_object* v_buckets_4521_; lean_object* v___x_4522_; lean_object* v___x_4523_; lean_object* v___x_4524_; lean_object* v___x_4525_; uint8_t v___x_4526_; 
v___x_4511_ = l_Lean_instInhabitedAttributeExtensionState_default;
v___x_4512_ = l_Lean_attributeMapRef;
v___x_4513_ = lean_st_ref_get(v___x_4512_);
v___x_4514_ = l_Lean_attributeExtension;
v_toEnvExtension_4519_ = lean_ctor_get(v___x_4514_, 0);
v_asyncMode_4520_ = lean_ctor_get(v_toEnvExtension_4519_, 2);
v_buckets_4521_ = lean_ctor_get(v___x_4513_, 1);
lean_inc_ref(v_buckets_4521_);
lean_dec(v___x_4513_);
v___x_4522_ = lean_box(0);
lean_inc_ref(v_env_4509_);
v___x_4523_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_4511_, v___x_4514_, v_env_4509_, v_asyncMode_4520_, v___x_4522_);
v___x_4524_ = lean_unsigned_to_nat(0u);
v___x_4525_ = lean_array_get_size(v_buckets_4521_);
v___x_4526_ = lean_nat_dec_lt(v___x_4524_, v___x_4525_);
if (v___x_4526_ == 0)
{
lean_dec_ref(v_buckets_4521_);
v___y_4516_ = v___x_4523_;
goto v___jp_4515_;
}
else
{
size_t v___x_4527_; size_t v___x_4528_; lean_object* v___x_4529_; 
v___x_4527_ = ((size_t)0ULL);
v___x_4528_ = lean_usize_of_nat(v___x_4525_);
v___x_4529_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_updateEnvAttributesImpl_spec__1(v_buckets_4521_, v___x_4527_, v___x_4528_, v___x_4523_);
lean_dec_ref(v_buckets_4521_);
v___y_4516_ = v___x_4529_;
goto v___jp_4515_;
}
v___jp_4515_:
{
lean_object* v___x_4517_; lean_object* v___x_4518_; 
v___x_4517_ = l_Lean_PersistentEnvExtension_setState___redArg(v___x_4514_, v_env_4509_, v___y_4516_);
v___x_4518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4518_, 0, v___x_4517_);
return v___x_4518_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_updateEnvAttributesImpl___boxed(lean_object* v_env_4530_, lean_object* v_a_4531_){
_start:
{
lean_object* v_res_4532_; 
v_res_4532_ = lean_update_env_attributes(v_env_4530_);
return v_res_4532_;
}
}
LEAN_EXPORT lean_object* lean_get_num_attributes(){
_start:
{
lean_object* v___x_4534_; lean_object* v___x_4535_; lean_object* v_size_4536_; lean_object* v___x_4537_; 
v___x_4534_ = l_Lean_attributeMapRef;
v___x_4535_ = lean_st_ref_get(v___x_4534_);
v_size_4536_ = lean_ctor_get(v___x_4535_, 0);
lean_inc(v_size_4536_);
lean_dec(v___x_4535_);
v___x_4537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4537_, 0, v_size_4536_);
return v___x_4537_;
}
}
LEAN_EXPORT lean_object* l_Lean_getNumBuiltinAttributesImpl___boxed(lean_object* v_a_4538_){
_start:
{
lean_object* v_res_4539_; 
v_res_4539_ = lean_get_num_attributes();
return v_res_4539_;
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
