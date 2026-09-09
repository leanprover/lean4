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
LEAN_EXPORT uint8_t l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_TagAttribute_hasTag(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TagAttribute_hasTag___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v___x_82_; lean_object* v_toCold_83_; lean_object* v_env_84_; lean_object* v_ref_85_; lean_object* v_options_86_; lean_object* v___x_87_; lean_object* v___x_88_; 
v___x_82_ = lean_st_ref_get(v___y_80_);
v_toCold_83_ = lean_ctor_get(v___y_79_, 0);
v_env_84_ = lean_ctor_get(v___x_82_, 0);
lean_inc_ref(v_env_84_);
lean_dec(v___x_82_);
v_ref_85_ = lean_ctor_get(v___y_79_, 2);
v_options_86_ = lean_ctor_get(v_toCold_83_, 2);
lean_inc_ref(v_options_86_);
v___x_87_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_87_, 0, v_env_84_);
lean_ctor_set(v___x_87_, 1, v_options_86_);
v___x_88_ = lean_apply_2(v_x_78_, v___x_87_, lean_box(0));
if (lean_obj_tag(v___x_88_) == 0)
{
lean_object* v_a_89_; lean_object* v___x_91_; uint8_t v_isShared_92_; uint8_t v_isSharedCheck_96_; 
v_a_89_ = lean_ctor_get(v___x_88_, 0);
v_isSharedCheck_96_ = !lean_is_exclusive(v___x_88_);
if (v_isSharedCheck_96_ == 0)
{
v___x_91_ = v___x_88_;
v_isShared_92_ = v_isSharedCheck_96_;
goto v_resetjp_90_;
}
else
{
lean_inc(v_a_89_);
lean_dec(v___x_88_);
v___x_91_ = lean_box(0);
v_isShared_92_ = v_isSharedCheck_96_;
goto v_resetjp_90_;
}
v_resetjp_90_:
{
lean_object* v___x_94_; 
if (v_isShared_92_ == 0)
{
v___x_94_ = v___x_91_;
goto v_reusejp_93_;
}
else
{
lean_object* v_reuseFailAlloc_95_; 
v_reuseFailAlloc_95_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_95_, 0, v_a_89_);
v___x_94_ = v_reuseFailAlloc_95_;
goto v_reusejp_93_;
}
v_reusejp_93_:
{
return v___x_94_;
}
}
}
else
{
lean_object* v_a_97_; lean_object* v___x_99_; uint8_t v_isShared_100_; uint8_t v_isSharedCheck_108_; 
v_a_97_ = lean_ctor_get(v___x_88_, 0);
v_isSharedCheck_108_ = !lean_is_exclusive(v___x_88_);
if (v_isSharedCheck_108_ == 0)
{
v___x_99_ = v___x_88_;
v_isShared_100_ = v_isSharedCheck_108_;
goto v_resetjp_98_;
}
else
{
lean_inc(v_a_97_);
lean_dec(v___x_88_);
v___x_99_ = lean_box(0);
v_isShared_100_ = v_isSharedCheck_108_;
goto v_resetjp_98_;
}
v_resetjp_98_:
{
lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_106_; 
v___x_101_ = lean_io_error_to_string(v_a_97_);
v___x_102_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_102_, 0, v___x_101_);
v___x_103_ = l_Lean_MessageData_ofFormat(v___x_102_);
lean_inc(v_ref_85_);
v___x_104_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_104_, 0, v_ref_85_);
lean_ctor_set(v___x_104_, 1, v___x_103_);
if (v_isShared_100_ == 0)
{
lean_ctor_set(v___x_99_, 0, v___x_104_);
v___x_106_ = v___x_99_;
goto v_reusejp_105_;
}
else
{
lean_object* v_reuseFailAlloc_107_; 
v_reuseFailAlloc_107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_107_, 0, v___x_104_);
v___x_106_ = v_reuseFailAlloc_107_;
goto v_reusejp_105_;
}
v_reusejp_105_:
{
return v___x_106_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadLiftImportMAttrM___lam__0___boxed(lean_object* v_00_u03b1_109_, lean_object* v_x_110_, lean_object* v___y_111_, lean_object* v___y_112_, lean_object* v___y_113_){
_start:
{
lean_object* v_res_114_; 
v_res_114_ = l_Lean_instMonadLiftImportMAttrM___lam__0(v_00_u03b1_109_, v_x_110_, v___y_111_, v___y_112_);
lean_dec(v___y_112_);
lean_dec_ref(v___y_111_);
return v_res_114_;
}
}
static lean_object* _init_l_Lean_AttributeImplCore_ref___autoParam___closed__12(void){
_start:
{
lean_object* v___x_143_; lean_object* v___x_144_; 
v___x_143_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__10));
v___x_144_ = l_Lean_mkAtom(v___x_143_);
return v___x_144_;
}
}
static lean_object* _init_l_Lean_AttributeImplCore_ref___autoParam___closed__13(void){
_start:
{
lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; 
v___x_145_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__12, &l_Lean_AttributeImplCore_ref___autoParam___closed__12_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__12);
v___x_146_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__5));
v___x_147_ = lean_array_push(v___x_146_, v___x_145_);
return v___x_147_;
}
}
static lean_object* _init_l_Lean_AttributeImplCore_ref___autoParam___closed__18(void){
_start:
{
lean_object* v___x_156_; lean_object* v___x_157_; 
v___x_156_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__17));
v___x_157_ = l_Lean_mkAtom(v___x_156_);
return v___x_157_;
}
}
static lean_object* _init_l_Lean_AttributeImplCore_ref___autoParam___closed__19(void){
_start:
{
lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; 
v___x_158_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__18, &l_Lean_AttributeImplCore_ref___autoParam___closed__18_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__18);
v___x_159_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__5));
v___x_160_ = lean_array_push(v___x_159_, v___x_158_);
return v___x_160_;
}
}
static lean_object* _init_l_Lean_AttributeImplCore_ref___autoParam___closed__20(void){
_start:
{
lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; 
v___x_161_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__19, &l_Lean_AttributeImplCore_ref___autoParam___closed__19_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__19);
v___x_162_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__16));
v___x_163_ = lean_box(2);
v___x_164_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_164_, 0, v___x_163_);
lean_ctor_set(v___x_164_, 1, v___x_162_);
lean_ctor_set(v___x_164_, 2, v___x_161_);
return v___x_164_;
}
}
static lean_object* _init_l_Lean_AttributeImplCore_ref___autoParam___closed__21(void){
_start:
{
lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; 
v___x_165_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__20, &l_Lean_AttributeImplCore_ref___autoParam___closed__20_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__20);
v___x_166_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__13, &l_Lean_AttributeImplCore_ref___autoParam___closed__13_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__13);
v___x_167_ = lean_array_push(v___x_166_, v___x_165_);
return v___x_167_;
}
}
static lean_object* _init_l_Lean_AttributeImplCore_ref___autoParam___closed__22(void){
_start:
{
lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; 
v___x_168_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__21, &l_Lean_AttributeImplCore_ref___autoParam___closed__21_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__21);
v___x_169_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__11));
v___x_170_ = lean_box(2);
v___x_171_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_171_, 0, v___x_170_);
lean_ctor_set(v___x_171_, 1, v___x_169_);
lean_ctor_set(v___x_171_, 2, v___x_168_);
return v___x_171_;
}
}
static lean_object* _init_l_Lean_AttributeImplCore_ref___autoParam___closed__23(void){
_start:
{
lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; 
v___x_172_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__22, &l_Lean_AttributeImplCore_ref___autoParam___closed__22_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__22);
v___x_173_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__5));
v___x_174_ = lean_array_push(v___x_173_, v___x_172_);
return v___x_174_;
}
}
static lean_object* _init_l_Lean_AttributeImplCore_ref___autoParam___closed__24(void){
_start:
{
lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; 
v___x_175_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__23, &l_Lean_AttributeImplCore_ref___autoParam___closed__23_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__23);
v___x_176_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__9));
v___x_177_ = lean_box(2);
v___x_178_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_178_, 0, v___x_177_);
lean_ctor_set(v___x_178_, 1, v___x_176_);
lean_ctor_set(v___x_178_, 2, v___x_175_);
return v___x_178_;
}
}
static lean_object* _init_l_Lean_AttributeImplCore_ref___autoParam___closed__25(void){
_start:
{
lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; 
v___x_179_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__24, &l_Lean_AttributeImplCore_ref___autoParam___closed__24_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__24);
v___x_180_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__5));
v___x_181_ = lean_array_push(v___x_180_, v___x_179_);
return v___x_181_;
}
}
static lean_object* _init_l_Lean_AttributeImplCore_ref___autoParam___closed__26(void){
_start:
{
lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; 
v___x_182_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__25, &l_Lean_AttributeImplCore_ref___autoParam___closed__25_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__25);
v___x_183_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__7));
v___x_184_ = lean_box(2);
v___x_185_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_185_, 0, v___x_184_);
lean_ctor_set(v___x_185_, 1, v___x_183_);
lean_ctor_set(v___x_185_, 2, v___x_182_);
return v___x_185_;
}
}
static lean_object* _init_l_Lean_AttributeImplCore_ref___autoParam___closed__27(void){
_start:
{
lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; 
v___x_186_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__26, &l_Lean_AttributeImplCore_ref___autoParam___closed__26_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__26);
v___x_187_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__5));
v___x_188_ = lean_array_push(v___x_187_, v___x_186_);
return v___x_188_;
}
}
static lean_object* _init_l_Lean_AttributeImplCore_ref___autoParam___closed__28(void){
_start:
{
lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; 
v___x_189_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__27, &l_Lean_AttributeImplCore_ref___autoParam___closed__27_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__27);
v___x_190_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__4));
v___x_191_ = lean_box(2);
v___x_192_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_192_, 0, v___x_191_);
lean_ctor_set(v___x_192_, 1, v___x_190_);
lean_ctor_set(v___x_192_, 2, v___x_189_);
return v___x_192_;
}
}
static lean_object* _init_l_Lean_AttributeImplCore_ref___autoParam(void){
_start:
{
lean_object* v___x_193_; 
v___x_193_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__28, &l_Lean_AttributeImplCore_ref___autoParam___closed__28_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__28);
return v___x_193_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_ctorIdx(uint8_t v_x_208_){
_start:
{
switch(v_x_208_)
{
case 0:
{
lean_object* v___x_209_; 
v___x_209_ = lean_unsigned_to_nat(0u);
return v___x_209_;
}
case 1:
{
lean_object* v___x_210_; 
v___x_210_ = lean_unsigned_to_nat(1u);
return v___x_210_;
}
default: 
{
lean_object* v___x_211_; 
v___x_211_ = lean_unsigned_to_nat(2u);
return v___x_211_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_ctorIdx___boxed(lean_object* v_x_212_){
_start:
{
uint8_t v_x_boxed_213_; lean_object* v_res_214_; 
v_x_boxed_213_ = lean_unbox(v_x_212_);
v_res_214_ = l_Lean_AttributeKind_ctorIdx(v_x_boxed_213_);
return v_res_214_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_ctorElim___redArg(lean_object* v_k_215_){
_start:
{
lean_inc(v_k_215_);
return v_k_215_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_ctorElim___redArg___boxed(lean_object* v_k_216_){
_start:
{
lean_object* v_res_217_; 
v_res_217_ = l_Lean_AttributeKind_ctorElim___redArg(v_k_216_);
lean_dec(v_k_216_);
return v_res_217_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_ctorElim(lean_object* v_motive_218_, lean_object* v_ctorIdx_219_, uint8_t v_t_220_, lean_object* v_h_221_, lean_object* v_k_222_){
_start:
{
lean_inc(v_k_222_);
return v_k_222_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_ctorElim___boxed(lean_object* v_motive_223_, lean_object* v_ctorIdx_224_, lean_object* v_t_225_, lean_object* v_h_226_, lean_object* v_k_227_){
_start:
{
uint8_t v_t_boxed_228_; lean_object* v_res_229_; 
v_t_boxed_228_ = lean_unbox(v_t_225_);
v_res_229_ = l_Lean_AttributeKind_ctorElim(v_motive_223_, v_ctorIdx_224_, v_t_boxed_228_, v_h_226_, v_k_227_);
lean_dec(v_k_227_);
lean_dec(v_ctorIdx_224_);
return v_res_229_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_global_elim___redArg(lean_object* v_global_230_){
_start:
{
lean_inc(v_global_230_);
return v_global_230_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_global_elim___redArg___boxed(lean_object* v_global_231_){
_start:
{
lean_object* v_res_232_; 
v_res_232_ = l_Lean_AttributeKind_global_elim___redArg(v_global_231_);
lean_dec(v_global_231_);
return v_res_232_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_global_elim(lean_object* v_motive_233_, uint8_t v_t_234_, lean_object* v_h_235_, lean_object* v_global_236_){
_start:
{
lean_inc(v_global_236_);
return v_global_236_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_global_elim___boxed(lean_object* v_motive_237_, lean_object* v_t_238_, lean_object* v_h_239_, lean_object* v_global_240_){
_start:
{
uint8_t v_t_boxed_241_; lean_object* v_res_242_; 
v_t_boxed_241_ = lean_unbox(v_t_238_);
v_res_242_ = l_Lean_AttributeKind_global_elim(v_motive_237_, v_t_boxed_241_, v_h_239_, v_global_240_);
lean_dec(v_global_240_);
return v_res_242_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_local_elim___redArg(lean_object* v_local_243_){
_start:
{
lean_inc(v_local_243_);
return v_local_243_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_local_elim___redArg___boxed(lean_object* v_local_244_){
_start:
{
lean_object* v_res_245_; 
v_res_245_ = l_Lean_AttributeKind_local_elim___redArg(v_local_244_);
lean_dec(v_local_244_);
return v_res_245_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_local_elim(lean_object* v_motive_246_, uint8_t v_t_247_, lean_object* v_h_248_, lean_object* v_local_249_){
_start:
{
lean_inc(v_local_249_);
return v_local_249_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_local_elim___boxed(lean_object* v_motive_250_, lean_object* v_t_251_, lean_object* v_h_252_, lean_object* v_local_253_){
_start:
{
uint8_t v_t_boxed_254_; lean_object* v_res_255_; 
v_t_boxed_254_ = lean_unbox(v_t_251_);
v_res_255_ = l_Lean_AttributeKind_local_elim(v_motive_250_, v_t_boxed_254_, v_h_252_, v_local_253_);
lean_dec(v_local_253_);
return v_res_255_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_scoped_elim___redArg(lean_object* v_scoped_256_){
_start:
{
lean_inc(v_scoped_256_);
return v_scoped_256_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_scoped_elim___redArg___boxed(lean_object* v_scoped_257_){
_start:
{
lean_object* v_res_258_; 
v_res_258_ = l_Lean_AttributeKind_scoped_elim___redArg(v_scoped_257_);
lean_dec(v_scoped_257_);
return v_res_258_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_scoped_elim(lean_object* v_motive_259_, uint8_t v_t_260_, lean_object* v_h_261_, lean_object* v_scoped_262_){
_start:
{
lean_inc(v_scoped_262_);
return v_scoped_262_;
}
}
LEAN_EXPORT lean_object* l_Lean_AttributeKind_scoped_elim___boxed(lean_object* v_motive_263_, lean_object* v_t_264_, lean_object* v_h_265_, lean_object* v_scoped_266_){
_start:
{
uint8_t v_t_boxed_267_; lean_object* v_res_268_; 
v_t_boxed_267_ = lean_unbox(v_t_264_);
v_res_268_ = l_Lean_AttributeKind_scoped_elim(v_motive_263_, v_t_boxed_267_, v_h_265_, v_scoped_266_);
lean_dec(v_scoped_266_);
return v_res_268_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqAttributeKind_beq(uint8_t v_x_269_, uint8_t v_y_270_){
_start:
{
lean_object* v___x_271_; lean_object* v___x_272_; uint8_t v___x_273_; 
v___x_271_ = l_Lean_AttributeKind_ctorIdx(v_x_269_);
v___x_272_ = l_Lean_AttributeKind_ctorIdx(v_y_270_);
v___x_273_ = lean_nat_dec_eq(v___x_271_, v___x_272_);
lean_dec(v___x_272_);
lean_dec(v___x_271_);
return v___x_273_;
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqAttributeKind_beq___boxed(lean_object* v_x_274_, lean_object* v_y_275_){
_start:
{
uint8_t v_x_21__boxed_276_; uint8_t v_y_22__boxed_277_; uint8_t v_res_278_; lean_object* v_r_279_; 
v_x_21__boxed_276_ = lean_unbox(v_x_274_);
v_y_22__boxed_277_ = lean_unbox(v_y_275_);
v_res_278_ = l_Lean_instBEqAttributeKind_beq(v_x_21__boxed_276_, v_y_22__boxed_277_);
v_r_279_ = lean_box(v_res_278_);
return v_r_279_;
}
}
static uint8_t _init_l_Lean_instInhabitedAttributeKind_default(void){
_start:
{
uint8_t v___x_282_; 
v___x_282_ = 0;
return v___x_282_;
}
}
static uint8_t _init_l_Lean_instInhabitedAttributeKind(void){
_start:
{
uint8_t v___x_283_; 
v___x_283_ = 0;
return v___x_283_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToStringAttributeKind___lam__0(uint8_t v_x_287_){
_start:
{
switch(v_x_287_)
{
case 0:
{
lean_object* v___x_288_; 
v___x_288_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__0));
return v___x_288_;
}
case 1:
{
lean_object* v___x_289_; 
v___x_289_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__1));
return v___x_289_;
}
default: 
{
lean_object* v___x_290_; 
v___x_290_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__2));
return v___x_290_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToStringAttributeKind___lam__0___boxed(lean_object* v_x_291_){
_start:
{
uint8_t v_x_36__boxed_292_; lean_object* v_res_293_; 
v_x_36__boxed_292_ = lean_unbox(v_x_291_);
v_res_293_ = l_Lean_instToStringAttributeKind___lam__0(v_x_36__boxed_292_);
return v_res_293_;
}
}
static lean_object* _init_l_Lean_instInhabitedAttributeImpl_default___lam__0___closed__0(void){
_start:
{
lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; 
v___x_296_ = l_Lean_instInhabitedMessageData_default;
v___x_297_ = lean_box(0);
v___x_298_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_298_, 0, v___x_297_);
lean_ctor_set(v___x_298_, 1, v___x_296_);
return v___x_298_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedAttributeImpl_default___lam__0(lean_object* v_x_299_, lean_object* v___y_300_, uint8_t v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_){
_start:
{
lean_object* v___x_305_; lean_object* v___x_306_; 
v___x_305_ = lean_obj_once(&l_Lean_instInhabitedAttributeImpl_default___lam__0___closed__0, &l_Lean_instInhabitedAttributeImpl_default___lam__0___closed__0_once, _init_l_Lean_instInhabitedAttributeImpl_default___lam__0___closed__0);
v___x_306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_306_, 0, v___x_305_);
return v___x_306_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedAttributeImpl_default___lam__0___boxed(lean_object* v_x_307_, lean_object* v___y_308_, lean_object* v___y_309_, lean_object* v___y_310_, lean_object* v___y_311_, lean_object* v___y_312_){
_start:
{
uint8_t v___y_1006__boxed_313_; lean_object* v_res_314_; 
v___y_1006__boxed_313_ = lean_unbox(v___y_309_);
v_res_314_ = l_Lean_instInhabitedAttributeImpl_default___lam__0(v_x_307_, v___y_308_, v___y_1006__boxed_313_, v___y_310_, v___y_311_);
lean_dec(v___y_311_);
lean_dec_ref(v___y_310_);
lean_dec(v___y_308_);
lean_dec(v_x_307_);
return v_res_314_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_315_; 
v___x_315_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_315_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_316_; lean_object* v___x_317_; 
v___x_316_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__0);
v___x_317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_317_, 0, v___x_316_);
return v___x_317_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; 
v___x_318_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__1);
v___x_319_ = lean_unsigned_to_nat(0u);
v___x_320_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_320_, 0, v___x_319_);
lean_ctor_set(v___x_320_, 1, v___x_319_);
lean_ctor_set(v___x_320_, 2, v___x_319_);
lean_ctor_set(v___x_320_, 3, v___x_319_);
lean_ctor_set(v___x_320_, 4, v___x_318_);
lean_ctor_set(v___x_320_, 5, v___x_318_);
lean_ctor_set(v___x_320_, 6, v___x_318_);
lean_ctor_set(v___x_320_, 7, v___x_318_);
lean_ctor_set(v___x_320_, 8, v___x_318_);
lean_ctor_set(v___x_320_, 9, v___x_318_);
lean_ctor_set(v___x_320_, 10, v___x_318_);
return v___x_320_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; 
v___x_321_ = lean_unsigned_to_nat(32u);
v___x_322_ = lean_mk_empty_array_with_capacity(v___x_321_);
v___x_323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_323_, 0, v___x_322_);
return v___x_323_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__4(void){
_start:
{
size_t v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; 
v___x_324_ = ((size_t)5ULL);
v___x_325_ = lean_unsigned_to_nat(0u);
v___x_326_ = lean_unsigned_to_nat(32u);
v___x_327_ = lean_mk_empty_array_with_capacity(v___x_326_);
v___x_328_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__3);
v___x_329_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_329_, 0, v___x_328_);
lean_ctor_set(v___x_329_, 1, v___x_327_);
lean_ctor_set(v___x_329_, 2, v___x_325_);
lean_ctor_set(v___x_329_, 3, v___x_325_);
lean_ctor_set_usize(v___x_329_, 4, v___x_324_);
return v___x_329_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; 
v___x_330_ = lean_box(1);
v___x_331_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__4);
v___x_332_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__1);
v___x_333_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_333_, 0, v___x_332_);
lean_ctor_set(v___x_333_, 1, v___x_331_);
lean_ctor_set(v___x_333_, 2, v___x_330_);
return v___x_333_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0(lean_object* v_msgData_334_, lean_object* v___y_335_, lean_object* v___y_336_){
_start:
{
lean_object* v___x_338_; lean_object* v_toCold_339_; lean_object* v_env_340_; lean_object* v_options_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; 
v___x_338_ = lean_st_ref_get(v___y_336_);
v_toCold_339_ = lean_ctor_get(v___y_335_, 0);
v_env_340_ = lean_ctor_get(v___x_338_, 0);
lean_inc_ref(v_env_340_);
lean_dec(v___x_338_);
v_options_341_ = lean_ctor_get(v_toCold_339_, 2);
v___x_342_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__2);
v___x_343_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___closed__5);
lean_inc_ref(v_options_341_);
v___x_344_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_344_, 0, v_env_340_);
lean_ctor_set(v___x_344_, 1, v___x_342_);
lean_ctor_set(v___x_344_, 2, v___x_343_);
lean_ctor_set(v___x_344_, 3, v_options_341_);
v___x_345_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_345_, 0, v___x_344_);
lean_ctor_set(v___x_345_, 1, v_msgData_334_);
v___x_346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_346_, 0, v___x_345_);
return v___x_346_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0___boxed(lean_object* v_msgData_347_, lean_object* v___y_348_, lean_object* v___y_349_, lean_object* v___y_350_){
_start:
{
lean_object* v_res_351_; 
v_res_351_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0(v_msgData_347_, v___y_348_, v___y_349_);
lean_dec(v___y_349_);
lean_dec_ref(v___y_348_);
return v_res_351_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(lean_object* v_msg_352_, lean_object* v___y_353_, lean_object* v___y_354_){
_start:
{
lean_object* v_ref_356_; lean_object* v___x_357_; lean_object* v_a_358_; lean_object* v___x_360_; uint8_t v_isShared_361_; uint8_t v_isSharedCheck_366_; 
v_ref_356_ = lean_ctor_get(v___y_353_, 2);
v___x_357_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0(v_msg_352_, v___y_353_, v___y_354_);
v_a_358_ = lean_ctor_get(v___x_357_, 0);
v_isSharedCheck_366_ = !lean_is_exclusive(v___x_357_);
if (v_isSharedCheck_366_ == 0)
{
v___x_360_ = v___x_357_;
v_isShared_361_ = v_isSharedCheck_366_;
goto v_resetjp_359_;
}
else
{
lean_inc(v_a_358_);
lean_dec(v___x_357_);
v___x_360_ = lean_box(0);
v_isShared_361_ = v_isSharedCheck_366_;
goto v_resetjp_359_;
}
v_resetjp_359_:
{
lean_object* v___x_362_; lean_object* v___x_364_; 
lean_inc(v_ref_356_);
v___x_362_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_362_, 0, v_ref_356_);
lean_ctor_set(v___x_362_, 1, v_a_358_);
if (v_isShared_361_ == 0)
{
lean_ctor_set_tag(v___x_360_, 1);
lean_ctor_set(v___x_360_, 0, v___x_362_);
v___x_364_ = v___x_360_;
goto v_reusejp_363_;
}
else
{
lean_object* v_reuseFailAlloc_365_; 
v_reuseFailAlloc_365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_365_, 0, v___x_362_);
v___x_364_ = v_reuseFailAlloc_365_;
goto v_reusejp_363_;
}
v_reusejp_363_:
{
return v___x_364_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg___boxed(lean_object* v_msg_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_){
_start:
{
lean_object* v_res_371_; 
v_res_371_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v_msg_367_, v___y_368_, v___y_369_);
lean_dec(v___y_369_);
lean_dec_ref(v___y_368_);
return v_res_371_;
}
}
static lean_object* _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1(void){
_start:
{
lean_object* v___x_373_; lean_object* v___x_374_; 
v___x_373_ = ((lean_object*)(l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__0));
v___x_374_ = l_Lean_stringToMessageData(v___x_373_);
return v___x_374_;
}
}
static lean_object* _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3(void){
_start:
{
lean_object* v___x_376_; lean_object* v___x_377_; 
v___x_376_ = ((lean_object*)(l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__2));
v___x_377_ = l_Lean_stringToMessageData(v___x_376_);
return v___x_377_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedAttributeImpl_default___lam__1(lean_object* v___x_378_, lean_object* v_decl_379_, lean_object* v___y_380_, lean_object* v___y_381_){
_start:
{
lean_object* v_name_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; 
v_name_383_ = lean_ctor_get(v___x_378_, 1);
lean_inc(v_name_383_);
lean_dec_ref(v___x_378_);
v___x_384_ = lean_obj_once(&l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1, &l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1_once, _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1);
v___x_385_ = l_Lean_MessageData_ofName(v_name_383_);
v___x_386_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_386_, 0, v___x_384_);
lean_ctor_set(v___x_386_, 1, v___x_385_);
v___x_387_ = lean_obj_once(&l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3, &l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3_once, _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3);
v___x_388_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_388_, 0, v___x_386_);
lean_ctor_set(v___x_388_, 1, v___x_387_);
v___x_389_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_388_, v___y_380_, v___y_381_);
return v___x_389_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedAttributeImpl_default___lam__1___boxed(lean_object* v___x_390_, lean_object* v_decl_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_){
_start:
{
lean_object* v_res_395_; 
v_res_395_ = l_Lean_instInhabitedAttributeImpl_default___lam__1(v___x_390_, v_decl_391_, v___y_392_, v___y_393_);
lean_dec(v___y_393_);
lean_dec_ref(v___y_392_);
lean_dec(v_decl_391_);
return v_res_395_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0(lean_object* v_00_u03b1_404_, lean_object* v_msg_405_, lean_object* v___y_406_, lean_object* v___y_407_){
_start:
{
lean_object* v___x_409_; 
v___x_409_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v_msg_405_, v___y_406_, v___y_407_);
return v___x_409_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___boxed(lean_object* v_00_u03b1_410_, lean_object* v_msg_411_, lean_object* v___y_412_, lean_object* v___y_413_, lean_object* v___y_414_){
_start:
{
lean_object* v_res_415_; 
v_res_415_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0(v_00_u03b1_410_, v_msg_411_, v___y_412_, v___y_413_);
lean_dec(v___y_413_);
lean_dec_ref(v___y_412_);
return v_res_415_;
}
}
static lean_object* _init_l___private_Lean_Attributes_0__Lean_initFn___closed__0_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; 
v___x_417_ = lean_box(0);
v___x_418_ = lean_unsigned_to_nat(16u);
v___x_419_ = lean_mk_array(v___x_418_, v___x_417_);
return v___x_419_;
}
}
static lean_object* _init_l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; 
v___x_420_ = lean_obj_once(&l___private_Lean_Attributes_0__Lean_initFn___closed__0_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_, &l___private_Lean_Attributes_0__Lean_initFn___closed__0_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2__once, _init_l___private_Lean_Attributes_0__Lean_initFn___closed__0_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_);
v___x_421_ = lean_unsigned_to_nat(0u);
v___x_422_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_422_, 0, v___x_421_);
lean_ctor_set(v___x_422_, 1, v___x_420_);
return v___x_422_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; 
v___x_424_ = lean_obj_once(&l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_, &l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2__once, _init_l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_);
v___x_425_ = lean_st_mk_ref(v___x_424_);
v___x_426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_426_, 0, v___x_425_);
return v___x_426_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2____boxed(lean_object* v_a_427_){
_start:
{
lean_object* v_res_428_; 
v_res_428_ = l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_();
return v_res_428_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0_spec__0___redArg(lean_object* v_a_429_, lean_object* v_x_430_){
_start:
{
if (lean_obj_tag(v_x_430_) == 0)
{
uint8_t v___x_431_; 
v___x_431_ = 0;
return v___x_431_;
}
else
{
lean_object* v_key_432_; lean_object* v_tail_433_; uint8_t v___x_434_; 
v_key_432_ = lean_ctor_get(v_x_430_, 0);
v_tail_433_ = lean_ctor_get(v_x_430_, 2);
v___x_434_ = lean_name_eq(v_key_432_, v_a_429_);
if (v___x_434_ == 0)
{
v_x_430_ = v_tail_433_;
goto _start;
}
else
{
return v___x_434_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0_spec__0___redArg___boxed(lean_object* v_a_436_, lean_object* v_x_437_){
_start:
{
uint8_t v_res_438_; lean_object* v_r_439_; 
v_res_438_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0_spec__0___redArg(v_a_436_, v_x_437_);
lean_dec(v_x_437_);
lean_dec(v_a_436_);
v_r_439_ = lean_box(v_res_438_);
return v_r_439_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(lean_object* v_m_440_, lean_object* v_a_441_){
_start:
{
lean_object* v_buckets_442_; lean_object* v___x_443_; uint64_t v___y_445_; 
v_buckets_442_ = lean_ctor_get(v_m_440_, 1);
v___x_443_ = lean_array_get_size(v_buckets_442_);
if (lean_obj_tag(v_a_441_) == 0)
{
uint64_t v___x_459_; 
v___x_459_ = 1723ULL;
v___y_445_ = v___x_459_;
goto v___jp_444_;
}
else
{
uint64_t v_hash_460_; 
v_hash_460_ = lean_ctor_get_uint64(v_a_441_, sizeof(void*)*2);
v___y_445_ = v_hash_460_;
goto v___jp_444_;
}
v___jp_444_:
{
uint64_t v___x_446_; uint64_t v___x_447_; uint64_t v_fold_448_; uint64_t v___x_449_; uint64_t v___x_450_; uint64_t v___x_451_; size_t v___x_452_; size_t v___x_453_; size_t v___x_454_; size_t v___x_455_; size_t v___x_456_; lean_object* v___x_457_; uint8_t v___x_458_; 
v___x_446_ = 32ULL;
v___x_447_ = lean_uint64_shift_right(v___y_445_, v___x_446_);
v_fold_448_ = lean_uint64_xor(v___y_445_, v___x_447_);
v___x_449_ = 16ULL;
v___x_450_ = lean_uint64_shift_right(v_fold_448_, v___x_449_);
v___x_451_ = lean_uint64_xor(v_fold_448_, v___x_450_);
v___x_452_ = lean_uint64_to_usize(v___x_451_);
v___x_453_ = lean_usize_of_nat(v___x_443_);
v___x_454_ = ((size_t)1ULL);
v___x_455_ = lean_usize_sub(v___x_453_, v___x_454_);
v___x_456_ = lean_usize_land(v___x_452_, v___x_455_);
v___x_457_ = lean_array_uget_borrowed(v_buckets_442_, v___x_456_);
v___x_458_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0_spec__0___redArg(v_a_441_, v___x_457_);
return v___x_458_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg___boxed(lean_object* v_m_461_, lean_object* v_a_462_){
_start:
{
uint8_t v_res_463_; lean_object* v_r_464_; 
v_res_463_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(v_m_461_, v_a_462_);
lean_dec(v_a_462_);
lean_dec_ref(v_m_461_);
v_r_464_ = lean_box(v_res_463_);
return v_r_464_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__3___redArg(lean_object* v_a_465_, lean_object* v_b_466_, lean_object* v_x_467_){
_start:
{
if (lean_obj_tag(v_x_467_) == 0)
{
lean_dec(v_b_466_);
lean_dec(v_a_465_);
return v_x_467_;
}
else
{
lean_object* v_key_468_; lean_object* v_value_469_; lean_object* v_tail_470_; lean_object* v___x_472_; uint8_t v_isShared_473_; uint8_t v_isSharedCheck_482_; 
v_key_468_ = lean_ctor_get(v_x_467_, 0);
v_value_469_ = lean_ctor_get(v_x_467_, 1);
v_tail_470_ = lean_ctor_get(v_x_467_, 2);
v_isSharedCheck_482_ = !lean_is_exclusive(v_x_467_);
if (v_isSharedCheck_482_ == 0)
{
v___x_472_ = v_x_467_;
v_isShared_473_ = v_isSharedCheck_482_;
goto v_resetjp_471_;
}
else
{
lean_inc(v_tail_470_);
lean_inc(v_value_469_);
lean_inc(v_key_468_);
lean_dec(v_x_467_);
v___x_472_ = lean_box(0);
v_isShared_473_ = v_isSharedCheck_482_;
goto v_resetjp_471_;
}
v_resetjp_471_:
{
uint8_t v___x_474_; 
v___x_474_ = lean_name_eq(v_key_468_, v_a_465_);
if (v___x_474_ == 0)
{
lean_object* v___x_475_; lean_object* v___x_477_; 
v___x_475_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__3___redArg(v_a_465_, v_b_466_, v_tail_470_);
if (v_isShared_473_ == 0)
{
lean_ctor_set(v___x_472_, 2, v___x_475_);
v___x_477_ = v___x_472_;
goto v_reusejp_476_;
}
else
{
lean_object* v_reuseFailAlloc_478_; 
v_reuseFailAlloc_478_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_478_, 0, v_key_468_);
lean_ctor_set(v_reuseFailAlloc_478_, 1, v_value_469_);
lean_ctor_set(v_reuseFailAlloc_478_, 2, v___x_475_);
v___x_477_ = v_reuseFailAlloc_478_;
goto v_reusejp_476_;
}
v_reusejp_476_:
{
return v___x_477_;
}
}
else
{
lean_object* v___x_480_; 
lean_dec(v_value_469_);
lean_dec(v_key_468_);
if (v_isShared_473_ == 0)
{
lean_ctor_set(v___x_472_, 1, v_b_466_);
lean_ctor_set(v___x_472_, 0, v_a_465_);
v___x_480_ = v___x_472_;
goto v_reusejp_479_;
}
else
{
lean_object* v_reuseFailAlloc_481_; 
v_reuseFailAlloc_481_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_481_, 0, v_a_465_);
lean_ctor_set(v_reuseFailAlloc_481_, 1, v_b_466_);
lean_ctor_set(v_reuseFailAlloc_481_, 2, v_tail_470_);
v___x_480_ = v_reuseFailAlloc_481_;
goto v_reusejp_479_;
}
v_reusejp_479_:
{
return v___x_480_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2_spec__3_spec__4___redArg(lean_object* v_x_483_, lean_object* v_x_484_){
_start:
{
if (lean_obj_tag(v_x_484_) == 0)
{
return v_x_483_;
}
else
{
lean_object* v_key_485_; lean_object* v_value_486_; lean_object* v_tail_487_; lean_object* v___x_489_; uint8_t v_isShared_490_; uint8_t v_isSharedCheck_513_; 
v_key_485_ = lean_ctor_get(v_x_484_, 0);
v_value_486_ = lean_ctor_get(v_x_484_, 1);
v_tail_487_ = lean_ctor_get(v_x_484_, 2);
v_isSharedCheck_513_ = !lean_is_exclusive(v_x_484_);
if (v_isSharedCheck_513_ == 0)
{
v___x_489_ = v_x_484_;
v_isShared_490_ = v_isSharedCheck_513_;
goto v_resetjp_488_;
}
else
{
lean_inc(v_tail_487_);
lean_inc(v_value_486_);
lean_inc(v_key_485_);
lean_dec(v_x_484_);
v___x_489_ = lean_box(0);
v_isShared_490_ = v_isSharedCheck_513_;
goto v_resetjp_488_;
}
v_resetjp_488_:
{
lean_object* v___x_491_; uint64_t v___y_493_; 
v___x_491_ = lean_array_get_size(v_x_483_);
if (lean_obj_tag(v_key_485_) == 0)
{
uint64_t v___x_511_; 
v___x_511_ = 1723ULL;
v___y_493_ = v___x_511_;
goto v___jp_492_;
}
else
{
uint64_t v_hash_512_; 
v_hash_512_ = lean_ctor_get_uint64(v_key_485_, sizeof(void*)*2);
v___y_493_ = v_hash_512_;
goto v___jp_492_;
}
v___jp_492_:
{
uint64_t v___x_494_; uint64_t v___x_495_; uint64_t v_fold_496_; uint64_t v___x_497_; uint64_t v___x_498_; uint64_t v___x_499_; size_t v___x_500_; size_t v___x_501_; size_t v___x_502_; size_t v___x_503_; size_t v___x_504_; lean_object* v___x_505_; lean_object* v___x_507_; 
v___x_494_ = 32ULL;
v___x_495_ = lean_uint64_shift_right(v___y_493_, v___x_494_);
v_fold_496_ = lean_uint64_xor(v___y_493_, v___x_495_);
v___x_497_ = 16ULL;
v___x_498_ = lean_uint64_shift_right(v_fold_496_, v___x_497_);
v___x_499_ = lean_uint64_xor(v_fold_496_, v___x_498_);
v___x_500_ = lean_uint64_to_usize(v___x_499_);
v___x_501_ = lean_usize_of_nat(v___x_491_);
v___x_502_ = ((size_t)1ULL);
v___x_503_ = lean_usize_sub(v___x_501_, v___x_502_);
v___x_504_ = lean_usize_land(v___x_500_, v___x_503_);
v___x_505_ = lean_array_uget_borrowed(v_x_483_, v___x_504_);
lean_inc(v___x_505_);
if (v_isShared_490_ == 0)
{
lean_ctor_set(v___x_489_, 2, v___x_505_);
v___x_507_ = v___x_489_;
goto v_reusejp_506_;
}
else
{
lean_object* v_reuseFailAlloc_510_; 
v_reuseFailAlloc_510_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_510_, 0, v_key_485_);
lean_ctor_set(v_reuseFailAlloc_510_, 1, v_value_486_);
lean_ctor_set(v_reuseFailAlloc_510_, 2, v___x_505_);
v___x_507_ = v_reuseFailAlloc_510_;
goto v_reusejp_506_;
}
v_reusejp_506_:
{
lean_object* v___x_508_; 
v___x_508_ = lean_array_uset(v_x_483_, v___x_504_, v___x_507_);
v_x_483_ = v___x_508_;
v_x_484_ = v_tail_487_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2_spec__3___redArg(lean_object* v_i_514_, lean_object* v_source_515_, lean_object* v_target_516_){
_start:
{
lean_object* v___x_517_; uint8_t v___x_518_; 
v___x_517_ = lean_array_get_size(v_source_515_);
v___x_518_ = lean_nat_dec_lt(v_i_514_, v___x_517_);
if (v___x_518_ == 0)
{
lean_dec_ref(v_source_515_);
lean_dec(v_i_514_);
return v_target_516_;
}
else
{
lean_object* v_es_519_; lean_object* v___x_520_; lean_object* v_source_521_; lean_object* v_target_522_; lean_object* v___x_523_; lean_object* v___x_524_; 
v_es_519_ = lean_array_fget(v_source_515_, v_i_514_);
v___x_520_ = lean_box(0);
v_source_521_ = lean_array_fset(v_source_515_, v_i_514_, v___x_520_);
v_target_522_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2_spec__3_spec__4___redArg(v_target_516_, v_es_519_);
v___x_523_ = lean_unsigned_to_nat(1u);
v___x_524_ = lean_nat_add(v_i_514_, v___x_523_);
lean_dec(v_i_514_);
v_i_514_ = v___x_524_;
v_source_515_ = v_source_521_;
v_target_516_ = v_target_522_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2___redArg(lean_object* v_data_526_){
_start:
{
lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v_nbuckets_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; 
v___x_527_ = lean_array_get_size(v_data_526_);
v___x_528_ = lean_unsigned_to_nat(2u);
v_nbuckets_529_ = lean_nat_mul(v___x_527_, v___x_528_);
v___x_530_ = lean_unsigned_to_nat(0u);
v___x_531_ = lean_box(0);
v___x_532_ = lean_mk_array(v_nbuckets_529_, v___x_531_);
v___x_533_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1_spec__2_spec__3___redArg(v___x_530_, v_data_526_, v___x_532_);
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
lean_object* v_toCold_659_; lean_object* v_currRecDepth_660_; lean_object* v_ref_661_; uint8_t v_diag_662_; uint8_t v_suppressElabErrors_663_; lean_object* v_ref_664_; lean_object* v___x_665_; lean_object* v___x_666_; 
v_toCold_659_ = lean_ctor_get(v___y_656_, 0);
v_currRecDepth_660_ = lean_ctor_get(v___y_656_, 1);
v_ref_661_ = lean_ctor_get(v___y_656_, 2);
v_diag_662_ = lean_ctor_get_uint8(v___y_656_, sizeof(void*)*3);
v_suppressElabErrors_663_ = lean_ctor_get_uint8(v___y_656_, sizeof(void*)*3 + 1);
v_ref_664_ = l_Lean_replaceRef(v_ref_654_, v_ref_661_);
lean_inc(v_currRecDepth_660_);
lean_inc_ref(v_toCold_659_);
v___x_665_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_665_, 0, v_toCold_659_);
lean_ctor_set(v___x_665_, 1, v_currRecDepth_660_);
lean_ctor_set(v___x_665_, 2, v_ref_664_);
lean_ctor_set_uint8(v___x_665_, sizeof(void*)*3, v_diag_662_);
lean_ctor_set_uint8(v___x_665_, sizeof(void*)*3 + 1, v_suppressElabErrors_663_);
v___x_666_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v_msg_655_, v___x_665_, v___y_657_);
lean_dec_ref_known(v___x_665_, 3);
return v___x_666_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg___boxed(lean_object* v_ref_667_, lean_object* v_msg_668_, lean_object* v___y_669_, lean_object* v___y_670_, lean_object* v___y_671_){
_start:
{
lean_object* v_res_672_; 
v_res_672_ = l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg(v_ref_667_, v_msg_668_, v___y_669_, v___y_670_);
lean_dec(v___y_670_);
lean_dec_ref(v___y_669_);
lean_dec(v_ref_667_);
return v_res_672_;
}
}
static lean_object* _init_l_Lean_Attribute_Builtin_ensureNoArgs___closed__4(void){
_start:
{
lean_object* v___x_681_; lean_object* v___x_682_; 
v___x_681_ = ((lean_object*)(l_Lean_Attribute_Builtin_ensureNoArgs___closed__3));
v___x_682_ = l_Lean_stringToMessageData(v___x_681_);
return v___x_682_;
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_ensureNoArgs(lean_object* v_stx_689_, lean_object* v_a_690_, lean_object* v_a_691_){
_start:
{
lean_object* v___x_693_; uint8_t v___y_704_; lean_object* v___x_710_; uint8_t v___x_711_; 
lean_inc(v_stx_689_);
v___x_693_ = l_Lean_Syntax_getKind(v_stx_689_);
v___x_710_ = ((lean_object*)(l_Lean_Attribute_Builtin_ensureNoArgs___closed__6));
v___x_711_ = lean_name_eq(v___x_693_, v___x_710_);
if (v___x_711_ == 0)
{
v___y_704_ = v___x_711_;
goto v___jp_703_;
}
else
{
lean_object* v___x_712_; lean_object* v___x_713_; uint8_t v___x_714_; 
v___x_712_ = lean_unsigned_to_nat(1u);
v___x_713_ = l_Lean_Syntax_getArg(v_stx_689_, v___x_712_);
v___x_714_ = l_Lean_Syntax_isNone(v___x_713_);
lean_dec(v___x_713_);
v___y_704_ = v___x_714_;
goto v___jp_703_;
}
v___jp_694_:
{
lean_object* v___x_695_; uint8_t v___x_696_; 
v___x_695_ = ((lean_object*)(l_Lean_Attribute_Builtin_ensureNoArgs___closed__2));
v___x_696_ = lean_name_eq(v___x_693_, v___x_695_);
lean_dec(v___x_693_);
if (v___x_696_ == 0)
{
if (lean_obj_tag(v_stx_689_) == 0)
{
lean_object* v___x_697_; lean_object* v___x_698_; 
v___x_697_ = lean_box(0);
v___x_698_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_698_, 0, v___x_697_);
return v___x_698_;
}
else
{
lean_object* v___x_699_; lean_object* v___x_700_; 
v___x_699_ = lean_obj_once(&l_Lean_Attribute_Builtin_ensureNoArgs___closed__4, &l_Lean_Attribute_Builtin_ensureNoArgs___closed__4_once, _init_l_Lean_Attribute_Builtin_ensureNoArgs___closed__4);
v___x_700_ = l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg(v_stx_689_, v___x_699_, v_a_690_, v_a_691_);
lean_dec(v_stx_689_);
return v___x_700_;
}
}
else
{
lean_object* v___x_701_; lean_object* v___x_702_; 
lean_dec(v_stx_689_);
v___x_701_ = lean_box(0);
v___x_702_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_702_, 0, v___x_701_);
return v___x_702_;
}
}
v___jp_703_:
{
if (v___y_704_ == 0)
{
goto v___jp_694_;
}
else
{
lean_object* v___x_705_; lean_object* v___x_706_; uint8_t v___x_707_; 
v___x_705_ = lean_unsigned_to_nat(2u);
v___x_706_ = l_Lean_Syntax_getArg(v_stx_689_, v___x_705_);
v___x_707_ = l_Lean_Syntax_isNone(v___x_706_);
lean_dec(v___x_706_);
if (v___x_707_ == 0)
{
goto v___jp_694_;
}
else
{
lean_object* v___x_708_; lean_object* v___x_709_; 
lean_dec(v___x_693_);
lean_dec(v_stx_689_);
v___x_708_ = lean_box(0);
v___x_709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_709_, 0, v___x_708_);
return v___x_709_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_ensureNoArgs___boxed(lean_object* v_stx_715_, lean_object* v_a_716_, lean_object* v_a_717_, lean_object* v_a_718_){
_start:
{
lean_object* v_res_719_; 
v_res_719_ = l_Lean_Attribute_Builtin_ensureNoArgs(v_stx_715_, v_a_716_, v_a_717_);
lean_dec(v_a_717_);
lean_dec_ref(v_a_716_);
return v_res_719_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0(lean_object* v_00_u03b1_720_, lean_object* v_ref_721_, lean_object* v_msg_722_, lean_object* v___y_723_, lean_object* v___y_724_){
_start:
{
lean_object* v___x_726_; 
v___x_726_ = l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg(v_ref_721_, v_msg_722_, v___y_723_, v___y_724_);
return v___x_726_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___boxed(lean_object* v_00_u03b1_727_, lean_object* v_ref_728_, lean_object* v_msg_729_, lean_object* v___y_730_, lean_object* v___y_731_, lean_object* v___y_732_){
_start:
{
lean_object* v_res_733_; 
v_res_733_ = l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0(v_00_u03b1_727_, v_ref_728_, v_msg_729_, v___y_730_, v___y_731_);
lean_dec(v___y_731_);
lean_dec_ref(v___y_730_);
lean_dec(v_ref_728_);
return v_res_733_;
}
}
static lean_object* _init_l_Lean_Attribute_Builtin_getIdent_x3f___closed__5(void){
_start:
{
lean_object* v___x_747_; lean_object* v___x_748_; 
v___x_747_ = ((lean_object*)(l_Lean_Attribute_Builtin_getIdent_x3f___closed__4));
v___x_748_ = l_Lean_stringToMessageData(v___x_747_);
return v___x_748_;
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getIdent_x3f(lean_object* v_stx_749_, lean_object* v_a_750_, lean_object* v_a_751_){
_start:
{
lean_object* v___x_761_; lean_object* v___x_762_; uint8_t v___x_763_; 
lean_inc(v_stx_749_);
v___x_761_ = l_Lean_Syntax_getKind(v_stx_749_);
v___x_762_ = ((lean_object*)(l_Lean_Attribute_Builtin_ensureNoArgs___closed__6));
v___x_763_ = lean_name_eq(v___x_761_, v___x_762_);
if (v___x_763_ == 0)
{
lean_object* v___x_764_; uint8_t v___x_765_; 
v___x_764_ = ((lean_object*)(l_Lean_Attribute_Builtin_getIdent_x3f___closed__1));
v___x_765_ = lean_name_eq(v___x_761_, v___x_764_);
if (v___x_765_ == 0)
{
lean_object* v___x_766_; uint8_t v___x_767_; 
v___x_766_ = ((lean_object*)(l_Lean_Attribute_Builtin_getIdent_x3f___closed__3));
v___x_767_ = lean_name_eq(v___x_761_, v___x_766_);
lean_dec(v___x_761_);
if (v___x_767_ == 0)
{
lean_object* v___x_768_; lean_object* v___x_769_; 
v___x_768_ = lean_obj_once(&l_Lean_Attribute_Builtin_getIdent_x3f___closed__5, &l_Lean_Attribute_Builtin_getIdent_x3f___closed__5_once, _init_l_Lean_Attribute_Builtin_getIdent_x3f___closed__5);
v___x_769_ = l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg(v_stx_749_, v___x_768_, v_a_750_, v_a_751_);
lean_dec(v_stx_749_);
return v___x_769_;
}
else
{
goto v___jp_753_;
}
}
else
{
lean_dec(v___x_761_);
goto v___jp_753_;
}
}
else
{
lean_object* v___x_770_; lean_object* v___x_771_; uint8_t v___x_772_; 
lean_dec(v___x_761_);
v___x_770_ = lean_unsigned_to_nat(1u);
v___x_771_ = l_Lean_Syntax_getArg(v_stx_749_, v___x_770_);
lean_dec(v_stx_749_);
v___x_772_ = l_Lean_Syntax_isNone(v___x_771_);
if (v___x_772_ == 0)
{
if (v___x_763_ == 0)
{
lean_dec(v___x_771_);
goto v___jp_758_;
}
else
{
lean_object* v___x_773_; lean_object* v___x_774_; uint8_t v___x_775_; 
v___x_773_ = lean_unsigned_to_nat(0u);
v___x_774_ = l_Lean_Syntax_getArg(v___x_771_, v___x_773_);
lean_dec(v___x_771_);
v___x_775_ = l_Lean_Syntax_isIdent(v___x_774_);
if (v___x_775_ == 0)
{
lean_dec(v___x_774_);
goto v___jp_758_;
}
else
{
lean_object* v___x_776_; lean_object* v___x_777_; 
v___x_776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_776_, 0, v___x_774_);
v___x_777_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_777_, 0, v___x_776_);
return v___x_777_;
}
}
}
else
{
lean_dec(v___x_771_);
goto v___jp_758_;
}
}
v___jp_753_:
{
lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; 
v___x_754_ = lean_unsigned_to_nat(1u);
v___x_755_ = l_Lean_Syntax_getArg(v_stx_749_, v___x_754_);
lean_dec(v_stx_749_);
v___x_756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_756_, 0, v___x_755_);
v___x_757_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_757_, 0, v___x_756_);
return v___x_757_;
}
v___jp_758_:
{
lean_object* v___x_759_; lean_object* v___x_760_; 
v___x_759_ = lean_box(0);
v___x_760_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_760_, 0, v___x_759_);
return v___x_760_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getIdent_x3f___boxed(lean_object* v_stx_778_, lean_object* v_a_779_, lean_object* v_a_780_, lean_object* v_a_781_){
_start:
{
lean_object* v_res_782_; 
v_res_782_ = l_Lean_Attribute_Builtin_getIdent_x3f(v_stx_778_, v_a_779_, v_a_780_);
lean_dec(v_a_780_);
lean_dec_ref(v_a_779_);
return v_res_782_;
}
}
static lean_object* _init_l_Lean_Attribute_Builtin_getIdent___closed__1(void){
_start:
{
lean_object* v___x_784_; lean_object* v___x_785_; 
v___x_784_ = ((lean_object*)(l_Lean_Attribute_Builtin_getIdent___closed__0));
v___x_785_ = l_Lean_stringToMessageData(v___x_784_);
return v___x_785_;
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getIdent(lean_object* v_stx_786_, lean_object* v_a_787_, lean_object* v_a_788_){
_start:
{
lean_object* v___x_790_; 
lean_inc(v_stx_786_);
v___x_790_ = l_Lean_Attribute_Builtin_getIdent_x3f(v_stx_786_, v_a_787_, v_a_788_);
if (lean_obj_tag(v___x_790_) == 0)
{
lean_object* v_a_791_; lean_object* v___x_793_; uint8_t v_isShared_794_; uint8_t v_isSharedCheck_804_; 
v_a_791_ = lean_ctor_get(v___x_790_, 0);
v_isSharedCheck_804_ = !lean_is_exclusive(v___x_790_);
if (v_isSharedCheck_804_ == 0)
{
v___x_793_ = v___x_790_;
v_isShared_794_ = v_isSharedCheck_804_;
goto v_resetjp_792_;
}
else
{
lean_inc(v_a_791_);
lean_dec(v___x_790_);
v___x_793_ = lean_box(0);
v_isShared_794_ = v_isSharedCheck_804_;
goto v_resetjp_792_;
}
v_resetjp_792_:
{
if (lean_obj_tag(v_a_791_) == 0)
{
lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; 
lean_del_object(v___x_793_);
v___x_795_ = lean_obj_once(&l_Lean_Attribute_Builtin_getIdent___closed__1, &l_Lean_Attribute_Builtin_getIdent___closed__1_once, _init_l_Lean_Attribute_Builtin_getIdent___closed__1);
lean_inc(v_stx_786_);
v___x_796_ = l_Lean_MessageData_ofSyntax(v_stx_786_);
v___x_797_ = l_Lean_indentD(v___x_796_);
v___x_798_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_798_, 0, v___x_795_);
lean_ctor_set(v___x_798_, 1, v___x_797_);
v___x_799_ = l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg(v_stx_786_, v___x_798_, v_a_787_, v_a_788_);
lean_dec(v_stx_786_);
return v___x_799_;
}
else
{
lean_object* v_val_800_; lean_object* v___x_802_; 
lean_dec(v_stx_786_);
v_val_800_ = lean_ctor_get(v_a_791_, 0);
lean_inc(v_val_800_);
lean_dec_ref_known(v_a_791_, 1);
if (v_isShared_794_ == 0)
{
lean_ctor_set(v___x_793_, 0, v_val_800_);
v___x_802_ = v___x_793_;
goto v_reusejp_801_;
}
else
{
lean_object* v_reuseFailAlloc_803_; 
v_reuseFailAlloc_803_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_803_, 0, v_val_800_);
v___x_802_ = v_reuseFailAlloc_803_;
goto v_reusejp_801_;
}
v_reusejp_801_:
{
return v___x_802_;
}
}
}
}
else
{
lean_object* v_a_805_; lean_object* v___x_807_; uint8_t v_isShared_808_; uint8_t v_isSharedCheck_812_; 
lean_dec(v_stx_786_);
v_a_805_ = lean_ctor_get(v___x_790_, 0);
v_isSharedCheck_812_ = !lean_is_exclusive(v___x_790_);
if (v_isSharedCheck_812_ == 0)
{
v___x_807_ = v___x_790_;
v_isShared_808_ = v_isSharedCheck_812_;
goto v_resetjp_806_;
}
else
{
lean_inc(v_a_805_);
lean_dec(v___x_790_);
v___x_807_ = lean_box(0);
v_isShared_808_ = v_isSharedCheck_812_;
goto v_resetjp_806_;
}
v_resetjp_806_:
{
lean_object* v___x_810_; 
if (v_isShared_808_ == 0)
{
v___x_810_ = v___x_807_;
goto v_reusejp_809_;
}
else
{
lean_object* v_reuseFailAlloc_811_; 
v_reuseFailAlloc_811_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_811_, 0, v_a_805_);
v___x_810_ = v_reuseFailAlloc_811_;
goto v_reusejp_809_;
}
v_reusejp_809_:
{
return v___x_810_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getIdent___boxed(lean_object* v_stx_813_, lean_object* v_a_814_, lean_object* v_a_815_, lean_object* v_a_816_){
_start:
{
lean_object* v_res_817_; 
v_res_817_ = l_Lean_Attribute_Builtin_getIdent(v_stx_813_, v_a_814_, v_a_815_);
lean_dec(v_a_815_);
lean_dec_ref(v_a_814_);
return v_res_817_;
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getId_x3f(lean_object* v_stx_818_, lean_object* v_a_819_, lean_object* v_a_820_){
_start:
{
lean_object* v___x_822_; 
v___x_822_ = l_Lean_Attribute_Builtin_getIdent_x3f(v_stx_818_, v_a_819_, v_a_820_);
if (lean_obj_tag(v___x_822_) == 0)
{
lean_object* v_a_823_; lean_object* v___x_825_; uint8_t v_isShared_826_; uint8_t v_isSharedCheck_843_; 
v_a_823_ = lean_ctor_get(v___x_822_, 0);
v_isSharedCheck_843_ = !lean_is_exclusive(v___x_822_);
if (v_isSharedCheck_843_ == 0)
{
v___x_825_ = v___x_822_;
v_isShared_826_ = v_isSharedCheck_843_;
goto v_resetjp_824_;
}
else
{
lean_inc(v_a_823_);
lean_dec(v___x_822_);
v___x_825_ = lean_box(0);
v_isShared_826_ = v_isSharedCheck_843_;
goto v_resetjp_824_;
}
v_resetjp_824_:
{
if (lean_obj_tag(v_a_823_) == 0)
{
lean_object* v___x_827_; lean_object* v___x_829_; 
v___x_827_ = lean_box(0);
if (v_isShared_826_ == 0)
{
lean_ctor_set(v___x_825_, 0, v___x_827_);
v___x_829_ = v___x_825_;
goto v_reusejp_828_;
}
else
{
lean_object* v_reuseFailAlloc_830_; 
v_reuseFailAlloc_830_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_830_, 0, v___x_827_);
v___x_829_ = v_reuseFailAlloc_830_;
goto v_reusejp_828_;
}
v_reusejp_828_:
{
return v___x_829_;
}
}
else
{
lean_object* v_val_831_; lean_object* v___x_833_; uint8_t v_isShared_834_; uint8_t v_isSharedCheck_842_; 
v_val_831_ = lean_ctor_get(v_a_823_, 0);
v_isSharedCheck_842_ = !lean_is_exclusive(v_a_823_);
if (v_isSharedCheck_842_ == 0)
{
v___x_833_ = v_a_823_;
v_isShared_834_ = v_isSharedCheck_842_;
goto v_resetjp_832_;
}
else
{
lean_inc(v_val_831_);
lean_dec(v_a_823_);
v___x_833_ = lean_box(0);
v_isShared_834_ = v_isSharedCheck_842_;
goto v_resetjp_832_;
}
v_resetjp_832_:
{
lean_object* v___x_835_; lean_object* v___x_837_; 
v___x_835_ = l_Lean_Syntax_getId(v_val_831_);
lean_dec(v_val_831_);
if (v_isShared_834_ == 0)
{
lean_ctor_set(v___x_833_, 0, v___x_835_);
v___x_837_ = v___x_833_;
goto v_reusejp_836_;
}
else
{
lean_object* v_reuseFailAlloc_841_; 
v_reuseFailAlloc_841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_841_, 0, v___x_835_);
v___x_837_ = v_reuseFailAlloc_841_;
goto v_reusejp_836_;
}
v_reusejp_836_:
{
lean_object* v___x_839_; 
if (v_isShared_826_ == 0)
{
lean_ctor_set(v___x_825_, 0, v___x_837_);
v___x_839_ = v___x_825_;
goto v_reusejp_838_;
}
else
{
lean_object* v_reuseFailAlloc_840_; 
v_reuseFailAlloc_840_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_840_, 0, v___x_837_);
v___x_839_ = v_reuseFailAlloc_840_;
goto v_reusejp_838_;
}
v_reusejp_838_:
{
return v___x_839_;
}
}
}
}
}
}
else
{
lean_object* v_a_844_; lean_object* v___x_846_; uint8_t v_isShared_847_; uint8_t v_isSharedCheck_851_; 
v_a_844_ = lean_ctor_get(v___x_822_, 0);
v_isSharedCheck_851_ = !lean_is_exclusive(v___x_822_);
if (v_isSharedCheck_851_ == 0)
{
v___x_846_ = v___x_822_;
v_isShared_847_ = v_isSharedCheck_851_;
goto v_resetjp_845_;
}
else
{
lean_inc(v_a_844_);
lean_dec(v___x_822_);
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
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getId_x3f___boxed(lean_object* v_stx_852_, lean_object* v_a_853_, lean_object* v_a_854_, lean_object* v_a_855_){
_start:
{
lean_object* v_res_856_; 
v_res_856_ = l_Lean_Attribute_Builtin_getId_x3f(v_stx_852_, v_a_853_, v_a_854_);
lean_dec(v_a_854_);
lean_dec_ref(v_a_853_);
return v_res_856_;
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getId(lean_object* v_stx_857_, lean_object* v_a_858_, lean_object* v_a_859_){
_start:
{
lean_object* v___x_861_; 
v___x_861_ = l_Lean_Attribute_Builtin_getIdent(v_stx_857_, v_a_858_, v_a_859_);
if (lean_obj_tag(v___x_861_) == 0)
{
lean_object* v_a_862_; lean_object* v___x_864_; uint8_t v_isShared_865_; uint8_t v_isSharedCheck_870_; 
v_a_862_ = lean_ctor_get(v___x_861_, 0);
v_isSharedCheck_870_ = !lean_is_exclusive(v___x_861_);
if (v_isSharedCheck_870_ == 0)
{
v___x_864_ = v___x_861_;
v_isShared_865_ = v_isSharedCheck_870_;
goto v_resetjp_863_;
}
else
{
lean_inc(v_a_862_);
lean_dec(v___x_861_);
v___x_864_ = lean_box(0);
v_isShared_865_ = v_isSharedCheck_870_;
goto v_resetjp_863_;
}
v_resetjp_863_:
{
lean_object* v___x_866_; lean_object* v___x_868_; 
v___x_866_ = l_Lean_Syntax_getId(v_a_862_);
lean_dec(v_a_862_);
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
}
else
{
lean_object* v_a_871_; lean_object* v___x_873_; uint8_t v_isShared_874_; uint8_t v_isSharedCheck_878_; 
v_a_871_ = lean_ctor_get(v___x_861_, 0);
v_isSharedCheck_878_ = !lean_is_exclusive(v___x_861_);
if (v_isSharedCheck_878_ == 0)
{
v___x_873_ = v___x_861_;
v_isShared_874_ = v_isSharedCheck_878_;
goto v_resetjp_872_;
}
else
{
lean_inc(v_a_871_);
lean_dec(v___x_861_);
v___x_873_ = lean_box(0);
v_isShared_874_ = v_isSharedCheck_878_;
goto v_resetjp_872_;
}
v_resetjp_872_:
{
lean_object* v___x_876_; 
if (v_isShared_874_ == 0)
{
v___x_876_ = v___x_873_;
goto v_reusejp_875_;
}
else
{
lean_object* v_reuseFailAlloc_877_; 
v_reuseFailAlloc_877_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_877_, 0, v_a_871_);
v___x_876_ = v_reuseFailAlloc_877_;
goto v_reusejp_875_;
}
v_reusejp_875_:
{
return v___x_876_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getId___boxed(lean_object* v_stx_879_, lean_object* v_a_880_, lean_object* v_a_881_, lean_object* v_a_882_){
_start:
{
lean_object* v_res_883_; 
v_res_883_ = l_Lean_Attribute_Builtin_getId(v_stx_879_, v_a_880_, v_a_881_);
lean_dec(v_a_881_);
lean_dec_ref(v_a_880_);
return v_res_883_;
}
}
static lean_object* _init_l_Lean_getAttrParamOptPrio___closed__1(void){
_start:
{
lean_object* v___x_885_; lean_object* v___x_886_; 
v___x_885_ = ((lean_object*)(l_Lean_getAttrParamOptPrio___closed__0));
v___x_886_ = l_Lean_stringToMessageData(v___x_885_);
return v___x_886_;
}
}
LEAN_EXPORT lean_object* l_Lean_getAttrParamOptPrio(lean_object* v_optPrioStx_887_, lean_object* v_a_888_, lean_object* v_a_889_){
_start:
{
uint8_t v___x_891_; 
v___x_891_ = l_Lean_Syntax_isNone(v_optPrioStx_887_);
if (v___x_891_ == 0)
{
lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; 
v___x_892_ = lean_unsigned_to_nat(0u);
v___x_893_ = l_Lean_Syntax_getArg(v_optPrioStx_887_, v___x_892_);
v___x_894_ = l_Lean_Syntax_isNatLit_x3f(v___x_893_);
lean_dec(v___x_893_);
if (lean_obj_tag(v___x_894_) == 0)
{
lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; 
v___x_895_ = lean_obj_once(&l_Lean_getAttrParamOptPrio___closed__1, &l_Lean_getAttrParamOptPrio___closed__1_once, _init_l_Lean_getAttrParamOptPrio___closed__1);
lean_inc(v_optPrioStx_887_);
v___x_896_ = l_Lean_MessageData_ofSyntax(v_optPrioStx_887_);
v___x_897_ = l_Lean_indentD(v___x_896_);
v___x_898_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_898_, 0, v___x_895_);
lean_ctor_set(v___x_898_, 1, v___x_897_);
v___x_899_ = l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg(v_optPrioStx_887_, v___x_898_, v_a_888_, v_a_889_);
lean_dec(v_optPrioStx_887_);
return v___x_899_;
}
else
{
lean_object* v_val_900_; lean_object* v___x_902_; uint8_t v_isShared_903_; uint8_t v_isSharedCheck_907_; 
lean_dec(v_optPrioStx_887_);
v_val_900_ = lean_ctor_get(v___x_894_, 0);
v_isSharedCheck_907_ = !lean_is_exclusive(v___x_894_);
if (v_isSharedCheck_907_ == 0)
{
v___x_902_ = v___x_894_;
v_isShared_903_ = v_isSharedCheck_907_;
goto v_resetjp_901_;
}
else
{
lean_inc(v_val_900_);
lean_dec(v___x_894_);
v___x_902_ = lean_box(0);
v_isShared_903_ = v_isSharedCheck_907_;
goto v_resetjp_901_;
}
v_resetjp_901_:
{
lean_object* v___x_905_; 
if (v_isShared_903_ == 0)
{
lean_ctor_set_tag(v___x_902_, 0);
v___x_905_ = v___x_902_;
goto v_reusejp_904_;
}
else
{
lean_object* v_reuseFailAlloc_906_; 
v_reuseFailAlloc_906_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_906_, 0, v_val_900_);
v___x_905_ = v_reuseFailAlloc_906_;
goto v_reusejp_904_;
}
v_reusejp_904_:
{
return v___x_905_;
}
}
}
}
else
{
lean_object* v___x_908_; lean_object* v___x_909_; 
lean_dec(v_optPrioStx_887_);
v___x_908_ = lean_unsigned_to_nat(1000u);
v___x_909_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_909_, 0, v___x_908_);
return v___x_909_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getAttrParamOptPrio___boxed(lean_object* v_optPrioStx_910_, lean_object* v_a_911_, lean_object* v_a_912_, lean_object* v_a_913_){
_start:
{
lean_object* v_res_914_; 
v_res_914_ = l_Lean_getAttrParamOptPrio(v_optPrioStx_910_, v_a_911_, v_a_912_);
lean_dec(v_a_912_);
lean_dec_ref(v_a_911_);
return v_res_914_;
}
}
static lean_object* _init_l_Lean_Attribute_Builtin_getPrio___closed__1(void){
_start:
{
lean_object* v___x_916_; lean_object* v___x_917_; 
v___x_916_ = ((lean_object*)(l_Lean_Attribute_Builtin_getPrio___closed__0));
v___x_917_ = l_Lean_stringToMessageData(v___x_916_);
return v___x_917_;
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getPrio(lean_object* v_stx_918_, lean_object* v_a_919_, lean_object* v_a_920_){
_start:
{
lean_object* v___x_922_; lean_object* v___x_923_; uint8_t v___x_924_; 
lean_inc(v_stx_918_);
v___x_922_ = l_Lean_Syntax_getKind(v_stx_918_);
v___x_923_ = ((lean_object*)(l_Lean_Attribute_Builtin_ensureNoArgs___closed__6));
v___x_924_ = lean_name_eq(v___x_922_, v___x_923_);
lean_dec(v___x_922_);
if (v___x_924_ == 0)
{
lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; 
v___x_925_ = lean_obj_once(&l_Lean_Attribute_Builtin_getPrio___closed__1, &l_Lean_Attribute_Builtin_getPrio___closed__1_once, _init_l_Lean_Attribute_Builtin_getPrio___closed__1);
lean_inc(v_stx_918_);
v___x_926_ = l_Lean_MessageData_ofSyntax(v_stx_918_);
v___x_927_ = l_Lean_indentD(v___x_926_);
v___x_928_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_928_, 0, v___x_925_);
lean_ctor_set(v___x_928_, 1, v___x_927_);
v___x_929_ = l_Lean_throwErrorAt___at___00Lean_Attribute_Builtin_ensureNoArgs_spec__0___redArg(v_stx_918_, v___x_928_, v_a_919_, v_a_920_);
lean_dec(v_stx_918_);
return v___x_929_;
}
else
{
lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; 
v___x_930_ = lean_unsigned_to_nat(1u);
v___x_931_ = l_Lean_Syntax_getArg(v_stx_918_, v___x_930_);
lean_dec(v_stx_918_);
v___x_932_ = l_Lean_getAttrParamOptPrio(v___x_931_, v_a_919_, v_a_920_);
return v___x_932_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_Builtin_getPrio___boxed(lean_object* v_stx_933_, lean_object* v_a_934_, lean_object* v_a_935_, lean_object* v_a_936_){
_start:
{
lean_object* v_res_937_; 
v_res_937_ = l_Lean_Attribute_Builtin_getPrio(v_stx_933_, v_a_934_, v_a_935_);
lean_dec(v_a_935_);
lean_dec_ref(v_a_934_);
return v_res_937_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__1(void){
_start:
{
lean_object* v___x_939_; lean_object* v___x_940_; 
v___x_939_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__0));
v___x_940_ = l_Lean_stringToMessageData(v___x_939_);
return v___x_940_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__3(void){
_start:
{
lean_object* v___x_942_; lean_object* v___x_943_; 
v___x_942_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__2));
v___x_943_ = l_Lean_stringToMessageData(v___x_942_);
return v___x_943_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__5(void){
_start:
{
lean_object* v___x_945_; lean_object* v___x_946_; 
v___x_945_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__4));
v___x_946_ = l_Lean_stringToMessageData(v___x_945_);
return v___x_946_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___redArg(lean_object* v_inst_947_, lean_object* v_inst_948_, lean_object* v_name_949_, uint8_t v_kind_950_){
_start:
{
lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___y_957_; 
v___x_951_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__1, &l_Lean_throwAttrMustBeGlobal___redArg___closed__1_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__1);
v___x_952_ = l_Lean_MessageData_ofName(v_name_949_);
v___x_953_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_953_, 0, v___x_951_);
lean_ctor_set(v___x_953_, 1, v___x_952_);
v___x_954_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__3, &l_Lean_throwAttrMustBeGlobal___redArg___closed__3_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__3);
v___x_955_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_955_, 0, v___x_953_);
lean_ctor_set(v___x_955_, 1, v___x_954_);
switch(v_kind_950_)
{
case 0:
{
lean_object* v___x_964_; 
v___x_964_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__0));
v___y_957_ = v___x_964_;
goto v___jp_956_;
}
case 1:
{
lean_object* v___x_965_; 
v___x_965_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__1));
v___y_957_ = v___x_965_;
goto v___jp_956_;
}
default: 
{
lean_object* v___x_966_; 
v___x_966_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__2));
v___y_957_ = v___x_966_;
goto v___jp_956_;
}
}
v___jp_956_:
{
lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; 
lean_inc_ref(v___y_957_);
v___x_958_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_958_, 0, v___y_957_);
v___x_959_ = l_Lean_MessageData_ofFormat(v___x_958_);
v___x_960_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_960_, 0, v___x_955_);
lean_ctor_set(v___x_960_, 1, v___x_959_);
v___x_961_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__5, &l_Lean_throwAttrMustBeGlobal___redArg___closed__5_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__5);
v___x_962_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_962_, 0, v___x_960_);
lean_ctor_set(v___x_962_, 1, v___x_961_);
v___x_963_ = l_Lean_throwError___redArg(v_inst_947_, v_inst_948_, v___x_962_);
return v___x_963_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___redArg___boxed(lean_object* v_inst_967_, lean_object* v_inst_968_, lean_object* v_name_969_, lean_object* v_kind_970_){
_start:
{
uint8_t v_kind_boxed_971_; lean_object* v_res_972_; 
v_kind_boxed_971_ = lean_unbox(v_kind_970_);
v_res_972_ = l_Lean_throwAttrMustBeGlobal___redArg(v_inst_967_, v_inst_968_, v_name_969_, v_kind_boxed_971_);
return v_res_972_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal(lean_object* v_m_973_, lean_object* v_inst_974_, lean_object* v_inst_975_, lean_object* v_00_u03b1_976_, lean_object* v_name_977_, uint8_t v_kind_978_){
_start:
{
lean_object* v___x_979_; 
v___x_979_ = l_Lean_throwAttrMustBeGlobal___redArg(v_inst_974_, v_inst_975_, v_name_977_, v_kind_978_);
return v___x_979_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___boxed(lean_object* v_m_980_, lean_object* v_inst_981_, lean_object* v_inst_982_, lean_object* v_00_u03b1_983_, lean_object* v_name_984_, lean_object* v_kind_985_){
_start:
{
uint8_t v_kind_boxed_986_; lean_object* v_res_987_; 
v_kind_boxed_986_ = lean_unbox(v_kind_985_);
v_res_987_ = l_Lean_throwAttrMustBeGlobal(v_m_980_, v_inst_981_, v_inst_982_, v_00_u03b1_983_, v_name_984_, v_kind_boxed_986_);
return v_res_987_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1(void){
_start:
{
lean_object* v___x_989_; lean_object* v___x_990_; 
v___x_989_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___redArg___closed__0));
v___x_990_ = l_Lean_stringToMessageData(v___x_989_);
return v___x_990_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__3(void){
_start:
{
lean_object* v___x_992_; lean_object* v___x_993_; 
v___x_992_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___redArg___closed__2));
v___x_993_ = l_Lean_stringToMessageData(v___x_992_);
return v___x_993_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__5(void){
_start:
{
lean_object* v___x_995_; lean_object* v___x_996_; 
v___x_995_ = ((lean_object*)(l_Lean_throwAttrDeclInImportedModule___redArg___closed__4));
v___x_996_ = l_Lean_stringToMessageData(v___x_995_);
return v___x_996_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___redArg(lean_object* v_inst_997_, lean_object* v_inst_998_, lean_object* v_attrName_999_, lean_object* v_declName_1000_){
_start:
{
lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; uint8_t v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; 
v___x_1001_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1);
v___x_1002_ = l_Lean_MessageData_ofName(v_attrName_999_);
v___x_1003_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1003_, 0, v___x_1001_);
lean_ctor_set(v___x_1003_, 1, v___x_1002_);
v___x_1004_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__3, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__3_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__3);
v___x_1005_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1005_, 0, v___x_1003_);
lean_ctor_set(v___x_1005_, 1, v___x_1004_);
v___x_1006_ = 0;
v___x_1007_ = l_Lean_MessageData_ofConstName(v_declName_1000_, v___x_1006_);
v___x_1008_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1008_, 0, v___x_1005_);
lean_ctor_set(v___x_1008_, 1, v___x_1007_);
v___x_1009_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__5, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__5_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__5);
v___x_1010_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1010_, 0, v___x_1008_);
lean_ctor_set(v___x_1010_, 1, v___x_1009_);
v___x_1011_ = l_Lean_throwError___redArg(v_inst_997_, v_inst_998_, v___x_1010_);
return v___x_1011_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule(lean_object* v_m_1012_, lean_object* v_inst_1013_, lean_object* v_inst_1014_, lean_object* v_00_u03b1_1015_, lean_object* v_attrName_1016_, lean_object* v_declName_1017_){
_start:
{
lean_object* v___x_1018_; 
v___x_1018_ = l_Lean_throwAttrDeclInImportedModule___redArg(v_inst_1013_, v_inst_1014_, v_attrName_1016_, v_declName_1017_);
return v___x_1018_;
}
}
static lean_object* _init_l_Lean_throwAttrNotInAsyncCtx___redArg___closed__1(void){
_start:
{
lean_object* v___x_1020_; lean_object* v___x_1021_; 
v___x_1020_ = ((lean_object*)(l_Lean_throwAttrNotInAsyncCtx___redArg___closed__0));
v___x_1021_ = l_Lean_stringToMessageData(v___x_1020_);
return v___x_1021_;
}
}
static lean_object* _init_l_Lean_throwAttrNotInAsyncCtx___redArg___closed__3(void){
_start:
{
lean_object* v___x_1023_; lean_object* v___x_1024_; 
v___x_1023_ = ((lean_object*)(l_Lean_throwAttrNotInAsyncCtx___redArg___closed__2));
v___x_1024_ = l_Lean_stringToMessageData(v___x_1023_);
return v___x_1024_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___redArg(lean_object* v_inst_1025_, lean_object* v_inst_1026_, lean_object* v_attrName_1027_, lean_object* v_declName_1028_, lean_object* v_asyncPrefix_x3f_1029_){
_start:
{
lean_object* v___y_1031_; 
if (lean_obj_tag(v_asyncPrefix_x3f_1029_) == 0)
{
lean_object* v___x_1044_; 
v___x_1044_ = l_Lean_MessageData_nil;
v___y_1031_ = v___x_1044_;
goto v___jp_1030_;
}
else
{
lean_object* v_val_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; 
v_val_1045_ = lean_ctor_get(v_asyncPrefix_x3f_1029_, 0);
lean_inc(v_val_1045_);
lean_dec_ref_known(v_asyncPrefix_x3f_1029_, 1);
v___x_1046_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___redArg___closed__3, &l_Lean_throwAttrNotInAsyncCtx___redArg___closed__3_once, _init_l_Lean_throwAttrNotInAsyncCtx___redArg___closed__3);
v___x_1047_ = l_Lean_MessageData_ofName(v_val_1045_);
v___x_1048_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1048_, 0, v___x_1046_);
lean_ctor_set(v___x_1048_, 1, v___x_1047_);
v___x_1049_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__5, &l_Lean_throwAttrMustBeGlobal___redArg___closed__5_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__5);
v___x_1050_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1050_, 0, v___x_1048_);
lean_ctor_set(v___x_1050_, 1, v___x_1049_);
v___y_1031_ = v___x_1050_;
goto v___jp_1030_;
}
v___jp_1030_:
{
lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; uint8_t v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; 
v___x_1032_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1);
v___x_1033_ = l_Lean_MessageData_ofName(v_attrName_1027_);
v___x_1034_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1034_, 0, v___x_1032_);
lean_ctor_set(v___x_1034_, 1, v___x_1033_);
v___x_1035_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__3, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__3_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__3);
v___x_1036_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1036_, 0, v___x_1034_);
lean_ctor_set(v___x_1036_, 1, v___x_1035_);
v___x_1037_ = 0;
v___x_1038_ = l_Lean_MessageData_ofConstName(v_declName_1028_, v___x_1037_);
v___x_1039_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1039_, 0, v___x_1036_);
lean_ctor_set(v___x_1039_, 1, v___x_1038_);
v___x_1040_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___redArg___closed__1, &l_Lean_throwAttrNotInAsyncCtx___redArg___closed__1_once, _init_l_Lean_throwAttrNotInAsyncCtx___redArg___closed__1);
v___x_1041_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1041_, 0, v___x_1039_);
lean_ctor_set(v___x_1041_, 1, v___x_1040_);
v___x_1042_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1042_, 0, v___x_1041_);
lean_ctor_set(v___x_1042_, 1, v___y_1031_);
v___x_1043_ = l_Lean_throwError___redArg(v_inst_1025_, v_inst_1026_, v___x_1042_);
return v___x_1043_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx(lean_object* v_m_1051_, lean_object* v_inst_1052_, lean_object* v_inst_1053_, lean_object* v_00_u03b1_1054_, lean_object* v_attrName_1055_, lean_object* v_declName_1056_, lean_object* v_asyncPrefix_x3f_1057_){
_start:
{
lean_object* v___x_1058_; 
v___x_1058_ = l_Lean_throwAttrNotInAsyncCtx___redArg(v_inst_1052_, v_inst_1053_, v_attrName_1055_, v_declName_1056_, v_asyncPrefix_x3f_1057_);
return v___x_1058_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1(void){
_start:
{
lean_object* v___x_1060_; lean_object* v___x_1061_; 
v___x_1060_ = ((lean_object*)(l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__0));
v___x_1061_ = l_Lean_stringToMessageData(v___x_1060_);
return v___x_1061_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__3(void){
_start:
{
lean_object* v___x_1063_; lean_object* v___x_1064_; 
v___x_1063_ = ((lean_object*)(l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__2));
v___x_1064_ = l_Lean_stringToMessageData(v___x_1063_);
return v___x_1064_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__5(void){
_start:
{
lean_object* v___x_1066_; lean_object* v___x_1067_; 
v___x_1066_ = ((lean_object*)(l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__4));
v___x_1067_ = l_Lean_stringToMessageData(v___x_1066_);
return v___x_1067_;
}
}
static lean_object* _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__7(void){
_start:
{
lean_object* v___x_1069_; lean_object* v___x_1070_; 
v___x_1069_ = ((lean_object*)(l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__6));
v___x_1070_ = l_Lean_stringToMessageData(v___x_1069_);
return v___x_1070_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclNotOfExpectedType___redArg(lean_object* v_inst_1071_, lean_object* v_inst_1072_, lean_object* v_attrName_1073_, lean_object* v_declName_1074_, lean_object* v_givenType_1075_, lean_object* v_expectedType_1076_){
_start:
{
lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; uint8_t v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; 
v___x_1077_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1);
v___x_1078_ = l_Lean_MessageData_ofName(v_attrName_1073_);
lean_inc_ref(v___x_1078_);
v___x_1079_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1079_, 0, v___x_1077_);
lean_ctor_set(v___x_1079_, 1, v___x_1078_);
v___x_1080_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1, &l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1);
v___x_1081_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1081_, 0, v___x_1079_);
lean_ctor_set(v___x_1081_, 1, v___x_1080_);
v___x_1082_ = 0;
v___x_1083_ = l_Lean_MessageData_ofConstName(v_declName_1074_, v___x_1082_);
v___x_1084_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1084_, 0, v___x_1081_);
lean_ctor_set(v___x_1084_, 1, v___x_1083_);
v___x_1085_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__3, &l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__3_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__3);
v___x_1086_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1086_, 0, v___x_1084_);
lean_ctor_set(v___x_1086_, 1, v___x_1085_);
v___x_1087_ = l_Lean_indentExpr(v_givenType_1075_);
v___x_1088_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1088_, 0, v___x_1086_);
lean_ctor_set(v___x_1088_, 1, v___x_1087_);
v___x_1089_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__5, &l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__5_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__5);
v___x_1090_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1090_, 0, v___x_1088_);
lean_ctor_set(v___x_1090_, 1, v___x_1089_);
v___x_1091_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1091_, 0, v___x_1090_);
lean_ctor_set(v___x_1091_, 1, v___x_1078_);
v___x_1092_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__7, &l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__7_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__7);
v___x_1093_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1093_, 0, v___x_1091_);
lean_ctor_set(v___x_1093_, 1, v___x_1092_);
v___x_1094_ = l_Lean_indentExpr(v_expectedType_1076_);
v___x_1095_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1095_, 0, v___x_1093_);
lean_ctor_set(v___x_1095_, 1, v___x_1094_);
v___x_1096_ = l_Lean_throwError___redArg(v_inst_1071_, v_inst_1072_, v___x_1095_);
return v___x_1096_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclNotOfExpectedType(lean_object* v_m_1097_, lean_object* v_inst_1098_, lean_object* v_inst_1099_, lean_object* v_00_u03b1_1100_, lean_object* v_attrName_1101_, lean_object* v_declName_1102_, lean_object* v_givenType_1103_, lean_object* v_expectedType_1104_){
_start:
{
lean_object* v___x_1105_; 
v___x_1105_ = l_Lean_throwAttrDeclNotOfExpectedType___redArg(v_inst_1098_, v_inst_1099_, v_attrName_1101_, v_declName_1102_, v_givenType_1103_, v_expectedType_1104_);
return v___x_1105_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1___redArg(lean_object* v_constName_1106_, uint8_t v_skipRealize_1107_, lean_object* v___y_1108_){
_start:
{
lean_object* v___x_1110_; lean_object* v_env_1111_; uint8_t v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; 
v___x_1110_ = lean_st_ref_get(v___y_1108_);
v_env_1111_ = lean_ctor_get(v___x_1110_, 0);
lean_inc_ref(v_env_1111_);
lean_dec(v___x_1110_);
v___x_1112_ = l_Lean_Environment_contains(v_env_1111_, v_constName_1106_, v_skipRealize_1107_);
v___x_1113_ = lean_box(v___x_1112_);
v___x_1114_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1114_, 0, v___x_1113_);
return v___x_1114_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1___redArg___boxed(lean_object* v_constName_1115_, lean_object* v_skipRealize_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_){
_start:
{
uint8_t v_skipRealize_boxed_1119_; lean_object* v_res_1120_; 
v_skipRealize_boxed_1119_ = lean_unbox(v_skipRealize_1116_);
v_res_1120_ = l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1___redArg(v_constName_1115_, v_skipRealize_boxed_1119_, v___y_1117_);
lean_dec(v___y_1117_);
return v_res_1120_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1(lean_object* v_constName_1121_, uint8_t v_skipRealize_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_){
_start:
{
lean_object* v___x_1126_; 
v___x_1126_ = l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1___redArg(v_constName_1121_, v_skipRealize_1122_, v___y_1124_);
return v___x_1126_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1___boxed(lean_object* v_constName_1127_, lean_object* v_skipRealize_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_){
_start:
{
uint8_t v_skipRealize_boxed_1132_; lean_object* v_res_1133_; 
v_skipRealize_boxed_1132_ = lean_unbox(v_skipRealize_1128_);
v_res_1133_ = l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1(v_constName_1127_, v_skipRealize_boxed_1132_, v___y_1129_, v___y_1130_);
lean_dec(v___y_1130_);
lean_dec_ref(v___y_1129_);
return v_res_1133_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___lam__0(lean_object* v___y_1134_, uint8_t v_isExporting_1135_, lean_object* v___x_1136_, lean_object* v_a_x3f_1137_){
_start:
{
lean_object* v___x_1139_; lean_object* v_env_1140_; lean_object* v_nextMacroScope_1141_; lean_object* v_ngen_1142_; lean_object* v_auxDeclNGen_1143_; lean_object* v_traceState_1144_; lean_object* v_messages_1145_; lean_object* v_infoState_1146_; lean_object* v_snapshotTasks_1147_; lean_object* v___x_1149_; uint8_t v_isShared_1150_; uint8_t v_isSharedCheck_1158_; 
v___x_1139_ = lean_st_ref_take(v___y_1134_);
v_env_1140_ = lean_ctor_get(v___x_1139_, 0);
v_nextMacroScope_1141_ = lean_ctor_get(v___x_1139_, 1);
v_ngen_1142_ = lean_ctor_get(v___x_1139_, 2);
v_auxDeclNGen_1143_ = lean_ctor_get(v___x_1139_, 3);
v_traceState_1144_ = lean_ctor_get(v___x_1139_, 4);
v_messages_1145_ = lean_ctor_get(v___x_1139_, 6);
v_infoState_1146_ = lean_ctor_get(v___x_1139_, 7);
v_snapshotTasks_1147_ = lean_ctor_get(v___x_1139_, 8);
v_isSharedCheck_1158_ = !lean_is_exclusive(v___x_1139_);
if (v_isSharedCheck_1158_ == 0)
{
lean_object* v_unused_1159_; 
v_unused_1159_ = lean_ctor_get(v___x_1139_, 5);
lean_dec(v_unused_1159_);
v___x_1149_ = v___x_1139_;
v_isShared_1150_ = v_isSharedCheck_1158_;
goto v_resetjp_1148_;
}
else
{
lean_inc(v_snapshotTasks_1147_);
lean_inc(v_infoState_1146_);
lean_inc(v_messages_1145_);
lean_inc(v_traceState_1144_);
lean_inc(v_auxDeclNGen_1143_);
lean_inc(v_ngen_1142_);
lean_inc(v_nextMacroScope_1141_);
lean_inc(v_env_1140_);
lean_dec(v___x_1139_);
v___x_1149_ = lean_box(0);
v_isShared_1150_ = v_isSharedCheck_1158_;
goto v_resetjp_1148_;
}
v_resetjp_1148_:
{
lean_object* v___x_1151_; lean_object* v___x_1153_; 
v___x_1151_ = l_Lean_Environment_setExporting(v_env_1140_, v_isExporting_1135_);
if (v_isShared_1150_ == 0)
{
lean_ctor_set(v___x_1149_, 5, v___x_1136_);
lean_ctor_set(v___x_1149_, 0, v___x_1151_);
v___x_1153_ = v___x_1149_;
goto v_reusejp_1152_;
}
else
{
lean_object* v_reuseFailAlloc_1157_; 
v_reuseFailAlloc_1157_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1157_, 0, v___x_1151_);
lean_ctor_set(v_reuseFailAlloc_1157_, 1, v_nextMacroScope_1141_);
lean_ctor_set(v_reuseFailAlloc_1157_, 2, v_ngen_1142_);
lean_ctor_set(v_reuseFailAlloc_1157_, 3, v_auxDeclNGen_1143_);
lean_ctor_set(v_reuseFailAlloc_1157_, 4, v_traceState_1144_);
lean_ctor_set(v_reuseFailAlloc_1157_, 5, v___x_1136_);
lean_ctor_set(v_reuseFailAlloc_1157_, 6, v_messages_1145_);
lean_ctor_set(v_reuseFailAlloc_1157_, 7, v_infoState_1146_);
lean_ctor_set(v_reuseFailAlloc_1157_, 8, v_snapshotTasks_1147_);
v___x_1153_ = v_reuseFailAlloc_1157_;
goto v_reusejp_1152_;
}
v_reusejp_1152_:
{
lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; 
v___x_1154_ = lean_st_ref_put(v___y_1134_, v___x_1153_);
v___x_1155_ = lean_box(0);
v___x_1156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1156_, 0, v___x_1155_);
return v___x_1156_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___lam__0___boxed(lean_object* v___y_1160_, lean_object* v_isExporting_1161_, lean_object* v___x_1162_, lean_object* v_a_x3f_1163_, lean_object* v___y_1164_){
_start:
{
uint8_t v_isExporting_boxed_1165_; lean_object* v_res_1166_; 
v_isExporting_boxed_1165_ = lean_unbox(v_isExporting_1161_);
v_res_1166_ = l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___lam__0(v___y_1160_, v_isExporting_boxed_1165_, v___x_1162_, v_a_x3f_1163_);
lean_dec(v_a_x3f_1163_);
lean_dec(v___y_1160_);
return v_res_1166_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_1167_; 
v___x_1167_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1167_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_1168_; lean_object* v___x_1169_; 
v___x_1168_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__0, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__0);
v___x_1169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1169_, 0, v___x_1168_);
return v___x_1169_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_1170_; lean_object* v___x_1171_; 
v___x_1170_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__1);
v___x_1171_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1171_, 0, v___x_1170_);
lean_ctor_set(v___x_1171_, 1, v___x_1170_);
return v___x_1171_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg(lean_object* v_x_1172_, uint8_t v_isExporting_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_){
_start:
{
lean_object* v___x_1177_; lean_object* v_env_1178_; lean_object* v___x_1179_; uint8_t v_isModule_1180_; 
v___x_1177_ = lean_st_ref_get(v___y_1175_);
v_env_1178_ = lean_ctor_get(v___x_1177_, 0);
lean_inc_ref(v_env_1178_);
lean_dec(v___x_1177_);
v___x_1179_ = l_Lean_Environment_header(v_env_1178_);
v_isModule_1180_ = lean_ctor_get_uint8(v___x_1179_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_1179_);
if (v_isModule_1180_ == 0)
{
lean_object* v___x_1181_; 
lean_dec_ref(v_env_1178_);
lean_inc(v___y_1175_);
lean_inc_ref(v___y_1174_);
v___x_1181_ = lean_apply_3(v_x_1172_, v___y_1174_, v___y_1175_, lean_box(0));
return v___x_1181_;
}
else
{
uint8_t v_isExporting_1182_; 
v_isExporting_1182_ = lean_ctor_get_uint8(v_env_1178_, sizeof(void*)*8);
lean_dec_ref(v_env_1178_);
if (v_isExporting_1173_ == 0)
{
if (v_isExporting_1182_ == 0)
{
lean_object* v___x_1233_; 
lean_inc(v___y_1175_);
lean_inc_ref(v___y_1174_);
v___x_1233_ = lean_apply_3(v_x_1172_, v___y_1174_, v___y_1175_, lean_box(0));
return v___x_1233_;
}
else
{
goto v___jp_1183_;
}
}
else
{
if (v_isExporting_1182_ == 0)
{
goto v___jp_1183_;
}
else
{
lean_object* v___x_1234_; 
lean_inc(v___y_1175_);
lean_inc_ref(v___y_1174_);
v___x_1234_ = lean_apply_3(v_x_1172_, v___y_1174_, v___y_1175_, lean_box(0));
return v___x_1234_;
}
}
v___jp_1183_:
{
lean_object* v___x_1184_; lean_object* v_env_1185_; lean_object* v_nextMacroScope_1186_; lean_object* v_ngen_1187_; lean_object* v_auxDeclNGen_1188_; lean_object* v_traceState_1189_; lean_object* v_messages_1190_; lean_object* v_infoState_1191_; lean_object* v_snapshotTasks_1192_; lean_object* v___x_1194_; uint8_t v_isShared_1195_; uint8_t v_isSharedCheck_1231_; 
v___x_1184_ = lean_st_ref_take(v___y_1175_);
v_env_1185_ = lean_ctor_get(v___x_1184_, 0);
v_nextMacroScope_1186_ = lean_ctor_get(v___x_1184_, 1);
v_ngen_1187_ = lean_ctor_get(v___x_1184_, 2);
v_auxDeclNGen_1188_ = lean_ctor_get(v___x_1184_, 3);
v_traceState_1189_ = lean_ctor_get(v___x_1184_, 4);
v_messages_1190_ = lean_ctor_get(v___x_1184_, 6);
v_infoState_1191_ = lean_ctor_get(v___x_1184_, 7);
v_snapshotTasks_1192_ = lean_ctor_get(v___x_1184_, 8);
v_isSharedCheck_1231_ = !lean_is_exclusive(v___x_1184_);
if (v_isSharedCheck_1231_ == 0)
{
lean_object* v_unused_1232_; 
v_unused_1232_ = lean_ctor_get(v___x_1184_, 5);
lean_dec(v_unused_1232_);
v___x_1194_ = v___x_1184_;
v_isShared_1195_ = v_isSharedCheck_1231_;
goto v_resetjp_1193_;
}
else
{
lean_inc(v_snapshotTasks_1192_);
lean_inc(v_infoState_1191_);
lean_inc(v_messages_1190_);
lean_inc(v_traceState_1189_);
lean_inc(v_auxDeclNGen_1188_);
lean_inc(v_ngen_1187_);
lean_inc(v_nextMacroScope_1186_);
lean_inc(v_env_1185_);
lean_dec(v___x_1184_);
v___x_1194_ = lean_box(0);
v_isShared_1195_ = v_isSharedCheck_1231_;
goto v_resetjp_1193_;
}
v_resetjp_1193_:
{
lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1199_; 
v___x_1196_ = l_Lean_Environment_setExporting(v_env_1185_, v_isExporting_1173_);
v___x_1197_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2);
if (v_isShared_1195_ == 0)
{
lean_ctor_set(v___x_1194_, 5, v___x_1197_);
lean_ctor_set(v___x_1194_, 0, v___x_1196_);
v___x_1199_ = v___x_1194_;
goto v_reusejp_1198_;
}
else
{
lean_object* v_reuseFailAlloc_1230_; 
v_reuseFailAlloc_1230_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1230_, 0, v___x_1196_);
lean_ctor_set(v_reuseFailAlloc_1230_, 1, v_nextMacroScope_1186_);
lean_ctor_set(v_reuseFailAlloc_1230_, 2, v_ngen_1187_);
lean_ctor_set(v_reuseFailAlloc_1230_, 3, v_auxDeclNGen_1188_);
lean_ctor_set(v_reuseFailAlloc_1230_, 4, v_traceState_1189_);
lean_ctor_set(v_reuseFailAlloc_1230_, 5, v___x_1197_);
lean_ctor_set(v_reuseFailAlloc_1230_, 6, v_messages_1190_);
lean_ctor_set(v_reuseFailAlloc_1230_, 7, v_infoState_1191_);
lean_ctor_set(v_reuseFailAlloc_1230_, 8, v_snapshotTasks_1192_);
v___x_1199_ = v_reuseFailAlloc_1230_;
goto v_reusejp_1198_;
}
v_reusejp_1198_:
{
lean_object* v___x_1200_; lean_object* v_r_1201_; 
v___x_1200_ = lean_st_ref_put(v___y_1175_, v___x_1199_);
lean_inc(v___y_1175_);
lean_inc_ref(v___y_1174_);
v_r_1201_ = lean_apply_3(v_x_1172_, v___y_1174_, v___y_1175_, lean_box(0));
if (lean_obj_tag(v_r_1201_) == 0)
{
lean_object* v_a_1202_; lean_object* v___x_1204_; uint8_t v_isShared_1205_; uint8_t v_isSharedCheck_1218_; 
v_a_1202_ = lean_ctor_get(v_r_1201_, 0);
v_isSharedCheck_1218_ = !lean_is_exclusive(v_r_1201_);
if (v_isSharedCheck_1218_ == 0)
{
v___x_1204_ = v_r_1201_;
v_isShared_1205_ = v_isSharedCheck_1218_;
goto v_resetjp_1203_;
}
else
{
lean_inc(v_a_1202_);
lean_dec(v_r_1201_);
v___x_1204_ = lean_box(0);
v_isShared_1205_ = v_isSharedCheck_1218_;
goto v_resetjp_1203_;
}
v_resetjp_1203_:
{
lean_object* v___x_1207_; 
lean_inc(v_a_1202_);
if (v_isShared_1205_ == 0)
{
lean_ctor_set_tag(v___x_1204_, 1);
v___x_1207_ = v___x_1204_;
goto v_reusejp_1206_;
}
else
{
lean_object* v_reuseFailAlloc_1217_; 
v_reuseFailAlloc_1217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1217_, 0, v_a_1202_);
v___x_1207_ = v_reuseFailAlloc_1217_;
goto v_reusejp_1206_;
}
v_reusejp_1206_:
{
lean_object* v___x_1208_; lean_object* v___x_1210_; uint8_t v_isShared_1211_; uint8_t v_isSharedCheck_1215_; 
v___x_1208_ = l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___lam__0(v___y_1175_, v_isExporting_1182_, v___x_1197_, v___x_1207_);
lean_dec_ref(v___x_1207_);
v_isSharedCheck_1215_ = !lean_is_exclusive(v___x_1208_);
if (v_isSharedCheck_1215_ == 0)
{
lean_object* v_unused_1216_; 
v_unused_1216_ = lean_ctor_get(v___x_1208_, 0);
lean_dec(v_unused_1216_);
v___x_1210_ = v___x_1208_;
v_isShared_1211_ = v_isSharedCheck_1215_;
goto v_resetjp_1209_;
}
else
{
lean_dec(v___x_1208_);
v___x_1210_ = lean_box(0);
v_isShared_1211_ = v_isSharedCheck_1215_;
goto v_resetjp_1209_;
}
v_resetjp_1209_:
{
lean_object* v___x_1213_; 
if (v_isShared_1211_ == 0)
{
lean_ctor_set(v___x_1210_, 0, v_a_1202_);
v___x_1213_ = v___x_1210_;
goto v_reusejp_1212_;
}
else
{
lean_object* v_reuseFailAlloc_1214_; 
v_reuseFailAlloc_1214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1214_, 0, v_a_1202_);
v___x_1213_ = v_reuseFailAlloc_1214_;
goto v_reusejp_1212_;
}
v_reusejp_1212_:
{
return v___x_1213_;
}
}
}
}
}
else
{
lean_object* v_a_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1223_; uint8_t v_isShared_1224_; uint8_t v_isSharedCheck_1228_; 
v_a_1219_ = lean_ctor_get(v_r_1201_, 0);
lean_inc(v_a_1219_);
lean_dec_ref_known(v_r_1201_, 1);
v___x_1220_ = lean_box(0);
v___x_1221_ = l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___lam__0(v___y_1175_, v_isExporting_1182_, v___x_1197_, v___x_1220_);
v_isSharedCheck_1228_ = !lean_is_exclusive(v___x_1221_);
if (v_isSharedCheck_1228_ == 0)
{
lean_object* v_unused_1229_; 
v_unused_1229_ = lean_ctor_get(v___x_1221_, 0);
lean_dec(v_unused_1229_);
v___x_1223_ = v___x_1221_;
v_isShared_1224_ = v_isSharedCheck_1228_;
goto v_resetjp_1222_;
}
else
{
lean_dec(v___x_1221_);
v___x_1223_ = lean_box(0);
v_isShared_1224_ = v_isSharedCheck_1228_;
goto v_resetjp_1222_;
}
v_resetjp_1222_:
{
lean_object* v___x_1226_; 
if (v_isShared_1224_ == 0)
{
lean_ctor_set_tag(v___x_1223_, 1);
lean_ctor_set(v___x_1223_, 0, v_a_1219_);
v___x_1226_ = v___x_1223_;
goto v_reusejp_1225_;
}
else
{
lean_object* v_reuseFailAlloc_1227_; 
v_reuseFailAlloc_1227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1227_, 0, v_a_1219_);
v___x_1226_ = v_reuseFailAlloc_1227_;
goto v_reusejp_1225_;
}
v_reusejp_1225_:
{
return v___x_1226_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___boxed(lean_object* v_x_1235_, lean_object* v_isExporting_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_){
_start:
{
uint8_t v_isExporting_boxed_1240_; lean_object* v_res_1241_; 
v_isExporting_boxed_1240_ = lean_unbox(v_isExporting_1236_);
v_res_1241_ = l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg(v_x_1235_, v_isExporting_boxed_1240_, v___y_1237_, v___y_1238_);
lean_dec(v___y_1238_);
lean_dec_ref(v___y_1237_);
return v_res_1241_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2(lean_object* v_00_u03b1_1242_, lean_object* v_x_1243_, uint8_t v_isExporting_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_){
_start:
{
lean_object* v___x_1248_; 
v___x_1248_ = l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg(v_x_1243_, v_isExporting_1244_, v___y_1245_, v___y_1246_);
return v___x_1248_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___boxed(lean_object* v_00_u03b1_1249_, lean_object* v_x_1250_, lean_object* v_isExporting_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_){
_start:
{
uint8_t v_isExporting_boxed_1255_; lean_object* v_res_1256_; 
v_isExporting_boxed_1255_ = lean_unbox(v_isExporting_1251_);
v_res_1256_ = l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2(v_00_u03b1_1249_, v_x_1250_, v_isExporting_boxed_1255_, v___y_1252_, v___y_1253_);
lean_dec(v___y_1253_);
lean_dec_ref(v___y_1252_);
return v_res_1256_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0_spec__3(lean_object* v_opts_1257_, lean_object* v_opt_1258_){
_start:
{
lean_object* v_name_1259_; lean_object* v_defValue_1260_; lean_object* v_map_1261_; lean_object* v___x_1262_; 
v_name_1259_ = lean_ctor_get(v_opt_1258_, 0);
v_defValue_1260_ = lean_ctor_get(v_opt_1258_, 1);
v_map_1261_ = lean_ctor_get(v_opts_1257_, 0);
v___x_1262_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1261_, v_name_1259_);
if (lean_obj_tag(v___x_1262_) == 0)
{
uint8_t v___x_1263_; 
v___x_1263_ = lean_unbox(v_defValue_1260_);
return v___x_1263_;
}
else
{
lean_object* v_val_1264_; 
v_val_1264_ = lean_ctor_get(v___x_1262_, 0);
lean_inc(v_val_1264_);
lean_dec_ref_known(v___x_1262_, 1);
if (lean_obj_tag(v_val_1264_) == 1)
{
uint8_t v_v_1265_; 
v_v_1265_ = lean_ctor_get_uint8(v_val_1264_, 0);
lean_dec_ref_known(v_val_1264_, 0);
return v_v_1265_;
}
else
{
uint8_t v___x_1266_; 
lean_dec(v_val_1264_);
v___x_1266_ = lean_unbox(v_defValue_1260_);
return v___x_1266_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0_spec__3___boxed(lean_object* v_opts_1267_, lean_object* v_opt_1268_){
_start:
{
uint8_t v_res_1269_; lean_object* v_r_1270_; 
v_res_1269_ = l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0_spec__3(v_opts_1267_, v_opt_1268_);
lean_dec_ref(v_opt_1268_);
lean_dec_ref(v_opts_1267_);
v_r_1270_ = lean_box(v_res_1269_);
return v_r_1270_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0(uint8_t v_suppressElabErrors_1278_, uint8_t v___y_1279_, lean_object* v_x_1280_){
_start:
{
if (lean_obj_tag(v_x_1280_) == 1)
{
lean_object* v_pre_1281_; 
v_pre_1281_ = lean_ctor_get(v_x_1280_, 0);
switch(lean_obj_tag(v_pre_1281_))
{
case 1:
{
lean_object* v_pre_1282_; 
v_pre_1282_ = lean_ctor_get(v_pre_1281_, 0);
switch(lean_obj_tag(v_pre_1282_))
{
case 0:
{
lean_object* v_str_1283_; lean_object* v_str_1284_; lean_object* v___x_1285_; uint8_t v___x_1286_; 
v_str_1283_ = lean_ctor_get(v_x_1280_, 1);
v_str_1284_ = lean_ctor_get(v_pre_1281_, 1);
v___x_1285_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__0));
v___x_1286_ = lean_string_dec_eq(v_str_1284_, v___x_1285_);
if (v___x_1286_ == 0)
{
lean_object* v___x_1287_; uint8_t v___x_1288_; 
v___x_1287_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__2));
v___x_1288_ = lean_string_dec_eq(v_str_1284_, v___x_1287_);
if (v___x_1288_ == 0)
{
return v___x_1288_;
}
else
{
lean_object* v___x_1289_; uint8_t v___x_1290_; 
v___x_1289_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__1));
v___x_1290_ = lean_string_dec_eq(v_str_1283_, v___x_1289_);
if (v___x_1290_ == 0)
{
return v___x_1290_;
}
else
{
return v_suppressElabErrors_1278_;
}
}
}
else
{
lean_object* v___x_1291_; uint8_t v___x_1292_; 
v___x_1291_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__2));
v___x_1292_ = lean_string_dec_eq(v_str_1283_, v___x_1291_);
if (v___x_1292_ == 0)
{
return v___x_1292_;
}
else
{
return v_suppressElabErrors_1278_;
}
}
}
case 1:
{
lean_object* v_pre_1293_; 
v_pre_1293_ = lean_ctor_get(v_pre_1282_, 0);
if (lean_obj_tag(v_pre_1293_) == 0)
{
lean_object* v_str_1294_; lean_object* v_str_1295_; lean_object* v_str_1296_; lean_object* v___x_1297_; uint8_t v___x_1298_; 
v_str_1294_ = lean_ctor_get(v_x_1280_, 1);
v_str_1295_ = lean_ctor_get(v_pre_1281_, 1);
v_str_1296_ = lean_ctor_get(v_pre_1282_, 1);
v___x_1297_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__3));
v___x_1298_ = lean_string_dec_eq(v_str_1296_, v___x_1297_);
if (v___x_1298_ == 0)
{
return v___x_1298_;
}
else
{
lean_object* v___x_1299_; uint8_t v___x_1300_; 
v___x_1299_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__4));
v___x_1300_ = lean_string_dec_eq(v_str_1295_, v___x_1299_);
if (v___x_1300_ == 0)
{
return v___x_1300_;
}
else
{
lean_object* v___x_1301_; uint8_t v___x_1302_; 
v___x_1301_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__5));
v___x_1302_ = lean_string_dec_eq(v_str_1294_, v___x_1301_);
if (v___x_1302_ == 0)
{
return v___x_1302_;
}
else
{
return v_suppressElabErrors_1278_;
}
}
}
}
else
{
return v___y_1279_;
}
}
default: 
{
return v___y_1279_;
}
}
}
case 0:
{
lean_object* v_str_1303_; lean_object* v___x_1304_; uint8_t v___x_1305_; 
v_str_1303_ = lean_ctor_get(v_x_1280_, 1);
v___x_1304_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___closed__6));
v___x_1305_ = lean_string_dec_eq(v_str_1303_, v___x_1304_);
if (v___x_1305_ == 0)
{
return v___x_1305_;
}
else
{
return v_suppressElabErrors_1278_;
}
}
default: 
{
return v___y_1279_;
}
}
}
else
{
return v___y_1279_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___boxed(lean_object* v_suppressElabErrors_1306_, lean_object* v___y_1307_, lean_object* v_x_1308_){
_start:
{
uint8_t v_suppressElabErrors_boxed_1309_; uint8_t v___y_5018__boxed_1310_; uint8_t v_res_1311_; lean_object* v_r_1312_; 
v_suppressElabErrors_boxed_1309_ = lean_unbox(v_suppressElabErrors_1306_);
v___y_5018__boxed_1310_ = lean_unbox(v___y_1307_);
v_res_1311_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0(v_suppressElabErrors_boxed_1309_, v___y_5018__boxed_1310_, v_x_1308_);
lean_dec(v_x_1308_);
v_r_1312_ = lean_box(v_res_1311_);
return v_r_1312_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6(lean_object* v_ref_1313_, lean_object* v_msgData_1314_, uint8_t v_severity_1315_, uint8_t v_isSilent_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_){
_start:
{
uint8_t v___y_1321_; lean_object* v___y_1322_; lean_object* v___y_1323_; uint8_t v___y_1324_; lean_object* v___y_1325_; lean_object* v___y_1326_; lean_object* v___y_1327_; lean_object* v___y_1328_; lean_object* v___y_1329_; lean_object* v___y_1358_; lean_object* v___y_1359_; uint8_t v___y_1360_; lean_object* v___y_1361_; uint8_t v___y_1362_; lean_object* v___y_1363_; uint8_t v___y_1364_; lean_object* v___y_1365_; lean_object* v___y_1383_; lean_object* v___y_1384_; uint8_t v___y_1385_; uint8_t v___y_1386_; uint8_t v___y_1387_; lean_object* v___y_1388_; lean_object* v___y_1389_; lean_object* v___y_1390_; lean_object* v___y_1394_; lean_object* v___y_1395_; uint8_t v___y_1396_; lean_object* v___y_1397_; uint8_t v___y_1398_; lean_object* v___y_1399_; uint8_t v___y_1400_; uint8_t v___x_1405_; lean_object* v___y_1407_; lean_object* v___y_1408_; lean_object* v___y_1409_; uint8_t v___y_1410_; lean_object* v___y_1411_; uint8_t v___y_1412_; uint8_t v___y_1413_; uint8_t v___y_1415_; uint8_t v___x_1431_; 
v___x_1405_ = 2;
v___x_1431_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1315_, v___x_1405_);
if (v___x_1431_ == 0)
{
v___y_1415_ = v___x_1431_;
goto v___jp_1414_;
}
else
{
uint8_t v___x_1432_; 
lean_inc_ref(v_msgData_1314_);
v___x_1432_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_1314_);
v___y_1415_ = v___x_1432_;
goto v___jp_1414_;
}
v___jp_1320_:
{
lean_object* v___x_1330_; lean_object* v_toCold_1331_; lean_object* v_currNamespace_1332_; lean_object* v_openDecls_1333_; lean_object* v_env_1334_; lean_object* v_nextMacroScope_1335_; lean_object* v_ngen_1336_; lean_object* v_auxDeclNGen_1337_; lean_object* v_traceState_1338_; lean_object* v_cache_1339_; lean_object* v_messages_1340_; lean_object* v_infoState_1341_; lean_object* v_snapshotTasks_1342_; lean_object* v___x_1344_; uint8_t v_isShared_1345_; uint8_t v_isSharedCheck_1356_; 
v___x_1330_ = lean_st_ref_take(v___y_1329_);
v_toCold_1331_ = lean_ctor_get(v___y_1328_, 0);
v_currNamespace_1332_ = lean_ctor_get(v_toCold_1331_, 4);
v_openDecls_1333_ = lean_ctor_get(v_toCold_1331_, 5);
v_env_1334_ = lean_ctor_get(v___x_1330_, 0);
v_nextMacroScope_1335_ = lean_ctor_get(v___x_1330_, 1);
v_ngen_1336_ = lean_ctor_get(v___x_1330_, 2);
v_auxDeclNGen_1337_ = lean_ctor_get(v___x_1330_, 3);
v_traceState_1338_ = lean_ctor_get(v___x_1330_, 4);
v_cache_1339_ = lean_ctor_get(v___x_1330_, 5);
v_messages_1340_ = lean_ctor_get(v___x_1330_, 6);
v_infoState_1341_ = lean_ctor_get(v___x_1330_, 7);
v_snapshotTasks_1342_ = lean_ctor_get(v___x_1330_, 8);
v_isSharedCheck_1356_ = !lean_is_exclusive(v___x_1330_);
if (v_isSharedCheck_1356_ == 0)
{
v___x_1344_ = v___x_1330_;
v_isShared_1345_ = v_isSharedCheck_1356_;
goto v_resetjp_1343_;
}
else
{
lean_inc(v_snapshotTasks_1342_);
lean_inc(v_infoState_1341_);
lean_inc(v_messages_1340_);
lean_inc(v_cache_1339_);
lean_inc(v_traceState_1338_);
lean_inc(v_auxDeclNGen_1337_);
lean_inc(v_ngen_1336_);
lean_inc(v_nextMacroScope_1335_);
lean_inc(v_env_1334_);
lean_dec(v___x_1330_);
v___x_1344_ = lean_box(0);
v_isShared_1345_ = v_isSharedCheck_1356_;
goto v_resetjp_1343_;
}
v_resetjp_1343_:
{
lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1351_; 
lean_inc(v_openDecls_1333_);
lean_inc(v_currNamespace_1332_);
v___x_1346_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1346_, 0, v_currNamespace_1332_);
lean_ctor_set(v___x_1346_, 1, v_openDecls_1333_);
v___x_1347_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1347_, 0, v___x_1346_);
lean_ctor_set(v___x_1347_, 1, v___y_1322_);
lean_inc_ref(v___y_1323_);
lean_inc_ref(v___y_1326_);
v___x_1348_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_1348_, 0, v___y_1326_);
lean_ctor_set(v___x_1348_, 1, v___y_1325_);
lean_ctor_set(v___x_1348_, 2, v___y_1327_);
lean_ctor_set(v___x_1348_, 3, v___y_1323_);
lean_ctor_set(v___x_1348_, 4, v___x_1347_);
lean_ctor_set_uint8(v___x_1348_, sizeof(void*)*5, v___y_1324_);
lean_ctor_set_uint8(v___x_1348_, sizeof(void*)*5 + 1, v___y_1321_);
lean_ctor_set_uint8(v___x_1348_, sizeof(void*)*5 + 2, v_isSilent_1316_);
v___x_1349_ = l_Lean_MessageLog_add(v___x_1348_, v_messages_1340_);
if (v_isShared_1345_ == 0)
{
lean_ctor_set(v___x_1344_, 6, v___x_1349_);
v___x_1351_ = v___x_1344_;
goto v_reusejp_1350_;
}
else
{
lean_object* v_reuseFailAlloc_1355_; 
v_reuseFailAlloc_1355_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1355_, 0, v_env_1334_);
lean_ctor_set(v_reuseFailAlloc_1355_, 1, v_nextMacroScope_1335_);
lean_ctor_set(v_reuseFailAlloc_1355_, 2, v_ngen_1336_);
lean_ctor_set(v_reuseFailAlloc_1355_, 3, v_auxDeclNGen_1337_);
lean_ctor_set(v_reuseFailAlloc_1355_, 4, v_traceState_1338_);
lean_ctor_set(v_reuseFailAlloc_1355_, 5, v_cache_1339_);
lean_ctor_set(v_reuseFailAlloc_1355_, 6, v___x_1349_);
lean_ctor_set(v_reuseFailAlloc_1355_, 7, v_infoState_1341_);
lean_ctor_set(v_reuseFailAlloc_1355_, 8, v_snapshotTasks_1342_);
v___x_1351_ = v_reuseFailAlloc_1355_;
goto v_reusejp_1350_;
}
v_reusejp_1350_:
{
lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; 
v___x_1352_ = lean_st_ref_put(v___y_1329_, v___x_1351_);
v___x_1353_ = lean_box(0);
v___x_1354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1354_, 0, v___x_1353_);
return v___x_1354_;
}
}
}
v___jp_1357_:
{
lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v_a_1368_; lean_object* v___x_1370_; uint8_t v_isShared_1371_; uint8_t v_isSharedCheck_1381_; 
v___x_1366_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_1314_);
v___x_1367_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0_spec__0(v___x_1366_, v___y_1317_, v___y_1318_);
v_a_1368_ = lean_ctor_get(v___x_1367_, 0);
v_isSharedCheck_1381_ = !lean_is_exclusive(v___x_1367_);
if (v_isSharedCheck_1381_ == 0)
{
v___x_1370_ = v___x_1367_;
v_isShared_1371_ = v_isSharedCheck_1381_;
goto v_resetjp_1369_;
}
else
{
lean_inc(v_a_1368_);
lean_dec(v___x_1367_);
v___x_1370_ = lean_box(0);
v_isShared_1371_ = v_isSharedCheck_1381_;
goto v_resetjp_1369_;
}
v_resetjp_1369_:
{
lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; 
lean_inc_ref_n(v___y_1361_, 2);
v___x_1372_ = l_Lean_FileMap_toPosition(v___y_1361_, v___y_1359_);
lean_dec(v___y_1359_);
v___x_1373_ = l_Lean_FileMap_toPosition(v___y_1361_, v___y_1365_);
lean_dec(v___y_1365_);
v___x_1374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1374_, 0, v___x_1373_);
v___x_1375_ = ((lean_object*)(l_Lean_instInhabitedAttributeImplCore_default___closed__3));
if (v___y_1362_ == 0)
{
lean_del_object(v___x_1370_);
lean_dec_ref(v___y_1358_);
v___y_1321_ = v___y_1360_;
v___y_1322_ = v_a_1368_;
v___y_1323_ = v___x_1375_;
v___y_1324_ = v___y_1364_;
v___y_1325_ = v___x_1372_;
v___y_1326_ = v___y_1363_;
v___y_1327_ = v___x_1374_;
v___y_1328_ = v___y_1317_;
v___y_1329_ = v___y_1318_;
goto v___jp_1320_;
}
else
{
uint8_t v___x_1376_; 
lean_inc(v_a_1368_);
v___x_1376_ = l_Lean_MessageData_hasTag(v___y_1358_, v_a_1368_);
if (v___x_1376_ == 0)
{
lean_object* v___x_1377_; lean_object* v___x_1379_; 
lean_dec_ref_known(v___x_1374_, 1);
lean_dec_ref(v___x_1372_);
lean_dec(v_a_1368_);
v___x_1377_ = lean_box(0);
if (v_isShared_1371_ == 0)
{
lean_ctor_set(v___x_1370_, 0, v___x_1377_);
v___x_1379_ = v___x_1370_;
goto v_reusejp_1378_;
}
else
{
lean_object* v_reuseFailAlloc_1380_; 
v_reuseFailAlloc_1380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1380_, 0, v___x_1377_);
v___x_1379_ = v_reuseFailAlloc_1380_;
goto v_reusejp_1378_;
}
v_reusejp_1378_:
{
return v___x_1379_;
}
}
else
{
lean_del_object(v___x_1370_);
v___y_1321_ = v___y_1360_;
v___y_1322_ = v_a_1368_;
v___y_1323_ = v___x_1375_;
v___y_1324_ = v___y_1364_;
v___y_1325_ = v___x_1372_;
v___y_1326_ = v___y_1363_;
v___y_1327_ = v___x_1374_;
v___y_1328_ = v___y_1317_;
v___y_1329_ = v___y_1318_;
goto v___jp_1320_;
}
}
}
}
v___jp_1382_:
{
lean_object* v___x_1391_; 
v___x_1391_ = l_Lean_Syntax_getTailPos_x3f(v___y_1389_, v___y_1387_);
lean_dec(v___y_1389_);
if (lean_obj_tag(v___x_1391_) == 0)
{
lean_inc(v___y_1390_);
v___y_1358_ = v___y_1383_;
v___y_1359_ = v___y_1390_;
v___y_1360_ = v___y_1385_;
v___y_1361_ = v___y_1384_;
v___y_1362_ = v___y_1386_;
v___y_1363_ = v___y_1388_;
v___y_1364_ = v___y_1387_;
v___y_1365_ = v___y_1390_;
goto v___jp_1357_;
}
else
{
lean_object* v_val_1392_; 
v_val_1392_ = lean_ctor_get(v___x_1391_, 0);
lean_inc(v_val_1392_);
lean_dec_ref_known(v___x_1391_, 1);
v___y_1358_ = v___y_1383_;
v___y_1359_ = v___y_1390_;
v___y_1360_ = v___y_1385_;
v___y_1361_ = v___y_1384_;
v___y_1362_ = v___y_1386_;
v___y_1363_ = v___y_1388_;
v___y_1364_ = v___y_1387_;
v___y_1365_ = v_val_1392_;
goto v___jp_1357_;
}
}
v___jp_1393_:
{
lean_object* v_ref_1401_; lean_object* v___x_1402_; 
v_ref_1401_ = l_Lean_replaceRef(v_ref_1313_, v___y_1399_);
v___x_1402_ = l_Lean_Syntax_getPos_x3f(v_ref_1401_, v___y_1398_);
if (lean_obj_tag(v___x_1402_) == 0)
{
lean_object* v___x_1403_; 
v___x_1403_ = lean_unsigned_to_nat(0u);
v___y_1383_ = v___y_1394_;
v___y_1384_ = v___y_1395_;
v___y_1385_ = v___y_1400_;
v___y_1386_ = v___y_1396_;
v___y_1387_ = v___y_1398_;
v___y_1388_ = v___y_1397_;
v___y_1389_ = v_ref_1401_;
v___y_1390_ = v___x_1403_;
goto v___jp_1382_;
}
else
{
lean_object* v_val_1404_; 
v_val_1404_ = lean_ctor_get(v___x_1402_, 0);
lean_inc(v_val_1404_);
lean_dec_ref_known(v___x_1402_, 1);
v___y_1383_ = v___y_1394_;
v___y_1384_ = v___y_1395_;
v___y_1385_ = v___y_1400_;
v___y_1386_ = v___y_1396_;
v___y_1387_ = v___y_1398_;
v___y_1388_ = v___y_1397_;
v___y_1389_ = v_ref_1401_;
v___y_1390_ = v_val_1404_;
goto v___jp_1382_;
}
}
v___jp_1406_:
{
if (v___y_1413_ == 0)
{
v___y_1394_ = v___y_1408_;
v___y_1395_ = v___y_1407_;
v___y_1396_ = v___y_1410_;
v___y_1397_ = v___y_1409_;
v___y_1398_ = v___y_1412_;
v___y_1399_ = v___y_1411_;
v___y_1400_ = v_severity_1315_;
goto v___jp_1393_;
}
else
{
v___y_1394_ = v___y_1408_;
v___y_1395_ = v___y_1407_;
v___y_1396_ = v___y_1410_;
v___y_1397_ = v___y_1409_;
v___y_1398_ = v___y_1412_;
v___y_1399_ = v___y_1411_;
v___y_1400_ = v___x_1405_;
goto v___jp_1393_;
}
}
v___jp_1414_:
{
if (v___y_1415_ == 0)
{
lean_object* v_toCold_1416_; lean_object* v_ref_1417_; uint8_t v_suppressElabErrors_1418_; lean_object* v_fileName_1419_; lean_object* v_fileMap_1420_; lean_object* v_options_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___f_1424_; uint8_t v___x_1425_; uint8_t v___x_1426_; 
v_toCold_1416_ = lean_ctor_get(v___y_1317_, 0);
v_ref_1417_ = lean_ctor_get(v___y_1317_, 2);
v_suppressElabErrors_1418_ = lean_ctor_get_uint8(v___y_1317_, sizeof(void*)*3 + 1);
v_fileName_1419_ = lean_ctor_get(v_toCold_1416_, 0);
v_fileMap_1420_ = lean_ctor_get(v_toCold_1416_, 1);
v_options_1421_ = lean_ctor_get(v_toCold_1416_, 2);
v___x_1422_ = lean_box(v_suppressElabErrors_1418_);
v___x_1423_ = lean_box(v___y_1415_);
v___f_1424_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1424_, 0, v___x_1422_);
lean_closure_set(v___f_1424_, 1, v___x_1423_);
v___x_1425_ = 1;
v___x_1426_ = l_Lean_instBEqMessageSeverity_beq(v_severity_1315_, v___x_1425_);
if (v___x_1426_ == 0)
{
v___y_1407_ = v_fileMap_1420_;
v___y_1408_ = v___f_1424_;
v___y_1409_ = v_fileName_1419_;
v___y_1410_ = v_suppressElabErrors_1418_;
v___y_1411_ = v_ref_1417_;
v___y_1412_ = v___y_1415_;
v___y_1413_ = v___x_1426_;
goto v___jp_1406_;
}
else
{
lean_object* v___x_1427_; uint8_t v___x_1428_; 
v___x_1427_ = l_Lean_warningAsError;
v___x_1428_ = l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0_spec__3(v_options_1421_, v___x_1427_);
v___y_1407_ = v_fileMap_1420_;
v___y_1408_ = v___f_1424_;
v___y_1409_ = v_fileName_1419_;
v___y_1410_ = v_suppressElabErrors_1418_;
v___y_1411_ = v_ref_1417_;
v___y_1412_ = v___y_1415_;
v___y_1413_ = v___x_1428_;
goto v___jp_1406_;
}
}
else
{
lean_object* v___x_1429_; lean_object* v___x_1430_; 
lean_dec_ref(v_msgData_1314_);
v___x_1429_ = lean_box(0);
v___x_1430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1430_, 0, v___x_1429_);
return v___x_1430_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6___boxed(lean_object* v_ref_1433_, lean_object* v_msgData_1434_, lean_object* v_severity_1435_, lean_object* v_isSilent_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_){
_start:
{
uint8_t v_severity_boxed_1440_; uint8_t v_isSilent_boxed_1441_; lean_object* v_res_1442_; 
v_severity_boxed_1440_ = lean_unbox(v_severity_1435_);
v_isSilent_boxed_1441_ = lean_unbox(v_isSilent_1436_);
v_res_1442_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6(v_ref_1433_, v_msgData_1434_, v_severity_boxed_1440_, v_isSilent_boxed_1441_, v___y_1437_, v___y_1438_);
lean_dec(v___y_1438_);
lean_dec_ref(v___y_1437_);
lean_dec(v_ref_1433_);
return v_res_1442_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5(lean_object* v_msgData_1443_, uint8_t v_severity_1444_, uint8_t v_isSilent_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_){
_start:
{
lean_object* v_ref_1449_; lean_object* v___x_1450_; 
v_ref_1449_ = lean_ctor_get(v___y_1446_, 2);
v___x_1450_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5_spec__6(v_ref_1449_, v_msgData_1443_, v_severity_1444_, v_isSilent_1445_, v___y_1446_, v___y_1447_);
return v___x_1450_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5___boxed(lean_object* v_msgData_1451_, lean_object* v_severity_1452_, lean_object* v_isSilent_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_){
_start:
{
uint8_t v_severity_boxed_1457_; uint8_t v_isSilent_boxed_1458_; lean_object* v_res_1459_; 
v_severity_boxed_1457_ = lean_unbox(v_severity_1452_);
v_isSilent_boxed_1458_ = lean_unbox(v_isSilent_1453_);
v_res_1459_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5(v_msgData_1451_, v_severity_boxed_1457_, v_isSilent_boxed_1458_, v___y_1454_, v___y_1455_);
lean_dec(v___y_1455_);
lean_dec_ref(v___y_1454_);
return v_res_1459_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1(lean_object* v_msgData_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_){
_start:
{
uint8_t v___x_1464_; uint8_t v___x_1465_; lean_object* v___x_1466_; 
v___x_1464_ = 1;
v___x_1465_ = 0;
v___x_1466_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1_spec__5(v_msgData_1460_, v___x_1464_, v___x_1465_, v___y_1461_, v___y_1462_);
return v___x_1466_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1___boxed(lean_object* v_msgData_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_){
_start:
{
lean_object* v_res_1471_; 
v_res_1471_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1(v_msgData_1467_, v___y_1468_, v___y_1469_);
lean_dec(v___y_1469_);
lean_dec_ref(v___y_1468_);
return v_res_1471_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0___redArg(lean_object* v_opt_1472_, lean_object* v___y_1473_){
_start:
{
lean_object* v_toCold_1475_; lean_object* v_options_1476_; uint8_t v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; 
v_toCold_1475_ = lean_ctor_get(v___y_1473_, 0);
v_options_1476_ = lean_ctor_get(v_toCold_1475_, 2);
v___x_1477_ = l_Lean_Option_get___at___00Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0_spec__3(v_options_1476_, v_opt_1472_);
v___x_1478_ = lean_box(v___x_1477_);
v___x_1479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1479_, 0, v___x_1478_);
return v___x_1479_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0___redArg___boxed(lean_object* v_opt_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_){
_start:
{
lean_object* v_res_1483_; 
v_res_1483_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0___redArg(v_opt_1480_, v___y_1481_);
lean_dec_ref(v___y_1481_);
lean_dec_ref(v_opt_1480_);
return v_res_1483_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1485_; lean_object* v___x_1486_; 
v___x_1485_ = ((lean_object*)(l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__0));
v___x_1486_ = l_Lean_stringToMessageData(v___x_1485_);
return v___x_1486_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__3(void){
_start:
{
lean_object* v___x_1488_; lean_object* v___x_1489_; 
v___x_1488_ = ((lean_object*)(l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__2));
v___x_1489_ = l_Lean_stringToMessageData(v___x_1488_);
return v___x_1489_;
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0(lean_object* v_id_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_){
_start:
{
lean_object* v___x_1494_; lean_object* v_env_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v_a_1498_; lean_object* v___x_1500_; uint8_t v_isShared_1501_; uint8_t v_isSharedCheck_1517_; 
v___x_1494_ = lean_st_ref_get(v___y_1492_);
v_env_1495_ = lean_ctor_get(v___x_1494_, 0);
lean_inc_ref(v_env_1495_);
lean_dec(v___x_1494_);
v___x_1496_ = l_Lean_ResolveName_backward_privateInPublic_warn;
v___x_1497_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0___redArg(v___x_1496_, v___y_1491_);
v_a_1498_ = lean_ctor_get(v___x_1497_, 0);
v_isSharedCheck_1517_ = !lean_is_exclusive(v___x_1497_);
if (v_isSharedCheck_1517_ == 0)
{
v___x_1500_ = v___x_1497_;
v_isShared_1501_ = v_isSharedCheck_1517_;
goto v_resetjp_1499_;
}
else
{
lean_inc(v_a_1498_);
lean_dec(v___x_1497_);
v___x_1500_ = lean_box(0);
v_isShared_1501_ = v_isSharedCheck_1517_;
goto v_resetjp_1499_;
}
v_resetjp_1499_:
{
uint8_t v_isExporting_1507_; 
v_isExporting_1507_ = lean_ctor_get_uint8(v_env_1495_, sizeof(void*)*8);
lean_dec_ref(v_env_1495_);
if (v_isExporting_1507_ == 0)
{
lean_dec(v_a_1498_);
lean_dec(v_id_1490_);
goto v___jp_1502_;
}
else
{
uint8_t v___x_1508_; 
v___x_1508_ = l_Lean_isPrivateName(v_id_1490_);
if (v___x_1508_ == 0)
{
lean_dec(v_a_1498_);
lean_dec(v_id_1490_);
goto v___jp_1502_;
}
else
{
uint8_t v___x_1509_; 
v___x_1509_ = lean_unbox(v_a_1498_);
lean_dec(v_a_1498_);
if (v___x_1509_ == 0)
{
lean_dec(v_id_1490_);
goto v___jp_1502_;
}
else
{
lean_object* v___x_1510_; uint8_t v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; 
lean_del_object(v___x_1500_);
v___x_1510_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__1, &l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__1_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__1);
v___x_1511_ = 0;
v___x_1512_ = l_Lean_MessageData_ofConstName(v_id_1490_, v___x_1511_);
v___x_1513_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1513_, 0, v___x_1510_);
lean_ctor_set(v___x_1513_, 1, v___x_1512_);
v___x_1514_ = lean_obj_once(&l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__3, &l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__3_once, _init_l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___closed__3);
v___x_1515_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1515_, 0, v___x_1513_);
lean_ctor_set(v___x_1515_, 1, v___x_1514_);
v___x_1516_ = l_Lean_logWarning___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__1(v___x_1515_, v___y_1491_, v___y_1492_);
return v___x_1516_;
}
}
}
v___jp_1502_:
{
lean_object* v___x_1503_; lean_object* v___x_1505_; 
v___x_1503_ = lean_box(0);
if (v_isShared_1501_ == 0)
{
lean_ctor_set(v___x_1500_, 0, v___x_1503_);
v___x_1505_ = v___x_1500_;
goto v_reusejp_1504_;
}
else
{
lean_object* v_reuseFailAlloc_1506_; 
v_reuseFailAlloc_1506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1506_, 0, v___x_1503_);
v___x_1505_ = v_reuseFailAlloc_1506_;
goto v_reusejp_1504_;
}
v_reusejp_1504_:
{
return v___x_1505_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0___boxed(lean_object* v_id_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_){
_start:
{
lean_object* v_res_1522_; 
v_res_1522_ = l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0(v_id_1518_, v___y_1519_, v___y_1520_);
lean_dec(v___y_1520_);
lean_dec_ref(v___y_1519_);
return v_res_1522_;
}
}
static lean_object* _init_l_Lean_ensureAttrDeclIsPublic___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1524_; lean_object* v___x_1525_; 
v___x_1524_ = ((lean_object*)(l_Lean_ensureAttrDeclIsPublic___lam__0___closed__0));
v___x_1525_ = l_Lean_stringToMessageData(v___x_1524_);
return v___x_1525_;
}
}
LEAN_EXPORT lean_object* l_Lean_ensureAttrDeclIsPublic___lam__0(lean_object* v_declName_1526_, uint8_t v_isModule_1527_, lean_object* v_attrName_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_){
_start:
{
lean_object* v___x_1532_; 
lean_inc(v_declName_1526_);
v___x_1532_ = l_Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0(v_declName_1526_, v___y_1529_, v___y_1530_);
if (lean_obj_tag(v___x_1532_) == 0)
{
lean_object* v___x_1533_; lean_object* v_a_1534_; lean_object* v___x_1536_; uint8_t v_isShared_1537_; uint8_t v_isSharedCheck_1554_; 
lean_dec_ref_known(v___x_1532_, 1);
lean_inc(v_declName_1526_);
v___x_1533_ = l_Lean_hasConst___at___00Lean_ensureAttrDeclIsPublic_spec__1___redArg(v_declName_1526_, v_isModule_1527_, v___y_1530_);
v_a_1534_ = lean_ctor_get(v___x_1533_, 0);
v_isSharedCheck_1554_ = !lean_is_exclusive(v___x_1533_);
if (v_isSharedCheck_1554_ == 0)
{
v___x_1536_ = v___x_1533_;
v_isShared_1537_ = v_isSharedCheck_1554_;
goto v_resetjp_1535_;
}
else
{
lean_inc(v_a_1534_);
lean_dec(v___x_1533_);
v___x_1536_ = lean_box(0);
v_isShared_1537_ = v_isSharedCheck_1554_;
goto v_resetjp_1535_;
}
v_resetjp_1535_:
{
uint8_t v___x_1538_; 
v___x_1538_ = lean_unbox(v_a_1534_);
if (v___x_1538_ == 0)
{
lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; uint8_t v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; 
lean_del_object(v___x_1536_);
v___x_1539_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1);
v___x_1540_ = l_Lean_MessageData_ofName(v_attrName_1528_);
v___x_1541_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1541_, 0, v___x_1539_);
lean_ctor_set(v___x_1541_, 1, v___x_1540_);
v___x_1542_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1, &l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1);
v___x_1543_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1543_, 0, v___x_1541_);
lean_ctor_set(v___x_1543_, 1, v___x_1542_);
v___x_1544_ = lean_unbox(v_a_1534_);
lean_dec(v_a_1534_);
v___x_1545_ = l_Lean_MessageData_ofConstName(v_declName_1526_, v___x_1544_);
v___x_1546_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1546_, 0, v___x_1543_);
lean_ctor_set(v___x_1546_, 1, v___x_1545_);
v___x_1547_ = lean_obj_once(&l_Lean_ensureAttrDeclIsPublic___lam__0___closed__1, &l_Lean_ensureAttrDeclIsPublic___lam__0___closed__1_once, _init_l_Lean_ensureAttrDeclIsPublic___lam__0___closed__1);
v___x_1548_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1548_, 0, v___x_1546_);
lean_ctor_set(v___x_1548_, 1, v___x_1547_);
v___x_1549_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_1548_, v___y_1529_, v___y_1530_);
return v___x_1549_;
}
else
{
lean_object* v___x_1550_; lean_object* v___x_1552_; 
lean_dec(v_a_1534_);
lean_dec(v_attrName_1528_);
lean_dec(v_declName_1526_);
v___x_1550_ = lean_box(0);
if (v_isShared_1537_ == 0)
{
lean_ctor_set(v___x_1536_, 0, v___x_1550_);
v___x_1552_ = v___x_1536_;
goto v_reusejp_1551_;
}
else
{
lean_object* v_reuseFailAlloc_1553_; 
v_reuseFailAlloc_1553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1553_, 0, v___x_1550_);
v___x_1552_ = v_reuseFailAlloc_1553_;
goto v_reusejp_1551_;
}
v_reusejp_1551_:
{
return v___x_1552_;
}
}
}
}
else
{
lean_dec(v_attrName_1528_);
lean_dec(v_declName_1526_);
return v___x_1532_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ensureAttrDeclIsPublic___lam__0___boxed(lean_object* v_declName_1555_, lean_object* v_isModule_1556_, lean_object* v_attrName_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_){
_start:
{
uint8_t v_isModule_boxed_1561_; lean_object* v_res_1562_; 
v_isModule_boxed_1561_ = lean_unbox(v_isModule_1556_);
v_res_1562_ = l_Lean_ensureAttrDeclIsPublic___lam__0(v_declName_1555_, v_isModule_boxed_1561_, v_attrName_1557_, v___y_1558_, v___y_1559_);
lean_dec(v___y_1559_);
lean_dec_ref(v___y_1558_);
return v_res_1562_;
}
}
LEAN_EXPORT lean_object* l_Lean_ensureAttrDeclIsPublic(lean_object* v_attrName_1563_, lean_object* v_declName_1564_, uint8_t v_attrKind_1565_, lean_object* v_a_1566_, lean_object* v_a_1567_){
_start:
{
lean_object* v___x_1569_; lean_object* v_env_1573_; lean_object* v___x_1574_; uint8_t v_isModule_1575_; 
v___x_1569_ = lean_st_ref_get(v_a_1567_);
v_env_1573_ = lean_ctor_get(v___x_1569_, 0);
lean_inc_ref(v_env_1573_);
lean_dec(v___x_1569_);
v___x_1574_ = l_Lean_Environment_header(v_env_1573_);
lean_dec_ref(v_env_1573_);
v_isModule_1575_ = lean_ctor_get_uint8(v___x_1574_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_1574_);
if (v_isModule_1575_ == 0)
{
lean_dec(v_declName_1564_);
lean_dec(v_attrName_1563_);
goto v___jp_1570_;
}
else
{
uint8_t v___x_1576_; uint8_t v___x_1577_; 
v___x_1576_ = 1;
v___x_1577_ = l_Lean_instBEqAttributeKind_beq(v_attrKind_1565_, v___x_1576_);
if (v___x_1577_ == 0)
{
lean_object* v___x_1578_; lean_object* v___f_1579_; lean_object* v___x_1580_; 
v___x_1578_ = lean_box(v_isModule_1575_);
v___f_1579_ = lean_alloc_closure((void*)(l_Lean_ensureAttrDeclIsPublic___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1579_, 0, v_declName_1564_);
lean_closure_set(v___f_1579_, 1, v___x_1578_);
lean_closure_set(v___f_1579_, 2, v_attrName_1563_);
v___x_1580_ = l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg(v___f_1579_, v_isModule_1575_, v_a_1566_, v_a_1567_);
return v___x_1580_;
}
else
{
lean_dec(v_declName_1564_);
lean_dec(v_attrName_1563_);
goto v___jp_1570_;
}
}
v___jp_1570_:
{
lean_object* v___x_1571_; lean_object* v___x_1572_; 
v___x_1571_ = lean_box(0);
v___x_1572_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1572_, 0, v___x_1571_);
return v___x_1572_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ensureAttrDeclIsPublic___boxed(lean_object* v_attrName_1581_, lean_object* v_declName_1582_, lean_object* v_attrKind_1583_, lean_object* v_a_1584_, lean_object* v_a_1585_, lean_object* v_a_1586_){
_start:
{
uint8_t v_attrKind_boxed_1587_; lean_object* v_res_1588_; 
v_attrKind_boxed_1587_ = lean_unbox(v_attrKind_1583_);
v_res_1588_ = l_Lean_ensureAttrDeclIsPublic(v_attrName_1581_, v_declName_1582_, v_attrKind_boxed_1587_, v_a_1584_, v_a_1585_);
lean_dec(v_a_1585_);
lean_dec_ref(v_a_1584_);
return v_res_1588_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0(lean_object* v_opt_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_){
_start:
{
lean_object* v___x_1593_; 
v___x_1593_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0___redArg(v_opt_1589_, v___y_1590_);
return v___x_1593_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0___boxed(lean_object* v_opt_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_){
_start:
{
lean_object* v_res_1598_; 
v_res_1598_ = l_Lean_Option_getM___at___00Lean_checkPrivateInPublic___at___00Lean_ensureAttrDeclIsPublic_spec__0_spec__0(v_opt_1594_, v___y_1595_, v___y_1596_);
lean_dec(v___y_1596_);
lean_dec_ref(v___y_1595_);
lean_dec_ref(v_opt_1594_);
return v_res_1598_;
}
}
static lean_object* _init_l_Lean_ensureAttrDeclIsMeta___closed__1(void){
_start:
{
lean_object* v___x_1600_; lean_object* v___x_1601_; 
v___x_1600_ = ((lean_object*)(l_Lean_ensureAttrDeclIsMeta___closed__0));
v___x_1601_ = l_Lean_stringToMessageData(v___x_1600_);
return v___x_1601_;
}
}
LEAN_EXPORT lean_object* l_Lean_ensureAttrDeclIsMeta(lean_object* v_attrName_1602_, lean_object* v_declName_1603_, uint8_t v_attrKind_1604_, lean_object* v_a_1605_, lean_object* v_a_1606_){
_start:
{
lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v_env_1610_; lean_object* v___x_1611_; uint8_t v_isModule_1612_; 
v___x_1608_ = lean_st_ref_get(v_a_1606_);
v___x_1609_ = lean_st_ref_get(v_a_1606_);
v_env_1610_ = lean_ctor_get(v___x_1608_, 0);
lean_inc_ref(v_env_1610_);
lean_dec(v___x_1608_);
v___x_1611_ = l_Lean_Environment_header(v_env_1610_);
lean_dec_ref(v_env_1610_);
v_isModule_1612_ = lean_ctor_get_uint8(v___x_1611_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_1611_);
if (v_isModule_1612_ == 0)
{
lean_object* v___x_1613_; 
lean_dec(v___x_1609_);
v___x_1613_ = l_Lean_ensureAttrDeclIsPublic(v_attrName_1602_, v_declName_1603_, v_attrKind_1604_, v_a_1605_, v_a_1606_);
return v___x_1613_;
}
else
{
lean_object* v_env_1614_; uint8_t v___x_1615_; 
v_env_1614_ = lean_ctor_get(v___x_1609_, 0);
lean_inc_ref(v_env_1614_);
lean_dec(v___x_1609_);
lean_inc(v_declName_1603_);
v___x_1615_ = l_Lean_isMarkedMeta(v_env_1614_, v_declName_1603_);
if (v___x_1615_ == 0)
{
lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; 
v___x_1616_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1);
v___x_1617_ = l_Lean_MessageData_ofName(v_attrName_1602_);
v___x_1618_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1618_, 0, v___x_1616_);
lean_ctor_set(v___x_1618_, 1, v___x_1617_);
v___x_1619_ = lean_obj_once(&l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1, &l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1_once, _init_l_Lean_throwAttrDeclNotOfExpectedType___redArg___closed__1);
v___x_1620_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1620_, 0, v___x_1618_);
lean_ctor_set(v___x_1620_, 1, v___x_1619_);
v___x_1621_ = l_Lean_MessageData_ofConstName(v_declName_1603_, v___x_1615_);
v___x_1622_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1622_, 0, v___x_1620_);
lean_ctor_set(v___x_1622_, 1, v___x_1621_);
v___x_1623_ = lean_obj_once(&l_Lean_ensureAttrDeclIsMeta___closed__1, &l_Lean_ensureAttrDeclIsMeta___closed__1_once, _init_l_Lean_ensureAttrDeclIsMeta___closed__1);
v___x_1624_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1624_, 0, v___x_1622_);
lean_ctor_set(v___x_1624_, 1, v___x_1623_);
v___x_1625_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_1624_, v_a_1605_, v_a_1606_);
return v___x_1625_;
}
else
{
lean_object* v___x_1626_; 
v___x_1626_ = l_Lean_ensureAttrDeclIsPublic(v_attrName_1602_, v_declName_1603_, v_attrKind_1604_, v_a_1605_, v_a_1606_);
return v___x_1626_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ensureAttrDeclIsMeta___boxed(lean_object* v_attrName_1627_, lean_object* v_declName_1628_, lean_object* v_attrKind_1629_, lean_object* v_a_1630_, lean_object* v_a_1631_, lean_object* v_a_1632_){
_start:
{
uint8_t v_attrKind_boxed_1633_; lean_object* v_res_1634_; 
v_attrKind_boxed_1633_ = lean_unbox(v_attrKind_1629_);
v_res_1634_ = l_Lean_ensureAttrDeclIsMeta(v_attrName_1627_, v_declName_1628_, v_attrKind_boxed_1633_, v_a_1630_, v_a_1631_);
lean_dec(v_a_1631_);
lean_dec_ref(v_a_1630_);
return v_res_1634_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__0(lean_object* v_x_1638_, lean_object* v___y_1639_){
_start:
{
lean_object* v___x_1641_; lean_object* v___x_1642_; 
v___x_1641_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___lam__0___closed__1));
v___x_1642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1642_, 0, v___x_1641_);
return v___x_1642_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__0___boxed(lean_object* v_x_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_){
_start:
{
lean_object* v_res_1646_; 
v_res_1646_ = l_Lean_instInhabitedTagAttribute_default___lam__0(v_x_1643_, v___y_1644_);
lean_dec_ref(v___y_1644_);
lean_dec_ref(v_x_1643_);
return v_res_1646_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__1(lean_object* v_s_1647_, lean_object* v_x_1648_){
_start:
{
lean_inc(v_s_1647_);
return v_s_1647_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__1___boxed(lean_object* v_s_1649_, lean_object* v_x_1650_){
_start:
{
lean_object* v_res_1651_; 
v_res_1651_ = l_Lean_instInhabitedTagAttribute_default___lam__1(v_s_1649_, v_x_1650_);
lean_dec(v_x_1650_);
lean_dec(v_s_1649_);
return v_res_1651_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__2(lean_object* v_x_1656_, lean_object* v_x_1657_){
_start:
{
lean_object* v___x_1658_; 
v___x_1658_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___lam__2___closed__1));
return v___x_1658_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__2___boxed(lean_object* v_x_1659_, lean_object* v_x_1660_){
_start:
{
lean_object* v_res_1661_; 
v_res_1661_ = l_Lean_instInhabitedTagAttribute_default___lam__2(v_x_1659_, v_x_1660_);
lean_dec(v_x_1660_);
lean_dec_ref(v_x_1659_);
return v_res_1661_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__3(lean_object* v_x_1662_){
_start:
{
lean_object* v___x_1663_; 
v___x_1663_ = lean_box(0);
return v___x_1663_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedTagAttribute_default___lam__3___boxed(lean_object* v_x_1664_){
_start:
{
lean_object* v_res_1665_; 
v_res_1665_ = l_Lean_instInhabitedTagAttribute_default___lam__3(v_x_1664_);
lean_dec(v_x_1664_);
return v_res_1665_;
}
}
static lean_object* _init_l_Lean_instInhabitedTagAttribute_default___closed__4(void){
_start:
{
lean_object* v___x_1670_; 
v___x_1670_ = l_Lean_instInhabitedEnvExtension_default(lean_box(0));
return v___x_1670_;
}
}
static lean_object* _init_l_Lean_instInhabitedTagAttribute_default___closed__5(void){
_start:
{
lean_object* v___f_1671_; lean_object* v___f_1672_; lean_object* v___f_1673_; lean_object* v___f_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; 
v___f_1671_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___closed__3));
v___f_1672_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___closed__2));
v___f_1673_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___closed__1));
v___f_1674_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___closed__0));
v___x_1675_ = lean_box(0);
v___x_1676_ = lean_obj_once(&l_Lean_instInhabitedTagAttribute_default___closed__4, &l_Lean_instInhabitedTagAttribute_default___closed__4_once, _init_l_Lean_instInhabitedTagAttribute_default___closed__4);
v___x_1677_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1677_, 0, v___x_1676_);
lean_ctor_set(v___x_1677_, 1, v___x_1675_);
lean_ctor_set(v___x_1677_, 2, v___f_1674_);
lean_ctor_set(v___x_1677_, 3, v___f_1673_);
lean_ctor_set(v___x_1677_, 4, v___f_1672_);
lean_ctor_set(v___x_1677_, 5, v___f_1671_);
return v___x_1677_;
}
}
static lean_object* _init_l_Lean_instInhabitedTagAttribute_default___closed__6(void){
_start:
{
lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; 
v___x_1678_ = lean_obj_once(&l_Lean_instInhabitedTagAttribute_default___closed__5, &l_Lean_instInhabitedTagAttribute_default___closed__5_once, _init_l_Lean_instInhabitedTagAttribute_default___closed__5);
v___x_1679_ = ((lean_object*)(l_Lean_instInhabitedAttributeImpl_default));
v___x_1680_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1680_, 0, v___x_1679_);
lean_ctor_set(v___x_1680_, 1, v___x_1678_);
return v___x_1680_;
}
}
static lean_object* _init_l_Lean_instInhabitedTagAttribute_default(void){
_start:
{
lean_object* v___x_1681_; 
v___x_1681_ = lean_obj_once(&l_Lean_instInhabitedTagAttribute_default___closed__6, &l_Lean_instInhabitedTagAttribute_default___closed__6_once, _init_l_Lean_instInhabitedTagAttribute_default___closed__6);
return v___x_1681_;
}
}
static lean_object* _init_l_Lean_instInhabitedTagAttribute(void){
_start:
{
lean_object* v___x_1682_; 
v___x_1682_ = l_Lean_instInhabitedTagAttribute_default;
return v___x_1682_;
}
}
static lean_object* _init_l_Lean_registerTagAttribute___auto__1(void){
_start:
{
lean_object* v___x_1683_; 
v___x_1683_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__28, &l_Lean_AttributeImplCore_ref___autoParam___closed__28_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__28);
return v___x_1683_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__0(lean_object* v_x_1684_){
_start:
{
lean_object* v___x_1685_; 
v___x_1685_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___lam__2___closed__0));
return v___x_1685_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__0___boxed(lean_object* v_x_1686_){
_start:
{
lean_object* v_res_1687_; 
v_res_1687_ = l_Lean_registerTagAttribute___lam__0(v_x_1686_);
lean_dec(v_x_1686_);
return v_res_1687_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerTagAttribute_spec__0(lean_object* v_newState_1688_, lean_object* v_x_1689_, lean_object* v_x_1690_){
_start:
{
if (lean_obj_tag(v_x_1690_) == 0)
{
return v_x_1689_;
}
else
{
lean_object* v_head_1691_; lean_object* v_tail_1692_; uint8_t v___x_1693_; 
v_head_1691_ = lean_ctor_get(v_x_1690_, 0);
lean_inc(v_head_1691_);
v_tail_1692_ = lean_ctor_get(v_x_1690_, 1);
lean_inc(v_tail_1692_);
lean_dec_ref_known(v_x_1690_, 2);
v___x_1693_ = l_Lean_NameSet_contains(v_newState_1688_, v_head_1691_);
if (v___x_1693_ == 0)
{
lean_dec(v_head_1691_);
v_x_1690_ = v_tail_1692_;
goto _start;
}
else
{
lean_object* v___x_1695_; 
v___x_1695_ = l_Lean_NameSet_insert(v_x_1689_, v_head_1691_);
v_x_1689_ = v___x_1695_;
v_x_1690_ = v_tail_1692_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerTagAttribute_spec__0___boxed(lean_object* v_newState_1697_, lean_object* v_x_1698_, lean_object* v_x_1699_){
_start:
{
lean_object* v_res_1700_; 
v_res_1700_ = l_List_foldl___at___00Lean_registerTagAttribute_spec__0(v_newState_1697_, v_x_1698_, v_x_1699_);
lean_dec(v_newState_1697_);
return v_res_1700_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__1(lean_object* v_x_1701_, lean_object* v_newState_1702_, lean_object* v_newConsts_1703_, lean_object* v_s_1704_){
_start:
{
lean_object* v___x_1705_; 
v___x_1705_ = l_List_foldl___at___00Lean_registerTagAttribute_spec__0(v_newState_1702_, v_s_1704_, v_newConsts_1703_);
return v___x_1705_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__1___boxed(lean_object* v_x_1706_, lean_object* v_newState_1707_, lean_object* v_newConsts_1708_, lean_object* v_s_1709_){
_start:
{
lean_object* v_res_1710_; 
v_res_1710_ = l_Lean_registerTagAttribute___lam__1(v_x_1706_, v_newState_1707_, v_newConsts_1708_, v_s_1709_);
lean_dec(v_newState_1707_);
lean_dec(v_x_1706_);
return v_res_1710_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__2(lean_object* v_s_1723_){
_start:
{
lean_object* v___x_1724_; lean_object* v___y_1726_; 
v___x_1724_ = ((lean_object*)(l_Lean_registerTagAttribute___lam__2___closed__5));
if (lean_obj_tag(v_s_1723_) == 0)
{
lean_object* v_size_1730_; 
v_size_1730_ = lean_ctor_get(v_s_1723_, 0);
lean_inc(v_size_1730_);
lean_dec_ref_known(v_s_1723_, 5);
v___y_1726_ = v_size_1730_;
goto v___jp_1725_;
}
else
{
lean_object* v___x_1731_; 
v___x_1731_ = lean_unsigned_to_nat(0u);
v___y_1726_ = v___x_1731_;
goto v___jp_1725_;
}
v___jp_1725_:
{
lean_object* v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; 
v___x_1727_ = l_Nat_reprFast(v___y_1726_);
v___x_1728_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1728_, 0, v___x_1727_);
v___x_1729_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1729_, 0, v___x_1724_);
lean_ctor_set(v___x_1729_, 1, v___x_1728_);
return v___x_1729_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4___redArg(lean_object* v_hi_1732_, lean_object* v_pivot_1733_, lean_object* v_as_1734_, lean_object* v_i_1735_, lean_object* v_k_1736_){
_start:
{
uint8_t v___x_1737_; 
v___x_1737_ = lean_nat_dec_lt(v_k_1736_, v_hi_1732_);
if (v___x_1737_ == 0)
{
lean_object* v___x_1738_; lean_object* v___x_1739_; 
lean_dec(v_k_1736_);
v___x_1738_ = lean_array_fswap(v_as_1734_, v_i_1735_, v_hi_1732_);
v___x_1739_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1739_, 0, v_i_1735_);
lean_ctor_set(v___x_1739_, 1, v___x_1738_);
return v___x_1739_;
}
else
{
lean_object* v___x_1740_; uint8_t v___x_1741_; 
v___x_1740_ = lean_array_fget_borrowed(v_as_1734_, v_k_1736_);
v___x_1741_ = l_Lean_Name_quickLt(v___x_1740_, v_pivot_1733_);
if (v___x_1741_ == 0)
{
lean_object* v___x_1742_; lean_object* v___x_1743_; 
v___x_1742_ = lean_unsigned_to_nat(1u);
v___x_1743_ = lean_nat_add(v_k_1736_, v___x_1742_);
lean_dec(v_k_1736_);
v_k_1736_ = v___x_1743_;
goto _start;
}
else
{
lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; 
v___x_1745_ = lean_array_fswap(v_as_1734_, v_i_1735_, v_k_1736_);
v___x_1746_ = lean_unsigned_to_nat(1u);
v___x_1747_ = lean_nat_add(v_i_1735_, v___x_1746_);
lean_dec(v_i_1735_);
v___x_1748_ = lean_nat_add(v_k_1736_, v___x_1746_);
lean_dec(v_k_1736_);
v_as_1734_ = v___x_1745_;
v_i_1735_ = v___x_1747_;
v_k_1736_ = v___x_1748_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4___redArg___boxed(lean_object* v_hi_1750_, lean_object* v_pivot_1751_, lean_object* v_as_1752_, lean_object* v_i_1753_, lean_object* v_k_1754_){
_start:
{
lean_object* v_res_1755_; 
v_res_1755_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4___redArg(v_hi_1750_, v_pivot_1751_, v_as_1752_, v_i_1753_, v_k_1754_);
lean_dec(v_pivot_1751_);
lean_dec(v_hi_1750_);
return v_res_1755_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___redArg(lean_object* v_n_1756_, lean_object* v_as_1757_, lean_object* v_lo_1758_, lean_object* v_hi_1759_){
_start:
{
lean_object* v___y_1761_; uint8_t v___x_1771_; 
v___x_1771_ = lean_nat_dec_lt(v_lo_1758_, v_hi_1759_);
if (v___x_1771_ == 0)
{
lean_dec(v_lo_1758_);
return v_as_1757_;
}
else
{
lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v_mid_1774_; lean_object* v___y_1776_; lean_object* v___y_1782_; lean_object* v___x_1787_; lean_object* v___x_1788_; uint8_t v___x_1789_; 
v___x_1772_ = lean_nat_add(v_lo_1758_, v_hi_1759_);
v___x_1773_ = lean_unsigned_to_nat(1u);
v_mid_1774_ = lean_nat_shiftr(v___x_1772_, v___x_1773_);
lean_dec(v___x_1772_);
v___x_1787_ = lean_array_fget_borrowed(v_as_1757_, v_mid_1774_);
v___x_1788_ = lean_array_fget_borrowed(v_as_1757_, v_lo_1758_);
v___x_1789_ = l_Lean_Name_quickLt(v___x_1787_, v___x_1788_);
if (v___x_1789_ == 0)
{
v___y_1782_ = v_as_1757_;
goto v___jp_1781_;
}
else
{
lean_object* v___x_1790_; 
v___x_1790_ = lean_array_fswap(v_as_1757_, v_lo_1758_, v_mid_1774_);
v___y_1782_ = v___x_1790_;
goto v___jp_1781_;
}
v___jp_1775_:
{
lean_object* v___x_1777_; lean_object* v___x_1778_; uint8_t v___x_1779_; 
v___x_1777_ = lean_array_fget_borrowed(v___y_1776_, v_mid_1774_);
v___x_1778_ = lean_array_fget_borrowed(v___y_1776_, v_hi_1759_);
v___x_1779_ = l_Lean_Name_quickLt(v___x_1777_, v___x_1778_);
if (v___x_1779_ == 0)
{
lean_dec(v_mid_1774_);
v___y_1761_ = v___y_1776_;
goto v___jp_1760_;
}
else
{
lean_object* v___x_1780_; 
v___x_1780_ = lean_array_fswap(v___y_1776_, v_mid_1774_, v_hi_1759_);
lean_dec(v_mid_1774_);
v___y_1761_ = v___x_1780_;
goto v___jp_1760_;
}
}
v___jp_1781_:
{
lean_object* v___x_1783_; lean_object* v___x_1784_; uint8_t v___x_1785_; 
v___x_1783_ = lean_array_fget_borrowed(v___y_1782_, v_hi_1759_);
v___x_1784_ = lean_array_fget_borrowed(v___y_1782_, v_lo_1758_);
v___x_1785_ = l_Lean_Name_quickLt(v___x_1783_, v___x_1784_);
if (v___x_1785_ == 0)
{
v___y_1776_ = v___y_1782_;
goto v___jp_1775_;
}
else
{
lean_object* v___x_1786_; 
v___x_1786_ = lean_array_fswap(v___y_1782_, v_lo_1758_, v_hi_1759_);
v___y_1776_ = v___x_1786_;
goto v___jp_1775_;
}
}
}
v___jp_1760_:
{
lean_object* v_pivot_1762_; lean_object* v___x_1763_; lean_object* v_fst_1764_; lean_object* v_snd_1765_; uint8_t v___x_1766_; 
v_pivot_1762_ = lean_array_fget(v___y_1761_, v_hi_1759_);
lean_inc_n(v_lo_1758_, 2);
v___x_1763_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4___redArg(v_hi_1759_, v_pivot_1762_, v___y_1761_, v_lo_1758_, v_lo_1758_);
lean_dec(v_pivot_1762_);
v_fst_1764_ = lean_ctor_get(v___x_1763_, 0);
lean_inc(v_fst_1764_);
v_snd_1765_ = lean_ctor_get(v___x_1763_, 1);
lean_inc(v_snd_1765_);
lean_dec_ref(v___x_1763_);
v___x_1766_ = lean_nat_dec_le(v_hi_1759_, v_fst_1764_);
if (v___x_1766_ == 0)
{
lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; 
v___x_1767_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___redArg(v_n_1756_, v_snd_1765_, v_lo_1758_, v_fst_1764_);
v___x_1768_ = lean_unsigned_to_nat(1u);
v___x_1769_ = lean_nat_add(v_fst_1764_, v___x_1768_);
lean_dec(v_fst_1764_);
v_as_1757_ = v___x_1767_;
v_lo_1758_ = v___x_1769_;
goto _start;
}
else
{
lean_dec(v_fst_1764_);
lean_dec(v_lo_1758_);
return v_snd_1765_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___redArg___boxed(lean_object* v_n_1791_, lean_object* v_as_1792_, lean_object* v_lo_1793_, lean_object* v_hi_1794_){
_start:
{
lean_object* v_res_1795_; 
v_res_1795_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___redArg(v_n_1791_, v_as_1792_, v_lo_1793_, v_hi_1794_);
lean_dec(v_hi_1794_);
lean_dec(v_n_1791_);
return v_res_1795_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerTagAttribute_spec__2(lean_object* v_env_1796_, lean_object* v_as_1797_, size_t v_i_1798_, size_t v_stop_1799_, lean_object* v_b_1800_){
_start:
{
lean_object* v___y_1802_; uint8_t v___x_1806_; 
v___x_1806_ = lean_usize_dec_eq(v_i_1798_, v_stop_1799_);
if (v___x_1806_ == 0)
{
lean_object* v___x_1807_; uint8_t v___x_1808_; lean_object* v___x_1809_; uint8_t v___x_1810_; 
v___x_1807_ = lean_array_uget_borrowed(v_as_1797_, v_i_1798_);
v___x_1808_ = 1;
lean_inc_ref(v_env_1796_);
v___x_1809_ = l_Lean_Environment_setExporting(v_env_1796_, v___x_1808_);
lean_inc(v___x_1807_);
v___x_1810_ = l_Lean_Environment_contains(v___x_1809_, v___x_1807_, v___x_1806_);
if (v___x_1810_ == 0)
{
v___y_1802_ = v_b_1800_;
goto v___jp_1801_;
}
else
{
lean_object* v___x_1811_; 
lean_inc(v___x_1807_);
v___x_1811_ = lean_array_push(v_b_1800_, v___x_1807_);
v___y_1802_ = v___x_1811_;
goto v___jp_1801_;
}
}
else
{
lean_dec_ref(v_env_1796_);
return v_b_1800_;
}
v___jp_1801_:
{
size_t v___x_1803_; size_t v___x_1804_; 
v___x_1803_ = ((size_t)1ULL);
v___x_1804_ = lean_usize_add(v_i_1798_, v___x_1803_);
v_i_1798_ = v___x_1804_;
v_b_1800_ = v___y_1802_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerTagAttribute_spec__2___boxed(lean_object* v_env_1812_, lean_object* v_as_1813_, lean_object* v_i_1814_, lean_object* v_stop_1815_, lean_object* v_b_1816_){
_start:
{
size_t v_i_boxed_1817_; size_t v_stop_boxed_1818_; lean_object* v_res_1819_; 
v_i_boxed_1817_ = lean_unbox_usize(v_i_1814_);
lean_dec(v_i_1814_);
v_stop_boxed_1818_ = lean_unbox_usize(v_stop_1815_);
lean_dec(v_stop_1815_);
v_res_1819_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerTagAttribute_spec__2(v_env_1812_, v_as_1813_, v_i_boxed_1817_, v_stop_boxed_1818_, v_b_1816_);
lean_dec_ref(v_as_1813_);
return v_res_1819_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerTagAttribute_spec__1_spec__1(lean_object* v_init_1820_, lean_object* v_x_1821_){
_start:
{
if (lean_obj_tag(v_x_1821_) == 0)
{
lean_object* v_k_1822_; lean_object* v_l_1823_; lean_object* v_r_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; 
v_k_1822_ = lean_ctor_get(v_x_1821_, 1);
lean_inc(v_k_1822_);
v_l_1823_ = lean_ctor_get(v_x_1821_, 3);
lean_inc(v_l_1823_);
v_r_1824_ = lean_ctor_get(v_x_1821_, 4);
lean_inc(v_r_1824_);
lean_dec_ref_known(v_x_1821_, 5);
v___x_1825_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerTagAttribute_spec__1_spec__1(v_init_1820_, v_l_1823_);
v___x_1826_ = lean_array_push(v___x_1825_, v_k_1822_);
v_init_1820_ = v___x_1826_;
v_x_1821_ = v_r_1824_;
goto _start;
}
else
{
return v_init_1820_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__3(lean_object* v_env_1828_, lean_object* v_es_1829_){
_start:
{
lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___y_1833_; lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___y_1850_; lean_object* v___y_1851_; uint8_t v___x_1853_; 
v___x_1830_ = lean_unsigned_to_nat(0u);
v___x_1831_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___lam__2___closed__0));
v___x_1847_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerTagAttribute_spec__1_spec__1(v___x_1831_, v_es_1829_);
v___x_1848_ = lean_array_get_size(v___x_1847_);
v___x_1853_ = lean_nat_dec_eq(v___x_1848_, v___x_1830_);
if (v___x_1853_ == 0)
{
lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___y_1857_; uint8_t v___x_1859_; 
v___x_1854_ = lean_unsigned_to_nat(1u);
v___x_1855_ = lean_nat_sub(v___x_1848_, v___x_1854_);
v___x_1859_ = lean_nat_dec_le(v___x_1830_, v___x_1855_);
if (v___x_1859_ == 0)
{
lean_inc(v___x_1855_);
v___y_1857_ = v___x_1855_;
goto v___jp_1856_;
}
else
{
v___y_1857_ = v___x_1830_;
goto v___jp_1856_;
}
v___jp_1856_:
{
uint8_t v___x_1858_; 
v___x_1858_ = lean_nat_dec_le(v___y_1857_, v___x_1855_);
if (v___x_1858_ == 0)
{
lean_dec(v___x_1855_);
lean_inc(v___y_1857_);
v___y_1850_ = v___y_1857_;
v___y_1851_ = v___y_1857_;
goto v___jp_1849_;
}
else
{
v___y_1850_ = v___y_1857_;
v___y_1851_ = v___x_1855_;
goto v___jp_1849_;
}
}
}
else
{
v___y_1833_ = v___x_1847_;
goto v___jp_1832_;
}
v___jp_1832_:
{
lean_object* v___x_1834_; uint8_t v___x_1835_; 
v___x_1834_ = lean_array_get_size(v___y_1833_);
v___x_1835_ = lean_nat_dec_lt(v___x_1830_, v___x_1834_);
if (v___x_1835_ == 0)
{
lean_object* v___x_1836_; 
lean_dec_ref(v_env_1828_);
v___x_1836_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1836_, 0, v___x_1831_);
lean_ctor_set(v___x_1836_, 1, v___x_1831_);
lean_ctor_set(v___x_1836_, 2, v___y_1833_);
return v___x_1836_;
}
else
{
uint8_t v___x_1837_; 
v___x_1837_ = lean_nat_dec_le(v___x_1834_, v___x_1834_);
if (v___x_1837_ == 0)
{
if (v___x_1835_ == 0)
{
lean_object* v___x_1838_; 
lean_dec_ref(v_env_1828_);
v___x_1838_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1838_, 0, v___x_1831_);
lean_ctor_set(v___x_1838_, 1, v___x_1831_);
lean_ctor_set(v___x_1838_, 2, v___y_1833_);
return v___x_1838_;
}
else
{
size_t v___x_1839_; size_t v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; 
v___x_1839_ = ((size_t)0ULL);
v___x_1840_ = lean_usize_of_nat(v___x_1834_);
v___x_1841_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerTagAttribute_spec__2(v_env_1828_, v___y_1833_, v___x_1839_, v___x_1840_, v___x_1831_);
lean_inc_ref(v___x_1841_);
v___x_1842_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1842_, 0, v___x_1841_);
lean_ctor_set(v___x_1842_, 1, v___x_1841_);
lean_ctor_set(v___x_1842_, 2, v___y_1833_);
return v___x_1842_;
}
}
else
{
size_t v___x_1843_; size_t v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; 
v___x_1843_ = ((size_t)0ULL);
v___x_1844_ = lean_usize_of_nat(v___x_1834_);
v___x_1845_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerTagAttribute_spec__2(v_env_1828_, v___y_1833_, v___x_1843_, v___x_1844_, v___x_1831_);
lean_inc_ref(v___x_1845_);
v___x_1846_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1846_, 0, v___x_1845_);
lean_ctor_set(v___x_1846_, 1, v___x_1845_);
lean_ctor_set(v___x_1846_, 2, v___y_1833_);
return v___x_1846_;
}
}
}
v___jp_1849_:
{
lean_object* v___x_1852_; 
v___x_1852_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___redArg(v___x_1848_, v___x_1847_, v___y_1850_, v___y_1851_);
lean_dec(v___y_1851_);
v___y_1833_ = v___x_1852_;
goto v___jp_1832_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__4(lean_object* v___x_1860_, lean_object* v_x_1861_, lean_object* v_x_1862_){
_start:
{
lean_object* v___x_1864_; 
v___x_1864_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1864_, 0, v___x_1860_);
return v___x_1864_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__4___boxed(lean_object* v___x_1865_, lean_object* v_x_1866_, lean_object* v_x_1867_, lean_object* v___y_1868_){
_start:
{
lean_object* v_res_1869_; 
v_res_1869_ = l_Lean_registerTagAttribute___lam__4(v___x_1865_, v_x_1866_, v_x_1867_);
lean_dec_ref(v_x_1867_);
lean_dec_ref(v_x_1866_);
return v_res_1869_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__5(lean_object* v___x_1870_){
_start:
{
lean_object* v___x_1872_; 
v___x_1872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1872_, 0, v___x_1870_);
return v___x_1872_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__5___boxed(lean_object* v___x_1873_, lean_object* v___y_1874_){
_start:
{
lean_object* v_res_1875_; 
v_res_1875_ = l_Lean_registerTagAttribute___lam__5(v___x_1873_);
return v_res_1875_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__6(lean_object* v_name_1876_, lean_object* v_decl_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_){
_start:
{
lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; 
v___x_1881_ = lean_obj_once(&l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1, &l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1_once, _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1);
v___x_1882_ = l_Lean_MessageData_ofName(v_name_1876_);
v___x_1883_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1883_, 0, v___x_1881_);
lean_ctor_set(v___x_1883_, 1, v___x_1882_);
v___x_1884_ = lean_obj_once(&l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3, &l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3_once, _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3);
v___x_1885_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1885_, 0, v___x_1883_);
lean_ctor_set(v___x_1885_, 1, v___x_1884_);
v___x_1886_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_1885_, v___y_1878_, v___y_1879_);
return v___x_1886_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__6___boxed(lean_object* v_name_1887_, lean_object* v_decl_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_){
_start:
{
lean_object* v_res_1892_; 
v_res_1892_ = l_Lean_registerTagAttribute___lam__6(v_name_1887_, v_decl_1888_, v___y_1889_, v___y_1890_);
lean_dec(v___y_1890_);
lean_dec_ref(v___y_1889_);
lean_dec(v_decl_1888_);
return v_res_1892_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg(lean_object* v_attrName_1893_, lean_object* v_declName_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_){
_start:
{
lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; uint8_t v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; 
v___x_1898_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1);
v___x_1899_ = l_Lean_MessageData_ofName(v_attrName_1893_);
v___x_1900_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1900_, 0, v___x_1898_);
lean_ctor_set(v___x_1900_, 1, v___x_1899_);
v___x_1901_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__3, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__3_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__3);
v___x_1902_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1902_, 0, v___x_1900_);
lean_ctor_set(v___x_1902_, 1, v___x_1901_);
v___x_1903_ = 0;
v___x_1904_ = l_Lean_MessageData_ofConstName(v_declName_1894_, v___x_1903_);
v___x_1905_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1905_, 0, v___x_1902_);
lean_ctor_set(v___x_1905_, 1, v___x_1904_);
v___x_1906_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__5, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__5_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__5);
v___x_1907_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1907_, 0, v___x_1905_);
lean_ctor_set(v___x_1907_, 1, v___x_1906_);
v___x_1908_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_1907_, v___y_1895_, v___y_1896_);
return v___x_1908_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg___boxed(lean_object* v_attrName_1909_, lean_object* v_declName_1910_, lean_object* v___y_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_){
_start:
{
lean_object* v_res_1914_; 
v_res_1914_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg(v_attrName_1909_, v_declName_1910_, v___y_1911_, v___y_1912_);
lean_dec(v___y_1912_);
lean_dec_ref(v___y_1911_);
return v_res_1914_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___redArg(lean_object* v_attrName_1915_, lean_object* v_declName_1916_, lean_object* v_asyncPrefix_x3f_1917_, lean_object* v___y_1918_, lean_object* v___y_1919_){
_start:
{
lean_object* v___y_1922_; 
if (lean_obj_tag(v_asyncPrefix_x3f_1917_) == 0)
{
lean_object* v___x_1935_; 
v___x_1935_ = l_Lean_MessageData_nil;
v___y_1922_ = v___x_1935_;
goto v___jp_1921_;
}
else
{
lean_object* v_val_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; 
v_val_1936_ = lean_ctor_get(v_asyncPrefix_x3f_1917_, 0);
lean_inc(v_val_1936_);
lean_dec_ref_known(v_asyncPrefix_x3f_1917_, 1);
v___x_1937_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___redArg___closed__3, &l_Lean_throwAttrNotInAsyncCtx___redArg___closed__3_once, _init_l_Lean_throwAttrNotInAsyncCtx___redArg___closed__3);
v___x_1938_ = l_Lean_MessageData_ofName(v_val_1936_);
v___x_1939_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1939_, 0, v___x_1937_);
lean_ctor_set(v___x_1939_, 1, v___x_1938_);
v___x_1940_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__5, &l_Lean_throwAttrMustBeGlobal___redArg___closed__5_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__5);
v___x_1941_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1941_, 0, v___x_1939_);
lean_ctor_set(v___x_1941_, 1, v___x_1940_);
v___y_1922_ = v___x_1941_;
goto v___jp_1921_;
}
v___jp_1921_:
{
lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; uint8_t v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; 
v___x_1923_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__1, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__1_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__1);
v___x_1924_ = l_Lean_MessageData_ofName(v_attrName_1915_);
v___x_1925_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1925_, 0, v___x_1923_);
lean_ctor_set(v___x_1925_, 1, v___x_1924_);
v___x_1926_ = lean_obj_once(&l_Lean_throwAttrDeclInImportedModule___redArg___closed__3, &l_Lean_throwAttrDeclInImportedModule___redArg___closed__3_once, _init_l_Lean_throwAttrDeclInImportedModule___redArg___closed__3);
v___x_1927_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1927_, 0, v___x_1925_);
lean_ctor_set(v___x_1927_, 1, v___x_1926_);
v___x_1928_ = 0;
v___x_1929_ = l_Lean_MessageData_ofConstName(v_declName_1916_, v___x_1928_);
v___x_1930_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1930_, 0, v___x_1927_);
lean_ctor_set(v___x_1930_, 1, v___x_1929_);
v___x_1931_ = lean_obj_once(&l_Lean_throwAttrNotInAsyncCtx___redArg___closed__1, &l_Lean_throwAttrNotInAsyncCtx___redArg___closed__1_once, _init_l_Lean_throwAttrNotInAsyncCtx___redArg___closed__1);
v___x_1932_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1932_, 0, v___x_1930_);
lean_ctor_set(v___x_1932_, 1, v___x_1931_);
v___x_1933_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1933_, 0, v___x_1932_);
lean_ctor_set(v___x_1933_, 1, v___y_1922_);
v___x_1934_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_1933_, v___y_1918_, v___y_1919_);
return v___x_1934_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___redArg___boxed(lean_object* v_attrName_1942_, lean_object* v_declName_1943_, lean_object* v_asyncPrefix_x3f_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_){
_start:
{
lean_object* v_res_1948_; 
v_res_1948_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___redArg(v_attrName_1942_, v_declName_1943_, v_asyncPrefix_x3f_1944_, v___y_1945_, v___y_1946_);
lean_dec(v___y_1946_);
lean_dec_ref(v___y_1945_);
return v_res_1948_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg(lean_object* v_name_1949_, uint8_t v_kind_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_){
_start:
{
lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; lean_object* v___y_1960_; 
v___x_1954_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__1, &l_Lean_throwAttrMustBeGlobal___redArg___closed__1_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__1);
v___x_1955_ = l_Lean_MessageData_ofName(v_name_1949_);
v___x_1956_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1956_, 0, v___x_1954_);
lean_ctor_set(v___x_1956_, 1, v___x_1955_);
v___x_1957_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__3, &l_Lean_throwAttrMustBeGlobal___redArg___closed__3_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__3);
v___x_1958_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1958_, 0, v___x_1956_);
lean_ctor_set(v___x_1958_, 1, v___x_1957_);
switch(v_kind_1950_)
{
case 0:
{
lean_object* v___x_1967_; 
v___x_1967_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__0));
v___y_1960_ = v___x_1967_;
goto v___jp_1959_;
}
case 1:
{
lean_object* v___x_1968_; 
v___x_1968_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__1));
v___y_1960_ = v___x_1968_;
goto v___jp_1959_;
}
default: 
{
lean_object* v___x_1969_; 
v___x_1969_ = ((lean_object*)(l_Lean_instToStringAttributeKind___lam__0___closed__2));
v___y_1960_ = v___x_1969_;
goto v___jp_1959_;
}
}
v___jp_1959_:
{
lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; 
lean_inc_ref(v___y_1960_);
v___x_1961_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1961_, 0, v___y_1960_);
v___x_1962_ = l_Lean_MessageData_ofFormat(v___x_1961_);
v___x_1963_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1963_, 0, v___x_1958_);
lean_ctor_set(v___x_1963_, 1, v___x_1962_);
v___x_1964_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___redArg___closed__5, &l_Lean_throwAttrMustBeGlobal___redArg___closed__5_once, _init_l_Lean_throwAttrMustBeGlobal___redArg___closed__5);
v___x_1965_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1965_, 0, v___x_1963_);
lean_ctor_set(v___x_1965_, 1, v___x_1964_);
v___x_1966_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_1965_, v___y_1951_, v___y_1952_);
return v___x_1966_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg___boxed(lean_object* v_name_1970_, lean_object* v_kind_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_){
_start:
{
uint8_t v_kind_boxed_1975_; lean_object* v_res_1976_; 
v_kind_boxed_1975_ = lean_unbox(v_kind_1971_);
v_res_1976_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg(v_name_1970_, v_kind_boxed_1975_, v___y_1972_, v___y_1973_);
lean_dec(v___y_1973_);
lean_dec_ref(v___y_1972_);
return v_res_1976_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__7(lean_object* v_validate_1977_, lean_object* v_a_1978_, lean_object* v_name_1979_, lean_object* v_decl_1980_, lean_object* v_stx_1981_, uint8_t v_kind_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_){
_start:
{
lean_object* v___y_1987_; lean_object* v___y_1988_; lean_object* v___y_2022_; lean_object* v___y_2023_; lean_object* v___y_2024_; lean_object* v___y_2031_; lean_object* v___y_2032_; lean_object* v___x_2037_; 
v___x_2037_ = l_Lean_Attribute_Builtin_ensureNoArgs(v_stx_1981_, v___y_1983_, v___y_1984_);
if (lean_obj_tag(v___x_2037_) == 0)
{
uint8_t v___x_2038_; uint8_t v___x_2039_; 
lean_dec_ref_known(v___x_2037_, 1);
v___x_2038_ = 0;
v___x_2039_ = l_Lean_instBEqAttributeKind_beq(v_kind_1982_, v___x_2038_);
if (v___x_2039_ == 0)
{
lean_object* v___x_2040_; 
lean_dec(v_decl_1980_);
lean_dec_ref(v_a_1978_);
lean_dec_ref(v_validate_1977_);
v___x_2040_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg(v_name_1979_, v_kind_1982_, v___y_1983_, v___y_1984_);
return v___x_2040_;
}
else
{
v___y_2031_ = v___y_1983_;
v___y_2032_ = v___y_1984_;
goto v___jp_2030_;
}
}
else
{
lean_dec(v_decl_1980_);
lean_dec(v_name_1979_);
lean_dec_ref(v_a_1978_);
lean_dec_ref(v_validate_1977_);
return v___x_2037_;
}
v___jp_1986_:
{
lean_object* v___x_1989_; 
lean_inc(v___y_1988_);
lean_inc_ref(v___y_1987_);
lean_inc(v_decl_1980_);
v___x_1989_ = lean_apply_4(v_validate_1977_, v_decl_1980_, v___y_1987_, v___y_1988_, lean_box(0));
if (lean_obj_tag(v___x_1989_) == 0)
{
lean_object* v___x_1991_; uint8_t v_isShared_1992_; uint8_t v_isSharedCheck_2019_; 
v_isSharedCheck_2019_ = !lean_is_exclusive(v___x_1989_);
if (v_isSharedCheck_2019_ == 0)
{
lean_object* v_unused_2020_; 
v_unused_2020_ = lean_ctor_get(v___x_1989_, 0);
lean_dec(v_unused_2020_);
v___x_1991_ = v___x_1989_;
v_isShared_1992_ = v_isSharedCheck_2019_;
goto v_resetjp_1990_;
}
else
{
lean_dec(v___x_1989_);
v___x_1991_ = lean_box(0);
v_isShared_1992_ = v_isSharedCheck_2019_;
goto v_resetjp_1990_;
}
v_resetjp_1990_:
{
lean_object* v___x_1993_; lean_object* v_toEnvExtension_1994_; lean_object* v_env_1995_; lean_object* v_nextMacroScope_1996_; lean_object* v_ngen_1997_; lean_object* v_auxDeclNGen_1998_; lean_object* v_traceState_1999_; lean_object* v_messages_2000_; lean_object* v_infoState_2001_; lean_object* v_snapshotTasks_2002_; lean_object* v___x_2004_; uint8_t v_isShared_2005_; uint8_t v_isSharedCheck_2017_; 
v___x_1993_ = lean_st_ref_take(v___y_1988_);
v_toEnvExtension_1994_ = lean_ctor_get(v_a_1978_, 0);
v_env_1995_ = lean_ctor_get(v___x_1993_, 0);
v_nextMacroScope_1996_ = lean_ctor_get(v___x_1993_, 1);
v_ngen_1997_ = lean_ctor_get(v___x_1993_, 2);
v_auxDeclNGen_1998_ = lean_ctor_get(v___x_1993_, 3);
v_traceState_1999_ = lean_ctor_get(v___x_1993_, 4);
v_messages_2000_ = lean_ctor_get(v___x_1993_, 6);
v_infoState_2001_ = lean_ctor_get(v___x_1993_, 7);
v_snapshotTasks_2002_ = lean_ctor_get(v___x_1993_, 8);
v_isSharedCheck_2017_ = !lean_is_exclusive(v___x_1993_);
if (v_isSharedCheck_2017_ == 0)
{
lean_object* v_unused_2018_; 
v_unused_2018_ = lean_ctor_get(v___x_1993_, 5);
lean_dec(v_unused_2018_);
v___x_2004_ = v___x_1993_;
v_isShared_2005_ = v_isSharedCheck_2017_;
goto v_resetjp_2003_;
}
else
{
lean_inc(v_snapshotTasks_2002_);
lean_inc(v_infoState_2001_);
lean_inc(v_messages_2000_);
lean_inc(v_traceState_1999_);
lean_inc(v_auxDeclNGen_1998_);
lean_inc(v_ngen_1997_);
lean_inc(v_nextMacroScope_1996_);
lean_inc(v_env_1995_);
lean_dec(v___x_1993_);
v___x_2004_ = lean_box(0);
v_isShared_2005_ = v_isSharedCheck_2017_;
goto v_resetjp_2003_;
}
v_resetjp_2003_:
{
lean_object* v_asyncMode_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2010_; 
v_asyncMode_2006_ = lean_ctor_get(v_toEnvExtension_1994_, 2);
lean_inc(v_asyncMode_2006_);
lean_inc(v_decl_1980_);
v___x_2007_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_a_1978_, v_env_1995_, v_decl_1980_, v_asyncMode_2006_, v_decl_1980_);
lean_dec(v_asyncMode_2006_);
v___x_2008_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2);
if (v_isShared_2005_ == 0)
{
lean_ctor_set(v___x_2004_, 5, v___x_2008_);
lean_ctor_set(v___x_2004_, 0, v___x_2007_);
v___x_2010_ = v___x_2004_;
goto v_reusejp_2009_;
}
else
{
lean_object* v_reuseFailAlloc_2016_; 
v_reuseFailAlloc_2016_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2016_, 0, v___x_2007_);
lean_ctor_set(v_reuseFailAlloc_2016_, 1, v_nextMacroScope_1996_);
lean_ctor_set(v_reuseFailAlloc_2016_, 2, v_ngen_1997_);
lean_ctor_set(v_reuseFailAlloc_2016_, 3, v_auxDeclNGen_1998_);
lean_ctor_set(v_reuseFailAlloc_2016_, 4, v_traceState_1999_);
lean_ctor_set(v_reuseFailAlloc_2016_, 5, v___x_2008_);
lean_ctor_set(v_reuseFailAlloc_2016_, 6, v_messages_2000_);
lean_ctor_set(v_reuseFailAlloc_2016_, 7, v_infoState_2001_);
lean_ctor_set(v_reuseFailAlloc_2016_, 8, v_snapshotTasks_2002_);
v___x_2010_ = v_reuseFailAlloc_2016_;
goto v_reusejp_2009_;
}
v_reusejp_2009_:
{
lean_object* v___x_2011_; lean_object* v___x_2012_; lean_object* v___x_2014_; 
v___x_2011_ = lean_st_ref_put(v___y_1988_, v___x_2010_);
v___x_2012_ = lean_box(0);
if (v_isShared_1992_ == 0)
{
lean_ctor_set(v___x_1991_, 0, v___x_2012_);
v___x_2014_ = v___x_1991_;
goto v_reusejp_2013_;
}
else
{
lean_object* v_reuseFailAlloc_2015_; 
v_reuseFailAlloc_2015_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2015_, 0, v___x_2012_);
v___x_2014_ = v_reuseFailAlloc_2015_;
goto v_reusejp_2013_;
}
v_reusejp_2013_:
{
return v___x_2014_;
}
}
}
}
}
else
{
lean_dec(v_decl_1980_);
lean_dec_ref(v_a_1978_);
return v___x_1989_;
}
}
v___jp_2021_:
{
lean_object* v_toEnvExtension_2025_; lean_object* v_asyncMode_2026_; uint8_t v___x_2027_; 
v_toEnvExtension_2025_ = lean_ctor_get(v_a_1978_, 0);
v_asyncMode_2026_ = lean_ctor_get(v_toEnvExtension_2025_, 2);
lean_inc(v_decl_1980_);
lean_inc_ref(v___y_2022_);
v___x_2027_ = l_Lean_EnvExtension_asyncMayModify___redArg(v___y_2022_, v_decl_1980_, v_asyncMode_2026_);
if (v___x_2027_ == 0)
{
lean_object* v___x_2028_; lean_object* v___x_2029_; 
lean_dec_ref(v_a_1978_);
lean_dec_ref(v_validate_1977_);
v___x_2028_ = l_Lean_Environment_asyncPrefix_x3f(v___y_2022_);
v___x_2029_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___redArg(v_name_1979_, v_decl_1980_, v___x_2028_, v___y_2023_, v___y_2024_);
return v___x_2029_;
}
else
{
lean_dec_ref(v___y_2022_);
lean_dec(v_name_1979_);
v___y_1987_ = v___y_2023_;
v___y_1988_ = v___y_2024_;
goto v___jp_1986_;
}
}
v___jp_2030_:
{
lean_object* v___x_2033_; lean_object* v_env_2034_; lean_object* v___x_2035_; 
v___x_2033_ = lean_st_ref_get(v___y_2032_);
v_env_2034_ = lean_ctor_get(v___x_2033_, 0);
lean_inc_ref(v_env_2034_);
lean_dec(v___x_2033_);
v___x_2035_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2034_, v_decl_1980_);
if (lean_obj_tag(v___x_2035_) == 0)
{
v___y_2022_ = v_env_2034_;
v___y_2023_ = v___y_2031_;
v___y_2024_ = v___y_2032_;
goto v___jp_2021_;
}
else
{
lean_object* v___x_2036_; 
lean_dec_ref_known(v___x_2035_, 1);
lean_dec_ref(v_env_2034_);
lean_dec_ref(v_a_1978_);
lean_dec_ref(v_validate_1977_);
v___x_2036_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg(v_name_1979_, v_decl_1980_, v___y_2031_, v___y_2032_);
return v___x_2036_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___lam__7___boxed(lean_object* v_validate_2041_, lean_object* v_a_2042_, lean_object* v_name_2043_, lean_object* v_decl_2044_, lean_object* v_stx_2045_, lean_object* v_kind_2046_, lean_object* v___y_2047_, lean_object* v___y_2048_, lean_object* v___y_2049_){
_start:
{
uint8_t v_kind_boxed_2050_; lean_object* v_res_2051_; 
v_kind_boxed_2050_ = lean_unbox(v_kind_2046_);
v_res_2051_ = l_Lean_registerTagAttribute___lam__7(v_validate_2041_, v_a_2042_, v_name_2043_, v_decl_2044_, v_stx_2045_, v_kind_boxed_2050_, v___y_2047_, v___y_2048_);
lean_dec(v___y_2048_);
lean_dec_ref(v___y_2047_);
return v_res_2051_;
}
}
static lean_object* _init_l_Lean_registerTagAttribute___closed__5(void){
_start:
{
lean_object* v___x_2057_; lean_object* v___f_2058_; 
v___x_2057_ = l_Lean_NameSet_empty;
v___f_2058_ = lean_alloc_closure((void*)(l_Lean_registerTagAttribute___lam__4___boxed), 4, 1);
lean_closure_set(v___f_2058_, 0, v___x_2057_);
return v___f_2058_;
}
}
static lean_object* _init_l_Lean_registerTagAttribute___closed__6(void){
_start:
{
lean_object* v___x_2059_; lean_object* v___f_2060_; 
v___x_2059_ = l_Lean_NameSet_empty;
v___f_2060_ = lean_alloc_closure((void*)(l_Lean_registerTagAttribute___lam__5___boxed), 2, 1);
lean_closure_set(v___f_2060_, 0, v___x_2059_);
return v___f_2060_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute(lean_object* v_name_2063_, lean_object* v_descr_2064_, lean_object* v_validate_2065_, lean_object* v_ref_2066_, uint8_t v_applicationTime_2067_, lean_object* v_asyncMode_2068_){
_start:
{
lean_object* v___f_2070_; lean_object* v___f_2071_; lean_object* v___f_2072_; lean_object* v___f_2073_; lean_object* v___f_2074_; lean_object* v___f_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; 
v___f_2070_ = ((lean_object*)(l_Lean_registerTagAttribute___closed__0));
v___f_2071_ = ((lean_object*)(l_Lean_registerTagAttribute___closed__2));
v___f_2072_ = ((lean_object*)(l_Lean_registerTagAttribute___closed__3));
v___f_2073_ = ((lean_object*)(l_Lean_registerTagAttribute___closed__4));
v___f_2074_ = lean_obj_once(&l_Lean_registerTagAttribute___closed__5, &l_Lean_registerTagAttribute___closed__5_once, _init_l_Lean_registerTagAttribute___closed__5);
v___f_2075_ = lean_obj_once(&l_Lean_registerTagAttribute___closed__6, &l_Lean_registerTagAttribute___closed__6_once, _init_l_Lean_registerTagAttribute___closed__6);
v___x_2076_ = ((lean_object*)(l_Lean_registerTagAttribute___closed__7));
lean_inc(v_ref_2066_);
v___x_2077_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_2077_, 0, v_ref_2066_);
lean_ctor_set(v___x_2077_, 1, v___f_2075_);
lean_ctor_set(v___x_2077_, 2, v___f_2074_);
lean_ctor_set(v___x_2077_, 3, v___f_2073_);
lean_ctor_set(v___x_2077_, 4, v___f_2072_);
lean_ctor_set(v___x_2077_, 5, v___f_2071_);
lean_ctor_set(v___x_2077_, 6, v_asyncMode_2068_);
lean_ctor_set(v___x_2077_, 7, v___x_2076_);
v___x_2078_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2078_, 0, v___x_2077_);
lean_ctor_set(v___x_2078_, 1, v___f_2070_);
v___x_2079_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_2078_);
if (lean_obj_tag(v___x_2079_) == 0)
{
lean_object* v_a_2080_; lean_object* v___f_2081_; lean_object* v___f_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; 
v_a_2080_ = lean_ctor_get(v___x_2079_, 0);
lean_inc_n(v_a_2080_, 2);
lean_dec_ref_known(v___x_2079_, 1);
lean_inc_n(v_name_2063_, 2);
v___f_2081_ = lean_alloc_closure((void*)(l_Lean_registerTagAttribute___lam__6___boxed), 5, 1);
lean_closure_set(v___f_2081_, 0, v_name_2063_);
v___f_2082_ = lean_alloc_closure((void*)(l_Lean_registerTagAttribute___lam__7___boxed), 9, 3);
lean_closure_set(v___f_2082_, 0, v_validate_2065_);
lean_closure_set(v___f_2082_, 1, v_a_2080_);
lean_closure_set(v___f_2082_, 2, v_name_2063_);
v___x_2083_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2083_, 0, v_ref_2066_);
lean_ctor_set(v___x_2083_, 1, v_name_2063_);
lean_ctor_set(v___x_2083_, 2, v_descr_2064_);
lean_ctor_set_uint8(v___x_2083_, sizeof(void*)*3, v_applicationTime_2067_);
v___x_2084_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2084_, 0, v___x_2083_);
lean_ctor_set(v___x_2084_, 1, v___f_2082_);
lean_ctor_set(v___x_2084_, 2, v___f_2081_);
lean_inc_ref(v___x_2084_);
v___x_2085_ = l_Lean_registerBuiltinAttribute(v___x_2084_);
if (lean_obj_tag(v___x_2085_) == 0)
{
lean_object* v___x_2087_; uint8_t v_isShared_2088_; uint8_t v_isSharedCheck_2093_; 
v_isSharedCheck_2093_ = !lean_is_exclusive(v___x_2085_);
if (v_isSharedCheck_2093_ == 0)
{
lean_object* v_unused_2094_; 
v_unused_2094_ = lean_ctor_get(v___x_2085_, 0);
lean_dec(v_unused_2094_);
v___x_2087_ = v___x_2085_;
v_isShared_2088_ = v_isSharedCheck_2093_;
goto v_resetjp_2086_;
}
else
{
lean_dec(v___x_2085_);
v___x_2087_ = lean_box(0);
v_isShared_2088_ = v_isSharedCheck_2093_;
goto v_resetjp_2086_;
}
v_resetjp_2086_:
{
lean_object* v___x_2089_; lean_object* v___x_2091_; 
v___x_2089_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2089_, 0, v___x_2084_);
lean_ctor_set(v___x_2089_, 1, v_a_2080_);
if (v_isShared_2088_ == 0)
{
lean_ctor_set(v___x_2087_, 0, v___x_2089_);
v___x_2091_ = v___x_2087_;
goto v_reusejp_2090_;
}
else
{
lean_object* v_reuseFailAlloc_2092_; 
v_reuseFailAlloc_2092_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2092_, 0, v___x_2089_);
v___x_2091_ = v_reuseFailAlloc_2092_;
goto v_reusejp_2090_;
}
v_reusejp_2090_:
{
return v___x_2091_;
}
}
}
else
{
lean_object* v_a_2095_; lean_object* v___x_2097_; uint8_t v_isShared_2098_; uint8_t v_isSharedCheck_2102_; 
lean_dec_ref_known(v___x_2084_, 3);
lean_dec(v_a_2080_);
v_a_2095_ = lean_ctor_get(v___x_2085_, 0);
v_isSharedCheck_2102_ = !lean_is_exclusive(v___x_2085_);
if (v_isSharedCheck_2102_ == 0)
{
v___x_2097_ = v___x_2085_;
v_isShared_2098_ = v_isSharedCheck_2102_;
goto v_resetjp_2096_;
}
else
{
lean_inc(v_a_2095_);
lean_dec(v___x_2085_);
v___x_2097_ = lean_box(0);
v_isShared_2098_ = v_isSharedCheck_2102_;
goto v_resetjp_2096_;
}
v_resetjp_2096_:
{
lean_object* v___x_2100_; 
if (v_isShared_2098_ == 0)
{
v___x_2100_ = v___x_2097_;
goto v_reusejp_2099_;
}
else
{
lean_object* v_reuseFailAlloc_2101_; 
v_reuseFailAlloc_2101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2101_, 0, v_a_2095_);
v___x_2100_ = v_reuseFailAlloc_2101_;
goto v_reusejp_2099_;
}
v_reusejp_2099_:
{
return v___x_2100_;
}
}
}
}
else
{
lean_object* v_a_2103_; lean_object* v___x_2105_; uint8_t v_isShared_2106_; uint8_t v_isSharedCheck_2110_; 
lean_dec(v_ref_2066_);
lean_dec_ref(v_validate_2065_);
lean_dec_ref(v_descr_2064_);
lean_dec(v_name_2063_);
v_a_2103_ = lean_ctor_get(v___x_2079_, 0);
v_isSharedCheck_2110_ = !lean_is_exclusive(v___x_2079_);
if (v_isSharedCheck_2110_ == 0)
{
v___x_2105_ = v___x_2079_;
v_isShared_2106_ = v_isSharedCheck_2110_;
goto v_resetjp_2104_;
}
else
{
lean_inc(v_a_2103_);
lean_dec(v___x_2079_);
v___x_2105_ = lean_box(0);
v_isShared_2106_ = v_isSharedCheck_2110_;
goto v_resetjp_2104_;
}
v_resetjp_2104_:
{
lean_object* v___x_2108_; 
if (v_isShared_2106_ == 0)
{
v___x_2108_ = v___x_2105_;
goto v_reusejp_2107_;
}
else
{
lean_object* v_reuseFailAlloc_2109_; 
v_reuseFailAlloc_2109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2109_, 0, v_a_2103_);
v___x_2108_ = v_reuseFailAlloc_2109_;
goto v_reusejp_2107_;
}
v_reusejp_2107_:
{
return v___x_2108_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerTagAttribute___boxed(lean_object* v_name_2111_, lean_object* v_descr_2112_, lean_object* v_validate_2113_, lean_object* v_ref_2114_, lean_object* v_applicationTime_2115_, lean_object* v_asyncMode_2116_, lean_object* v_a_2117_){
_start:
{
uint8_t v_applicationTime_boxed_2118_; lean_object* v_res_2119_; 
v_applicationTime_boxed_2118_ = lean_unbox(v_applicationTime_2115_);
v_res_2119_ = l_Lean_registerTagAttribute(v_name_2111_, v_descr_2112_, v_validate_2113_, v_ref_2114_, v_applicationTime_boxed_2118_, v_asyncMode_2116_);
return v_res_2119_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerTagAttribute_spec__1(lean_object* v_init_2120_, lean_object* v_t_2121_){
_start:
{
lean_object* v___x_2122_; 
v___x_2122_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerTagAttribute_spec__1_spec__1(v_init_2120_, v_t_2121_);
return v___x_2122_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3(lean_object* v_n_2123_, lean_object* v_as_2124_, lean_object* v_lo_2125_, lean_object* v_hi_2126_, lean_object* v_w_2127_, lean_object* v_hlo_2128_, lean_object* v_hhi_2129_){
_start:
{
lean_object* v___x_2130_; 
v___x_2130_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___redArg(v_n_2123_, v_as_2124_, v_lo_2125_, v_hi_2126_);
return v___x_2130_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3___boxed(lean_object* v_n_2131_, lean_object* v_as_2132_, lean_object* v_lo_2133_, lean_object* v_hi_2134_, lean_object* v_w_2135_, lean_object* v_hlo_2136_, lean_object* v_hhi_2137_){
_start:
{
lean_object* v_res_2138_; 
v_res_2138_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3(v_n_2131_, v_as_2132_, v_lo_2133_, v_hi_2134_, v_w_2135_, v_hlo_2136_, v_hhi_2137_);
lean_dec(v_hi_2134_);
lean_dec(v_n_2131_);
return v_res_2138_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4(lean_object* v_00_u03b1_2139_, lean_object* v_attrName_2140_, lean_object* v_declName_2141_, lean_object* v_asyncPrefix_x3f_2142_, lean_object* v___y_2143_, lean_object* v___y_2144_){
_start:
{
lean_object* v___x_2146_; 
v___x_2146_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___redArg(v_attrName_2140_, v_declName_2141_, v_asyncPrefix_x3f_2142_, v___y_2143_, v___y_2144_);
return v___x_2146_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4___boxed(lean_object* v_00_u03b1_2147_, lean_object* v_attrName_2148_, lean_object* v_declName_2149_, lean_object* v_asyncPrefix_x3f_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_, lean_object* v___y_2153_){
_start:
{
lean_object* v_res_2154_; 
v_res_2154_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_registerTagAttribute_spec__4(v_00_u03b1_2147_, v_attrName_2148_, v_declName_2149_, v_asyncPrefix_x3f_2150_, v___y_2151_, v___y_2152_);
lean_dec(v___y_2152_);
lean_dec_ref(v___y_2151_);
return v_res_2154_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5(lean_object* v_00_u03b1_2155_, lean_object* v_attrName_2156_, lean_object* v_declName_2157_, lean_object* v___y_2158_, lean_object* v___y_2159_){
_start:
{
lean_object* v___x_2161_; 
v___x_2161_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg(v_attrName_2156_, v_declName_2157_, v___y_2158_, v___y_2159_);
return v___x_2161_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___boxed(lean_object* v_00_u03b1_2162_, lean_object* v_attrName_2163_, lean_object* v_declName_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_, lean_object* v___y_2167_){
_start:
{
lean_object* v_res_2168_; 
v_res_2168_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5(v_00_u03b1_2162_, v_attrName_2163_, v_declName_2164_, v___y_2165_, v___y_2166_);
lean_dec(v___y_2166_);
lean_dec_ref(v___y_2165_);
return v_res_2168_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6(lean_object* v_00_u03b1_2169_, lean_object* v_name_2170_, uint8_t v_kind_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_){
_start:
{
lean_object* v___x_2175_; 
v___x_2175_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg(v_name_2170_, v_kind_2171_, v___y_2172_, v___y_2173_);
return v___x_2175_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___boxed(lean_object* v_00_u03b1_2176_, lean_object* v_name_2177_, lean_object* v_kind_2178_, lean_object* v___y_2179_, lean_object* v___y_2180_, lean_object* v___y_2181_){
_start:
{
uint8_t v_kind_boxed_2182_; lean_object* v_res_2183_; 
v_kind_boxed_2182_ = lean_unbox(v_kind_2178_);
v_res_2183_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6(v_00_u03b1_2176_, v_name_2177_, v_kind_boxed_2182_, v___y_2179_, v___y_2180_);
lean_dec(v___y_2180_);
lean_dec_ref(v___y_2179_);
return v_res_2183_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4(lean_object* v_n_2184_, lean_object* v_lo_2185_, lean_object* v_hi_2186_, lean_object* v_hhi_2187_, lean_object* v_pivot_2188_, lean_object* v_as_2189_, lean_object* v_i_2190_, lean_object* v_k_2191_, lean_object* v_ilo_2192_, lean_object* v_ik_2193_, lean_object* v_w_2194_){
_start:
{
lean_object* v___x_2195_; 
v___x_2195_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4___redArg(v_hi_2186_, v_pivot_2188_, v_as_2189_, v_i_2190_, v_k_2191_);
return v___x_2195_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4___boxed(lean_object* v_n_2196_, lean_object* v_lo_2197_, lean_object* v_hi_2198_, lean_object* v_hhi_2199_, lean_object* v_pivot_2200_, lean_object* v_as_2201_, lean_object* v_i_2202_, lean_object* v_k_2203_, lean_object* v_ilo_2204_, lean_object* v_ik_2205_, lean_object* v_w_2206_){
_start:
{
lean_object* v_res_2207_; 
v_res_2207_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerTagAttribute_spec__3_spec__4(v_n_2196_, v_lo_2197_, v_hi_2198_, v_hhi_2199_, v_pivot_2200_, v_as_2201_, v_i_2202_, v_k_2203_, v_ilo_2204_, v_ik_2205_, v_w_2206_);
lean_dec(v_pivot_2200_);
lean_dec(v_hi_2198_);
lean_dec(v_lo_2197_);
lean_dec(v_n_2196_);
return v_res_2207_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg___lam__0(lean_object* v_attr_2208_, lean_object* v_decl_2209_, lean_object* v_env_2210_){
_start:
{
lean_object* v_ext_2211_; lean_object* v_toEnvExtension_2212_; lean_object* v_asyncMode_2213_; lean_object* v___x_2214_; 
v_ext_2211_ = lean_ctor_get(v_attr_2208_, 1);
lean_inc_ref(v_ext_2211_);
lean_dec_ref(v_attr_2208_);
v_toEnvExtension_2212_ = lean_ctor_get(v_ext_2211_, 0);
v_asyncMode_2213_ = lean_ctor_get(v_toEnvExtension_2212_, 2);
lean_inc(v_asyncMode_2213_);
lean_inc(v_decl_2209_);
v___x_2214_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_ext_2211_, v_env_2210_, v_decl_2209_, v_asyncMode_2213_, v_decl_2209_);
lean_dec(v_asyncMode_2213_);
return v___x_2214_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg___lam__1(lean_object* v_modifyEnv_2215_, lean_object* v___f_2216_, lean_object* v_____r_2217_){
_start:
{
lean_object* v___x_2218_; 
v___x_2218_ = lean_apply_1(v_modifyEnv_2215_, v___f_2216_);
return v___x_2218_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg___lam__2(lean_object* v_attr_2219_, lean_object* v_env_2220_, lean_object* v_decl_2221_, lean_object* v_inst_2222_, lean_object* v_inst_2223_, lean_object* v_toBind_2224_, lean_object* v___f_2225_, lean_object* v_modifyEnv_2226_, lean_object* v___f_2227_, lean_object* v_____r_2228_){
_start:
{
lean_object* v_ext_2229_; lean_object* v_toEnvExtension_2230_; lean_object* v_attr_2231_; lean_object* v_asyncMode_2232_; uint8_t v___x_2233_; 
v_ext_2229_ = lean_ctor_get(v_attr_2219_, 1);
v_toEnvExtension_2230_ = lean_ctor_get(v_ext_2229_, 0);
lean_inc_ref(v_toEnvExtension_2230_);
v_attr_2231_ = lean_ctor_get(v_attr_2219_, 0);
lean_inc_ref(v_attr_2231_);
lean_dec_ref(v_attr_2219_);
v_asyncMode_2232_ = lean_ctor_get(v_toEnvExtension_2230_, 2);
lean_inc(v_asyncMode_2232_);
lean_dec_ref(v_toEnvExtension_2230_);
lean_inc(v_decl_2221_);
lean_inc_ref(v_env_2220_);
v___x_2233_ = l_Lean_EnvExtension_asyncMayModify___redArg(v_env_2220_, v_decl_2221_, v_asyncMode_2232_);
lean_dec(v_asyncMode_2232_);
if (v___x_2233_ == 0)
{
lean_object* v_toAttributeImplCore_2234_; lean_object* v_name_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; 
lean_dec_ref(v___f_2227_);
lean_dec(v_modifyEnv_2226_);
v_toAttributeImplCore_2234_ = lean_ctor_get(v_attr_2231_, 0);
lean_inc_ref(v_toAttributeImplCore_2234_);
lean_dec_ref(v_attr_2231_);
v_name_2235_ = lean_ctor_get(v_toAttributeImplCore_2234_, 1);
lean_inc(v_name_2235_);
lean_dec_ref(v_toAttributeImplCore_2234_);
v___x_2236_ = l_Lean_Environment_asyncPrefix_x3f(v_env_2220_);
v___x_2237_ = l_Lean_throwAttrNotInAsyncCtx___redArg(v_inst_2222_, v_inst_2223_, v_name_2235_, v_decl_2221_, v___x_2236_);
v___x_2238_ = lean_apply_4(v_toBind_2224_, lean_box(0), lean_box(0), v___x_2237_, v___f_2225_);
return v___x_2238_;
}
else
{
lean_object* v___x_2239_; 
lean_dec_ref(v_attr_2231_);
lean_dec(v___f_2225_);
lean_dec(v_toBind_2224_);
lean_dec_ref(v_inst_2223_);
lean_dec_ref(v_inst_2222_);
lean_dec(v_decl_2221_);
lean_dec_ref(v_env_2220_);
v___x_2239_ = lean_apply_1(v_modifyEnv_2226_, v___f_2227_);
return v___x_2239_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg___lam__3(lean_object* v___f_2240_, lean_object* v_____r_2241_){
_start:
{
lean_object* v___x_2242_; 
v___x_2242_ = lean_apply_1(v___f_2240_, v_____r_2241_);
return v___x_2242_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg___lam__4(lean_object* v_attr_2243_, lean_object* v_decl_2244_, lean_object* v_inst_2245_, lean_object* v_inst_2246_, lean_object* v_toBind_2247_, lean_object* v___f_2248_, lean_object* v_modifyEnv_2249_, lean_object* v___f_2250_, lean_object* v_env_2251_){
_start:
{
lean_object* v___f_2252_; lean_object* v___x_2253_; 
lean_inc_ref(v___f_2250_);
lean_inc(v_modifyEnv_2249_);
lean_inc(v___f_2248_);
lean_inc(v_toBind_2247_);
lean_inc_ref(v_inst_2246_);
lean_inc_ref(v_inst_2245_);
lean_inc(v_decl_2244_);
lean_inc_ref(v_env_2251_);
lean_inc_ref(v_attr_2243_);
v___f_2252_ = lean_alloc_closure((void*)(l_Lean_TagAttribute_setTag___redArg___lam__2), 10, 9);
lean_closure_set(v___f_2252_, 0, v_attr_2243_);
lean_closure_set(v___f_2252_, 1, v_env_2251_);
lean_closure_set(v___f_2252_, 2, v_decl_2244_);
lean_closure_set(v___f_2252_, 3, v_inst_2245_);
lean_closure_set(v___f_2252_, 4, v_inst_2246_);
lean_closure_set(v___f_2252_, 5, v_toBind_2247_);
lean_closure_set(v___f_2252_, 6, v___f_2248_);
lean_closure_set(v___f_2252_, 7, v_modifyEnv_2249_);
lean_closure_set(v___f_2252_, 8, v___f_2250_);
v___x_2253_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2251_, v_decl_2244_);
if (lean_obj_tag(v___x_2253_) == 0)
{
lean_object* v___x_2254_; lean_object* v___x_2255_; 
lean_dec_ref(v___f_2252_);
v___x_2254_ = lean_box(0);
v___x_2255_ = l_Lean_TagAttribute_setTag___redArg___lam__2(v_attr_2243_, v_env_2251_, v_decl_2244_, v_inst_2245_, v_inst_2246_, v_toBind_2247_, v___f_2248_, v_modifyEnv_2249_, v___f_2250_, v___x_2254_);
return v___x_2255_;
}
else
{
lean_object* v_attr_2256_; lean_object* v_toAttributeImplCore_2257_; lean_object* v_name_2258_; lean_object* v___f_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; 
lean_dec_ref_known(v___x_2253_, 1);
lean_dec_ref(v_env_2251_);
lean_dec_ref(v___f_2250_);
lean_dec(v_modifyEnv_2249_);
lean_dec(v___f_2248_);
v_attr_2256_ = lean_ctor_get(v_attr_2243_, 0);
lean_inc_ref(v_attr_2256_);
lean_dec_ref(v_attr_2243_);
v_toAttributeImplCore_2257_ = lean_ctor_get(v_attr_2256_, 0);
lean_inc_ref(v_toAttributeImplCore_2257_);
lean_dec_ref(v_attr_2256_);
v_name_2258_ = lean_ctor_get(v_toAttributeImplCore_2257_, 1);
lean_inc(v_name_2258_);
lean_dec_ref(v_toAttributeImplCore_2257_);
v___f_2259_ = lean_alloc_closure((void*)(l_Lean_TagAttribute_setTag___redArg___lam__3), 2, 1);
lean_closure_set(v___f_2259_, 0, v___f_2252_);
v___x_2260_ = l_Lean_throwAttrDeclInImportedModule___redArg(v_inst_2245_, v_inst_2246_, v_name_2258_, v_decl_2244_);
v___x_2261_ = lean_apply_4(v_toBind_2247_, lean_box(0), lean_box(0), v___x_2260_, v___f_2259_);
return v___x_2261_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag___redArg(lean_object* v_inst_2262_, lean_object* v_inst_2263_, lean_object* v_inst_2264_, lean_object* v_attr_2265_, lean_object* v_decl_2266_){
_start:
{
lean_object* v_toBind_2267_; lean_object* v_getEnv_2268_; lean_object* v_modifyEnv_2269_; lean_object* v___f_2270_; lean_object* v___f_2271_; lean_object* v___f_2272_; lean_object* v___x_2273_; 
v_toBind_2267_ = lean_ctor_get(v_inst_2262_, 1);
lean_inc_n(v_toBind_2267_, 2);
v_getEnv_2268_ = lean_ctor_get(v_inst_2264_, 0);
lean_inc(v_getEnv_2268_);
v_modifyEnv_2269_ = lean_ctor_get(v_inst_2264_, 1);
lean_inc_n(v_modifyEnv_2269_, 2);
lean_dec_ref(v_inst_2264_);
lean_inc(v_decl_2266_);
lean_inc_ref(v_attr_2265_);
v___f_2270_ = lean_alloc_closure((void*)(l_Lean_TagAttribute_setTag___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2270_, 0, v_attr_2265_);
lean_closure_set(v___f_2270_, 1, v_decl_2266_);
lean_inc_ref(v___f_2270_);
v___f_2271_ = lean_alloc_closure((void*)(l_Lean_TagAttribute_setTag___redArg___lam__1), 3, 2);
lean_closure_set(v___f_2271_, 0, v_modifyEnv_2269_);
lean_closure_set(v___f_2271_, 1, v___f_2270_);
v___f_2272_ = lean_alloc_closure((void*)(l_Lean_TagAttribute_setTag___redArg___lam__4), 9, 8);
lean_closure_set(v___f_2272_, 0, v_attr_2265_);
lean_closure_set(v___f_2272_, 1, v_decl_2266_);
lean_closure_set(v___f_2272_, 2, v_inst_2262_);
lean_closure_set(v___f_2272_, 3, v_inst_2263_);
lean_closure_set(v___f_2272_, 4, v_toBind_2267_);
lean_closure_set(v___f_2272_, 5, v___f_2271_);
lean_closure_set(v___f_2272_, 6, v_modifyEnv_2269_);
lean_closure_set(v___f_2272_, 7, v___f_2270_);
v___x_2273_ = lean_apply_4(v_toBind_2267_, lean_box(0), lean_box(0), v_getEnv_2268_, v___f_2272_);
return v___x_2273_;
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_setTag(lean_object* v_m_2274_, lean_object* v_inst_2275_, lean_object* v_inst_2276_, lean_object* v_inst_2277_, lean_object* v_attr_2278_, lean_object* v_decl_2279_){
_start:
{
lean_object* v___x_2280_; 
v___x_2280_ = l_Lean_TagAttribute_setTag___redArg(v_inst_2275_, v_inst_2276_, v_inst_2277_, v_attr_2278_, v_decl_2279_);
return v___x_2280_;
}
}
LEAN_EXPORT uint8_t l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___redArg(lean_object* v___y_2281_, lean_object* v_as_2282_, lean_object* v_k_2283_, lean_object* v_x_2284_, lean_object* v_x_2285_){
_start:
{
lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v_m_2288_; lean_object* v_a_2289_; uint8_t v___x_2290_; 
v___x_2286_ = lean_nat_add(v_x_2284_, v_x_2285_);
v___x_2287_ = lean_unsigned_to_nat(1u);
v_m_2288_ = lean_nat_shiftr(v___x_2286_, v___x_2287_);
lean_dec(v___x_2286_);
v_a_2289_ = lean_array_fget_borrowed(v_as_2282_, v_m_2288_);
v___x_2290_ = l_Lean_Name_quickLt(v_a_2289_, v_k_2283_);
if (v___x_2290_ == 0)
{
lean_object* v___x_2291_; uint8_t v___x_2292_; 
lean_dec(v_x_2285_);
v___x_2291_ = lean_unsigned_to_nat(0u);
v___x_2292_ = l_Lean_Name_quickLt(v_k_2283_, v_a_2289_);
if (v___x_2292_ == 0)
{
uint8_t v___x_2293_; 
lean_dec(v_m_2288_);
lean_dec(v_x_2284_);
v___x_2293_ = lean_nat_dec_le(v___x_2291_, v___y_2281_);
return v___x_2293_;
}
else
{
uint8_t v___x_2294_; lean_object* v___x_2295_; uint8_t v___y_2297_; 
v___x_2294_ = lean_nat_dec_eq(v_m_2288_, v___x_2291_);
v___x_2295_ = lean_nat_sub(v_m_2288_, v___x_2287_);
lean_dec(v_m_2288_);
if (v___x_2294_ == 0)
{
uint8_t v___x_2299_; 
v___x_2299_ = lean_nat_dec_lt(v___x_2295_, v_x_2284_);
v___y_2297_ = v___x_2299_;
goto v___jp_2296_;
}
else
{
v___y_2297_ = v___x_2294_;
goto v___jp_2296_;
}
v___jp_2296_:
{
if (v___y_2297_ == 0)
{
v_x_2285_ = v___x_2295_;
goto _start;
}
else
{
lean_dec(v___x_2295_);
lean_dec(v_x_2284_);
return v___x_2290_;
}
}
}
}
else
{
lean_object* v___x_2300_; uint8_t v___x_2301_; 
lean_dec(v_x_2284_);
v___x_2300_ = lean_nat_add(v_m_2288_, v___x_2287_);
lean_dec(v_m_2288_);
v___x_2301_ = lean_nat_dec_le(v___x_2300_, v_x_2285_);
if (v___x_2301_ == 0)
{
lean_dec(v___x_2300_);
lean_dec(v_x_2285_);
return v___x_2301_;
}
else
{
v_x_2284_ = v___x_2300_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___redArg___boxed(lean_object* v___y_2303_, lean_object* v_as_2304_, lean_object* v_k_2305_, lean_object* v_x_2306_, lean_object* v_x_2307_){
_start:
{
uint8_t v_res_2308_; lean_object* v_r_2309_; 
v_res_2308_ = l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___redArg(v___y_2303_, v_as_2304_, v_k_2305_, v_x_2306_, v_x_2307_);
lean_dec(v_k_2305_);
lean_dec_ref(v_as_2304_);
lean_dec(v___y_2303_);
v_r_2309_ = lean_box(v_res_2308_);
return v_r_2309_;
}
}
LEAN_EXPORT uint8_t l_Lean_TagAttribute_hasTag(lean_object* v_attr_2310_, lean_object* v_env_2311_, lean_object* v_decl_2312_){
_start:
{
lean_object* v___x_2313_; lean_object* v___x_2314_; 
v___x_2313_ = lean_box(1);
v___x_2314_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2311_, v_decl_2312_);
if (lean_obj_tag(v___x_2314_) == 0)
{
lean_object* v_ext_2315_; lean_object* v_toEnvExtension_2316_; lean_object* v_asyncMode_2317_; lean_object* v___x_2318_; uint8_t v___x_2319_; 
v_ext_2315_ = lean_ctor_get(v_attr_2310_, 1);
v_toEnvExtension_2316_ = lean_ctor_get(v_ext_2315_, 0);
v_asyncMode_2317_ = lean_ctor_get(v_toEnvExtension_2316_, 2);
lean_inc(v_decl_2312_);
v___x_2318_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_2313_, v_ext_2315_, v_env_2311_, v_asyncMode_2317_, v_decl_2312_);
v___x_2319_ = l_Lean_NameSet_contains(v___x_2318_, v_decl_2312_);
lean_dec(v_decl_2312_);
lean_dec(v___x_2318_);
return v___x_2319_;
}
else
{
lean_object* v_val_2320_; lean_object* v_ext_2321_; uint8_t v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; uint8_t v___x_2326_; 
v_val_2320_ = lean_ctor_get(v___x_2314_, 0);
lean_inc(v_val_2320_);
lean_dec_ref_known(v___x_2314_, 1);
v_ext_2321_ = lean_ctor_get(v_attr_2310_, 1);
v___x_2322_ = 0;
v___x_2323_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_2313_, v_ext_2321_, v_env_2311_, v_val_2320_, v___x_2322_);
lean_dec(v_val_2320_);
lean_dec_ref(v_env_2311_);
v___x_2324_ = lean_unsigned_to_nat(0u);
v___x_2325_ = lean_array_get_size(v___x_2323_);
v___x_2326_ = lean_nat_dec_lt(v___x_2324_, v___x_2325_);
if (v___x_2326_ == 0)
{
lean_dec_ref(v___x_2323_);
lean_dec(v_decl_2312_);
return v___x_2326_;
}
else
{
lean_object* v___x_2327_; lean_object* v___x_2328_; uint8_t v___x_2329_; 
v___x_2327_ = lean_unsigned_to_nat(1u);
v___x_2328_ = lean_nat_sub(v___x_2325_, v___x_2327_);
v___x_2329_ = lean_nat_dec_le(v___x_2324_, v___x_2328_);
if (v___x_2329_ == 0)
{
lean_dec(v___x_2328_);
lean_dec_ref(v___x_2323_);
lean_dec(v_decl_2312_);
return v___x_2329_;
}
else
{
uint8_t v___x_2330_; 
lean_inc(v___x_2328_);
v___x_2330_ = l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___redArg(v___x_2328_, v___x_2323_, v_decl_2312_, v___x_2324_, v___x_2328_);
lean_dec(v_decl_2312_);
lean_dec_ref(v___x_2323_);
lean_dec(v___x_2328_);
return v___x_2330_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_TagAttribute_hasTag___boxed(lean_object* v_attr_2331_, lean_object* v_env_2332_, lean_object* v_decl_2333_){
_start:
{
uint8_t v_res_2334_; lean_object* v_r_2335_; 
v_res_2334_ = l_Lean_TagAttribute_hasTag(v_attr_2331_, v_env_2332_, v_decl_2333_);
lean_dec_ref(v_attr_2331_);
v_r_2335_ = lean_box(v_res_2334_);
return v_r_2335_;
}
}
LEAN_EXPORT uint8_t l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0(lean_object* v___y_2336_, lean_object* v_as_2337_, lean_object* v_k_2338_, lean_object* v_x_2339_, lean_object* v_x_2340_, lean_object* v_x_2341_){
_start:
{
uint8_t v___x_2342_; 
v___x_2342_ = l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___redArg(v___y_2336_, v_as_2337_, v_k_2338_, v_x_2339_, v_x_2340_);
return v___x_2342_;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0___boxed(lean_object* v___y_2343_, lean_object* v_as_2344_, lean_object* v_k_2345_, lean_object* v_x_2346_, lean_object* v_x_2347_, lean_object* v_x_2348_){
_start:
{
uint8_t v_res_2349_; lean_object* v_r_2350_; 
v_res_2349_ = l_Array_binSearchAux___at___00Lean_TagAttribute_hasTag_spec__0(v___y_2343_, v_as_2344_, v_k_2345_, v_x_2346_, v_x_2347_, v_x_2348_);
lean_dec(v_k_2345_);
lean_dec_ref(v_as_2344_);
lean_dec(v___y_2343_);
v_r_2350_ = lean_box(v_res_2349_);
return v_r_2350_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__0(lean_object* v_x_2351_, lean_object* v___y_2352_){
_start:
{
lean_object* v___x_2354_; lean_object* v___x_2355_; 
v___x_2354_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___lam__0___closed__1));
v___x_2355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2355_, 0, v___x_2354_);
return v___x_2355_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__0___boxed(lean_object* v_x_2356_, lean_object* v___y_2357_, lean_object* v___y_2358_){
_start:
{
lean_object* v_res_2359_; 
v_res_2359_ = l_Lean_instInhabitedParametricAttribute_default___lam__0(v_x_2356_, v___y_2357_);
lean_dec_ref(v___y_2357_);
lean_dec_ref(v_x_2356_);
return v_res_2359_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__1(lean_object* v_s_2360_, lean_object* v_x_2361_){
_start:
{
lean_inc_ref(v_s_2360_);
return v_s_2360_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__1___boxed(lean_object* v_s_2362_, lean_object* v_x_2363_){
_start:
{
lean_object* v_res_2364_; 
v_res_2364_ = l_Lean_instInhabitedParametricAttribute_default___lam__1(v_s_2362_, v_x_2363_);
lean_dec_ref(v_x_2363_);
lean_dec_ref(v_s_2362_);
return v_res_2364_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__2(lean_object* v_x_2369_, lean_object* v_x_2370_){
_start:
{
lean_object* v___x_2371_; 
v___x_2371_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___lam__2___closed__1));
return v___x_2371_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__2___boxed(lean_object* v_x_2372_, lean_object* v_x_2373_){
_start:
{
lean_object* v_res_2374_; 
v_res_2374_ = l_Lean_instInhabitedParametricAttribute_default___lam__2(v_x_2372_, v_x_2373_);
lean_dec_ref(v_x_2373_);
lean_dec_ref(v_x_2372_);
return v_res_2374_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__3(lean_object* v_x_2375_){
_start:
{
lean_object* v___x_2376_; 
v___x_2376_ = lean_box(0);
return v___x_2376_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default___lam__3___boxed(lean_object* v_x_2377_){
_start:
{
lean_object* v_res_2378_; 
v_res_2378_ = l_Lean_instInhabitedParametricAttribute_default___lam__3(v_x_2377_);
lean_dec_ref(v_x_2377_);
return v_res_2378_;
}
}
static lean_object* _init_l_Lean_instInhabitedParametricAttribute_default___closed__4(void){
_start:
{
lean_object* v___x_2383_; 
v___x_2383_ = l_Lean_instInhabitedEnvExtension_default(lean_box(0));
return v___x_2383_;
}
}
static lean_object* _init_l_Lean_instInhabitedParametricAttribute_default___closed__5(void){
_start:
{
lean_object* v___f_2384_; lean_object* v___f_2385_; lean_object* v___f_2386_; lean_object* v___f_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; 
v___f_2384_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___closed__3));
v___f_2385_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___closed__2));
v___f_2386_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___closed__1));
v___f_2387_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___closed__0));
v___x_2388_ = lean_box(0);
v___x_2389_ = lean_obj_once(&l_Lean_instInhabitedParametricAttribute_default___closed__4, &l_Lean_instInhabitedParametricAttribute_default___closed__4_once, _init_l_Lean_instInhabitedParametricAttribute_default___closed__4);
v___x_2390_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2390_, 0, v___x_2389_);
lean_ctor_set(v___x_2390_, 1, v___x_2388_);
lean_ctor_set(v___x_2390_, 2, v___f_2387_);
lean_ctor_set(v___x_2390_, 3, v___f_2386_);
lean_ctor_set(v___x_2390_, 4, v___f_2385_);
lean_ctor_set(v___x_2390_, 5, v___f_2384_);
return v___x_2390_;
}
}
static lean_object* _init_l_Lean_instInhabitedParametricAttribute_default___closed__6(void){
_start:
{
uint8_t v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; 
v___x_2391_ = 0;
v___x_2392_ = lean_obj_once(&l_Lean_instInhabitedParametricAttribute_default___closed__5, &l_Lean_instInhabitedParametricAttribute_default___closed__5_once, _init_l_Lean_instInhabitedParametricAttribute_default___closed__5);
v___x_2393_ = ((lean_object*)(l_Lean_instInhabitedAttributeImpl_default));
v___x_2394_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2394_, 0, v___x_2393_);
lean_ctor_set(v___x_2394_, 1, v___x_2392_);
lean_ctor_set_uint8(v___x_2394_, sizeof(void*)*2, v___x_2391_);
return v___x_2394_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute_default(lean_object* v_00_u03b1_2395_){
_start:
{
lean_object* v___x_2396_; 
v___x_2396_ = lean_obj_once(&l_Lean_instInhabitedParametricAttribute_default___closed__6, &l_Lean_instInhabitedParametricAttribute_default___closed__6_once, _init_l_Lean_instInhabitedParametricAttribute_default___closed__6);
return v___x_2396_;
}
}
static lean_object* _init_l_Lean_instInhabitedParametricAttribute___closed__0(void){
_start:
{
lean_object* v___x_2397_; 
v___x_2397_ = l_Lean_instInhabitedParametricAttribute_default(lean_box(0));
return v___x_2397_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedParametricAttribute(lean_object* v_a_2398_){
_start:
{
lean_object* v___x_2399_; 
v___x_2399_ = lean_obj_once(&l_Lean_instInhabitedParametricAttribute___closed__0, &l_Lean_instInhabitedParametricAttribute___closed__0_once, _init_l_Lean_instInhabitedParametricAttribute___closed__0);
return v___x_2399_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__0(lean_object* v_x_2400_, lean_object* v_p_2401_){
_start:
{
lean_object* v_fst_2402_; lean_object* v_snd_2403_; lean_object* v___x_2405_; uint8_t v_isShared_2406_; uint8_t v_isSharedCheck_2420_; 
v_fst_2402_ = lean_ctor_get(v_x_2400_, 0);
v_snd_2403_ = lean_ctor_get(v_x_2400_, 1);
v_isSharedCheck_2420_ = !lean_is_exclusive(v_x_2400_);
if (v_isSharedCheck_2420_ == 0)
{
v___x_2405_ = v_x_2400_;
v_isShared_2406_ = v_isSharedCheck_2420_;
goto v_resetjp_2404_;
}
else
{
lean_inc(v_snd_2403_);
lean_inc(v_fst_2402_);
lean_dec(v_x_2400_);
v___x_2405_ = lean_box(0);
v_isShared_2406_ = v_isSharedCheck_2420_;
goto v_resetjp_2404_;
}
v_resetjp_2404_:
{
lean_object* v_fst_2407_; lean_object* v_snd_2408_; lean_object* v___x_2410_; uint8_t v_isShared_2411_; uint8_t v_isSharedCheck_2419_; 
v_fst_2407_ = lean_ctor_get(v_p_2401_, 0);
v_snd_2408_ = lean_ctor_get(v_p_2401_, 1);
v_isSharedCheck_2419_ = !lean_is_exclusive(v_p_2401_);
if (v_isSharedCheck_2419_ == 0)
{
v___x_2410_ = v_p_2401_;
v_isShared_2411_ = v_isSharedCheck_2419_;
goto v_resetjp_2409_;
}
else
{
lean_inc(v_snd_2408_);
lean_inc(v_fst_2407_);
lean_dec(v_p_2401_);
v___x_2410_ = lean_box(0);
v_isShared_2411_ = v_isSharedCheck_2419_;
goto v_resetjp_2409_;
}
v_resetjp_2409_:
{
lean_object* v___x_2413_; 
lean_inc(v_fst_2407_);
if (v_isShared_2406_ == 0)
{
lean_ctor_set_tag(v___x_2405_, 1);
lean_ctor_set(v___x_2405_, 1, v_fst_2402_);
lean_ctor_set(v___x_2405_, 0, v_fst_2407_);
v___x_2413_ = v___x_2405_;
goto v_reusejp_2412_;
}
else
{
lean_object* v_reuseFailAlloc_2418_; 
v_reuseFailAlloc_2418_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2418_, 0, v_fst_2407_);
lean_ctor_set(v_reuseFailAlloc_2418_, 1, v_fst_2402_);
v___x_2413_ = v_reuseFailAlloc_2418_;
goto v_reusejp_2412_;
}
v_reusejp_2412_:
{
lean_object* v___x_2414_; lean_object* v___x_2416_; 
v___x_2414_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_2407_, v_snd_2408_, v_snd_2403_);
if (v_isShared_2411_ == 0)
{
lean_ctor_set(v___x_2410_, 1, v___x_2414_);
lean_ctor_set(v___x_2410_, 0, v___x_2413_);
v___x_2416_ = v___x_2410_;
goto v_reusejp_2415_;
}
else
{
lean_object* v_reuseFailAlloc_2417_; 
v_reuseFailAlloc_2417_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2417_, 0, v___x_2413_);
lean_ctor_set(v_reuseFailAlloc_2417_, 1, v___x_2414_);
v___x_2416_ = v_reuseFailAlloc_2417_;
goto v_reusejp_2415_;
}
v_reusejp_2415_:
{
return v___x_2416_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg(lean_object* v_init_2421_, lean_object* v_x_2422_){
_start:
{
if (lean_obj_tag(v_x_2422_) == 0)
{
lean_object* v_k_2423_; lean_object* v_v_2424_; lean_object* v_l_2425_; lean_object* v_r_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; 
v_k_2423_ = lean_ctor_get(v_x_2422_, 1);
v_v_2424_ = lean_ctor_get(v_x_2422_, 2);
v_l_2425_ = lean_ctor_get(v_x_2422_, 3);
v_r_2426_ = lean_ctor_get(v_x_2422_, 4);
v___x_2427_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg(v_init_2421_, v_l_2425_);
lean_inc(v_v_2424_);
lean_inc(v_k_2423_);
v___x_2428_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2428_, 0, v_k_2423_);
lean_ctor_set(v___x_2428_, 1, v_v_2424_);
v___x_2429_ = lean_array_push(v___x_2427_, v___x_2428_);
v_init_2421_ = v___x_2429_;
v_x_2422_ = v_r_2426_;
goto _start;
}
else
{
return v_init_2421_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg___boxed(lean_object* v_init_2431_, lean_object* v_x_2432_){
_start:
{
lean_object* v_res_2433_; 
v_res_2433_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg(v_init_2431_, v_x_2432_);
lean_dec(v_x_2432_);
return v_res_2433_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5___redArg(lean_object* v_snd_2434_, lean_object* v_as_2435_, size_t v_i_2436_, size_t v_stop_2437_, lean_object* v_b_2438_){
_start:
{
lean_object* v___y_2440_; uint8_t v___x_2444_; 
v___x_2444_ = lean_usize_dec_eq(v_i_2436_, v_stop_2437_);
if (v___x_2444_ == 0)
{
lean_object* v___x_2445_; lean_object* v___x_2446_; 
v___x_2445_ = lean_array_uget_borrowed(v_as_2435_, v_i_2436_);
v___x_2446_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_snd_2434_, v___x_2445_);
if (lean_obj_tag(v___x_2446_) == 0)
{
v___y_2440_ = v_b_2438_;
goto v___jp_2439_;
}
else
{
lean_object* v_val_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; 
v_val_2447_ = lean_ctor_get(v___x_2446_, 0);
lean_inc(v_val_2447_);
lean_dec_ref_known(v___x_2446_, 1);
lean_inc(v___x_2445_);
v___x_2448_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2448_, 0, v___x_2445_);
lean_ctor_set(v___x_2448_, 1, v_val_2447_);
v___x_2449_ = lean_array_push(v_b_2438_, v___x_2448_);
v___y_2440_ = v___x_2449_;
goto v___jp_2439_;
}
}
else
{
return v_b_2438_;
}
v___jp_2439_:
{
size_t v___x_2441_; size_t v___x_2442_; 
v___x_2441_ = ((size_t)1ULL);
v___x_2442_ = lean_usize_add(v_i_2436_, v___x_2441_);
v_i_2436_ = v___x_2442_;
v_b_2438_ = v___y_2440_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5___redArg___boxed(lean_object* v_snd_2450_, lean_object* v_as_2451_, lean_object* v_i_2452_, lean_object* v_stop_2453_, lean_object* v_b_2454_){
_start:
{
size_t v_i_boxed_2455_; size_t v_stop_boxed_2456_; lean_object* v_res_2457_; 
v_i_boxed_2455_ = lean_unbox_usize(v_i_2452_);
lean_dec(v_i_2452_);
v_stop_boxed_2456_ = lean_unbox_usize(v_stop_2453_);
lean_dec(v_stop_2453_);
v_res_2457_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5___redArg(v_snd_2450_, v_as_2451_, v_i_boxed_2455_, v_stop_boxed_2456_, v_b_2454_);
lean_dec_ref(v_as_2451_);
lean_dec(v_snd_2450_);
return v_res_2457_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3___redArg(lean_object* v_snd_2458_, lean_object* v_as_2459_, lean_object* v_start_2460_, lean_object* v_stop_2461_){
_start:
{
lean_object* v___x_2462_; uint8_t v___x_2463_; 
v___x_2462_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___lam__2___closed__0));
v___x_2463_ = lean_nat_dec_lt(v_start_2460_, v_stop_2461_);
if (v___x_2463_ == 0)
{
return v___x_2462_;
}
else
{
lean_object* v___x_2464_; uint8_t v___x_2465_; 
v___x_2464_ = lean_array_get_size(v_as_2459_);
v___x_2465_ = lean_nat_dec_le(v_stop_2461_, v___x_2464_);
if (v___x_2465_ == 0)
{
uint8_t v___x_2466_; 
v___x_2466_ = lean_nat_dec_lt(v_start_2460_, v___x_2464_);
if (v___x_2466_ == 0)
{
return v___x_2462_;
}
else
{
size_t v___x_2467_; size_t v___x_2468_; lean_object* v___x_2469_; 
v___x_2467_ = lean_usize_of_nat(v_start_2460_);
v___x_2468_ = lean_usize_of_nat(v___x_2464_);
v___x_2469_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5___redArg(v_snd_2458_, v_as_2459_, v___x_2467_, v___x_2468_, v___x_2462_);
return v___x_2469_;
}
}
else
{
size_t v___x_2470_; size_t v___x_2471_; lean_object* v___x_2472_; 
v___x_2470_ = lean_usize_of_nat(v_start_2460_);
v___x_2471_ = lean_usize_of_nat(v_stop_2461_);
v___x_2472_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5___redArg(v_snd_2458_, v_as_2459_, v___x_2470_, v___x_2471_, v___x_2462_);
return v___x_2472_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3___redArg___boxed(lean_object* v_snd_2473_, lean_object* v_as_2474_, lean_object* v_start_2475_, lean_object* v_stop_2476_){
_start:
{
lean_object* v_res_2477_; 
v_res_2477_ = l_Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3___redArg(v_snd_2473_, v_as_2474_, v_start_2475_, v_stop_2476_);
lean_dec(v_stop_2476_);
lean_dec(v_start_2475_);
lean_dec_ref(v_as_2474_);
lean_dec(v_snd_2473_);
return v_res_2477_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2_spec__3___redArg(lean_object* v_hi_2478_, lean_object* v_pivot_2479_, lean_object* v_as_2480_, lean_object* v_i_2481_, lean_object* v_k_2482_){
_start:
{
uint8_t v___x_2483_; 
v___x_2483_ = lean_nat_dec_lt(v_k_2482_, v_hi_2478_);
if (v___x_2483_ == 0)
{
lean_object* v___x_2484_; lean_object* v___x_2485_; 
lean_dec(v_k_2482_);
v___x_2484_ = lean_array_fswap(v_as_2480_, v_i_2481_, v_hi_2478_);
v___x_2485_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2485_, 0, v_i_2481_);
lean_ctor_set(v___x_2485_, 1, v___x_2484_);
return v___x_2485_;
}
else
{
lean_object* v___x_2486_; lean_object* v_fst_2487_; lean_object* v_fst_2488_; uint8_t v___x_2489_; 
v___x_2486_ = lean_array_fget_borrowed(v_as_2480_, v_k_2482_);
v_fst_2487_ = lean_ctor_get(v___x_2486_, 0);
v_fst_2488_ = lean_ctor_get(v_pivot_2479_, 0);
v___x_2489_ = l_Lean_Name_quickLt(v_fst_2487_, v_fst_2488_);
if (v___x_2489_ == 0)
{
lean_object* v___x_2490_; lean_object* v___x_2491_; 
v___x_2490_ = lean_unsigned_to_nat(1u);
v___x_2491_ = lean_nat_add(v_k_2482_, v___x_2490_);
lean_dec(v_k_2482_);
v_k_2482_ = v___x_2491_;
goto _start;
}
else
{
lean_object* v___x_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; lean_object* v___x_2496_; 
v___x_2493_ = lean_array_fswap(v_as_2480_, v_i_2481_, v_k_2482_);
v___x_2494_ = lean_unsigned_to_nat(1u);
v___x_2495_ = lean_nat_add(v_i_2481_, v___x_2494_);
lean_dec(v_i_2481_);
v___x_2496_ = lean_nat_add(v_k_2482_, v___x_2494_);
lean_dec(v_k_2482_);
v_as_2480_ = v___x_2493_;
v_i_2481_ = v___x_2495_;
v_k_2482_ = v___x_2496_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2_spec__3___redArg___boxed(lean_object* v_hi_2498_, lean_object* v_pivot_2499_, lean_object* v_as_2500_, lean_object* v_i_2501_, lean_object* v_k_2502_){
_start:
{
lean_object* v_res_2503_; 
v_res_2503_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2_spec__3___redArg(v_hi_2498_, v_pivot_2499_, v_as_2500_, v_i_2501_, v_k_2502_);
lean_dec_ref(v_pivot_2499_);
lean_dec(v_hi_2498_);
return v_res_2503_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg___lam__0(lean_object* v_a_2504_, lean_object* v_b_2505_){
_start:
{
lean_object* v_fst_2506_; lean_object* v_fst_2507_; uint8_t v___x_2508_; 
v_fst_2506_ = lean_ctor_get(v_a_2504_, 0);
v_fst_2507_ = lean_ctor_get(v_b_2505_, 0);
v___x_2508_ = l_Lean_Name_quickLt(v_fst_2506_, v_fst_2507_);
return v___x_2508_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg___lam__0___boxed(lean_object* v_a_2509_, lean_object* v_b_2510_){
_start:
{
uint8_t v_res_2511_; lean_object* v_r_2512_; 
v_res_2511_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg___lam__0(v_a_2509_, v_b_2510_);
lean_dec_ref(v_b_2510_);
lean_dec_ref(v_a_2509_);
v_r_2512_ = lean_box(v_res_2511_);
return v_r_2512_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg(lean_object* v_n_2513_, lean_object* v_as_2514_, lean_object* v_lo_2515_, lean_object* v_hi_2516_){
_start:
{
lean_object* v___y_2518_; uint8_t v___x_2528_; 
v___x_2528_ = lean_nat_dec_lt(v_lo_2515_, v_hi_2516_);
if (v___x_2528_ == 0)
{
lean_dec(v_lo_2515_);
return v_as_2514_;
}
else
{
lean_object* v___x_2529_; lean_object* v___x_2530_; lean_object* v_mid_2531_; lean_object* v___y_2533_; lean_object* v___y_2539_; lean_object* v___x_2544_; lean_object* v___x_2545_; uint8_t v___x_2546_; 
v___x_2529_ = lean_nat_add(v_lo_2515_, v_hi_2516_);
v___x_2530_ = lean_unsigned_to_nat(1u);
v_mid_2531_ = lean_nat_shiftr(v___x_2529_, v___x_2530_);
lean_dec(v___x_2529_);
v___x_2544_ = lean_array_fget_borrowed(v_as_2514_, v_mid_2531_);
v___x_2545_ = lean_array_fget_borrowed(v_as_2514_, v_lo_2515_);
v___x_2546_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg___lam__0(v___x_2544_, v___x_2545_);
if (v___x_2546_ == 0)
{
v___y_2539_ = v_as_2514_;
goto v___jp_2538_;
}
else
{
lean_object* v___x_2547_; 
v___x_2547_ = lean_array_fswap(v_as_2514_, v_lo_2515_, v_mid_2531_);
v___y_2539_ = v___x_2547_;
goto v___jp_2538_;
}
v___jp_2532_:
{
lean_object* v___x_2534_; lean_object* v___x_2535_; uint8_t v___x_2536_; 
v___x_2534_ = lean_array_fget_borrowed(v___y_2533_, v_mid_2531_);
v___x_2535_ = lean_array_fget_borrowed(v___y_2533_, v_hi_2516_);
v___x_2536_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg___lam__0(v___x_2534_, v___x_2535_);
if (v___x_2536_ == 0)
{
lean_dec(v_mid_2531_);
v___y_2518_ = v___y_2533_;
goto v___jp_2517_;
}
else
{
lean_object* v___x_2537_; 
v___x_2537_ = lean_array_fswap(v___y_2533_, v_mid_2531_, v_hi_2516_);
lean_dec(v_mid_2531_);
v___y_2518_ = v___x_2537_;
goto v___jp_2517_;
}
}
v___jp_2538_:
{
lean_object* v___x_2540_; lean_object* v___x_2541_; uint8_t v___x_2542_; 
v___x_2540_ = lean_array_fget_borrowed(v___y_2539_, v_hi_2516_);
v___x_2541_ = lean_array_fget_borrowed(v___y_2539_, v_lo_2515_);
v___x_2542_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg___lam__0(v___x_2540_, v___x_2541_);
if (v___x_2542_ == 0)
{
v___y_2533_ = v___y_2539_;
goto v___jp_2532_;
}
else
{
lean_object* v___x_2543_; 
v___x_2543_ = lean_array_fswap(v___y_2539_, v_lo_2515_, v_hi_2516_);
v___y_2533_ = v___x_2543_;
goto v___jp_2532_;
}
}
}
v___jp_2517_:
{
lean_object* v_pivot_2519_; lean_object* v___x_2520_; lean_object* v_fst_2521_; lean_object* v_snd_2522_; uint8_t v___x_2523_; 
v_pivot_2519_ = lean_array_fget(v___y_2518_, v_hi_2516_);
lean_inc_n(v_lo_2515_, 2);
v___x_2520_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2_spec__3___redArg(v_hi_2516_, v_pivot_2519_, v___y_2518_, v_lo_2515_, v_lo_2515_);
lean_dec(v_pivot_2519_);
v_fst_2521_ = lean_ctor_get(v___x_2520_, 0);
lean_inc(v_fst_2521_);
v_snd_2522_ = lean_ctor_get(v___x_2520_, 1);
lean_inc(v_snd_2522_);
lean_dec_ref(v___x_2520_);
v___x_2523_ = lean_nat_dec_le(v_hi_2516_, v_fst_2521_);
if (v___x_2523_ == 0)
{
lean_object* v___x_2524_; lean_object* v___x_2525_; lean_object* v___x_2526_; 
v___x_2524_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg(v_n_2513_, v_snd_2522_, v_lo_2515_, v_fst_2521_);
v___x_2525_ = lean_unsigned_to_nat(1u);
v___x_2526_ = lean_nat_add(v_fst_2521_, v___x_2525_);
lean_dec(v_fst_2521_);
v_as_2514_ = v___x_2524_;
v_lo_2515_ = v___x_2526_;
goto _start;
}
else
{
lean_dec(v_fst_2521_);
lean_dec(v_lo_2515_);
return v_snd_2522_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg___boxed(lean_object* v_n_2548_, lean_object* v_as_2549_, lean_object* v_lo_2550_, lean_object* v_hi_2551_){
_start:
{
lean_object* v_res_2552_; 
v_res_2552_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg(v_n_2548_, v_as_2549_, v_lo_2550_, v_hi_2551_);
lean_dec(v_hi_2551_);
lean_dec(v_n_2548_);
return v_res_2552_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0___redArg(lean_object* v_filterExport_2553_, lean_object* v_env_2554_, lean_object* v_as_2555_, size_t v_i_2556_, size_t v_stop_2557_, lean_object* v_b_2558_){
_start:
{
lean_object* v___y_2560_; uint8_t v___x_2564_; 
v___x_2564_ = lean_usize_dec_eq(v_i_2556_, v_stop_2557_);
if (v___x_2564_ == 0)
{
lean_object* v___x_2565_; lean_object* v_fst_2566_; lean_object* v_snd_2567_; lean_object* v___x_2568_; uint8_t v___x_2569_; 
v___x_2565_ = lean_array_uget_borrowed(v_as_2555_, v_i_2556_);
v_fst_2566_ = lean_ctor_get(v___x_2565_, 0);
v_snd_2567_ = lean_ctor_get(v___x_2565_, 1);
lean_inc_ref(v_filterExport_2553_);
lean_inc(v_snd_2567_);
lean_inc(v_fst_2566_);
lean_inc_ref(v_env_2554_);
v___x_2568_ = lean_apply_3(v_filterExport_2553_, v_env_2554_, v_fst_2566_, v_snd_2567_);
v___x_2569_ = lean_unbox(v___x_2568_);
if (v___x_2569_ == 0)
{
v___y_2560_ = v_b_2558_;
goto v___jp_2559_;
}
else
{
lean_object* v___x_2570_; 
lean_inc(v___x_2565_);
v___x_2570_ = lean_array_push(v_b_2558_, v___x_2565_);
v___y_2560_ = v___x_2570_;
goto v___jp_2559_;
}
}
else
{
lean_dec_ref(v_env_2554_);
lean_dec_ref(v_filterExport_2553_);
return v_b_2558_;
}
v___jp_2559_:
{
size_t v___x_2561_; size_t v___x_2562_; 
v___x_2561_ = ((size_t)1ULL);
v___x_2562_ = lean_usize_add(v_i_2556_, v___x_2561_);
v_i_2556_ = v___x_2562_;
v_b_2558_ = v___y_2560_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0___redArg___boxed(lean_object* v_filterExport_2571_, lean_object* v_env_2572_, lean_object* v_as_2573_, lean_object* v_i_2574_, lean_object* v_stop_2575_, lean_object* v_b_2576_){
_start:
{
size_t v_i_boxed_2577_; size_t v_stop_boxed_2578_; lean_object* v_res_2579_; 
v_i_boxed_2577_ = lean_unbox_usize(v_i_2574_);
lean_dec(v_i_2574_);
v_stop_boxed_2578_ = lean_unbox_usize(v_stop_2575_);
lean_dec(v_stop_2575_);
v_res_2579_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0___redArg(v_filterExport_2571_, v_env_2572_, v_as_2573_, v_i_boxed_2577_, v_stop_boxed_2578_, v_b_2576_);
lean_dec_ref(v_as_2573_);
return v_res_2579_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__1(lean_object* v_filterExport_2580_, uint8_t v_preserveOrder_2581_, lean_object* v_env_2582_, lean_object* v_x_2583_){
_start:
{
lean_object* v___y_2585_; 
if (v_preserveOrder_2581_ == 0)
{
lean_object* v_snd_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; lean_object* v_r_2604_; lean_object* v___x_2605_; lean_object* v___y_2607_; lean_object* v___y_2608_; uint8_t v___x_2610_; 
v_snd_2601_ = lean_ctor_get(v_x_2583_, 1);
lean_inc(v_snd_2601_);
lean_dec_ref(v_x_2583_);
v___x_2602_ = lean_unsigned_to_nat(0u);
v___x_2603_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___lam__2___closed__0));
v_r_2604_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg(v___x_2603_, v_snd_2601_);
lean_dec(v_snd_2601_);
v___x_2605_ = lean_array_get_size(v_r_2604_);
v___x_2610_ = lean_nat_dec_eq(v___x_2605_, v___x_2602_);
if (v___x_2610_ == 0)
{
lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v___y_2614_; uint8_t v___x_2616_; 
v___x_2611_ = lean_unsigned_to_nat(1u);
v___x_2612_ = lean_nat_sub(v___x_2605_, v___x_2611_);
v___x_2616_ = lean_nat_dec_le(v___x_2602_, v___x_2612_);
if (v___x_2616_ == 0)
{
lean_inc(v___x_2612_);
v___y_2614_ = v___x_2612_;
goto v___jp_2613_;
}
else
{
v___y_2614_ = v___x_2602_;
goto v___jp_2613_;
}
v___jp_2613_:
{
uint8_t v___x_2615_; 
v___x_2615_ = lean_nat_dec_le(v___y_2614_, v___x_2612_);
if (v___x_2615_ == 0)
{
lean_dec(v___x_2612_);
lean_inc(v___y_2614_);
v___y_2607_ = v___y_2614_;
v___y_2608_ = v___y_2614_;
goto v___jp_2606_;
}
else
{
v___y_2607_ = v___y_2614_;
v___y_2608_ = v___x_2612_;
goto v___jp_2606_;
}
}
}
else
{
v___y_2585_ = v_r_2604_;
goto v___jp_2584_;
}
v___jp_2606_:
{
lean_object* v___x_2609_; 
v___x_2609_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg(v___x_2605_, v_r_2604_, v___y_2607_, v___y_2608_);
lean_dec(v___y_2608_);
v___y_2585_ = v___x_2609_;
goto v___jp_2584_;
}
}
else
{
lean_object* v_fst_2617_; lean_object* v_snd_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; 
v_fst_2617_ = lean_ctor_get(v_x_2583_, 0);
lean_inc(v_fst_2617_);
v_snd_2618_ = lean_ctor_get(v_x_2583_, 1);
lean_inc(v_snd_2618_);
lean_dec_ref(v_x_2583_);
v___x_2619_ = lean_array_mk(v_fst_2617_);
v___x_2620_ = l_Array_reverse___redArg(v___x_2619_);
v___x_2621_ = lean_unsigned_to_nat(0u);
v___x_2622_ = lean_array_get_size(v___x_2620_);
v___x_2623_ = l_Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3___redArg(v_snd_2618_, v___x_2620_, v___x_2621_, v___x_2622_);
lean_dec_ref(v___x_2620_);
lean_dec(v_snd_2618_);
v___y_2585_ = v___x_2623_;
goto v___jp_2584_;
}
v___jp_2584_:
{
lean_object* v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; uint8_t v___x_2589_; 
v___x_2586_ = lean_unsigned_to_nat(0u);
v___x_2587_ = lean_array_get_size(v___y_2585_);
v___x_2588_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___lam__2___closed__0));
v___x_2589_ = lean_nat_dec_lt(v___x_2586_, v___x_2587_);
if (v___x_2589_ == 0)
{
lean_object* v___x_2590_; 
lean_dec_ref(v_env_2582_);
lean_dec_ref(v_filterExport_2580_);
v___x_2590_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2590_, 0, v___x_2588_);
lean_ctor_set(v___x_2590_, 1, v___x_2588_);
lean_ctor_set(v___x_2590_, 2, v___y_2585_);
return v___x_2590_;
}
else
{
uint8_t v___x_2591_; 
v___x_2591_ = lean_nat_dec_le(v___x_2587_, v___x_2587_);
if (v___x_2591_ == 0)
{
if (v___x_2589_ == 0)
{
lean_object* v___x_2592_; 
lean_dec_ref(v_env_2582_);
lean_dec_ref(v_filterExport_2580_);
v___x_2592_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2592_, 0, v___x_2588_);
lean_ctor_set(v___x_2592_, 1, v___x_2588_);
lean_ctor_set(v___x_2592_, 2, v___y_2585_);
return v___x_2592_;
}
else
{
size_t v___x_2593_; size_t v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; 
v___x_2593_ = ((size_t)0ULL);
v___x_2594_ = lean_usize_of_nat(v___x_2587_);
v___x_2595_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0___redArg(v_filterExport_2580_, v_env_2582_, v___y_2585_, v___x_2593_, v___x_2594_, v___x_2588_);
lean_inc_ref(v___x_2595_);
v___x_2596_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2596_, 0, v___x_2595_);
lean_ctor_set(v___x_2596_, 1, v___x_2595_);
lean_ctor_set(v___x_2596_, 2, v___y_2585_);
return v___x_2596_;
}
}
else
{
size_t v___x_2597_; size_t v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; 
v___x_2597_ = ((size_t)0ULL);
v___x_2598_ = lean_usize_of_nat(v___x_2587_);
v___x_2599_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0___redArg(v_filterExport_2580_, v_env_2582_, v___y_2585_, v___x_2597_, v___x_2598_, v___x_2588_);
lean_inc_ref(v___x_2599_);
v___x_2600_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2600_, 0, v___x_2599_);
lean_ctor_set(v___x_2600_, 1, v___x_2599_);
lean_ctor_set(v___x_2600_, 2, v___y_2585_);
return v___x_2600_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__1___boxed(lean_object* v_filterExport_2624_, lean_object* v_preserveOrder_2625_, lean_object* v_env_2626_, lean_object* v_x_2627_){
_start:
{
uint8_t v_preserveOrder_boxed_2628_; lean_object* v_res_2629_; 
v_preserveOrder_boxed_2628_ = lean_unbox(v_preserveOrder_2625_);
v_res_2629_ = l_Lean_registerParametricAttributeExt___redArg___lam__1(v_filterExport_2624_, v_preserveOrder_boxed_2628_, v_env_2626_, v_x_2627_);
return v_res_2629_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__2(lean_object* v_x_2639_){
_start:
{
lean_object* v_snd_2640_; lean_object* v___x_2642_; uint8_t v_isShared_2643_; uint8_t v_isSharedCheck_2654_; 
v_snd_2640_ = lean_ctor_get(v_x_2639_, 1);
v_isSharedCheck_2654_ = !lean_is_exclusive(v_x_2639_);
if (v_isSharedCheck_2654_ == 0)
{
lean_object* v_unused_2655_; 
v_unused_2655_ = lean_ctor_get(v_x_2639_, 0);
lean_dec(v_unused_2655_);
v___x_2642_ = v_x_2639_;
v_isShared_2643_ = v_isSharedCheck_2654_;
goto v_resetjp_2641_;
}
else
{
lean_inc(v_snd_2640_);
lean_dec(v_x_2639_);
v___x_2642_ = lean_box(0);
v_isShared_2643_ = v_isSharedCheck_2654_;
goto v_resetjp_2641_;
}
v_resetjp_2641_:
{
lean_object* v___x_2644_; lean_object* v___y_2646_; 
v___x_2644_ = ((lean_object*)(l_Lean_registerParametricAttributeExt___redArg___lam__2___closed__3));
if (lean_obj_tag(v_snd_2640_) == 0)
{
lean_object* v_size_2652_; 
v_size_2652_ = lean_ctor_get(v_snd_2640_, 0);
lean_inc(v_size_2652_);
lean_dec_ref_known(v_snd_2640_, 5);
v___y_2646_ = v_size_2652_;
goto v___jp_2645_;
}
else
{
lean_object* v___x_2653_; 
v___x_2653_ = lean_unsigned_to_nat(0u);
v___y_2646_ = v___x_2653_;
goto v___jp_2645_;
}
v___jp_2645_:
{
lean_object* v___x_2647_; lean_object* v___x_2648_; lean_object* v___x_2650_; 
v___x_2647_ = l_Nat_reprFast(v___y_2646_);
v___x_2648_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2648_, 0, v___x_2647_);
if (v_isShared_2643_ == 0)
{
lean_ctor_set_tag(v___x_2642_, 5);
lean_ctor_set(v___x_2642_, 1, v___x_2648_);
lean_ctor_set(v___x_2642_, 0, v___x_2644_);
v___x_2650_ = v___x_2642_;
goto v_reusejp_2649_;
}
else
{
lean_object* v_reuseFailAlloc_2651_; 
v_reuseFailAlloc_2651_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2651_, 0, v___x_2644_);
lean_ctor_set(v_reuseFailAlloc_2651_, 1, v___x_2648_);
v___x_2650_ = v_reuseFailAlloc_2651_;
goto v_reusejp_2649_;
}
v_reusejp_2649_:
{
return v___x_2650_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__3(lean_object* v_x_2656_){
_start:
{
lean_object* v___x_2657_; 
v___x_2657_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___lam__2___closed__0));
return v___x_2657_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__3___boxed(lean_object* v_x_2658_){
_start:
{
lean_object* v_res_2659_; 
v_res_2659_ = l_Lean_registerParametricAttributeExt___redArg___lam__3(v_x_2658_);
lean_dec_ref(v_x_2658_);
return v_res_2659_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__4(lean_object* v___x_2660_){
_start:
{
lean_object* v___x_2662_; 
v___x_2662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2662_, 0, v___x_2660_);
return v___x_2662_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__4___boxed(lean_object* v___x_2663_, lean_object* v___y_2664_){
_start:
{
lean_object* v_res_2665_; 
v_res_2665_ = l_Lean_registerParametricAttributeExt___redArg___lam__4(v___x_2663_);
return v_res_2665_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__5(lean_object* v___x_2666_, lean_object* v_x_2667_, lean_object* v___y_2668_){
_start:
{
lean_object* v___x_2670_; 
v___x_2670_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2670_, 0, v___x_2666_);
return v___x_2670_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___lam__5___boxed(lean_object* v___x_2671_, lean_object* v_x_2672_, lean_object* v___y_2673_, lean_object* v___y_2674_){
_start:
{
lean_object* v_res_2675_; 
v_res_2675_ = l_Lean_registerParametricAttributeExt___redArg___lam__5(v___x_2671_, v_x_2672_, v___y_2673_);
lean_dec_ref(v___y_2673_);
lean_dec_ref(v_x_2672_);
return v_res_2675_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg(lean_object* v_ref_2686_, uint8_t v_preserveOrder_2687_, lean_object* v_filterExport_2688_){
_start:
{
lean_object* v___f_2690_; lean_object* v___x_2691_; lean_object* v___f_2692_; lean_object* v___f_2693_; lean_object* v___f_2694_; lean_object* v___f_2695_; lean_object* v___f_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; 
v___f_2690_ = ((lean_object*)(l_Lean_registerParametricAttributeExt___redArg___closed__0));
v___x_2691_ = lean_box(v_preserveOrder_2687_);
v___f_2692_ = lean_alloc_closure((void*)(l_Lean_registerParametricAttributeExt___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_2692_, 0, v_filterExport_2688_);
lean_closure_set(v___f_2692_, 1, v___x_2691_);
v___f_2693_ = ((lean_object*)(l_Lean_registerParametricAttributeExt___redArg___closed__1));
v___f_2694_ = ((lean_object*)(l_Lean_registerParametricAttributeExt___redArg___closed__2));
v___f_2695_ = ((lean_object*)(l_Lean_registerParametricAttributeExt___redArg___closed__4));
v___f_2696_ = ((lean_object*)(l_Lean_registerParametricAttributeExt___redArg___closed__5));
v___x_2697_ = lean_box(2);
v___x_2698_ = lean_box(0);
v___x_2699_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_2699_, 0, v_ref_2686_);
lean_ctor_set(v___x_2699_, 1, v___f_2695_);
lean_ctor_set(v___x_2699_, 2, v___f_2696_);
lean_ctor_set(v___x_2699_, 3, v___f_2690_);
lean_ctor_set(v___x_2699_, 4, v___f_2692_);
lean_ctor_set(v___x_2699_, 5, v___f_2693_);
lean_ctor_set(v___x_2699_, 6, v___x_2697_);
lean_ctor_set(v___x_2699_, 7, v___x_2698_);
v___x_2700_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2700_, 0, v___x_2699_);
lean_ctor_set(v___x_2700_, 1, v___f_2694_);
v___x_2701_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_2700_);
return v___x_2701_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___redArg___boxed(lean_object* v_ref_2702_, lean_object* v_preserveOrder_2703_, lean_object* v_filterExport_2704_, lean_object* v_a_2705_){
_start:
{
uint8_t v_preserveOrder_boxed_2706_; lean_object* v_res_2707_; 
v_preserveOrder_boxed_2706_ = lean_unbox(v_preserveOrder_2703_);
v_res_2707_ = l_Lean_registerParametricAttributeExt___redArg(v_ref_2702_, v_preserveOrder_boxed_2706_, v_filterExport_2704_);
return v_res_2707_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt(lean_object* v_00_u03b1_2708_, lean_object* v_ref_2709_, uint8_t v_preserveOrder_2710_, lean_object* v_filterExport_2711_){
_start:
{
lean_object* v___x_2713_; 
v___x_2713_ = l_Lean_registerParametricAttributeExt___redArg(v_ref_2709_, v_preserveOrder_2710_, v_filterExport_2711_);
return v___x_2713_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeExt___boxed(lean_object* v_00_u03b1_2714_, lean_object* v_ref_2715_, lean_object* v_preserveOrder_2716_, lean_object* v_filterExport_2717_, lean_object* v_a_2718_){
_start:
{
uint8_t v_preserveOrder_boxed_2719_; lean_object* v_res_2720_; 
v_preserveOrder_boxed_2719_ = lean_unbox(v_preserveOrder_2716_);
v_res_2720_ = l_Lean_registerParametricAttributeExt(v_00_u03b1_2714_, v_ref_2715_, v_preserveOrder_boxed_2719_, v_filterExport_2717_);
return v_res_2720_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0(lean_object* v_00_u03b1_2721_, lean_object* v_filterExport_2722_, lean_object* v_env_2723_, lean_object* v_as_2724_, size_t v_i_2725_, size_t v_stop_2726_, lean_object* v_b_2727_){
_start:
{
lean_object* v___x_2728_; 
v___x_2728_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0___redArg(v_filterExport_2722_, v_env_2723_, v_as_2724_, v_i_2725_, v_stop_2726_, v_b_2727_);
return v___x_2728_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0___boxed(lean_object* v_00_u03b1_2729_, lean_object* v_filterExport_2730_, lean_object* v_env_2731_, lean_object* v_as_2732_, lean_object* v_i_2733_, lean_object* v_stop_2734_, lean_object* v_b_2735_){
_start:
{
size_t v_i_boxed_2736_; size_t v_stop_boxed_2737_; lean_object* v_res_2738_; 
v_i_boxed_2736_ = lean_unbox_usize(v_i_2733_);
lean_dec(v_i_2733_);
v_stop_boxed_2737_ = lean_unbox_usize(v_stop_2734_);
lean_dec(v_stop_2734_);
v_res_2738_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerParametricAttributeExt_spec__0(v_00_u03b1_2729_, v_filterExport_2730_, v_env_2731_, v_as_2732_, v_i_boxed_2736_, v_stop_boxed_2737_, v_b_2735_);
lean_dec_ref(v_as_2732_);
return v_res_2738_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1___redArg(lean_object* v_init_2739_, lean_object* v_t_2740_){
_start:
{
lean_object* v___x_2741_; 
v___x_2741_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg(v_init_2739_, v_t_2740_);
return v___x_2741_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1___redArg___boxed(lean_object* v_init_2742_, lean_object* v_t_2743_){
_start:
{
lean_object* v_res_2744_; 
v_res_2744_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1___redArg(v_init_2742_, v_t_2743_);
lean_dec(v_t_2743_);
return v_res_2744_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1(lean_object* v_00_u03b1_2745_, lean_object* v_init_2746_, lean_object* v_t_2747_){
_start:
{
lean_object* v___x_2748_; 
v___x_2748_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg(v_init_2746_, v_t_2747_);
return v___x_2748_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1___boxed(lean_object* v_00_u03b1_2749_, lean_object* v_init_2750_, lean_object* v_t_2751_){
_start:
{
lean_object* v_res_2752_; 
v_res_2752_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1(v_00_u03b1_2749_, v_init_2750_, v_t_2751_);
lean_dec(v_t_2751_);
return v_res_2752_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2(lean_object* v_00_u03b1_2753_, lean_object* v_n_2754_, lean_object* v_as_2755_, lean_object* v_lo_2756_, lean_object* v_hi_2757_, lean_object* v_w_2758_, lean_object* v_hlo_2759_, lean_object* v_hhi_2760_){
_start:
{
lean_object* v___x_2761_; 
v___x_2761_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg(v_n_2754_, v_as_2755_, v_lo_2756_, v_hi_2757_);
return v___x_2761_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___boxed(lean_object* v_00_u03b1_2762_, lean_object* v_n_2763_, lean_object* v_as_2764_, lean_object* v_lo_2765_, lean_object* v_hi_2766_, lean_object* v_w_2767_, lean_object* v_hlo_2768_, lean_object* v_hhi_2769_){
_start:
{
lean_object* v_res_2770_; 
v_res_2770_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2(v_00_u03b1_2762_, v_n_2763_, v_as_2764_, v_lo_2765_, v_hi_2766_, v_w_2767_, v_hlo_2768_, v_hhi_2769_);
lean_dec(v_hi_2766_);
lean_dec(v_n_2763_);
return v_res_2770_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3(lean_object* v_00_u03b1_2771_, lean_object* v_snd_2772_, lean_object* v_as_2773_, lean_object* v_start_2774_, lean_object* v_stop_2775_){
_start:
{
lean_object* v___x_2776_; 
v___x_2776_ = l_Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3___redArg(v_snd_2772_, v_as_2773_, v_start_2774_, v_stop_2775_);
return v___x_2776_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3___boxed(lean_object* v_00_u03b1_2777_, lean_object* v_snd_2778_, lean_object* v_as_2779_, lean_object* v_start_2780_, lean_object* v_stop_2781_){
_start:
{
lean_object* v_res_2782_; 
v_res_2782_ = l_Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3(v_00_u03b1_2777_, v_snd_2778_, v_as_2779_, v_start_2780_, v_stop_2781_);
lean_dec(v_stop_2781_);
lean_dec(v_start_2780_);
lean_dec_ref(v_as_2779_);
lean_dec(v_snd_2778_);
return v_res_2782_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1(lean_object* v_00_u03b1_2783_, lean_object* v_init_2784_, lean_object* v_x_2785_){
_start:
{
lean_object* v___x_2786_; 
v___x_2786_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg(v_init_2784_, v_x_2785_);
return v___x_2786_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___boxed(lean_object* v_00_u03b1_2787_, lean_object* v_init_2788_, lean_object* v_x_2789_){
_start:
{
lean_object* v_res_2790_; 
v_res_2790_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1(v_00_u03b1_2787_, v_init_2788_, v_x_2789_);
lean_dec(v_x_2789_);
return v_res_2790_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2_spec__3(lean_object* v_00_u03b1_2791_, lean_object* v_n_2792_, lean_object* v_lo_2793_, lean_object* v_hi_2794_, lean_object* v_hhi_2795_, lean_object* v_pivot_2796_, lean_object* v_as_2797_, lean_object* v_i_2798_, lean_object* v_k_2799_, lean_object* v_ilo_2800_, lean_object* v_ik_2801_, lean_object* v_w_2802_){
_start:
{
lean_object* v___x_2803_; 
v___x_2803_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2_spec__3___redArg(v_hi_2794_, v_pivot_2796_, v_as_2797_, v_i_2798_, v_k_2799_);
return v___x_2803_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2_spec__3___boxed(lean_object* v_00_u03b1_2804_, lean_object* v_n_2805_, lean_object* v_lo_2806_, lean_object* v_hi_2807_, lean_object* v_hhi_2808_, lean_object* v_pivot_2809_, lean_object* v_as_2810_, lean_object* v_i_2811_, lean_object* v_k_2812_, lean_object* v_ilo_2813_, lean_object* v_ik_2814_, lean_object* v_w_2815_){
_start:
{
lean_object* v_res_2816_; 
v_res_2816_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2_spec__3(v_00_u03b1_2804_, v_n_2805_, v_lo_2806_, v_hi_2807_, v_hhi_2808_, v_pivot_2809_, v_as_2810_, v_i_2811_, v_k_2812_, v_ilo_2813_, v_ik_2814_, v_w_2815_);
lean_dec_ref(v_pivot_2809_);
lean_dec(v_hi_2807_);
lean_dec(v_lo_2806_);
lean_dec(v_n_2805_);
return v_res_2816_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5(lean_object* v_00_u03b1_2817_, lean_object* v_snd_2818_, lean_object* v_as_2819_, size_t v_i_2820_, size_t v_stop_2821_, lean_object* v_b_2822_){
_start:
{
lean_object* v___x_2823_; 
v___x_2823_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5___redArg(v_snd_2818_, v_as_2819_, v_i_2820_, v_stop_2821_, v_b_2822_);
return v___x_2823_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5___boxed(lean_object* v_00_u03b1_2824_, lean_object* v_snd_2825_, lean_object* v_as_2826_, lean_object* v_i_2827_, lean_object* v_stop_2828_, lean_object* v_b_2829_){
_start:
{
size_t v_i_boxed_2830_; size_t v_stop_boxed_2831_; lean_object* v_res_2832_; 
v_i_boxed_2830_ = lean_unbox_usize(v_i_2827_);
lean_dec(v_i_2827_);
v_stop_boxed_2831_ = lean_unbox_usize(v_stop_2828_);
lean_dec(v_stop_2828_);
v_res_2832_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_registerParametricAttributeExt_spec__3_spec__5(v_00_u03b1_2824_, v_snd_2825_, v_as_2826_, v_i_boxed_2830_, v_stop_boxed_2831_, v_b_2829_);
lean_dec_ref(v_as_2826_);
lean_dec(v_snd_2825_);
return v_res_2832_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_registerParametricAttributeForExt_spec__0___redArg(lean_object* v_env_2833_, lean_object* v___y_2834_){
_start:
{
lean_object* v___x_2836_; lean_object* v_nextMacroScope_2837_; lean_object* v_ngen_2838_; lean_object* v_auxDeclNGen_2839_; lean_object* v_traceState_2840_; lean_object* v_messages_2841_; lean_object* v_infoState_2842_; lean_object* v_snapshotTasks_2843_; lean_object* v___x_2845_; uint8_t v_isShared_2846_; uint8_t v_isSharedCheck_2854_; 
v___x_2836_ = lean_st_ref_take(v___y_2834_);
v_nextMacroScope_2837_ = lean_ctor_get(v___x_2836_, 1);
v_ngen_2838_ = lean_ctor_get(v___x_2836_, 2);
v_auxDeclNGen_2839_ = lean_ctor_get(v___x_2836_, 3);
v_traceState_2840_ = lean_ctor_get(v___x_2836_, 4);
v_messages_2841_ = lean_ctor_get(v___x_2836_, 6);
v_infoState_2842_ = lean_ctor_get(v___x_2836_, 7);
v_snapshotTasks_2843_ = lean_ctor_get(v___x_2836_, 8);
v_isSharedCheck_2854_ = !lean_is_exclusive(v___x_2836_);
if (v_isSharedCheck_2854_ == 0)
{
lean_object* v_unused_2855_; lean_object* v_unused_2856_; 
v_unused_2855_ = lean_ctor_get(v___x_2836_, 5);
lean_dec(v_unused_2855_);
v_unused_2856_ = lean_ctor_get(v___x_2836_, 0);
lean_dec(v_unused_2856_);
v___x_2845_ = v___x_2836_;
v_isShared_2846_ = v_isSharedCheck_2854_;
goto v_resetjp_2844_;
}
else
{
lean_inc(v_snapshotTasks_2843_);
lean_inc(v_infoState_2842_);
lean_inc(v_messages_2841_);
lean_inc(v_traceState_2840_);
lean_inc(v_auxDeclNGen_2839_);
lean_inc(v_ngen_2838_);
lean_inc(v_nextMacroScope_2837_);
lean_dec(v___x_2836_);
v___x_2845_ = lean_box(0);
v_isShared_2846_ = v_isSharedCheck_2854_;
goto v_resetjp_2844_;
}
v_resetjp_2844_:
{
lean_object* v___x_2847_; lean_object* v___x_2849_; 
v___x_2847_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2);
if (v_isShared_2846_ == 0)
{
lean_ctor_set(v___x_2845_, 5, v___x_2847_);
lean_ctor_set(v___x_2845_, 0, v_env_2833_);
v___x_2849_ = v___x_2845_;
goto v_reusejp_2848_;
}
else
{
lean_object* v_reuseFailAlloc_2853_; 
v_reuseFailAlloc_2853_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2853_, 0, v_env_2833_);
lean_ctor_set(v_reuseFailAlloc_2853_, 1, v_nextMacroScope_2837_);
lean_ctor_set(v_reuseFailAlloc_2853_, 2, v_ngen_2838_);
lean_ctor_set(v_reuseFailAlloc_2853_, 3, v_auxDeclNGen_2839_);
lean_ctor_set(v_reuseFailAlloc_2853_, 4, v_traceState_2840_);
lean_ctor_set(v_reuseFailAlloc_2853_, 5, v___x_2847_);
lean_ctor_set(v_reuseFailAlloc_2853_, 6, v_messages_2841_);
lean_ctor_set(v_reuseFailAlloc_2853_, 7, v_infoState_2842_);
lean_ctor_set(v_reuseFailAlloc_2853_, 8, v_snapshotTasks_2843_);
v___x_2849_ = v_reuseFailAlloc_2853_;
goto v_reusejp_2848_;
}
v_reusejp_2848_:
{
lean_object* v___x_2850_; lean_object* v___x_2851_; lean_object* v___x_2852_; 
v___x_2850_ = lean_st_ref_put(v___y_2834_, v___x_2849_);
v___x_2851_ = lean_box(0);
v___x_2852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2852_, 0, v___x_2851_);
return v___x_2852_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_registerParametricAttributeForExt_spec__0___redArg___boxed(lean_object* v_env_2857_, lean_object* v___y_2858_, lean_object* v___y_2859_){
_start:
{
lean_object* v_res_2860_; 
v_res_2860_ = l_Lean_setEnv___at___00Lean_registerParametricAttributeForExt_spec__0___redArg(v_env_2857_, v___y_2858_);
lean_dec(v___y_2858_);
return v_res_2860_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_registerParametricAttributeForExt_spec__0(lean_object* v_env_2861_, lean_object* v___y_2862_, lean_object* v___y_2863_){
_start:
{
lean_object* v___x_2865_; 
v___x_2865_ = l_Lean_setEnv___at___00Lean_registerParametricAttributeForExt_spec__0___redArg(v_env_2861_, v___y_2863_);
return v___x_2865_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_registerParametricAttributeForExt_spec__0___boxed(lean_object* v_env_2866_, lean_object* v___y_2867_, lean_object* v___y_2868_, lean_object* v___y_2869_){
_start:
{
lean_object* v_res_2870_; 
v_res_2870_ = l_Lean_setEnv___at___00Lean_registerParametricAttributeForExt_spec__0(v_env_2866_, v___y_2867_, v___y_2868_);
lean_dec(v___y_2868_);
lean_dec_ref(v___y_2867_);
return v_res_2870_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerParametricAttributeForExt___redArg___lam__0(lean_object* v_getParam_2871_, lean_object* v_ext_2872_, lean_object* v_afterSet_2873_, lean_object* v_toAttributeImplCore_2874_, lean_object* v_decl_2875_, lean_object* v_stx_2876_, uint8_t v_kind_2877_, lean_object* v___y_2878_, lean_object* v___y_2879_){
_start:
{
lean_object* v___y_2882_; lean_object* v___y_2883_; lean_object* v___y_2884_; lean_object* v___y_2885_; uint8_t v___y_2886_; lean_object* v___y_2889_; lean_object* v___y_2890_; lean_object* v___y_2891_; uint8_t v___x_2935_; uint8_t v___x_2936_; 
v___x_2935_ = 0;
v___x_2936_ = l_Lean_instBEqAttributeKind_beq(v_kind_2877_, v___x_2935_);
if (v___x_2936_ == 0)
{
lean_object* v_name_2937_; lean_object* v___x_2938_; 
lean_dec(v_stx_2876_);
lean_dec(v_decl_2875_);
lean_dec_ref(v_afterSet_2873_);
lean_dec_ref(v_ext_2872_);
lean_dec_ref(v_getParam_2871_);
v_name_2937_ = lean_ctor_get(v_toAttributeImplCore_2874_, 1);
lean_inc(v_name_2937_);
lean_dec_ref(v_toAttributeImplCore_2874_);
v___x_2938_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg(v_name_2937_, v_kind_2877_, v___y_2878_, v___y_2879_);
return v___x_2938_;
}
else
{
goto v___jp_2929_;
}
v___jp_2881_:
{
if (v___y_2886_ == 0)
{
lean_object* v___x_2887_; 
lean_dec_ref(v___y_2883_);
v___x_2887_ = l_Lean_setEnv___at___00Lean_registerParametricAttributeForExt_spec__0___redArg(v___y_2882_, v___y_2884_);
return v___x_2887_;
}
else
{
lean_dec_ref(v___y_2882_);
return v___y_2883_;
}
}
v___jp_2888_:
{
lean_object* v___x_2892_; 
lean_inc(v___y_2891_);
lean_inc_ref(v___y_2890_);
lean_inc(v_decl_2875_);
v___x_2892_ = lean_apply_5(v_getParam_2871_, v_decl_2875_, v_stx_2876_, v___y_2890_, v___y_2891_, lean_box(0));
if (lean_obj_tag(v___x_2892_) == 0)
{
lean_object* v_a_2893_; lean_object* v___x_2894_; lean_object* v_toEnvExtension_2895_; lean_object* v_env_2896_; lean_object* v_nextMacroScope_2897_; lean_object* v_ngen_2898_; lean_object* v_auxDeclNGen_2899_; lean_object* v_traceState_2900_; lean_object* v_messages_2901_; lean_object* v_infoState_2902_; lean_object* v_snapshotTasks_2903_; lean_object* v___x_2905_; uint8_t v_isShared_2906_; uint8_t v_isSharedCheck_2919_; 
v_a_2893_ = lean_ctor_get(v___x_2892_, 0);
lean_inc(v_a_2893_);
lean_dec_ref_known(v___x_2892_, 1);
v___x_2894_ = lean_st_ref_take(v___y_2891_);
v_toEnvExtension_2895_ = lean_ctor_get(v_ext_2872_, 0);
v_env_2896_ = lean_ctor_get(v___x_2894_, 0);
v_nextMacroScope_2897_ = lean_ctor_get(v___x_2894_, 1);
v_ngen_2898_ = lean_ctor_get(v___x_2894_, 2);
v_auxDeclNGen_2899_ = lean_ctor_get(v___x_2894_, 3);
v_traceState_2900_ = lean_ctor_get(v___x_2894_, 4);
v_messages_2901_ = lean_ctor_get(v___x_2894_, 6);
v_infoState_2902_ = lean_ctor_get(v___x_2894_, 7);
v_snapshotTasks_2903_ = lean_ctor_get(v___x_2894_, 8);
v_isSharedCheck_2919_ = !lean_is_exclusive(v___x_2894_);
if (v_isSharedCheck_2919_ == 0)
{
lean_object* v_unused_2920_; 
v_unused_2920_ = lean_ctor_get(v___x_2894_, 5);
lean_dec(v_unused_2920_);
v___x_2905_ = v___x_2894_;
v_isShared_2906_ = v_isSharedCheck_2919_;
goto v_resetjp_2904_;
}
else
{
lean_inc(v_snapshotTasks_2903_);
lean_inc(v_infoState_2902_);
lean_inc(v_messages_2901_);
lean_inc(v_traceState_2900_);
lean_inc(v_auxDeclNGen_2899_);
lean_inc(v_ngen_2898_);
lean_inc(v_nextMacroScope_2897_);
lean_inc(v_env_2896_);
lean_dec(v___x_2894_);
v___x_2905_ = lean_box(0);
v_isShared_2906_ = v_isSharedCheck_2919_;
goto v_resetjp_2904_;
}
v_resetjp_2904_:
{
lean_object* v_asyncMode_2907_; lean_object* v___x_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; lean_object* v___x_2912_; 
v_asyncMode_2907_ = lean_ctor_get(v_toEnvExtension_2895_, 2);
lean_inc(v_asyncMode_2907_);
lean_inc(v_a_2893_);
lean_inc_n(v_decl_2875_, 2);
v___x_2908_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2908_, 0, v_decl_2875_);
lean_ctor_set(v___x_2908_, 1, v_a_2893_);
v___x_2909_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_ext_2872_, v_env_2896_, v___x_2908_, v_asyncMode_2907_, v_decl_2875_);
lean_dec(v_asyncMode_2907_);
v___x_2910_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2);
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
v_reuseFailAlloc_2918_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2918_, 0, v___x_2909_);
lean_ctor_set(v_reuseFailAlloc_2918_, 1, v_nextMacroScope_2897_);
lean_ctor_set(v_reuseFailAlloc_2918_, 2, v_ngen_2898_);
lean_ctor_set(v_reuseFailAlloc_2918_, 3, v_auxDeclNGen_2899_);
lean_ctor_set(v_reuseFailAlloc_2918_, 4, v_traceState_2900_);
lean_ctor_set(v_reuseFailAlloc_2918_, 5, v___x_2910_);
lean_ctor_set(v_reuseFailAlloc_2918_, 6, v_messages_2901_);
lean_ctor_set(v_reuseFailAlloc_2918_, 7, v_infoState_2902_);
lean_ctor_set(v_reuseFailAlloc_2918_, 8, v_snapshotTasks_2903_);
v___x_2912_ = v_reuseFailAlloc_2918_;
goto v_reusejp_2911_;
}
v_reusejp_2911_:
{
lean_object* v___x_2913_; lean_object* v___x_2914_; 
v___x_2913_ = lean_st_ref_put(v___y_2891_, v___x_2912_);
lean_inc(v___y_2891_);
lean_inc_ref(v___y_2890_);
v___x_2914_ = lean_apply_5(v_afterSet_2873_, v_decl_2875_, v_a_2893_, v___y_2890_, v___y_2891_, lean_box(0));
if (lean_obj_tag(v___x_2914_) == 0)
{
lean_dec_ref(v___y_2889_);
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
v___y_2882_ = v___y_2889_;
v___y_2883_ = v___x_2914_;
v___y_2884_ = v___y_2891_;
v___y_2885_ = v___y_2890_;
v___y_2886_ = v___x_2917_;
goto v___jp_2881_;
}
else
{
lean_dec(v_a_2915_);
v___y_2882_ = v___y_2889_;
v___y_2883_ = v___x_2914_;
v___y_2884_ = v___y_2891_;
v___y_2885_ = v___y_2890_;
v___y_2886_ = v___x_2916_;
goto v___jp_2881_;
}
}
}
}
}
else
{
lean_object* v_a_2921_; lean_object* v___x_2923_; uint8_t v_isShared_2924_; uint8_t v_isSharedCheck_2928_; 
lean_dec_ref(v___y_2889_);
lean_dec(v_decl_2875_);
lean_dec_ref(v_afterSet_2873_);
lean_dec_ref(v_ext_2872_);
v_a_2921_ = lean_ctor_get(v___x_2892_, 0);
v_isSharedCheck_2928_ = !lean_is_exclusive(v___x_2892_);
if (v_isSharedCheck_2928_ == 0)
{
v___x_2923_ = v___x_2892_;
v_isShared_2924_ = v_isSharedCheck_2928_;
goto v_resetjp_2922_;
}
else
{
lean_inc(v_a_2921_);
lean_dec(v___x_2892_);
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
v___x_2930_ = lean_st_ref_get(v___y_2879_);
v_env_2931_ = lean_ctor_get(v___x_2930_, 0);
lean_inc_ref(v_env_2931_);
lean_dec(v___x_2930_);
v___x_2932_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2931_, v_decl_2875_);
if (lean_obj_tag(v___x_2932_) == 0)
{
lean_dec_ref(v_toAttributeImplCore_2874_);
v___y_2889_ = v_env_2931_;
v___y_2890_ = v___y_2878_;
v___y_2891_ = v___y_2879_;
goto v___jp_2888_;
}
else
{
lean_object* v_name_2933_; lean_object* v___x_2934_; 
lean_dec_ref_known(v___x_2932_, 1);
lean_dec_ref(v_env_2931_);
lean_dec(v_stx_2876_);
lean_dec_ref(v_afterSet_2873_);
lean_dec_ref(v_ext_2872_);
lean_dec_ref(v_getParam_2871_);
v_name_2933_ = lean_ctor_get(v_toAttributeImplCore_2874_, 1);
lean_inc(v_name_2933_);
lean_dec_ref(v_toAttributeImplCore_2874_);
v___x_2934_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg(v_name_2933_, v_decl_2875_, v___y_2878_, v___y_2879_);
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
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___lam__0(lean_object* v_x_3272_, lean_object* v___y_3273_){
_start:
{
lean_object* v___x_3275_; lean_object* v___x_3276_; 
v___x_3275_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___lam__0___closed__1));
v___x_3276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3276_, 0, v___x_3275_);
return v___x_3276_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___lam__0___boxed(lean_object* v_x_3277_, lean_object* v___y_3278_, lean_object* v___y_3279_){
_start:
{
lean_object* v_res_3280_; 
v_res_3280_ = l_Lean_instInhabitedEnumAttributes_default___lam__0(v_x_3277_, v___y_3278_);
lean_dec_ref(v___y_3278_);
lean_dec_ref(v_x_3277_);
return v_res_3280_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___lam__1(lean_object* v_s_3281_, lean_object* v_x_3282_){
_start:
{
lean_inc(v_s_3281_);
return v_s_3281_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___lam__1___boxed(lean_object* v_s_3283_, lean_object* v_x_3284_){
_start:
{
lean_object* v_res_3285_; 
v_res_3285_ = l_Lean_instInhabitedEnumAttributes_default___lam__1(v_s_3283_, v_x_3284_);
lean_dec_ref(v_x_3284_);
lean_dec(v_s_3283_);
return v_res_3285_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___lam__2(lean_object* v_x_3286_, lean_object* v_x_3287_){
_start:
{
lean_object* v___x_3288_; 
v___x_3288_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___lam__2___closed__1));
return v___x_3288_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default___lam__2___boxed(lean_object* v_x_3289_, lean_object* v_x_3290_){
_start:
{
lean_object* v_res_3291_; 
v_res_3291_ = l_Lean_instInhabitedEnumAttributes_default___lam__2(v_x_3289_, v_x_3290_);
lean_dec(v_x_3290_);
lean_dec_ref(v_x_3289_);
return v_res_3291_;
}
}
static lean_object* _init_l_Lean_instInhabitedEnumAttributes_default___closed__3(void){
_start:
{
lean_object* v___x_3295_; 
v___x_3295_ = l_Lean_instInhabitedEnvExtension_default(lean_box(0));
return v___x_3295_;
}
}
static lean_object* _init_l_Lean_instInhabitedEnumAttributes_default___closed__4(void){
_start:
{
lean_object* v___f_3296_; lean_object* v___f_3297_; lean_object* v___f_3298_; lean_object* v___f_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; 
v___f_3296_ = ((lean_object*)(l_Lean_instInhabitedTagAttribute_default___closed__3));
v___f_3297_ = ((lean_object*)(l_Lean_instInhabitedEnumAttributes_default___closed__2));
v___f_3298_ = ((lean_object*)(l_Lean_instInhabitedEnumAttributes_default___closed__1));
v___f_3299_ = ((lean_object*)(l_Lean_instInhabitedEnumAttributes_default___closed__0));
v___x_3300_ = lean_box(0);
v___x_3301_ = lean_obj_once(&l_Lean_instInhabitedEnumAttributes_default___closed__3, &l_Lean_instInhabitedEnumAttributes_default___closed__3_once, _init_l_Lean_instInhabitedEnumAttributes_default___closed__3);
v___x_3302_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3302_, 0, v___x_3301_);
lean_ctor_set(v___x_3302_, 1, v___x_3300_);
lean_ctor_set(v___x_3302_, 2, v___f_3299_);
lean_ctor_set(v___x_3302_, 3, v___f_3298_);
lean_ctor_set(v___x_3302_, 4, v___f_3297_);
lean_ctor_set(v___x_3302_, 5, v___f_3296_);
return v___x_3302_;
}
}
static lean_object* _init_l_Lean_instInhabitedEnumAttributes_default___closed__5(void){
_start:
{
lean_object* v___x_3303_; lean_object* v___x_3304_; lean_object* v___x_3305_; 
v___x_3303_ = lean_obj_once(&l_Lean_instInhabitedEnumAttributes_default___closed__4, &l_Lean_instInhabitedEnumAttributes_default___closed__4_once, _init_l_Lean_instInhabitedEnumAttributes_default___closed__4);
v___x_3304_ = lean_box(0);
v___x_3305_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3305_, 0, v___x_3304_);
lean_ctor_set(v___x_3305_, 1, v___x_3303_);
return v___x_3305_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes_default(lean_object* v_00_u03b1_3306_){
_start:
{
lean_object* v___x_3307_; 
v___x_3307_ = lean_obj_once(&l_Lean_instInhabitedEnumAttributes_default___closed__5, &l_Lean_instInhabitedEnumAttributes_default___closed__5_once, _init_l_Lean_instInhabitedEnumAttributes_default___closed__5);
return v___x_3307_;
}
}
static lean_object* _init_l_Lean_instInhabitedEnumAttributes___closed__0(void){
_start:
{
lean_object* v___x_3308_; 
v___x_3308_ = l_Lean_instInhabitedEnumAttributes_default(lean_box(0));
return v___x_3308_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedEnumAttributes(lean_object* v_a_3309_){
_start:
{
lean_object* v___x_3310_; 
v___x_3310_ = lean_obj_once(&l_Lean_instInhabitedEnumAttributes___closed__0, &l_Lean_instInhabitedEnumAttributes___closed__0_once, _init_l_Lean_instInhabitedEnumAttributes___closed__0);
return v___x_3310_;
}
}
static lean_object* _init_l_Lean_registerEnumAttributes___auto__1(void){
_start:
{
lean_object* v___x_3311_; 
v___x_3311_ = lean_obj_once(&l_Lean_AttributeImplCore_ref___autoParam___closed__28, &l_Lean_AttributeImplCore_ref___autoParam___closed__28_once, _init_l_Lean_AttributeImplCore_ref___autoParam___closed__28);
return v___x_3311_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__0(lean_object* v_x_3312_){
_start:
{
lean_object* v___x_3313_; 
v___x_3313_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___lam__2___closed__0));
return v___x_3313_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__0___boxed(lean_object* v_x_3314_){
_start:
{
lean_object* v_res_3315_; 
v_res_3315_ = l_Lean_registerEnumAttributes___redArg___lam__0(v_x_3314_);
lean_dec(v_x_3314_);
return v_res_3315_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___redArg(lean_object* v_newState_3316_, lean_object* v_x_3317_, lean_object* v_x_3318_){
_start:
{
if (lean_obj_tag(v_x_3318_) == 0)
{
return v_x_3317_;
}
else
{
lean_object* v_head_3319_; lean_object* v_tail_3320_; lean_object* v___x_3321_; 
v_head_3319_ = lean_ctor_get(v_x_3318_, 0);
lean_inc(v_head_3319_);
v_tail_3320_ = lean_ctor_get(v_x_3318_, 1);
lean_inc(v_tail_3320_);
lean_dec_ref_known(v_x_3318_, 2);
v___x_3321_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_newState_3316_, v_head_3319_);
if (lean_obj_tag(v___x_3321_) == 1)
{
lean_object* v_val_3322_; lean_object* v___x_3323_; 
v_val_3322_ = lean_ctor_get(v___x_3321_, 0);
lean_inc(v_val_3322_);
lean_dec_ref_known(v___x_3321_, 1);
v___x_3323_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_head_3319_, v_val_3322_, v_x_3317_);
v_x_3317_ = v___x_3323_;
v_x_3318_ = v_tail_3320_;
goto _start;
}
else
{
lean_dec(v___x_3321_);
lean_dec(v_head_3319_);
v_x_3318_ = v_tail_3320_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___redArg___boxed(lean_object* v_newState_3326_, lean_object* v_x_3327_, lean_object* v_x_3328_){
_start:
{
lean_object* v_res_3329_; 
v_res_3329_ = l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___redArg(v_newState_3326_, v_x_3327_, v_x_3328_);
lean_dec(v_newState_3326_);
return v_res_3329_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__1(lean_object* v_x_3330_, lean_object* v_newState_3331_, lean_object* v_consts_3332_, lean_object* v_st_3333_){
_start:
{
lean_object* v___x_3334_; 
v___x_3334_ = l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___redArg(v_newState_3331_, v_st_3333_, v_consts_3332_);
return v___x_3334_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__1___boxed(lean_object* v_x_3335_, lean_object* v_newState_3336_, lean_object* v_consts_3337_, lean_object* v_st_3338_){
_start:
{
lean_object* v_res_3339_; 
v_res_3339_ = l_Lean_registerEnumAttributes___redArg___lam__1(v_x_3335_, v_newState_3336_, v_consts_3337_, v_st_3338_);
lean_dec(v_newState_3336_);
lean_dec(v_x_3335_);
return v_res_3339_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__2(lean_object* v_s_3349_){
_start:
{
lean_object* v___x_3350_; lean_object* v___y_3352_; 
v___x_3350_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___lam__2___closed__3));
if (lean_obj_tag(v_s_3349_) == 0)
{
lean_object* v_size_3356_; 
v_size_3356_ = lean_ctor_get(v_s_3349_, 0);
lean_inc(v_size_3356_);
lean_dec_ref_known(v_s_3349_, 5);
v___y_3352_ = v_size_3356_;
goto v___jp_3351_;
}
else
{
lean_object* v___x_3357_; 
v___x_3357_ = lean_unsigned_to_nat(0u);
v___y_3352_ = v___x_3357_;
goto v___jp_3351_;
}
v___jp_3351_:
{
lean_object* v___x_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; 
v___x_3353_ = l_Nat_reprFast(v___y_3352_);
v___x_3354_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3354_, 0, v___x_3353_);
v___x_3355_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3355_, 0, v___x_3350_);
lean_ctor_set(v___x_3355_, 1, v___x_3354_);
return v___x_3355_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg(lean_object* v_env_3358_, lean_object* v_as_3359_, size_t v_i_3360_, size_t v_stop_3361_, lean_object* v_b_3362_){
_start:
{
lean_object* v___y_3364_; uint8_t v___x_3368_; 
v___x_3368_ = lean_usize_dec_eq(v_i_3360_, v_stop_3361_);
if (v___x_3368_ == 0)
{
lean_object* v___x_3369_; lean_object* v_fst_3370_; uint8_t v___x_3371_; lean_object* v___x_3372_; uint8_t v___x_3373_; 
v___x_3369_ = lean_array_uget_borrowed(v_as_3359_, v_i_3360_);
v_fst_3370_ = lean_ctor_get(v___x_3369_, 0);
v___x_3371_ = 1;
lean_inc_ref(v_env_3358_);
v___x_3372_ = l_Lean_Environment_setExporting(v_env_3358_, v___x_3371_);
lean_inc(v_fst_3370_);
v___x_3373_ = l_Lean_Environment_contains(v___x_3372_, v_fst_3370_, v___x_3368_);
if (v___x_3373_ == 0)
{
v___y_3364_ = v_b_3362_;
goto v___jp_3363_;
}
else
{
lean_object* v___x_3374_; 
lean_inc(v___x_3369_);
v___x_3374_ = lean_array_push(v_b_3362_, v___x_3369_);
v___y_3364_ = v___x_3374_;
goto v___jp_3363_;
}
}
else
{
lean_dec_ref(v_env_3358_);
return v_b_3362_;
}
v___jp_3363_:
{
size_t v___x_3365_; size_t v___x_3366_; 
v___x_3365_ = ((size_t)1ULL);
v___x_3366_ = lean_usize_add(v_i_3360_, v___x_3365_);
v_i_3360_ = v___x_3366_;
v_b_3362_ = v___y_3364_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg___boxed(lean_object* v_env_3375_, lean_object* v_as_3376_, lean_object* v_i_3377_, lean_object* v_stop_3378_, lean_object* v_b_3379_){
_start:
{
size_t v_i_boxed_3380_; size_t v_stop_boxed_3381_; lean_object* v_res_3382_; 
v_i_boxed_3380_ = lean_unbox_usize(v_i_3377_);
lean_dec(v_i_3377_);
v_stop_boxed_3381_ = lean_unbox_usize(v_stop_3378_);
lean_dec(v_stop_3378_);
v_res_3382_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg(v_env_3375_, v_as_3376_, v_i_boxed_3380_, v_stop_boxed_3381_, v_b_3379_);
lean_dec_ref(v_as_3376_);
return v_res_3382_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__3(lean_object* v_env_3383_, lean_object* v_m_3384_){
_start:
{
lean_object* v___x_3385_; lean_object* v___x_3386_; lean_object* v___y_3388_; lean_object* v___x_3402_; lean_object* v___x_3403_; lean_object* v___y_3405_; lean_object* v___y_3406_; uint8_t v___x_3408_; 
v___x_3385_ = lean_unsigned_to_nat(0u);
v___x_3386_ = ((lean_object*)(l_Lean_instInhabitedParametricAttribute_default___lam__2___closed__0));
v___x_3402_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_registerParametricAttributeExt_spec__1_spec__1___redArg(v___x_3386_, v_m_3384_);
v___x_3403_ = lean_array_get_size(v___x_3402_);
v___x_3408_ = lean_nat_dec_eq(v___x_3403_, v___x_3385_);
if (v___x_3408_ == 0)
{
lean_object* v___x_3409_; lean_object* v___x_3410_; lean_object* v___y_3412_; uint8_t v___x_3414_; 
v___x_3409_ = lean_unsigned_to_nat(1u);
v___x_3410_ = lean_nat_sub(v___x_3403_, v___x_3409_);
v___x_3414_ = lean_nat_dec_le(v___x_3385_, v___x_3410_);
if (v___x_3414_ == 0)
{
lean_inc(v___x_3410_);
v___y_3412_ = v___x_3410_;
goto v___jp_3411_;
}
else
{
v___y_3412_ = v___x_3385_;
goto v___jp_3411_;
}
v___jp_3411_:
{
uint8_t v___x_3413_; 
v___x_3413_ = lean_nat_dec_le(v___y_3412_, v___x_3410_);
if (v___x_3413_ == 0)
{
lean_dec(v___x_3410_);
lean_inc(v___y_3412_);
v___y_3405_ = v___y_3412_;
v___y_3406_ = v___y_3412_;
goto v___jp_3404_;
}
else
{
v___y_3405_ = v___y_3412_;
v___y_3406_ = v___x_3410_;
goto v___jp_3404_;
}
}
}
else
{
v___y_3388_ = v___x_3402_;
goto v___jp_3387_;
}
v___jp_3387_:
{
lean_object* v___x_3389_; uint8_t v___x_3390_; 
v___x_3389_ = lean_array_get_size(v___y_3388_);
v___x_3390_ = lean_nat_dec_lt(v___x_3385_, v___x_3389_);
if (v___x_3390_ == 0)
{
lean_object* v___x_3391_; 
lean_dec_ref(v_env_3383_);
v___x_3391_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3391_, 0, v___x_3386_);
lean_ctor_set(v___x_3391_, 1, v___x_3386_);
lean_ctor_set(v___x_3391_, 2, v___y_3388_);
return v___x_3391_;
}
else
{
uint8_t v___x_3392_; 
v___x_3392_ = lean_nat_dec_le(v___x_3389_, v___x_3389_);
if (v___x_3392_ == 0)
{
if (v___x_3390_ == 0)
{
lean_object* v___x_3393_; 
lean_dec_ref(v_env_3383_);
v___x_3393_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3393_, 0, v___x_3386_);
lean_ctor_set(v___x_3393_, 1, v___x_3386_);
lean_ctor_set(v___x_3393_, 2, v___y_3388_);
return v___x_3393_;
}
else
{
size_t v___x_3394_; size_t v___x_3395_; lean_object* v___x_3396_; lean_object* v___x_3397_; 
v___x_3394_ = ((size_t)0ULL);
v___x_3395_ = lean_usize_of_nat(v___x_3389_);
v___x_3396_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg(v_env_3383_, v___y_3388_, v___x_3394_, v___x_3395_, v___x_3386_);
lean_inc_ref(v___x_3396_);
v___x_3397_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3397_, 0, v___x_3396_);
lean_ctor_set(v___x_3397_, 1, v___x_3396_);
lean_ctor_set(v___x_3397_, 2, v___y_3388_);
return v___x_3397_;
}
}
else
{
size_t v___x_3398_; size_t v___x_3399_; lean_object* v___x_3400_; lean_object* v___x_3401_; 
v___x_3398_ = ((size_t)0ULL);
v___x_3399_ = lean_usize_of_nat(v___x_3389_);
v___x_3400_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg(v_env_3383_, v___y_3388_, v___x_3398_, v___x_3399_, v___x_3386_);
lean_inc_ref(v___x_3400_);
v___x_3401_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3401_, 0, v___x_3400_);
lean_ctor_set(v___x_3401_, 1, v___x_3400_);
lean_ctor_set(v___x_3401_, 2, v___y_3388_);
return v___x_3401_;
}
}
}
v___jp_3404_:
{
lean_object* v___x_3407_; 
v___x_3407_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_registerParametricAttributeExt_spec__2___redArg(v___x_3403_, v___x_3402_, v___y_3405_, v___y_3406_);
lean_dec(v___y_3406_);
v___y_3388_ = v___x_3407_;
goto v___jp_3387_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__3___boxed(lean_object* v_env_3415_, lean_object* v_m_3416_){
_start:
{
lean_object* v_res_3417_; 
v_res_3417_ = l_Lean_registerEnumAttributes___redArg___lam__3(v_env_3415_, v_m_3416_);
lean_dec(v_m_3416_);
return v_res_3417_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__4(lean_object* v_s_3418_, lean_object* v_p_3419_){
_start:
{
lean_object* v_fst_3420_; lean_object* v_snd_3421_; lean_object* v___x_3422_; 
v_fst_3420_ = lean_ctor_get(v_p_3419_, 0);
lean_inc(v_fst_3420_);
v_snd_3421_ = lean_ctor_get(v_p_3419_, 1);
lean_inc(v_snd_3421_);
lean_dec_ref(v_p_3419_);
v___x_3422_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_3420_, v_snd_3421_, v_s_3418_);
return v___x_3422_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__6(lean_object* v___x_3423_, lean_object* v_x_3424_, lean_object* v_x_3425_){
_start:
{
lean_object* v___x_3427_; 
v___x_3427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3427_, 0, v___x_3423_);
return v___x_3427_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___lam__6___boxed(lean_object* v___x_3428_, lean_object* v_x_3429_, lean_object* v_x_3430_, lean_object* v___y_3431_){
_start:
{
lean_object* v_res_3432_; 
v_res_3432_ = l_Lean_registerEnumAttributes___redArg___lam__6(v___x_3428_, v_x_3429_, v_x_3430_);
lean_dec_ref(v_x_3430_);
lean_dec_ref(v_x_3429_);
return v_res_3432_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_registerEnumAttributes_spec__3(lean_object* v_as_3433_){
_start:
{
if (lean_obj_tag(v_as_3433_) == 0)
{
lean_object* v___x_3435_; lean_object* v___x_3436_; 
v___x_3435_ = lean_box(0);
v___x_3436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3436_, 0, v___x_3435_);
return v___x_3436_;
}
else
{
lean_object* v_head_3437_; lean_object* v_tail_3438_; lean_object* v___x_3439_; 
v_head_3437_ = lean_ctor_get(v_as_3433_, 0);
lean_inc(v_head_3437_);
v_tail_3438_ = lean_ctor_get(v_as_3433_, 1);
lean_inc(v_tail_3438_);
lean_dec_ref_known(v_as_3433_, 2);
v___x_3439_ = l_Lean_registerBuiltinAttribute(v_head_3437_);
if (lean_obj_tag(v___x_3439_) == 0)
{
lean_dec_ref_known(v___x_3439_, 1);
v_as_3433_ = v_tail_3438_;
goto _start;
}
else
{
lean_dec(v_tail_3438_);
return v___x_3439_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_registerEnumAttributes_spec__3___boxed(lean_object* v_as_3441_, lean_object* v___y_3442_){
_start:
{
lean_object* v_res_3443_; 
v_res_3443_ = l_List_forM___at___00Lean_registerEnumAttributes_spec__3(v_as_3441_);
return v_res_3443_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__1(lean_object* v_validate_3444_, lean_object* v_snd_3445_, lean_object* v_a_3446_, lean_object* v_fst_3447_, lean_object* v_decl_3448_, lean_object* v_stx_3449_, uint8_t v_kind_3450_, lean_object* v___y_3451_, lean_object* v___y_3452_){
_start:
{
lean_object* v___y_3455_; lean_object* v___y_3456_; lean_object* v___y_3491_; lean_object* v___y_3492_; lean_object* v___x_3497_; 
v___x_3497_ = l_Lean_Attribute_Builtin_ensureNoArgs(v_stx_3449_, v___y_3451_, v___y_3452_);
if (lean_obj_tag(v___x_3497_) == 0)
{
uint8_t v___x_3498_; uint8_t v___x_3499_; 
lean_dec_ref_known(v___x_3497_, 1);
v___x_3498_ = 0;
v___x_3499_ = l_Lean_instBEqAttributeKind_beq(v_kind_3450_, v___x_3498_);
if (v___x_3499_ == 0)
{
lean_object* v___x_3500_; 
lean_dec(v_decl_3448_);
lean_dec_ref(v_a_3446_);
lean_dec(v_snd_3445_);
lean_dec_ref(v_validate_3444_);
v___x_3500_ = l_Lean_throwAttrMustBeGlobal___at___00Lean_registerTagAttribute_spec__6___redArg(v_fst_3447_, v_kind_3450_, v___y_3451_, v___y_3452_);
return v___x_3500_;
}
else
{
v___y_3491_ = v___y_3451_;
v___y_3492_ = v___y_3452_;
goto v___jp_3490_;
}
}
else
{
lean_dec(v_decl_3448_);
lean_dec(v_fst_3447_);
lean_dec_ref(v_a_3446_);
lean_dec(v_snd_3445_);
lean_dec_ref(v_validate_3444_);
return v___x_3497_;
}
v___jp_3454_:
{
lean_object* v___x_3457_; 
lean_inc(v___y_3456_);
lean_inc_ref(v___y_3455_);
lean_inc(v_snd_3445_);
lean_inc(v_decl_3448_);
v___x_3457_ = lean_apply_5(v_validate_3444_, v_decl_3448_, v_snd_3445_, v___y_3455_, v___y_3456_, lean_box(0));
if (lean_obj_tag(v___x_3457_) == 0)
{
lean_object* v___x_3459_; uint8_t v_isShared_3460_; uint8_t v_isSharedCheck_3488_; 
v_isSharedCheck_3488_ = !lean_is_exclusive(v___x_3457_);
if (v_isSharedCheck_3488_ == 0)
{
lean_object* v_unused_3489_; 
v_unused_3489_ = lean_ctor_get(v___x_3457_, 0);
lean_dec(v_unused_3489_);
v___x_3459_ = v___x_3457_;
v_isShared_3460_ = v_isSharedCheck_3488_;
goto v_resetjp_3458_;
}
else
{
lean_dec(v___x_3457_);
v___x_3459_ = lean_box(0);
v_isShared_3460_ = v_isSharedCheck_3488_;
goto v_resetjp_3458_;
}
v_resetjp_3458_:
{
lean_object* v___x_3461_; lean_object* v_toEnvExtension_3462_; lean_object* v_env_3463_; lean_object* v_nextMacroScope_3464_; lean_object* v_ngen_3465_; lean_object* v_auxDeclNGen_3466_; lean_object* v_traceState_3467_; lean_object* v_messages_3468_; lean_object* v_infoState_3469_; lean_object* v_snapshotTasks_3470_; lean_object* v___x_3472_; uint8_t v_isShared_3473_; uint8_t v_isSharedCheck_3486_; 
v___x_3461_ = lean_st_ref_take(v___y_3456_);
v_toEnvExtension_3462_ = lean_ctor_get(v_a_3446_, 0);
v_env_3463_ = lean_ctor_get(v___x_3461_, 0);
v_nextMacroScope_3464_ = lean_ctor_get(v___x_3461_, 1);
v_ngen_3465_ = lean_ctor_get(v___x_3461_, 2);
v_auxDeclNGen_3466_ = lean_ctor_get(v___x_3461_, 3);
v_traceState_3467_ = lean_ctor_get(v___x_3461_, 4);
v_messages_3468_ = lean_ctor_get(v___x_3461_, 6);
v_infoState_3469_ = lean_ctor_get(v___x_3461_, 7);
v_snapshotTasks_3470_ = lean_ctor_get(v___x_3461_, 8);
v_isSharedCheck_3486_ = !lean_is_exclusive(v___x_3461_);
if (v_isSharedCheck_3486_ == 0)
{
lean_object* v_unused_3487_; 
v_unused_3487_ = lean_ctor_get(v___x_3461_, 5);
lean_dec(v_unused_3487_);
v___x_3472_ = v___x_3461_;
v_isShared_3473_ = v_isSharedCheck_3486_;
goto v_resetjp_3471_;
}
else
{
lean_inc(v_snapshotTasks_3470_);
lean_inc(v_infoState_3469_);
lean_inc(v_messages_3468_);
lean_inc(v_traceState_3467_);
lean_inc(v_auxDeclNGen_3466_);
lean_inc(v_ngen_3465_);
lean_inc(v_nextMacroScope_3464_);
lean_inc(v_env_3463_);
lean_dec(v___x_3461_);
v___x_3472_ = lean_box(0);
v_isShared_3473_ = v_isSharedCheck_3486_;
goto v_resetjp_3471_;
}
v_resetjp_3471_:
{
lean_object* v_asyncMode_3474_; lean_object* v___x_3475_; lean_object* v___x_3476_; lean_object* v___x_3477_; lean_object* v___x_3479_; 
v_asyncMode_3474_ = lean_ctor_get(v_toEnvExtension_3462_, 2);
lean_inc(v_asyncMode_3474_);
lean_inc(v_decl_3448_);
v___x_3475_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3475_, 0, v_decl_3448_);
lean_ctor_set(v___x_3475_, 1, v_snd_3445_);
v___x_3476_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_a_3446_, v_env_3463_, v___x_3475_, v_asyncMode_3474_, v_decl_3448_);
lean_dec(v_asyncMode_3474_);
v___x_3477_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2, &l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_ensureAttrDeclIsPublic_spec__2___redArg___closed__2);
if (v_isShared_3473_ == 0)
{
lean_ctor_set(v___x_3472_, 5, v___x_3477_);
lean_ctor_set(v___x_3472_, 0, v___x_3476_);
v___x_3479_ = v___x_3472_;
goto v_reusejp_3478_;
}
else
{
lean_object* v_reuseFailAlloc_3485_; 
v_reuseFailAlloc_3485_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3485_, 0, v___x_3476_);
lean_ctor_set(v_reuseFailAlloc_3485_, 1, v_nextMacroScope_3464_);
lean_ctor_set(v_reuseFailAlloc_3485_, 2, v_ngen_3465_);
lean_ctor_set(v_reuseFailAlloc_3485_, 3, v_auxDeclNGen_3466_);
lean_ctor_set(v_reuseFailAlloc_3485_, 4, v_traceState_3467_);
lean_ctor_set(v_reuseFailAlloc_3485_, 5, v___x_3477_);
lean_ctor_set(v_reuseFailAlloc_3485_, 6, v_messages_3468_);
lean_ctor_set(v_reuseFailAlloc_3485_, 7, v_infoState_3469_);
lean_ctor_set(v_reuseFailAlloc_3485_, 8, v_snapshotTasks_3470_);
v___x_3479_ = v_reuseFailAlloc_3485_;
goto v_reusejp_3478_;
}
v_reusejp_3478_:
{
lean_object* v___x_3480_; lean_object* v___x_3481_; lean_object* v___x_3483_; 
v___x_3480_ = lean_st_ref_put(v___y_3456_, v___x_3479_);
v___x_3481_ = lean_box(0);
if (v_isShared_3460_ == 0)
{
lean_ctor_set(v___x_3459_, 0, v___x_3481_);
v___x_3483_ = v___x_3459_;
goto v_reusejp_3482_;
}
else
{
lean_object* v_reuseFailAlloc_3484_; 
v_reuseFailAlloc_3484_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3484_, 0, v___x_3481_);
v___x_3483_ = v_reuseFailAlloc_3484_;
goto v_reusejp_3482_;
}
v_reusejp_3482_:
{
return v___x_3483_;
}
}
}
}
}
else
{
lean_dec(v_decl_3448_);
lean_dec_ref(v_a_3446_);
lean_dec(v_snd_3445_);
return v___x_3457_;
}
}
v___jp_3490_:
{
lean_object* v___x_3493_; lean_object* v_env_3494_; lean_object* v___x_3495_; 
v___x_3493_ = lean_st_ref_get(v___y_3492_);
v_env_3494_ = lean_ctor_get(v___x_3493_, 0);
lean_inc_ref(v_env_3494_);
lean_dec(v___x_3493_);
v___x_3495_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3494_, v_decl_3448_);
lean_dec_ref(v_env_3494_);
if (lean_obj_tag(v___x_3495_) == 0)
{
lean_dec(v_fst_3447_);
v___y_3455_ = v___y_3491_;
v___y_3456_ = v___y_3492_;
goto v___jp_3454_;
}
else
{
lean_object* v___x_3496_; 
lean_dec_ref_known(v___x_3495_, 1);
lean_dec_ref(v_a_3446_);
lean_dec(v_snd_3445_);
lean_dec_ref(v_validate_3444_);
v___x_3496_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_registerTagAttribute_spec__5___redArg(v_fst_3447_, v_decl_3448_, v___y_3491_, v___y_3492_);
return v___x_3496_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__1___boxed(lean_object* v_validate_3501_, lean_object* v_snd_3502_, lean_object* v_a_3503_, lean_object* v_fst_3504_, lean_object* v_decl_3505_, lean_object* v_stx_3506_, lean_object* v_kind_3507_, lean_object* v___y_3508_, lean_object* v___y_3509_, lean_object* v___y_3510_){
_start:
{
uint8_t v_kind_boxed_3511_; lean_object* v_res_3512_; 
v_kind_boxed_3511_ = lean_unbox(v_kind_3507_);
v_res_3512_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__1(v_validate_3501_, v_snd_3502_, v_a_3503_, v_fst_3504_, v_decl_3505_, v_stx_3506_, v_kind_boxed_3511_, v___y_3508_, v___y_3509_);
lean_dec(v___y_3509_);
lean_dec_ref(v___y_3508_);
return v_res_3512_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__0(lean_object* v_fst_3513_, lean_object* v_decl_3514_, lean_object* v___y_3515_, lean_object* v___y_3516_){
_start:
{
lean_object* v___x_3518_; lean_object* v___x_3519_; lean_object* v___x_3520_; lean_object* v___x_3521_; lean_object* v___x_3522_; lean_object* v___x_3523_; 
v___x_3518_ = lean_obj_once(&l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1, &l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1_once, _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__1);
v___x_3519_ = l_Lean_MessageData_ofName(v_fst_3513_);
v___x_3520_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3520_, 0, v___x_3518_);
lean_ctor_set(v___x_3520_, 1, v___x_3519_);
v___x_3521_ = lean_obj_once(&l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3, &l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3_once, _init_l_Lean_instInhabitedAttributeImpl_default___lam__1___closed__3);
v___x_3522_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3522_, 0, v___x_3520_);
lean_ctor_set(v___x_3522_, 1, v___x_3521_);
v___x_3523_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_3522_, v___y_3515_, v___y_3516_);
return v___x_3523_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__0___boxed(lean_object* v_fst_3524_, lean_object* v_decl_3525_, lean_object* v___y_3526_, lean_object* v___y_3527_, lean_object* v___y_3528_){
_start:
{
lean_object* v_res_3529_; 
v_res_3529_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__0(v_fst_3524_, v_decl_3525_, v___y_3526_, v___y_3527_);
lean_dec(v___y_3527_);
lean_dec_ref(v___y_3526_);
lean_dec(v_decl_3525_);
return v_res_3529_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg(lean_object* v_validate_3530_, lean_object* v_a_3531_, lean_object* v_ref_3532_, uint8_t v_applicationTime_3533_, lean_object* v_a_3534_, lean_object* v_a_3535_){
_start:
{
if (lean_obj_tag(v_a_3534_) == 0)
{
lean_object* v___x_3536_; 
lean_dec(v_ref_3532_);
lean_dec_ref(v_a_3531_);
lean_dec_ref(v_validate_3530_);
v___x_3536_ = l_List_reverse___redArg(v_a_3535_);
return v___x_3536_;
}
else
{
lean_object* v_head_3537_; lean_object* v_snd_3538_; lean_object* v_tail_3539_; lean_object* v___x_3541_; uint8_t v_isShared_3542_; uint8_t v_isSharedCheck_3554_; 
v_head_3537_ = lean_ctor_get(v_a_3534_, 0);
lean_inc(v_head_3537_);
v_snd_3538_ = lean_ctor_get(v_head_3537_, 1);
lean_inc(v_snd_3538_);
v_tail_3539_ = lean_ctor_get(v_a_3534_, 1);
v_isSharedCheck_3554_ = !lean_is_exclusive(v_a_3534_);
if (v_isSharedCheck_3554_ == 0)
{
lean_object* v_unused_3555_; 
v_unused_3555_ = lean_ctor_get(v_a_3534_, 0);
lean_dec(v_unused_3555_);
v___x_3541_ = v_a_3534_;
v_isShared_3542_ = v_isSharedCheck_3554_;
goto v_resetjp_3540_;
}
else
{
lean_inc(v_tail_3539_);
lean_dec(v_a_3534_);
v___x_3541_ = lean_box(0);
v_isShared_3542_ = v_isSharedCheck_3554_;
goto v_resetjp_3540_;
}
v_resetjp_3540_:
{
lean_object* v_fst_3543_; lean_object* v_fst_3544_; lean_object* v_snd_3545_; lean_object* v___f_3546_; lean_object* v___f_3547_; lean_object* v___x_3548_; lean_object* v___x_3549_; lean_object* v___x_3551_; 
v_fst_3543_ = lean_ctor_get(v_head_3537_, 0);
lean_inc_n(v_fst_3543_, 3);
lean_dec(v_head_3537_);
v_fst_3544_ = lean_ctor_get(v_snd_3538_, 0);
lean_inc(v_fst_3544_);
v_snd_3545_ = lean_ctor_get(v_snd_3538_, 1);
lean_inc(v_snd_3545_);
lean_dec(v_snd_3538_);
v___f_3546_ = lean_alloc_closure((void*)(l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__0___boxed), 5, 1);
lean_closure_set(v___f_3546_, 0, v_fst_3543_);
lean_inc_ref(v_a_3531_);
lean_inc_ref(v_validate_3530_);
v___f_3547_ = lean_alloc_closure((void*)(l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___lam__1___boxed), 10, 4);
lean_closure_set(v___f_3547_, 0, v_validate_3530_);
lean_closure_set(v___f_3547_, 1, v_snd_3545_);
lean_closure_set(v___f_3547_, 2, v_a_3531_);
lean_closure_set(v___f_3547_, 3, v_fst_3543_);
lean_inc(v_ref_3532_);
v___x_3548_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_3548_, 0, v_ref_3532_);
lean_ctor_set(v___x_3548_, 1, v_fst_3543_);
lean_ctor_set(v___x_3548_, 2, v_fst_3544_);
lean_ctor_set_uint8(v___x_3548_, sizeof(void*)*3, v_applicationTime_3533_);
v___x_3549_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3549_, 0, v___x_3548_);
lean_ctor_set(v___x_3549_, 1, v___f_3547_);
lean_ctor_set(v___x_3549_, 2, v___f_3546_);
if (v_isShared_3542_ == 0)
{
lean_ctor_set(v___x_3541_, 1, v_a_3535_);
lean_ctor_set(v___x_3541_, 0, v___x_3549_);
v___x_3551_ = v___x_3541_;
goto v_reusejp_3550_;
}
else
{
lean_object* v_reuseFailAlloc_3553_; 
v_reuseFailAlloc_3553_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3553_, 0, v___x_3549_);
lean_ctor_set(v_reuseFailAlloc_3553_, 1, v_a_3535_);
v___x_3551_ = v_reuseFailAlloc_3553_;
goto v_reusejp_3550_;
}
v_reusejp_3550_:
{
v_a_3534_ = v_tail_3539_;
v_a_3535_ = v___x_3551_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg___boxed(lean_object* v_validate_3556_, lean_object* v_a_3557_, lean_object* v_ref_3558_, lean_object* v_applicationTime_3559_, lean_object* v_a_3560_, lean_object* v_a_3561_){
_start:
{
uint8_t v_applicationTime_boxed_3562_; lean_object* v_res_3563_; 
v_applicationTime_boxed_3562_ = lean_unbox(v_applicationTime_3559_);
v_res_3563_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg(v_validate_3556_, v_a_3557_, v_ref_3558_, v_applicationTime_boxed_3562_, v_a_3560_, v_a_3561_);
return v_res_3563_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg(lean_object* v_attrDescrs_3577_, lean_object* v_validate_3578_, uint8_t v_applicationTime_3579_, lean_object* v_ref_3580_){
_start:
{
lean_object* v___f_3582_; lean_object* v___f_3583_; lean_object* v___f_3584_; lean_object* v___f_3585_; lean_object* v___f_3586_; lean_object* v___f_3587_; lean_object* v___x_3588_; lean_object* v___x_3589_; lean_object* v___x_3590_; lean_object* v___x_3591_; lean_object* v___x_3592_; 
v___f_3582_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__0));
v___f_3583_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__2));
v___f_3584_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__3));
v___f_3585_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__4));
v___f_3586_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__5));
v___f_3587_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__6));
v___x_3588_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__7));
v___x_3589_ = ((lean_object*)(l_Lean_registerEnumAttributes___redArg___closed__8));
lean_inc(v_ref_3580_);
v___x_3590_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_3590_, 0, v_ref_3580_);
lean_ctor_set(v___x_3590_, 1, v___f_3586_);
lean_ctor_set(v___x_3590_, 2, v___f_3587_);
lean_ctor_set(v___x_3590_, 3, v___f_3585_);
lean_ctor_set(v___x_3590_, 4, v___f_3584_);
lean_ctor_set(v___x_3590_, 5, v___f_3583_);
lean_ctor_set(v___x_3590_, 6, v___x_3588_);
lean_ctor_set(v___x_3590_, 7, v___x_3589_);
v___x_3591_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3591_, 0, v___x_3590_);
lean_ctor_set(v___x_3591_, 1, v___f_3582_);
v___x_3592_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_3591_);
if (lean_obj_tag(v___x_3592_) == 0)
{
lean_object* v_a_3593_; lean_object* v___x_3594_; lean_object* v___x_3595_; lean_object* v___x_3596_; 
v_a_3593_ = lean_ctor_get(v___x_3592_, 0);
lean_inc_n(v_a_3593_, 2);
lean_dec_ref_known(v___x_3592_, 1);
v___x_3594_ = lean_box(0);
v___x_3595_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg(v_validate_3578_, v_a_3593_, v_ref_3580_, v_applicationTime_3579_, v_attrDescrs_3577_, v___x_3594_);
lean_inc(v___x_3595_);
v___x_3596_ = l_List_forM___at___00Lean_registerEnumAttributes_spec__3(v___x_3595_);
if (lean_obj_tag(v___x_3596_) == 0)
{
lean_object* v___x_3598_; uint8_t v_isShared_3599_; uint8_t v_isSharedCheck_3604_; 
v_isSharedCheck_3604_ = !lean_is_exclusive(v___x_3596_);
if (v_isSharedCheck_3604_ == 0)
{
lean_object* v_unused_3605_; 
v_unused_3605_ = lean_ctor_get(v___x_3596_, 0);
lean_dec(v_unused_3605_);
v___x_3598_ = v___x_3596_;
v_isShared_3599_ = v_isSharedCheck_3604_;
goto v_resetjp_3597_;
}
else
{
lean_dec(v___x_3596_);
v___x_3598_ = lean_box(0);
v_isShared_3599_ = v_isSharedCheck_3604_;
goto v_resetjp_3597_;
}
v_resetjp_3597_:
{
lean_object* v___x_3600_; lean_object* v___x_3602_; 
v___x_3600_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3600_, 0, v___x_3595_);
lean_ctor_set(v___x_3600_, 1, v_a_3593_);
if (v_isShared_3599_ == 0)
{
lean_ctor_set(v___x_3598_, 0, v___x_3600_);
v___x_3602_ = v___x_3598_;
goto v_reusejp_3601_;
}
else
{
lean_object* v_reuseFailAlloc_3603_; 
v_reuseFailAlloc_3603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3603_, 0, v___x_3600_);
v___x_3602_ = v_reuseFailAlloc_3603_;
goto v_reusejp_3601_;
}
v_reusejp_3601_:
{
return v___x_3602_;
}
}
}
else
{
lean_object* v_a_3606_; lean_object* v___x_3608_; uint8_t v_isShared_3609_; uint8_t v_isSharedCheck_3613_; 
lean_dec(v___x_3595_);
lean_dec(v_a_3593_);
v_a_3606_ = lean_ctor_get(v___x_3596_, 0);
v_isSharedCheck_3613_ = !lean_is_exclusive(v___x_3596_);
if (v_isSharedCheck_3613_ == 0)
{
v___x_3608_ = v___x_3596_;
v_isShared_3609_ = v_isSharedCheck_3613_;
goto v_resetjp_3607_;
}
else
{
lean_inc(v_a_3606_);
lean_dec(v___x_3596_);
v___x_3608_ = lean_box(0);
v_isShared_3609_ = v_isSharedCheck_3613_;
goto v_resetjp_3607_;
}
v_resetjp_3607_:
{
lean_object* v___x_3611_; 
if (v_isShared_3609_ == 0)
{
v___x_3611_ = v___x_3608_;
goto v_reusejp_3610_;
}
else
{
lean_object* v_reuseFailAlloc_3612_; 
v_reuseFailAlloc_3612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3612_, 0, v_a_3606_);
v___x_3611_ = v_reuseFailAlloc_3612_;
goto v_reusejp_3610_;
}
v_reusejp_3610_:
{
return v___x_3611_;
}
}
}
}
else
{
lean_object* v_a_3614_; lean_object* v___x_3616_; uint8_t v_isShared_3617_; uint8_t v_isSharedCheck_3621_; 
lean_dec(v_ref_3580_);
lean_dec_ref(v_validate_3578_);
lean_dec(v_attrDescrs_3577_);
v_a_3614_ = lean_ctor_get(v___x_3592_, 0);
v_isSharedCheck_3621_ = !lean_is_exclusive(v___x_3592_);
if (v_isSharedCheck_3621_ == 0)
{
v___x_3616_ = v___x_3592_;
v_isShared_3617_ = v_isSharedCheck_3621_;
goto v_resetjp_3615_;
}
else
{
lean_inc(v_a_3614_);
lean_dec(v___x_3592_);
v___x_3616_ = lean_box(0);
v_isShared_3617_ = v_isSharedCheck_3621_;
goto v_resetjp_3615_;
}
v_resetjp_3615_:
{
lean_object* v___x_3619_; 
if (v_isShared_3617_ == 0)
{
v___x_3619_ = v___x_3616_;
goto v_reusejp_3618_;
}
else
{
lean_object* v_reuseFailAlloc_3620_; 
v_reuseFailAlloc_3620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3620_, 0, v_a_3614_);
v___x_3619_ = v_reuseFailAlloc_3620_;
goto v_reusejp_3618_;
}
v_reusejp_3618_:
{
return v___x_3619_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___redArg___boxed(lean_object* v_attrDescrs_3622_, lean_object* v_validate_3623_, lean_object* v_applicationTime_3624_, lean_object* v_ref_3625_, lean_object* v_a_3626_){
_start:
{
uint8_t v_applicationTime_boxed_3627_; lean_object* v_res_3628_; 
v_applicationTime_boxed_3627_ = lean_unbox(v_applicationTime_3624_);
v_res_3628_ = l_Lean_registerEnumAttributes___redArg(v_attrDescrs_3622_, v_validate_3623_, v_applicationTime_boxed_3627_, v_ref_3625_);
return v_res_3628_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes(lean_object* v_00_u03b1_3629_, lean_object* v_attrDescrs_3630_, lean_object* v_validate_3631_, uint8_t v_applicationTime_3632_, lean_object* v_ref_3633_){
_start:
{
lean_object* v___x_3635_; 
v___x_3635_ = l_Lean_registerEnumAttributes___redArg(v_attrDescrs_3630_, v_validate_3631_, v_applicationTime_3632_, v_ref_3633_);
return v___x_3635_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerEnumAttributes___boxed(lean_object* v_00_u03b1_3636_, lean_object* v_attrDescrs_3637_, lean_object* v_validate_3638_, lean_object* v_applicationTime_3639_, lean_object* v_ref_3640_, lean_object* v_a_3641_){
_start:
{
uint8_t v_applicationTime_boxed_3642_; lean_object* v_res_3643_; 
v_applicationTime_boxed_3642_ = lean_unbox(v_applicationTime_3639_);
v_res_3643_ = l_Lean_registerEnumAttributes(v_00_u03b1_3636_, v_attrDescrs_3637_, v_validate_3638_, v_applicationTime_boxed_3642_, v_ref_3640_);
return v_res_3643_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0(lean_object* v_00_u03b1_3644_, lean_object* v_env_3645_, lean_object* v_as_3646_, size_t v_i_3647_, size_t v_stop_3648_, lean_object* v_b_3649_){
_start:
{
lean_object* v___x_3650_; 
v___x_3650_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___redArg(v_env_3645_, v_as_3646_, v_i_3647_, v_stop_3648_, v_b_3649_);
return v___x_3650_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0___boxed(lean_object* v_00_u03b1_3651_, lean_object* v_env_3652_, lean_object* v_as_3653_, lean_object* v_i_3654_, lean_object* v_stop_3655_, lean_object* v_b_3656_){
_start:
{
size_t v_i_boxed_3657_; size_t v_stop_boxed_3658_; lean_object* v_res_3659_; 
v_i_boxed_3657_ = lean_unbox_usize(v_i_3654_);
lean_dec(v_i_3654_);
v_stop_boxed_3658_ = lean_unbox_usize(v_stop_3655_);
lean_dec(v_stop_3655_);
v_res_3659_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_registerEnumAttributes_spec__0(v_00_u03b1_3651_, v_env_3652_, v_as_3653_, v_i_boxed_3657_, v_stop_boxed_3658_, v_b_3656_);
lean_dec_ref(v_as_3653_);
return v_res_3659_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerEnumAttributes_spec__1(lean_object* v_00_u03b1_3660_, lean_object* v_newState_3661_, lean_object* v_x_3662_, lean_object* v_x_3663_){
_start:
{
lean_object* v___x_3664_; 
v___x_3664_ = l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___redArg(v_newState_3661_, v_x_3662_, v_x_3663_);
return v___x_3664_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_registerEnumAttributes_spec__1___boxed(lean_object* v_00_u03b1_3665_, lean_object* v_newState_3666_, lean_object* v_x_3667_, lean_object* v_x_3668_){
_start:
{
lean_object* v_res_3669_; 
v_res_3669_ = l_List_foldl___at___00Lean_registerEnumAttributes_spec__1(v_00_u03b1_3665_, v_newState_3666_, v_x_3667_, v_x_3668_);
lean_dec(v_newState_3666_);
return v_res_3669_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2(lean_object* v_00_u03b1_3670_, lean_object* v_validate_3671_, lean_object* v_a_3672_, lean_object* v_ref_3673_, uint8_t v_applicationTime_3674_, lean_object* v_a_3675_, lean_object* v_a_3676_){
_start:
{
lean_object* v___x_3677_; 
v___x_3677_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___redArg(v_validate_3671_, v_a_3672_, v_ref_3673_, v_applicationTime_3674_, v_a_3675_, v_a_3676_);
return v___x_3677_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2___boxed(lean_object* v_00_u03b1_3678_, lean_object* v_validate_3679_, lean_object* v_a_3680_, lean_object* v_ref_3681_, lean_object* v_applicationTime_3682_, lean_object* v_a_3683_, lean_object* v_a_3684_){
_start:
{
uint8_t v_applicationTime_boxed_3685_; lean_object* v_res_3686_; 
v_applicationTime_boxed_3685_ = lean_unbox(v_applicationTime_3682_);
v_res_3686_ = l_List_mapTR_loop___at___00Lean_registerEnumAttributes_spec__2(v_00_u03b1_3678_, v_validate_3679_, v_a_3680_, v_ref_3681_, v_applicationTime_boxed_3685_, v_a_3683_, v_a_3684_);
return v_res_3686_;
}
}
LEAN_EXPORT lean_object* l_Lean_EnumAttributes_getValue___redArg(lean_object* v_inst_3687_, lean_object* v_attr_3688_, lean_object* v_env_3689_, lean_object* v_decl_3690_){
_start:
{
lean_object* v___x_3691_; lean_object* v___x_3692_; 
v___x_3691_ = lean_box(1);
v___x_3692_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3689_, v_decl_3690_);
if (lean_obj_tag(v___x_3692_) == 0)
{
lean_object* v_ext_3693_; lean_object* v_toEnvExtension_3694_; lean_object* v_asyncMode_3695_; lean_object* v___x_3696_; lean_object* v___x_3697_; 
lean_dec(v_inst_3687_);
v_ext_3693_ = lean_ctor_get(v_attr_3688_, 1);
lean_inc_ref(v_ext_3693_);
lean_dec_ref(v_attr_3688_);
v_toEnvExtension_3694_ = lean_ctor_get(v_ext_3693_, 0);
v_asyncMode_3695_ = lean_ctor_get(v_toEnvExtension_3694_, 2);
lean_inc(v_asyncMode_3695_);
lean_inc(v_decl_3690_);
v___x_3696_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3691_, v_ext_3693_, v_env_3689_, v_asyncMode_3695_, v_decl_3690_);
lean_dec(v_asyncMode_3695_);
lean_dec_ref(v_ext_3693_);
v___x_3697_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_3696_, v_decl_3690_);
lean_dec(v_decl_3690_);
lean_dec(v___x_3696_);
return v___x_3697_;
}
else
{
lean_object* v_val_3698_; lean_object* v_ext_3699_; lean_object* v___x_3701_; uint8_t v_isShared_3702_; uint8_t v_isSharedCheck_3729_; 
v_val_3698_ = lean_ctor_get(v___x_3692_, 0);
lean_inc(v_val_3698_);
lean_dec_ref_known(v___x_3692_, 1);
v_ext_3699_ = lean_ctor_get(v_attr_3688_, 1);
v_isSharedCheck_3729_ = !lean_is_exclusive(v_attr_3688_);
if (v_isSharedCheck_3729_ == 0)
{
lean_object* v_unused_3730_; 
v_unused_3730_ = lean_ctor_get(v_attr_3688_, 0);
lean_dec(v_unused_3730_);
v___x_3701_ = v_attr_3688_;
v_isShared_3702_ = v_isSharedCheck_3729_;
goto v_resetjp_3700_;
}
else
{
lean_inc(v_ext_3699_);
lean_dec(v_attr_3688_);
v___x_3701_ = lean_box(0);
v_isShared_3702_ = v_isSharedCheck_3729_;
goto v_resetjp_3700_;
}
v_resetjp_3700_:
{
uint8_t v___x_3703_; lean_object* v___x_3704_; lean_object* v___x_3705_; lean_object* v___x_3706_; uint8_t v___x_3707_; 
v___x_3703_ = 0;
v___x_3704_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(v___x_3691_, v_ext_3699_, v_env_3689_, v_val_3698_, v___x_3703_);
lean_dec(v_val_3698_);
lean_dec_ref(v_env_3689_);
lean_dec_ref(v_ext_3699_);
v___x_3705_ = lean_unsigned_to_nat(0u);
v___x_3706_ = lean_array_get_size(v___x_3704_);
v___x_3707_ = lean_nat_dec_lt(v___x_3705_, v___x_3706_);
if (v___x_3707_ == 0)
{
lean_object* v___x_3708_; 
lean_dec_ref(v___x_3704_);
lean_del_object(v___x_3701_);
lean_dec(v_decl_3690_);
lean_dec(v_inst_3687_);
v___x_3708_ = lean_box(0);
return v___x_3708_;
}
else
{
lean_object* v___x_3709_; lean_object* v___x_3710_; uint8_t v___x_3711_; 
v___x_3709_ = lean_unsigned_to_nat(1u);
v___x_3710_ = lean_nat_sub(v___x_3706_, v___x_3709_);
v___x_3711_ = lean_nat_dec_le(v___x_3705_, v___x_3710_);
if (v___x_3711_ == 0)
{
lean_object* v___x_3712_; 
lean_dec(v___x_3710_);
lean_dec_ref(v___x_3704_);
lean_del_object(v___x_3701_);
lean_dec(v_decl_3690_);
lean_dec(v_inst_3687_);
v___x_3712_ = lean_box(0);
return v___x_3712_;
}
else
{
lean_object* v___f_3713_; lean_object* v___x_3715_; 
v___f_3713_ = ((lean_object*)(l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__1));
if (v_isShared_3702_ == 0)
{
lean_ctor_set(v___x_3701_, 1, v_inst_3687_);
lean_ctor_set(v___x_3701_, 0, v_decl_3690_);
v___x_3715_ = v___x_3701_;
goto v_reusejp_3714_;
}
else
{
lean_object* v_reuseFailAlloc_3728_; 
v_reuseFailAlloc_3728_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3728_, 0, v_decl_3690_);
lean_ctor_set(v_reuseFailAlloc_3728_, 1, v_inst_3687_);
v___x_3715_ = v_reuseFailAlloc_3728_;
goto v_reusejp_3714_;
}
v_reusejp_3714_:
{
lean_object* v___x_3716_; lean_object* v___x_3717_; 
v___x_3716_ = ((lean_object*)(l_Lean_ParametricAttribute_getParamFromExt_x3f___redArg___closed__2));
v___x_3717_ = l_Array_binSearchAux___redArg(v___f_3713_, v___x_3716_, v___x_3704_, v___x_3715_, v___x_3705_, v___x_3710_);
lean_dec_ref(v___x_3704_);
if (lean_obj_tag(v___x_3717_) == 0)
{
lean_object* v___x_3718_; 
v___x_3718_ = lean_box(0);
return v___x_3718_;
}
else
{
lean_object* v_val_3719_; lean_object* v___x_3721_; uint8_t v_isShared_3722_; uint8_t v_isSharedCheck_3727_; 
v_val_3719_ = lean_ctor_get(v___x_3717_, 0);
v_isSharedCheck_3727_ = !lean_is_exclusive(v___x_3717_);
if (v_isSharedCheck_3727_ == 0)
{
v___x_3721_ = v___x_3717_;
v_isShared_3722_ = v_isSharedCheck_3727_;
goto v_resetjp_3720_;
}
else
{
lean_inc(v_val_3719_);
lean_dec(v___x_3717_);
v___x_3721_ = lean_box(0);
v_isShared_3722_ = v_isSharedCheck_3727_;
goto v_resetjp_3720_;
}
v_resetjp_3720_:
{
lean_object* v_snd_3723_; lean_object* v___x_3725_; 
v_snd_3723_ = lean_ctor_get(v_val_3719_, 1);
lean_inc(v_snd_3723_);
lean_dec(v_val_3719_);
if (v_isShared_3722_ == 0)
{
lean_ctor_set(v___x_3721_, 0, v_snd_3723_);
v___x_3725_ = v___x_3721_;
goto v_reusejp_3724_;
}
else
{
lean_object* v_reuseFailAlloc_3726_; 
v_reuseFailAlloc_3726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3726_, 0, v_snd_3723_);
v___x_3725_ = v_reuseFailAlloc_3726_;
goto v_reusejp_3724_;
}
v_reusejp_3724_:
{
return v___x_3725_;
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
LEAN_EXPORT lean_object* l_Lean_EnumAttributes_getValue(lean_object* v_00_u03b1_3731_, lean_object* v_inst_3732_, lean_object* v_attr_3733_, lean_object* v_env_3734_, lean_object* v_decl_3735_){
_start:
{
lean_object* v___x_3736_; 
v___x_3736_ = l_Lean_EnumAttributes_getValue___redArg(v_inst_3732_, v_attr_3733_, v_env_3734_, v_decl_3735_);
return v___x_3736_;
}
}
LEAN_EXPORT lean_object* l_Lean_EnumAttributes_setValue___redArg(lean_object* v_attrs_3745_, lean_object* v_env_3746_, lean_object* v_decl_3747_, lean_object* v_val_3748_){
_start:
{
lean_object* v_ext_3749_; lean_object* v___x_3751_; uint8_t v_isShared_3752_; uint8_t v_isSharedCheck_3812_; 
v_ext_3749_ = lean_ctor_get(v_attrs_3745_, 1);
v_isSharedCheck_3812_ = !lean_is_exclusive(v_attrs_3745_);
if (v_isSharedCheck_3812_ == 0)
{
lean_object* v_unused_3813_; 
v_unused_3813_ = lean_ctor_get(v_attrs_3745_, 0);
lean_dec(v_unused_3813_);
v___x_3751_ = v_attrs_3745_;
v_isShared_3752_ = v_isSharedCheck_3812_;
goto v_resetjp_3750_;
}
else
{
lean_inc(v_ext_3749_);
lean_dec(v_attrs_3745_);
v___x_3751_ = lean_box(0);
v_isShared_3752_ = v_isSharedCheck_3812_;
goto v_resetjp_3750_;
}
v_resetjp_3750_:
{
lean_object* v_toEnvExtension_3753_; lean_object* v_name_3754_; lean_object* v___x_3755_; uint8_t v___x_3756_; lean_object* v___x_3757_; lean_object* v___x_3758_; lean_object* v___x_3759_; lean_object* v___x_3760_; lean_object* v___x_3761_; lean_object* v___x_3762_; lean_object* v___x_3763_; lean_object* v_pfx_3764_; lean_object* v___x_3765_; 
v_toEnvExtension_3753_ = lean_ctor_get(v_ext_3749_, 0);
v_name_3754_ = lean_ctor_get(v_ext_3749_, 1);
v___x_3755_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__0));
v___x_3756_ = 1;
lean_inc(v_name_3754_);
v___x_3757_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_3754_, v___x_3756_);
v___x_3758_ = lean_string_append(v___x_3755_, v___x_3757_);
lean_dec_ref(v___x_3757_);
v___x_3759_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__1));
v___x_3760_ = lean_string_append(v___x_3758_, v___x_3759_);
lean_inc(v_decl_3747_);
v___x_3761_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_decl_3747_, v___x_3756_);
v___x_3762_ = lean_string_append(v___x_3760_, v___x_3761_);
lean_dec_ref(v___x_3761_);
v___x_3763_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__4));
v_pfx_3764_ = lean_string_append(v___x_3762_, v___x_3763_);
v___x_3765_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3746_, v_decl_3747_);
if (lean_obj_tag(v___x_3765_) == 0)
{
lean_object* v_asyncMode_3766_; uint8_t v___x_3767_; 
v_asyncMode_3766_ = lean_ctor_get(v_toEnvExtension_3753_, 2);
lean_inc(v_asyncMode_3766_);
lean_inc(v_decl_3747_);
lean_inc_ref(v_env_3746_);
v___x_3767_ = l_Lean_EnvExtension_asyncMayModify___redArg(v_env_3746_, v_decl_3747_, v_asyncMode_3766_);
if (v___x_3767_ == 0)
{
lean_object* v___x_3768_; lean_object* v___x_3769_; lean_object* v___y_3771_; lean_object* v___x_3775_; 
lean_dec(v_asyncMode_3766_);
lean_del_object(v___x_3751_);
lean_dec_ref(v_ext_3749_);
lean_dec(v_val_3748_);
lean_dec(v_decl_3747_);
v___x_3768_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__2));
v___x_3769_ = lean_string_append(v_pfx_3764_, v___x_3768_);
v___x_3775_ = l_Lean_Environment_asyncPrefix_x3f(v_env_3746_);
if (lean_obj_tag(v___x_3775_) == 0)
{
lean_object* v___x_3776_; 
v___x_3776_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__3));
v___y_3771_ = v___x_3776_;
goto v___jp_3770_;
}
else
{
lean_object* v_val_3777_; lean_object* v___x_3778_; lean_object* v___x_3779_; lean_object* v___x_3780_; lean_object* v___x_3781_; lean_object* v___x_3782_; lean_object* v___x_3783_; 
v_val_3777_ = lean_ctor_get(v___x_3775_, 0);
lean_inc(v_val_3777_);
lean_dec_ref_known(v___x_3775_, 1);
v___x_3778_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__4));
v___x_3779_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_val_3777_, v___x_3756_);
v___x_3780_ = l_addParenHeuristic(v___x_3779_);
v___x_3781_ = lean_string_append(v___x_3778_, v___x_3780_);
lean_dec_ref(v___x_3780_);
v___x_3782_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__5));
v___x_3783_ = lean_string_append(v___x_3781_, v___x_3782_);
v___y_3771_ = v___x_3783_;
goto v___jp_3770_;
}
v___jp_3770_:
{
lean_object* v___x_3772_; lean_object* v___x_3773_; lean_object* v___x_3774_; 
v___x_3772_ = lean_string_append(v___x_3769_, v___y_3771_);
lean_dec_ref(v___y_3771_);
v___x_3773_ = lean_string_append(v___x_3772_, v___x_3763_);
v___x_3774_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3774_, 0, v___x_3773_);
return v___x_3774_;
}
}
else
{
lean_object* v___x_3784_; lean_object* v___x_3785_; lean_object* v___x_3786_; 
v___x_3784_ = lean_box(1);
lean_inc(v_decl_3747_);
lean_inc_ref(v_env_3746_);
v___x_3785_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_3784_, v_ext_3749_, v_env_3746_, v_asyncMode_3766_, v_decl_3747_);
v___x_3786_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_3785_, v_decl_3747_);
lean_dec(v___x_3785_);
if (lean_obj_tag(v___x_3786_) == 0)
{
lean_object* v___x_3788_; 
lean_dec_ref(v_pfx_3764_);
lean_inc(v_decl_3747_);
if (v_isShared_3752_ == 0)
{
lean_ctor_set(v___x_3751_, 1, v_val_3748_);
lean_ctor_set(v___x_3751_, 0, v_decl_3747_);
v___x_3788_ = v___x_3751_;
goto v_reusejp_3787_;
}
else
{
lean_object* v_reuseFailAlloc_3791_; 
v_reuseFailAlloc_3791_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3791_, 0, v_decl_3747_);
lean_ctor_set(v_reuseFailAlloc_3791_, 1, v_val_3748_);
v___x_3788_ = v_reuseFailAlloc_3791_;
goto v_reusejp_3787_;
}
v_reusejp_3787_:
{
lean_object* v___x_3789_; lean_object* v___x_3790_; 
v___x_3789_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v_ext_3749_, v_env_3746_, v___x_3788_, v_asyncMode_3766_, v_decl_3747_);
lean_dec(v_asyncMode_3766_);
v___x_3790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3790_, 0, v___x_3789_);
return v___x_3790_;
}
}
else
{
lean_object* v___x_3793_; uint8_t v_isShared_3794_; uint8_t v_isSharedCheck_3800_; 
lean_dec(v_asyncMode_3766_);
lean_del_object(v___x_3751_);
lean_dec_ref(v_ext_3749_);
lean_dec(v_val_3748_);
lean_dec(v_decl_3747_);
lean_dec_ref(v_env_3746_);
v_isSharedCheck_3800_ = !lean_is_exclusive(v___x_3786_);
if (v_isSharedCheck_3800_ == 0)
{
lean_object* v_unused_3801_; 
v_unused_3801_ = lean_ctor_get(v___x_3786_, 0);
lean_dec(v_unused_3801_);
v___x_3793_ = v___x_3786_;
v_isShared_3794_ = v_isSharedCheck_3800_;
goto v_resetjp_3792_;
}
else
{
lean_dec(v___x_3786_);
v___x_3793_ = lean_box(0);
v_isShared_3794_ = v_isSharedCheck_3800_;
goto v_resetjp_3792_;
}
v_resetjp_3792_:
{
lean_object* v___x_3795_; lean_object* v___x_3796_; lean_object* v___x_3798_; 
v___x_3795_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__6));
v___x_3796_ = lean_string_append(v_pfx_3764_, v___x_3795_);
if (v_isShared_3794_ == 0)
{
lean_ctor_set_tag(v___x_3793_, 0);
lean_ctor_set(v___x_3793_, 0, v___x_3796_);
v___x_3798_ = v___x_3793_;
goto v_reusejp_3797_;
}
else
{
lean_object* v_reuseFailAlloc_3799_; 
v_reuseFailAlloc_3799_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3799_, 0, v___x_3796_);
v___x_3798_ = v_reuseFailAlloc_3799_;
goto v_reusejp_3797_;
}
v_reusejp_3797_:
{
return v___x_3798_;
}
}
}
}
}
else
{
lean_object* v___x_3803_; uint8_t v_isShared_3804_; uint8_t v_isSharedCheck_3810_; 
lean_del_object(v___x_3751_);
lean_dec_ref(v_ext_3749_);
lean_dec(v_val_3748_);
lean_dec(v_decl_3747_);
lean_dec_ref(v_env_3746_);
v_isSharedCheck_3810_ = !lean_is_exclusive(v___x_3765_);
if (v_isSharedCheck_3810_ == 0)
{
lean_object* v_unused_3811_; 
v_unused_3811_ = lean_ctor_get(v___x_3765_, 0);
lean_dec(v_unused_3811_);
v___x_3803_ = v___x_3765_;
v_isShared_3804_ = v_isSharedCheck_3810_;
goto v_resetjp_3802_;
}
else
{
lean_dec(v___x_3765_);
v___x_3803_ = lean_box(0);
v_isShared_3804_ = v_isSharedCheck_3810_;
goto v_resetjp_3802_;
}
v_resetjp_3802_:
{
lean_object* v___x_3805_; lean_object* v___x_3806_; lean_object* v___x_3808_; 
v___x_3805_ = ((lean_object*)(l_Lean_EnumAttributes_setValue___redArg___closed__7));
v___x_3806_ = lean_string_append(v_pfx_3764_, v___x_3805_);
if (v_isShared_3804_ == 0)
{
lean_ctor_set_tag(v___x_3803_, 0);
lean_ctor_set(v___x_3803_, 0, v___x_3806_);
v___x_3808_ = v___x_3803_;
goto v_reusejp_3807_;
}
else
{
lean_object* v_reuseFailAlloc_3809_; 
v_reuseFailAlloc_3809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3809_, 0, v___x_3806_);
v___x_3808_ = v_reuseFailAlloc_3809_;
goto v_reusejp_3807_;
}
v_reusejp_3807_:
{
return v___x_3808_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_EnumAttributes_setValue(lean_object* v_00_u03b1_3814_, lean_object* v_attrs_3815_, lean_object* v_env_3816_, lean_object* v_decl_3817_, lean_object* v_val_3818_){
_start:
{
lean_object* v___x_3819_; 
v___x_3819_ = l_Lean_EnumAttributes_setValue___redArg(v_attrs_3815_, v_env_3816_, v_decl_3817_, v_val_3818_);
return v___x_3819_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_2990505691____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3821_; lean_object* v___x_3822_; lean_object* v___x_3823_; 
v___x_3821_ = lean_obj_once(&l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_, &l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2__once, _init_l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_);
v___x_3822_ = lean_st_mk_ref(v___x_3821_);
v___x_3823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3823_, 0, v___x_3822_);
return v___x_3823_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_2990505691____hygCtx___hyg_2____boxed(lean_object* v_a_3824_){
_start:
{
lean_object* v_res_3825_; 
v_res_3825_ = l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_2990505691____hygCtx___hyg_2_();
return v_res_3825_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerAttributeImplBuilder(lean_object* v_builderId_3828_, lean_object* v_builder_3829_){
_start:
{
lean_object* v___x_3831_; lean_object* v___x_3832_; uint8_t v___x_3833_; 
v___x_3831_ = l_Lean_attributeImplBuilderTableRef;
v___x_3832_ = lean_st_ref_get(v___x_3831_);
v___x_3833_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(v___x_3832_, v_builderId_3828_);
lean_dec(v___x_3832_);
if (v___x_3833_ == 0)
{
lean_object* v___x_3834_; lean_object* v___x_3835_; lean_object* v___x_3836_; lean_object* v___x_3837_; 
v___x_3834_ = lean_st_ref_take(v___x_3831_);
v___x_3835_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1___redArg(v___x_3834_, v_builderId_3828_, v_builder_3829_);
v___x_3836_ = lean_st_ref_put(v___x_3831_, v___x_3835_);
v___x_3837_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3837_, 0, v___x_3836_);
return v___x_3837_;
}
else
{
lean_object* v___x_3838_; lean_object* v___x_3839_; lean_object* v___x_3840_; lean_object* v___x_3841_; lean_object* v___x_3842_; lean_object* v___x_3843_; lean_object* v___x_3844_; 
lean_dec_ref(v_builder_3829_);
v___x_3838_ = ((lean_object*)(l_Lean_registerAttributeImplBuilder___closed__0));
v___x_3839_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_builderId_3828_, v___x_3833_);
v___x_3840_ = lean_string_append(v___x_3838_, v___x_3839_);
lean_dec_ref(v___x_3839_);
v___x_3841_ = ((lean_object*)(l_Lean_registerAttributeImplBuilder___closed__1));
v___x_3842_ = lean_string_append(v___x_3840_, v___x_3841_);
v___x_3843_ = lean_mk_io_user_error(v___x_3842_);
v___x_3844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3844_, 0, v___x_3843_);
return v___x_3844_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerAttributeImplBuilder___boxed(lean_object* v_builderId_3845_, lean_object* v_builder_3846_, lean_object* v_a_3847_){
_start:
{
lean_object* v_res_3848_; 
v_res_3848_ = l_Lean_registerAttributeImplBuilder(v_builderId_3845_, v_builder_3846_);
return v_res_3848_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___redArg(lean_object* v_e_3849_){
_start:
{
if (lean_obj_tag(v_e_3849_) == 0)
{
lean_object* v_a_3851_; lean_object* v___x_3853_; uint8_t v_isShared_3854_; uint8_t v_isSharedCheck_3859_; 
v_a_3851_ = lean_ctor_get(v_e_3849_, 0);
v_isSharedCheck_3859_ = !lean_is_exclusive(v_e_3849_);
if (v_isSharedCheck_3859_ == 0)
{
v___x_3853_ = v_e_3849_;
v_isShared_3854_ = v_isSharedCheck_3859_;
goto v_resetjp_3852_;
}
else
{
lean_inc(v_a_3851_);
lean_dec(v_e_3849_);
v___x_3853_ = lean_box(0);
v_isShared_3854_ = v_isSharedCheck_3859_;
goto v_resetjp_3852_;
}
v_resetjp_3852_:
{
lean_object* v___x_3855_; lean_object* v___x_3857_; 
v___x_3855_ = lean_mk_io_user_error(v_a_3851_);
if (v_isShared_3854_ == 0)
{
lean_ctor_set_tag(v___x_3853_, 1);
lean_ctor_set(v___x_3853_, 0, v___x_3855_);
v___x_3857_ = v___x_3853_;
goto v_reusejp_3856_;
}
else
{
lean_object* v_reuseFailAlloc_3858_; 
v_reuseFailAlloc_3858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3858_, 0, v___x_3855_);
v___x_3857_ = v_reuseFailAlloc_3858_;
goto v_reusejp_3856_;
}
v_reusejp_3856_:
{
return v___x_3857_;
}
}
}
else
{
lean_object* v_a_3860_; lean_object* v___x_3862_; uint8_t v_isShared_3863_; uint8_t v_isSharedCheck_3867_; 
v_a_3860_ = lean_ctor_get(v_e_3849_, 0);
v_isSharedCheck_3867_ = !lean_is_exclusive(v_e_3849_);
if (v_isSharedCheck_3867_ == 0)
{
v___x_3862_ = v_e_3849_;
v_isShared_3863_ = v_isSharedCheck_3867_;
goto v_resetjp_3861_;
}
else
{
lean_inc(v_a_3860_);
lean_dec(v_e_3849_);
v___x_3862_ = lean_box(0);
v_isShared_3863_ = v_isSharedCheck_3867_;
goto v_resetjp_3861_;
}
v_resetjp_3861_:
{
lean_object* v___x_3865_; 
if (v_isShared_3863_ == 0)
{
lean_ctor_set_tag(v___x_3862_, 0);
v___x_3865_ = v___x_3862_;
goto v_reusejp_3864_;
}
else
{
lean_object* v_reuseFailAlloc_3866_; 
v_reuseFailAlloc_3866_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3866_, 0, v_a_3860_);
v___x_3865_ = v_reuseFailAlloc_3866_;
goto v_reusejp_3864_;
}
v_reusejp_3864_:
{
return v___x_3865_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___redArg___boxed(lean_object* v_e_3868_, lean_object* v_a_3869_){
_start:
{
lean_object* v_res_3870_; 
v_res_3870_ = l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___redArg(v_e_3868_);
return v_res_3870_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1(lean_object* v_00_u03b1_3871_, lean_object* v_e_3872_){
_start:
{
lean_object* v___x_3874_; 
v___x_3874_ = l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___redArg(v_e_3872_);
return v___x_3874_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___boxed(lean_object* v_00_u03b1_3875_, lean_object* v_e_3876_, lean_object* v_a_3877_){
_start:
{
lean_object* v_res_3878_; 
v_res_3878_ = l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1(v_00_u03b1_3875_, v_e_3876_);
return v_res_3878_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___redArg(lean_object* v_a_3879_, lean_object* v_x_3880_){
_start:
{
if (lean_obj_tag(v_x_3880_) == 0)
{
lean_object* v___x_3881_; 
v___x_3881_ = lean_box(0);
return v___x_3881_;
}
else
{
lean_object* v_key_3882_; lean_object* v_value_3883_; lean_object* v_tail_3884_; uint8_t v___x_3885_; 
v_key_3882_ = lean_ctor_get(v_x_3880_, 0);
v_value_3883_ = lean_ctor_get(v_x_3880_, 1);
v_tail_3884_ = lean_ctor_get(v_x_3880_, 2);
v___x_3885_ = lean_name_eq(v_key_3882_, v_a_3879_);
if (v___x_3885_ == 0)
{
v_x_3880_ = v_tail_3884_;
goto _start;
}
else
{
lean_object* v___x_3887_; 
lean_inc(v_value_3883_);
v___x_3887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3887_, 0, v_value_3883_);
return v___x_3887_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___redArg___boxed(lean_object* v_a_3888_, lean_object* v_x_3889_){
_start:
{
lean_object* v_res_3890_; 
v_res_3890_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___redArg(v_a_3888_, v_x_3889_);
lean_dec(v_x_3889_);
lean_dec(v_a_3888_);
return v_res_3890_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(lean_object* v_m_3891_, lean_object* v_a_3892_){
_start:
{
lean_object* v_buckets_3893_; lean_object* v___x_3894_; uint64_t v___y_3896_; 
v_buckets_3893_ = lean_ctor_get(v_m_3891_, 1);
v___x_3894_ = lean_array_get_size(v_buckets_3893_);
if (lean_obj_tag(v_a_3892_) == 0)
{
uint64_t v___x_3910_; 
v___x_3910_ = 1723ULL;
v___y_3896_ = v___x_3910_;
goto v___jp_3895_;
}
else
{
uint64_t v_hash_3911_; 
v_hash_3911_ = lean_ctor_get_uint64(v_a_3892_, sizeof(void*)*2);
v___y_3896_ = v_hash_3911_;
goto v___jp_3895_;
}
v___jp_3895_:
{
uint64_t v___x_3897_; uint64_t v___x_3898_; uint64_t v_fold_3899_; uint64_t v___x_3900_; uint64_t v___x_3901_; uint64_t v___x_3902_; size_t v___x_3903_; size_t v___x_3904_; size_t v___x_3905_; size_t v___x_3906_; size_t v___x_3907_; lean_object* v___x_3908_; lean_object* v___x_3909_; 
v___x_3897_ = 32ULL;
v___x_3898_ = lean_uint64_shift_right(v___y_3896_, v___x_3897_);
v_fold_3899_ = lean_uint64_xor(v___y_3896_, v___x_3898_);
v___x_3900_ = 16ULL;
v___x_3901_ = lean_uint64_shift_right(v_fold_3899_, v___x_3900_);
v___x_3902_ = lean_uint64_xor(v_fold_3899_, v___x_3901_);
v___x_3903_ = lean_uint64_to_usize(v___x_3902_);
v___x_3904_ = lean_usize_of_nat(v___x_3894_);
v___x_3905_ = ((size_t)1ULL);
v___x_3906_ = lean_usize_sub(v___x_3904_, v___x_3905_);
v___x_3907_ = lean_usize_land(v___x_3903_, v___x_3906_);
v___x_3908_ = lean_array_uget_borrowed(v_buckets_3893_, v___x_3907_);
v___x_3909_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___redArg(v_a_3892_, v___x_3908_);
return v___x_3909_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg___boxed(lean_object* v_m_3912_, lean_object* v_a_3913_){
_start:
{
lean_object* v_res_3914_; 
v_res_3914_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(v_m_3912_, v_a_3913_);
lean_dec(v_a_3913_);
lean_dec_ref(v_m_3912_);
return v_res_3914_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAttributeImplOfEntry(lean_object* v_e_3916_){
_start:
{
lean_object* v___x_3918_; lean_object* v___x_3919_; lean_object* v_builderId_3920_; lean_object* v_ref_3921_; lean_object* v_args_3922_; lean_object* v___x_3923_; 
v___x_3918_ = l_Lean_attributeImplBuilderTableRef;
v___x_3919_ = lean_st_ref_get(v___x_3918_);
v_builderId_3920_ = lean_ctor_get(v_e_3916_, 0);
lean_inc(v_builderId_3920_);
v_ref_3921_ = lean_ctor_get(v_e_3916_, 1);
lean_inc(v_ref_3921_);
v_args_3922_ = lean_ctor_get(v_e_3916_, 2);
lean_inc(v_args_3922_);
lean_dec_ref(v_e_3916_);
v___x_3923_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(v___x_3919_, v_builderId_3920_);
lean_dec(v___x_3919_);
if (lean_obj_tag(v___x_3923_) == 0)
{
lean_object* v___x_3924_; uint8_t v___x_3925_; lean_object* v___x_3926_; lean_object* v___x_3927_; lean_object* v___x_3928_; lean_object* v___x_3929_; lean_object* v___x_3930_; lean_object* v___x_3931_; 
lean_dec(v_args_3922_);
lean_dec(v_ref_3921_);
v___x_3924_ = ((lean_object*)(l_Lean_mkAttributeImplOfEntry___closed__0));
v___x_3925_ = 1;
v___x_3926_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_builderId_3920_, v___x_3925_);
v___x_3927_ = lean_string_append(v___x_3924_, v___x_3926_);
lean_dec_ref(v___x_3926_);
v___x_3928_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__4));
v___x_3929_ = lean_string_append(v___x_3927_, v___x_3928_);
v___x_3930_ = lean_mk_io_user_error(v___x_3929_);
v___x_3931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3931_, 0, v___x_3930_);
return v___x_3931_;
}
else
{
lean_object* v_val_3932_; lean_object* v___x_3933_; lean_object* v___x_3934_; 
lean_dec(v_builderId_3920_);
v_val_3932_ = lean_ctor_get(v___x_3923_, 0);
lean_inc(v_val_3932_);
lean_dec_ref_known(v___x_3923_, 1);
v___x_3933_ = lean_apply_2(v_val_3932_, v_ref_3921_, v_args_3922_);
v___x_3934_ = l_IO_ofExcept___at___00Lean_mkAttributeImplOfEntry_spec__1___redArg(v___x_3933_);
return v___x_3934_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkAttributeImplOfEntry___boxed(lean_object* v_e_3935_, lean_object* v_a_3936_){
_start:
{
lean_object* v_res_3937_; 
v_res_3937_ = l_Lean_mkAttributeImplOfEntry(v_e_3935_);
return v_res_3937_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0(lean_object* v_00_u03b2_3938_, lean_object* v_m_3939_, lean_object* v_a_3940_){
_start:
{
lean_object* v___x_3941_; 
v___x_3941_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(v_m_3939_, v_a_3940_);
return v___x_3941_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___boxed(lean_object* v_00_u03b2_3942_, lean_object* v_m_3943_, lean_object* v_a_3944_){
_start:
{
lean_object* v_res_3945_; 
v_res_3945_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0(v_00_u03b2_3942_, v_m_3943_, v_a_3944_);
lean_dec(v_a_3944_);
lean_dec_ref(v_m_3943_);
return v_res_3945_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0(lean_object* v_00_u03b2_3946_, lean_object* v_a_3947_, lean_object* v_x_3948_){
_start:
{
lean_object* v___x_3949_; 
v___x_3949_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___redArg(v_a_3947_, v_x_3948_);
return v___x_3949_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3950_, lean_object* v_a_3951_, lean_object* v_x_3952_){
_start:
{
lean_object* v_res_3953_; 
v_res_3953_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0_spec__0(v_00_u03b2_3950_, v_a_3951_, v_x_3952_);
lean_dec(v_x_3952_);
lean_dec(v_a_3951_);
return v_res_3953_;
}
}
static lean_object* _init_l_Lean_instInhabitedAttributeExtensionState_default___closed__0(void){
_start:
{
lean_object* v___x_3954_; lean_object* v___x_3955_; lean_object* v___x_3956_; 
v___x_3954_ = lean_obj_once(&l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_, &l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2__once, _init_l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_285812513____hygCtx___hyg_2_);
v___x_3955_ = lean_box(0);
v___x_3956_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3956_, 0, v___x_3955_);
lean_ctor_set(v___x_3956_, 1, v___x_3954_);
return v___x_3956_;
}
}
static lean_object* _init_l_Lean_instInhabitedAttributeExtensionState_default(void){
_start:
{
lean_object* v___x_3957_; 
v___x_3957_ = lean_obj_once(&l_Lean_instInhabitedAttributeExtensionState_default___closed__0, &l_Lean_instInhabitedAttributeExtensionState_default___closed__0_once, _init_l_Lean_instInhabitedAttributeExtensionState_default___closed__0);
return v___x_3957_;
}
}
static lean_object* _init_l_Lean_instInhabitedAttributeExtensionState(void){
_start:
{
lean_object* v___x_3958_; 
v___x_3958_ = l_Lean_instInhabitedAttributeExtensionState_default;
return v___x_3958_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_AttributeExtension_mkInitial(){
_start:
{
lean_object* v___x_3960_; lean_object* v___x_3961_; lean_object* v___x_3962_; lean_object* v___x_3963_; lean_object* v___x_3964_; 
v___x_3960_ = l_Lean_attributeMapRef;
v___x_3961_ = lean_st_ref_get(v___x_3960_);
v___x_3962_ = lean_box(0);
v___x_3963_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3963_, 0, v___x_3962_);
lean_ctor_set(v___x_3963_, 1, v___x_3961_);
v___x_3964_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3964_, 0, v___x_3963_);
return v___x_3964_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_AttributeExtension_mkInitial___boxed(lean_object* v_a_3965_){
_start:
{
lean_object* v_res_3966_; 
v_res_3966_ = l___private_Lean_Attributes_0__Lean_AttributeExtension_mkInitial();
return v_res_3966_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAttributeImplOfConstantUnsafe(lean_object* v_env_3972_, lean_object* v_opts_3973_, lean_object* v_declName_3974_){
_start:
{
uint8_t v___x_3977_; lean_object* v___x_3978_; 
v___x_3977_ = 0;
lean_inc(v_declName_3974_);
lean_inc_ref(v_env_3972_);
v___x_3978_ = l_Lean_Environment_find_x3f(v_env_3972_, v_declName_3974_, v___x_3977_);
if (lean_obj_tag(v___x_3978_) == 0)
{
lean_object* v___x_3979_; uint8_t v___x_3980_; lean_object* v___x_3981_; lean_object* v___x_3982_; lean_object* v___x_3983_; lean_object* v___x_3984_; lean_object* v___x_3985_; 
lean_dec_ref(v_env_3972_);
v___x_3979_ = ((lean_object*)(l_Lean_mkAttributeImplOfConstantUnsafe___closed__2));
v___x_3980_ = 1;
v___x_3981_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_declName_3974_, v___x_3980_);
v___x_3982_ = lean_string_append(v___x_3979_, v___x_3981_);
lean_dec_ref(v___x_3981_);
v___x_3983_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__4));
v___x_3984_ = lean_string_append(v___x_3982_, v___x_3983_);
v___x_3985_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3985_, 0, v___x_3984_);
return v___x_3985_;
}
else
{
lean_object* v_val_3986_; lean_object* v___x_3987_; 
v_val_3986_ = lean_ctor_get(v___x_3978_, 0);
lean_inc(v_val_3986_);
lean_dec_ref_known(v___x_3978_, 1);
v___x_3987_ = l_Lean_ConstantInfo_type(v_val_3986_);
lean_dec(v_val_3986_);
if (lean_obj_tag(v___x_3987_) == 4)
{
lean_object* v_declName_3988_; 
v_declName_3988_ = lean_ctor_get(v___x_3987_, 0);
lean_inc(v_declName_3988_);
lean_dec_ref_known(v___x_3987_, 2);
if (lean_obj_tag(v_declName_3988_) == 1)
{
lean_object* v_pre_3989_; 
v_pre_3989_ = lean_ctor_get(v_declName_3988_, 0);
lean_inc(v_pre_3989_);
if (lean_obj_tag(v_pre_3989_) == 1)
{
lean_object* v_pre_3990_; 
v_pre_3990_ = lean_ctor_get(v_pre_3989_, 0);
if (lean_obj_tag(v_pre_3990_) == 0)
{
lean_object* v_str_3991_; lean_object* v_str_3992_; lean_object* v___x_3993_; uint8_t v___x_3994_; 
v_str_3991_ = lean_ctor_get(v_declName_3988_, 1);
lean_inc_ref(v_str_3991_);
lean_dec_ref_known(v_declName_3988_, 2);
v_str_3992_ = lean_ctor_get(v_pre_3989_, 1);
lean_inc_ref(v_str_3992_);
lean_dec_ref_known(v_pre_3989_, 2);
v___x_3993_ = ((lean_object*)(l_Lean_AttributeImplCore_ref___autoParam___closed__0));
v___x_3994_ = lean_string_dec_eq(v_str_3992_, v___x_3993_);
lean_dec_ref(v_str_3992_);
if (v___x_3994_ == 0)
{
lean_dec_ref(v_str_3991_);
lean_dec(v_declName_3974_);
lean_dec_ref(v_env_3972_);
goto v___jp_3975_;
}
else
{
lean_object* v___x_3995_; uint8_t v___x_3996_; 
v___x_3995_ = ((lean_object*)(l_Lean_mkAttributeImplOfConstantUnsafe___closed__3));
v___x_3996_ = lean_string_dec_eq(v_str_3991_, v___x_3995_);
lean_dec_ref(v_str_3991_);
if (v___x_3996_ == 0)
{
lean_dec(v_declName_3974_);
lean_dec_ref(v_env_3972_);
goto v___jp_3975_;
}
else
{
lean_object* v___x_3997_; 
v___x_3997_ = l_Lean_Environment_evalConst___redArg(v_env_3972_, v_opts_3973_, v_declName_3974_, v___x_3996_);
lean_dec(v_declName_3974_);
lean_dec_ref(v_env_3972_);
return v___x_3997_;
}
}
}
else
{
lean_dec_ref_known(v_pre_3989_, 2);
lean_dec_ref_known(v_declName_3988_, 2);
lean_dec(v_declName_3974_);
lean_dec_ref(v_env_3972_);
goto v___jp_3975_;
}
}
else
{
lean_dec(v_pre_3989_);
lean_dec_ref_known(v_declName_3988_, 2);
lean_dec(v_declName_3974_);
lean_dec_ref(v_env_3972_);
goto v___jp_3975_;
}
}
else
{
lean_dec(v_declName_3988_);
lean_dec(v_declName_3974_);
lean_dec_ref(v_env_3972_);
goto v___jp_3975_;
}
}
else
{
lean_dec_ref(v___x_3987_);
lean_dec(v_declName_3974_);
lean_dec_ref(v_env_3972_);
goto v___jp_3975_;
}
}
v___jp_3975_:
{
lean_object* v___x_3976_; 
v___x_3976_ = ((lean_object*)(l_Lean_mkAttributeImplOfConstantUnsafe___closed__1));
return v___x_3976_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkAttributeImplOfConstantUnsafe___boxed(lean_object* v_env_3998_, lean_object* v_opts_3999_, lean_object* v_declName_4000_){
_start:
{
lean_object* v_res_4001_; 
v_res_4001_ = l_Lean_mkAttributeImplOfConstantUnsafe(v_env_3998_, v_opts_3999_, v_declName_4000_);
lean_dec_ref(v_opts_3999_);
return v_res_4001_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg(lean_object* v_as_4002_, size_t v_i_4003_, size_t v_stop_4004_, lean_object* v_b_4005_){
_start:
{
uint8_t v___x_4007_; 
v___x_4007_ = lean_usize_dec_eq(v_i_4003_, v_stop_4004_);
if (v___x_4007_ == 0)
{
lean_object* v___x_4008_; lean_object* v___x_4009_; 
v___x_4008_ = lean_array_uget_borrowed(v_as_4002_, v_i_4003_);
lean_inc(v___x_4008_);
v___x_4009_ = l_Lean_mkAttributeImplOfEntry(v___x_4008_);
if (lean_obj_tag(v___x_4009_) == 0)
{
lean_object* v_a_4010_; lean_object* v_toAttributeImplCore_4011_; lean_object* v_name_4012_; lean_object* v___x_4013_; size_t v___x_4014_; size_t v___x_4015_; 
v_a_4010_ = lean_ctor_get(v___x_4009_, 0);
lean_inc(v_a_4010_);
lean_dec_ref_known(v___x_4009_, 1);
v_toAttributeImplCore_4011_ = lean_ctor_get(v_a_4010_, 0);
v_name_4012_ = lean_ctor_get(v_toAttributeImplCore_4011_, 1);
lean_inc(v_name_4012_);
v___x_4013_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1___redArg(v_b_4005_, v_name_4012_, v_a_4010_);
v___x_4014_ = ((size_t)1ULL);
v___x_4015_ = lean_usize_add(v_i_4003_, v___x_4014_);
v_i_4003_ = v___x_4015_;
v_b_4005_ = v___x_4013_;
goto _start;
}
else
{
lean_object* v_a_4017_; lean_object* v___x_4019_; uint8_t v_isShared_4020_; uint8_t v_isSharedCheck_4024_; 
lean_dec_ref(v_b_4005_);
v_a_4017_ = lean_ctor_get(v___x_4009_, 0);
v_isSharedCheck_4024_ = !lean_is_exclusive(v___x_4009_);
if (v_isSharedCheck_4024_ == 0)
{
v___x_4019_ = v___x_4009_;
v_isShared_4020_ = v_isSharedCheck_4024_;
goto v_resetjp_4018_;
}
else
{
lean_inc(v_a_4017_);
lean_dec(v___x_4009_);
v___x_4019_ = lean_box(0);
v_isShared_4020_ = v_isSharedCheck_4024_;
goto v_resetjp_4018_;
}
v_resetjp_4018_:
{
lean_object* v___x_4022_; 
if (v_isShared_4020_ == 0)
{
v___x_4022_ = v___x_4019_;
goto v_reusejp_4021_;
}
else
{
lean_object* v_reuseFailAlloc_4023_; 
v_reuseFailAlloc_4023_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4023_, 0, v_a_4017_);
v___x_4022_ = v_reuseFailAlloc_4023_;
goto v_reusejp_4021_;
}
v_reusejp_4021_:
{
return v___x_4022_;
}
}
}
}
else
{
lean_object* v___x_4025_; 
v___x_4025_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4025_, 0, v_b_4005_);
return v___x_4025_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg___boxed(lean_object* v_as_4026_, lean_object* v_i_4027_, lean_object* v_stop_4028_, lean_object* v_b_4029_, lean_object* v___y_4030_){
_start:
{
size_t v_i_boxed_4031_; size_t v_stop_boxed_4032_; lean_object* v_res_4033_; 
v_i_boxed_4031_ = lean_unbox_usize(v_i_4027_);
lean_dec(v_i_4027_);
v_stop_boxed_4032_ = lean_unbox_usize(v_stop_4028_);
lean_dec(v_stop_4028_);
v_res_4033_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg(v_as_4026_, v_i_boxed_4031_, v_stop_boxed_4032_, v_b_4029_);
lean_dec_ref(v_as_4026_);
return v_res_4033_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__1(lean_object* v_as_4034_, size_t v_i_4035_, size_t v_stop_4036_, lean_object* v_b_4037_, lean_object* v___y_4038_){
_start:
{
lean_object* v_a_4041_; lean_object* v___y_4046_; uint8_t v___x_4048_; 
v___x_4048_ = lean_usize_dec_eq(v_i_4035_, v_stop_4036_);
if (v___x_4048_ == 0)
{
lean_object* v___x_4049_; lean_object* v___x_4050_; lean_object* v___x_4051_; uint8_t v___x_4052_; 
v___x_4049_ = lean_array_uget_borrowed(v_as_4034_, v_i_4035_);
v___x_4050_ = lean_unsigned_to_nat(0u);
v___x_4051_ = lean_array_get_size(v___x_4049_);
v___x_4052_ = lean_nat_dec_lt(v___x_4050_, v___x_4051_);
if (v___x_4052_ == 0)
{
v_a_4041_ = v_b_4037_;
goto v___jp_4040_;
}
else
{
uint8_t v___x_4053_; 
v___x_4053_ = lean_nat_dec_le(v___x_4051_, v___x_4051_);
if (v___x_4053_ == 0)
{
if (v___x_4052_ == 0)
{
v_a_4041_ = v_b_4037_;
goto v___jp_4040_;
}
else
{
size_t v___x_4054_; size_t v___x_4055_; lean_object* v___x_4056_; 
v___x_4054_ = ((size_t)0ULL);
v___x_4055_ = lean_usize_of_nat(v___x_4051_);
v___x_4056_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg(v___x_4049_, v___x_4054_, v___x_4055_, v_b_4037_);
v___y_4046_ = v___x_4056_;
goto v___jp_4045_;
}
}
else
{
size_t v___x_4057_; size_t v___x_4058_; lean_object* v___x_4059_; 
v___x_4057_ = ((size_t)0ULL);
v___x_4058_ = lean_usize_of_nat(v___x_4051_);
v___x_4059_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg(v___x_4049_, v___x_4057_, v___x_4058_, v_b_4037_);
v___y_4046_ = v___x_4059_;
goto v___jp_4045_;
}
}
}
else
{
lean_object* v___x_4060_; 
v___x_4060_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4060_, 0, v_b_4037_);
return v___x_4060_;
}
v___jp_4040_:
{
size_t v___x_4042_; size_t v___x_4043_; 
v___x_4042_ = ((size_t)1ULL);
v___x_4043_ = lean_usize_add(v_i_4035_, v___x_4042_);
v_i_4035_ = v___x_4043_;
v_b_4037_ = v_a_4041_;
goto _start;
}
v___jp_4045_:
{
if (lean_obj_tag(v___y_4046_) == 0)
{
lean_object* v_a_4047_; 
v_a_4047_ = lean_ctor_get(v___y_4046_, 0);
lean_inc(v_a_4047_);
lean_dec_ref_known(v___y_4046_, 1);
v_a_4041_ = v_a_4047_;
goto v___jp_4040_;
}
else
{
return v___y_4046_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__1___boxed(lean_object* v_as_4061_, lean_object* v_i_4062_, lean_object* v_stop_4063_, lean_object* v_b_4064_, lean_object* v___y_4065_, lean_object* v___y_4066_){
_start:
{
size_t v_i_boxed_4067_; size_t v_stop_boxed_4068_; lean_object* v_res_4069_; 
v_i_boxed_4067_ = lean_unbox_usize(v_i_4062_);
lean_dec(v_i_4062_);
v_stop_boxed_4068_ = lean_unbox_usize(v_stop_4063_);
lean_dec(v_stop_4063_);
v_res_4069_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__1(v_as_4061_, v_i_boxed_4067_, v_stop_boxed_4068_, v_b_4064_, v___y_4065_);
lean_dec_ref(v___y_4065_);
lean_dec_ref(v_as_4061_);
return v_res_4069_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_AttributeExtension_addImported(lean_object* v_es_4070_, lean_object* v_a_4071_){
_start:
{
lean_object* v_a_4074_; lean_object* v___y_4079_; lean_object* v___x_4089_; lean_object* v___x_4090_; lean_object* v___x_4091_; lean_object* v___x_4092_; uint8_t v___x_4093_; 
v___x_4089_ = l_Lean_attributeMapRef;
v___x_4090_ = lean_st_ref_get(v___x_4089_);
v___x_4091_ = lean_unsigned_to_nat(0u);
v___x_4092_ = lean_array_get_size(v_es_4070_);
v___x_4093_ = lean_nat_dec_lt(v___x_4091_, v___x_4092_);
if (v___x_4093_ == 0)
{
v_a_4074_ = v___x_4090_;
goto v___jp_4073_;
}
else
{
uint8_t v___x_4094_; 
v___x_4094_ = lean_nat_dec_le(v___x_4092_, v___x_4092_);
if (v___x_4094_ == 0)
{
if (v___x_4093_ == 0)
{
v_a_4074_ = v___x_4090_;
goto v___jp_4073_;
}
else
{
size_t v___x_4095_; size_t v___x_4096_; lean_object* v___x_4097_; 
v___x_4095_ = ((size_t)0ULL);
v___x_4096_ = lean_usize_of_nat(v___x_4092_);
v___x_4097_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__1(v_es_4070_, v___x_4095_, v___x_4096_, v___x_4090_, v_a_4071_);
v___y_4079_ = v___x_4097_;
goto v___jp_4078_;
}
}
else
{
size_t v___x_4098_; size_t v___x_4099_; lean_object* v___x_4100_; 
v___x_4098_ = ((size_t)0ULL);
v___x_4099_ = lean_usize_of_nat(v___x_4092_);
v___x_4100_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__1(v_es_4070_, v___x_4098_, v___x_4099_, v___x_4090_, v_a_4071_);
v___y_4079_ = v___x_4100_;
goto v___jp_4078_;
}
}
v___jp_4073_:
{
lean_object* v___x_4075_; lean_object* v___x_4076_; lean_object* v___x_4077_; 
v___x_4075_ = lean_box(0);
v___x_4076_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4076_, 0, v___x_4075_);
lean_ctor_set(v___x_4076_, 1, v_a_4074_);
v___x_4077_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4077_, 0, v___x_4076_);
return v___x_4077_;
}
v___jp_4078_:
{
if (lean_obj_tag(v___y_4079_) == 0)
{
lean_object* v_a_4080_; 
v_a_4080_ = lean_ctor_get(v___y_4079_, 0);
lean_inc(v_a_4080_);
lean_dec_ref_known(v___y_4079_, 1);
v_a_4074_ = v_a_4080_;
goto v___jp_4073_;
}
else
{
lean_object* v_a_4081_; lean_object* v___x_4083_; uint8_t v_isShared_4084_; uint8_t v_isSharedCheck_4088_; 
v_a_4081_ = lean_ctor_get(v___y_4079_, 0);
v_isSharedCheck_4088_ = !lean_is_exclusive(v___y_4079_);
if (v_isSharedCheck_4088_ == 0)
{
v___x_4083_ = v___y_4079_;
v_isShared_4084_ = v_isSharedCheck_4088_;
goto v_resetjp_4082_;
}
else
{
lean_inc(v_a_4081_);
lean_dec(v___y_4079_);
v___x_4083_ = lean_box(0);
v_isShared_4084_ = v_isSharedCheck_4088_;
goto v_resetjp_4082_;
}
v_resetjp_4082_:
{
lean_object* v___x_4086_; 
if (v_isShared_4084_ == 0)
{
v___x_4086_ = v___x_4083_;
goto v_reusejp_4085_;
}
else
{
lean_object* v_reuseFailAlloc_4087_; 
v_reuseFailAlloc_4087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4087_, 0, v_a_4081_);
v___x_4086_ = v_reuseFailAlloc_4087_;
goto v_reusejp_4085_;
}
v_reusejp_4085_:
{
return v___x_4086_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_AttributeExtension_addImported___boxed(lean_object* v_es_4101_, lean_object* v_a_4102_, lean_object* v_a_4103_){
_start:
{
lean_object* v_res_4104_; 
v_res_4104_ = l___private_Lean_Attributes_0__Lean_AttributeExtension_addImported(v_es_4101_, v_a_4102_);
lean_dec_ref(v_a_4102_);
lean_dec_ref(v_es_4101_);
return v_res_4104_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0(lean_object* v_as_4105_, size_t v_i_4106_, size_t v_stop_4107_, lean_object* v_b_4108_, lean_object* v___y_4109_){
_start:
{
lean_object* v___x_4111_; 
v___x_4111_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___redArg(v_as_4105_, v_i_4106_, v_stop_4107_, v_b_4108_);
return v___x_4111_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0___boxed(lean_object* v_as_4112_, lean_object* v_i_4113_, lean_object* v_stop_4114_, lean_object* v_b_4115_, lean_object* v___y_4116_, lean_object* v___y_4117_){
_start:
{
size_t v_i_boxed_4118_; size_t v_stop_boxed_4119_; lean_object* v_res_4120_; 
v_i_boxed_4118_ = lean_unbox_usize(v_i_4113_);
lean_dec(v_i_4113_);
v_stop_boxed_4119_ = lean_unbox_usize(v_stop_4114_);
lean_dec(v_stop_4114_);
v_res_4120_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Attributes_0__Lean_AttributeExtension_addImported_spec__0(v_as_4112_, v_i_boxed_4118_, v_stop_boxed_4119_, v_b_4115_, v___y_4116_);
lean_dec_ref(v___y_4116_);
lean_dec_ref(v_as_4112_);
return v_res_4120_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_addAttrEntry(lean_object* v_s_4121_, lean_object* v_e_4122_){
_start:
{
lean_object* v_snd_4123_; lean_object* v_toAttributeImplCore_4124_; lean_object* v_fst_4125_; lean_object* v___x_4127_; uint8_t v_isShared_4128_; uint8_t v_isSharedCheck_4143_; 
v_snd_4123_ = lean_ctor_get(v_e_4122_, 1);
lean_inc(v_snd_4123_);
v_toAttributeImplCore_4124_ = lean_ctor_get(v_snd_4123_, 0);
v_fst_4125_ = lean_ctor_get(v_e_4122_, 0);
v_isSharedCheck_4143_ = !lean_is_exclusive(v_e_4122_);
if (v_isSharedCheck_4143_ == 0)
{
lean_object* v_unused_4144_; 
v_unused_4144_ = lean_ctor_get(v_e_4122_, 1);
lean_dec(v_unused_4144_);
v___x_4127_ = v_e_4122_;
v_isShared_4128_ = v_isSharedCheck_4143_;
goto v_resetjp_4126_;
}
else
{
lean_inc(v_fst_4125_);
lean_dec(v_e_4122_);
v___x_4127_ = lean_box(0);
v_isShared_4128_ = v_isSharedCheck_4143_;
goto v_resetjp_4126_;
}
v_resetjp_4126_:
{
lean_object* v_newEntries_4129_; lean_object* v_map_4130_; lean_object* v___x_4132_; uint8_t v_isShared_4133_; uint8_t v_isSharedCheck_4142_; 
v_newEntries_4129_ = lean_ctor_get(v_s_4121_, 0);
v_map_4130_ = lean_ctor_get(v_s_4121_, 1);
v_isSharedCheck_4142_ = !lean_is_exclusive(v_s_4121_);
if (v_isSharedCheck_4142_ == 0)
{
v___x_4132_ = v_s_4121_;
v_isShared_4133_ = v_isSharedCheck_4142_;
goto v_resetjp_4131_;
}
else
{
lean_inc(v_map_4130_);
lean_inc(v_newEntries_4129_);
lean_dec(v_s_4121_);
v___x_4132_ = lean_box(0);
v_isShared_4133_ = v_isSharedCheck_4142_;
goto v_resetjp_4131_;
}
v_resetjp_4131_:
{
lean_object* v_name_4134_; lean_object* v___x_4136_; 
v_name_4134_ = lean_ctor_get(v_toAttributeImplCore_4124_, 1);
lean_inc(v_name_4134_);
if (v_isShared_4128_ == 0)
{
lean_ctor_set_tag(v___x_4127_, 1);
lean_ctor_set(v___x_4127_, 1, v_newEntries_4129_);
v___x_4136_ = v___x_4127_;
goto v_reusejp_4135_;
}
else
{
lean_object* v_reuseFailAlloc_4141_; 
v_reuseFailAlloc_4141_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4141_, 0, v_fst_4125_);
lean_ctor_set(v_reuseFailAlloc_4141_, 1, v_newEntries_4129_);
v___x_4136_ = v_reuseFailAlloc_4141_;
goto v_reusejp_4135_;
}
v_reusejp_4135_:
{
lean_object* v___x_4137_; lean_object* v___x_4139_; 
v___x_4137_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1___redArg(v_map_4130_, v_name_4134_, v_snd_4123_);
if (v_isShared_4133_ == 0)
{
lean_ctor_set(v___x_4132_, 1, v___x_4137_);
lean_ctor_set(v___x_4132_, 0, v___x_4136_);
v___x_4139_ = v___x_4132_;
goto v_reusejp_4138_;
}
else
{
lean_object* v_reuseFailAlloc_4140_; 
v_reuseFailAlloc_4140_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4140_, 0, v___x_4136_);
lean_ctor_set(v_reuseFailAlloc_4140_, 1, v___x_4137_);
v___x_4139_ = v_reuseFailAlloc_4140_;
goto v_reusejp_4138_;
}
v_reusejp_4138_:
{
return v___x_4139_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn___lam__0_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(lean_object* v_x_4145_, lean_object* v_s_4146_){
_start:
{
lean_object* v_newEntries_4147_; lean_object* v___x_4148_; lean_object* v___x_4149_; lean_object* v___x_4150_; 
v_newEntries_4147_ = lean_ctor_get(v_s_4146_, 0);
lean_inc(v_newEntries_4147_);
lean_dec_ref(v_s_4146_);
v___x_4148_ = l_List_reverse___redArg(v_newEntries_4147_);
v___x_4149_ = lean_array_mk(v___x_4148_);
lean_inc_ref_n(v___x_4149_, 2);
v___x_4150_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4150_, 0, v___x_4149_);
lean_ctor_set(v___x_4150_, 1, v___x_4149_);
lean_ctor_set(v___x_4150_, 2, v___x_4149_);
return v___x_4150_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn___lam__0_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2____boxed(lean_object* v_x_4151_, lean_object* v_s_4152_){
_start:
{
lean_object* v_res_4153_; 
v_res_4153_ = l___private_Lean_Attributes_0__Lean_initFn___lam__0_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(v_x_4151_, v_s_4152_);
lean_dec_ref(v_x_4151_);
return v_res_4153_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn___lam__1_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(lean_object* v_s_4154_){
_start:
{
lean_object* v_newEntries_4155_; lean_object* v___x_4157_; uint8_t v_isShared_4158_; uint8_t v_isSharedCheck_4166_; 
v_newEntries_4155_ = lean_ctor_get(v_s_4154_, 0);
v_isSharedCheck_4166_ = !lean_is_exclusive(v_s_4154_);
if (v_isSharedCheck_4166_ == 0)
{
lean_object* v_unused_4167_; 
v_unused_4167_ = lean_ctor_get(v_s_4154_, 1);
lean_dec(v_unused_4167_);
v___x_4157_ = v_s_4154_;
v_isShared_4158_ = v_isSharedCheck_4166_;
goto v_resetjp_4156_;
}
else
{
lean_inc(v_newEntries_4155_);
lean_dec(v_s_4154_);
v___x_4157_ = lean_box(0);
v_isShared_4158_ = v_isSharedCheck_4166_;
goto v_resetjp_4156_;
}
v_resetjp_4156_:
{
lean_object* v___x_4159_; lean_object* v___x_4160_; lean_object* v___x_4161_; lean_object* v___x_4162_; lean_object* v___x_4164_; 
v___x_4159_ = ((lean_object*)(l_Lean_registerTagAttribute___lam__2___closed__4));
v___x_4160_ = l_List_lengthTR___redArg(v_newEntries_4155_);
lean_dec(v_newEntries_4155_);
v___x_4161_ = l_Nat_reprFast(v___x_4160_);
v___x_4162_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4162_, 0, v___x_4161_);
if (v_isShared_4158_ == 0)
{
lean_ctor_set_tag(v___x_4157_, 5);
lean_ctor_set(v___x_4157_, 1, v___x_4162_);
lean_ctor_set(v___x_4157_, 0, v___x_4159_);
v___x_4164_ = v___x_4157_;
goto v_reusejp_4163_;
}
else
{
lean_object* v_reuseFailAlloc_4165_; 
v_reuseFailAlloc_4165_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4165_, 0, v___x_4159_);
lean_ctor_set(v_reuseFailAlloc_4165_, 1, v___x_4162_);
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
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn___lam__2_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(lean_object* v_s_4168_){
_start:
{
lean_object* v_newEntries_4169_; lean_object* v___x_4170_; lean_object* v___x_4171_; 
v_newEntries_4169_ = lean_ctor_get(v_s_4168_, 0);
lean_inc(v_newEntries_4169_);
lean_dec_ref(v_s_4168_);
v___x_4170_ = l_List_reverse___redArg(v_newEntries_4169_);
v___x_4171_ = lean_array_mk(v___x_4170_);
return v___x_4171_;
}
}
static lean_object* _init_l___private_Lean_Attributes_0__Lean_initFn___closed__7_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4181_; lean_object* v___x_4182_; lean_object* v___f_4183_; lean_object* v___f_4184_; lean_object* v___x_4185_; lean_object* v___x_4186_; lean_object* v___x_4187_; lean_object* v___x_4188_; lean_object* v___x_4189_; 
v___x_4181_ = lean_box(0);
v___x_4182_ = lean_box(2);
v___f_4183_ = ((lean_object*)(l___private_Lean_Attributes_0__Lean_initFn___closed__1_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___f_4184_ = ((lean_object*)(l___private_Lean_Attributes_0__Lean_initFn___closed__0_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___x_4185_ = ((lean_object*)(l___private_Lean_Attributes_0__Lean_initFn___closed__6_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___x_4186_ = ((lean_object*)(l___private_Lean_Attributes_0__Lean_initFn___closed__5_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___x_4187_ = lean_alloc_closure((void*)(l___private_Lean_Attributes_0__Lean_AttributeExtension_mkInitial___boxed), 1, 0);
v___x_4188_ = ((lean_object*)(l___private_Lean_Attributes_0__Lean_initFn___closed__4_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___x_4189_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_4189_, 0, v___x_4188_);
lean_ctor_set(v___x_4189_, 1, v___x_4187_);
lean_ctor_set(v___x_4189_, 2, v___x_4186_);
lean_ctor_set(v___x_4189_, 3, v___x_4185_);
lean_ctor_set(v___x_4189_, 4, v___f_4184_);
lean_ctor_set(v___x_4189_, 5, v___f_4183_);
lean_ctor_set(v___x_4189_, 6, v___x_4182_);
lean_ctor_set(v___x_4189_, 7, v___x_4181_);
return v___x_4189_;
}
}
static lean_object* _init_l___private_Lean_Attributes_0__Lean_initFn___closed__8_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_4190_; lean_object* v___x_4191_; lean_object* v___x_4192_; 
v___f_4190_ = ((lean_object*)(l___private_Lean_Attributes_0__Lean_initFn___closed__2_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_));
v___x_4191_ = lean_obj_once(&l___private_Lean_Attributes_0__Lean_initFn___closed__7_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_, &l___private_Lean_Attributes_0__Lean_initFn___closed__7_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2__once, _init_l___private_Lean_Attributes_0__Lean_initFn___closed__7_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_);
v___x_4192_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4192_, 0, v___x_4191_);
lean_ctor_set(v___x_4192_, 1, v___f_4190_);
return v___x_4192_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4194_; lean_object* v___x_4195_; 
v___x_4194_ = lean_obj_once(&l___private_Lean_Attributes_0__Lean_initFn___closed__8_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_, &l___private_Lean_Attributes_0__Lean_initFn___closed__8_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2__once, _init_l___private_Lean_Attributes_0__Lean_initFn___closed__8_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_);
v___x_4195_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_4194_);
return v___x_4195_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2____boxed(lean_object* v_a_4196_){
_start:
{
lean_object* v_res_4197_; 
v_res_4197_ = l___private_Lean_Attributes_0__Lean_initFn_00___x40_Lean_Attributes_3560353829____hygCtx___hyg_2_();
return v_res_4197_;
}
}
LEAN_EXPORT lean_object* l_Lean_isBuiltinAttribute(lean_object* v_n_4198_){
_start:
{
lean_object* v___x_4200_; lean_object* v___x_4201_; uint8_t v___x_4202_; lean_object* v___x_4203_; lean_object* v___x_4204_; 
v___x_4200_ = l_Lean_attributeMapRef;
v___x_4201_ = lean_st_ref_get(v___x_4200_);
v___x_4202_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(v___x_4201_, v_n_4198_);
lean_dec(v___x_4201_);
v___x_4203_ = lean_box(v___x_4202_);
v___x_4204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4204_, 0, v___x_4203_);
return v___x_4204_;
}
}
LEAN_EXPORT lean_object* l_Lean_isBuiltinAttribute___boxed(lean_object* v_n_4205_, lean_object* v_a_4206_){
_start:
{
lean_object* v_res_4207_; 
v_res_4207_ = l_Lean_isBuiltinAttribute(v_n_4205_);
lean_dec(v_n_4205_);
return v_res_4207_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_getBuiltinAttributeNames_spec__0(lean_object* v_x_4208_, lean_object* v_x_4209_){
_start:
{
if (lean_obj_tag(v_x_4209_) == 0)
{
return v_x_4208_;
}
else
{
lean_object* v_key_4210_; lean_object* v_tail_4211_; lean_object* v___x_4212_; 
v_key_4210_ = lean_ctor_get(v_x_4209_, 0);
v_tail_4211_ = lean_ctor_get(v_x_4209_, 2);
lean_inc(v_key_4210_);
v___x_4212_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4212_, 0, v_key_4210_);
lean_ctor_set(v___x_4212_, 1, v_x_4208_);
v_x_4208_ = v___x_4212_;
v_x_4209_ = v_tail_4211_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_getBuiltinAttributeNames_spec__0___boxed(lean_object* v_x_4214_, lean_object* v_x_4215_){
_start:
{
lean_object* v_res_4216_; 
v_res_4216_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_getBuiltinAttributeNames_spec__0(v_x_4214_, v_x_4215_);
lean_dec(v_x_4215_);
return v_res_4216_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1(lean_object* v_as_4217_, size_t v_i_4218_, size_t v_stop_4219_, lean_object* v_b_4220_){
_start:
{
uint8_t v___x_4221_; 
v___x_4221_ = lean_usize_dec_eq(v_i_4218_, v_stop_4219_);
if (v___x_4221_ == 0)
{
lean_object* v___x_4222_; lean_object* v___x_4223_; size_t v___x_4224_; size_t v___x_4225_; 
v___x_4222_ = lean_array_uget_borrowed(v_as_4217_, v_i_4218_);
v___x_4223_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_getBuiltinAttributeNames_spec__0(v_b_4220_, v___x_4222_);
v___x_4224_ = ((size_t)1ULL);
v___x_4225_ = lean_usize_add(v_i_4218_, v___x_4224_);
v_i_4218_ = v___x_4225_;
v_b_4220_ = v___x_4223_;
goto _start;
}
else
{
return v_b_4220_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1___boxed(lean_object* v_as_4227_, lean_object* v_i_4228_, lean_object* v_stop_4229_, lean_object* v_b_4230_){
_start:
{
size_t v_i_boxed_4231_; size_t v_stop_boxed_4232_; lean_object* v_res_4233_; 
v_i_boxed_4231_ = lean_unbox_usize(v_i_4228_);
lean_dec(v_i_4228_);
v_stop_boxed_4232_ = lean_unbox_usize(v_stop_4229_);
lean_dec(v_stop_4229_);
v_res_4233_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1(v_as_4227_, v_i_boxed_4231_, v_stop_boxed_4232_, v_b_4230_);
lean_dec_ref(v_as_4227_);
return v_res_4233_;
}
}
LEAN_EXPORT lean_object* l_Lean_getBuiltinAttributeNames(){
_start:
{
lean_object* v___x_4235_; lean_object* v___x_4236_; lean_object* v_buckets_4237_; lean_object* v___x_4238_; lean_object* v___x_4239_; lean_object* v___x_4240_; uint8_t v___x_4241_; 
v___x_4235_ = l_Lean_attributeMapRef;
v___x_4236_ = lean_st_ref_get(v___x_4235_);
v_buckets_4237_ = lean_ctor_get(v___x_4236_, 1);
lean_inc_ref(v_buckets_4237_);
lean_dec(v___x_4236_);
v___x_4238_ = lean_box(0);
v___x_4239_ = lean_unsigned_to_nat(0u);
v___x_4240_ = lean_array_get_size(v_buckets_4237_);
v___x_4241_ = lean_nat_dec_lt(v___x_4239_, v___x_4240_);
if (v___x_4241_ == 0)
{
lean_object* v___x_4242_; 
lean_dec_ref(v_buckets_4237_);
v___x_4242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4242_, 0, v___x_4238_);
return v___x_4242_;
}
else
{
size_t v___x_4243_; size_t v___x_4244_; lean_object* v___x_4245_; lean_object* v___x_4246_; 
v___x_4243_ = ((size_t)0ULL);
v___x_4244_ = lean_usize_of_nat(v___x_4240_);
v___x_4245_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1(v_buckets_4237_, v___x_4243_, v___x_4244_, v___x_4238_);
lean_dec_ref(v_buckets_4237_);
v___x_4246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4246_, 0, v___x_4245_);
return v___x_4246_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getBuiltinAttributeNames___boxed(lean_object* v_a_4247_){
_start:
{
lean_object* v_res_4248_; 
v_res_4248_ = l_Lean_getBuiltinAttributeNames();
return v_res_4248_;
}
}
LEAN_EXPORT lean_object* l_Lean_getBuiltinAttributeImpl(lean_object* v_attrName_4250_){
_start:
{
lean_object* v___x_4252_; lean_object* v___x_4253_; lean_object* v___x_4254_; 
v___x_4252_ = l_Lean_attributeMapRef;
v___x_4253_ = lean_st_ref_get(v___x_4252_);
v___x_4254_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(v___x_4253_, v_attrName_4250_);
lean_dec(v___x_4253_);
if (lean_obj_tag(v___x_4254_) == 0)
{
lean_object* v___x_4255_; uint8_t v___x_4256_; lean_object* v___x_4257_; lean_object* v___x_4258_; lean_object* v___x_4259_; lean_object* v___x_4260_; lean_object* v___x_4261_; lean_object* v___x_4262_; 
v___x_4255_ = ((lean_object*)(l_Lean_getBuiltinAttributeImpl___closed__0));
v___x_4256_ = 1;
v___x_4257_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_attrName_4250_, v___x_4256_);
v___x_4258_ = lean_string_append(v___x_4255_, v___x_4257_);
lean_dec_ref(v___x_4257_);
v___x_4259_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__4));
v___x_4260_ = lean_string_append(v___x_4258_, v___x_4259_);
v___x_4261_ = lean_mk_io_user_error(v___x_4260_);
v___x_4262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4262_, 0, v___x_4261_);
return v___x_4262_;
}
else
{
lean_object* v_val_4263_; lean_object* v___x_4265_; uint8_t v_isShared_4266_; uint8_t v_isSharedCheck_4270_; 
lean_dec(v_attrName_4250_);
v_val_4263_ = lean_ctor_get(v___x_4254_, 0);
v_isSharedCheck_4270_ = !lean_is_exclusive(v___x_4254_);
if (v_isSharedCheck_4270_ == 0)
{
v___x_4265_ = v___x_4254_;
v_isShared_4266_ = v_isSharedCheck_4270_;
goto v_resetjp_4264_;
}
else
{
lean_inc(v_val_4263_);
lean_dec(v___x_4254_);
v___x_4265_ = lean_box(0);
v_isShared_4266_ = v_isSharedCheck_4270_;
goto v_resetjp_4264_;
}
v_resetjp_4264_:
{
lean_object* v___x_4268_; 
if (v_isShared_4266_ == 0)
{
lean_ctor_set_tag(v___x_4265_, 0);
v___x_4268_ = v___x_4265_;
goto v_reusejp_4267_;
}
else
{
lean_object* v_reuseFailAlloc_4269_; 
v_reuseFailAlloc_4269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4269_, 0, v_val_4263_);
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
LEAN_EXPORT lean_object* l_Lean_getBuiltinAttributeImpl___boxed(lean_object* v_attrName_4271_, lean_object* v_a_4272_){
_start:
{
lean_object* v_res_4273_; 
v_res_4273_ = l_Lean_getBuiltinAttributeImpl(v_attrName_4271_);
return v_res_4273_;
}
}
LEAN_EXPORT uint8_t l_Lean_isAttribute(lean_object* v_env_4274_, lean_object* v_attrName_4275_){
_start:
{
lean_object* v___x_4276_; lean_object* v_toEnvExtension_4277_; lean_object* v_asyncMode_4278_; lean_object* v___x_4279_; lean_object* v___x_4280_; lean_object* v___x_4281_; lean_object* v_map_4282_; uint8_t v___x_4283_; 
v___x_4276_ = l_Lean_attributeExtension;
v_toEnvExtension_4277_ = lean_ctor_get(v___x_4276_, 0);
v_asyncMode_4278_ = lean_ctor_get(v_toEnvExtension_4277_, 2);
v___x_4279_ = l_Lean_instInhabitedAttributeExtensionState_default;
v___x_4280_ = lean_box(0);
v___x_4281_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_4279_, v___x_4276_, v_env_4274_, v_asyncMode_4278_, v___x_4280_);
v_map_4282_ = lean_ctor_get(v___x_4281_, 1);
lean_inc_ref(v_map_4282_);
lean_dec(v___x_4281_);
v___x_4283_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(v_map_4282_, v_attrName_4275_);
lean_dec_ref(v_map_4282_);
return v___x_4283_;
}
}
LEAN_EXPORT lean_object* l_Lean_isAttribute___boxed(lean_object* v_env_4284_, lean_object* v_attrName_4285_){
_start:
{
uint8_t v_res_4286_; lean_object* v_r_4287_; 
v_res_4286_ = l_Lean_isAttribute(v_env_4284_, v_attrName_4285_);
lean_dec(v_attrName_4285_);
v_r_4287_ = lean_box(v_res_4286_);
return v_r_4287_;
}
}
LEAN_EXPORT lean_object* l_Lean_getAttributeNames(lean_object* v_env_4288_){
_start:
{
lean_object* v___x_4289_; lean_object* v_toEnvExtension_4290_; lean_object* v_asyncMode_4291_; lean_object* v___x_4292_; lean_object* v___x_4293_; lean_object* v___x_4294_; lean_object* v_map_4295_; lean_object* v_buckets_4296_; lean_object* v___x_4297_; lean_object* v___x_4298_; lean_object* v___x_4299_; uint8_t v___x_4300_; 
v___x_4289_ = l_Lean_attributeExtension;
v_toEnvExtension_4290_ = lean_ctor_get(v___x_4289_, 0);
v_asyncMode_4291_ = lean_ctor_get(v_toEnvExtension_4290_, 2);
v___x_4292_ = l_Lean_instInhabitedAttributeExtensionState_default;
v___x_4293_ = lean_box(0);
v___x_4294_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_4292_, v___x_4289_, v_env_4288_, v_asyncMode_4291_, v___x_4293_);
v_map_4295_ = lean_ctor_get(v___x_4294_, 1);
lean_inc_ref(v_map_4295_);
lean_dec(v___x_4294_);
v_buckets_4296_ = lean_ctor_get(v_map_4295_, 1);
lean_inc_ref(v_buckets_4296_);
lean_dec_ref(v_map_4295_);
v___x_4297_ = lean_box(0);
v___x_4298_ = lean_unsigned_to_nat(0u);
v___x_4299_ = lean_array_get_size(v_buckets_4296_);
v___x_4300_ = lean_nat_dec_lt(v___x_4298_, v___x_4299_);
if (v___x_4300_ == 0)
{
lean_dec_ref(v_buckets_4296_);
return v___x_4297_;
}
else
{
size_t v___x_4301_; size_t v___x_4302_; lean_object* v___x_4303_; 
v___x_4301_ = ((size_t)0ULL);
v___x_4302_ = lean_usize_of_nat(v___x_4299_);
v___x_4303_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_getBuiltinAttributeNames_spec__1(v_buckets_4296_, v___x_4301_, v___x_4302_, v___x_4297_);
lean_dec_ref(v_buckets_4296_);
return v___x_4303_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getAttributeImpl(lean_object* v_env_4304_, lean_object* v_attrName_4305_){
_start:
{
lean_object* v___x_4306_; lean_object* v_toEnvExtension_4307_; lean_object* v_asyncMode_4308_; lean_object* v___x_4309_; lean_object* v___x_4310_; lean_object* v___x_4311_; lean_object* v_map_4312_; lean_object* v___x_4313_; 
v___x_4306_ = l_Lean_attributeExtension;
v_toEnvExtension_4307_ = lean_ctor_get(v___x_4306_, 0);
v_asyncMode_4308_ = lean_ctor_get(v_toEnvExtension_4307_, 2);
v___x_4309_ = l_Lean_instInhabitedAttributeExtensionState_default;
v___x_4310_ = lean_box(0);
v___x_4311_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_4309_, v___x_4306_, v_env_4304_, v_asyncMode_4308_, v___x_4310_);
v_map_4312_ = lean_ctor_get(v___x_4311_, 1);
lean_inc_ref(v_map_4312_);
lean_dec(v___x_4311_);
v___x_4313_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_mkAttributeImplOfEntry_spec__0___redArg(v_map_4312_, v_attrName_4305_);
lean_dec_ref(v_map_4312_);
if (lean_obj_tag(v___x_4313_) == 0)
{
lean_object* v___x_4314_; uint8_t v___x_4315_; lean_object* v___x_4316_; lean_object* v___x_4317_; lean_object* v___x_4318_; lean_object* v___x_4319_; lean_object* v___x_4320_; 
v___x_4314_ = ((lean_object*)(l_Lean_getBuiltinAttributeImpl___closed__0));
v___x_4315_ = 1;
v___x_4316_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_attrName_4305_, v___x_4315_);
v___x_4317_ = lean_string_append(v___x_4314_, v___x_4316_);
lean_dec_ref(v___x_4316_);
v___x_4318_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___redArg___closed__4));
v___x_4319_ = lean_string_append(v___x_4317_, v___x_4318_);
v___x_4320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4320_, 0, v___x_4319_);
return v___x_4320_;
}
else
{
lean_object* v_val_4321_; lean_object* v___x_4323_; uint8_t v_isShared_4324_; uint8_t v_isSharedCheck_4328_; 
lean_dec(v_attrName_4305_);
v_val_4321_ = lean_ctor_get(v___x_4313_, 0);
v_isSharedCheck_4328_ = !lean_is_exclusive(v___x_4313_);
if (v_isSharedCheck_4328_ == 0)
{
v___x_4323_ = v___x_4313_;
v_isShared_4324_ = v_isSharedCheck_4328_;
goto v_resetjp_4322_;
}
else
{
lean_inc(v_val_4321_);
lean_dec(v___x_4313_);
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
lean_ctor_set(v_reuseFailAlloc_4327_, 0, v_val_4321_);
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
LEAN_EXPORT lean_object* l_Lean_registerAttributeOfBuilder(lean_object* v_env_4329_, lean_object* v_builderId_4330_, lean_object* v_ref_4331_, lean_object* v_args_4332_){
_start:
{
lean_object* v_entry_4334_; lean_object* v___x_4335_; 
v_entry_4334_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_entry_4334_, 0, v_builderId_4330_);
lean_ctor_set(v_entry_4334_, 1, v_ref_4331_);
lean_ctor_set(v_entry_4334_, 2, v_args_4332_);
lean_inc_ref(v_entry_4334_);
v___x_4335_ = l_Lean_mkAttributeImplOfEntry(v_entry_4334_);
if (lean_obj_tag(v___x_4335_) == 0)
{
lean_object* v_a_4336_; lean_object* v___x_4338_; uint8_t v_isShared_4339_; uint8_t v_isSharedCheck_4361_; 
v_a_4336_ = lean_ctor_get(v___x_4335_, 0);
v_isSharedCheck_4361_ = !lean_is_exclusive(v___x_4335_);
if (v_isSharedCheck_4361_ == 0)
{
v___x_4338_ = v___x_4335_;
v_isShared_4339_ = v_isSharedCheck_4361_;
goto v_resetjp_4337_;
}
else
{
lean_inc(v_a_4336_);
lean_dec(v___x_4335_);
v___x_4338_ = lean_box(0);
v_isShared_4339_ = v_isSharedCheck_4361_;
goto v_resetjp_4337_;
}
v_resetjp_4337_:
{
lean_object* v_toAttributeImplCore_4340_; lean_object* v_name_4341_; uint8_t v___x_4342_; 
v_toAttributeImplCore_4340_ = lean_ctor_get(v_a_4336_, 0);
v_name_4341_ = lean_ctor_get(v_toAttributeImplCore_4340_, 1);
lean_inc_ref(v_env_4329_);
v___x_4342_ = l_Lean_isAttribute(v_env_4329_, v_name_4341_);
if (v___x_4342_ == 0)
{
lean_object* v___x_4343_; lean_object* v_toEnvExtension_4344_; lean_object* v_asyncMode_4345_; lean_object* v___x_4346_; lean_object* v___x_4347_; lean_object* v___x_4348_; lean_object* v___x_4350_; 
v___x_4343_ = l_Lean_attributeExtension;
v_toEnvExtension_4344_ = lean_ctor_get(v___x_4343_, 0);
v_asyncMode_4345_ = lean_ctor_get(v_toEnvExtension_4344_, 2);
v___x_4346_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4346_, 0, v_entry_4334_);
lean_ctor_set(v___x_4346_, 1, v_a_4336_);
v___x_4347_ = lean_box(0);
v___x_4348_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_4343_, v_env_4329_, v___x_4346_, v_asyncMode_4345_, v___x_4347_);
if (v_isShared_4339_ == 0)
{
lean_ctor_set(v___x_4338_, 0, v___x_4348_);
v___x_4350_ = v___x_4338_;
goto v_reusejp_4349_;
}
else
{
lean_object* v_reuseFailAlloc_4351_; 
v_reuseFailAlloc_4351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4351_, 0, v___x_4348_);
v___x_4350_ = v_reuseFailAlloc_4351_;
goto v_reusejp_4349_;
}
v_reusejp_4349_:
{
return v___x_4350_;
}
}
else
{
lean_object* v___x_4352_; lean_object* v___x_4353_; lean_object* v___x_4354_; lean_object* v___x_4355_; lean_object* v___x_4356_; lean_object* v___x_4357_; lean_object* v___x_4359_; 
lean_inc(v_name_4341_);
lean_dec(v_a_4336_);
lean_dec_ref_known(v_entry_4334_, 3);
lean_dec_ref(v_env_4329_);
v___x_4352_ = ((lean_object*)(l_Lean_registerBuiltinAttribute___closed__2));
v___x_4353_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_4341_, v___x_4342_);
v___x_4354_ = lean_string_append(v___x_4352_, v___x_4353_);
lean_dec_ref(v___x_4353_);
v___x_4355_ = ((lean_object*)(l_Lean_registerBuiltinAttribute___closed__3));
v___x_4356_ = lean_string_append(v___x_4354_, v___x_4355_);
v___x_4357_ = lean_mk_io_user_error(v___x_4356_);
if (v_isShared_4339_ == 0)
{
lean_ctor_set_tag(v___x_4338_, 1);
lean_ctor_set(v___x_4338_, 0, v___x_4357_);
v___x_4359_ = v___x_4338_;
goto v_reusejp_4358_;
}
else
{
lean_object* v_reuseFailAlloc_4360_; 
v_reuseFailAlloc_4360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4360_, 0, v___x_4357_);
v___x_4359_ = v_reuseFailAlloc_4360_;
goto v_reusejp_4358_;
}
v_reusejp_4358_:
{
return v___x_4359_;
}
}
}
}
else
{
lean_object* v_a_4362_; lean_object* v___x_4364_; uint8_t v_isShared_4365_; uint8_t v_isSharedCheck_4369_; 
lean_dec_ref_known(v_entry_4334_, 3);
lean_dec_ref(v_env_4329_);
v_a_4362_ = lean_ctor_get(v___x_4335_, 0);
v_isSharedCheck_4369_ = !lean_is_exclusive(v___x_4335_);
if (v_isSharedCheck_4369_ == 0)
{
v___x_4364_ = v___x_4335_;
v_isShared_4365_ = v_isSharedCheck_4369_;
goto v_resetjp_4363_;
}
else
{
lean_inc(v_a_4362_);
lean_dec(v___x_4335_);
v___x_4364_ = lean_box(0);
v_isShared_4365_ = v_isSharedCheck_4369_;
goto v_resetjp_4363_;
}
v_resetjp_4363_:
{
lean_object* v___x_4367_; 
if (v_isShared_4365_ == 0)
{
v___x_4367_ = v___x_4364_;
goto v_reusejp_4366_;
}
else
{
lean_object* v_reuseFailAlloc_4368_; 
v_reuseFailAlloc_4368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4368_, 0, v_a_4362_);
v___x_4367_ = v_reuseFailAlloc_4368_;
goto v_reusejp_4366_;
}
v_reusejp_4366_:
{
return v___x_4367_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerAttributeOfBuilder___boxed(lean_object* v_env_4370_, lean_object* v_builderId_4371_, lean_object* v_ref_4372_, lean_object* v_args_4373_, lean_object* v_a_4374_){
_start:
{
lean_object* v_res_4375_; 
v_res_4375_ = l_Lean_registerAttributeOfBuilder(v_env_4370_, v_builderId_4371_, v_ref_4372_, v_args_4373_);
return v_res_4375_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg(lean_object* v_x_4376_, lean_object* v___y_4377_, lean_object* v___y_4378_){
_start:
{
if (lean_obj_tag(v_x_4376_) == 0)
{
lean_object* v_a_4380_; lean_object* v___x_4381_; lean_object* v___x_4382_; 
v_a_4380_ = lean_ctor_get(v_x_4376_, 0);
lean_inc(v_a_4380_);
lean_dec_ref_known(v_x_4376_, 1);
v___x_4381_ = l_Lean_stringToMessageData(v_a_4380_);
v___x_4382_ = l_Lean_throwError___at___00Lean_instInhabitedAttributeImpl_default_spec__0___redArg(v___x_4381_, v___y_4377_, v___y_4378_);
return v___x_4382_;
}
else
{
lean_object* v_a_4383_; lean_object* v___x_4385_; uint8_t v_isShared_4386_; uint8_t v_isSharedCheck_4390_; 
v_a_4383_ = lean_ctor_get(v_x_4376_, 0);
v_isSharedCheck_4390_ = !lean_is_exclusive(v_x_4376_);
if (v_isSharedCheck_4390_ == 0)
{
v___x_4385_ = v_x_4376_;
v_isShared_4386_ = v_isSharedCheck_4390_;
goto v_resetjp_4384_;
}
else
{
lean_inc(v_a_4383_);
lean_dec(v_x_4376_);
v___x_4385_ = lean_box(0);
v_isShared_4386_ = v_isSharedCheck_4390_;
goto v_resetjp_4384_;
}
v_resetjp_4384_:
{
lean_object* v___x_4388_; 
if (v_isShared_4386_ == 0)
{
lean_ctor_set_tag(v___x_4385_, 0);
v___x_4388_ = v___x_4385_;
goto v_reusejp_4387_;
}
else
{
lean_object* v_reuseFailAlloc_4389_; 
v_reuseFailAlloc_4389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4389_, 0, v_a_4383_);
v___x_4388_ = v_reuseFailAlloc_4389_;
goto v_reusejp_4387_;
}
v_reusejp_4387_:
{
return v___x_4388_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg___boxed(lean_object* v_x_4391_, lean_object* v___y_4392_, lean_object* v___y_4393_, lean_object* v___y_4394_){
_start:
{
lean_object* v_res_4395_; 
v_res_4395_ = l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg(v_x_4391_, v___y_4392_, v___y_4393_);
lean_dec(v___y_4393_);
lean_dec_ref(v___y_4392_);
return v_res_4395_;
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_add(lean_object* v_declName_4396_, lean_object* v_attrName_4397_, lean_object* v_stx_4398_, uint8_t v_kind_4399_, lean_object* v_a_4400_, lean_object* v_a_4401_){
_start:
{
lean_object* v___x_4403_; lean_object* v_env_4404_; lean_object* v___x_4405_; lean_object* v___x_4406_; 
v___x_4403_ = lean_st_ref_get(v_a_4401_);
v_env_4404_ = lean_ctor_get(v___x_4403_, 0);
lean_inc_ref(v_env_4404_);
lean_dec(v___x_4403_);
v___x_4405_ = l_Lean_getAttributeImpl(v_env_4404_, v_attrName_4397_);
v___x_4406_ = l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg(v___x_4405_, v_a_4400_, v_a_4401_);
if (lean_obj_tag(v___x_4406_) == 0)
{
lean_object* v_a_4407_; lean_object* v_add_4408_; lean_object* v___x_4409_; lean_object* v___x_4410_; 
v_a_4407_ = lean_ctor_get(v___x_4406_, 0);
lean_inc(v_a_4407_);
lean_dec_ref_known(v___x_4406_, 1);
v_add_4408_ = lean_ctor_get(v_a_4407_, 1);
lean_inc_ref(v_add_4408_);
lean_dec(v_a_4407_);
v___x_4409_ = lean_box(v_kind_4399_);
lean_inc(v_a_4401_);
lean_inc_ref(v_a_4400_);
v___x_4410_ = lean_apply_6(v_add_4408_, v_declName_4396_, v_stx_4398_, v___x_4409_, v_a_4400_, v_a_4401_, lean_box(0));
return v___x_4410_;
}
else
{
lean_object* v_a_4411_; lean_object* v___x_4413_; uint8_t v_isShared_4414_; uint8_t v_isSharedCheck_4418_; 
lean_dec(v_stx_4398_);
lean_dec(v_declName_4396_);
v_a_4411_ = lean_ctor_get(v___x_4406_, 0);
v_isSharedCheck_4418_ = !lean_is_exclusive(v___x_4406_);
if (v_isSharedCheck_4418_ == 0)
{
v___x_4413_ = v___x_4406_;
v_isShared_4414_ = v_isSharedCheck_4418_;
goto v_resetjp_4412_;
}
else
{
lean_inc(v_a_4411_);
lean_dec(v___x_4406_);
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
LEAN_EXPORT lean_object* l_Lean_Attribute_add___boxed(lean_object* v_declName_4419_, lean_object* v_attrName_4420_, lean_object* v_stx_4421_, lean_object* v_kind_4422_, lean_object* v_a_4423_, lean_object* v_a_4424_, lean_object* v_a_4425_){
_start:
{
uint8_t v_kind_boxed_4426_; lean_object* v_res_4427_; 
v_kind_boxed_4426_ = lean_unbox(v_kind_4422_);
v_res_4427_ = l_Lean_Attribute_add(v_declName_4419_, v_attrName_4420_, v_stx_4421_, v_kind_boxed_4426_, v_a_4423_, v_a_4424_);
lean_dec(v_a_4424_);
lean_dec_ref(v_a_4423_);
return v_res_4427_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0(lean_object* v_00_u03b1_4428_, lean_object* v_x_4429_, lean_object* v___y_4430_, lean_object* v___y_4431_){
_start:
{
lean_object* v___x_4433_; 
v___x_4433_ = l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg(v_x_4429_, v___y_4430_, v___y_4431_);
return v___x_4433_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___boxed(lean_object* v_00_u03b1_4434_, lean_object* v_x_4435_, lean_object* v___y_4436_, lean_object* v___y_4437_, lean_object* v___y_4438_){
_start:
{
lean_object* v_res_4439_; 
v_res_4439_ = l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0(v_00_u03b1_4434_, v_x_4435_, v___y_4436_, v___y_4437_);
lean_dec(v___y_4437_);
lean_dec_ref(v___y_4436_);
return v_res_4439_;
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_erase(lean_object* v_declName_4440_, lean_object* v_attrName_4441_, lean_object* v_a_4442_, lean_object* v_a_4443_){
_start:
{
lean_object* v___x_4445_; lean_object* v_env_4446_; lean_object* v___x_4447_; lean_object* v___x_4448_; 
v___x_4445_ = lean_st_ref_get(v_a_4443_);
v_env_4446_ = lean_ctor_get(v___x_4445_, 0);
lean_inc_ref(v_env_4446_);
lean_dec(v___x_4445_);
v___x_4447_ = l_Lean_getAttributeImpl(v_env_4446_, v_attrName_4441_);
v___x_4448_ = l_Lean_ofExcept___at___00Lean_Attribute_add_spec__0___redArg(v___x_4447_, v_a_4442_, v_a_4443_);
if (lean_obj_tag(v___x_4448_) == 0)
{
lean_object* v_a_4449_; lean_object* v_erase_4450_; lean_object* v___x_4451_; 
v_a_4449_ = lean_ctor_get(v___x_4448_, 0);
lean_inc(v_a_4449_);
lean_dec_ref_known(v___x_4448_, 1);
v_erase_4450_ = lean_ctor_get(v_a_4449_, 2);
lean_inc_ref(v_erase_4450_);
lean_dec(v_a_4449_);
lean_inc(v_a_4443_);
lean_inc_ref(v_a_4442_);
v___x_4451_ = lean_apply_4(v_erase_4450_, v_declName_4440_, v_a_4442_, v_a_4443_, lean_box(0));
return v___x_4451_;
}
else
{
lean_object* v_a_4452_; lean_object* v___x_4454_; uint8_t v_isShared_4455_; uint8_t v_isSharedCheck_4459_; 
lean_dec(v_declName_4440_);
v_a_4452_ = lean_ctor_get(v___x_4448_, 0);
v_isSharedCheck_4459_ = !lean_is_exclusive(v___x_4448_);
if (v_isSharedCheck_4459_ == 0)
{
v___x_4454_ = v___x_4448_;
v_isShared_4455_ = v_isSharedCheck_4459_;
goto v_resetjp_4453_;
}
else
{
lean_inc(v_a_4452_);
lean_dec(v___x_4448_);
v___x_4454_ = lean_box(0);
v_isShared_4455_ = v_isSharedCheck_4459_;
goto v_resetjp_4453_;
}
v_resetjp_4453_:
{
lean_object* v___x_4457_; 
if (v_isShared_4455_ == 0)
{
v___x_4457_ = v___x_4454_;
goto v_reusejp_4456_;
}
else
{
lean_object* v_reuseFailAlloc_4458_; 
v_reuseFailAlloc_4458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4458_, 0, v_a_4452_);
v___x_4457_ = v_reuseFailAlloc_4458_;
goto v_reusejp_4456_;
}
v_reusejp_4456_:
{
return v___x_4457_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Attribute_erase___boxed(lean_object* v_declName_4460_, lean_object* v_attrName_4461_, lean_object* v_a_4462_, lean_object* v_a_4463_, lean_object* v_a_4464_){
_start:
{
lean_object* v_res_4465_; 
v_res_4465_ = l_Lean_Attribute_erase(v_declName_4460_, v_attrName_4461_, v_a_4462_, v_a_4463_);
lean_dec(v_a_4463_);
lean_dec_ref(v_a_4462_);
return v_res_4465_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_updateEnvAttributesImpl_spec__0(lean_object* v_x_4466_, lean_object* v_x_4467_){
_start:
{
if (lean_obj_tag(v_x_4467_) == 0)
{
return v_x_4466_;
}
else
{
lean_object* v_key_4468_; lean_object* v_value_4469_; lean_object* v_tail_4470_; lean_object* v_newEntries_4471_; lean_object* v_map_4472_; uint8_t v___x_4473_; 
v_key_4468_ = lean_ctor_get(v_x_4467_, 0);
lean_inc(v_key_4468_);
v_value_4469_ = lean_ctor_get(v_x_4467_, 1);
lean_inc(v_value_4469_);
v_tail_4470_ = lean_ctor_get(v_x_4467_, 2);
lean_inc(v_tail_4470_);
lean_dec_ref_known(v_x_4467_, 3);
v_newEntries_4471_ = lean_ctor_get(v_x_4466_, 0);
v_map_4472_ = lean_ctor_get(v_x_4466_, 1);
v___x_4473_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_registerBuiltinAttribute_spec__0___redArg(v_map_4472_, v_key_4468_);
if (v___x_4473_ == 0)
{
lean_object* v___x_4475_; uint8_t v_isShared_4476_; uint8_t v_isSharedCheck_4482_; 
lean_inc_ref(v_map_4472_);
lean_inc(v_newEntries_4471_);
v_isSharedCheck_4482_ = !lean_is_exclusive(v_x_4466_);
if (v_isSharedCheck_4482_ == 0)
{
lean_object* v_unused_4483_; lean_object* v_unused_4484_; 
v_unused_4483_ = lean_ctor_get(v_x_4466_, 1);
lean_dec(v_unused_4483_);
v_unused_4484_ = lean_ctor_get(v_x_4466_, 0);
lean_dec(v_unused_4484_);
v___x_4475_ = v_x_4466_;
v_isShared_4476_ = v_isSharedCheck_4482_;
goto v_resetjp_4474_;
}
else
{
lean_dec(v_x_4466_);
v___x_4475_ = lean_box(0);
v_isShared_4476_ = v_isSharedCheck_4482_;
goto v_resetjp_4474_;
}
v_resetjp_4474_:
{
lean_object* v___x_4477_; lean_object* v___x_4479_; 
v___x_4477_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_registerBuiltinAttribute_spec__1___redArg(v_map_4472_, v_key_4468_, v_value_4469_);
if (v_isShared_4476_ == 0)
{
lean_ctor_set(v___x_4475_, 1, v___x_4477_);
v___x_4479_ = v___x_4475_;
goto v_reusejp_4478_;
}
else
{
lean_object* v_reuseFailAlloc_4481_; 
v_reuseFailAlloc_4481_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4481_, 0, v_newEntries_4471_);
lean_ctor_set(v_reuseFailAlloc_4481_, 1, v___x_4477_);
v___x_4479_ = v_reuseFailAlloc_4481_;
goto v_reusejp_4478_;
}
v_reusejp_4478_:
{
v_x_4466_ = v___x_4479_;
v_x_4467_ = v_tail_4470_;
goto _start;
}
}
}
else
{
lean_dec(v_value_4469_);
lean_dec(v_key_4468_);
v_x_4467_ = v_tail_4470_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_updateEnvAttributesImpl_spec__1(lean_object* v_as_4486_, size_t v_i_4487_, size_t v_stop_4488_, lean_object* v_b_4489_){
_start:
{
uint8_t v___x_4490_; 
v___x_4490_ = lean_usize_dec_eq(v_i_4487_, v_stop_4488_);
if (v___x_4490_ == 0)
{
lean_object* v___x_4491_; lean_object* v___x_4492_; size_t v___x_4493_; size_t v___x_4494_; 
v___x_4491_ = lean_array_uget_borrowed(v_as_4486_, v_i_4487_);
lean_inc(v___x_4491_);
v___x_4492_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_updateEnvAttributesImpl_spec__0(v_b_4489_, v___x_4491_);
v___x_4493_ = ((size_t)1ULL);
v___x_4494_ = lean_usize_add(v_i_4487_, v___x_4493_);
v_i_4487_ = v___x_4494_;
v_b_4489_ = v___x_4492_;
goto _start;
}
else
{
return v_b_4489_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_updateEnvAttributesImpl_spec__1___boxed(lean_object* v_as_4496_, lean_object* v_i_4497_, lean_object* v_stop_4498_, lean_object* v_b_4499_){
_start:
{
size_t v_i_boxed_4500_; size_t v_stop_boxed_4501_; lean_object* v_res_4502_; 
v_i_boxed_4500_ = lean_unbox_usize(v_i_4497_);
lean_dec(v_i_4497_);
v_stop_boxed_4501_ = lean_unbox_usize(v_stop_4498_);
lean_dec(v_stop_4498_);
v_res_4502_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_updateEnvAttributesImpl_spec__1(v_as_4496_, v_i_boxed_4500_, v_stop_boxed_4501_, v_b_4499_);
lean_dec_ref(v_as_4496_);
return v_res_4502_;
}
}
LEAN_EXPORT lean_object* lean_update_env_attributes(lean_object* v_env_4503_){
_start:
{
lean_object* v___x_4505_; lean_object* v___x_4506_; lean_object* v___x_4507_; lean_object* v___y_4509_; lean_object* v_toEnvExtension_4512_; lean_object* v_asyncMode_4513_; lean_object* v_buckets_4514_; lean_object* v___x_4515_; lean_object* v___x_4516_; lean_object* v___x_4517_; lean_object* v___x_4518_; lean_object* v___x_4519_; uint8_t v___x_4520_; 
v___x_4505_ = l_Lean_attributeMapRef;
v___x_4506_ = lean_st_ref_get(v___x_4505_);
v___x_4507_ = l_Lean_attributeExtension;
v_toEnvExtension_4512_ = lean_ctor_get(v___x_4507_, 0);
v_asyncMode_4513_ = lean_ctor_get(v_toEnvExtension_4512_, 2);
v_buckets_4514_ = lean_ctor_get(v___x_4506_, 1);
lean_inc_ref(v_buckets_4514_);
lean_dec(v___x_4506_);
v___x_4515_ = l_Lean_instInhabitedAttributeExtensionState_default;
v___x_4516_ = lean_box(0);
lean_inc_ref(v_env_4503_);
v___x_4517_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_4515_, v___x_4507_, v_env_4503_, v_asyncMode_4513_, v___x_4516_);
v___x_4518_ = lean_unsigned_to_nat(0u);
v___x_4519_ = lean_array_get_size(v_buckets_4514_);
v___x_4520_ = lean_nat_dec_lt(v___x_4518_, v___x_4519_);
if (v___x_4520_ == 0)
{
lean_dec_ref(v_buckets_4514_);
v___y_4509_ = v___x_4517_;
goto v___jp_4508_;
}
else
{
size_t v___x_4521_; size_t v___x_4522_; lean_object* v___x_4523_; 
v___x_4521_ = ((size_t)0ULL);
v___x_4522_ = lean_usize_of_nat(v___x_4519_);
v___x_4523_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_updateEnvAttributesImpl_spec__1(v_buckets_4514_, v___x_4521_, v___x_4522_, v___x_4517_);
lean_dec_ref(v_buckets_4514_);
v___y_4509_ = v___x_4523_;
goto v___jp_4508_;
}
v___jp_4508_:
{
lean_object* v___x_4510_; lean_object* v___x_4511_; 
v___x_4510_ = l_Lean_PersistentEnvExtension_setState___redArg(v___x_4507_, v_env_4503_, v___y_4509_);
v___x_4511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4511_, 0, v___x_4510_);
return v___x_4511_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_updateEnvAttributesImpl___boxed(lean_object* v_env_4524_, lean_object* v_a_4525_){
_start:
{
lean_object* v_res_4526_; 
v_res_4526_ = lean_update_env_attributes(v_env_4524_);
return v_res_4526_;
}
}
LEAN_EXPORT lean_object* lean_get_num_attributes(){
_start:
{
lean_object* v___x_4528_; lean_object* v___x_4529_; lean_object* v_size_4530_; lean_object* v___x_4531_; 
v___x_4528_ = l_Lean_attributeMapRef;
v___x_4529_ = lean_st_ref_get(v___x_4528_);
v_size_4530_ = lean_ctor_get(v___x_4529_, 0);
lean_inc(v_size_4530_);
lean_dec(v___x_4529_);
v___x_4531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4531_, 0, v_size_4530_);
return v___x_4531_;
}
}
LEAN_EXPORT lean_object* l_Lean_getNumBuiltinAttributesImpl___boxed(lean_object* v_a_4532_){
_start:
{
lean_object* v_res_4533_; 
v_res_4533_ = lean_get_num_attributes();
return v_res_4533_;
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
