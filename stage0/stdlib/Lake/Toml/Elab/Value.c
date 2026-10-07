// Lean compiler output
// Module: Lake.Toml.Elab.Value
// Imports: public import Lake.Toml.Data.Value public import Lake.Toml.Grammar meta import all Lake.Toml.Grammar
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
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl___boxed(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_String_Slice_Pos_nextn(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_String_Slice_Pos_prevn(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_string_utf8_extract_fast(lean_object*, lean_object*, lean_object*);
uint32_t lean_uint32_of_nat(lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* lean_substring_tostring(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
uint8_t lean_string_utf8_at_end(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
uint32_t lean_uint32_sub(uint32_t, uint32_t);
lean_object* lean_uint32_to_nat(uint32_t);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_String_instInhabitedSlice;
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
uint8_t lean_string_is_valid_pos(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
lean_object* l_Substring_Raw_nextn(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_isLit_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
uint8_t l_Lake_Toml_RBDict_contains___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Toml_RBDict_push___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_pop(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lake_Toml_RBDict_findEntry_x3f___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_String_Slice_toString(lean_object*);
lean_object* l_String_Slice_subslice_x21(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Lake_Toml_DateTime_ofString_x3f(lean_object*);
lean_object* l_String_Slice_Pos_get_x3f(lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* l_Lean_Syntax_TSepArray_getElems___redArg(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Int_negOfNat(lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
double l_Float_ofScientific(lean_object*, uint8_t, lean_object*);
double lean_float_negate(double);
double lean_float_of_nat(lean_object*);
double lean_float_div(double, double);
lean_object* l_instMonadEIO___redArg();
lean_object* l_StateRefT_x27_instMonad___redArg(lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instMonadExceptOfExceptionCoreM;
extern lean_object* l_Lean_Core_instMonadRefCoreM;
extern lean_object* l_Lean_Core_instAddMessageContextCoreM;
lean_object* l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(lean_object*, lean_object*);
lean_object* l_Lean_throwErrorAt___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Toml_RBDict_empty___redArg();
lean_object* lean_string_append(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__0;
static lean_once_cell_t l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__1;
static const lean_closure_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__2 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__2_value;
static const lean_closure_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__3 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__3_value;
static const lean_string_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "ill-formed "};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__4 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__4_value;
static const lean_string_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = " syntax"};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__5 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__5_value;
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lake"};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__0 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__0_value;
static const lean_string_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Toml"};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__1 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__1_value;
static const lean_string_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "boolean"};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__2 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__2_value;
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__3_value_aux_0),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__1_value),LEAN_SCALAR_PTR_LITERAL(162, 254, 21, 174, 177, 224, 84, 229)}};
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__3_value_aux_1),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__2_value),LEAN_SCALAR_PTR_LITERAL(76, 74, 28, 167, 158, 175, 30, 0)}};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__3 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__3_value;
static const lean_string_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "invalid boolean"};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__4 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__4_value;
static lean_once_cell_t l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__5;
static const lean_string_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__6 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__6_value;
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__7_value_aux_0),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__1_value),LEAN_SCALAR_PTR_LITERAL(162, 254, 21, 174, 177, 224, 84, 229)}};
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__7_value_aux_1),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__6_value),LEAN_SCALAR_PTR_LITERAL(94, 186, 129, 3, 94, 77, 39, 82)}};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__7 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__7_value;
static const lean_string_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__8 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__8_value;
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__9_value_aux_0),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__1_value),LEAN_SCALAR_PTR_LITERAL(162, 254, 21, 174, 177, 224, 84, 229)}};
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__9_value_aux_1),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__8_value),LEAN_SCALAR_PTR_LITERAL(45, 94, 147, 128, 103, 18, 162, 55)}};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__9 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__9_value;
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeDecNum_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeDecNum_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeDecNum(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeDecNum___boxed(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeDecNum_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeDecNum_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeSign(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeDecInt(lean_object*);
static const lean_string_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "decInt"};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt___closed__0 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt___closed__0_value;
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt___closed__1_value_aux_0),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__1_value),LEAN_SCALAR_PTR_LITERAL(162, 254, 21, 174, 177, 224, 84, 229)}};
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt___closed__1_value_aux_1),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt___closed__0_value),LEAN_SCALAR_PTR_LITERAL(146, 5, 249, 175, 125, 238, 54, 100)}};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt___closed__1 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt___closed__1_value;
static const lean_string_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "ill-formed decimal integer syntax"};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt___closed__2 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt___closed__2_value;
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt___closed__2_value)}};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt___closed__3 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt___closed__3_value;
static lean_once_cell_t l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt___closed__4;
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeMantissa_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeMantissa_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeMantissa(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeMantissa___boxed(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeMantissa_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeMantissa_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_String_Slice_splitToSubslice___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__0___redArg___closed__0 = (const lean_object*)&l_String_Slice_splitToSubslice___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__0___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__0___redArg();
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__0___redArg___boxed(lean_object*);
static lean_once_cell_t l_String_Slice_splitToSubslice___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__0___closed__0;
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp___closed__0;
static lean_once_cell_t l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp___closed__1;
static const lean_array_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp___closed__2 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "inf"};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___closed__0 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___closed__0_value;
static const lean_string_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "nan"};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___closed__1 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___closed__1_value;
static lean_once_cell_t l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___closed__2;
LEAN_EXPORT double l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___boxed(lean_object*);
static const lean_string_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "float"};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat___closed__0 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat___closed__0_value;
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat___closed__1_value_aux_0),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__1_value),LEAN_SCALAR_PTR_LITERAL(162, 254, 21, 174, 177, 224, 84, 229)}};
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat___closed__1_value_aux_1),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat___closed__0_value),LEAN_SCALAR_PTR_LITERAL(104, 154, 151, 104, 68, 255, 246, 246)}};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat___closed__1 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat___closed__1_value;
static const lean_string_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "ill-formed float syntax"};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat___closed__2 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat___closed__2_value;
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat___closed__2_value)}};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat___closed__3 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat___closed__3_value;
static lean_once_cell_t l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat___closed__4;
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "binNum"};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum___closed__0 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum___closed__0_value;
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum___closed__1_value_aux_0),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__1_value),LEAN_SCALAR_PTR_LITERAL(162, 254, 21, 174, 177, 224, 84, 229)}};
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum___closed__1_value_aux_1),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum___closed__0_value),LEAN_SCALAR_PTR_LITERAL(59, 60, 170, 39, 77, 137, 193, 6)}};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum___closed__1 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum___closed__1_value;
static const lean_string_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "ill-formed binary number syntax"};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum___closed__2 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum___closed__2_value;
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum___closed__2_value)}};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum___closed__3 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum___closed__3_value;
static lean_once_cell_t l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum___closed__4;
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "octNum"};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum___closed__0 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum___closed__0_value;
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum___closed__1_value_aux_0),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__1_value),LEAN_SCALAR_PTR_LITERAL(162, 254, 21, 174, 177, 224, 84, 229)}};
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum___closed__1_value_aux_1),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum___closed__0_value),LEAN_SCALAR_PTR_LITERAL(93, 70, 221, 168, 145, 119, 144, 197)}};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum___closed__1 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum___closed__1_value;
static const lean_string_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "ill-formed octal number syntax"};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum___closed__2 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum___closed__2_value;
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum___closed__2_value)}};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum___closed__3 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum___closed__3_value;
static lean_once_cell_t l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum___closed__4;
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigit(uint32_t);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigit___boxed(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "hexNum"};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum___closed__0 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum___closed__0_value;
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum___closed__1_value_aux_0),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__1_value),LEAN_SCALAR_PTR_LITERAL(162, 254, 21, 174, 177, 224, 84, 229)}};
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum___closed__1_value_aux_1),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum___closed__0_value),LEAN_SCALAR_PTR_LITERAL(93, 174, 95, 211, 123, 63, 171, 252)}};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum___closed__1 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum___closed__1_value;
static const lean_string_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "ill-formed hexadecimal number syntax"};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum___closed__2 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum___closed__2_value;
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum___closed__2_value)}};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum___closed__3 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum___closed__3_value;
static lean_once_cell_t l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum___closed__4;
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "invalid date-time"};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__0 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__0_value;
static lean_once_cell_t l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__1;
static const lean_string_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "dateTime"};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__2 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__2_value;
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__3_value_aux_0),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__1_value),LEAN_SCALAR_PTR_LITERAL(162, 254, 21, 174, 177, 224, 84, 229)}};
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__3_value_aux_1),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__2_value),LEAN_SCALAR_PTR_LITERAL(100, 234, 1, 129, 172, 254, 231, 202)}};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__3 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__3_value;
static const lean_string_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "ill-formed date-time syntax"};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__4 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__4_value;
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__4_value)}};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__5 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__5_value;
static lean_once_cell_t l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__6;
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "literalString"};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString___closed__0 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString___closed__0_value;
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString___closed__1_value_aux_0),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__1_value),LEAN_SCALAR_PTR_LITERAL(162, 254, 21, 174, 177, 224, 84, 229)}};
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString___closed__1_value_aux_1),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString___closed__0_value),LEAN_SCALAR_PTR_LITERAL(241, 168, 165, 209, 230, 255, 154, 83)}};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString___closed__1 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString___closed__1_value;
static const lean_string_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "ill-formed literalString syntax"};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString___closed__2 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString___closed__2_value;
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString___closed__2_value)}};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString___closed__3 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString___closed__3_value;
static lean_once_cell_t l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString___closed__4;
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Init.Data.Option.BasicAux"};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits___closed__0 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits___closed__0_value;
static const lean_string_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Option.get!"};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits___closed__1 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits___closed__1_value;
static const lean_string_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "value is none"};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits___closed__2 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits___closed__2_value;
static lean_once_cell_t l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits___closed__3;
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "invalid unicode escape `"};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__0 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__0_value;
static lean_once_cell_t l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__1;
static const lean_string_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__2 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__2_value;
static lean_once_cell_t l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__3;
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__0 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__0_value;
static const lean_string_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "basicString"};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__1 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__1_value;
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__2_value_aux_0),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__1_value),LEAN_SCALAR_PTR_LITERAL(162, 254, 21, 174, 177, 224, 84, 229)}};
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__2_value_aux_1),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__1_value),LEAN_SCALAR_PTR_LITERAL(164, 34, 208, 112, 75, 114, 213, 233)}};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__2 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__2_value;
static const lean_string_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "ill-formed basic string syntax"};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__3 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__3_value;
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__3_value)}};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__4 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__4_value;
static lean_once_cell_t l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__5;
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_dropInitialNewline(lean_object*);
static const lean_string_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "mlLiteralString"};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString___closed__0 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString___closed__0_value;
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString___closed__1_value_aux_0),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__1_value),LEAN_SCALAR_PTR_LITERAL(162, 254, 21, 174, 177, 224, 84, 229)}};
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString___closed__1_value_aux_1),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString___closed__0_value),LEAN_SCALAR_PTR_LITERAL(249, 215, 18, 247, 52, 33, 2, 54)}};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString___closed__1 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString___closed__1_value;
static const lean_string_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = "ill-formed multi-line literal string syntax"};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString___closed__2 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString___closed__2_value;
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString___closed__2_value)}};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString___closed__3 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString___closed__3_value;
static lean_once_cell_t l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString___closed__4;
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "mlBasicString"};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString___closed__0 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString___closed__0_value;
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString___closed__1_value_aux_0),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__1_value),LEAN_SCALAR_PTR_LITERAL(162, 254, 21, 174, 177, 224, 84, 229)}};
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString___closed__1_value_aux_1),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString___closed__0_value),LEAN_SCALAR_PTR_LITERAL(205, 27, 188, 79, 217, 46, 221, 25)}};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString___closed__1 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString___closed__1_value;
static const lean_string_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "ill-formed multi-line basic string syntax"};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString___closed__2 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString___closed__2_value;
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString___closed__2_value)}};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString___closed__3 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString___closed__3_value;
static lean_once_cell_t l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString___closed__4;
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "string"};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString___closed__0 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString___closed__0_value;
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString___closed__1_value_aux_0),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__1_value),LEAN_SCALAR_PTR_LITERAL(162, 254, 21, 174, 177, 224, 84, 229)}};
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString___closed__1_value_aux_1),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString___closed__0_value),LEAN_SCALAR_PTR_LITERAL(79, 134, 223, 178, 21, 25, 142, 203)}};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString___closed__1 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString___closed__1_value;
static const lean_string_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "ill-formed string syntax"};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString___closed__2 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString___closed__2_value;
static lean_once_cell_t l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString___closed__3;
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "unquotedKey"};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__0 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__0_value;
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__1_value_aux_0),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__1_value),LEAN_SCALAR_PTR_LITERAL(162, 254, 21, 174, 177, 224, 84, 229)}};
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__1_value_aux_1),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__0_value),LEAN_SCALAR_PTR_LITERAL(56, 43, 232, 206, 44, 188, 39, 241)}};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__1 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__1_value;
static const lean_string_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "ill-formed unquoted key syntax"};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__2 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__2_value;
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__2_value)}};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__3 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__3_value;
static lean_once_cell_t l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__4;
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_Toml_elabSimpleKey___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "simpleKey"};
static const lean_object* l_Lake_Toml_elabSimpleKey___closed__0 = (const lean_object*)&l_Lake_Toml_elabSimpleKey___closed__0_value;
static const lean_ctor_object l_Lake_Toml_elabSimpleKey___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_Toml_elabSimpleKey___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Toml_elabSimpleKey___closed__1_value_aux_0),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__1_value),LEAN_SCALAR_PTR_LITERAL(162, 254, 21, 174, 177, 224, 84, 229)}};
static const lean_ctor_object l_Lake_Toml_elabSimpleKey___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Toml_elabSimpleKey___closed__1_value_aux_1),((lean_object*)&l_Lake_Toml_elabSimpleKey___closed__0_value),LEAN_SCALAR_PTR_LITERAL(187, 51, 117, 190, 121, 223, 170, 220)}};
static const lean_object* l_Lake_Toml_elabSimpleKey___closed__1 = (const lean_object*)&l_Lake_Toml_elabSimpleKey___closed__1_value;
static const lean_string_object l_Lake_Toml_elabSimpleKey___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "ill-formed simple key syntax"};
static const lean_object* l_Lake_Toml_elabSimpleKey___closed__2 = (const lean_object*)&l_Lake_Toml_elabSimpleKey___closed__2_value;
static lean_once_cell_t l_Lake_Toml_elabSimpleKey___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_elabSimpleKey___closed__3;
LEAN_EXPORT lean_object* l_Lake_Toml_elabSimpleKey(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_elabSimpleKey___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "array"};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg___closed__0 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg___closed__0_value;
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg___closed__1_value_aux_0),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__1_value),LEAN_SCALAR_PTR_LITERAL(162, 254, 21, 174, 177, 224, 84, 229)}};
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg___closed__1_value_aux_1),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 212, 239, 77, 14, 34, 57, 134)}};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg___closed__1 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg___closed__1_value;
static const lean_string_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "ill-formed array syntax"};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg___closed__2 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg___closed__2_value;
static lean_once_cell_t l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg___closed__3;
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "cannot redefine key `"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___closed__1_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___closed__2;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2(lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__3(uint8_t, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "keyval"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__1_value_aux_0),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__1_value),LEAN_SCALAR_PTR_LITERAL(162, 254, 21, 174, 177, 224, 84, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__1_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__0_value),LEAN_SCALAR_PTR_LITERAL(105, 46, 78, 232, 161, 211, 209, 25)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "ill-formed key-value pair syntax"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__2_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__3;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "key"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__4_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__5_value_aux_0),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__1_value),LEAN_SCALAR_PTR_LITERAL(162, 254, 21, 174, 177, 224, 84, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__5_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__4_value),LEAN_SCALAR_PTR_LITERAL(44, 24, 166, 18, 184, 133, 165, 53)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__5_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "ill-formed key syntax"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__6_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__7;
static const lean_array_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__8 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__8_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__4(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "inlineTable"};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__0 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__0_value;
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__1_value_aux_0),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__1_value),LEAN_SCALAR_PTR_LITERAL(162, 254, 21, 174, 177, 224, 84, 229)}};
static const lean_ctor_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__1_value_aux_1),((lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__0_value),LEAN_SCALAR_PTR_LITERAL(160, 125, 46, 131, 161, 142, 50, 23)}};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__1 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__1_value;
static const lean_string_object l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "ill-formed inline table syntax"};
static const lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__2 = (const lean_object*)&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__2_value;
static lean_once_cell_t l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__3;
static lean_once_cell_t l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__4;
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_Toml_elabVal___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "ill-formed value syntax"};
static const lean_object* l_Lake_Toml_elabVal___closed__0 = (const lean_object*)&l_Lake_Toml_elabVal___closed__0_value;
static lean_once_cell_t l_Lake_Toml_elabVal___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_elabVal___closed__1;
LEAN_EXPORT lean_object* l_Lake_Toml_elabVal___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_elabVal(lean_object*, lean_object*, lean_object*);
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__0(void){
_start:
{
lean_object* v___x_1_; 
v___x_1_ = l_instMonadEIO___redArg();
return v___x_1_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__1(void){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__0, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__0_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__0);
v___x_3_ = l_StateRefT_x27_instMonad___redArg(v___x_2_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit(lean_object* v_k_8_, lean_object* v_x_9_, lean_object* v_name_10_, lean_object* v_a_11_, lean_object* v_a_12_){
_start:
{
lean_object* v___x_14_; lean_object* v_toApplicative_15_; lean_object* v_toFunctor_16_; lean_object* v_toSeq_17_; lean_object* v_toSeqLeft_18_; lean_object* v_toSeqRight_19_; lean_object* v___f_20_; lean_object* v___f_21_; lean_object* v___f_22_; lean_object* v___f_23_; lean_object* v___x_24_; lean_object* v___f_25_; lean_object* v___f_26_; lean_object* v___f_27_; lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; 
v___x_14_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__1, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__1_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__1);
v_toApplicative_15_ = lean_ctor_get(v___x_14_, 0);
v_toFunctor_16_ = lean_ctor_get(v_toApplicative_15_, 0);
v_toSeq_17_ = lean_ctor_get(v_toApplicative_15_, 2);
v_toSeqLeft_18_ = lean_ctor_get(v_toApplicative_15_, 3);
v_toSeqRight_19_ = lean_ctor_get(v_toApplicative_15_, 4);
v___f_20_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__2));
v___f_21_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__3));
lean_inc_ref_n(v_toFunctor_16_, 2);
v___f_22_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_22_, 0, v_toFunctor_16_);
v___f_23_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_23_, 0, v_toFunctor_16_);
v___x_24_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_24_, 0, v___f_22_);
lean_ctor_set(v___x_24_, 1, v___f_23_);
lean_inc(v_toSeqRight_19_);
v___f_25_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_25_, 0, v_toSeqRight_19_);
lean_inc(v_toSeqLeft_18_);
v___f_26_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_26_, 0, v_toSeqLeft_18_);
lean_inc(v_toSeq_17_);
v___f_27_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_27_, 0, v_toSeq_17_);
v___x_28_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_28_, 0, v___x_24_);
lean_ctor_set(v___x_28_, 1, v___f_20_);
lean_ctor_set(v___x_28_, 2, v___f_27_);
lean_ctor_set(v___x_28_, 3, v___f_26_);
lean_ctor_set(v___x_28_, 4, v___f_25_);
v___x_29_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_29_, 0, v___x_28_);
lean_ctor_set(v___x_29_, 1, v___f_21_);
v___x_30_ = l_Lean_instMonadExceptOfExceptionCoreM;
v___x_31_ = l_Lean_Core_instMonadRefCoreM;
v___x_32_ = l_Lean_Core_instAddMessageContextCoreM;
lean_inc_ref(v___x_29_);
v___x_33_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(v___x_32_, v___x_29_);
v___x_34_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_34_, 0, v___x_30_);
lean_ctor_set(v___x_34_, 1, v___x_31_);
lean_ctor_set(v___x_34_, 2, v___x_33_);
v___x_35_ = l_Lean_Syntax_isLit_x3f(v_k_8_, v_x_9_);
if (lean_obj_tag(v___x_35_) == 1)
{
lean_object* v_val_36_; lean_object* v___x_38_; uint8_t v_isShared_39_; uint8_t v_isSharedCheck_43_; 
lean_dec_ref_known(v___x_34_, 3);
lean_dec_ref_known(v___x_29_, 2);
lean_dec(v_x_9_);
v_val_36_ = lean_ctor_get(v___x_35_, 0);
v_isSharedCheck_43_ = !lean_is_exclusive(v___x_35_);
if (v_isSharedCheck_43_ == 0)
{
v___x_38_ = v___x_35_;
v_isShared_39_ = v_isSharedCheck_43_;
goto v_resetjp_37_;
}
else
{
lean_inc(v_val_36_);
lean_dec(v___x_35_);
v___x_38_ = lean_box(0);
v_isShared_39_ = v_isSharedCheck_43_;
goto v_resetjp_37_;
}
v_resetjp_37_:
{
lean_object* v___x_41_; 
if (v_isShared_39_ == 0)
{
lean_ctor_set_tag(v___x_38_, 0);
v___x_41_ = v___x_38_;
goto v_reusejp_40_;
}
else
{
lean_object* v_reuseFailAlloc_42_; 
v_reuseFailAlloc_42_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_42_, 0, v_val_36_);
v___x_41_ = v_reuseFailAlloc_42_;
goto v_reusejp_40_;
}
v_reusejp_40_:
{
return v___x_41_;
}
}
}
else
{
lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_194__overap_50_; lean_object* v___x_51_; 
lean_dec(v___x_35_);
v___x_44_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__4));
v___x_45_ = lean_string_append(v___x_44_, v_name_10_);
v___x_46_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__5));
v___x_47_ = lean_string_append(v___x_45_, v___x_46_);
v___x_48_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_48_, 0, v___x_47_);
v___x_49_ = l_Lean_MessageData_ofFormat(v___x_48_);
v___x_194__overap_50_ = l_Lean_throwErrorAt___redArg(v___x_29_, v___x_34_, v_x_9_, v___x_49_);
lean_inc(v_a_12_);
lean_inc_ref(v_a_11_);
v___x_51_ = lean_apply_3(v___x_194__overap_50_, v_a_11_, v_a_12_, lean_box(0));
return v___x_51_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___boxed(lean_object* v_k_52_, lean_object* v_x_53_, lean_object* v_name_54_, lean_object* v_a_55_, lean_object* v_a_56_, lean_object* v_a_57_){
_start:
{
lean_object* v_res_58_; 
v_res_58_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit(v_k_52_, v_x_53_, v_name_54_, v_a_55_, v_a_56_);
lean_dec(v_a_56_);
lean_dec_ref(v_a_55_);
lean_dec_ref(v_name_54_);
lean_dec(v_k_52_);
return v_res_58_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__0(void){
_start:
{
lean_object* v___x_59_; 
v___x_59_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_59_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__1(void){
_start:
{
lean_object* v___x_60_; lean_object* v___x_61_; 
v___x_60_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__0);
v___x_61_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_61_, 0, v___x_60_);
return v___x_61_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__2(void){
_start:
{
lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; 
v___x_62_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_63_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__1);
v___x_64_ = lean_unsigned_to_nat(0u);
v___x_65_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_65_, 0, v___x_64_);
lean_ctor_set(v___x_65_, 1, v___x_64_);
lean_ctor_set(v___x_65_, 2, v___x_64_);
lean_ctor_set(v___x_65_, 3, v___x_64_);
lean_ctor_set(v___x_65_, 4, v___x_63_);
lean_ctor_set(v___x_65_, 5, v___x_63_);
lean_ctor_set(v___x_65_, 6, v___x_63_);
lean_ctor_set(v___x_65_, 7, v___x_63_);
lean_ctor_set(v___x_65_, 8, v___x_63_);
lean_ctor_set(v___x_65_, 9, v___x_63_);
lean_ctor_set(v___x_65_, 10, v___x_63_);
lean_ctor_set(v___x_65_, 11, v___x_62_);
return v___x_65_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__3(void){
_start:
{
lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; 
v___x_66_ = lean_unsigned_to_nat(32u);
v___x_67_ = lean_mk_empty_array_with_capacity(v___x_66_);
v___x_68_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_68_, 0, v___x_67_);
return v___x_68_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__4(void){
_start:
{
size_t v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; 
v___x_69_ = ((size_t)5ULL);
v___x_70_ = lean_unsigned_to_nat(0u);
v___x_71_ = lean_unsigned_to_nat(32u);
v___x_72_ = lean_mk_empty_array_with_capacity(v___x_71_);
v___x_73_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__3);
v___x_74_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_74_, 0, v___x_73_);
lean_ctor_set(v___x_74_, 1, v___x_72_);
lean_ctor_set(v___x_74_, 2, v___x_70_);
lean_ctor_set(v___x_74_, 3, v___x_70_);
lean_ctor_set_usize(v___x_74_, 4, v___x_69_);
return v___x_74_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__5(void){
_start:
{
lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; 
v___x_75_ = lean_box(1);
v___x_76_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__4);
v___x_77_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__1);
v___x_78_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_78_, 0, v___x_77_);
lean_ctor_set(v___x_78_, 1, v___x_76_);
lean_ctor_set(v___x_78_, 2, v___x_75_);
return v___x_78_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1(lean_object* v_msgData_79_, lean_object* v___y_80_, lean_object* v___y_81_){
_start:
{
lean_object* v___x_83_; lean_object* v_toCold_84_; lean_object* v_env_85_; lean_object* v_options_86_; uint8_t v___x_87_; lean_object* v_env_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; 
v___x_83_ = lean_st_ref_get(v___y_81_);
v_toCold_84_ = lean_ctor_get(v___y_80_, 0);
v_env_85_ = lean_ctor_get(v___x_83_, 0);
lean_inc_ref(v_env_85_);
lean_dec(v___x_83_);
v_options_86_ = lean_ctor_get(v_toCold_84_, 2);
v___x_87_ = 0;
v_env_88_ = l_Lean_Environment_setRecordingDeps(v_env_85_, v___x_87_);
v___x_89_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__2);
v___x_90_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___closed__5);
lean_inc_ref(v_options_86_);
v___x_91_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_91_, 0, v_env_88_);
lean_ctor_set(v___x_91_, 1, v___x_89_);
lean_ctor_set(v___x_91_, 2, v___x_90_);
lean_ctor_set(v___x_91_, 3, v_options_86_);
v___x_92_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_92_, 0, v___x_91_);
lean_ctor_set(v___x_92_, 1, v_msgData_79_);
v___x_93_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_93_, 0, v___x_92_);
return v___x_93_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1___boxed(lean_object* v_msgData_94_, lean_object* v___y_95_, lean_object* v___y_96_, lean_object* v___y_97_){
_start:
{
lean_object* v_res_98_; 
v_res_98_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1(v_msgData_94_, v___y_95_, v___y_96_);
lean_dec(v___y_96_);
lean_dec_ref(v___y_95_);
return v_res_98_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0___redArg(lean_object* v_msg_99_, lean_object* v___y_100_, lean_object* v___y_101_){
_start:
{
lean_object* v_ref_103_; lean_object* v___x_104_; lean_object* v_a_105_; lean_object* v___x_107_; uint8_t v_isShared_108_; uint8_t v_isSharedCheck_113_; 
v_ref_103_ = lean_ctor_get(v___y_100_, 2);
v___x_104_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1(v_msg_99_, v___y_100_, v___y_101_);
v_a_105_ = lean_ctor_get(v___x_104_, 0);
v_isSharedCheck_113_ = !lean_is_exclusive(v___x_104_);
if (v_isSharedCheck_113_ == 0)
{
v___x_107_ = v___x_104_;
v_isShared_108_ = v_isSharedCheck_113_;
goto v_resetjp_106_;
}
else
{
lean_inc(v_a_105_);
lean_dec(v___x_104_);
v___x_107_ = lean_box(0);
v_isShared_108_ = v_isSharedCheck_113_;
goto v_resetjp_106_;
}
v_resetjp_106_:
{
lean_object* v___x_109_; lean_object* v___x_111_; 
lean_inc(v_ref_103_);
v___x_109_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_109_, 0, v_ref_103_);
lean_ctor_set(v___x_109_, 1, v_a_105_);
if (v_isShared_108_ == 0)
{
lean_ctor_set_tag(v___x_107_, 1);
lean_ctor_set(v___x_107_, 0, v___x_109_);
v___x_111_ = v___x_107_;
goto v_reusejp_110_;
}
else
{
lean_object* v_reuseFailAlloc_112_; 
v_reuseFailAlloc_112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_112_, 0, v___x_109_);
v___x_111_ = v_reuseFailAlloc_112_;
goto v_reusejp_110_;
}
v_reusejp_110_:
{
return v___x_111_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0___redArg___boxed(lean_object* v_msg_114_, lean_object* v___y_115_, lean_object* v___y_116_, lean_object* v___y_117_){
_start:
{
lean_object* v_res_118_; 
v_res_118_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0___redArg(v_msg_114_, v___y_115_, v___y_116_);
lean_dec(v___y_116_);
lean_dec_ref(v___y_115_);
return v_res_118_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(lean_object* v_ref_119_, lean_object* v_msg_120_, lean_object* v___y_121_, lean_object* v___y_122_){
_start:
{
lean_object* v_toCold_124_; lean_object* v_currRecDepth_125_; lean_object* v_ref_126_; uint16_t v_optionFlags_127_; uint8_t v_suppressElabErrors_128_; uint8_t v_isRecordingDeps_129_; lean_object* v_ref_130_; lean_object* v___x_131_; lean_object* v___x_132_; 
v_toCold_124_ = lean_ctor_get(v___y_121_, 0);
v_currRecDepth_125_ = lean_ctor_get(v___y_121_, 1);
v_ref_126_ = lean_ctor_get(v___y_121_, 2);
v_optionFlags_127_ = lean_ctor_get_uint16(v___y_121_, sizeof(void*)*3);
v_suppressElabErrors_128_ = lean_ctor_get_uint8(v___y_121_, sizeof(void*)*3 + 2);
v_isRecordingDeps_129_ = lean_ctor_get_uint8(v___y_121_, sizeof(void*)*3 + 3);
v_ref_130_ = l_Lean_replaceRef(v_ref_119_, v_ref_126_);
lean_inc(v_currRecDepth_125_);
lean_inc_ref(v_toCold_124_);
v___x_131_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_131_, 0, v_toCold_124_);
lean_ctor_set(v___x_131_, 1, v_currRecDepth_125_);
lean_ctor_set(v___x_131_, 2, v_ref_130_);
lean_ctor_set_uint16(v___x_131_, sizeof(void*)*3, v_optionFlags_127_);
lean_ctor_set_uint8(v___x_131_, sizeof(void*)*3 + 2, v_suppressElabErrors_128_);
lean_ctor_set_uint8(v___x_131_, sizeof(void*)*3 + 3, v_isRecordingDeps_129_);
v___x_132_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0___redArg(v_msg_120_, v___x_131_, v___y_122_);
lean_dec_ref_known(v___x_131_, 3);
return v___x_132_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg___boxed(lean_object* v_ref_133_, lean_object* v_msg_134_, lean_object* v___y_135_, lean_object* v___y_136_, lean_object* v___y_137_){
_start:
{
lean_object* v_res_138_; 
v_res_138_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_ref_133_, v_msg_134_, v___y_135_, v___y_136_);
lean_dec(v___y_136_);
lean_dec_ref(v___y_135_);
lean_dec(v_ref_133_);
return v_res_138_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__5(void){
_start:
{
lean_object* v___x_147_; lean_object* v___x_148_; 
v___x_147_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__4));
v___x_148_ = l_Lean_stringToMessageData(v___x_147_);
return v___x_148_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean(lean_object* v_x_159_, lean_object* v_a_160_, lean_object* v_a_161_){
_start:
{
lean_object* v___x_163_; uint8_t v___x_164_; 
v___x_163_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__3));
lean_inc(v_x_159_);
v___x_164_ = l_Lean_Syntax_isOfKind(v_x_159_, v___x_163_);
if (v___x_164_ == 0)
{
lean_object* v___x_165_; lean_object* v___x_166_; 
v___x_165_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__5, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__5_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__5);
v___x_166_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_x_159_, v___x_165_, v_a_160_, v_a_161_);
lean_dec(v_x_159_);
return v___x_166_;
}
else
{
lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; uint8_t v___x_170_; 
v___x_167_ = lean_unsigned_to_nat(0u);
v___x_168_ = l_Lean_Syntax_getArg(v_x_159_, v___x_167_);
v___x_169_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__7));
lean_inc(v___x_168_);
v___x_170_ = l_Lean_Syntax_isOfKind(v___x_168_, v___x_169_);
if (v___x_170_ == 0)
{
lean_object* v___x_171_; uint8_t v___x_172_; 
v___x_171_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__9));
v___x_172_ = l_Lean_Syntax_isOfKind(v___x_168_, v___x_171_);
if (v___x_172_ == 0)
{
lean_object* v___x_173_; lean_object* v___x_174_; 
v___x_173_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__5, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__5_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__5);
v___x_174_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_x_159_, v___x_173_, v_a_160_, v_a_161_);
lean_dec(v_x_159_);
return v___x_174_;
}
else
{
lean_object* v___x_175_; lean_object* v___x_176_; 
lean_dec(v_x_159_);
v___x_175_ = lean_box(v___x_170_);
v___x_176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_176_, 0, v___x_175_);
return v___x_176_;
}
}
else
{
lean_object* v___x_177_; lean_object* v___x_178_; 
lean_dec(v___x_168_);
lean_dec(v_x_159_);
v___x_177_ = lean_box(v___x_170_);
v___x_178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_178_, 0, v___x_177_);
return v___x_178_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___boxed(lean_object* v_x_179_, lean_object* v_a_180_, lean_object* v_a_181_, lean_object* v_a_182_){
_start:
{
lean_object* v_res_183_; 
v_res_183_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean(v_x_179_, v_a_180_, v_a_181_);
lean_dec(v_a_181_);
lean_dec_ref(v_a_180_);
return v_res_183_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0(lean_object* v_00_u03b1_184_, lean_object* v_ref_185_, lean_object* v_msg_186_, lean_object* v___y_187_, lean_object* v___y_188_){
_start:
{
lean_object* v___x_190_; 
v___x_190_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_ref_185_, v_msg_186_, v___y_187_, v___y_188_);
return v___x_190_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___boxed(lean_object* v_00_u03b1_191_, lean_object* v_ref_192_, lean_object* v_msg_193_, lean_object* v___y_194_, lean_object* v___y_195_, lean_object* v___y_196_){
_start:
{
lean_object* v_res_197_; 
v_res_197_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0(v_00_u03b1_191_, v_ref_192_, v_msg_193_, v___y_194_, v___y_195_);
lean_dec(v___y_195_);
lean_dec_ref(v___y_194_);
lean_dec(v_ref_192_);
return v_res_197_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0(lean_object* v_00_u03b1_198_, lean_object* v_msg_199_, lean_object* v___y_200_, lean_object* v___y_201_){
_start:
{
lean_object* v___x_203_; 
v___x_203_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0___redArg(v_msg_199_, v___y_200_, v___y_201_);
return v___x_203_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0___boxed(lean_object* v_00_u03b1_204_, lean_object* v_msg_205_, lean_object* v___y_206_, lean_object* v___y_207_, lean_object* v___y_208_){
_start:
{
lean_object* v_res_209_; 
v_res_209_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0(v_00_u03b1_204_, v_msg_205_, v___y_206_, v___y_207_);
lean_dec(v___y_207_);
lean_dec_ref(v___y_206_);
return v_res_209_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeDecNum_spec__0___redArg(lean_object* v___x_210_, lean_object* v_s_211_, lean_object* v_a_212_, lean_object* v_b_213_){
_start:
{
uint8_t v_decide_214_; 
v_decide_214_ = lean_nat_dec_eq(v_a_212_, v___x_210_);
if (v_decide_214_ == 0)
{
uint32_t v___x_215_; lean_object* v___x_216_; uint32_t v___x_217_; uint8_t v___x_218_; 
v___x_215_ = lean_string_utf8_get_fast(v_s_211_, v_a_212_);
v___x_216_ = lean_string_utf8_next_fast(v_s_211_, v_a_212_);
lean_dec(v_a_212_);
v___x_217_ = 95;
v___x_218_ = lean_uint32_dec_eq(v___x_215_, v___x_217_);
if (v___x_218_ == 0)
{
lean_object* v___x_219_; lean_object* v___x_220_; uint32_t v___x_221_; uint32_t v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; 
v___x_219_ = lean_unsigned_to_nat(10u);
v___x_220_ = lean_nat_mul(v_b_213_, v___x_219_);
lean_dec(v_b_213_);
v___x_221_ = 48;
v___x_222_ = lean_uint32_sub(v___x_215_, v___x_221_);
v___x_223_ = lean_uint32_to_nat(v___x_222_);
v___x_224_ = lean_nat_add(v___x_220_, v___x_223_);
lean_dec(v___x_223_);
lean_dec(v___x_220_);
v_a_212_ = v___x_216_;
v_b_213_ = v___x_224_;
goto _start;
}
else
{
v_a_212_ = v___x_216_;
goto _start;
}
}
else
{
lean_dec(v_a_212_);
return v_b_213_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeDecNum_spec__0___redArg___boxed(lean_object* v___x_227_, lean_object* v_s_228_, lean_object* v_a_229_, lean_object* v_b_230_){
_start:
{
lean_object* v_res_231_; 
v_res_231_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeDecNum_spec__0___redArg(v___x_227_, v_s_228_, v_a_229_, v_b_230_);
lean_dec_ref(v_s_228_);
lean_dec(v___x_227_);
return v_res_231_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeDecNum(lean_object* v_s_232_){
_start:
{
lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; 
v___x_233_ = lean_unsigned_to_nat(0u);
v___x_234_ = lean_string_utf8_byte_size(v_s_232_);
v___x_235_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeDecNum_spec__0___redArg(v___x_234_, v_s_232_, v___x_233_, v___x_233_);
return v___x_235_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeDecNum___boxed(lean_object* v_s_236_){
_start:
{
lean_object* v_res_237_; 
v_res_237_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeDecNum(v_s_236_);
lean_dec_ref(v_s_236_);
return v_res_237_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeDecNum_spec__0(lean_object* v___x_238_, lean_object* v___x_239_, lean_object* v_s_240_, lean_object* v_inst_241_, lean_object* v_R_242_, lean_object* v_a_243_, lean_object* v_b_244_, lean_object* v_c_245_){
_start:
{
lean_object* v___x_246_; 
v___x_246_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeDecNum_spec__0___redArg(v___x_239_, v_s_240_, v_a_243_, v_b_244_);
return v___x_246_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeDecNum_spec__0___boxed(lean_object* v___x_247_, lean_object* v___x_248_, lean_object* v_s_249_, lean_object* v_inst_250_, lean_object* v_R_251_, lean_object* v_a_252_, lean_object* v_b_253_, lean_object* v_c_254_){
_start:
{
lean_object* v_res_255_; 
v_res_255_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeDecNum_spec__0(v___x_247_, v___x_248_, v_s_249_, v_inst_250_, v_R_251_, v_a_252_, v_b_253_, v_c_254_);
lean_dec_ref(v_s_249_);
lean_dec(v___x_248_);
lean_dec_ref(v___x_247_);
return v_res_255_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeSign(lean_object* v_s_256_){
_start:
{
uint32_t v___y_258_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; 
v___x_281_ = lean_unsigned_to_nat(0u);
v___x_282_ = lean_string_utf8_byte_size(v_s_256_);
lean_inc_ref(v_s_256_);
v___x_283_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_283_, 0, v_s_256_);
lean_ctor_set(v___x_283_, 1, v___x_281_);
lean_ctor_set(v___x_283_, 2, v___x_282_);
v___x_284_ = l_String_Slice_Pos_get_x3f(v___x_283_, v___x_281_);
lean_dec_ref_known(v___x_283_, 3);
if (lean_obj_tag(v___x_284_) == 0)
{
uint32_t v___x_285_; 
v___x_285_ = 65;
v___y_258_ = v___x_285_;
goto v___jp_257_;
}
else
{
lean_object* v_val_286_; uint32_t v___x_287_; 
v_val_286_ = lean_ctor_get(v___x_284_, 0);
lean_inc(v_val_286_);
lean_dec_ref_known(v___x_284_, 1);
v___x_287_ = lean_unbox_uint32(v_val_286_);
lean_dec(v_val_286_);
v___y_258_ = v___x_287_;
goto v___jp_257_;
}
v___jp_257_:
{
uint32_t v___x_259_; uint8_t v___x_260_; 
v___x_259_ = 45;
v___x_260_ = lean_uint32_dec_eq(v___y_258_, v___x_259_);
if (v___x_260_ == 0)
{
uint32_t v___x_261_; uint8_t v___x_262_; 
v___x_261_ = 43;
v___x_262_ = lean_uint32_dec_eq(v___y_258_, v___x_261_);
if (v___x_262_ == 0)
{
lean_object* v___x_263_; lean_object* v___x_264_; 
v___x_263_ = lean_box(v___x_262_);
v___x_264_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_264_, 0, v___x_263_);
lean_ctor_set(v___x_264_, 1, v_s_256_);
return v___x_264_;
}
else
{
lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; 
v___x_265_ = lean_unsigned_to_nat(1u);
v___x_266_ = lean_unsigned_to_nat(0u);
v___x_267_ = lean_string_utf8_byte_size(v_s_256_);
lean_inc_ref(v_s_256_);
v___x_268_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_268_, 0, v_s_256_);
lean_ctor_set(v___x_268_, 1, v___x_266_);
lean_ctor_set(v___x_268_, 2, v___x_267_);
v___x_269_ = l_String_Slice_Pos_nextn(v___x_268_, v___x_266_, v___x_265_);
lean_dec_ref_known(v___x_268_, 3);
v___x_270_ = lean_string_utf8_extract_fast(v_s_256_, v___x_269_, v___x_267_);
lean_dec(v___x_269_);
lean_dec_ref(v_s_256_);
v___x_271_ = lean_box(v___x_260_);
v___x_272_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_272_, 0, v___x_271_);
lean_ctor_set(v___x_272_, 1, v___x_270_);
return v___x_272_;
}
}
else
{
lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; 
v___x_273_ = lean_unsigned_to_nat(1u);
v___x_274_ = lean_unsigned_to_nat(0u);
v___x_275_ = lean_string_utf8_byte_size(v_s_256_);
lean_inc_ref(v_s_256_);
v___x_276_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_276_, 0, v_s_256_);
lean_ctor_set(v___x_276_, 1, v___x_274_);
lean_ctor_set(v___x_276_, 2, v___x_275_);
v___x_277_ = l_String_Slice_Pos_nextn(v___x_276_, v___x_274_, v___x_273_);
lean_dec_ref_known(v___x_276_, 3);
v___x_278_ = lean_string_utf8_extract_fast(v_s_256_, v___x_277_, v___x_275_);
lean_dec(v___x_277_);
lean_dec_ref(v_s_256_);
v___x_279_ = lean_box(v___x_260_);
v___x_280_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_280_, 0, v___x_279_);
lean_ctor_set(v___x_280_, 1, v___x_278_);
return v___x_280_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeDecInt(lean_object* v_s_288_){
_start:
{
lean_object* v_snd_290_; uint32_t v___y_294_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; 
v___x_313_ = lean_unsigned_to_nat(0u);
v___x_314_ = lean_string_utf8_byte_size(v_s_288_);
lean_inc_ref(v_s_288_);
v___x_315_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_315_, 0, v_s_288_);
lean_ctor_set(v___x_315_, 1, v___x_313_);
lean_ctor_set(v___x_315_, 2, v___x_314_);
v___x_316_ = l_String_Slice_Pos_get_x3f(v___x_315_, v___x_313_);
lean_dec_ref_known(v___x_315_, 3);
if (lean_obj_tag(v___x_316_) == 0)
{
uint32_t v___x_317_; 
v___x_317_ = 65;
v___y_294_ = v___x_317_;
goto v___jp_293_;
}
else
{
lean_object* v_val_318_; uint32_t v___x_319_; 
v_val_318_ = lean_ctor_get(v___x_316_, 0);
lean_inc(v_val_318_);
lean_dec_ref_known(v___x_316_, 1);
v___x_319_ = lean_unbox_uint32(v_val_318_);
lean_dec(v_val_318_);
v___y_294_ = v___x_319_;
goto v___jp_293_;
}
v___jp_289_:
{
lean_object* v___x_291_; lean_object* v___x_292_; 
v___x_291_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeDecNum(v_snd_290_);
lean_dec_ref(v_snd_290_);
v___x_292_ = lean_nat_to_int(v___x_291_);
return v___x_292_;
}
v___jp_293_:
{
uint32_t v___x_295_; uint8_t v___x_296_; 
v___x_295_ = 45;
v___x_296_ = lean_uint32_dec_eq(v___y_294_, v___x_295_);
if (v___x_296_ == 0)
{
uint32_t v___x_297_; uint8_t v___x_298_; 
v___x_297_ = 43;
v___x_298_ = lean_uint32_dec_eq(v___y_294_, v___x_297_);
if (v___x_298_ == 0)
{
v_snd_290_ = v_s_288_;
goto v___jp_289_;
}
else
{
lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; 
v___x_299_ = lean_unsigned_to_nat(1u);
v___x_300_ = lean_unsigned_to_nat(0u);
v___x_301_ = lean_string_utf8_byte_size(v_s_288_);
lean_inc_ref(v_s_288_);
v___x_302_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_302_, 0, v_s_288_);
lean_ctor_set(v___x_302_, 1, v___x_300_);
lean_ctor_set(v___x_302_, 2, v___x_301_);
v___x_303_ = l_String_Slice_Pos_nextn(v___x_302_, v___x_300_, v___x_299_);
lean_dec_ref_known(v___x_302_, 3);
v___x_304_ = lean_string_utf8_extract_fast(v_s_288_, v___x_303_, v___x_301_);
lean_dec(v___x_303_);
lean_dec_ref(v_s_288_);
v_snd_290_ = v___x_304_;
goto v___jp_289_;
}
}
else
{
lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; 
v___x_305_ = lean_unsigned_to_nat(1u);
v___x_306_ = lean_unsigned_to_nat(0u);
v___x_307_ = lean_string_utf8_byte_size(v_s_288_);
lean_inc_ref(v_s_288_);
v___x_308_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_308_, 0, v_s_288_);
lean_ctor_set(v___x_308_, 1, v___x_306_);
lean_ctor_set(v___x_308_, 2, v___x_307_);
v___x_309_ = l_String_Slice_Pos_nextn(v___x_308_, v___x_306_, v___x_305_);
lean_dec_ref_known(v___x_308_, 3);
v___x_310_ = lean_string_utf8_extract_fast(v_s_288_, v___x_309_, v___x_307_);
lean_dec(v___x_309_);
lean_dec_ref(v_s_288_);
v___x_311_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeDecNum(v___x_310_);
lean_dec_ref(v___x_310_);
v___x_312_ = l_Int_negOfNat(v___x_311_);
lean_dec(v___x_311_);
return v___x_312_;
}
}
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt___closed__4(void){
_start:
{
lean_object* v___x_328_; lean_object* v___x_329_; 
v___x_328_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt___closed__3));
v___x_329_ = l_Lean_MessageData_ofFormat(v___x_328_);
return v___x_329_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt(lean_object* v_x_330_, lean_object* v_a_331_, lean_object* v_a_332_){
_start:
{
lean_object* v_a_335_; lean_object* v___x_338_; lean_object* v___x_339_; 
v___x_338_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt___closed__1));
v___x_339_ = l_Lean_Syntax_isLit_x3f(v___x_338_, v_x_330_);
if (lean_obj_tag(v___x_339_) == 1)
{
lean_object* v_val_340_; 
v_val_340_ = lean_ctor_get(v___x_339_, 0);
lean_inc(v_val_340_);
lean_dec_ref_known(v___x_339_, 1);
v_a_335_ = v_val_340_;
goto v___jp_334_;
}
else
{
lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v_a_343_; lean_object* v___x_345_; uint8_t v_isShared_346_; uint8_t v_isSharedCheck_350_; 
lean_dec(v___x_339_);
v___x_341_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt___closed__4, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt___closed__4_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt___closed__4);
v___x_342_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_x_330_, v___x_341_, v_a_331_, v_a_332_);
v_a_343_ = lean_ctor_get(v___x_342_, 0);
v_isSharedCheck_350_ = !lean_is_exclusive(v___x_342_);
if (v_isSharedCheck_350_ == 0)
{
v___x_345_ = v___x_342_;
v_isShared_346_ = v_isSharedCheck_350_;
goto v_resetjp_344_;
}
else
{
lean_inc(v_a_343_);
lean_dec(v___x_342_);
v___x_345_ = lean_box(0);
v_isShared_346_ = v_isSharedCheck_350_;
goto v_resetjp_344_;
}
v_resetjp_344_:
{
lean_object* v___x_348_; 
if (v_isShared_346_ == 0)
{
v___x_348_ = v___x_345_;
goto v_reusejp_347_;
}
else
{
lean_object* v_reuseFailAlloc_349_; 
v_reuseFailAlloc_349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_349_, 0, v_a_343_);
v___x_348_ = v_reuseFailAlloc_349_;
goto v_reusejp_347_;
}
v_reusejp_347_:
{
return v___x_348_;
}
}
}
v___jp_334_:
{
lean_object* v___x_336_; lean_object* v___x_337_; 
v___x_336_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeDecInt(v_a_335_);
v___x_337_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_337_, 0, v___x_336_);
return v___x_337_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt___boxed(lean_object* v_x_351_, lean_object* v_a_352_, lean_object* v_a_353_, lean_object* v_a_354_){
_start:
{
lean_object* v_res_355_; 
v_res_355_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt(v_x_351_, v_a_352_, v_a_353_);
lean_dec(v_a_353_);
lean_dec_ref(v_a_352_);
lean_dec(v_x_351_);
return v_res_355_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeMantissa_spec__0___redArg(lean_object* v___x_356_, lean_object* v_s_357_, lean_object* v_a_358_, lean_object* v_b_359_){
_start:
{
uint8_t v_decide_360_; 
v_decide_360_ = lean_nat_dec_eq(v_a_358_, v___x_356_);
if (v_decide_360_ == 0)
{
lean_object* v_fst_361_; lean_object* v_snd_362_; uint32_t v___x_363_; lean_object* v___x_364_; uint32_t v___x_365_; uint8_t v___x_366_; 
v_fst_361_ = lean_ctor_get(v_b_359_, 0);
v_snd_362_ = lean_ctor_get(v_b_359_, 1);
v___x_363_ = lean_string_utf8_get_fast(v_s_357_, v_a_358_);
v___x_364_ = lean_string_utf8_next_fast(v_s_357_, v_a_358_);
lean_dec(v_a_358_);
v___x_365_ = 95;
v___x_366_ = lean_uint32_dec_eq(v___x_363_, v___x_365_);
if (v___x_366_ == 0)
{
lean_object* v___x_368_; uint8_t v_isShared_369_; uint8_t v_isSharedCheck_389_; 
lean_inc(v_snd_362_);
lean_inc(v_fst_361_);
v_isSharedCheck_389_ = !lean_is_exclusive(v_b_359_);
if (v_isSharedCheck_389_ == 0)
{
lean_object* v_unused_390_; lean_object* v_unused_391_; 
v_unused_390_ = lean_ctor_get(v_b_359_, 1);
lean_dec(v_unused_390_);
v_unused_391_ = lean_ctor_get(v_b_359_, 0);
lean_dec(v_unused_391_);
v___x_368_ = v_b_359_;
v_isShared_369_ = v_isSharedCheck_389_;
goto v_resetjp_367_;
}
else
{
lean_dec(v_b_359_);
v___x_368_ = lean_box(0);
v_isShared_369_ = v_isSharedCheck_389_;
goto v_resetjp_367_;
}
v_resetjp_367_:
{
uint32_t v___x_370_; uint8_t v___x_371_; 
v___x_370_ = 46;
v___x_371_ = lean_uint32_dec_eq(v___x_363_, v___x_370_);
if (v___x_371_ == 0)
{
lean_object* v___x_372_; lean_object* v___x_373_; uint32_t v___x_374_; uint32_t v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_381_; 
v___x_372_ = lean_unsigned_to_nat(10u);
v___x_373_ = lean_nat_mul(v_fst_361_, v___x_372_);
lean_dec(v_fst_361_);
v___x_374_ = 48;
v___x_375_ = lean_uint32_sub(v___x_363_, v___x_374_);
v___x_376_ = lean_uint32_to_nat(v___x_375_);
v___x_377_ = lean_nat_add(v___x_373_, v___x_376_);
lean_dec(v___x_376_);
lean_dec(v___x_373_);
v___x_378_ = lean_unsigned_to_nat(1u);
v___x_379_ = lean_nat_add(v_snd_362_, v___x_378_);
lean_dec(v_snd_362_);
if (v_isShared_369_ == 0)
{
lean_ctor_set(v___x_368_, 1, v___x_379_);
lean_ctor_set(v___x_368_, 0, v___x_377_);
v___x_381_ = v___x_368_;
goto v_reusejp_380_;
}
else
{
lean_object* v_reuseFailAlloc_383_; 
v_reuseFailAlloc_383_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_383_, 0, v___x_377_);
lean_ctor_set(v_reuseFailAlloc_383_, 1, v___x_379_);
v___x_381_ = v_reuseFailAlloc_383_;
goto v_reusejp_380_;
}
v_reusejp_380_:
{
v_a_358_ = v___x_364_;
v_b_359_ = v___x_381_;
goto _start;
}
}
else
{
lean_object* v___x_384_; lean_object* v___x_386_; 
lean_dec(v_snd_362_);
v___x_384_ = lean_unsigned_to_nat(0u);
if (v_isShared_369_ == 0)
{
lean_ctor_set(v___x_368_, 1, v___x_384_);
v___x_386_ = v___x_368_;
goto v_reusejp_385_;
}
else
{
lean_object* v_reuseFailAlloc_388_; 
v_reuseFailAlloc_388_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_388_, 0, v_fst_361_);
lean_ctor_set(v_reuseFailAlloc_388_, 1, v___x_384_);
v___x_386_ = v_reuseFailAlloc_388_;
goto v_reusejp_385_;
}
v_reusejp_385_:
{
v_a_358_ = v___x_364_;
v_b_359_ = v___x_386_;
goto _start;
}
}
}
}
else
{
v_a_358_ = v___x_364_;
goto _start;
}
}
else
{
lean_dec(v_a_358_);
return v_b_359_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeMantissa_spec__0___redArg___boxed(lean_object* v___x_393_, lean_object* v_s_394_, lean_object* v_a_395_, lean_object* v_b_396_){
_start:
{
lean_object* v_res_397_; 
v_res_397_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeMantissa_spec__0___redArg(v___x_393_, v_s_394_, v_a_395_, v_b_396_);
lean_dec_ref(v_s_394_);
lean_dec(v___x_393_);
return v_res_397_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeMantissa(lean_object* v_s_398_){
_start:
{
lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v_fst_403_; lean_object* v_snd_404_; lean_object* v___x_405_; uint8_t v___x_406_; 
v___x_399_ = lean_unsigned_to_nat(0u);
v___x_400_ = lean_string_utf8_byte_size(v_s_398_);
v___x_401_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_401_, 0, v___x_399_);
lean_ctor_set(v___x_401_, 1, v___x_400_);
v___x_402_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeMantissa_spec__0___redArg(v___x_400_, v_s_398_, v___x_399_, v___x_401_);
v_fst_403_ = lean_ctor_get(v___x_402_, 0);
v_snd_404_ = lean_ctor_get(v___x_402_, 1);
v___x_405_ = lean_string_length(v_s_398_);
v___x_406_ = lean_nat_dec_le(v___x_405_, v_snd_404_);
if (v___x_406_ == 0)
{
return v___x_402_;
}
else
{
lean_object* v___x_408_; uint8_t v_isShared_409_; uint8_t v_isSharedCheck_413_; 
lean_inc(v_fst_403_);
v_isSharedCheck_413_ = !lean_is_exclusive(v___x_402_);
if (v_isSharedCheck_413_ == 0)
{
lean_object* v_unused_414_; lean_object* v_unused_415_; 
v_unused_414_ = lean_ctor_get(v___x_402_, 1);
lean_dec(v_unused_414_);
v_unused_415_ = lean_ctor_get(v___x_402_, 0);
lean_dec(v_unused_415_);
v___x_408_ = v___x_402_;
v_isShared_409_ = v_isSharedCheck_413_;
goto v_resetjp_407_;
}
else
{
lean_dec(v___x_402_);
v___x_408_ = lean_box(0);
v_isShared_409_ = v_isSharedCheck_413_;
goto v_resetjp_407_;
}
v_resetjp_407_:
{
lean_object* v___x_411_; 
if (v_isShared_409_ == 0)
{
lean_ctor_set(v___x_408_, 1, v___x_399_);
v___x_411_ = v___x_408_;
goto v_reusejp_410_;
}
else
{
lean_object* v_reuseFailAlloc_412_; 
v_reuseFailAlloc_412_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_412_, 0, v_fst_403_);
lean_ctor_set(v_reuseFailAlloc_412_, 1, v___x_399_);
v___x_411_ = v_reuseFailAlloc_412_;
goto v_reusejp_410_;
}
v_reusejp_410_:
{
return v___x_411_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeMantissa___boxed(lean_object* v_s_416_){
_start:
{
lean_object* v_res_417_; 
v_res_417_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeMantissa(v_s_416_);
lean_dec_ref(v_s_416_);
return v_res_417_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeMantissa_spec__0(lean_object* v___x_418_, lean_object* v___x_419_, lean_object* v_s_420_, lean_object* v_inst_421_, lean_object* v_R_422_, lean_object* v_a_423_, lean_object* v_b_424_, lean_object* v_c_425_){
_start:
{
lean_object* v___x_426_; 
v___x_426_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeMantissa_spec__0___redArg(v___x_419_, v_s_420_, v_a_423_, v_b_424_);
return v___x_426_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeMantissa_spec__0___boxed(lean_object* v___x_427_, lean_object* v___x_428_, lean_object* v_s_429_, lean_object* v_inst_430_, lean_object* v_R_431_, lean_object* v_a_432_, lean_object* v_b_433_, lean_object* v_c_434_){
_start:
{
lean_object* v_res_435_; 
v_res_435_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeMantissa_spec__0(v___x_427_, v___x_428_, v_s_429_, v_inst_430_, v_R_431_, v_a_432_, v_b_433_, v_c_434_);
lean_dec_ref(v_s_429_);
lean_dec(v___x_428_);
lean_dec_ref(v___x_427_);
return v_res_435_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__0___redArg(){
_start:
{
lean_object* v___x_439_; 
v___x_439_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__0___redArg___closed__0));
return v___x_439_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__0___redArg___boxed(lean_object* v___dummy_440_){
_start:
{
lean_object* v_res_441_; 
v_res_441_ = l_String_Slice_splitToSubslice___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__0___redArg();
return v_res_441_;
}
}
static lean_object* _init_l_String_Slice_splitToSubslice___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__0___closed__0(void){
_start:
{
lean_object* v___x_442_; 
v___x_442_ = l_String_Slice_splitToSubslice___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__0___redArg();
return v___x_442_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__0(lean_object* v_s_443_){
_start:
{
lean_object* v___x_444_; 
v___x_444_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__0___closed__0);
return v___x_444_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__0___boxed(lean_object* v_s_445_){
_start:
{
lean_object* v_res_446_; 
v_res_446_ = l_String_Slice_splitToSubslice___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__0(v_s_445_);
lean_dec_ref(v_s_445_);
return v_res_446_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__1___redArg(lean_object* v_s_447_, lean_object* v___x_448_, lean_object* v___x_449_, lean_object* v_a_450_, lean_object* v_b_451_){
_start:
{
lean_object* v_it_453_; lean_object* v_startInclusive_454_; lean_object* v_endExclusive_455_; 
if (lean_obj_tag(v_a_450_) == 0)
{
lean_object* v_currPos_460_; lean_object* v_searcher_461_; lean_object* v___x_463_; uint8_t v_isShared_464_; uint8_t v_isSharedCheck_488_; 
v_currPos_460_ = lean_ctor_get(v_a_450_, 0);
v_searcher_461_ = lean_ctor_get(v_a_450_, 1);
v_isSharedCheck_488_ = !lean_is_exclusive(v_a_450_);
if (v_isSharedCheck_488_ == 0)
{
v___x_463_ = v_a_450_;
v_isShared_464_ = v_isSharedCheck_488_;
goto v_resetjp_462_;
}
else
{
lean_inc(v_searcher_461_);
lean_inc(v_currPos_460_);
lean_dec(v_a_450_);
v___x_463_ = lean_box(0);
v_isShared_464_ = v_isSharedCheck_488_;
goto v_resetjp_462_;
}
v_resetjp_462_:
{
uint8_t v___y_466_; uint8_t v_decide_481_; 
v_decide_481_ = lean_nat_dec_eq(v_searcher_461_, v___x_449_);
if (v_decide_481_ == 0)
{
uint32_t v___x_482_; uint32_t v___x_483_; uint8_t v___x_484_; 
v___x_482_ = lean_string_utf8_get_fast(v_s_447_, v_searcher_461_);
v___x_483_ = 69;
v___x_484_ = lean_uint32_dec_eq(v___x_482_, v___x_483_);
if (v___x_484_ == 0)
{
uint32_t v___x_485_; uint8_t v___x_486_; 
v___x_485_ = 101;
v___x_486_ = lean_uint32_dec_eq(v___x_482_, v___x_485_);
v___y_466_ = v___x_486_;
goto v___jp_465_;
}
else
{
v___y_466_ = v___x_484_;
goto v___jp_465_;
}
}
else
{
lean_object* v___x_487_; 
lean_del_object(v___x_463_);
lean_dec(v_searcher_461_);
v___x_487_ = lean_box(1);
lean_inc(v___x_449_);
v_it_453_ = v___x_487_;
v_startInclusive_454_ = v_currPos_460_;
v_endExclusive_455_ = v___x_449_;
goto v___jp_452_;
}
v___jp_465_:
{
if (v___y_466_ == 0)
{
lean_object* v___x_467_; lean_object* v___x_469_; 
v___x_467_ = lean_string_utf8_next_fast(v_s_447_, v_searcher_461_);
lean_dec(v_searcher_461_);
if (v_isShared_464_ == 0)
{
lean_ctor_set(v___x_463_, 1, v___x_467_);
v___x_469_ = v___x_463_;
goto v_reusejp_468_;
}
else
{
lean_object* v_reuseFailAlloc_471_; 
v_reuseFailAlloc_471_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_471_, 0, v_currPos_460_);
lean_ctor_set(v_reuseFailAlloc_471_, 1, v___x_467_);
v___x_469_ = v_reuseFailAlloc_471_;
goto v_reusejp_468_;
}
v_reusejp_468_:
{
v_a_450_ = v___x_469_;
goto _start;
}
}
else
{
lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v_slice_475_; lean_object* v_nextIt_477_; 
v___x_472_ = lean_string_utf8_next_fast(v_s_447_, v_searcher_461_);
v___x_473_ = lean_nat_sub(v___x_472_, v_searcher_461_);
v___x_474_ = lean_nat_add(v_searcher_461_, v___x_473_);
lean_dec(v___x_473_);
v_slice_475_ = l_String_Slice_subslice_x21(v___x_448_, v_currPos_460_, v_searcher_461_);
lean_inc(v___x_474_);
if (v_isShared_464_ == 0)
{
lean_ctor_set(v___x_463_, 1, v___x_474_);
lean_ctor_set(v___x_463_, 0, v___x_474_);
v_nextIt_477_ = v___x_463_;
goto v_reusejp_476_;
}
else
{
lean_object* v_reuseFailAlloc_480_; 
v_reuseFailAlloc_480_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_480_, 0, v___x_474_);
lean_ctor_set(v_reuseFailAlloc_480_, 1, v___x_474_);
v_nextIt_477_ = v_reuseFailAlloc_480_;
goto v_reusejp_476_;
}
v_reusejp_476_:
{
lean_object* v_startInclusive_478_; lean_object* v_endExclusive_479_; 
v_startInclusive_478_ = lean_ctor_get(v_slice_475_, 0);
lean_inc(v_startInclusive_478_);
v_endExclusive_479_ = lean_ctor_get(v_slice_475_, 1);
lean_inc(v_endExclusive_479_);
lean_dec_ref(v_slice_475_);
v_it_453_ = v_nextIt_477_;
v_startInclusive_454_ = v_startInclusive_478_;
v_endExclusive_455_ = v_endExclusive_479_;
goto v___jp_452_;
}
}
}
}
}
else
{
lean_dec(v___x_449_);
lean_dec_ref(v_s_447_);
return v_b_451_;
}
v___jp_452_:
{
lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; 
lean_inc_ref(v_s_447_);
v___x_456_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_456_, 0, v_s_447_);
lean_ctor_set(v___x_456_, 1, v_startInclusive_454_);
lean_ctor_set(v___x_456_, 2, v_endExclusive_455_);
v___x_457_ = l_String_Slice_toString(v___x_456_);
lean_dec_ref_known(v___x_456_, 3);
v___x_458_ = lean_array_push(v_b_451_, v___x_457_);
v_a_450_ = v_it_453_;
v_b_451_ = v___x_458_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__1___redArg___boxed(lean_object* v_s_489_, lean_object* v___x_490_, lean_object* v___x_491_, lean_object* v_a_492_, lean_object* v_b_493_){
_start:
{
lean_object* v_res_494_; 
v_res_494_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__1___redArg(v_s_489_, v___x_490_, v___x_491_, v_a_492_, v_b_493_);
lean_dec_ref(v___x_490_);
return v_res_494_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp___closed__0(void){
_start:
{
lean_object* v___x_495_; lean_object* v___x_496_; 
v___x_495_ = lean_unsigned_to_nat(0u);
v___x_496_ = lean_nat_to_int(v___x_495_);
return v___x_496_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp___closed__1(void){
_start:
{
lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; 
v___x_497_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp___closed__0, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp___closed__0_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp___closed__0);
v___x_498_ = lean_unsigned_to_nat(0u);
v___x_499_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_499_, 0, v___x_498_);
lean_ctor_set(v___x_499_, 1, v___x_497_);
return v___x_499_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp(lean_object* v_s_502_){
_start:
{
lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; 
v___x_505_ = lean_unsigned_to_nat(0u);
v___x_506_ = lean_string_utf8_byte_size(v_s_502_);
lean_inc_ref(v_s_502_);
v___x_507_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_507_, 0, v_s_502_);
lean_ctor_set(v___x_507_, 1, v___x_505_);
lean_ctor_set(v___x_507_, 2, v___x_506_);
v___x_508_ = lean_obj_once(&l_String_Slice_splitToSubslice___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__0___closed__0, &l_String_Slice_splitToSubslice___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__0___closed__0_once, _init_l_String_Slice_splitToSubslice___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__0___closed__0);
v___x_509_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp___closed__2));
v___x_510_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__1___redArg(v_s_502_, v___x_507_, v___x_506_, v___x_508_, v___x_509_);
lean_dec_ref_known(v___x_507_, 3);
v___x_511_ = lean_array_to_list(v___x_510_);
if (lean_obj_tag(v___x_511_) == 1)
{
lean_object* v_tail_512_; 
v_tail_512_ = lean_ctor_get(v___x_511_, 1);
if (lean_obj_tag(v_tail_512_) == 0)
{
lean_object* v_head_513_; lean_object* v___x_514_; lean_object* v_fst_515_; lean_object* v_snd_516_; lean_object* v___x_518_; uint8_t v_isShared_519_; uint8_t v_isSharedCheck_524_; 
v_head_513_ = lean_ctor_get(v___x_511_, 0);
lean_inc(v_head_513_);
lean_dec_ref_known(v___x_511_, 2);
v___x_514_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeMantissa(v_head_513_);
lean_dec(v_head_513_);
v_fst_515_ = lean_ctor_get(v___x_514_, 0);
v_snd_516_ = lean_ctor_get(v___x_514_, 1);
v_isSharedCheck_524_ = !lean_is_exclusive(v___x_514_);
if (v_isSharedCheck_524_ == 0)
{
v___x_518_ = v___x_514_;
v_isShared_519_ = v_isSharedCheck_524_;
goto v_resetjp_517_;
}
else
{
lean_inc(v_snd_516_);
lean_inc(v_fst_515_);
lean_dec(v___x_514_);
v___x_518_ = lean_box(0);
v_isShared_519_ = v_isSharedCheck_524_;
goto v_resetjp_517_;
}
v_resetjp_517_:
{
lean_object* v___x_520_; lean_object* v___x_522_; 
v___x_520_ = l_Int_negOfNat(v_snd_516_);
lean_dec(v_snd_516_);
if (v_isShared_519_ == 0)
{
lean_ctor_set(v___x_518_, 1, v___x_520_);
v___x_522_ = v___x_518_;
goto v_reusejp_521_;
}
else
{
lean_object* v_reuseFailAlloc_523_; 
v_reuseFailAlloc_523_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_523_, 0, v_fst_515_);
lean_ctor_set(v_reuseFailAlloc_523_, 1, v___x_520_);
v___x_522_ = v_reuseFailAlloc_523_;
goto v_reusejp_521_;
}
v_reusejp_521_:
{
return v___x_522_;
}
}
}
else
{
lean_object* v_tail_525_; 
lean_inc_ref(v_tail_512_);
v_tail_525_ = lean_ctor_get(v_tail_512_, 1);
if (lean_obj_tag(v_tail_525_) == 0)
{
lean_object* v_head_526_; lean_object* v_head_527_; lean_object* v___x_528_; lean_object* v_fst_529_; lean_object* v_snd_530_; lean_object* v___x_532_; uint8_t v_isShared_533_; uint8_t v_isSharedCheck_540_; 
v_head_526_ = lean_ctor_get(v___x_511_, 0);
lean_inc(v_head_526_);
lean_dec_ref_known(v___x_511_, 2);
v_head_527_ = lean_ctor_get(v_tail_512_, 0);
lean_inc(v_head_527_);
lean_dec_ref_known(v_tail_512_, 2);
v___x_528_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeMantissa(v_head_526_);
lean_dec(v_head_526_);
v_fst_529_ = lean_ctor_get(v___x_528_, 0);
v_snd_530_ = lean_ctor_get(v___x_528_, 1);
v_isSharedCheck_540_ = !lean_is_exclusive(v___x_528_);
if (v_isSharedCheck_540_ == 0)
{
v___x_532_ = v___x_528_;
v_isShared_533_ = v_isSharedCheck_540_;
goto v_resetjp_531_;
}
else
{
lean_inc(v_snd_530_);
lean_inc(v_fst_529_);
lean_dec(v___x_528_);
v___x_532_ = lean_box(0);
v_isShared_533_ = v_isSharedCheck_540_;
goto v_resetjp_531_;
}
v_resetjp_531_:
{
lean_object* v_exp_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_538_; 
v_exp_534_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeDecInt(v_head_527_);
v___x_535_ = l_Int_negOfNat(v_snd_530_);
lean_dec(v_snd_530_);
v___x_536_ = lean_int_add(v___x_535_, v_exp_534_);
lean_dec(v_exp_534_);
lean_dec(v___x_535_);
if (v_isShared_533_ == 0)
{
lean_ctor_set(v___x_532_, 1, v___x_536_);
v___x_538_ = v___x_532_;
goto v_reusejp_537_;
}
else
{
lean_object* v_reuseFailAlloc_539_; 
v_reuseFailAlloc_539_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_539_, 0, v_fst_529_);
lean_ctor_set(v_reuseFailAlloc_539_, 1, v___x_536_);
v___x_538_ = v_reuseFailAlloc_539_;
goto v_reusejp_537_;
}
v_reusejp_537_:
{
return v___x_538_;
}
}
}
else
{
lean_dec_ref_known(v_tail_512_, 2);
lean_dec_ref_known(v___x_511_, 2);
goto v___jp_503_;
}
}
}
else
{
lean_dec(v___x_511_);
goto v___jp_503_;
}
v___jp_503_:
{
lean_object* v___x_504_; 
v___x_504_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp___closed__1, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp___closed__1_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp___closed__1);
return v___x_504_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__1(lean_object* v_s_541_, lean_object* v___x_542_, lean_object* v___x_543_, lean_object* v_inst_544_, lean_object* v_R_545_, lean_object* v_a_546_, lean_object* v_b_547_){
_start:
{
lean_object* v___x_548_; 
v___x_548_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__1___redArg(v_s_541_, v___x_542_, v___x_543_, v_a_546_, v_b_547_);
return v___x_548_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__1___boxed(lean_object* v_s_549_, lean_object* v___x_550_, lean_object* v___x_551_, lean_object* v_inst_552_, lean_object* v_R_553_, lean_object* v_a_554_, lean_object* v_b_555_){
_start:
{
lean_object* v_res_556_; 
v_res_556_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp_spec__1(v_s_549_, v___x_550_, v___x_551_, v_inst_552_, v_R_553_, v_a_554_, v_b_555_);
lean_dec_ref(v___x_550_);
return v_res_556_;
}
}
static double _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___closed__2(void){
_start:
{
lean_object* v___x_559_; double v___x_560_; 
v___x_559_ = lean_unsigned_to_nat(0u);
v___x_560_ = lean_float_of_nat(v___x_559_);
return v___x_560_;
}
}
LEAN_EXPORT double l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat(lean_object* v_s_561_){
_start:
{
lean_object* v___x_562_; lean_object* v_fst_563_; lean_object* v_snd_564_; lean_object* v___x_565_; uint8_t v___x_566_; 
v___x_562_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeSign(v_s_561_);
v_fst_563_ = lean_ctor_get(v___x_562_, 0);
lean_inc(v_fst_563_);
v_snd_564_ = lean_ctor_get(v___x_562_, 1);
lean_inc(v_snd_564_);
lean_dec_ref(v___x_562_);
v___x_565_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___closed__0));
v___x_566_ = lean_string_dec_eq(v_snd_564_, v___x_565_);
if (v___x_566_ == 0)
{
lean_object* v___x_567_; uint8_t v___x_568_; 
v___x_567_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___closed__1));
v___x_568_ = lean_string_dec_eq(v_snd_564_, v___x_567_);
if (v___x_568_ == 0)
{
lean_object* v___x_569_; lean_object* v_fst_570_; lean_object* v_snd_571_; lean_object* v___x_572_; uint8_t v___x_573_; lean_object* v___x_574_; double v_flt_575_; uint8_t v___x_576_; 
v___x_569_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp(v_snd_564_);
v_fst_570_ = lean_ctor_get(v___x_569_, 0);
lean_inc(v_fst_570_);
v_snd_571_ = lean_ctor_get(v___x_569_, 1);
lean_inc(v_snd_571_);
lean_dec_ref(v___x_569_);
v___x_572_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp___closed__0, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp___closed__0_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFrExp___closed__0);
v___x_573_ = lean_int_dec_lt(v_snd_571_, v___x_572_);
v___x_574_ = lean_nat_abs(v_snd_571_);
lean_dec(v_snd_571_);
v_flt_575_ = l_Float_ofScientific(v_fst_570_, v___x_573_, v___x_574_);
v___x_576_ = lean_unbox(v_fst_563_);
lean_dec(v_fst_563_);
if (v___x_576_ == 0)
{
return v_flt_575_;
}
else
{
double v___x_577_; 
v___x_577_ = lean_float_negate(v_flt_575_);
return v___x_577_;
}
}
else
{
uint8_t v___x_578_; 
lean_dec(v_snd_564_);
v___x_578_ = lean_unbox(v_fst_563_);
lean_dec(v_fst_563_);
if (v___x_578_ == 0)
{
lean_object* v___x_579_; lean_object* v___x_580_; double v___x_581_; double v___x_582_; double v___x_583_; 
v___x_579_ = lean_unsigned_to_nat(0u);
v___x_580_ = lean_unsigned_to_nat(1u);
v___x_581_ = l_Float_ofScientific(v___x_579_, v___x_568_, v___x_580_);
v___x_582_ = lean_float_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___closed__2, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___closed__2_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___closed__2);
v___x_583_ = lean_float_div(v___x_581_, v___x_582_);
return v___x_583_;
}
else
{
lean_object* v___x_584_; lean_object* v___x_585_; double v___x_586_; double v___x_587_; double v___x_588_; double v___x_589_; 
v___x_584_ = lean_unsigned_to_nat(0u);
v___x_585_ = lean_unsigned_to_nat(1u);
v___x_586_ = l_Float_ofScientific(v___x_584_, v___x_568_, v___x_585_);
v___x_587_ = lean_float_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___closed__2, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___closed__2_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___closed__2);
v___x_588_ = lean_float_div(v___x_586_, v___x_587_);
v___x_589_ = lean_float_negate(v___x_588_);
return v___x_589_;
}
}
}
else
{
uint8_t v___x_590_; 
lean_dec(v_snd_564_);
v___x_590_ = lean_unbox(v_fst_563_);
lean_dec(v_fst_563_);
if (v___x_590_ == 0)
{
lean_object* v___x_591_; lean_object* v___x_592_; double v___x_593_; double v___x_594_; double v___x_595_; 
v___x_591_ = lean_unsigned_to_nat(10u);
v___x_592_ = lean_unsigned_to_nat(1u);
v___x_593_ = l_Float_ofScientific(v___x_591_, v___x_566_, v___x_592_);
v___x_594_ = lean_float_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___closed__2, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___closed__2_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___closed__2);
v___x_595_ = lean_float_div(v___x_593_, v___x_594_);
return v___x_595_;
}
else
{
lean_object* v___x_596_; lean_object* v___x_597_; double v___x_598_; double v___x_599_; double v___x_600_; double v___x_601_; 
v___x_596_ = lean_unsigned_to_nat(10u);
v___x_597_ = lean_unsigned_to_nat(1u);
v___x_598_ = l_Float_ofScientific(v___x_596_, v___x_566_, v___x_597_);
v___x_599_ = lean_float_negate(v___x_598_);
v___x_600_ = lean_float_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___closed__2, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___closed__2_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___closed__2);
v___x_601_ = lean_float_div(v___x_599_, v___x_600_);
return v___x_601_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat___boxed(lean_object* v_s_602_){
_start:
{
double v_res_603_; lean_object* v_r_604_; 
v_res_603_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat(v_s_602_);
v_r_604_ = lean_box_float(v_res_603_);
return v_r_604_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat___closed__4(void){
_start:
{
lean_object* v___x_613_; lean_object* v___x_614_; 
v___x_613_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat___closed__3));
v___x_614_ = l_Lean_MessageData_ofFormat(v___x_613_);
return v___x_614_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat(lean_object* v_x_615_, lean_object* v_a_616_, lean_object* v_a_617_){
_start:
{
lean_object* v_a_620_; lean_object* v___x_624_; lean_object* v___x_625_; 
v___x_624_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat___closed__1));
v___x_625_ = l_Lean_Syntax_isLit_x3f(v___x_624_, v_x_615_);
if (lean_obj_tag(v___x_625_) == 1)
{
lean_object* v_val_626_; 
v_val_626_ = lean_ctor_get(v___x_625_, 0);
lean_inc(v_val_626_);
lean_dec_ref_known(v___x_625_, 1);
v_a_620_ = v_val_626_;
goto v___jp_619_;
}
else
{
lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v_a_629_; lean_object* v___x_631_; uint8_t v_isShared_632_; uint8_t v_isSharedCheck_636_; 
lean_dec(v___x_625_);
v___x_627_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat___closed__4, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat___closed__4_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat___closed__4);
v___x_628_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_x_615_, v___x_627_, v_a_616_, v_a_617_);
v_a_629_ = lean_ctor_get(v___x_628_, 0);
v_isSharedCheck_636_ = !lean_is_exclusive(v___x_628_);
if (v_isSharedCheck_636_ == 0)
{
v___x_631_ = v___x_628_;
v_isShared_632_ = v_isSharedCheck_636_;
goto v_resetjp_630_;
}
else
{
lean_inc(v_a_629_);
lean_dec(v___x_628_);
v___x_631_ = lean_box(0);
v_isShared_632_ = v_isSharedCheck_636_;
goto v_resetjp_630_;
}
v_resetjp_630_:
{
lean_object* v___x_634_; 
if (v_isShared_632_ == 0)
{
v___x_634_ = v___x_631_;
goto v_reusejp_633_;
}
else
{
lean_object* v_reuseFailAlloc_635_; 
v_reuseFailAlloc_635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_635_, 0, v_a_629_);
v___x_634_ = v_reuseFailAlloc_635_;
goto v_reusejp_633_;
}
v_reusejp_633_:
{
return v___x_634_;
}
}
}
v___jp_619_:
{
double v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; 
v___x_621_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeFloat(v_a_620_);
v___x_622_ = lean_box_float(v___x_621_);
v___x_623_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_623_, 0, v___x_622_);
return v___x_623_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat___boxed(lean_object* v_x_637_, lean_object* v_a_638_, lean_object* v_a_639_, lean_object* v_a_640_){
_start:
{
lean_object* v_res_641_; 
v_res_641_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat(v_x_637_, v_a_638_, v_a_639_);
lean_dec(v_a_639_);
lean_dec_ref(v_a_638_);
lean_dec(v_x_637_);
return v_res_641_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum_spec__0___redArg(lean_object* v___x_642_, lean_object* v___x_643_, lean_object* v_a_644_, lean_object* v_a_645_, lean_object* v_b_646_){
_start:
{
lean_object* v___x_647_; uint8_t v_decide_648_; 
v___x_647_ = lean_nat_sub(v___x_642_, v___x_643_);
v_decide_648_ = lean_nat_dec_eq(v_a_645_, v___x_647_);
lean_dec(v___x_647_);
if (v_decide_648_ == 0)
{
lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; uint32_t v___x_652_; uint32_t v___x_653_; uint8_t v___x_654_; 
v___x_649_ = lean_nat_add(v___x_643_, v_a_645_);
lean_dec(v_a_645_);
v___x_650_ = lean_string_utf8_next_fast(v_a_644_, v___x_649_);
v___x_651_ = lean_nat_sub(v___x_650_, v___x_643_);
v___x_652_ = lean_string_utf8_get_fast(v_a_644_, v___x_649_);
lean_dec(v___x_649_);
v___x_653_ = 95;
v___x_654_ = lean_uint32_dec_eq(v___x_652_, v___x_653_);
if (v___x_654_ == 0)
{
lean_object* v___x_655_; lean_object* v___x_656_; uint32_t v___x_657_; uint32_t v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; 
v___x_655_ = lean_unsigned_to_nat(2u);
v___x_656_ = lean_nat_mul(v_b_646_, v___x_655_);
lean_dec(v_b_646_);
v___x_657_ = 48;
v___x_658_ = lean_uint32_sub(v___x_652_, v___x_657_);
v___x_659_ = lean_uint32_to_nat(v___x_658_);
v___x_660_ = lean_nat_add(v___x_656_, v___x_659_);
lean_dec(v___x_659_);
lean_dec(v___x_656_);
v_a_645_ = v___x_651_;
v_b_646_ = v___x_660_;
goto _start;
}
else
{
v_a_645_ = v___x_651_;
goto _start;
}
}
else
{
lean_dec(v_a_645_);
return v_b_646_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum_spec__0___redArg___boxed(lean_object* v___x_663_, lean_object* v___x_664_, lean_object* v_a_665_, lean_object* v_a_666_, lean_object* v_b_667_){
_start:
{
lean_object* v_res_668_; 
v_res_668_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum_spec__0___redArg(v___x_663_, v___x_664_, v_a_665_, v_a_666_, v_b_667_);
lean_dec_ref(v_a_665_);
lean_dec(v___x_664_);
lean_dec(v___x_663_);
return v_res_668_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum___closed__4(void){
_start:
{
lean_object* v___x_677_; lean_object* v___x_678_; 
v___x_677_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum___closed__3));
v___x_678_ = l_Lean_MessageData_ofFormat(v___x_677_);
return v___x_678_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum(lean_object* v_x_679_, lean_object* v_a_680_, lean_object* v_a_681_){
_start:
{
lean_object* v_a_684_; lean_object* v___x_692_; lean_object* v___x_693_; 
v___x_692_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum___closed__1));
v___x_693_ = l_Lean_Syntax_isLit_x3f(v___x_692_, v_x_679_);
if (lean_obj_tag(v___x_693_) == 1)
{
lean_object* v_val_694_; 
v_val_694_ = lean_ctor_get(v___x_693_, 0);
lean_inc(v_val_694_);
lean_dec_ref_known(v___x_693_, 1);
v_a_684_ = v_val_694_;
goto v___jp_683_;
}
else
{
lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v_a_697_; lean_object* v___x_699_; uint8_t v_isShared_700_; uint8_t v_isSharedCheck_704_; 
lean_dec(v___x_693_);
v___x_695_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum___closed__4, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum___closed__4_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum___closed__4);
v___x_696_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_x_679_, v___x_695_, v_a_680_, v_a_681_);
v_a_697_ = lean_ctor_get(v___x_696_, 0);
v_isSharedCheck_704_ = !lean_is_exclusive(v___x_696_);
if (v_isSharedCheck_704_ == 0)
{
v___x_699_ = v___x_696_;
v_isShared_700_ = v_isSharedCheck_704_;
goto v_resetjp_698_;
}
else
{
lean_inc(v_a_697_);
lean_dec(v___x_696_);
v___x_699_ = lean_box(0);
v_isShared_700_ = v_isSharedCheck_704_;
goto v_resetjp_698_;
}
v_resetjp_698_:
{
lean_object* v___x_702_; 
if (v_isShared_700_ == 0)
{
v___x_702_ = v___x_699_;
goto v_reusejp_701_;
}
else
{
lean_object* v_reuseFailAlloc_703_; 
v_reuseFailAlloc_703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_703_, 0, v_a_697_);
v___x_702_ = v_reuseFailAlloc_703_;
goto v_reusejp_701_;
}
v_reusejp_701_:
{
return v___x_702_;
}
}
}
v___jp_683_:
{
lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; 
v___x_685_ = lean_unsigned_to_nat(0u);
v___x_686_ = lean_unsigned_to_nat(2u);
v___x_687_ = lean_string_utf8_byte_size(v_a_684_);
lean_inc_ref(v_a_684_);
v___x_688_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_688_, 0, v_a_684_);
lean_ctor_set(v___x_688_, 1, v___x_685_);
lean_ctor_set(v___x_688_, 2, v___x_687_);
v___x_689_ = l_String_Slice_Pos_nextn(v___x_688_, v___x_685_, v___x_686_);
lean_dec_ref_known(v___x_688_, 3);
v___x_690_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum_spec__0___redArg(v___x_687_, v___x_689_, v_a_684_, v___x_685_, v___x_685_);
lean_dec_ref(v_a_684_);
lean_dec(v___x_689_);
v___x_691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_691_, 0, v___x_690_);
return v___x_691_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum___boxed(lean_object* v_x_705_, lean_object* v_a_706_, lean_object* v_a_707_, lean_object* v_a_708_){
_start:
{
lean_object* v_res_709_; 
v_res_709_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum(v_x_705_, v_a_706_, v_a_707_);
lean_dec(v_a_707_);
lean_dec_ref(v_a_706_);
lean_dec(v_x_705_);
return v_res_709_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum_spec__0(lean_object* v___x_710_, lean_object* v___x_711_, lean_object* v___x_712_, lean_object* v_a_713_, lean_object* v_inst_714_, lean_object* v_R_715_, lean_object* v_a_716_, lean_object* v_b_717_, lean_object* v_c_718_){
_start:
{
lean_object* v___x_719_; 
v___x_719_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum_spec__0___redArg(v___x_710_, v___x_711_, v_a_713_, v_a_716_, v_b_717_);
return v___x_719_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum_spec__0___boxed(lean_object* v___x_720_, lean_object* v___x_721_, lean_object* v___x_722_, lean_object* v_a_723_, lean_object* v_inst_724_, lean_object* v_R_725_, lean_object* v_a_726_, lean_object* v_b_727_, lean_object* v_c_728_){
_start:
{
lean_object* v_res_729_; 
v_res_729_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum_spec__0(v___x_720_, v___x_721_, v___x_722_, v_a_723_, v_inst_724_, v_R_725_, v_a_726_, v_b_727_, v_c_728_);
lean_dec_ref(v_a_723_);
lean_dec_ref(v___x_722_);
lean_dec(v___x_721_);
lean_dec(v___x_720_);
return v_res_729_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum_spec__0___redArg(lean_object* v___x_730_, lean_object* v___x_731_, lean_object* v_a_732_, lean_object* v_a_733_, lean_object* v_b_734_){
_start:
{
lean_object* v___x_735_; uint8_t v_decide_736_; 
v___x_735_ = lean_nat_sub(v___x_730_, v___x_731_);
v_decide_736_ = lean_nat_dec_eq(v_a_733_, v___x_735_);
lean_dec(v___x_735_);
if (v_decide_736_ == 0)
{
lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; uint32_t v___x_740_; uint32_t v___x_741_; uint8_t v___x_742_; 
v___x_737_ = lean_nat_add(v___x_731_, v_a_733_);
lean_dec(v_a_733_);
v___x_738_ = lean_string_utf8_next_fast(v_a_732_, v___x_737_);
v___x_739_ = lean_nat_sub(v___x_738_, v___x_731_);
v___x_740_ = lean_string_utf8_get_fast(v_a_732_, v___x_737_);
lean_dec(v___x_737_);
v___x_741_ = 95;
v___x_742_ = lean_uint32_dec_eq(v___x_740_, v___x_741_);
if (v___x_742_ == 0)
{
lean_object* v___x_743_; lean_object* v___x_744_; uint32_t v___x_745_; uint32_t v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; 
v___x_743_ = lean_unsigned_to_nat(8u);
v___x_744_ = lean_nat_mul(v_b_734_, v___x_743_);
lean_dec(v_b_734_);
v___x_745_ = 48;
v___x_746_ = lean_uint32_sub(v___x_740_, v___x_745_);
v___x_747_ = lean_uint32_to_nat(v___x_746_);
v___x_748_ = lean_nat_add(v___x_744_, v___x_747_);
lean_dec(v___x_747_);
lean_dec(v___x_744_);
v_a_733_ = v___x_739_;
v_b_734_ = v___x_748_;
goto _start;
}
else
{
v_a_733_ = v___x_739_;
goto _start;
}
}
else
{
lean_dec(v_a_733_);
return v_b_734_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum_spec__0___redArg___boxed(lean_object* v___x_751_, lean_object* v___x_752_, lean_object* v_a_753_, lean_object* v_a_754_, lean_object* v_b_755_){
_start:
{
lean_object* v_res_756_; 
v_res_756_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum_spec__0___redArg(v___x_751_, v___x_752_, v_a_753_, v_a_754_, v_b_755_);
lean_dec_ref(v_a_753_);
lean_dec(v___x_752_);
lean_dec(v___x_751_);
return v_res_756_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum___closed__4(void){
_start:
{
lean_object* v___x_765_; lean_object* v___x_766_; 
v___x_765_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum___closed__3));
v___x_766_ = l_Lean_MessageData_ofFormat(v___x_765_);
return v___x_766_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum(lean_object* v_x_767_, lean_object* v_a_768_, lean_object* v_a_769_){
_start:
{
lean_object* v_a_772_; lean_object* v___x_780_; lean_object* v___x_781_; 
v___x_780_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum___closed__1));
v___x_781_ = l_Lean_Syntax_isLit_x3f(v___x_780_, v_x_767_);
if (lean_obj_tag(v___x_781_) == 1)
{
lean_object* v_val_782_; 
v_val_782_ = lean_ctor_get(v___x_781_, 0);
lean_inc(v_val_782_);
lean_dec_ref_known(v___x_781_, 1);
v_a_772_ = v_val_782_;
goto v___jp_771_;
}
else
{
lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v_a_785_; lean_object* v___x_787_; uint8_t v_isShared_788_; uint8_t v_isSharedCheck_792_; 
lean_dec(v___x_781_);
v___x_783_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum___closed__4, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum___closed__4_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum___closed__4);
v___x_784_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_x_767_, v___x_783_, v_a_768_, v_a_769_);
v_a_785_ = lean_ctor_get(v___x_784_, 0);
v_isSharedCheck_792_ = !lean_is_exclusive(v___x_784_);
if (v_isSharedCheck_792_ == 0)
{
v___x_787_ = v___x_784_;
v_isShared_788_ = v_isSharedCheck_792_;
goto v_resetjp_786_;
}
else
{
lean_inc(v_a_785_);
lean_dec(v___x_784_);
v___x_787_ = lean_box(0);
v_isShared_788_ = v_isSharedCheck_792_;
goto v_resetjp_786_;
}
v_resetjp_786_:
{
lean_object* v___x_790_; 
if (v_isShared_788_ == 0)
{
v___x_790_ = v___x_787_;
goto v_reusejp_789_;
}
else
{
lean_object* v_reuseFailAlloc_791_; 
v_reuseFailAlloc_791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_791_, 0, v_a_785_);
v___x_790_ = v_reuseFailAlloc_791_;
goto v_reusejp_789_;
}
v_reusejp_789_:
{
return v___x_790_;
}
}
}
v___jp_771_:
{
lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; 
v___x_773_ = lean_unsigned_to_nat(0u);
v___x_774_ = lean_unsigned_to_nat(2u);
v___x_775_ = lean_string_utf8_byte_size(v_a_772_);
lean_inc_ref(v_a_772_);
v___x_776_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_776_, 0, v_a_772_);
lean_ctor_set(v___x_776_, 1, v___x_773_);
lean_ctor_set(v___x_776_, 2, v___x_775_);
v___x_777_ = l_String_Slice_Pos_nextn(v___x_776_, v___x_773_, v___x_774_);
lean_dec_ref_known(v___x_776_, 3);
v___x_778_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum_spec__0___redArg(v___x_775_, v___x_777_, v_a_772_, v___x_773_, v___x_773_);
lean_dec_ref(v_a_772_);
lean_dec(v___x_777_);
v___x_779_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_779_, 0, v___x_778_);
return v___x_779_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum___boxed(lean_object* v_x_793_, lean_object* v_a_794_, lean_object* v_a_795_, lean_object* v_a_796_){
_start:
{
lean_object* v_res_797_; 
v_res_797_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum(v_x_793_, v_a_794_, v_a_795_);
lean_dec(v_a_795_);
lean_dec_ref(v_a_794_);
lean_dec(v_x_793_);
return v_res_797_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum_spec__0(lean_object* v___x_798_, lean_object* v___x_799_, lean_object* v___x_800_, lean_object* v_a_801_, lean_object* v_inst_802_, lean_object* v_R_803_, lean_object* v_a_804_, lean_object* v_b_805_, lean_object* v_c_806_){
_start:
{
lean_object* v___x_807_; 
v___x_807_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum_spec__0___redArg(v___x_798_, v___x_799_, v_a_801_, v_a_804_, v_b_805_);
return v___x_807_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum_spec__0___boxed(lean_object* v___x_808_, lean_object* v___x_809_, lean_object* v___x_810_, lean_object* v_a_811_, lean_object* v_inst_812_, lean_object* v_R_813_, lean_object* v_a_814_, lean_object* v_b_815_, lean_object* v_c_816_){
_start:
{
lean_object* v_res_817_; 
v_res_817_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum_spec__0(v___x_808_, v___x_809_, v___x_810_, v_a_811_, v_inst_812_, v_R_813_, v_a_814_, v_b_815_, v_c_816_);
lean_dec_ref(v_a_811_);
lean_dec_ref(v___x_810_);
lean_dec(v___x_809_);
lean_dec(v___x_808_);
return v_res_817_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigit(uint32_t v_c_818_){
_start:
{
uint32_t v___x_819_; uint8_t v___x_820_; 
v___x_819_ = 57;
v___x_820_ = lean_uint32_dec_le(v_c_818_, v___x_819_);
if (v___x_820_ == 0)
{
uint32_t v___x_821_; uint8_t v___x_822_; 
v___x_821_ = 70;
v___x_822_ = lean_uint32_dec_le(v_c_818_, v___x_821_);
if (v___x_822_ == 0)
{
lean_object* v___x_823_; uint32_t v___x_824_; uint32_t v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; 
v___x_823_ = lean_unsigned_to_nat(10u);
v___x_824_ = 97;
v___x_825_ = lean_uint32_sub(v_c_818_, v___x_824_);
v___x_826_ = lean_uint32_to_nat(v___x_825_);
v___x_827_ = lean_nat_add(v___x_823_, v___x_826_);
lean_dec(v___x_826_);
return v___x_827_;
}
else
{
lean_object* v___x_828_; uint32_t v___x_829_; uint32_t v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; 
v___x_828_ = lean_unsigned_to_nat(10u);
v___x_829_ = 65;
v___x_830_ = lean_uint32_sub(v_c_818_, v___x_829_);
v___x_831_ = lean_uint32_to_nat(v___x_830_);
v___x_832_ = lean_nat_add(v___x_828_, v___x_831_);
lean_dec(v___x_831_);
return v___x_832_;
}
}
else
{
uint32_t v___x_833_; uint32_t v___x_834_; lean_object* v___x_835_; 
v___x_833_ = 48;
v___x_834_ = lean_uint32_sub(v_c_818_, v___x_833_);
v___x_835_ = lean_uint32_to_nat(v___x_834_);
return v___x_835_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigit___boxed(lean_object* v_c_836_){
_start:
{
uint32_t v_c_boxed_837_; lean_object* v_res_838_; 
v_c_boxed_837_ = lean_unbox_uint32(v_c_836_);
lean_dec(v_c_836_);
v_res_838_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigit(v_c_boxed_837_);
return v_res_838_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum_spec__0___redArg(lean_object* v___x_839_, lean_object* v___x_840_, lean_object* v_a_841_, lean_object* v_a_842_, lean_object* v_b_843_){
_start:
{
lean_object* v___x_844_; uint8_t v_decide_845_; 
v___x_844_ = lean_nat_sub(v___x_839_, v___x_840_);
v_decide_845_ = lean_nat_dec_eq(v_a_842_, v___x_844_);
lean_dec(v___x_844_);
if (v_decide_845_ == 0)
{
lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; uint32_t v___x_849_; uint32_t v___x_850_; uint8_t v___x_851_; 
v___x_846_ = lean_nat_add(v___x_840_, v_a_842_);
lean_dec(v_a_842_);
v___x_847_ = lean_string_utf8_next_fast(v_a_841_, v___x_846_);
v___x_848_ = lean_nat_sub(v___x_847_, v___x_840_);
v___x_849_ = lean_string_utf8_get_fast(v_a_841_, v___x_846_);
lean_dec(v___x_846_);
v___x_850_ = 95;
v___x_851_ = lean_uint32_dec_eq(v___x_849_, v___x_850_);
if (v___x_851_ == 0)
{
lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; 
v___x_852_ = lean_unsigned_to_nat(16u);
v___x_853_ = lean_nat_mul(v_b_843_, v___x_852_);
lean_dec(v_b_843_);
v___x_854_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigit(v___x_849_);
v___x_855_ = lean_nat_add(v___x_853_, v___x_854_);
lean_dec(v___x_854_);
lean_dec(v___x_853_);
v_a_842_ = v___x_848_;
v_b_843_ = v___x_855_;
goto _start;
}
else
{
v_a_842_ = v___x_848_;
goto _start;
}
}
else
{
lean_dec(v_a_842_);
return v_b_843_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum_spec__0___redArg___boxed(lean_object* v___x_858_, lean_object* v___x_859_, lean_object* v_a_860_, lean_object* v_a_861_, lean_object* v_b_862_){
_start:
{
lean_object* v_res_863_; 
v_res_863_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum_spec__0___redArg(v___x_858_, v___x_859_, v_a_860_, v_a_861_, v_b_862_);
lean_dec_ref(v_a_860_);
lean_dec(v___x_859_);
lean_dec(v___x_858_);
return v_res_863_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum___closed__4(void){
_start:
{
lean_object* v___x_872_; lean_object* v___x_873_; 
v___x_872_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum___closed__3));
v___x_873_ = l_Lean_MessageData_ofFormat(v___x_872_);
return v___x_873_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum(lean_object* v_x_874_, lean_object* v_a_875_, lean_object* v_a_876_){
_start:
{
lean_object* v_a_879_; lean_object* v___x_887_; lean_object* v___x_888_; 
v___x_887_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum___closed__1));
v___x_888_ = l_Lean_Syntax_isLit_x3f(v___x_887_, v_x_874_);
if (lean_obj_tag(v___x_888_) == 1)
{
lean_object* v_val_889_; 
v_val_889_ = lean_ctor_get(v___x_888_, 0);
lean_inc(v_val_889_);
lean_dec_ref_known(v___x_888_, 1);
v_a_879_ = v_val_889_;
goto v___jp_878_;
}
else
{
lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v_a_892_; lean_object* v___x_894_; uint8_t v_isShared_895_; uint8_t v_isSharedCheck_899_; 
lean_dec(v___x_888_);
v___x_890_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum___closed__4, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum___closed__4_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum___closed__4);
v___x_891_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_x_874_, v___x_890_, v_a_875_, v_a_876_);
v_a_892_ = lean_ctor_get(v___x_891_, 0);
v_isSharedCheck_899_ = !lean_is_exclusive(v___x_891_);
if (v_isSharedCheck_899_ == 0)
{
v___x_894_ = v___x_891_;
v_isShared_895_ = v_isSharedCheck_899_;
goto v_resetjp_893_;
}
else
{
lean_inc(v_a_892_);
lean_dec(v___x_891_);
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
v___jp_878_:
{
lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; 
v___x_880_ = lean_unsigned_to_nat(0u);
v___x_881_ = lean_unsigned_to_nat(2u);
v___x_882_ = lean_string_utf8_byte_size(v_a_879_);
lean_inc_ref(v_a_879_);
v___x_883_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_883_, 0, v_a_879_);
lean_ctor_set(v___x_883_, 1, v___x_880_);
lean_ctor_set(v___x_883_, 2, v___x_882_);
v___x_884_ = l_String_Slice_Pos_nextn(v___x_883_, v___x_880_, v___x_881_);
lean_dec_ref_known(v___x_883_, 3);
v___x_885_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum_spec__0___redArg(v___x_882_, v___x_884_, v_a_879_, v___x_880_, v___x_880_);
lean_dec_ref(v_a_879_);
lean_dec(v___x_884_);
v___x_886_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_886_, 0, v___x_885_);
return v___x_886_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum___boxed(lean_object* v_x_900_, lean_object* v_a_901_, lean_object* v_a_902_, lean_object* v_a_903_){
_start:
{
lean_object* v_res_904_; 
v_res_904_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum(v_x_900_, v_a_901_, v_a_902_);
lean_dec(v_a_902_);
lean_dec_ref(v_a_901_);
lean_dec(v_x_900_);
return v_res_904_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum_spec__0(lean_object* v___x_905_, lean_object* v___x_906_, lean_object* v___x_907_, lean_object* v_a_908_, lean_object* v_inst_909_, lean_object* v_R_910_, lean_object* v_a_911_, lean_object* v_b_912_, lean_object* v_c_913_){
_start:
{
lean_object* v___x_914_; 
v___x_914_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum_spec__0___redArg(v___x_905_, v___x_906_, v_a_908_, v_a_911_, v_b_912_);
return v___x_914_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum_spec__0___boxed(lean_object* v___x_915_, lean_object* v___x_916_, lean_object* v___x_917_, lean_object* v_a_918_, lean_object* v_inst_919_, lean_object* v_R_920_, lean_object* v_a_921_, lean_object* v_b_922_, lean_object* v_c_923_){
_start:
{
lean_object* v_res_924_; 
v_res_924_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum_spec__0(v___x_915_, v___x_916_, v___x_917_, v_a_918_, v_inst_919_, v_R_920_, v_a_921_, v_b_922_, v_c_923_);
lean_dec_ref(v_a_918_);
lean_dec_ref(v___x_917_);
lean_dec(v___x_916_);
lean_dec(v___x_915_);
return v_res_924_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__1(void){
_start:
{
lean_object* v___x_926_; lean_object* v___x_927_; 
v___x_926_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__0));
v___x_927_ = l_Lean_stringToMessageData(v___x_926_);
return v___x_927_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__6(void){
_start:
{
lean_object* v___x_936_; lean_object* v___x_937_; 
v___x_936_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__5));
v___x_937_ = l_Lean_MessageData_ofFormat(v___x_936_);
return v___x_937_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime(lean_object* v_x_938_, lean_object* v_a_939_, lean_object* v_a_940_){
_start:
{
lean_object* v_a_943_; lean_object* v___x_955_; lean_object* v___x_956_; 
v___x_955_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__3));
v___x_956_ = l_Lean_Syntax_isLit_x3f(v___x_955_, v_x_938_);
if (lean_obj_tag(v___x_956_) == 1)
{
lean_object* v_val_957_; 
v_val_957_ = lean_ctor_get(v___x_956_, 0);
lean_inc(v_val_957_);
lean_dec_ref_known(v___x_956_, 1);
v_a_943_ = v_val_957_;
goto v___jp_942_;
}
else
{
lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v_a_960_; lean_object* v___x_962_; uint8_t v_isShared_963_; uint8_t v_isSharedCheck_967_; 
lean_dec(v___x_956_);
v___x_958_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__6, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__6_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__6);
v___x_959_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_x_938_, v___x_958_, v_a_939_, v_a_940_);
v_a_960_ = lean_ctor_get(v___x_959_, 0);
v_isSharedCheck_967_ = !lean_is_exclusive(v___x_959_);
if (v_isSharedCheck_967_ == 0)
{
v___x_962_ = v___x_959_;
v_isShared_963_ = v_isSharedCheck_967_;
goto v_resetjp_961_;
}
else
{
lean_inc(v_a_960_);
lean_dec(v___x_959_);
v___x_962_ = lean_box(0);
v_isShared_963_ = v_isSharedCheck_967_;
goto v_resetjp_961_;
}
v_resetjp_961_:
{
lean_object* v___x_965_; 
if (v_isShared_963_ == 0)
{
v___x_965_ = v___x_962_;
goto v_reusejp_964_;
}
else
{
lean_object* v_reuseFailAlloc_966_; 
v_reuseFailAlloc_966_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_966_, 0, v_a_960_);
v___x_965_ = v_reuseFailAlloc_966_;
goto v_reusejp_964_;
}
v_reusejp_964_:
{
return v___x_965_;
}
}
}
v___jp_942_:
{
lean_object* v___x_944_; 
v___x_944_ = l_Lake_Toml_DateTime_ofString_x3f(v_a_943_);
if (lean_obj_tag(v___x_944_) == 1)
{
lean_object* v_val_945_; lean_object* v___x_947_; uint8_t v_isShared_948_; uint8_t v_isSharedCheck_952_; 
v_val_945_ = lean_ctor_get(v___x_944_, 0);
v_isSharedCheck_952_ = !lean_is_exclusive(v___x_944_);
if (v_isSharedCheck_952_ == 0)
{
v___x_947_ = v___x_944_;
v_isShared_948_ = v_isSharedCheck_952_;
goto v_resetjp_946_;
}
else
{
lean_inc(v_val_945_);
lean_dec(v___x_944_);
v___x_947_ = lean_box(0);
v_isShared_948_ = v_isSharedCheck_952_;
goto v_resetjp_946_;
}
v_resetjp_946_:
{
lean_object* v___x_950_; 
if (v_isShared_948_ == 0)
{
lean_ctor_set_tag(v___x_947_, 0);
v___x_950_ = v___x_947_;
goto v_reusejp_949_;
}
else
{
lean_object* v_reuseFailAlloc_951_; 
v_reuseFailAlloc_951_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_951_, 0, v_val_945_);
v___x_950_ = v_reuseFailAlloc_951_;
goto v_reusejp_949_;
}
v_reusejp_949_:
{
return v___x_950_;
}
}
}
else
{
lean_object* v___x_953_; lean_object* v___x_954_; 
lean_dec(v___x_944_);
v___x_953_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__1, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__1_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__1);
v___x_954_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_x_938_, v___x_953_, v_a_939_, v_a_940_);
return v___x_954_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___boxed(lean_object* v_x_968_, lean_object* v_a_969_, lean_object* v_a_970_, lean_object* v_a_971_){
_start:
{
lean_object* v_res_972_; 
v_res_972_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime(v_x_968_, v_a_969_, v_a_970_);
lean_dec(v_a_970_);
lean_dec_ref(v_a_969_);
lean_dec(v_x_968_);
return v_res_972_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString___closed__4(void){
_start:
{
lean_object* v___x_981_; lean_object* v___x_982_; 
v___x_981_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString___closed__3));
v___x_982_ = l_Lean_MessageData_ofFormat(v___x_981_);
return v___x_982_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString(lean_object* v_x_983_, lean_object* v_a_984_, lean_object* v_a_985_){
_start:
{
lean_object* v_a_988_; lean_object* v___x_1000_; lean_object* v___x_1001_; 
v___x_1000_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString___closed__1));
v___x_1001_ = l_Lean_Syntax_isLit_x3f(v___x_1000_, v_x_983_);
if (lean_obj_tag(v___x_1001_) == 1)
{
lean_object* v_val_1002_; 
v_val_1002_ = lean_ctor_get(v___x_1001_, 0);
lean_inc(v_val_1002_);
lean_dec_ref_known(v___x_1001_, 1);
v_a_988_ = v_val_1002_;
goto v___jp_987_;
}
else
{
lean_object* v___x_1003_; lean_object* v___x_1004_; 
lean_dec(v___x_1001_);
v___x_1003_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString___closed__4, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString___closed__4_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString___closed__4);
v___x_1004_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_x_983_, v___x_1003_, v_a_984_, v_a_985_);
return v___x_1004_;
}
v___jp_987_:
{
lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; 
v___x_989_ = lean_unsigned_to_nat(1u);
v___x_990_ = lean_unsigned_to_nat(0u);
v___x_991_ = lean_string_utf8_byte_size(v_a_988_);
lean_inc_ref_n(v_a_988_, 2);
v___x_992_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_992_, 0, v_a_988_);
lean_ctor_set(v___x_992_, 1, v___x_990_);
lean_ctor_set(v___x_992_, 2, v___x_991_);
v___x_993_ = l_String_Slice_Pos_nextn(v___x_992_, v___x_990_, v___x_989_);
lean_dec_ref_known(v___x_992_, 3);
lean_inc(v___x_993_);
v___x_994_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_994_, 0, v_a_988_);
lean_ctor_set(v___x_994_, 1, v___x_993_);
lean_ctor_set(v___x_994_, 2, v___x_991_);
v___x_995_ = lean_nat_sub(v___x_991_, v___x_993_);
v___x_996_ = l_String_Slice_Pos_prevn(v___x_994_, v___x_995_, v___x_989_);
lean_dec_ref_known(v___x_994_, 3);
v___x_997_ = lean_nat_add(v___x_993_, v___x_996_);
lean_dec(v___x_996_);
v___x_998_ = lean_string_utf8_extract_fast(v_a_988_, v___x_993_, v___x_997_);
lean_dec(v___x_997_);
lean_dec(v___x_993_);
lean_dec_ref(v_a_988_);
v___x_999_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_999_, 0, v___x_998_);
return v___x_999_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString___boxed(lean_object* v_x_1005_, lean_object* v_a_1006_, lean_object* v_a_1007_, lean_object* v_a_1008_){
_start:
{
lean_object* v_res_1009_; 
v_res_1009_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString(v_x_1005_, v_a_1006_, v_a_1007_);
lean_dec(v_a_1007_);
lean_dec_ref(v_a_1006_);
lean_dec(v_x_1005_);
return v_res_1009_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits_spec__1(lean_object* v_msg_1010_){
_start:
{
lean_object* v___x_1011_; lean_object* v___x_1012_; 
v___x_1011_ = l_String_instInhabitedSlice;
v___x_1012_ = lean_panic_fn_borrowed(v___x_1011_, v_msg_1010_);
return v___x_1012_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits_spec__0___redArg(lean_object* v___y_1013_, lean_object* v_a_1014_, lean_object* v_b_1015_){
_start:
{
lean_object* v_str_1016_; lean_object* v_startInclusive_1017_; lean_object* v_endExclusive_1018_; lean_object* v___x_1019_; uint8_t v_decide_1020_; 
v_str_1016_ = lean_ctor_get(v___y_1013_, 0);
v_startInclusive_1017_ = lean_ctor_get(v___y_1013_, 1);
v_endExclusive_1018_ = lean_ctor_get(v___y_1013_, 2);
v___x_1019_ = lean_nat_sub(v_endExclusive_1018_, v_startInclusive_1017_);
v_decide_1020_ = lean_nat_dec_eq(v_a_1014_, v___x_1019_);
lean_dec(v___x_1019_);
if (v_decide_1020_ == 0)
{
lean_object* v___x_1021_; uint32_t v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; 
v___x_1021_ = lean_nat_add(v_startInclusive_1017_, v_a_1014_);
lean_dec(v_a_1014_);
v___x_1022_ = lean_string_utf8_get_fast(v_str_1016_, v___x_1021_);
v___x_1023_ = lean_string_utf8_next_fast(v_str_1016_, v___x_1021_);
lean_dec(v___x_1021_);
v___x_1024_ = lean_nat_sub(v___x_1023_, v_startInclusive_1017_);
v___x_1025_ = lean_unsigned_to_nat(16u);
v___x_1026_ = lean_nat_mul(v_b_1015_, v___x_1025_);
lean_dec(v_b_1015_);
v___x_1027_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigit(v___x_1022_);
v___x_1028_ = lean_nat_add(v___x_1026_, v___x_1027_);
lean_dec(v___x_1027_);
lean_dec(v___x_1026_);
v_a_1014_ = v___x_1024_;
v_b_1015_ = v___x_1028_;
goto _start;
}
else
{
lean_dec(v_a_1014_);
return v_b_1015_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits_spec__0___redArg___boxed(lean_object* v___y_1030_, lean_object* v_a_1031_, lean_object* v_b_1032_){
_start:
{
lean_object* v_res_1033_; 
v_res_1033_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits_spec__0___redArg(v___y_1030_, v_a_1031_, v_b_1032_);
lean_dec_ref(v___y_1030_);
return v_res_1033_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits___closed__3(void){
_start:
{
lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; 
v___x_1037_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits___closed__2));
v___x_1038_ = lean_unsigned_to_nat(14u);
v___x_1039_ = lean_unsigned_to_nat(22u);
v___x_1040_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits___closed__1));
v___x_1041_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits___closed__0));
v___x_1042_ = l_mkPanicMessageWithDecl(v___x_1041_, v___x_1040_, v___x_1039_, v___x_1038_, v___x_1037_);
return v___x_1042_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits(lean_object* v_s_1043_){
_start:
{
lean_object* v_str_1044_; lean_object* v_startPos_1045_; lean_object* v_stopPos_1046_; lean_object* v___x_1048_; uint8_t v_isShared_1049_; uint8_t v_isSharedCheck_1064_; 
v_str_1044_ = lean_ctor_get(v_s_1043_, 0);
v_startPos_1045_ = lean_ctor_get(v_s_1043_, 1);
v_stopPos_1046_ = lean_ctor_get(v_s_1043_, 2);
v_isSharedCheck_1064_ = !lean_is_exclusive(v_s_1043_);
if (v_isSharedCheck_1064_ == 0)
{
v___x_1048_ = v_s_1043_;
v_isShared_1049_ = v_isSharedCheck_1064_;
goto v_resetjp_1047_;
}
else
{
lean_inc(v_stopPos_1046_);
lean_inc(v_startPos_1045_);
lean_inc(v_str_1044_);
lean_dec(v_s_1043_);
v___x_1048_ = lean_box(0);
v_isShared_1049_ = v_isSharedCheck_1064_;
goto v_resetjp_1047_;
}
v_resetjp_1047_:
{
lean_object* v___x_1050_; lean_object* v___y_1052_; uint8_t v___y_1055_; uint8_t v___x_1061_; 
v___x_1050_ = lean_unsigned_to_nat(0u);
v___x_1061_ = lean_string_is_valid_pos(v_str_1044_, v_startPos_1045_);
if (v___x_1061_ == 0)
{
v___y_1055_ = v___x_1061_;
goto v___jp_1054_;
}
else
{
uint8_t v___x_1062_; 
v___x_1062_ = lean_string_is_valid_pos(v_str_1044_, v_stopPos_1046_);
if (v___x_1062_ == 0)
{
v___y_1055_ = v___x_1062_;
goto v___jp_1054_;
}
else
{
uint8_t v___x_1063_; 
v___x_1063_ = lean_nat_dec_le(v_startPos_1045_, v_stopPos_1046_);
v___y_1055_ = v___x_1063_;
goto v___jp_1054_;
}
}
v___jp_1051_:
{
lean_object* v___x_1053_; 
v___x_1053_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits_spec__0___redArg(v___y_1052_, v___x_1050_, v___x_1050_);
lean_dec_ref(v___y_1052_);
return v___x_1053_;
}
v___jp_1054_:
{
if (v___y_1055_ == 0)
{
lean_object* v___x_1056_; lean_object* v___x_1057_; 
lean_del_object(v___x_1048_);
lean_dec(v_stopPos_1046_);
lean_dec(v_startPos_1045_);
lean_dec_ref(v_str_1044_);
v___x_1056_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits___closed__3, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits___closed__3_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits___closed__3);
v___x_1057_ = l_panic___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits_spec__1(v___x_1056_);
v___y_1052_ = v___x_1057_;
goto v___jp_1051_;
}
else
{
lean_object* v___x_1059_; 
if (v_isShared_1049_ == 0)
{
v___x_1059_ = v___x_1048_;
goto v_reusejp_1058_;
}
else
{
lean_object* v_reuseFailAlloc_1060_; 
v_reuseFailAlloc_1060_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1060_, 0, v_str_1044_);
lean_ctor_set(v_reuseFailAlloc_1060_, 1, v_startPos_1045_);
lean_ctor_set(v_reuseFailAlloc_1060_, 2, v_stopPos_1046_);
v___x_1059_ = v_reuseFailAlloc_1060_;
goto v_reusejp_1058_;
}
v_reusejp_1058_:
{
v___y_1052_ = v___x_1059_;
goto v___jp_1051_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits_spec__0(lean_object* v___y_1065_, lean_object* v_inst_1066_, lean_object* v_R_1067_, lean_object* v_a_1068_, lean_object* v_b_1069_, lean_object* v_c_1070_){
_start:
{
lean_object* v___x_1071_; 
v___x_1071_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits_spec__0___redArg(v___y_1065_, v_a_1068_, v_b_1069_);
return v___x_1071_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits_spec__0___boxed(lean_object* v___y_1072_, lean_object* v_inst_1073_, lean_object* v_R_1074_, lean_object* v_a_1075_, lean_object* v_b_1076_, lean_object* v_c_1077_){
_start:
{
lean_object* v_res_1078_; 
v_res_1078_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits_spec__0(v___y_1072_, v_inst_1073_, v_R_1074_, v_a_1075_, v_b_1076_, v_c_1077_);
lean_dec_ref(v___y_1072_);
return v_res_1078_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore_spec__0(lean_object* v_s_1079_, lean_object* v_stopPos_1080_, lean_object* v_i_1081_){
_start:
{
uint8_t v___y_1083_; lean_object* v___x_1086_; lean_object* v___x_1087_; uint8_t v___x_1088_; 
v___x_1086_ = lean_unsigned_to_nat(1u);
v___x_1087_ = lean_nat_add(v_i_1081_, v___x_1086_);
v___x_1088_ = lean_nat_dec_le(v___x_1087_, v_stopPos_1080_);
lean_dec(v___x_1087_);
if (v___x_1088_ == 0)
{
return v_i_1081_;
}
else
{
if (v___x_1088_ == 0)
{
v___y_1083_ = v___x_1088_;
goto v___jp_1082_;
}
else
{
uint32_t v___x_1089_; uint32_t v___x_1090_; uint8_t v___x_1091_; 
v___x_1089_ = lean_string_utf8_get(v_s_1079_, v_i_1081_);
v___x_1090_ = 32;
v___x_1091_ = lean_uint32_dec_eq(v___x_1089_, v___x_1090_);
if (v___x_1091_ == 0)
{
uint32_t v___x_1092_; uint8_t v___x_1093_; 
v___x_1092_ = 9;
v___x_1093_ = lean_uint32_dec_eq(v___x_1089_, v___x_1092_);
if (v___x_1093_ == 0)
{
uint32_t v___x_1094_; uint8_t v___x_1095_; 
v___x_1094_ = 13;
v___x_1095_ = lean_uint32_dec_eq(v___x_1089_, v___x_1094_);
if (v___x_1095_ == 0)
{
uint32_t v___x_1096_; uint8_t v___x_1097_; 
v___x_1096_ = 10;
v___x_1097_ = lean_uint32_dec_eq(v___x_1089_, v___x_1096_);
v___y_1083_ = v___x_1097_;
goto v___jp_1082_;
}
else
{
v___y_1083_ = v___x_1095_;
goto v___jp_1082_;
}
}
else
{
v___y_1083_ = v___x_1093_;
goto v___jp_1082_;
}
}
else
{
v___y_1083_ = v___x_1091_;
goto v___jp_1082_;
}
}
}
v___jp_1082_:
{
if (v___y_1083_ == 0)
{
return v_i_1081_;
}
else
{
lean_object* v___x_1084_; 
v___x_1084_ = lean_string_utf8_next(v_s_1079_, v_i_1081_);
lean_dec(v_i_1081_);
v_i_1081_ = v___x_1084_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore_spec__0___boxed(lean_object* v_s_1098_, lean_object* v_stopPos_1099_, lean_object* v_i_1100_){
_start:
{
lean_object* v_res_1101_; 
v_res_1101_ = l_Substring_Raw_takeWhileAux___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore_spec__0(v_s_1098_, v_stopPos_1099_, v_i_1100_);
lean_dec(v_stopPos_1099_);
lean_dec_ref(v_s_1098_);
return v_res_1101_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__1(void){
_start:
{
lean_object* v___x_1103_; lean_object* v___x_1104_; 
v___x_1103_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__0));
v___x_1104_ = l_Lean_stringToMessageData(v___x_1103_);
return v___x_1104_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__3(void){
_start:
{
lean_object* v___x_1106_; lean_object* v___x_1107_; 
v___x_1106_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__2));
v___x_1107_ = l_Lean_stringToMessageData(v___x_1106_);
return v___x_1107_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore(lean_object* v_lit_1108_, lean_object* v_i_1109_, lean_object* v_out_1110_, lean_object* v_a_1111_, lean_object* v_a_1112_){
_start:
{
lean_object* v___y_1115_; lean_object* v___y_1116_; lean_object* v___y_1117_; lean_object* v___y_1118_; lean_object* v___y_1124_; lean_object* v___y_1125_; lean_object* v___y_1126_; lean_object* v___y_1127_; uint8_t v___y_1128_; uint8_t v___x_1137_; 
v___x_1137_ = lean_string_utf8_at_end(v_lit_1108_, v_i_1109_);
if (v___x_1137_ == 0)
{
uint32_t v_curr_1138_; lean_object* v_i_1139_; uint32_t v___x_1140_; uint8_t v___x_1141_; 
v_curr_1138_ = lean_string_utf8_get_fast(v_lit_1108_, v_i_1109_);
v_i_1139_ = lean_string_utf8_next_fast(v_lit_1108_, v_i_1109_);
lean_dec(v_i_1109_);
v___x_1140_ = 92;
v___x_1141_ = lean_uint32_dec_eq(v_curr_1138_, v___x_1140_);
if (v___x_1141_ == 0)
{
lean_object* v___x_1142_; 
v___x_1142_ = lean_string_push(v_out_1110_, v_curr_1138_);
v_i_1109_ = v_i_1139_;
v_out_1110_ = v___x_1142_;
goto _start;
}
else
{
uint8_t v___x_1144_; lean_object* v_escape_1146_; lean_object* v___y_1147_; lean_object* v___y_1148_; 
v___x_1144_ = lean_string_utf8_at_end(v_lit_1108_, v_i_1139_);
if (v___x_1144_ == 0)
{
uint32_t v_curr_1156_; lean_object* v_next_1157_; uint32_t v___x_1158_; uint8_t v___x_1159_; 
v_curr_1156_ = lean_string_utf8_get_fast(v_lit_1108_, v_i_1139_);
v_next_1157_ = lean_string_utf8_next_fast(v_lit_1108_, v_i_1139_);
v___x_1158_ = 98;
v___x_1159_ = lean_uint32_dec_eq(v_curr_1156_, v___x_1158_);
if (v___x_1159_ == 0)
{
uint32_t v___x_1160_; uint8_t v___x_1161_; 
v___x_1160_ = 116;
v___x_1161_ = lean_uint32_dec_eq(v_curr_1156_, v___x_1160_);
if (v___x_1161_ == 0)
{
uint32_t v___x_1162_; uint8_t v___x_1163_; 
v___x_1162_ = 110;
v___x_1163_ = lean_uint32_dec_eq(v_curr_1156_, v___x_1162_);
if (v___x_1163_ == 0)
{
uint32_t v___x_1164_; uint8_t v___x_1165_; 
v___x_1164_ = 102;
v___x_1165_ = lean_uint32_dec_eq(v_curr_1156_, v___x_1164_);
if (v___x_1165_ == 0)
{
uint32_t v___x_1166_; uint8_t v___x_1167_; 
v___x_1166_ = 114;
v___x_1167_ = lean_uint32_dec_eq(v_curr_1156_, v___x_1166_);
if (v___x_1167_ == 0)
{
uint32_t v___x_1168_; uint8_t v___x_1169_; 
v___x_1168_ = 34;
v___x_1169_ = lean_uint32_dec_eq(v_curr_1156_, v___x_1168_);
if (v___x_1169_ == 0)
{
uint8_t v___x_1170_; 
v___x_1170_ = lean_uint32_dec_eq(v_curr_1156_, v___x_1140_);
if (v___x_1170_ == 0)
{
uint32_t v___x_1171_; uint8_t v___x_1172_; 
v___x_1171_ = 117;
v___x_1172_ = lean_uint32_dec_eq(v_curr_1156_, v___x_1171_);
if (v___x_1172_ == 0)
{
uint32_t v___x_1173_; uint8_t v___x_1174_; 
v___x_1173_ = 85;
v___x_1174_ = lean_uint32_dec_eq(v_curr_1156_, v___x_1173_);
if (v___x_1174_ == 0)
{
lean_object* v___x_1175_; lean_object* v_b_1176_; 
v___x_1175_ = lean_string_utf8_byte_size(v_lit_1108_);
v_b_1176_ = l_Substring_Raw_takeWhileAux___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore_spec__0(v_lit_1108_, v___x_1175_, v_i_1139_);
v_i_1109_ = v_b_1176_;
goto _start;
}
else
{
lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; 
v___x_1178_ = lean_string_utf8_byte_size(v_lit_1108_);
lean_inc_ref_n(v_lit_1108_, 2);
v___x_1179_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1179_, 0, v_lit_1108_);
lean_ctor_set(v___x_1179_, 1, v_next_1157_);
lean_ctor_set(v___x_1179_, 2, v___x_1178_);
v___x_1180_ = lean_unsigned_to_nat(8u);
v___x_1181_ = lean_unsigned_to_nat(0u);
v___x_1182_ = l_Substring_Raw_nextn(v___x_1179_, v___x_1180_, v___x_1181_);
lean_dec_ref_known(v___x_1179_, 3);
v___x_1183_ = lean_nat_add(v_next_1157_, v___x_1182_);
lean_dec(v___x_1182_);
v___x_1184_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1184_, 0, v_lit_1108_);
lean_ctor_set(v___x_1184_, 1, v_next_1157_);
lean_ctor_set(v___x_1184_, 2, v___x_1183_);
v_escape_1146_ = v___x_1184_;
v___y_1147_ = v_a_1111_;
v___y_1148_ = v_a_1112_;
goto v___jp_1145_;
}
}
else
{
lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; 
v___x_1185_ = lean_string_utf8_byte_size(v_lit_1108_);
lean_inc_ref_n(v_lit_1108_, 2);
v___x_1186_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1186_, 0, v_lit_1108_);
lean_ctor_set(v___x_1186_, 1, v_next_1157_);
lean_ctor_set(v___x_1186_, 2, v___x_1185_);
v___x_1187_ = lean_unsigned_to_nat(4u);
v___x_1188_ = lean_unsigned_to_nat(0u);
v___x_1189_ = l_Substring_Raw_nextn(v___x_1186_, v___x_1187_, v___x_1188_);
lean_dec_ref_known(v___x_1186_, 3);
v___x_1190_ = lean_nat_add(v_next_1157_, v___x_1189_);
lean_dec(v___x_1189_);
v___x_1191_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1191_, 0, v_lit_1108_);
lean_ctor_set(v___x_1191_, 1, v_next_1157_);
lean_ctor_set(v___x_1191_, 2, v___x_1190_);
v_escape_1146_ = v___x_1191_;
v___y_1147_ = v_a_1111_;
v___y_1148_ = v_a_1112_;
goto v___jp_1145_;
}
}
else
{
lean_object* v___x_1192_; 
v___x_1192_ = lean_string_push(v_out_1110_, v___x_1140_);
v_i_1109_ = v_next_1157_;
v_out_1110_ = v___x_1192_;
goto _start;
}
}
else
{
lean_object* v___x_1194_; 
v___x_1194_ = lean_string_push(v_out_1110_, v___x_1168_);
v_i_1109_ = v_next_1157_;
v_out_1110_ = v___x_1194_;
goto _start;
}
}
else
{
uint32_t v___x_1196_; lean_object* v___x_1197_; 
v___x_1196_ = 13;
v___x_1197_ = lean_string_push(v_out_1110_, v___x_1196_);
v_i_1109_ = v_next_1157_;
v_out_1110_ = v___x_1197_;
goto _start;
}
}
else
{
uint32_t v___x_1199_; lean_object* v___x_1200_; 
v___x_1199_ = 12;
v___x_1200_ = lean_string_push(v_out_1110_, v___x_1199_);
v_i_1109_ = v_next_1157_;
v_out_1110_ = v___x_1200_;
goto _start;
}
}
else
{
uint32_t v___x_1202_; lean_object* v___x_1203_; 
v___x_1202_ = 10;
v___x_1203_ = lean_string_push(v_out_1110_, v___x_1202_);
v_i_1109_ = v_next_1157_;
v_out_1110_ = v___x_1203_;
goto _start;
}
}
else
{
uint32_t v___x_1205_; lean_object* v___x_1206_; 
v___x_1205_ = 9;
v___x_1206_ = lean_string_push(v_out_1110_, v___x_1205_);
v_i_1109_ = v_next_1157_;
v_out_1110_ = v___x_1206_;
goto _start;
}
}
else
{
uint32_t v___x_1208_; lean_object* v___x_1209_; 
v___x_1208_ = 8;
v___x_1209_ = lean_string_push(v_out_1110_, v___x_1208_);
v_i_1109_ = v_next_1157_;
v_out_1110_ = v___x_1209_;
goto _start;
}
}
else
{
lean_object* v___x_1211_; 
lean_dec_ref(v_lit_1108_);
v___x_1211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1211_, 0, v_out_1110_);
return v___x_1211_;
}
v___jp_1145_:
{
lean_object* v_val_1149_; lean_object* v___x_1150_; uint8_t v___x_1151_; 
lean_inc_ref(v_escape_1146_);
v_val_1149_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_decodeHexDigits(v_escape_1146_);
v___x_1150_ = lean_unsigned_to_nat(55296u);
v___x_1151_ = lean_nat_dec_lt(v_val_1149_, v___x_1150_);
if (v___x_1151_ == 0)
{
lean_object* v___x_1152_; uint8_t v___x_1153_; 
v___x_1152_ = lean_unsigned_to_nat(57343u);
v___x_1153_ = lean_nat_dec_lt(v___x_1152_, v_val_1149_);
if (v___x_1153_ == 0)
{
v___y_1124_ = v___y_1148_;
v___y_1125_ = v___y_1147_;
v___y_1126_ = v_escape_1146_;
v___y_1127_ = v_val_1149_;
v___y_1128_ = v___x_1144_;
goto v___jp_1123_;
}
else
{
lean_object* v___x_1154_; uint8_t v___x_1155_; 
v___x_1154_ = lean_unsigned_to_nat(1114112u);
v___x_1155_ = lean_nat_dec_lt(v_val_1149_, v___x_1154_);
v___y_1124_ = v___y_1148_;
v___y_1125_ = v___y_1147_;
v___y_1126_ = v_escape_1146_;
v___y_1127_ = v_val_1149_;
v___y_1128_ = v___x_1155_;
goto v___jp_1123_;
}
}
else
{
v___y_1115_ = v___y_1148_;
v___y_1116_ = v___y_1147_;
v___y_1117_ = v_escape_1146_;
v___y_1118_ = v_val_1149_;
goto v___jp_1114_;
}
}
}
}
else
{
lean_object* v___x_1212_; 
lean_dec(v_i_1109_);
lean_dec_ref(v_lit_1108_);
v___x_1212_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1212_, 0, v_out_1110_);
return v___x_1212_;
}
v___jp_1114_:
{
lean_object* v_stopPos_1119_; uint32_t v_ch_1120_; lean_object* v___x_1121_; 
v_stopPos_1119_ = lean_ctor_get(v___y_1117_, 2);
lean_inc(v_stopPos_1119_);
lean_dec_ref(v___y_1117_);
v_ch_1120_ = lean_uint32_of_nat(v___y_1118_);
lean_dec(v___y_1118_);
v___x_1121_ = lean_string_push(v_out_1110_, v_ch_1120_);
v_i_1109_ = v_stopPos_1119_;
v_out_1110_ = v___x_1121_;
v_a_1111_ = v___y_1116_;
v_a_1112_ = v___y_1115_;
goto _start;
}
v___jp_1123_:
{
if (v___y_1128_ == 0)
{
lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; 
lean_dec(v___y_1127_);
lean_dec_ref(v_out_1110_);
lean_dec_ref(v_lit_1108_);
v___x_1129_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__1, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__1_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__1);
v___x_1130_ = lean_substring_tostring(v___y_1126_);
v___x_1131_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1131_, 0, v___x_1130_);
v___x_1132_ = l_Lean_MessageData_ofFormat(v___x_1131_);
v___x_1133_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1133_, 0, v___x_1129_);
lean_ctor_set(v___x_1133_, 1, v___x_1132_);
v___x_1134_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__3, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__3_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__3);
v___x_1135_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1135_, 0, v___x_1133_);
lean_ctor_set(v___x_1135_, 1, v___x_1134_);
v___x_1136_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0___redArg(v___x_1135_, v___y_1125_, v___y_1124_);
return v___x_1136_;
}
else
{
v___y_1115_ = v___y_1124_;
v___y_1116_ = v___y_1125_;
v___y_1117_ = v___y_1126_;
v___y_1118_ = v___y_1127_;
goto v___jp_1114_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___boxed(lean_object* v_lit_1213_, lean_object* v_i_1214_, lean_object* v_out_1215_, lean_object* v_a_1216_, lean_object* v_a_1217_, lean_object* v_a_1218_){
_start:
{
lean_object* v_res_1219_; 
v_res_1219_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore(v_lit_1213_, v_i_1214_, v_out_1215_, v_a_1216_, v_a_1217_);
lean_dec(v_a_1217_);
lean_dec_ref(v_a_1216_);
return v_res_1219_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__5(void){
_start:
{
lean_object* v___x_1229_; lean_object* v___x_1230_; 
v___x_1229_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__4));
v___x_1230_ = l_Lean_MessageData_ofFormat(v___x_1229_);
return v___x_1230_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString(lean_object* v_x_1231_, lean_object* v_a_1232_, lean_object* v_a_1233_){
_start:
{
lean_object* v_a_1236_; lean_object* v___x_1257_; lean_object* v___x_1258_; 
v___x_1257_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__2));
v___x_1258_ = l_Lean_Syntax_isLit_x3f(v___x_1257_, v_x_1231_);
if (lean_obj_tag(v___x_1258_) == 1)
{
lean_object* v_val_1259_; 
v_val_1259_ = lean_ctor_get(v___x_1258_, 0);
lean_inc(v_val_1259_);
lean_dec_ref_known(v___x_1258_, 1);
v_a_1236_ = v_val_1259_;
goto v___jp_1235_;
}
else
{
lean_object* v___x_1260_; lean_object* v___x_1261_; 
lean_dec(v___x_1258_);
v___x_1260_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__5, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__5_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__5);
v___x_1261_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_x_1231_, v___x_1260_, v_a_1232_, v_a_1233_);
return v___x_1261_;
}
v___jp_1235_:
{
lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v_toCold_1240_; lean_object* v_currRecDepth_1241_; lean_object* v_ref_1242_; uint16_t v_optionFlags_1243_; uint8_t v_suppressElabErrors_1244_; uint8_t v_isRecordingDeps_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v_ref_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; 
v___x_1237_ = lean_unsigned_to_nat(0u);
v___x_1238_ = lean_string_utf8_byte_size(v_a_1236_);
lean_inc_ref_n(v_a_1236_, 2);
v___x_1239_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1239_, 0, v_a_1236_);
lean_ctor_set(v___x_1239_, 1, v___x_1237_);
lean_ctor_set(v___x_1239_, 2, v___x_1238_);
v_toCold_1240_ = lean_ctor_get(v_a_1232_, 0);
v_currRecDepth_1241_ = lean_ctor_get(v_a_1232_, 1);
v_ref_1242_ = lean_ctor_get(v_a_1232_, 2);
v_optionFlags_1243_ = lean_ctor_get_uint16(v_a_1232_, sizeof(void*)*3);
v_suppressElabErrors_1244_ = lean_ctor_get_uint8(v_a_1232_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1245_ = lean_ctor_get_uint8(v_a_1232_, sizeof(void*)*3 + 3);
v___x_1246_ = lean_unsigned_to_nat(1u);
v___x_1247_ = l_String_Slice_Pos_nextn(v___x_1239_, v___x_1237_, v___x_1246_);
lean_dec_ref_known(v___x_1239_, 3);
lean_inc(v___x_1247_);
v___x_1248_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1248_, 0, v_a_1236_);
lean_ctor_set(v___x_1248_, 1, v___x_1247_);
lean_ctor_set(v___x_1248_, 2, v___x_1238_);
v___x_1249_ = lean_nat_sub(v___x_1238_, v___x_1247_);
v___x_1250_ = l_String_Slice_Pos_prevn(v___x_1248_, v___x_1249_, v___x_1246_);
lean_dec_ref_known(v___x_1248_, 3);
v___x_1251_ = lean_nat_add(v___x_1247_, v___x_1250_);
lean_dec(v___x_1250_);
v___x_1252_ = lean_string_utf8_extract_fast(v_a_1236_, v___x_1247_, v___x_1251_);
lean_dec(v___x_1251_);
lean_dec(v___x_1247_);
lean_dec_ref(v_a_1236_);
v___x_1253_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__0));
v_ref_1254_ = l_Lean_replaceRef(v_x_1231_, v_ref_1242_);
lean_inc(v_currRecDepth_1241_);
lean_inc_ref(v_toCold_1240_);
v___x_1255_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1255_, 0, v_toCold_1240_);
lean_ctor_set(v___x_1255_, 1, v_currRecDepth_1241_);
lean_ctor_set(v___x_1255_, 2, v_ref_1254_);
lean_ctor_set_uint16(v___x_1255_, sizeof(void*)*3, v_optionFlags_1243_);
lean_ctor_set_uint8(v___x_1255_, sizeof(void*)*3 + 2, v_suppressElabErrors_1244_);
lean_ctor_set_uint8(v___x_1255_, sizeof(void*)*3 + 3, v_isRecordingDeps_1245_);
v___x_1256_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore(v___x_1252_, v___x_1237_, v___x_1253_, v___x_1255_, v_a_1233_);
lean_dec_ref_known(v___x_1255_, 3);
return v___x_1256_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___boxed(lean_object* v_x_1262_, lean_object* v_a_1263_, lean_object* v_a_1264_, lean_object* v_a_1265_){
_start:
{
lean_object* v_res_1266_; 
v_res_1266_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString(v_x_1262_, v_a_1263_, v_a_1264_);
lean_dec(v_a_1264_);
lean_dec_ref(v_a_1263_);
lean_dec(v_x_1262_);
return v_res_1266_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_dropInitialNewline(lean_object* v_s_1267_){
_start:
{
uint32_t v___y_1269_; lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; 
v___x_1286_ = lean_unsigned_to_nat(0u);
v___x_1287_ = lean_string_utf8_byte_size(v_s_1267_);
lean_inc_ref(v_s_1267_);
v___x_1288_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1288_, 0, v_s_1267_);
lean_ctor_set(v___x_1288_, 1, v___x_1286_);
lean_ctor_set(v___x_1288_, 2, v___x_1287_);
v___x_1289_ = l_String_Slice_Pos_get_x3f(v___x_1288_, v___x_1286_);
lean_dec_ref_known(v___x_1288_, 3);
if (lean_obj_tag(v___x_1289_) == 0)
{
uint32_t v___x_1290_; 
v___x_1290_ = 65;
v___y_1269_ = v___x_1290_;
goto v___jp_1268_;
}
else
{
lean_object* v_val_1291_; uint32_t v___x_1292_; 
v_val_1291_ = lean_ctor_get(v___x_1289_, 0);
lean_inc(v_val_1291_);
lean_dec_ref_known(v___x_1289_, 1);
v___x_1292_ = lean_unbox_uint32(v_val_1291_);
lean_dec(v_val_1291_);
v___y_1269_ = v___x_1292_;
goto v___jp_1268_;
}
v___jp_1268_:
{
uint32_t v___x_1270_; uint8_t v___x_1271_; 
v___x_1270_ = 13;
v___x_1271_ = lean_uint32_dec_eq(v___y_1269_, v___x_1270_);
if (v___x_1271_ == 0)
{
uint32_t v___x_1272_; uint8_t v___x_1273_; 
v___x_1272_ = 10;
v___x_1273_ = lean_uint32_dec_eq(v___y_1269_, v___x_1272_);
if (v___x_1273_ == 0)
{
return v_s_1267_;
}
else
{
lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; 
v___x_1274_ = lean_unsigned_to_nat(1u);
v___x_1275_ = lean_unsigned_to_nat(0u);
v___x_1276_ = lean_string_utf8_byte_size(v_s_1267_);
lean_inc_ref(v_s_1267_);
v___x_1277_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1277_, 0, v_s_1267_);
lean_ctor_set(v___x_1277_, 1, v___x_1275_);
lean_ctor_set(v___x_1277_, 2, v___x_1276_);
v___x_1278_ = l_String_Slice_Pos_nextn(v___x_1277_, v___x_1275_, v___x_1274_);
lean_dec_ref_known(v___x_1277_, 3);
v___x_1279_ = lean_string_utf8_extract_fast(v_s_1267_, v___x_1278_, v___x_1276_);
lean_dec(v___x_1278_);
lean_dec_ref(v_s_1267_);
return v___x_1279_;
}
}
else
{
lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; 
v___x_1280_ = lean_unsigned_to_nat(2u);
v___x_1281_ = lean_unsigned_to_nat(0u);
v___x_1282_ = lean_string_utf8_byte_size(v_s_1267_);
lean_inc_ref(v_s_1267_);
v___x_1283_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1283_, 0, v_s_1267_);
lean_ctor_set(v___x_1283_, 1, v___x_1281_);
lean_ctor_set(v___x_1283_, 2, v___x_1282_);
v___x_1284_ = l_String_Slice_Pos_nextn(v___x_1283_, v___x_1281_, v___x_1280_);
lean_dec_ref_known(v___x_1283_, 3);
v___x_1285_ = lean_string_utf8_extract_fast(v_s_1267_, v___x_1284_, v___x_1282_);
lean_dec(v___x_1284_);
lean_dec_ref(v_s_1267_);
return v___x_1285_;
}
}
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString___closed__4(void){
_start:
{
lean_object* v___x_1301_; lean_object* v___x_1302_; 
v___x_1301_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString___closed__3));
v___x_1302_ = l_Lean_MessageData_ofFormat(v___x_1301_);
return v___x_1302_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString(lean_object* v_x_1303_, lean_object* v_a_1304_, lean_object* v_a_1305_){
_start:
{
lean_object* v_a_1308_; lean_object* v___x_1321_; lean_object* v___x_1322_; 
v___x_1321_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString___closed__1));
v___x_1322_ = l_Lean_Syntax_isLit_x3f(v___x_1321_, v_x_1303_);
if (lean_obj_tag(v___x_1322_) == 1)
{
lean_object* v_val_1323_; 
v_val_1323_ = lean_ctor_get(v___x_1322_, 0);
lean_inc(v_val_1323_);
lean_dec_ref_known(v___x_1322_, 1);
v_a_1308_ = v_val_1323_;
goto v___jp_1307_;
}
else
{
lean_object* v___x_1324_; lean_object* v___x_1325_; 
lean_dec(v___x_1322_);
v___x_1324_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString___closed__4, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString___closed__4_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString___closed__4);
v___x_1325_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_x_1303_, v___x_1324_, v_a_1304_, v_a_1305_);
return v___x_1325_;
}
v___jp_1307_:
{
lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; 
v___x_1309_ = lean_unsigned_to_nat(3u);
v___x_1310_ = lean_unsigned_to_nat(0u);
v___x_1311_ = lean_string_utf8_byte_size(v_a_1308_);
lean_inc_ref_n(v_a_1308_, 2);
v___x_1312_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1312_, 0, v_a_1308_);
lean_ctor_set(v___x_1312_, 1, v___x_1310_);
lean_ctor_set(v___x_1312_, 2, v___x_1311_);
v___x_1313_ = l_String_Slice_Pos_nextn(v___x_1312_, v___x_1310_, v___x_1309_);
lean_dec_ref_known(v___x_1312_, 3);
lean_inc(v___x_1313_);
v___x_1314_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1314_, 0, v_a_1308_);
lean_ctor_set(v___x_1314_, 1, v___x_1313_);
lean_ctor_set(v___x_1314_, 2, v___x_1311_);
v___x_1315_ = lean_nat_sub(v___x_1311_, v___x_1313_);
v___x_1316_ = l_String_Slice_Pos_prevn(v___x_1314_, v___x_1315_, v___x_1309_);
lean_dec_ref_known(v___x_1314_, 3);
v___x_1317_ = lean_nat_add(v___x_1313_, v___x_1316_);
lean_dec(v___x_1316_);
v___x_1318_ = lean_string_utf8_extract_fast(v_a_1308_, v___x_1313_, v___x_1317_);
lean_dec(v___x_1317_);
lean_dec(v___x_1313_);
lean_dec_ref(v_a_1308_);
v___x_1319_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_dropInitialNewline(v___x_1318_);
v___x_1320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1320_, 0, v___x_1319_);
return v___x_1320_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString___boxed(lean_object* v_x_1326_, lean_object* v_a_1327_, lean_object* v_a_1328_, lean_object* v_a_1329_){
_start:
{
lean_object* v_res_1330_; 
v_res_1330_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString(v_x_1326_, v_a_1327_, v_a_1328_);
lean_dec(v_a_1328_);
lean_dec_ref(v_a_1327_);
lean_dec(v_x_1326_);
return v_res_1330_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString___closed__4(void){
_start:
{
lean_object* v___x_1339_; lean_object* v___x_1340_; 
v___x_1339_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString___closed__3));
v___x_1340_ = l_Lean_MessageData_ofFormat(v___x_1339_);
return v___x_1340_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString(lean_object* v_x_1341_, lean_object* v_a_1342_, lean_object* v_a_1343_){
_start:
{
lean_object* v_a_1346_; lean_object* v___x_1368_; lean_object* v___x_1369_; 
v___x_1368_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString___closed__1));
v___x_1369_ = l_Lean_Syntax_isLit_x3f(v___x_1368_, v_x_1341_);
if (lean_obj_tag(v___x_1369_) == 1)
{
lean_object* v_val_1370_; 
v_val_1370_ = lean_ctor_get(v___x_1369_, 0);
lean_inc(v_val_1370_);
lean_dec_ref_known(v___x_1369_, 1);
v_a_1346_ = v_val_1370_;
goto v___jp_1345_;
}
else
{
lean_object* v___x_1371_; lean_object* v___x_1372_; 
lean_dec(v___x_1369_);
v___x_1371_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString___closed__4, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString___closed__4_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString___closed__4);
v___x_1372_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_x_1341_, v___x_1371_, v_a_1342_, v_a_1343_);
return v___x_1372_;
}
v___jp_1345_:
{
lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v_toCold_1350_; lean_object* v_currRecDepth_1351_; lean_object* v_ref_1352_; uint16_t v_optionFlags_1353_; uint8_t v_suppressElabErrors_1354_; uint8_t v_isRecordingDeps_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v_ref_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; 
v___x_1347_ = lean_unsigned_to_nat(0u);
v___x_1348_ = lean_string_utf8_byte_size(v_a_1346_);
lean_inc_ref_n(v_a_1346_, 2);
v___x_1349_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1349_, 0, v_a_1346_);
lean_ctor_set(v___x_1349_, 1, v___x_1347_);
lean_ctor_set(v___x_1349_, 2, v___x_1348_);
v_toCold_1350_ = lean_ctor_get(v_a_1342_, 0);
v_currRecDepth_1351_ = lean_ctor_get(v_a_1342_, 1);
v_ref_1352_ = lean_ctor_get(v_a_1342_, 2);
v_optionFlags_1353_ = lean_ctor_get_uint16(v_a_1342_, sizeof(void*)*3);
v_suppressElabErrors_1354_ = lean_ctor_get_uint8(v_a_1342_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1355_ = lean_ctor_get_uint8(v_a_1342_, sizeof(void*)*3 + 3);
v___x_1356_ = lean_unsigned_to_nat(3u);
v___x_1357_ = l_String_Slice_Pos_nextn(v___x_1349_, v___x_1347_, v___x_1356_);
lean_dec_ref_known(v___x_1349_, 3);
lean_inc(v___x_1357_);
v___x_1358_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1358_, 0, v_a_1346_);
lean_ctor_set(v___x_1358_, 1, v___x_1357_);
lean_ctor_set(v___x_1358_, 2, v___x_1348_);
v___x_1359_ = lean_nat_sub(v___x_1348_, v___x_1357_);
v___x_1360_ = l_String_Slice_Pos_prevn(v___x_1358_, v___x_1359_, v___x_1356_);
lean_dec_ref_known(v___x_1358_, 3);
v___x_1361_ = lean_nat_add(v___x_1357_, v___x_1360_);
lean_dec(v___x_1360_);
v___x_1362_ = lean_string_utf8_extract_fast(v_a_1346_, v___x_1357_, v___x_1361_);
lean_dec(v___x_1361_);
lean_dec(v___x_1357_);
lean_dec_ref(v_a_1346_);
v___x_1363_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_dropInitialNewline(v___x_1362_);
v___x_1364_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__0));
v_ref_1365_ = l_Lean_replaceRef(v_x_1341_, v_ref_1352_);
lean_inc(v_currRecDepth_1351_);
lean_inc_ref(v_toCold_1350_);
v___x_1366_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1366_, 0, v_toCold_1350_);
lean_ctor_set(v___x_1366_, 1, v_currRecDepth_1351_);
lean_ctor_set(v___x_1366_, 2, v_ref_1365_);
lean_ctor_set_uint16(v___x_1366_, sizeof(void*)*3, v_optionFlags_1353_);
lean_ctor_set_uint8(v___x_1366_, sizeof(void*)*3 + 2, v_suppressElabErrors_1354_);
lean_ctor_set_uint8(v___x_1366_, sizeof(void*)*3 + 3, v_isRecordingDeps_1355_);
v___x_1367_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore(v___x_1363_, v___x_1347_, v___x_1364_, v___x_1366_, v_a_1343_);
lean_dec_ref_known(v___x_1366_, 3);
return v___x_1367_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString___boxed(lean_object* v_x_1373_, lean_object* v_a_1374_, lean_object* v_a_1375_, lean_object* v_a_1376_){
_start:
{
lean_object* v_res_1377_; 
v_res_1377_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString(v_x_1373_, v_a_1374_, v_a_1375_);
lean_dec(v_a_1375_);
lean_dec_ref(v_a_1374_);
lean_dec(v_x_1373_);
return v_res_1377_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString___closed__3(void){
_start:
{
lean_object* v___x_1384_; lean_object* v___x_1385_; 
v___x_1384_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString___closed__2));
v___x_1385_ = l_Lean_stringToMessageData(v___x_1384_);
return v___x_1385_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString(lean_object* v_x_1386_, lean_object* v_a_1387_, lean_object* v_a_1388_){
_start:
{
lean_object* v___x_1390_; uint8_t v___x_1391_; 
v___x_1390_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString___closed__1));
lean_inc(v_x_1386_);
v___x_1391_ = l_Lean_Syntax_isOfKind(v_x_1386_, v___x_1390_);
if (v___x_1391_ == 0)
{
lean_object* v___x_1392_; lean_object* v___x_1393_; 
v___x_1392_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString___closed__3, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString___closed__3_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString___closed__3);
v___x_1393_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_x_1386_, v___x_1392_, v_a_1387_, v_a_1388_);
lean_dec(v_x_1386_);
return v___x_1393_;
}
else
{
lean_object* v___x_1394_; lean_object* v_x_1395_; lean_object* v___x_1396_; uint8_t v___x_1397_; 
v___x_1394_ = lean_unsigned_to_nat(0u);
v_x_1395_ = l_Lean_Syntax_getArg(v_x_1386_, v___x_1394_);
v___x_1396_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString___closed__1));
lean_inc(v_x_1395_);
v___x_1397_ = l_Lean_Syntax_isOfKind(v_x_1395_, v___x_1396_);
if (v___x_1397_ == 0)
{
lean_object* v___x_1398_; uint8_t v___x_1399_; 
v___x_1398_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__2));
lean_inc(v_x_1395_);
v___x_1399_ = l_Lean_Syntax_isOfKind(v_x_1395_, v___x_1398_);
if (v___x_1399_ == 0)
{
lean_object* v___x_1400_; uint8_t v___x_1401_; 
v___x_1400_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString___closed__1));
lean_inc(v_x_1395_);
v___x_1401_ = l_Lean_Syntax_isOfKind(v_x_1395_, v___x_1400_);
if (v___x_1401_ == 0)
{
lean_object* v___x_1402_; uint8_t v___x_1403_; 
v___x_1402_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString___closed__1));
lean_inc(v_x_1395_);
v___x_1403_ = l_Lean_Syntax_isOfKind(v_x_1395_, v___x_1402_);
if (v___x_1403_ == 0)
{
lean_object* v___x_1404_; lean_object* v___x_1405_; 
lean_dec(v_x_1395_);
v___x_1404_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString___closed__3, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString___closed__3_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString___closed__3);
v___x_1405_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_x_1386_, v___x_1404_, v_a_1387_, v_a_1388_);
lean_dec(v_x_1386_);
return v___x_1405_;
}
else
{
lean_object* v___x_1406_; 
lean_dec(v_x_1386_);
v___x_1406_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlBasicString(v_x_1395_, v_a_1387_, v_a_1388_);
lean_dec(v_x_1395_);
return v___x_1406_;
}
}
else
{
lean_object* v___x_1407_; 
lean_dec(v_x_1386_);
v___x_1407_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabMlLiteralString(v_x_1395_, v_a_1387_, v_a_1388_);
lean_dec(v_x_1395_);
return v___x_1407_;
}
}
else
{
lean_object* v___x_1408_; 
lean_dec(v_x_1386_);
v___x_1408_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString(v_x_1395_, v_a_1387_, v_a_1388_);
lean_dec(v_x_1395_);
return v___x_1408_;
}
}
else
{
lean_object* v___x_1409_; 
lean_dec(v_x_1386_);
v___x_1409_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString(v_x_1395_, v_a_1387_, v_a_1388_);
lean_dec(v_x_1395_);
return v___x_1409_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString___boxed(lean_object* v_x_1410_, lean_object* v_a_1411_, lean_object* v_a_1412_, lean_object* v_a_1413_){
_start:
{
lean_object* v_res_1414_; 
v_res_1414_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString(v_x_1410_, v_a_1411_, v_a_1412_);
lean_dec(v_a_1412_);
lean_dec_ref(v_a_1411_);
return v_res_1414_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__4(void){
_start:
{
lean_object* v___x_1423_; lean_object* v___x_1424_; 
v___x_1423_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__3));
v___x_1424_ = l_Lean_MessageData_ofFormat(v___x_1423_);
return v___x_1424_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey(lean_object* v_x_1425_, lean_object* v_a_1426_, lean_object* v_a_1427_){
_start:
{
lean_object* v___x_1429_; lean_object* v_toApplicative_1430_; lean_object* v_toFunctor_1431_; lean_object* v_toSeq_1432_; lean_object* v_toSeqLeft_1433_; lean_object* v_toSeqRight_1434_; lean_object* v___x_1435_; lean_object* v___f_1436_; lean_object* v___f_1437_; lean_object* v___f_1438_; lean_object* v___f_1439_; lean_object* v___x_1440_; lean_object* v___f_1441_; lean_object* v___f_1442_; lean_object* v___f_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; 
v___x_1429_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__1, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__1_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__1);
v_toApplicative_1430_ = lean_ctor_get(v___x_1429_, 0);
v_toFunctor_1431_ = lean_ctor_get(v_toApplicative_1430_, 0);
v_toSeq_1432_ = lean_ctor_get(v_toApplicative_1430_, 2);
v_toSeqLeft_1433_ = lean_ctor_get(v_toApplicative_1430_, 3);
v_toSeqRight_1434_ = lean_ctor_get(v_toApplicative_1430_, 4);
v___x_1435_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__1));
v___f_1436_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__2));
v___f_1437_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLit___closed__3));
lean_inc_ref_n(v_toFunctor_1431_, 2);
v___f_1438_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1438_, 0, v_toFunctor_1431_);
v___f_1439_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1439_, 0, v_toFunctor_1431_);
v___x_1440_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1440_, 0, v___f_1438_);
lean_ctor_set(v___x_1440_, 1, v___f_1439_);
lean_inc(v_toSeqRight_1434_);
v___f_1441_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1441_, 0, v_toSeqRight_1434_);
lean_inc(v_toSeqLeft_1433_);
v___f_1442_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1442_, 0, v_toSeqLeft_1433_);
lean_inc(v_toSeq_1432_);
v___f_1443_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1443_, 0, v_toSeq_1432_);
v___x_1444_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1444_, 0, v___x_1440_);
lean_ctor_set(v___x_1444_, 1, v___f_1436_);
lean_ctor_set(v___x_1444_, 2, v___f_1443_);
lean_ctor_set(v___x_1444_, 3, v___f_1442_);
lean_ctor_set(v___x_1444_, 4, v___f_1441_);
v___x_1445_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1445_, 0, v___x_1444_);
lean_ctor_set(v___x_1445_, 1, v___f_1437_);
v___x_1446_ = l_Lean_instMonadExceptOfExceptionCoreM;
v___x_1447_ = l_Lean_Core_instMonadRefCoreM;
v___x_1448_ = l_Lean_Core_instAddMessageContextCoreM;
lean_inc_ref(v___x_1445_);
v___x_1449_ = l_Lean_instAddErrorMessageContextOfAddMessageContextOfMonad___redArg(v___x_1448_, v___x_1445_);
v___x_1450_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1450_, 0, v___x_1446_);
lean_ctor_set(v___x_1450_, 1, v___x_1447_);
lean_ctor_set(v___x_1450_, 2, v___x_1449_);
v___x_1451_ = l_Lean_Syntax_isLit_x3f(v___x_1435_, v_x_1425_);
if (lean_obj_tag(v___x_1451_) == 1)
{
lean_object* v_val_1452_; lean_object* v___x_1454_; uint8_t v_isShared_1455_; uint8_t v_isSharedCheck_1459_; 
lean_dec_ref_known(v___x_1450_, 3);
lean_dec_ref_known(v___x_1445_, 2);
lean_dec(v_x_1425_);
v_val_1452_ = lean_ctor_get(v___x_1451_, 0);
v_isSharedCheck_1459_ = !lean_is_exclusive(v___x_1451_);
if (v_isSharedCheck_1459_ == 0)
{
v___x_1454_ = v___x_1451_;
v_isShared_1455_ = v_isSharedCheck_1459_;
goto v_resetjp_1453_;
}
else
{
lean_inc(v_val_1452_);
lean_dec(v___x_1451_);
v___x_1454_ = lean_box(0);
v_isShared_1455_ = v_isSharedCheck_1459_;
goto v_resetjp_1453_;
}
v_resetjp_1453_:
{
lean_object* v___x_1457_; 
if (v_isShared_1455_ == 0)
{
lean_ctor_set_tag(v___x_1454_, 0);
v___x_1457_ = v___x_1454_;
goto v_reusejp_1456_;
}
else
{
lean_object* v_reuseFailAlloc_1458_; 
v_reuseFailAlloc_1458_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1458_, 0, v_val_1452_);
v___x_1457_ = v_reuseFailAlloc_1458_;
goto v_reusejp_1456_;
}
v_reusejp_1456_:
{
return v___x_1457_;
}
}
}
else
{
lean_object* v___x_1460_; lean_object* v___x_40__overap_1461_; lean_object* v___x_1462_; 
lean_dec(v___x_1451_);
v___x_1460_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__4, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__4_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__4);
v___x_40__overap_1461_ = l_Lean_throwErrorAt___redArg(v___x_1445_, v___x_1450_, v_x_1425_, v___x_1460_);
lean_inc(v_a_1427_);
lean_inc_ref(v_a_1426_);
v___x_1462_ = lean_apply_3(v___x_40__overap_1461_, v_a_1426_, v_a_1427_, lean_box(0));
return v___x_1462_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___boxed(lean_object* v_x_1463_, lean_object* v_a_1464_, lean_object* v_a_1465_, lean_object* v_a_1466_){
_start:
{
lean_object* v_res_1467_; 
v_res_1467_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey(v_x_1463_, v_a_1464_, v_a_1465_);
lean_dec(v_a_1465_);
lean_dec_ref(v_a_1464_);
return v_res_1467_;
}
}
static lean_object* _init_l_Lake_Toml_elabSimpleKey___closed__3(void){
_start:
{
lean_object* v___x_1474_; lean_object* v___x_1475_; 
v___x_1474_ = ((lean_object*)(l_Lake_Toml_elabSimpleKey___closed__2));
v___x_1475_ = l_Lean_stringToMessageData(v___x_1474_);
return v___x_1475_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_elabSimpleKey(lean_object* v_x_1476_, lean_object* v_a_1477_, lean_object* v_a_1478_){
_start:
{
lean_object* v___x_1480_; uint8_t v___x_1481_; 
v___x_1480_ = ((lean_object*)(l_Lake_Toml_elabSimpleKey___closed__1));
lean_inc(v_x_1476_);
v___x_1481_ = l_Lean_Syntax_isOfKind(v_x_1476_, v___x_1480_);
if (v___x_1481_ == 0)
{
lean_object* v___x_1482_; lean_object* v___x_1483_; 
v___x_1482_ = lean_obj_once(&l_Lake_Toml_elabSimpleKey___closed__3, &l_Lake_Toml_elabSimpleKey___closed__3_once, _init_l_Lake_Toml_elabSimpleKey___closed__3);
v___x_1483_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_x_1476_, v___x_1482_, v_a_1477_, v_a_1478_);
lean_dec(v_x_1476_);
return v___x_1483_;
}
else
{
lean_object* v___x_1484_; lean_object* v_x_1485_; lean_object* v___x_1486_; uint8_t v___x_1487_; 
v___x_1484_ = lean_unsigned_to_nat(0u);
v_x_1485_ = l_Lean_Syntax_getArg(v_x_1476_, v___x_1484_);
v___x_1486_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__1));
lean_inc(v_x_1485_);
v___x_1487_ = l_Lean_Syntax_isOfKind(v_x_1485_, v___x_1486_);
if (v___x_1487_ == 0)
{
lean_object* v___x_1488_; uint8_t v___x_1489_; 
v___x_1488_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString___closed__1));
lean_inc(v_x_1485_);
v___x_1489_ = l_Lean_Syntax_isOfKind(v_x_1485_, v___x_1488_);
if (v___x_1489_ == 0)
{
lean_object* v___x_1490_; uint8_t v___x_1491_; 
v___x_1490_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString___closed__2));
lean_inc(v_x_1485_);
v___x_1491_ = l_Lean_Syntax_isOfKind(v_x_1485_, v___x_1490_);
if (v___x_1491_ == 0)
{
lean_object* v___x_1492_; lean_object* v___x_1493_; 
lean_dec(v_x_1485_);
v___x_1492_ = lean_obj_once(&l_Lake_Toml_elabSimpleKey___closed__3, &l_Lake_Toml_elabSimpleKey___closed__3_once, _init_l_Lake_Toml_elabSimpleKey___closed__3);
v___x_1493_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_x_1476_, v___x_1492_, v_a_1477_, v_a_1478_);
lean_dec(v_x_1476_);
return v___x_1493_;
}
else
{
lean_object* v___x_1494_; 
lean_dec(v_x_1476_);
v___x_1494_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicString(v_x_1485_, v_a_1477_, v_a_1478_);
lean_dec(v_x_1485_);
return v___x_1494_;
}
}
else
{
lean_object* v___x_1495_; 
lean_dec(v_x_1476_);
v___x_1495_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabLiteralString(v_x_1485_, v_a_1477_, v_a_1478_);
lean_dec(v_x_1485_);
return v___x_1495_;
}
}
else
{
lean_object* v___x_1496_; 
lean_dec(v_x_1476_);
v___x_1496_ = l_Lean_Syntax_isLit_x3f(v___x_1486_, v_x_1485_);
if (lean_obj_tag(v___x_1496_) == 1)
{
lean_object* v_val_1497_; lean_object* v___x_1499_; uint8_t v_isShared_1500_; uint8_t v_isSharedCheck_1504_; 
lean_dec(v_x_1485_);
v_val_1497_ = lean_ctor_get(v___x_1496_, 0);
v_isSharedCheck_1504_ = !lean_is_exclusive(v___x_1496_);
if (v_isSharedCheck_1504_ == 0)
{
v___x_1499_ = v___x_1496_;
v_isShared_1500_ = v_isSharedCheck_1504_;
goto v_resetjp_1498_;
}
else
{
lean_inc(v_val_1497_);
lean_dec(v___x_1496_);
v___x_1499_ = lean_box(0);
v_isShared_1500_ = v_isSharedCheck_1504_;
goto v_resetjp_1498_;
}
v_resetjp_1498_:
{
lean_object* v___x_1502_; 
if (v_isShared_1500_ == 0)
{
lean_ctor_set_tag(v___x_1499_, 0);
v___x_1502_ = v___x_1499_;
goto v_reusejp_1501_;
}
else
{
lean_object* v_reuseFailAlloc_1503_; 
v_reuseFailAlloc_1503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1503_, 0, v_val_1497_);
v___x_1502_ = v_reuseFailAlloc_1503_;
goto v_reusejp_1501_;
}
v_reusejp_1501_:
{
return v___x_1502_;
}
}
}
else
{
lean_object* v___x_1505_; lean_object* v___x_1506_; 
lean_dec(v___x_1496_);
v___x_1505_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__4, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__4_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabUnquotedKey___closed__4);
v___x_1506_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_x_1485_, v___x_1505_, v_a_1477_, v_a_1478_);
lean_dec(v_x_1485_);
return v___x_1506_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_elabSimpleKey___boxed(lean_object* v_x_1507_, lean_object* v_a_1508_, lean_object* v_a_1509_, lean_object* v_a_1510_){
_start:
{
lean_object* v_res_1511_; 
v_res_1511_ = l_Lake_Toml_elabSimpleKey(v_x_1507_, v_a_1508_, v_a_1509_);
lean_dec(v_a_1509_);
lean_dec_ref(v_a_1508_);
return v_res_1511_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray_spec__0___redArg(lean_object* v_elabVal_1512_, size_t v_sz_1513_, size_t v_i_1514_, lean_object* v_bs_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_){
_start:
{
uint8_t v___x_1519_; 
v___x_1519_ = lean_usize_dec_lt(v_i_1514_, v_sz_1513_);
if (v___x_1519_ == 0)
{
lean_object* v___x_1520_; 
lean_dec_ref(v_elabVal_1512_);
v___x_1520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1520_, 0, v_bs_1515_);
return v___x_1520_;
}
else
{
lean_object* v_v_1521_; lean_object* v___x_1522_; lean_object* v_bs_x27_1523_; lean_object* v___x_1524_; 
v_v_1521_ = lean_array_uget(v_bs_1515_, v_i_1514_);
v___x_1522_ = lean_unsigned_to_nat(0u);
v_bs_x27_1523_ = lean_array_uset(v_bs_1515_, v_i_1514_, v___x_1522_);
lean_inc_ref(v_elabVal_1512_);
lean_inc(v___y_1517_);
lean_inc_ref(v___y_1516_);
v___x_1524_ = lean_apply_4(v_elabVal_1512_, v_v_1521_, v___y_1516_, v___y_1517_, lean_box(0));
if (lean_obj_tag(v___x_1524_) == 0)
{
lean_object* v_a_1525_; size_t v___x_1526_; size_t v___x_1527_; lean_object* v___x_1528_; 
v_a_1525_ = lean_ctor_get(v___x_1524_, 0);
lean_inc(v_a_1525_);
lean_dec_ref_known(v___x_1524_, 1);
v___x_1526_ = ((size_t)1ULL);
v___x_1527_ = lean_usize_add(v_i_1514_, v___x_1526_);
v___x_1528_ = lean_array_uset(v_bs_x27_1523_, v_i_1514_, v_a_1525_);
v_i_1514_ = v___x_1527_;
v_bs_1515_ = v___x_1528_;
goto _start;
}
else
{
lean_object* v_a_1530_; lean_object* v___x_1532_; uint8_t v_isShared_1533_; uint8_t v_isSharedCheck_1537_; 
lean_dec_ref(v_bs_x27_1523_);
lean_dec_ref(v_elabVal_1512_);
v_a_1530_ = lean_ctor_get(v___x_1524_, 0);
v_isSharedCheck_1537_ = !lean_is_exclusive(v___x_1524_);
if (v_isSharedCheck_1537_ == 0)
{
v___x_1532_ = v___x_1524_;
v_isShared_1533_ = v_isSharedCheck_1537_;
goto v_resetjp_1531_;
}
else
{
lean_inc(v_a_1530_);
lean_dec(v___x_1524_);
v___x_1532_ = lean_box(0);
v_isShared_1533_ = v_isSharedCheck_1537_;
goto v_resetjp_1531_;
}
v_resetjp_1531_:
{
lean_object* v___x_1535_; 
if (v_isShared_1533_ == 0)
{
v___x_1535_ = v___x_1532_;
goto v_reusejp_1534_;
}
else
{
lean_object* v_reuseFailAlloc_1536_; 
v_reuseFailAlloc_1536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1536_, 0, v_a_1530_);
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
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray_spec__0___redArg___boxed(lean_object* v_elabVal_1538_, lean_object* v_sz_1539_, lean_object* v_i_1540_, lean_object* v_bs_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_){
_start:
{
size_t v_sz_boxed_1545_; size_t v_i_boxed_1546_; lean_object* v_res_1547_; 
v_sz_boxed_1545_ = lean_unbox_usize(v_sz_1539_);
lean_dec(v_sz_1539_);
v_i_boxed_1546_ = lean_unbox_usize(v_i_1540_);
lean_dec(v_i_1540_);
v_res_1547_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray_spec__0___redArg(v_elabVal_1538_, v_sz_boxed_1545_, v_i_boxed_1546_, v_bs_1541_, v___y_1542_, v___y_1543_);
lean_dec(v___y_1543_);
lean_dec_ref(v___y_1542_);
return v_res_1547_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg___closed__3(void){
_start:
{
lean_object* v___x_1554_; lean_object* v___x_1555_; 
v___x_1554_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg___closed__2));
v___x_1555_ = l_Lean_stringToMessageData(v___x_1554_);
return v___x_1555_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg(lean_object* v_x_1556_, lean_object* v_elabVal_1557_, lean_object* v_a_1558_, lean_object* v_a_1559_){
_start:
{
lean_object* v___x_1561_; uint8_t v___x_1562_; 
v___x_1561_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg___closed__1));
lean_inc(v_x_1556_);
v___x_1562_ = l_Lean_Syntax_isOfKind(v_x_1556_, v___x_1561_);
if (v___x_1562_ == 0)
{
lean_object* v___x_1563_; lean_object* v___x_1564_; 
lean_dec_ref(v_elabVal_1557_);
v___x_1563_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg___closed__3, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg___closed__3_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg___closed__3);
v___x_1564_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_x_1556_, v___x_1563_, v_a_1558_, v_a_1559_);
lean_dec(v_x_1556_);
return v___x_1564_;
}
else
{
lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v_xs_1567_; lean_object* v___x_1568_; size_t v_sz_1569_; size_t v___x_1570_; lean_object* v___x_1571_; 
v___x_1565_ = lean_unsigned_to_nat(1u);
v___x_1566_ = l_Lean_Syntax_getArg(v_x_1556_, v___x_1565_);
lean_dec(v_x_1556_);
v_xs_1567_ = l_Lean_Syntax_getArgs(v___x_1566_);
lean_dec(v___x_1566_);
v___x_1568_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_xs_1567_);
lean_dec_ref(v_xs_1567_);
v_sz_1569_ = lean_array_size(v___x_1568_);
v___x_1570_ = ((size_t)0ULL);
v___x_1571_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray_spec__0___redArg(v_elabVal_1557_, v_sz_1569_, v___x_1570_, v___x_1568_, v_a_1558_, v_a_1559_);
return v___x_1571_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg___boxed(lean_object* v_x_1572_, lean_object* v_elabVal_1573_, lean_object* v_a_1574_, lean_object* v_a_1575_, lean_object* v_a_1576_){
_start:
{
lean_object* v_res_1577_; 
v_res_1577_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg(v_x_1572_, v_elabVal_1573_, v_a_1574_, v_a_1575_);
lean_dec(v_a_1575_);
lean_dec_ref(v_a_1574_);
return v_res_1577_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray(lean_object* v_00_u03b1_1578_, lean_object* v_x_1579_, lean_object* v_elabVal_1580_, lean_object* v_a_1581_, lean_object* v_a_1582_){
_start:
{
lean_object* v___x_1584_; 
v___x_1584_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg(v_x_1579_, v_elabVal_1580_, v_a_1581_, v_a_1582_);
return v___x_1584_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___boxed(lean_object* v_00_u03b1_1585_, lean_object* v_x_1586_, lean_object* v_elabVal_1587_, lean_object* v_a_1588_, lean_object* v_a_1589_, lean_object* v_a_1590_){
_start:
{
lean_object* v_res_1591_; 
v_res_1591_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray(v_00_u03b1_1585_, v_x_1586_, v_elabVal_1587_, v_a_1588_, v_a_1589_);
lean_dec(v_a_1589_);
lean_dec_ref(v_a_1588_);
return v_res_1591_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray_spec__0(lean_object* v_00_u03b1_1592_, lean_object* v_elabVal_1593_, size_t v_sz_1594_, size_t v_i_1595_, lean_object* v_bs_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_){
_start:
{
lean_object* v___x_1600_; 
v___x_1600_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray_spec__0___redArg(v_elabVal_1593_, v_sz_1594_, v_i_1595_, v_bs_1596_, v___y_1597_, v___y_1598_);
return v___x_1600_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray_spec__0___boxed(lean_object* v_00_u03b1_1601_, lean_object* v_elabVal_1602_, lean_object* v_sz_1603_, lean_object* v_i_1604_, lean_object* v_bs_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_){
_start:
{
size_t v_sz_boxed_1609_; size_t v_i_boxed_1610_; lean_object* v_res_1611_; 
v_sz_boxed_1609_ = lean_unbox_usize(v_sz_1603_);
lean_dec(v_sz_1603_);
v_i_boxed_1610_ = lean_unbox_usize(v_i_1604_);
lean_dec(v_i_1604_);
v_res_1611_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray_spec__0(v_00_u03b1_1601_, v_elabVal_1602_, v_sz_boxed_1609_, v_i_boxed_1610_, v_bs_1605_, v___y_1606_, v___y_1607_);
lean_dec(v___y_1607_);
lean_dec_ref(v___y_1606_);
return v_res_1611_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__1(size_t v_sz_1612_, size_t v_i_1613_, lean_object* v_bs_1614_){
_start:
{
uint8_t v___x_1615_; 
v___x_1615_ = lean_usize_dec_lt(v_i_1613_, v_sz_1612_);
if (v___x_1615_ == 0)
{
lean_object* v___x_1616_; 
v___x_1616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1616_, 0, v_bs_1614_);
return v___x_1616_;
}
else
{
lean_object* v_v_1617_; lean_object* v___x_1618_; lean_object* v_bs_x27_1619_; size_t v___x_1620_; size_t v___x_1621_; lean_object* v___x_1622_; 
v_v_1617_ = lean_array_uget(v_bs_1614_, v_i_1613_);
v___x_1618_ = lean_unsigned_to_nat(0u);
v_bs_x27_1619_ = lean_array_uset(v_bs_1614_, v_i_1613_, v___x_1618_);
v___x_1620_ = ((size_t)1ULL);
v___x_1621_ = lean_usize_add(v_i_1613_, v___x_1620_);
v___x_1622_ = lean_array_uset(v_bs_x27_1619_, v_i_1613_, v_v_1617_);
v_i_1613_ = v___x_1621_;
v_bs_1614_ = v___x_1622_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__1___boxed(lean_object* v_sz_1624_, lean_object* v_i_1625_, lean_object* v_bs_1626_){
_start:
{
size_t v_sz_boxed_1627_; size_t v_i_boxed_1628_; lean_object* v_res_1629_; 
v_sz_boxed_1627_ = lean_unbox_usize(v_sz_1624_);
lean_dec(v_sz_1624_);
v_i_boxed_1628_ = lean_unbox_usize(v_i_1625_);
lean_dec(v_i_1625_);
v_res_1629_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__1(v_sz_boxed_1627_, v_i_boxed_1628_, v_bs_1626_);
return v_res_1629_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__0_spec__0___redArg(lean_object* v_msg_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_){
_start:
{
lean_object* v_ref_1634_; lean_object* v___x_1635_; lean_object* v_a_1636_; lean_object* v___x_1638_; uint8_t v_isShared_1639_; uint8_t v_isSharedCheck_1644_; 
v_ref_1634_ = lean_ctor_get(v___y_1631_, 2);
v___x_1635_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0_spec__0_spec__1(v_msg_1630_, v___y_1631_, v___y_1632_);
v_a_1636_ = lean_ctor_get(v___x_1635_, 0);
v_isSharedCheck_1644_ = !lean_is_exclusive(v___x_1635_);
if (v_isSharedCheck_1644_ == 0)
{
v___x_1638_ = v___x_1635_;
v_isShared_1639_ = v_isSharedCheck_1644_;
goto v_resetjp_1637_;
}
else
{
lean_inc(v_a_1636_);
lean_dec(v___x_1635_);
v___x_1638_ = lean_box(0);
v_isShared_1639_ = v_isSharedCheck_1644_;
goto v_resetjp_1637_;
}
v_resetjp_1637_:
{
lean_object* v___x_1640_; lean_object* v___x_1642_; 
lean_inc(v_ref_1634_);
v___x_1640_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1640_, 0, v_ref_1634_);
lean_ctor_set(v___x_1640_, 1, v_a_1636_);
if (v_isShared_1639_ == 0)
{
lean_ctor_set_tag(v___x_1638_, 1);
lean_ctor_set(v___x_1638_, 0, v___x_1640_);
v___x_1642_ = v___x_1638_;
goto v_reusejp_1641_;
}
else
{
lean_object* v_reuseFailAlloc_1643_; 
v_reuseFailAlloc_1643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1643_, 0, v___x_1640_);
v___x_1642_ = v_reuseFailAlloc_1643_;
goto v_reusejp_1641_;
}
v_reusejp_1641_:
{
return v___x_1642_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__0_spec__0___redArg___boxed(lean_object* v_msg_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_){
_start:
{
lean_object* v_res_1649_; 
v_res_1649_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__0_spec__0___redArg(v_msg_1645_, v___y_1646_, v___y_1647_);
lean_dec(v___y_1647_);
lean_dec_ref(v___y_1646_);
return v_res_1649_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__0___redArg(lean_object* v_ref_1650_, lean_object* v_msg_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_){
_start:
{
lean_object* v_toCold_1656_; lean_object* v_currRecDepth_1657_; lean_object* v_ref_1658_; uint16_t v_optionFlags_1659_; uint8_t v_suppressElabErrors_1660_; uint8_t v_isRecordingDeps_1661_; lean_object* v_ref_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; 
v_toCold_1656_ = lean_ctor_get(v___y_1653_, 0);
v_currRecDepth_1657_ = lean_ctor_get(v___y_1653_, 1);
v_ref_1658_ = lean_ctor_get(v___y_1653_, 2);
v_optionFlags_1659_ = lean_ctor_get_uint16(v___y_1653_, sizeof(void*)*3);
v_suppressElabErrors_1660_ = lean_ctor_get_uint8(v___y_1653_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1661_ = lean_ctor_get_uint8(v___y_1653_, sizeof(void*)*3 + 3);
v_ref_1662_ = l_Lean_replaceRef(v_ref_1650_, v_ref_1658_);
lean_inc(v_currRecDepth_1657_);
lean_inc_ref(v_toCold_1656_);
v___x_1663_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1663_, 0, v_toCold_1656_);
lean_ctor_set(v___x_1663_, 1, v_currRecDepth_1657_);
lean_ctor_set(v___x_1663_, 2, v_ref_1662_);
lean_ctor_set_uint16(v___x_1663_, sizeof(void*)*3, v_optionFlags_1659_);
lean_ctor_set_uint8(v___x_1663_, sizeof(void*)*3 + 2, v_suppressElabErrors_1660_);
lean_ctor_set_uint8(v___x_1663_, sizeof(void*)*3 + 3, v_isRecordingDeps_1661_);
v___x_1664_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__0_spec__0___redArg(v_msg_1651_, v___x_1663_, v___y_1654_);
lean_dec_ref_known(v___x_1663_, 3);
return v___x_1664_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__0___redArg___boxed(lean_object* v_ref_1665_, lean_object* v_msg_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_){
_start:
{
lean_object* v_res_1671_; 
v_res_1671_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__0___redArg(v_ref_1665_, v_msg_1666_, v___y_1667_, v___y_1668_, v___y_1669_);
lean_dec(v___y_1669_);
lean_dec_ref(v___y_1668_);
lean_dec_ref(v___y_1667_);
lean_dec(v_ref_1665_);
return v_res_1671_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___closed__2(void){
_start:
{
lean_object* v___x_1674_; lean_object* v___x_1675_; 
v___x_1674_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___closed__1));
v___x_1675_ = l_Lean_stringToMessageData(v___x_1674_);
return v___x_1675_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2(lean_object* v_t_1676_, uint8_t v___x_1677_, lean_object* v_as_1678_, size_t v_i_1679_, size_t v_stop_1680_, lean_object* v_b_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_){
_start:
{
lean_object* v_fst_1687_; lean_object* v_snd_1688_; uint8_t v___x_1692_; 
v___x_1692_ = lean_usize_dec_eq(v_i_1679_, v_stop_1680_);
if (v___x_1692_ == 0)
{
lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; 
v___x_1693_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___closed__0));
v___x_1694_ = lean_array_uget_borrowed(v_as_1678_, v_i_1679_);
lean_inc(v___x_1694_);
v___x_1695_ = l_Lake_Toml_elabSimpleKey(v___x_1694_, v___y_1683_, v___y_1684_);
if (lean_obj_tag(v___x_1695_) == 0)
{
lean_object* v_a_1696_; lean_object* v___x_1697_; lean_object* v___x_1715_; 
v_a_1696_ = lean_ctor_get(v___x_1695_, 0);
lean_inc(v_a_1696_);
lean_dec_ref_known(v___x_1695_, 1);
v___x_1697_ = l_Lean_Name_str___override(v_b_1681_, v_a_1696_);
lean_inc_ref(v_t_1676_);
lean_inc(v___x_1697_);
v___x_1715_ = l_Lake_Toml_RBDict_findEntry_x3f___redArg(v___x_1693_, v___x_1697_, v_t_1676_);
if (lean_obj_tag(v___x_1715_) == 0)
{
lean_object* v___x_1716_; lean_object* v___x_1717_; 
v___x_1716_ = lean_box(0);
lean_inc(v___x_1697_);
v___x_1717_ = l_Lake_Toml_RBDict_push___redArg(v___x_1693_, v___x_1697_, v___x_1716_, v___y_1682_);
v_fst_1687_ = v___x_1697_;
v_snd_1688_ = v___x_1717_;
goto v___jp_1686_;
}
else
{
lean_object* v_val_1718_; lean_object* v_snd_1719_; 
v_val_1718_ = lean_ctor_get(v___x_1715_, 0);
lean_inc(v_val_1718_);
lean_dec_ref_known(v___x_1715_, 1);
v_snd_1719_ = lean_ctor_get(v_val_1718_, 1);
lean_inc(v_snd_1719_);
lean_dec(v_val_1718_);
if (lean_obj_tag(v_snd_1719_) == 0)
{
if (v___x_1677_ == 0)
{
goto v___jp_1698_;
}
else
{
v_fst_1687_ = v___x_1697_;
v_snd_1688_ = v___y_1682_;
goto v___jp_1686_;
}
}
else
{
lean_dec_ref_known(v_snd_1719_, 1);
goto v___jp_1698_;
}
}
v___jp_1698_:
{
lean_object* v___x_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; 
v___x_1699_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___closed__2, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___closed__2);
lean_inc(v___x_1697_);
v___x_1700_ = l_Lean_MessageData_ofName(v___x_1697_);
v___x_1701_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1701_, 0, v___x_1699_);
lean_ctor_set(v___x_1701_, 1, v___x_1700_);
v___x_1702_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__3, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__3_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__3);
v___x_1703_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1703_, 0, v___x_1701_);
lean_ctor_set(v___x_1703_, 1, v___x_1702_);
v___x_1704_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__0___redArg(v___x_1694_, v___x_1703_, v___y_1682_, v___y_1683_, v___y_1684_);
lean_dec_ref(v___y_1682_);
if (lean_obj_tag(v___x_1704_) == 0)
{
lean_object* v_a_1705_; lean_object* v_snd_1706_; 
v_a_1705_ = lean_ctor_get(v___x_1704_, 0);
lean_inc(v_a_1705_);
lean_dec_ref_known(v___x_1704_, 1);
v_snd_1706_ = lean_ctor_get(v_a_1705_, 1);
lean_inc(v_snd_1706_);
lean_dec(v_a_1705_);
v_fst_1687_ = v___x_1697_;
v_snd_1688_ = v_snd_1706_;
goto v___jp_1686_;
}
else
{
lean_object* v_a_1707_; lean_object* v___x_1709_; uint8_t v_isShared_1710_; uint8_t v_isSharedCheck_1714_; 
lean_dec(v___x_1697_);
lean_dec_ref(v_t_1676_);
v_a_1707_ = lean_ctor_get(v___x_1704_, 0);
v_isSharedCheck_1714_ = !lean_is_exclusive(v___x_1704_);
if (v_isSharedCheck_1714_ == 0)
{
v___x_1709_ = v___x_1704_;
v_isShared_1710_ = v_isSharedCheck_1714_;
goto v_resetjp_1708_;
}
else
{
lean_inc(v_a_1707_);
lean_dec(v___x_1704_);
v___x_1709_ = lean_box(0);
v_isShared_1710_ = v_isSharedCheck_1714_;
goto v_resetjp_1708_;
}
v_resetjp_1708_:
{
lean_object* v___x_1712_; 
if (v_isShared_1710_ == 0)
{
v___x_1712_ = v___x_1709_;
goto v_reusejp_1711_;
}
else
{
lean_object* v_reuseFailAlloc_1713_; 
v_reuseFailAlloc_1713_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1713_, 0, v_a_1707_);
v___x_1712_ = v_reuseFailAlloc_1713_;
goto v_reusejp_1711_;
}
v_reusejp_1711_:
{
return v___x_1712_;
}
}
}
}
}
else
{
lean_object* v_a_1720_; lean_object* v___x_1722_; uint8_t v_isShared_1723_; uint8_t v_isSharedCheck_1727_; 
lean_dec_ref(v___y_1682_);
lean_dec(v_b_1681_);
lean_dec_ref(v_t_1676_);
v_a_1720_ = lean_ctor_get(v___x_1695_, 0);
v_isSharedCheck_1727_ = !lean_is_exclusive(v___x_1695_);
if (v_isSharedCheck_1727_ == 0)
{
v___x_1722_ = v___x_1695_;
v_isShared_1723_ = v_isSharedCheck_1727_;
goto v_resetjp_1721_;
}
else
{
lean_inc(v_a_1720_);
lean_dec(v___x_1695_);
v___x_1722_ = lean_box(0);
v_isShared_1723_ = v_isSharedCheck_1727_;
goto v_resetjp_1721_;
}
v_resetjp_1721_:
{
lean_object* v___x_1725_; 
if (v_isShared_1723_ == 0)
{
v___x_1725_ = v___x_1722_;
goto v_reusejp_1724_;
}
else
{
lean_object* v_reuseFailAlloc_1726_; 
v_reuseFailAlloc_1726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1726_, 0, v_a_1720_);
v___x_1725_ = v_reuseFailAlloc_1726_;
goto v_reusejp_1724_;
}
v_reusejp_1724_:
{
return v___x_1725_;
}
}
}
}
else
{
lean_object* v___x_1728_; lean_object* v___x_1729_; 
lean_dec_ref(v_t_1676_);
v___x_1728_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1728_, 0, v_b_1681_);
lean_ctor_set(v___x_1728_, 1, v___y_1682_);
v___x_1729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1729_, 0, v___x_1728_);
return v___x_1729_;
}
v___jp_1686_:
{
size_t v___x_1689_; size_t v___x_1690_; 
v___x_1689_ = ((size_t)1ULL);
v___x_1690_ = lean_usize_add(v_i_1679_, v___x_1689_);
v_i_1679_ = v___x_1690_;
v_b_1681_ = v_fst_1687_;
v___y_1682_ = v_snd_1688_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___boxed(lean_object* v_t_1730_, lean_object* v___x_1731_, lean_object* v_as_1732_, lean_object* v_i_1733_, lean_object* v_stop_1734_, lean_object* v_b_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_){
_start:
{
uint8_t v___x_7034__boxed_1740_; size_t v_i_boxed_1741_; size_t v_stop_boxed_1742_; lean_object* v_res_1743_; 
v___x_7034__boxed_1740_ = lean_unbox(v___x_1731_);
v_i_boxed_1741_ = lean_unbox_usize(v_i_1733_);
lean_dec(v_i_1733_);
v_stop_boxed_1742_ = lean_unbox_usize(v_stop_1734_);
lean_dec(v_stop_1734_);
v_res_1743_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2(v_t_1730_, v___x_7034__boxed_1740_, v_as_1732_, v_i_boxed_1741_, v_stop_boxed_1742_, v_b_1735_, v___y_1736_, v___y_1737_, v___y_1738_);
lean_dec(v___y_1738_);
lean_dec_ref(v___y_1737_);
lean_dec_ref(v_as_1732_);
return v_res_1743_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__3(uint8_t v___x_1744_, lean_object* v_as_1745_, size_t v_i_1746_, size_t v_stop_1747_, lean_object* v_b_1748_){
_start:
{
lean_object* v___y_1750_; uint8_t v___x_1754_; 
v___x_1754_ = lean_usize_dec_eq(v_i_1746_, v_stop_1747_);
if (v___x_1754_ == 0)
{
lean_object* v_fst_1755_; uint8_t v___x_1756_; 
v_fst_1755_ = lean_ctor_get(v_b_1748_, 0);
v___x_1756_ = lean_unbox(v_fst_1755_);
if (v___x_1756_ == 0)
{
lean_object* v_snd_1757_; lean_object* v___x_1759_; uint8_t v_isShared_1760_; uint8_t v_isSharedCheck_1765_; 
v_snd_1757_ = lean_ctor_get(v_b_1748_, 1);
v_isSharedCheck_1765_ = !lean_is_exclusive(v_b_1748_);
if (v_isSharedCheck_1765_ == 0)
{
lean_object* v_unused_1766_; 
v_unused_1766_ = lean_ctor_get(v_b_1748_, 0);
lean_dec(v_unused_1766_);
v___x_1759_ = v_b_1748_;
v_isShared_1760_ = v_isSharedCheck_1765_;
goto v_resetjp_1758_;
}
else
{
lean_inc(v_snd_1757_);
lean_dec(v_b_1748_);
v___x_1759_ = lean_box(0);
v_isShared_1760_ = v_isSharedCheck_1765_;
goto v_resetjp_1758_;
}
v_resetjp_1758_:
{
lean_object* v___x_1761_; lean_object* v___x_1763_; 
v___x_1761_ = lean_box(v___x_1744_);
if (v_isShared_1760_ == 0)
{
lean_ctor_set(v___x_1759_, 0, v___x_1761_);
v___x_1763_ = v___x_1759_;
goto v_reusejp_1762_;
}
else
{
lean_object* v_reuseFailAlloc_1764_; 
v_reuseFailAlloc_1764_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1764_, 0, v___x_1761_);
lean_ctor_set(v_reuseFailAlloc_1764_, 1, v_snd_1757_);
v___x_1763_ = v_reuseFailAlloc_1764_;
goto v_reusejp_1762_;
}
v_reusejp_1762_:
{
v___y_1750_ = v___x_1763_;
goto v___jp_1749_;
}
}
}
else
{
lean_object* v_snd_1767_; lean_object* v___x_1769_; uint8_t v_isShared_1770_; uint8_t v_isSharedCheck_1777_; 
v_snd_1767_ = lean_ctor_get(v_b_1748_, 1);
v_isSharedCheck_1777_ = !lean_is_exclusive(v_b_1748_);
if (v_isSharedCheck_1777_ == 0)
{
lean_object* v_unused_1778_; 
v_unused_1778_ = lean_ctor_get(v_b_1748_, 0);
lean_dec(v_unused_1778_);
v___x_1769_ = v_b_1748_;
v_isShared_1770_ = v_isSharedCheck_1777_;
goto v_resetjp_1768_;
}
else
{
lean_inc(v_snd_1767_);
lean_dec(v_b_1748_);
v___x_1769_ = lean_box(0);
v_isShared_1770_ = v_isSharedCheck_1777_;
goto v_resetjp_1768_;
}
v_resetjp_1768_:
{
lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1775_; 
v___x_1771_ = lean_array_uget_borrowed(v_as_1745_, v_i_1746_);
lean_inc(v___x_1771_);
v___x_1772_ = lean_array_push(v_snd_1767_, v___x_1771_);
v___x_1773_ = lean_box(v___x_1754_);
if (v_isShared_1770_ == 0)
{
lean_ctor_set(v___x_1769_, 1, v___x_1772_);
lean_ctor_set(v___x_1769_, 0, v___x_1773_);
v___x_1775_ = v___x_1769_;
goto v_reusejp_1774_;
}
else
{
lean_object* v_reuseFailAlloc_1776_; 
v_reuseFailAlloc_1776_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1776_, 0, v___x_1773_);
lean_ctor_set(v_reuseFailAlloc_1776_, 1, v___x_1772_);
v___x_1775_ = v_reuseFailAlloc_1776_;
goto v_reusejp_1774_;
}
v_reusejp_1774_:
{
v___y_1750_ = v___x_1775_;
goto v___jp_1749_;
}
}
}
}
else
{
return v_b_1748_;
}
v___jp_1749_:
{
size_t v___x_1751_; size_t v___x_1752_; 
v___x_1751_ = ((size_t)1ULL);
v___x_1752_ = lean_usize_add(v_i_1746_, v___x_1751_);
v_i_1746_ = v___x_1752_;
v_b_1748_ = v___y_1750_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__3___boxed(lean_object* v___x_1779_, lean_object* v_as_1780_, lean_object* v_i_1781_, lean_object* v_stop_1782_, lean_object* v_b_1783_){
_start:
{
uint8_t v___x_7141__boxed_1784_; size_t v_i_boxed_1785_; size_t v_stop_boxed_1786_; lean_object* v_res_1787_; 
v___x_7141__boxed_1784_ = lean_unbox(v___x_1779_);
v_i_boxed_1785_ = lean_unbox_usize(v_i_1781_);
lean_dec(v_i_1781_);
v_stop_boxed_1786_ = lean_unbox_usize(v_stop_1782_);
lean_dec(v_stop_1782_);
v_res_1787_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__3(v___x_7141__boxed_1784_, v_as_1780_, v_i_boxed_1785_, v_stop_boxed_1786_, v_b_1783_);
lean_dec_ref(v_as_1780_);
return v_res_1787_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__3(void){
_start:
{
lean_object* v___x_1794_; lean_object* v___x_1795_; 
v___x_1794_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__2));
v___x_1795_ = l_Lean_stringToMessageData(v___x_1794_);
return v___x_1795_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__7(void){
_start:
{
lean_object* v___x_1802_; lean_object* v___x_1803_; 
v___x_1802_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__6));
v___x_1803_ = l_Lean_stringToMessageData(v___x_1802_);
return v___x_1803_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5(lean_object* v_elabVal_1806_, lean_object* v_as_1807_, size_t v_i_1808_, size_t v_stop_1809_, lean_object* v_b_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_){
_start:
{
lean_object* v_a_1815_; lean_object* v___y_1820_; uint8_t v___x_1822_; 
v___x_1822_ = lean_usize_dec_eq(v_i_1808_, v_stop_1809_);
if (v___x_1822_ == 0)
{
lean_object* v___x_1823_; lean_object* v___x_1824_; uint8_t v___x_1825_; 
v___x_1823_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__1));
v___x_1824_ = lean_array_uget_borrowed(v_as_1807_, v_i_1808_);
lean_inc(v___x_1824_);
v___x_1825_ = l_Lean_Syntax_isOfKind(v___x_1824_, v___x_1823_);
if (v___x_1825_ == 0)
{
lean_object* v___x_1826_; lean_object* v___x_1827_; 
lean_dec_ref(v_b_1810_);
v___x_1826_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__3, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__3);
v___x_1827_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v___x_1824_, v___x_1826_, v___y_1811_, v___y_1812_);
v___y_1820_ = v___x_1827_;
goto v___jp_1819_;
}
else
{
lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; uint8_t v___x_1831_; 
v___x_1828_ = lean_unsigned_to_nat(0u);
v___x_1829_ = l_Lean_Syntax_getArg(v___x_1824_, v___x_1828_);
v___x_1830_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__5));
lean_inc(v___x_1829_);
v___x_1831_ = l_Lean_Syntax_isOfKind(v___x_1829_, v___x_1830_);
if (v___x_1831_ == 0)
{
lean_object* v___x_1832_; lean_object* v___x_1833_; 
lean_dec_ref(v_b_1810_);
v___x_1832_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__7, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__7);
v___x_1833_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v___x_1829_, v___x_1832_, v___y_1811_, v___y_1812_);
lean_dec(v___x_1829_);
v___y_1820_ = v___x_1833_;
goto v___jp_1819_;
}
else
{
lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v_v_1836_; lean_object* v___y_1838_; lean_object* v_fst_1839_; lean_object* v_snd_1840_; lean_object* v___y_1872_; lean_object* v___y_1873_; lean_object* v___y_1886_; lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; uint8_t v___x_1911_; 
v___x_1834_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___closed__0));
v___x_1835_ = lean_unsigned_to_nat(2u);
v_v_1836_ = l_Lean_Syntax_getArg(v___x_1824_, v___x_1835_);
v___x_1907_ = l_Lean_Syntax_getArg(v___x_1829_, v___x_1828_);
v___x_1908_ = l_Lean_Syntax_getArgs(v___x_1907_);
lean_dec(v___x_1907_);
v___x_1909_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__8));
v___x_1910_ = lean_array_get_size(v___x_1908_);
v___x_1911_ = lean_nat_dec_lt(v___x_1828_, v___x_1910_);
if (v___x_1911_ == 0)
{
lean_dec_ref(v___x_1908_);
v___y_1886_ = v___x_1909_;
goto v___jp_1885_;
}
else
{
lean_object* v___x_1912_; lean_object* v___x_1913_; size_t v___x_1914_; size_t v___x_1915_; lean_object* v___x_1916_; lean_object* v_snd_1917_; 
v___x_1912_ = lean_box(v___x_1911_);
v___x_1913_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1913_, 0, v___x_1912_);
lean_ctor_set(v___x_1913_, 1, v___x_1909_);
v___x_1914_ = ((size_t)0ULL);
v___x_1915_ = lean_usize_of_nat(v___x_1910_);
v___x_1916_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__3(v___x_1831_, v___x_1908_, v___x_1914_, v___x_1915_, v___x_1913_);
lean_dec_ref(v___x_1908_);
v_snd_1917_ = lean_ctor_get(v___x_1916_, 1);
lean_inc(v_snd_1917_);
lean_dec_ref(v___x_1916_);
v___y_1886_ = v_snd_1917_;
goto v___jp_1885_;
}
v___jp_1837_:
{
lean_object* v___x_1841_; 
lean_inc(v___y_1838_);
v___x_1841_ = l_Lake_Toml_elabSimpleKey(v___y_1838_, v___y_1811_, v___y_1812_);
if (lean_obj_tag(v___x_1841_) == 0)
{
lean_object* v_a_1842_; lean_object* v___x_1843_; uint8_t v___x_1844_; 
v_a_1842_ = lean_ctor_get(v___x_1841_, 0);
lean_inc(v_a_1842_);
lean_dec_ref_known(v___x_1841_, 1);
v___x_1843_ = l_Lean_Name_str___override(v_fst_1839_, v_a_1842_);
lean_inc_ref(v_snd_1840_);
lean_inc(v___x_1843_);
v___x_1844_ = l_Lake_Toml_RBDict_contains___redArg(v___x_1834_, v___x_1843_, v_snd_1840_);
if (v___x_1844_ == 0)
{
lean_object* v___x_1845_; 
lean_dec(v___y_1838_);
lean_inc_ref(v_elabVal_1806_);
lean_inc(v___y_1812_);
lean_inc_ref(v___y_1811_);
v___x_1845_ = lean_apply_4(v_elabVal_1806_, v_v_1836_, v___y_1811_, v___y_1812_, lean_box(0));
if (lean_obj_tag(v___x_1845_) == 0)
{
lean_object* v_a_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; 
v_a_1846_ = lean_ctor_get(v___x_1845_, 0);
lean_inc(v_a_1846_);
lean_dec_ref_known(v___x_1845_, 1);
v___x_1847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1847_, 0, v_a_1846_);
v___x_1848_ = l_Lake_Toml_RBDict_push___redArg(v___x_1834_, v___x_1843_, v___x_1847_, v_snd_1840_);
v_a_1815_ = v___x_1848_;
goto v___jp_1814_;
}
else
{
lean_object* v_a_1849_; lean_object* v___x_1851_; uint8_t v_isShared_1852_; uint8_t v_isSharedCheck_1856_; 
lean_dec(v___x_1843_);
lean_dec_ref(v_snd_1840_);
lean_dec_ref(v_elabVal_1806_);
v_a_1849_ = lean_ctor_get(v___x_1845_, 0);
v_isSharedCheck_1856_ = !lean_is_exclusive(v___x_1845_);
if (v_isSharedCheck_1856_ == 0)
{
v___x_1851_ = v___x_1845_;
v_isShared_1852_ = v_isSharedCheck_1856_;
goto v_resetjp_1850_;
}
else
{
lean_inc(v_a_1849_);
lean_dec(v___x_1845_);
v___x_1851_ = lean_box(0);
v_isShared_1852_ = v_isSharedCheck_1856_;
goto v_resetjp_1850_;
}
v_resetjp_1850_:
{
lean_object* v___x_1854_; 
if (v_isShared_1852_ == 0)
{
v___x_1854_ = v___x_1851_;
goto v_reusejp_1853_;
}
else
{
lean_object* v_reuseFailAlloc_1855_; 
v_reuseFailAlloc_1855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1855_, 0, v_a_1849_);
v___x_1854_ = v_reuseFailAlloc_1855_;
goto v_reusejp_1853_;
}
v_reusejp_1853_:
{
return v___x_1854_;
}
}
}
}
else
{
lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; 
lean_dec_ref(v_snd_1840_);
lean_dec(v_v_1836_);
v___x_1857_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___closed__2, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___closed__2);
v___x_1858_ = l_Lean_MessageData_ofName(v___x_1843_);
v___x_1859_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1859_, 0, v___x_1857_);
lean_ctor_set(v___x_1859_, 1, v___x_1858_);
v___x_1860_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__3, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__3_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBasicStringCore___closed__3);
v___x_1861_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1861_, 0, v___x_1859_);
lean_ctor_set(v___x_1861_, 1, v___x_1860_);
v___x_1862_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v___y_1838_, v___x_1861_, v___y_1811_, v___y_1812_);
lean_dec(v___y_1838_);
v___y_1820_ = v___x_1862_;
goto v___jp_1819_;
}
}
else
{
lean_object* v_a_1863_; lean_object* v___x_1865_; uint8_t v_isShared_1866_; uint8_t v_isSharedCheck_1870_; 
lean_dec_ref(v_snd_1840_);
lean_dec(v_fst_1839_);
lean_dec(v___y_1838_);
lean_dec(v_v_1836_);
lean_dec_ref(v_elabVal_1806_);
v_a_1863_ = lean_ctor_get(v___x_1841_, 0);
v_isSharedCheck_1870_ = !lean_is_exclusive(v___x_1841_);
if (v_isSharedCheck_1870_ == 0)
{
v___x_1865_ = v___x_1841_;
v_isShared_1866_ = v_isSharedCheck_1870_;
goto v_resetjp_1864_;
}
else
{
lean_inc(v_a_1863_);
lean_dec(v___x_1841_);
v___x_1865_ = lean_box(0);
v_isShared_1866_ = v_isSharedCheck_1870_;
goto v_resetjp_1864_;
}
v_resetjp_1864_:
{
lean_object* v___x_1868_; 
if (v_isShared_1866_ == 0)
{
v___x_1868_ = v___x_1865_;
goto v_reusejp_1867_;
}
else
{
lean_object* v_reuseFailAlloc_1869_; 
v_reuseFailAlloc_1869_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1869_, 0, v_a_1863_);
v___x_1868_ = v_reuseFailAlloc_1869_;
goto v_reusejp_1867_;
}
v_reusejp_1867_:
{
return v___x_1868_;
}
}
}
}
v___jp_1871_:
{
if (lean_obj_tag(v___y_1873_) == 0)
{
lean_object* v_a_1874_; lean_object* v_fst_1875_; lean_object* v_snd_1876_; 
v_a_1874_ = lean_ctor_get(v___y_1873_, 0);
lean_inc(v_a_1874_);
lean_dec_ref_known(v___y_1873_, 1);
v_fst_1875_ = lean_ctor_get(v_a_1874_, 0);
lean_inc(v_fst_1875_);
v_snd_1876_ = lean_ctor_get(v_a_1874_, 1);
lean_inc(v_snd_1876_);
lean_dec(v_a_1874_);
v___y_1838_ = v___y_1872_;
v_fst_1839_ = v_fst_1875_;
v_snd_1840_ = v_snd_1876_;
goto v___jp_1837_;
}
else
{
lean_object* v_a_1877_; lean_object* v___x_1879_; uint8_t v_isShared_1880_; uint8_t v_isSharedCheck_1884_; 
lean_dec(v___y_1872_);
lean_dec(v_v_1836_);
lean_dec_ref(v_elabVal_1806_);
v_a_1877_ = lean_ctor_get(v___y_1873_, 0);
v_isSharedCheck_1884_ = !lean_is_exclusive(v___y_1873_);
if (v_isSharedCheck_1884_ == 0)
{
v___x_1879_ = v___y_1873_;
v_isShared_1880_ = v_isSharedCheck_1884_;
goto v_resetjp_1878_;
}
else
{
lean_inc(v_a_1877_);
lean_dec(v___y_1873_);
v___x_1879_ = lean_box(0);
v_isShared_1880_ = v_isSharedCheck_1884_;
goto v_resetjp_1878_;
}
v_resetjp_1878_:
{
lean_object* v___x_1882_; 
if (v_isShared_1880_ == 0)
{
v___x_1882_ = v___x_1879_;
goto v_reusejp_1881_;
}
else
{
lean_object* v_reuseFailAlloc_1883_; 
v_reuseFailAlloc_1883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1883_, 0, v_a_1877_);
v___x_1882_ = v_reuseFailAlloc_1883_;
goto v_reusejp_1881_;
}
v_reusejp_1881_:
{
return v___x_1882_;
}
}
}
}
v___jp_1885_:
{
size_t v_sz_1887_; size_t v___x_1888_; lean_object* v___x_1889_; 
v_sz_1887_ = lean_array_size(v___y_1886_);
v___x_1888_ = ((size_t)0ULL);
v___x_1889_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__1(v_sz_1887_, v___x_1888_, v___y_1886_);
if (lean_obj_tag(v___x_1889_) == 0)
{
lean_object* v___x_1890_; lean_object* v___x_1891_; 
lean_dec(v_v_1836_);
lean_dec_ref(v_b_1810_);
v___x_1890_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__7, &l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___closed__7);
v___x_1891_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v___x_1829_, v___x_1890_, v___y_1811_, v___y_1812_);
lean_dec(v___x_1829_);
v___y_1820_ = v___x_1891_;
goto v___jp_1819_;
}
else
{
lean_object* v_val_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; lean_object* v_tailKey_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; uint8_t v___x_1901_; 
lean_dec(v___x_1829_);
v_val_1892_ = lean_ctor_get(v___x_1889_, 0);
lean_inc(v_val_1892_);
lean_dec_ref_known(v___x_1889_, 1);
v___x_1893_ = lean_box(0);
v___x_1894_ = lean_array_get_size(v_val_1892_);
v___x_1895_ = lean_unsigned_to_nat(1u);
v___x_1896_ = lean_nat_sub(v___x_1894_, v___x_1895_);
v_tailKey_1897_ = lean_array_get(v___x_1893_, v_val_1892_, v___x_1896_);
lean_dec(v___x_1896_);
v___x_1898_ = lean_box(0);
v___x_1899_ = lean_array_pop(v_val_1892_);
v___x_1900_ = lean_array_get_size(v___x_1899_);
v___x_1901_ = lean_nat_dec_lt(v___x_1828_, v___x_1900_);
if (v___x_1901_ == 0)
{
lean_dec_ref(v___x_1899_);
v___y_1838_ = v_tailKey_1897_;
v_fst_1839_ = v___x_1898_;
v_snd_1840_ = v_b_1810_;
goto v___jp_1837_;
}
else
{
uint8_t v___x_1902_; 
v___x_1902_ = lean_nat_dec_le(v___x_1900_, v___x_1900_);
if (v___x_1902_ == 0)
{
if (v___x_1901_ == 0)
{
lean_dec_ref(v___x_1899_);
v___y_1838_ = v_tailKey_1897_;
v_fst_1839_ = v___x_1898_;
v_snd_1840_ = v_b_1810_;
goto v___jp_1837_;
}
else
{
size_t v___x_1903_; lean_object* v___x_1904_; 
v___x_1903_ = lean_usize_of_nat(v___x_1900_);
lean_inc_ref(v_b_1810_);
v___x_1904_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2(v_b_1810_, v___x_1831_, v___x_1899_, v___x_1888_, v___x_1903_, v___x_1898_, v_b_1810_, v___y_1811_, v___y_1812_);
lean_dec_ref(v___x_1899_);
v___y_1872_ = v_tailKey_1897_;
v___y_1873_ = v___x_1904_;
goto v___jp_1871_;
}
}
else
{
size_t v___x_1905_; lean_object* v___x_1906_; 
v___x_1905_ = lean_usize_of_nat(v___x_1900_);
lean_inc_ref(v_b_1810_);
v___x_1906_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2(v_b_1810_, v___x_1831_, v___x_1899_, v___x_1888_, v___x_1905_, v___x_1898_, v_b_1810_, v___y_1811_, v___y_1812_);
lean_dec_ref(v___x_1899_);
v___y_1872_ = v_tailKey_1897_;
v___y_1873_ = v___x_1906_;
goto v___jp_1871_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1918_; 
lean_dec_ref(v_elabVal_1806_);
v___x_1918_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1918_, 0, v_b_1810_);
return v___x_1918_;
}
v___jp_1814_:
{
size_t v___x_1816_; size_t v___x_1817_; 
v___x_1816_ = ((size_t)1ULL);
v___x_1817_ = lean_usize_add(v_i_1808_, v___x_1816_);
v_i_1808_ = v___x_1817_;
v_b_1810_ = v_a_1815_;
goto _start;
}
v___jp_1819_:
{
if (lean_obj_tag(v___y_1820_) == 0)
{
lean_object* v_a_1821_; 
v_a_1821_ = lean_ctor_get(v___y_1820_, 0);
lean_inc(v_a_1821_);
lean_dec_ref_known(v___y_1820_, 1);
v_a_1815_ = v_a_1821_;
goto v___jp_1814_;
}
else
{
lean_dec_ref(v_elabVal_1806_);
return v___y_1820_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5___boxed(lean_object* v_elabVal_1919_, lean_object* v_as_1920_, lean_object* v_i_1921_, lean_object* v_stop_1922_, lean_object* v_b_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_){
_start:
{
size_t v_i_boxed_1927_; size_t v_stop_boxed_1928_; lean_object* v_res_1929_; 
v_i_boxed_1927_ = lean_unbox_usize(v_i_1921_);
lean_dec(v_i_1921_);
v_stop_boxed_1928_ = lean_unbox_usize(v_stop_1922_);
lean_dec(v_stop_1922_);
v_res_1929_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5(v_elabVal_1919_, v_as_1920_, v_i_boxed_1927_, v_stop_boxed_1928_, v_b_1923_, v___y_1924_, v___y_1925_);
lean_dec(v___y_1925_);
lean_dec_ref(v___y_1924_);
lean_dec_ref(v_as_1920_);
return v_res_1929_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__4(lean_object* v_as_1930_, size_t v_i_1931_, size_t v_stop_1932_, lean_object* v_b_1933_){
_start:
{
lean_object* v___y_1935_; uint8_t v___x_1939_; 
v___x_1939_ = lean_usize_dec_eq(v_i_1931_, v_stop_1932_);
if (v___x_1939_ == 0)
{
lean_object* v___x_1940_; lean_object* v_snd_1941_; 
v___x_1940_ = lean_array_uget_borrowed(v_as_1930_, v_i_1931_);
v_snd_1941_ = lean_ctor_get(v___x_1940_, 1);
if (lean_obj_tag(v_snd_1941_) == 1)
{
lean_object* v_fst_1942_; lean_object* v_val_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; 
v_fst_1942_ = lean_ctor_get(v___x_1940_, 0);
v_val_1943_ = lean_ctor_get(v_snd_1941_, 0);
v___x_1944_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__2___closed__0));
lean_inc(v_val_1943_);
lean_inc(v_fst_1942_);
v___x_1945_ = l_Lake_Toml_RBDict_push___redArg(v___x_1944_, v_fst_1942_, v_val_1943_, v_b_1933_);
v___y_1935_ = v___x_1945_;
goto v___jp_1934_;
}
else
{
v___y_1935_ = v_b_1933_;
goto v___jp_1934_;
}
}
else
{
return v_b_1933_;
}
v___jp_1934_:
{
size_t v___x_1936_; size_t v___x_1937_; 
v___x_1936_ = ((size_t)1ULL);
v___x_1937_ = lean_usize_add(v_i_1931_, v___x_1936_);
v_i_1931_ = v___x_1937_;
v_b_1933_ = v___y_1935_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__4___boxed(lean_object* v_as_1946_, lean_object* v_i_1947_, lean_object* v_stop_1948_, lean_object* v_b_1949_){
_start:
{
size_t v_i_boxed_1950_; size_t v_stop_boxed_1951_; lean_object* v_res_1952_; 
v_i_boxed_1950_ = lean_unbox_usize(v_i_1947_);
lean_dec(v_i_1947_);
v_stop_boxed_1951_ = lean_unbox_usize(v_stop_1948_);
lean_dec(v_stop_1948_);
v_res_1952_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__4(v_as_1946_, v_i_boxed_1950_, v_stop_boxed_1951_, v_b_1949_);
lean_dec_ref(v_as_1946_);
return v_res_1952_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__3(void){
_start:
{
lean_object* v___x_1959_; lean_object* v___x_1960_; 
v___x_1959_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__2));
v___x_1960_ = l_Lean_stringToMessageData(v___x_1959_);
return v___x_1960_;
}
}
static lean_object* _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__4(void){
_start:
{
lean_object* v___x_1961_; 
v___x_1961_ = l_Lake_Toml_RBDict_empty___redArg();
return v___x_1961_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable(lean_object* v_x_1962_, lean_object* v_elabVal_1963_, lean_object* v_a_1964_, lean_object* v_a_1965_){
_start:
{
lean_object* v___x_1967_; uint8_t v___x_1968_; 
v___x_1967_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__1));
lean_inc(v_x_1962_);
v___x_1968_ = l_Lean_Syntax_isOfKind(v_x_1962_, v___x_1967_);
if (v___x_1968_ == 0)
{
lean_object* v___x_1969_; lean_object* v___x_1970_; 
lean_dec_ref(v_elabVal_1963_);
v___x_1969_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__3, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__3_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__3);
v___x_1970_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_x_1962_, v___x_1969_, v_a_1964_, v_a_1965_);
lean_dec(v_x_1962_);
return v___x_1970_;
}
else
{
lean_object* v___x_1971_; lean_object* v_a_1973_; lean_object* v___y_1984_; lean_object* v___x_1994_; lean_object* v___x_1995_; lean_object* v_kvs_1996_; lean_object* v_t_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; uint8_t v___x_2000_; 
v___x_1971_ = lean_unsigned_to_nat(0u);
v___x_1994_ = lean_unsigned_to_nat(1u);
v___x_1995_ = l_Lean_Syntax_getArg(v_x_1962_, v___x_1994_);
lean_dec(v_x_1962_);
v_kvs_1996_ = l_Lean_Syntax_getArgs(v___x_1995_);
lean_dec(v___x_1995_);
v_t_1997_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__4, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__4_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__4);
v___x_1998_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_kvs_1996_);
lean_dec_ref(v_kvs_1996_);
v___x_1999_ = lean_array_get_size(v___x_1998_);
v___x_2000_ = lean_nat_dec_lt(v___x_1971_, v___x_1999_);
if (v___x_2000_ == 0)
{
lean_dec_ref(v___x_1998_);
lean_dec_ref(v_elabVal_1963_);
v_a_1973_ = v_t_1997_;
goto v___jp_1972_;
}
else
{
uint8_t v___x_2001_; 
v___x_2001_ = lean_nat_dec_le(v___x_1999_, v___x_1999_);
if (v___x_2001_ == 0)
{
if (v___x_2000_ == 0)
{
lean_dec_ref(v___x_1998_);
lean_dec_ref(v_elabVal_1963_);
v_a_1973_ = v_t_1997_;
goto v___jp_1972_;
}
else
{
size_t v___x_2002_; size_t v___x_2003_; lean_object* v___x_2004_; 
v___x_2002_ = ((size_t)0ULL);
v___x_2003_ = lean_usize_of_nat(v___x_1999_);
v___x_2004_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5(v_elabVal_1963_, v___x_1998_, v___x_2002_, v___x_2003_, v_t_1997_, v_a_1964_, v_a_1965_);
lean_dec_ref(v___x_1998_);
v___y_1984_ = v___x_2004_;
goto v___jp_1983_;
}
}
else
{
size_t v___x_2005_; size_t v___x_2006_; lean_object* v___x_2007_; 
v___x_2005_ = ((size_t)0ULL);
v___x_2006_ = lean_usize_of_nat(v___x_1999_);
v___x_2007_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__5(v_elabVal_1963_, v___x_1998_, v___x_2005_, v___x_2006_, v_t_1997_, v_a_1964_, v_a_1965_);
lean_dec_ref(v___x_1998_);
v___y_1984_ = v___x_2007_;
goto v___jp_1983_;
}
}
v___jp_1972_:
{
lean_object* v_items_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; uint8_t v___x_1977_; 
v_items_1974_ = lean_ctor_get(v_a_1973_, 0);
lean_inc_ref(v_items_1974_);
lean_dec_ref(v_a_1973_);
v___x_1975_ = lean_obj_once(&l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__4, &l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__4_once, _init_l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__4);
v___x_1976_ = lean_array_get_size(v_items_1974_);
v___x_1977_ = lean_nat_dec_lt(v___x_1971_, v___x_1976_);
if (v___x_1977_ == 0)
{
lean_object* v___x_1978_; 
lean_dec_ref(v_items_1974_);
v___x_1978_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1978_, 0, v___x_1975_);
return v___x_1978_;
}
else
{
size_t v___x_1979_; size_t v___x_1980_; lean_object* v___x_1981_; lean_object* v___x_1982_; 
v___x_1979_ = ((size_t)0ULL);
v___x_1980_ = lean_usize_of_nat(v___x_1976_);
v___x_1981_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__4(v_items_1974_, v___x_1979_, v___x_1980_, v___x_1975_);
lean_dec_ref(v_items_1974_);
v___x_1982_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1982_, 0, v___x_1981_);
return v___x_1982_;
}
}
v___jp_1983_:
{
if (lean_obj_tag(v___y_1984_) == 0)
{
lean_object* v_a_1985_; 
v_a_1985_ = lean_ctor_get(v___y_1984_, 0);
lean_inc(v_a_1985_);
lean_dec_ref_known(v___y_1984_, 1);
v_a_1973_ = v_a_1985_;
goto v___jp_1972_;
}
else
{
lean_object* v_a_1986_; lean_object* v___x_1988_; uint8_t v_isShared_1989_; uint8_t v_isSharedCheck_1993_; 
v_a_1986_ = lean_ctor_get(v___y_1984_, 0);
v_isSharedCheck_1993_ = !lean_is_exclusive(v___y_1984_);
if (v_isSharedCheck_1993_ == 0)
{
v___x_1988_ = v___y_1984_;
v_isShared_1989_ = v_isSharedCheck_1993_;
goto v_resetjp_1987_;
}
else
{
lean_inc(v_a_1986_);
lean_dec(v___y_1984_);
v___x_1988_ = lean_box(0);
v_isShared_1989_ = v_isSharedCheck_1993_;
goto v_resetjp_1987_;
}
v_resetjp_1987_:
{
lean_object* v___x_1991_; 
if (v_isShared_1989_ == 0)
{
v___x_1991_ = v___x_1988_;
goto v_reusejp_1990_;
}
else
{
lean_object* v_reuseFailAlloc_1992_; 
v_reuseFailAlloc_1992_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1992_, 0, v_a_1986_);
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
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___boxed(lean_object* v_x_2008_, lean_object* v_elabVal_2009_, lean_object* v_a_2010_, lean_object* v_a_2011_, lean_object* v_a_2012_){
_start:
{
lean_object* v_res_2013_; 
v_res_2013_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable(v_x_2008_, v_elabVal_2009_, v_a_2010_, v_a_2011_);
lean_dec(v_a_2011_);
lean_dec_ref(v_a_2010_);
return v_res_2013_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__0(lean_object* v_00_u03b1_2014_, lean_object* v_ref_2015_, lean_object* v_msg_2016_, lean_object* v___y_2017_, lean_object* v___y_2018_, lean_object* v___y_2019_){
_start:
{
lean_object* v___x_2021_; 
v___x_2021_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__0___redArg(v_ref_2015_, v_msg_2016_, v___y_2017_, v___y_2018_, v___y_2019_);
return v___x_2021_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__0___boxed(lean_object* v_00_u03b1_2022_, lean_object* v_ref_2023_, lean_object* v_msg_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_){
_start:
{
lean_object* v_res_2029_; 
v_res_2029_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__0(v_00_u03b1_2022_, v_ref_2023_, v_msg_2024_, v___y_2025_, v___y_2026_, v___y_2027_);
lean_dec(v___y_2027_);
lean_dec_ref(v___y_2026_);
lean_dec_ref(v___y_2025_);
lean_dec(v_ref_2023_);
return v_res_2029_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__0_spec__0(lean_object* v_00_u03b1_2030_, lean_object* v_msg_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_, lean_object* v___y_2034_){
_start:
{
lean_object* v___x_2036_; 
v___x_2036_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__0_spec__0___redArg(v_msg_2031_, v___y_2033_, v___y_2034_);
return v___x_2036_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2037_, lean_object* v_msg_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_){
_start:
{
lean_object* v_res_2043_; 
v_res_2043_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable_spec__0_spec__0(v_00_u03b1_2037_, v_msg_2038_, v___y_2039_, v___y_2040_, v___y_2041_);
lean_dec(v___y_2041_);
lean_dec_ref(v___y_2040_);
lean_dec_ref(v___y_2039_);
return v_res_2043_;
}
}
static lean_object* _init_l_Lake_Toml_elabVal___closed__1(void){
_start:
{
lean_object* v___x_2045_; lean_object* v___x_2046_; 
v___x_2045_ = ((lean_object*)(l_Lake_Toml_elabVal___closed__0));
v___x_2046_ = l_Lean_stringToMessageData(v___x_2045_);
return v___x_2046_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_elabVal___boxed(lean_object* v_x_2047_, lean_object* v_a_2048_, lean_object* v_a_2049_, lean_object* v_a_2050_){
_start:
{
lean_object* v_res_2051_; 
v_res_2051_ = l_Lake_Toml_elabVal(v_x_2047_, v_a_2048_, v_a_2049_);
lean_dec(v_a_2049_);
lean_dec_ref(v_a_2048_);
return v_res_2051_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_elabVal(lean_object* v_x_2052_, lean_object* v_a_2053_, lean_object* v_a_2054_){
_start:
{
lean_object* v___x_2056_; uint8_t v___x_2057_; 
v___x_2056_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat___closed__1));
lean_inc(v_x_2052_);
v___x_2057_ = l_Lean_Syntax_isOfKind(v_x_2052_, v___x_2056_);
if (v___x_2057_ == 0)
{
lean_object* v___x_2058_; uint8_t v___x_2059_; 
v___x_2058_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt___closed__1));
lean_inc(v_x_2052_);
v___x_2059_ = l_Lean_Syntax_isOfKind(v_x_2052_, v___x_2058_);
if (v___x_2059_ == 0)
{
lean_object* v___x_2060_; uint8_t v___x_2061_; 
v___x_2060_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum___closed__1));
lean_inc(v_x_2052_);
v___x_2061_ = l_Lean_Syntax_isOfKind(v_x_2052_, v___x_2060_);
if (v___x_2061_ == 0)
{
lean_object* v___x_2062_; uint8_t v___x_2063_; 
v___x_2062_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum___closed__1));
lean_inc(v_x_2052_);
v___x_2063_ = l_Lean_Syntax_isOfKind(v_x_2052_, v___x_2062_);
if (v___x_2063_ == 0)
{
lean_object* v___x_2064_; uint8_t v___x_2065_; 
v___x_2064_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum___closed__1));
lean_inc(v_x_2052_);
v___x_2065_ = l_Lean_Syntax_isOfKind(v_x_2052_, v___x_2064_);
if (v___x_2065_ == 0)
{
lean_object* v___x_2066_; uint8_t v___x_2067_; 
v___x_2066_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime___closed__3));
lean_inc(v_x_2052_);
v___x_2067_ = l_Lean_Syntax_isOfKind(v_x_2052_, v___x_2066_);
if (v___x_2067_ == 0)
{
lean_object* v___x_2068_; uint8_t v___x_2069_; 
v___x_2068_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString___closed__1));
lean_inc(v_x_2052_);
v___x_2069_ = l_Lean_Syntax_isOfKind(v_x_2052_, v___x_2068_);
if (v___x_2069_ == 0)
{
lean_object* v___x_2070_; uint8_t v___x_2071_; 
v___x_2070_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean___closed__3));
lean_inc(v_x_2052_);
v___x_2071_ = l_Lean_Syntax_isOfKind(v_x_2052_, v___x_2070_);
if (v___x_2071_ == 0)
{
lean_object* v___x_2072_; uint8_t v___x_2073_; 
v___x_2072_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg___closed__1));
lean_inc(v_x_2052_);
v___x_2073_ = l_Lean_Syntax_isOfKind(v_x_2052_, v___x_2072_);
if (v___x_2073_ == 0)
{
lean_object* v___x_2074_; uint8_t v___x_2075_; 
v___x_2074_ = ((lean_object*)(l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable___closed__1));
lean_inc(v_x_2052_);
v___x_2075_ = l_Lean_Syntax_isOfKind(v_x_2052_, v___x_2074_);
if (v___x_2075_ == 0)
{
lean_object* v___x_2076_; lean_object* v___x_2077_; 
v___x_2076_ = lean_obj_once(&l_Lake_Toml_elabVal___closed__1, &l_Lake_Toml_elabVal___closed__1_once, _init_l_Lake_Toml_elabVal___closed__1);
v___x_2077_ = l_Lean_throwErrorAt___at___00__private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean_spec__0___redArg(v_x_2052_, v___x_2076_, v_a_2053_, v_a_2054_);
lean_dec(v_x_2052_);
return v___x_2077_;
}
else
{
lean_object* v___x_2078_; lean_object* v___x_2079_; 
v___x_2078_ = lean_alloc_closure((void*)(l_Lake_Toml_elabVal___boxed), 4, 0);
lean_inc(v_x_2052_);
v___x_2079_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabInlineTable(v_x_2052_, v___x_2078_, v_a_2053_, v_a_2054_);
if (lean_obj_tag(v___x_2079_) == 0)
{
lean_object* v_a_2080_; lean_object* v___x_2082_; uint8_t v_isShared_2083_; uint8_t v_isSharedCheck_2088_; 
v_a_2080_ = lean_ctor_get(v___x_2079_, 0);
v_isSharedCheck_2088_ = !lean_is_exclusive(v___x_2079_);
if (v_isSharedCheck_2088_ == 0)
{
v___x_2082_ = v___x_2079_;
v_isShared_2083_ = v_isSharedCheck_2088_;
goto v_resetjp_2081_;
}
else
{
lean_inc(v_a_2080_);
lean_dec(v___x_2079_);
v___x_2082_ = lean_box(0);
v_isShared_2083_ = v_isSharedCheck_2088_;
goto v_resetjp_2081_;
}
v_resetjp_2081_:
{
lean_object* v___x_2084_; lean_object* v___x_2086_; 
v___x_2084_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v___x_2084_, 0, v_x_2052_);
lean_ctor_set(v___x_2084_, 1, v_a_2080_);
if (v_isShared_2083_ == 0)
{
lean_ctor_set(v___x_2082_, 0, v___x_2084_);
v___x_2086_ = v___x_2082_;
goto v_reusejp_2085_;
}
else
{
lean_object* v_reuseFailAlloc_2087_; 
v_reuseFailAlloc_2087_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2087_, 0, v___x_2084_);
v___x_2086_ = v_reuseFailAlloc_2087_;
goto v_reusejp_2085_;
}
v_reusejp_2085_:
{
return v___x_2086_;
}
}
}
else
{
lean_object* v_a_2089_; lean_object* v___x_2091_; uint8_t v_isShared_2092_; uint8_t v_isSharedCheck_2096_; 
lean_dec(v_x_2052_);
v_a_2089_ = lean_ctor_get(v___x_2079_, 0);
v_isSharedCheck_2096_ = !lean_is_exclusive(v___x_2079_);
if (v_isSharedCheck_2096_ == 0)
{
v___x_2091_ = v___x_2079_;
v_isShared_2092_ = v_isSharedCheck_2096_;
goto v_resetjp_2090_;
}
else
{
lean_inc(v_a_2089_);
lean_dec(v___x_2079_);
v___x_2091_ = lean_box(0);
v_isShared_2092_ = v_isSharedCheck_2096_;
goto v_resetjp_2090_;
}
v_resetjp_2090_:
{
lean_object* v___x_2094_; 
if (v_isShared_2092_ == 0)
{
v___x_2094_ = v___x_2091_;
goto v_reusejp_2093_;
}
else
{
lean_object* v_reuseFailAlloc_2095_; 
v_reuseFailAlloc_2095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2095_, 0, v_a_2089_);
v___x_2094_ = v_reuseFailAlloc_2095_;
goto v_reusejp_2093_;
}
v_reusejp_2093_:
{
return v___x_2094_;
}
}
}
}
}
else
{
lean_object* v___x_2097_; lean_object* v___x_2098_; 
v___x_2097_ = lean_alloc_closure((void*)(l_Lake_Toml_elabVal___boxed), 4, 0);
lean_inc(v_x_2052_);
v___x_2098_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabArray___redArg(v_x_2052_, v___x_2097_, v_a_2053_, v_a_2054_);
if (lean_obj_tag(v___x_2098_) == 0)
{
lean_object* v_a_2099_; lean_object* v___x_2101_; uint8_t v_isShared_2102_; uint8_t v_isSharedCheck_2107_; 
v_a_2099_ = lean_ctor_get(v___x_2098_, 0);
v_isSharedCheck_2107_ = !lean_is_exclusive(v___x_2098_);
if (v_isSharedCheck_2107_ == 0)
{
v___x_2101_ = v___x_2098_;
v_isShared_2102_ = v_isSharedCheck_2107_;
goto v_resetjp_2100_;
}
else
{
lean_inc(v_a_2099_);
lean_dec(v___x_2098_);
v___x_2101_ = lean_box(0);
v_isShared_2102_ = v_isSharedCheck_2107_;
goto v_resetjp_2100_;
}
v_resetjp_2100_:
{
lean_object* v___x_2103_; lean_object* v___x_2105_; 
v___x_2103_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2103_, 0, v_x_2052_);
lean_ctor_set(v___x_2103_, 1, v_a_2099_);
if (v_isShared_2102_ == 0)
{
lean_ctor_set(v___x_2101_, 0, v___x_2103_);
v___x_2105_ = v___x_2101_;
goto v_reusejp_2104_;
}
else
{
lean_object* v_reuseFailAlloc_2106_; 
v_reuseFailAlloc_2106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2106_, 0, v___x_2103_);
v___x_2105_ = v_reuseFailAlloc_2106_;
goto v_reusejp_2104_;
}
v_reusejp_2104_:
{
return v___x_2105_;
}
}
}
else
{
lean_object* v_a_2108_; lean_object* v___x_2110_; uint8_t v_isShared_2111_; uint8_t v_isSharedCheck_2115_; 
lean_dec(v_x_2052_);
v_a_2108_ = lean_ctor_get(v___x_2098_, 0);
v_isSharedCheck_2115_ = !lean_is_exclusive(v___x_2098_);
if (v_isSharedCheck_2115_ == 0)
{
v___x_2110_ = v___x_2098_;
v_isShared_2111_ = v_isSharedCheck_2115_;
goto v_resetjp_2109_;
}
else
{
lean_inc(v_a_2108_);
lean_dec(v___x_2098_);
v___x_2110_ = lean_box(0);
v_isShared_2111_ = v_isSharedCheck_2115_;
goto v_resetjp_2109_;
}
v_resetjp_2109_:
{
lean_object* v___x_2113_; 
if (v_isShared_2111_ == 0)
{
v___x_2113_ = v___x_2110_;
goto v_reusejp_2112_;
}
else
{
lean_object* v_reuseFailAlloc_2114_; 
v_reuseFailAlloc_2114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2114_, 0, v_a_2108_);
v___x_2113_ = v_reuseFailAlloc_2114_;
goto v_reusejp_2112_;
}
v_reusejp_2112_:
{
return v___x_2113_;
}
}
}
}
}
else
{
lean_object* v___x_2116_; 
lean_inc(v_x_2052_);
v___x_2116_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBoolean(v_x_2052_, v_a_2053_, v_a_2054_);
if (lean_obj_tag(v___x_2116_) == 0)
{
lean_object* v_a_2117_; lean_object* v___x_2119_; uint8_t v_isShared_2120_; uint8_t v_isSharedCheck_2126_; 
v_a_2117_ = lean_ctor_get(v___x_2116_, 0);
v_isSharedCheck_2126_ = !lean_is_exclusive(v___x_2116_);
if (v_isSharedCheck_2126_ == 0)
{
v___x_2119_ = v___x_2116_;
v_isShared_2120_ = v_isSharedCheck_2126_;
goto v_resetjp_2118_;
}
else
{
lean_inc(v_a_2117_);
lean_dec(v___x_2116_);
v___x_2119_ = lean_box(0);
v_isShared_2120_ = v_isSharedCheck_2126_;
goto v_resetjp_2118_;
}
v_resetjp_2118_:
{
lean_object* v___x_2121_; uint8_t v___x_2122_; lean_object* v___x_2124_; 
v___x_2121_ = lean_alloc_ctor(3, 1, 1);
lean_ctor_set(v___x_2121_, 0, v_x_2052_);
v___x_2122_ = lean_unbox(v_a_2117_);
lean_dec(v_a_2117_);
lean_ctor_set_uint8(v___x_2121_, sizeof(void*)*1, v___x_2122_);
if (v_isShared_2120_ == 0)
{
lean_ctor_set(v___x_2119_, 0, v___x_2121_);
v___x_2124_ = v___x_2119_;
goto v_reusejp_2123_;
}
else
{
lean_object* v_reuseFailAlloc_2125_; 
v_reuseFailAlloc_2125_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2125_, 0, v___x_2121_);
v___x_2124_ = v_reuseFailAlloc_2125_;
goto v_reusejp_2123_;
}
v_reusejp_2123_:
{
return v___x_2124_;
}
}
}
else
{
lean_object* v_a_2127_; lean_object* v___x_2129_; uint8_t v_isShared_2130_; uint8_t v_isSharedCheck_2134_; 
lean_dec(v_x_2052_);
v_a_2127_ = lean_ctor_get(v___x_2116_, 0);
v_isSharedCheck_2134_ = !lean_is_exclusive(v___x_2116_);
if (v_isSharedCheck_2134_ == 0)
{
v___x_2129_ = v___x_2116_;
v_isShared_2130_ = v_isSharedCheck_2134_;
goto v_resetjp_2128_;
}
else
{
lean_inc(v_a_2127_);
lean_dec(v___x_2116_);
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
}
else
{
lean_object* v___x_2135_; 
lean_inc(v_x_2052_);
v___x_2135_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabString(v_x_2052_, v_a_2053_, v_a_2054_);
if (lean_obj_tag(v___x_2135_) == 0)
{
lean_object* v_a_2136_; lean_object* v___x_2138_; uint8_t v_isShared_2139_; uint8_t v_isSharedCheck_2144_; 
v_a_2136_ = lean_ctor_get(v___x_2135_, 0);
v_isSharedCheck_2144_ = !lean_is_exclusive(v___x_2135_);
if (v_isSharedCheck_2144_ == 0)
{
v___x_2138_ = v___x_2135_;
v_isShared_2139_ = v_isSharedCheck_2144_;
goto v_resetjp_2137_;
}
else
{
lean_inc(v_a_2136_);
lean_dec(v___x_2135_);
v___x_2138_ = lean_box(0);
v_isShared_2139_ = v_isSharedCheck_2144_;
goto v_resetjp_2137_;
}
v_resetjp_2137_:
{
lean_object* v___x_2140_; lean_object* v___x_2142_; 
v___x_2140_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2140_, 0, v_x_2052_);
lean_ctor_set(v___x_2140_, 1, v_a_2136_);
if (v_isShared_2139_ == 0)
{
lean_ctor_set(v___x_2138_, 0, v___x_2140_);
v___x_2142_ = v___x_2138_;
goto v_reusejp_2141_;
}
else
{
lean_object* v_reuseFailAlloc_2143_; 
v_reuseFailAlloc_2143_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2143_, 0, v___x_2140_);
v___x_2142_ = v_reuseFailAlloc_2143_;
goto v_reusejp_2141_;
}
v_reusejp_2141_:
{
return v___x_2142_;
}
}
}
else
{
lean_object* v_a_2145_; lean_object* v___x_2147_; uint8_t v_isShared_2148_; uint8_t v_isSharedCheck_2152_; 
lean_dec(v_x_2052_);
v_a_2145_ = lean_ctor_get(v___x_2135_, 0);
v_isSharedCheck_2152_ = !lean_is_exclusive(v___x_2135_);
if (v_isSharedCheck_2152_ == 0)
{
v___x_2147_ = v___x_2135_;
v_isShared_2148_ = v_isSharedCheck_2152_;
goto v_resetjp_2146_;
}
else
{
lean_inc(v_a_2145_);
lean_dec(v___x_2135_);
v___x_2147_ = lean_box(0);
v_isShared_2148_ = v_isSharedCheck_2152_;
goto v_resetjp_2146_;
}
v_resetjp_2146_:
{
lean_object* v___x_2150_; 
if (v_isShared_2148_ == 0)
{
v___x_2150_ = v___x_2147_;
goto v_reusejp_2149_;
}
else
{
lean_object* v_reuseFailAlloc_2151_; 
v_reuseFailAlloc_2151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2151_, 0, v_a_2145_);
v___x_2150_ = v_reuseFailAlloc_2151_;
goto v_reusejp_2149_;
}
v_reusejp_2149_:
{
return v___x_2150_;
}
}
}
}
}
else
{
lean_object* v___x_2153_; 
v___x_2153_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDateTime(v_x_2052_, v_a_2053_, v_a_2054_);
if (lean_obj_tag(v___x_2153_) == 0)
{
lean_object* v_a_2154_; lean_object* v___x_2156_; uint8_t v_isShared_2157_; uint8_t v_isSharedCheck_2162_; 
v_a_2154_ = lean_ctor_get(v___x_2153_, 0);
v_isSharedCheck_2162_ = !lean_is_exclusive(v___x_2153_);
if (v_isSharedCheck_2162_ == 0)
{
v___x_2156_ = v___x_2153_;
v_isShared_2157_ = v_isSharedCheck_2162_;
goto v_resetjp_2155_;
}
else
{
lean_inc(v_a_2154_);
lean_dec(v___x_2153_);
v___x_2156_ = lean_box(0);
v_isShared_2157_ = v_isSharedCheck_2162_;
goto v_resetjp_2155_;
}
v_resetjp_2155_:
{
lean_object* v___x_2158_; lean_object* v___x_2160_; 
v___x_2158_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_2158_, 0, v_x_2052_);
lean_ctor_set(v___x_2158_, 1, v_a_2154_);
if (v_isShared_2157_ == 0)
{
lean_ctor_set(v___x_2156_, 0, v___x_2158_);
v___x_2160_ = v___x_2156_;
goto v_reusejp_2159_;
}
else
{
lean_object* v_reuseFailAlloc_2161_; 
v_reuseFailAlloc_2161_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2161_, 0, v___x_2158_);
v___x_2160_ = v_reuseFailAlloc_2161_;
goto v_reusejp_2159_;
}
v_reusejp_2159_:
{
return v___x_2160_;
}
}
}
else
{
lean_object* v_a_2163_; lean_object* v___x_2165_; uint8_t v_isShared_2166_; uint8_t v_isSharedCheck_2170_; 
lean_dec(v_x_2052_);
v_a_2163_ = lean_ctor_get(v___x_2153_, 0);
v_isSharedCheck_2170_ = !lean_is_exclusive(v___x_2153_);
if (v_isSharedCheck_2170_ == 0)
{
v___x_2165_ = v___x_2153_;
v_isShared_2166_ = v_isSharedCheck_2170_;
goto v_resetjp_2164_;
}
else
{
lean_inc(v_a_2163_);
lean_dec(v___x_2153_);
v___x_2165_ = lean_box(0);
v_isShared_2166_ = v_isSharedCheck_2170_;
goto v_resetjp_2164_;
}
v_resetjp_2164_:
{
lean_object* v___x_2168_; 
if (v_isShared_2166_ == 0)
{
v___x_2168_ = v___x_2165_;
goto v_reusejp_2167_;
}
else
{
lean_object* v_reuseFailAlloc_2169_; 
v_reuseFailAlloc_2169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2169_, 0, v_a_2163_);
v___x_2168_ = v_reuseFailAlloc_2169_;
goto v_reusejp_2167_;
}
v_reusejp_2167_:
{
return v___x_2168_;
}
}
}
}
}
else
{
lean_object* v___x_2171_; 
v___x_2171_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabHexNum(v_x_2052_, v_a_2053_, v_a_2054_);
if (lean_obj_tag(v___x_2171_) == 0)
{
lean_object* v_a_2172_; lean_object* v___x_2174_; uint8_t v_isShared_2175_; uint8_t v_isSharedCheck_2181_; 
v_a_2172_ = lean_ctor_get(v___x_2171_, 0);
v_isSharedCheck_2181_ = !lean_is_exclusive(v___x_2171_);
if (v_isSharedCheck_2181_ == 0)
{
v___x_2174_ = v___x_2171_;
v_isShared_2175_ = v_isSharedCheck_2181_;
goto v_resetjp_2173_;
}
else
{
lean_inc(v_a_2172_);
lean_dec(v___x_2171_);
v___x_2174_ = lean_box(0);
v_isShared_2175_ = v_isSharedCheck_2181_;
goto v_resetjp_2173_;
}
v_resetjp_2173_:
{
lean_object* v___x_2176_; lean_object* v___x_2177_; lean_object* v___x_2179_; 
v___x_2176_ = lean_nat_to_int(v_a_2172_);
v___x_2177_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2177_, 0, v_x_2052_);
lean_ctor_set(v___x_2177_, 1, v___x_2176_);
if (v_isShared_2175_ == 0)
{
lean_ctor_set(v___x_2174_, 0, v___x_2177_);
v___x_2179_ = v___x_2174_;
goto v_reusejp_2178_;
}
else
{
lean_object* v_reuseFailAlloc_2180_; 
v_reuseFailAlloc_2180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2180_, 0, v___x_2177_);
v___x_2179_ = v_reuseFailAlloc_2180_;
goto v_reusejp_2178_;
}
v_reusejp_2178_:
{
return v___x_2179_;
}
}
}
else
{
lean_object* v_a_2182_; lean_object* v___x_2184_; uint8_t v_isShared_2185_; uint8_t v_isSharedCheck_2189_; 
lean_dec(v_x_2052_);
v_a_2182_ = lean_ctor_get(v___x_2171_, 0);
v_isSharedCheck_2189_ = !lean_is_exclusive(v___x_2171_);
if (v_isSharedCheck_2189_ == 0)
{
v___x_2184_ = v___x_2171_;
v_isShared_2185_ = v_isSharedCheck_2189_;
goto v_resetjp_2183_;
}
else
{
lean_inc(v_a_2182_);
lean_dec(v___x_2171_);
v___x_2184_ = lean_box(0);
v_isShared_2185_ = v_isSharedCheck_2189_;
goto v_resetjp_2183_;
}
v_resetjp_2183_:
{
lean_object* v___x_2187_; 
if (v_isShared_2185_ == 0)
{
v___x_2187_ = v___x_2184_;
goto v_reusejp_2186_;
}
else
{
lean_object* v_reuseFailAlloc_2188_; 
v_reuseFailAlloc_2188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2188_, 0, v_a_2182_);
v___x_2187_ = v_reuseFailAlloc_2188_;
goto v_reusejp_2186_;
}
v_reusejp_2186_:
{
return v___x_2187_;
}
}
}
}
}
else
{
lean_object* v___x_2190_; 
v___x_2190_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabOctNum(v_x_2052_, v_a_2053_, v_a_2054_);
if (lean_obj_tag(v___x_2190_) == 0)
{
lean_object* v_a_2191_; lean_object* v___x_2193_; uint8_t v_isShared_2194_; uint8_t v_isSharedCheck_2200_; 
v_a_2191_ = lean_ctor_get(v___x_2190_, 0);
v_isSharedCheck_2200_ = !lean_is_exclusive(v___x_2190_);
if (v_isSharedCheck_2200_ == 0)
{
v___x_2193_ = v___x_2190_;
v_isShared_2194_ = v_isSharedCheck_2200_;
goto v_resetjp_2192_;
}
else
{
lean_inc(v_a_2191_);
lean_dec(v___x_2190_);
v___x_2193_ = lean_box(0);
v_isShared_2194_ = v_isSharedCheck_2200_;
goto v_resetjp_2192_;
}
v_resetjp_2192_:
{
lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2198_; 
v___x_2195_ = lean_nat_to_int(v_a_2191_);
v___x_2196_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2196_, 0, v_x_2052_);
lean_ctor_set(v___x_2196_, 1, v___x_2195_);
if (v_isShared_2194_ == 0)
{
lean_ctor_set(v___x_2193_, 0, v___x_2196_);
v___x_2198_ = v___x_2193_;
goto v_reusejp_2197_;
}
else
{
lean_object* v_reuseFailAlloc_2199_; 
v_reuseFailAlloc_2199_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2199_, 0, v___x_2196_);
v___x_2198_ = v_reuseFailAlloc_2199_;
goto v_reusejp_2197_;
}
v_reusejp_2197_:
{
return v___x_2198_;
}
}
}
else
{
lean_object* v_a_2201_; lean_object* v___x_2203_; uint8_t v_isShared_2204_; uint8_t v_isSharedCheck_2208_; 
lean_dec(v_x_2052_);
v_a_2201_ = lean_ctor_get(v___x_2190_, 0);
v_isSharedCheck_2208_ = !lean_is_exclusive(v___x_2190_);
if (v_isSharedCheck_2208_ == 0)
{
v___x_2203_ = v___x_2190_;
v_isShared_2204_ = v_isSharedCheck_2208_;
goto v_resetjp_2202_;
}
else
{
lean_inc(v_a_2201_);
lean_dec(v___x_2190_);
v___x_2203_ = lean_box(0);
v_isShared_2204_ = v_isSharedCheck_2208_;
goto v_resetjp_2202_;
}
v_resetjp_2202_:
{
lean_object* v___x_2206_; 
if (v_isShared_2204_ == 0)
{
v___x_2206_ = v___x_2203_;
goto v_reusejp_2205_;
}
else
{
lean_object* v_reuseFailAlloc_2207_; 
v_reuseFailAlloc_2207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2207_, 0, v_a_2201_);
v___x_2206_ = v_reuseFailAlloc_2207_;
goto v_reusejp_2205_;
}
v_reusejp_2205_:
{
return v___x_2206_;
}
}
}
}
}
else
{
lean_object* v___x_2209_; 
v___x_2209_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabBinNum(v_x_2052_, v_a_2053_, v_a_2054_);
if (lean_obj_tag(v___x_2209_) == 0)
{
lean_object* v_a_2210_; lean_object* v___x_2212_; uint8_t v_isShared_2213_; uint8_t v_isSharedCheck_2219_; 
v_a_2210_ = lean_ctor_get(v___x_2209_, 0);
v_isSharedCheck_2219_ = !lean_is_exclusive(v___x_2209_);
if (v_isSharedCheck_2219_ == 0)
{
v___x_2212_ = v___x_2209_;
v_isShared_2213_ = v_isSharedCheck_2219_;
goto v_resetjp_2211_;
}
else
{
lean_inc(v_a_2210_);
lean_dec(v___x_2209_);
v___x_2212_ = lean_box(0);
v_isShared_2213_ = v_isSharedCheck_2219_;
goto v_resetjp_2211_;
}
v_resetjp_2211_:
{
lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2217_; 
v___x_2214_ = lean_nat_to_int(v_a_2210_);
v___x_2215_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2215_, 0, v_x_2052_);
lean_ctor_set(v___x_2215_, 1, v___x_2214_);
if (v_isShared_2213_ == 0)
{
lean_ctor_set(v___x_2212_, 0, v___x_2215_);
v___x_2217_ = v___x_2212_;
goto v_reusejp_2216_;
}
else
{
lean_object* v_reuseFailAlloc_2218_; 
v_reuseFailAlloc_2218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2218_, 0, v___x_2215_);
v___x_2217_ = v_reuseFailAlloc_2218_;
goto v_reusejp_2216_;
}
v_reusejp_2216_:
{
return v___x_2217_;
}
}
}
else
{
lean_object* v_a_2220_; lean_object* v___x_2222_; uint8_t v_isShared_2223_; uint8_t v_isSharedCheck_2227_; 
lean_dec(v_x_2052_);
v_a_2220_ = lean_ctor_get(v___x_2209_, 0);
v_isSharedCheck_2227_ = !lean_is_exclusive(v___x_2209_);
if (v_isSharedCheck_2227_ == 0)
{
v___x_2222_ = v___x_2209_;
v_isShared_2223_ = v_isSharedCheck_2227_;
goto v_resetjp_2221_;
}
else
{
lean_inc(v_a_2220_);
lean_dec(v___x_2209_);
v___x_2222_ = lean_box(0);
v_isShared_2223_ = v_isSharedCheck_2227_;
goto v_resetjp_2221_;
}
v_resetjp_2221_:
{
lean_object* v___x_2225_; 
if (v_isShared_2223_ == 0)
{
v___x_2225_ = v___x_2222_;
goto v_reusejp_2224_;
}
else
{
lean_object* v_reuseFailAlloc_2226_; 
v_reuseFailAlloc_2226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2226_, 0, v_a_2220_);
v___x_2225_ = v_reuseFailAlloc_2226_;
goto v_reusejp_2224_;
}
v_reusejp_2224_:
{
return v___x_2225_;
}
}
}
}
}
else
{
lean_object* v___x_2228_; 
v___x_2228_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabDecInt(v_x_2052_, v_a_2053_, v_a_2054_);
if (lean_obj_tag(v___x_2228_) == 0)
{
lean_object* v_a_2229_; lean_object* v___x_2231_; uint8_t v_isShared_2232_; uint8_t v_isSharedCheck_2237_; 
v_a_2229_ = lean_ctor_get(v___x_2228_, 0);
v_isSharedCheck_2237_ = !lean_is_exclusive(v___x_2228_);
if (v_isSharedCheck_2237_ == 0)
{
v___x_2231_ = v___x_2228_;
v_isShared_2232_ = v_isSharedCheck_2237_;
goto v_resetjp_2230_;
}
else
{
lean_inc(v_a_2229_);
lean_dec(v___x_2228_);
v___x_2231_ = lean_box(0);
v_isShared_2232_ = v_isSharedCheck_2237_;
goto v_resetjp_2230_;
}
v_resetjp_2230_:
{
lean_object* v___x_2233_; lean_object* v___x_2235_; 
v___x_2233_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2233_, 0, v_x_2052_);
lean_ctor_set(v___x_2233_, 1, v_a_2229_);
if (v_isShared_2232_ == 0)
{
lean_ctor_set(v___x_2231_, 0, v___x_2233_);
v___x_2235_ = v___x_2231_;
goto v_reusejp_2234_;
}
else
{
lean_object* v_reuseFailAlloc_2236_; 
v_reuseFailAlloc_2236_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2236_, 0, v___x_2233_);
v___x_2235_ = v_reuseFailAlloc_2236_;
goto v_reusejp_2234_;
}
v_reusejp_2234_:
{
return v___x_2235_;
}
}
}
else
{
lean_object* v_a_2238_; lean_object* v___x_2240_; uint8_t v_isShared_2241_; uint8_t v_isSharedCheck_2245_; 
lean_dec(v_x_2052_);
v_a_2238_ = lean_ctor_get(v___x_2228_, 0);
v_isSharedCheck_2245_ = !lean_is_exclusive(v___x_2228_);
if (v_isSharedCheck_2245_ == 0)
{
v___x_2240_ = v___x_2228_;
v_isShared_2241_ = v_isSharedCheck_2245_;
goto v_resetjp_2239_;
}
else
{
lean_inc(v_a_2238_);
lean_dec(v___x_2228_);
v___x_2240_ = lean_box(0);
v_isShared_2241_ = v_isSharedCheck_2245_;
goto v_resetjp_2239_;
}
v_resetjp_2239_:
{
lean_object* v___x_2243_; 
if (v_isShared_2241_ == 0)
{
v___x_2243_ = v___x_2240_;
goto v_reusejp_2242_;
}
else
{
lean_object* v_reuseFailAlloc_2244_; 
v_reuseFailAlloc_2244_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2244_, 0, v_a_2238_);
v___x_2243_ = v_reuseFailAlloc_2244_;
goto v_reusejp_2242_;
}
v_reusejp_2242_:
{
return v___x_2243_;
}
}
}
}
}
else
{
lean_object* v___x_2246_; 
v___x_2246_ = l___private_Lake_Toml_Elab_Value_0__Lake_Toml_elabFloat(v_x_2052_, v_a_2053_, v_a_2054_);
if (lean_obj_tag(v___x_2246_) == 0)
{
lean_object* v_a_2247_; lean_object* v___x_2249_; uint8_t v_isShared_2250_; uint8_t v_isSharedCheck_2256_; 
v_a_2247_ = lean_ctor_get(v___x_2246_, 0);
v_isSharedCheck_2256_ = !lean_is_exclusive(v___x_2246_);
if (v_isSharedCheck_2256_ == 0)
{
v___x_2249_ = v___x_2246_;
v_isShared_2250_ = v_isSharedCheck_2256_;
goto v_resetjp_2248_;
}
else
{
lean_inc(v_a_2247_);
lean_dec(v___x_2246_);
v___x_2249_ = lean_box(0);
v_isShared_2250_ = v_isSharedCheck_2256_;
goto v_resetjp_2248_;
}
v_resetjp_2248_:
{
lean_object* v___x_2251_; double v___x_2252_; lean_object* v___x_2254_; 
v___x_2251_ = lean_alloc_ctor(2, 1, 8);
lean_ctor_set(v___x_2251_, 0, v_x_2052_);
v___x_2252_ = lean_unbox_float(v_a_2247_);
lean_dec(v_a_2247_);
lean_ctor_set_float(v___x_2251_, sizeof(void*)*1, v___x_2252_);
if (v_isShared_2250_ == 0)
{
lean_ctor_set(v___x_2249_, 0, v___x_2251_);
v___x_2254_ = v___x_2249_;
goto v_reusejp_2253_;
}
else
{
lean_object* v_reuseFailAlloc_2255_; 
v_reuseFailAlloc_2255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2255_, 0, v___x_2251_);
v___x_2254_ = v_reuseFailAlloc_2255_;
goto v_reusejp_2253_;
}
v_reusejp_2253_:
{
return v___x_2254_;
}
}
}
else
{
lean_object* v_a_2257_; lean_object* v___x_2259_; uint8_t v_isShared_2260_; uint8_t v_isSharedCheck_2264_; 
lean_dec(v_x_2052_);
v_a_2257_ = lean_ctor_get(v___x_2246_, 0);
v_isSharedCheck_2264_ = !lean_is_exclusive(v___x_2246_);
if (v_isSharedCheck_2264_ == 0)
{
v___x_2259_ = v___x_2246_;
v_isShared_2260_ = v_isSharedCheck_2264_;
goto v_resetjp_2258_;
}
else
{
lean_inc(v_a_2257_);
lean_dec(v___x_2246_);
v___x_2259_ = lean_box(0);
v_isShared_2260_ = v_isSharedCheck_2264_;
goto v_resetjp_2258_;
}
v_resetjp_2258_:
{
lean_object* v___x_2262_; 
if (v_isShared_2260_ == 0)
{
v___x_2262_ = v___x_2259_;
goto v_reusejp_2261_;
}
else
{
lean_object* v_reuseFailAlloc_2263_; 
v_reuseFailAlloc_2263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2263_, 0, v_a_2257_);
v___x_2262_ = v_reuseFailAlloc_2263_;
goto v_reusejp_2261_;
}
v_reusejp_2261_:
{
return v___x_2262_;
}
}
}
}
}
}
lean_object* runtime_initialize_Lake_Toml_Data_Value(uint8_t builtin);
lean_object* runtime_initialize_Lake_Toml_Grammar(uint8_t builtin);
void lean_initialize();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Toml_Elab_Value(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize();
res = runtime_initialize_Lake_Toml_Data_Value(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Toml_Grammar(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Lake_Toml_Grammar(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_Toml_Elab_Value(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Lake_Toml_Grammar(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lake_Toml_Data_Value(uint8_t builtin);
lean_object* initialize_Lake_Toml_Grammar(uint8_t builtin);
lean_object* initialize_Lake_Toml_Grammar(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Toml_Elab_Value(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Toml_Data_Value(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Toml_Grammar(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Toml_Grammar(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Toml_Elab_Value(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_Toml_Elab_Value(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_Toml_Elab_Value(builtin);
}
#ifdef __cplusplus
}
#endif
