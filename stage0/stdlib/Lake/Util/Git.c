// Lean compiler output
// Module: Lake.Util.Git
// Imports: public import Init.Data.ToString public import Lake.Util.Proc import Init.Data.String.TakeDrop import Init.Data.String.Search import Lake.Util.String
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lake_proc(lean_object*, uint8_t, lean_object*);
lean_object* l_Lake_captureProc_x3f(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_string_memcmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_Pos_prevn(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
uint8_t l_Lake_testProc(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_String_Slice_toString(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_String_Slice_subslice_x21(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
uint8_t l_Lake_isHex(lean_object*);
uint8_t l_System_FilePath_isDir(lean_object*);
lean_object* l_Lake_captureProc_x27(lean_object*, lean_object*);
lean_object* l_String_Slice_trimAscii(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
static const lean_string_object l_Lake_Git_defaultRemote___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "origin"};
static const lean_object* l_Lake_Git_defaultRemote___closed__0 = (const lean_object*)&l_Lake_Git_defaultRemote___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_Git_defaultRemote = (const lean_object*)&l_Lake_Git_defaultRemote___closed__0_value;
static const lean_string_object l_Lake_Git_upstreamBranch___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "master"};
static const lean_object* l_Lake_Git_upstreamBranch___closed__0 = (const lean_object*)&l_Lake_Git_upstreamBranch___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_Git_upstreamBranch = (const lean_object*)&l_Lake_Git_upstreamBranch___closed__0_value;
static const lean_string_object l_Lake_Git_filterUrl_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = ".git"};
static const lean_object* l_Lake_Git_filterUrl_x3f___closed__0 = (const lean_object*)&l_Lake_Git_filterUrl_x3f___closed__0_value;
static lean_once_cell_t l_Lake_Git_filterUrl_x3f___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Git_filterUrl_x3f___closed__1;
static const lean_string_object l_Lake_Git_filterUrl_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "git"};
static const lean_object* l_Lake_Git_filterUrl_x3f___closed__2 = (const lean_object*)&l_Lake_Git_filterUrl_x3f___closed__2_value;
static lean_once_cell_t l_Lake_Git_filterUrl_x3f___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Git_filterUrl_x3f___closed__3;
LEAN_EXPORT lean_object* l_Lake_Git_filterUrl_x3f(lean_object*);
LEAN_EXPORT uint8_t l_Lake_Git_isFullObjectName(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Git_isFullObjectName___boxed(lean_object*);
static const lean_string_object l_Lake_GitRev_head___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HEAD"};
static const lean_object* l_Lake_GitRev_head___closed__0 = (const lean_object*)&l_Lake_GitRev_head___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_GitRev_head = (const lean_object*)&l_Lake_GitRev_head___closed__0_value;
static const lean_string_object l_Lake_GitRev_fetchHead___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "FETCH_HEAD"};
static const lean_object* l_Lake_GitRev_fetchHead___closed__0 = (const lean_object*)&l_Lake_GitRev_fetchHead___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_GitRev_fetchHead = (const lean_object*)&l_Lake_GitRev_fetchHead___closed__0_value;
LEAN_EXPORT uint8_t l_Lake_GitRev_isFullSha1(lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRev_isFullSha1___boxed(lean_object*);
static const lean_string_object l_Lake_GitRev_withRemote___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "/"};
static const lean_object* l_Lake_GitRev_withRemote___closed__0 = (const lean_object*)&l_Lake_GitRev_withRemote___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_GitRev_withRemote(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRev_withRemote___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_instCoeFilePath___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_instCoeFilePath___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lake_GitRepo_instCoeFilePath___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_GitRepo_instCoeFilePath___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_GitRepo_instCoeFilePath___closed__0 = (const lean_object*)&l_Lake_GitRepo_instCoeFilePath___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_GitRepo_instCoeFilePath = (const lean_object*)&l_Lake_GitRepo_instCoeFilePath___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_GitRepo_instToString = (const lean_object*)&l_Lake_GitRepo_instCoeFilePath___closed__0_value;
static const lean_string_object l_Lake_GitRepo_cwd___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l_Lake_GitRepo_cwd___closed__0 = (const lean_object*)&l_Lake_GitRepo_cwd___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_GitRepo_cwd = (const lean_object*)&l_Lake_GitRepo_cwd___closed__0_value;
LEAN_EXPORT uint8_t l_Lake_GitRepo_dirExists(lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_dirExists___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_Lake_GitRepo_captureGit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(1, 1, 1, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lake_GitRepo_captureGit___closed__0 = (const lean_object*)&l_Lake_GitRepo_captureGit___closed__0_value;
static const lean_array_object l_Lake_GitRepo_captureGit___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_GitRepo_captureGit___closed__1 = (const lean_object*)&l_Lake_GitRepo_captureGit___closed__1_value;
LEAN_EXPORT lean_object* l_Lake_GitRepo_captureGit(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_captureGit___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_captureGit_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_captureGit_x3f___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_execGit(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_execGit___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_GitRepo_testGit(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_testGit___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_GitRepo_clone___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "clone"};
static const lean_object* l_Lake_GitRepo_clone___closed__0 = (const lean_object*)&l_Lake_GitRepo_clone___closed__0_value;
static lean_once_cell_t l_Lake_GitRepo_clone___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_clone___closed__1;
LEAN_EXPORT lean_object* l_Lake_GitRepo_clone(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_clone___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_GitRepo_quietInit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "init"};
static const lean_object* l_Lake_GitRepo_quietInit___closed__0 = (const lean_object*)&l_Lake_GitRepo_quietInit___closed__0_value;
static const lean_string_object l_Lake_GitRepo_quietInit___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "-q"};
static const lean_object* l_Lake_GitRepo_quietInit___closed__1 = (const lean_object*)&l_Lake_GitRepo_quietInit___closed__1_value;
static const lean_array_object l_Lake_GitRepo_quietInit___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 246}, .m_size = 2, .m_capacity = 2, .m_data = {((lean_object*)&l_Lake_GitRepo_quietInit___closed__0_value),((lean_object*)&l_Lake_GitRepo_quietInit___closed__1_value)}};
static const lean_object* l_Lake_GitRepo_quietInit___closed__2 = (const lean_object*)&l_Lake_GitRepo_quietInit___closed__2_value;
LEAN_EXPORT lean_object* l_Lake_GitRepo_quietInit(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_quietInit___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_GitRepo_bareInit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "--bare"};
static const lean_object* l_Lake_GitRepo_bareInit___closed__0 = (const lean_object*)&l_Lake_GitRepo_bareInit___closed__0_value;
static const lean_array_object l_Lake_GitRepo_bareInit___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 246}, .m_size = 3, .m_capacity = 3, .m_data = {((lean_object*)&l_Lake_GitRepo_quietInit___closed__0_value),((lean_object*)&l_Lake_GitRepo_bareInit___closed__0_value),((lean_object*)&l_Lake_GitRepo_quietInit___closed__1_value)}};
static const lean_object* l_Lake_GitRepo_bareInit___closed__1 = (const lean_object*)&l_Lake_GitRepo_bareInit___closed__1_value;
LEAN_EXPORT lean_object* l_Lake_GitRepo_bareInit(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_bareInit___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_GitRepo_insideWorkTree___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "rev-parse"};
static const lean_object* l_Lake_GitRepo_insideWorkTree___closed__0 = (const lean_object*)&l_Lake_GitRepo_insideWorkTree___closed__0_value;
static const lean_string_object l_Lake_GitRepo_insideWorkTree___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "--is-inside-work-tree"};
static const lean_object* l_Lake_GitRepo_insideWorkTree___closed__1 = (const lean_object*)&l_Lake_GitRepo_insideWorkTree___closed__1_value;
static const lean_array_object l_Lake_GitRepo_insideWorkTree___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 246}, .m_size = 2, .m_capacity = 2, .m_data = {((lean_object*)&l_Lake_GitRepo_insideWorkTree___closed__0_value),((lean_object*)&l_Lake_GitRepo_insideWorkTree___closed__1_value)}};
static const lean_object* l_Lake_GitRepo_insideWorkTree___closed__2 = (const lean_object*)&l_Lake_GitRepo_insideWorkTree___closed__2_value;
LEAN_EXPORT uint8_t l_Lake_GitRepo_insideWorkTree(lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_insideWorkTree___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lake_GitRepo_fetch___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "fetch"};
static const lean_object* l_Lake_GitRepo_fetch___closed__0 = (const lean_object*)&l_Lake_GitRepo_fetch___closed__0_value;
static const lean_string_object l_Lake_GitRepo_fetch___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "--tags"};
static const lean_object* l_Lake_GitRepo_fetch___closed__1 = (const lean_object*)&l_Lake_GitRepo_fetch___closed__1_value;
static const lean_string_object l_Lake_GitRepo_fetch___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "--force"};
static const lean_object* l_Lake_GitRepo_fetch___closed__2 = (const lean_object*)&l_Lake_GitRepo_fetch___closed__2_value;
static lean_once_cell_t l_Lake_GitRepo_fetch___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_fetch___closed__3;
static lean_once_cell_t l_Lake_GitRepo_fetch___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_fetch___closed__4;
static lean_once_cell_t l_Lake_GitRepo_fetch___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_fetch___closed__5;
LEAN_EXPORT lean_object* l_Lake_GitRepo_fetch(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_fetch___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_GitRepo_addWorktreeDetach___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "worktree"};
static const lean_object* l_Lake_GitRepo_addWorktreeDetach___closed__0 = (const lean_object*)&l_Lake_GitRepo_addWorktreeDetach___closed__0_value;
static const lean_string_object l_Lake_GitRepo_addWorktreeDetach___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "add"};
static const lean_object* l_Lake_GitRepo_addWorktreeDetach___closed__1 = (const lean_object*)&l_Lake_GitRepo_addWorktreeDetach___closed__1_value;
static const lean_string_object l_Lake_GitRepo_addWorktreeDetach___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "--detach"};
static const lean_object* l_Lake_GitRepo_addWorktreeDetach___closed__2 = (const lean_object*)&l_Lake_GitRepo_addWorktreeDetach___closed__2_value;
static lean_once_cell_t l_Lake_GitRepo_addWorktreeDetach___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_addWorktreeDetach___closed__3;
static lean_once_cell_t l_Lake_GitRepo_addWorktreeDetach___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_addWorktreeDetach___closed__4;
static lean_once_cell_t l_Lake_GitRepo_addWorktreeDetach___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_addWorktreeDetach___closed__5;
LEAN_EXPORT lean_object* l_Lake_GitRepo_addWorktreeDetach(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_addWorktreeDetach___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_GitRepo_checkoutBranch___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "checkout"};
static const lean_object* l_Lake_GitRepo_checkoutBranch___closed__0 = (const lean_object*)&l_Lake_GitRepo_checkoutBranch___closed__0_value;
static const lean_string_object l_Lake_GitRepo_checkoutBranch___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "-B"};
static const lean_object* l_Lake_GitRepo_checkoutBranch___closed__1 = (const lean_object*)&l_Lake_GitRepo_checkoutBranch___closed__1_value;
static lean_once_cell_t l_Lake_GitRepo_checkoutBranch___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_checkoutBranch___closed__2;
static lean_once_cell_t l_Lake_GitRepo_checkoutBranch___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_checkoutBranch___closed__3;
LEAN_EXPORT lean_object* l_Lake_GitRepo_checkoutBranch(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_checkoutBranch___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_GitRepo_checkoutDetach___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "--"};
static const lean_object* l_Lake_GitRepo_checkoutDetach___closed__0 = (const lean_object*)&l_Lake_GitRepo_checkoutDetach___closed__0_value;
static lean_once_cell_t l_Lake_GitRepo_checkoutDetach___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_checkoutDetach___closed__1;
static lean_once_cell_t l_Lake_GitRepo_checkoutDetach___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_checkoutDetach___closed__2;
LEAN_EXPORT lean_object* l_Lake_GitRepo_checkoutDetach(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_checkoutDetach___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_GitRepo_clean___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "clean"};
static const lean_object* l_Lake_GitRepo_clean___closed__0 = (const lean_object*)&l_Lake_GitRepo_clean___closed__0_value;
static const lean_string_object l_Lake_GitRepo_clean___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "-xf"};
static const lean_object* l_Lake_GitRepo_clean___closed__1 = (const lean_object*)&l_Lake_GitRepo_clean___closed__1_value;
static const lean_array_object l_Lake_GitRepo_clean___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 246}, .m_size = 2, .m_capacity = 2, .m_data = {((lean_object*)&l_Lake_GitRepo_clean___closed__0_value),((lean_object*)&l_Lake_GitRepo_clean___closed__1_value)}};
static const lean_object* l_Lake_GitRepo_clean___closed__2 = (const lean_object*)&l_Lake_GitRepo_clean___closed__2_value;
LEAN_EXPORT lean_object* l_Lake_GitRepo_clean(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_clean___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_GitRepo_resolveRevision_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "--verify"};
static const lean_object* l_Lake_GitRepo_resolveRevision_x3f___closed__0 = (const lean_object*)&l_Lake_GitRepo_resolveRevision_x3f___closed__0_value;
static const lean_string_object l_Lake_GitRepo_resolveRevision_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "--end-of-options"};
static const lean_object* l_Lake_GitRepo_resolveRevision_x3f___closed__1 = (const lean_object*)&l_Lake_GitRepo_resolveRevision_x3f___closed__1_value;
static lean_once_cell_t l_Lake_GitRepo_resolveRevision_x3f___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_resolveRevision_x3f___closed__2;
static lean_once_cell_t l_Lake_GitRepo_resolveRevision_x3f___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_resolveRevision_x3f___closed__3;
static lean_once_cell_t l_Lake_GitRepo_resolveRevision_x3f___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_resolveRevision_x3f___closed__4;
LEAN_EXPORT lean_object* l_Lake_GitRepo_resolveRevision_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_resolveRevision_x3f___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_GitRepo_findCommit_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "^{commit}"};
static const lean_object* l_Lake_GitRepo_findCommit_x3f___closed__0 = (const lean_object*)&l_Lake_GitRepo_findCommit_x3f___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_GitRepo_findCommit_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_findCommit_x3f___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_GitRepo_resolveRevision___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = ": revision not found '"};
static const lean_object* l_Lake_GitRepo_resolveRevision___closed__0 = (const lean_object*)&l_Lake_GitRepo_resolveRevision___closed__0_value;
static const lean_string_object l_Lake_GitRepo_resolveRevision___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l_Lake_GitRepo_resolveRevision___closed__1 = (const lean_object*)&l_Lake_GitRepo_resolveRevision___closed__1_value;
LEAN_EXPORT lean_object* l_Lake_GitRepo_resolveRevision(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_resolveRevision___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_getHeadRevision_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_getHeadRevision_x3f___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lake_GitRepo_getHeadRevision___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 114, .m_capacity = 114, .m_length = 113, .m_data = ": could not resolve 'HEAD' to a commit; the repository may be corrupt, so you may need to remove it and try again"};
static const lean_object* l_Lake_GitRepo_getHeadRevision___closed__0 = (const lean_object*)&l_Lake_GitRepo_getHeadRevision___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_GitRepo_getHeadRevision(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_getHeadRevision___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_GitRepo_fetchRevision_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "--refetch"};
static const lean_object* l_Lake_GitRepo_fetchRevision_x3f___closed__0 = (const lean_object*)&l_Lake_GitRepo_fetchRevision_x3f___closed__0_value;
static const lean_string_object l_Lake_GitRepo_fetchRevision_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "--filter=tree:0"};
static const lean_object* l_Lake_GitRepo_fetchRevision_x3f___closed__1 = (const lean_object*)&l_Lake_GitRepo_fetchRevision_x3f___closed__1_value;
static lean_once_cell_t l_Lake_GitRepo_fetchRevision_x3f___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_fetchRevision_x3f___closed__2;
static lean_once_cell_t l_Lake_GitRepo_fetchRevision_x3f___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_fetchRevision_x3f___closed__3;
static lean_once_cell_t l_Lake_GitRepo_fetchRevision_x3f___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_fetchRevision_x3f___closed__4;
static lean_once_cell_t l_Lake_GitRepo_fetchRevision_x3f___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_fetchRevision_x3f___closed__5;
static lean_once_cell_t l_Lake_GitRepo_fetchRevision_x3f___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_fetchRevision_x3f___closed__6;
static const lean_string_object l_Lake_GitRepo_fetchRevision_x3f___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 110, .m_capacity = 110, .m_length = 109, .m_data = ": could not resolve 'FETCH_HEAD' to a commit after fetching; this may be an issue with Lake; please report it"};
static const lean_object* l_Lake_GitRepo_fetchRevision_x3f___closed__7 = (const lean_object*)&l_Lake_GitRepo_fetchRevision_x3f___closed__7_value;
LEAN_EXPORT lean_object* l_Lake_GitRepo_fetchRevision_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_fetchRevision_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_String_Slice_splitToSubslice___at___00Lake_GitRepo_getHeadRevisions_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_String_Slice_splitToSubslice___at___00Lake_GitRepo_getHeadRevisions_spec__0___closed__0 = (const lean_object*)&l_String_Slice_splitToSubslice___at___00Lake_GitRepo_getHeadRevisions_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_GitRepo_getHeadRevisions_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_GitRepo_getHeadRevisions_spec__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_GitRepo_getHeadRevisions_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_GitRepo_getHeadRevisions_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_GitRepo_getHeadRevisions___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "rev-list"};
static const lean_object* l_Lake_GitRepo_getHeadRevisions___closed__0 = (const lean_object*)&l_Lake_GitRepo_getHeadRevisions___closed__0_value;
static const lean_array_object l_Lake_GitRepo_getHeadRevisions___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 246}, .m_size = 2, .m_capacity = 2, .m_data = {((lean_object*)&l_Lake_GitRepo_getHeadRevisions___closed__0_value),((lean_object*)&l_Lake_GitRev_head___closed__0_value)}};
static const lean_object* l_Lake_GitRepo_getHeadRevisions___closed__1 = (const lean_object*)&l_Lake_GitRepo_getHeadRevisions___closed__1_value;
static const lean_string_object l_Lake_GitRepo_getHeadRevisions___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "-n"};
static const lean_object* l_Lake_GitRepo_getHeadRevisions___closed__2 = (const lean_object*)&l_Lake_GitRepo_getHeadRevisions___closed__2_value;
static lean_once_cell_t l_Lake_GitRepo_getHeadRevisions___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_getHeadRevisions___closed__3;
LEAN_EXPORT lean_object* l_Lake_GitRepo_getHeadRevisions(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_getHeadRevisions___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_GitRepo_getHeadRevisions_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_GitRepo_getHeadRevisions_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_resolveRemoteRevision(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_resolveRemoteRevision___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_findRemoteRevision(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_findRemoteRevision___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_GitRepo_branchExists___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "show-ref"};
static const lean_object* l_Lake_GitRepo_branchExists___closed__0 = (const lean_object*)&l_Lake_GitRepo_branchExists___closed__0_value;
static const lean_string_object l_Lake_GitRepo_branchExists___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "refs/heads/"};
static const lean_object* l_Lake_GitRepo_branchExists___closed__1 = (const lean_object*)&l_Lake_GitRepo_branchExists___closed__1_value;
static lean_once_cell_t l_Lake_GitRepo_branchExists___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_branchExists___closed__2;
static lean_once_cell_t l_Lake_GitRepo_branchExists___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_branchExists___closed__3;
LEAN_EXPORT uint8_t l_Lake_GitRepo_branchExists(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_branchExists___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lake_GitRepo_revisionExists___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_revisionExists___closed__0;
static lean_once_cell_t l_Lake_GitRepo_revisionExists___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_revisionExists___closed__1;
LEAN_EXPORT uint8_t l_Lake_GitRepo_revisionExists(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_revisionExists___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_GitRepo_getTags___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "tag"};
static const lean_object* l_Lake_GitRepo_getTags___closed__0 = (const lean_object*)&l_Lake_GitRepo_getTags___closed__0_value;
static const lean_array_object l_Lake_GitRepo_getTags___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 246}, .m_size = 1, .m_capacity = 1, .m_data = {((lean_object*)&l_Lake_GitRepo_getTags___closed__0_value)}};
static const lean_object* l_Lake_GitRepo_getTags___closed__1 = (const lean_object*)&l_Lake_GitRepo_getTags___closed__1_value;
LEAN_EXPORT lean_object* l_Lake_GitRepo_getTags(lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_getTags___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lake_GitRepo_findTag_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "describe"};
static const lean_object* l_Lake_GitRepo_findTag_x3f___closed__0 = (const lean_object*)&l_Lake_GitRepo_findTag_x3f___closed__0_value;
static const lean_string_object l_Lake_GitRepo_findTag_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "--exact-match"};
static const lean_object* l_Lake_GitRepo_findTag_x3f___closed__1 = (const lean_object*)&l_Lake_GitRepo_findTag_x3f___closed__1_value;
static lean_once_cell_t l_Lake_GitRepo_findTag_x3f___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_findTag_x3f___closed__2;
static lean_once_cell_t l_Lake_GitRepo_findTag_x3f___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_findTag_x3f___closed__3;
static lean_once_cell_t l_Lake_GitRepo_findTag_x3f___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_findTag_x3f___closed__4;
LEAN_EXPORT lean_object* l_Lake_GitRepo_findTag_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_findTag_x3f___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_GitRepo_getRemoteUrl_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "remote"};
static const lean_object* l_Lake_GitRepo_getRemoteUrl_x3f___closed__0 = (const lean_object*)&l_Lake_GitRepo_getRemoteUrl_x3f___closed__0_value;
static const lean_string_object l_Lake_GitRepo_getRemoteUrl_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "get-url"};
static const lean_object* l_Lake_GitRepo_getRemoteUrl_x3f___closed__1 = (const lean_object*)&l_Lake_GitRepo_getRemoteUrl_x3f___closed__1_value;
static lean_once_cell_t l_Lake_GitRepo_getRemoteUrl_x3f___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_getRemoteUrl_x3f___closed__2;
static lean_once_cell_t l_Lake_GitRepo_getRemoteUrl_x3f___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_getRemoteUrl_x3f___closed__3;
LEAN_EXPORT lean_object* l_Lake_GitRepo_getRemoteUrl_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_getRemoteUrl_x3f___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lake_GitRepo_addRemote___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_addRemote___closed__0;
static lean_once_cell_t l_Lake_GitRepo_addRemote___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_addRemote___closed__1;
LEAN_EXPORT lean_object* l_Lake_GitRepo_addRemote(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_addRemote___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_GitRepo_setRemoteUrl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "set-url"};
static const lean_object* l_Lake_GitRepo_setRemoteUrl___closed__0 = (const lean_object*)&l_Lake_GitRepo_setRemoteUrl___closed__0_value;
static lean_once_cell_t l_Lake_GitRepo_setRemoteUrl___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_GitRepo_setRemoteUrl___closed__1;
LEAN_EXPORT lean_object* l_Lake_GitRepo_setRemoteUrl(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_setRemoteUrl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_getFilteredRemoteUrl_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_getFilteredRemoteUrl_x3f___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_GitRepo_hasNoDiff___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "diff"};
static const lean_object* l_Lake_GitRepo_hasNoDiff___closed__0 = (const lean_object*)&l_Lake_GitRepo_hasNoDiff___closed__0_value;
static const lean_string_object l_Lake_GitRepo_hasNoDiff___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "--exit-code"};
static const lean_object* l_Lake_GitRepo_hasNoDiff___closed__1 = (const lean_object*)&l_Lake_GitRepo_hasNoDiff___closed__1_value;
static const lean_array_object l_Lake_GitRepo_hasNoDiff___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 246}, .m_size = 3, .m_capacity = 3, .m_data = {((lean_object*)&l_Lake_GitRepo_hasNoDiff___closed__0_value),((lean_object*)&l_Lake_GitRepo_hasNoDiff___closed__1_value),((lean_object*)&l_Lake_GitRev_head___closed__0_value)}};
static const lean_object* l_Lake_GitRepo_hasNoDiff___closed__2 = (const lean_object*)&l_Lake_GitRepo_hasNoDiff___closed__2_value;
LEAN_EXPORT uint8_t l_Lake_GitRepo_hasNoDiff(lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_hasNoDiff___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_GitRepo_hasDiff(lean_object*);
LEAN_EXPORT lean_object* l_Lake_GitRepo_hasDiff___boxed(lean_object*, lean_object*);
static lean_object* _init_l_Lake_Git_filterUrl_x3f___closed__1(void){
_start:
{
lean_object* v___x_6_; lean_object* v___x_7_; 
v___x_6_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__0));
v___x_7_ = lean_string_utf8_byte_size(v___x_6_);
return v___x_7_;
}
}
static lean_object* _init_l_Lake_Git_filterUrl_x3f___closed__3(void){
_start:
{
lean_object* v___x_9_; lean_object* v___x_10_; 
v___x_9_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
v___x_10_ = lean_string_utf8_byte_size(v___x_9_);
return v___x_10_;
}
}
LEAN_EXPORT lean_object* l_Lake_Git_filterUrl_x3f(lean_object* v_url_11_){
_start:
{
lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; uint8_t v___x_30_; 
v___x_27_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
v___x_28_ = lean_string_utf8_byte_size(v_url_11_);
v___x_29_ = lean_obj_once(&l_Lake_Git_filterUrl_x3f___closed__3, &l_Lake_Git_filterUrl_x3f___closed__3_once, _init_l_Lake_Git_filterUrl_x3f___closed__3);
v___x_30_ = lean_nat_dec_le(v___x_29_, v___x_28_);
if (v___x_30_ == 0)
{
goto v___jp_12_;
}
else
{
lean_object* v___x_31_; uint8_t v___x_32_; 
v___x_31_ = lean_unsigned_to_nat(0u);
v___x_32_ = lean_string_memcmp(v_url_11_, v___x_27_, v___x_31_, v___x_31_, v___x_29_);
if (v___x_32_ == 0)
{
goto v___jp_12_;
}
else
{
lean_object* v___x_33_; 
lean_dec_ref(v_url_11_);
v___x_33_ = lean_box(0);
return v___x_33_;
}
}
v___jp_12_:
{
lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___x_15_; uint8_t v___x_16_; 
v___x_13_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__0));
v___x_14_ = lean_string_utf8_byte_size(v_url_11_);
v___x_15_ = lean_obj_once(&l_Lake_Git_filterUrl_x3f___closed__1, &l_Lake_Git_filterUrl_x3f___closed__1_once, _init_l_Lake_Git_filterUrl_x3f___closed__1);
v___x_16_ = lean_nat_dec_le(v___x_15_, v___x_14_);
if (v___x_16_ == 0)
{
lean_object* v___x_17_; 
v___x_17_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_17_, 0, v_url_11_);
return v___x_17_;
}
else
{
lean_object* v___x_18_; lean_object* v___x_19_; uint8_t v___x_20_; 
v___x_18_ = lean_unsigned_to_nat(0u);
v___x_19_ = lean_nat_sub(v___x_14_, v___x_15_);
v___x_20_ = lean_string_memcmp(v_url_11_, v___x_13_, v___x_19_, v___x_18_, v___x_15_);
lean_dec(v___x_19_);
if (v___x_20_ == 0)
{
lean_object* v___x_21_; 
v___x_21_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_21_, 0, v_url_11_);
return v___x_21_;
}
else
{
lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; 
v___x_22_ = lean_unsigned_to_nat(4u);
lean_inc_ref(v_url_11_);
v___x_23_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_23_, 0, v_url_11_);
lean_ctor_set(v___x_23_, 1, v___x_18_);
lean_ctor_set(v___x_23_, 2, v___x_14_);
v___x_24_ = l_String_Slice_Pos_prevn(v___x_23_, v___x_14_, v___x_22_);
lean_dec_ref(v___x_23_);
v___x_25_ = lean_string_utf8_extract(v_url_11_, v___x_18_, v___x_24_);
lean_dec(v___x_24_);
lean_dec_ref(v_url_11_);
v___x_26_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_26_, 0, v___x_25_);
return v___x_26_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lake_Git_isFullObjectName(lean_object* v_rev_34_){
_start:
{
lean_object* v___x_35_; lean_object* v___x_36_; uint8_t v___x_37_; 
v___x_35_ = lean_string_utf8_byte_size(v_rev_34_);
v___x_36_ = lean_unsigned_to_nat(40u);
v___x_37_ = lean_nat_dec_eq(v___x_35_, v___x_36_);
if (v___x_37_ == 0)
{
return v___x_37_;
}
else
{
uint8_t v___x_38_; 
v___x_38_ = l_Lake_isHex(v_rev_34_);
return v___x_38_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Git_isFullObjectName___boxed(lean_object* v_rev_39_){
_start:
{
uint8_t v_res_40_; lean_object* v_r_41_; 
v_res_40_ = l_Lake_Git_isFullObjectName(v_rev_39_);
lean_dec_ref(v_rev_39_);
v_r_41_ = lean_box(v_res_40_);
return v_r_41_;
}
}
LEAN_EXPORT uint8_t l_Lake_GitRev_isFullSha1(lean_object* v_rev_46_){
_start:
{
lean_object* v___x_47_; lean_object* v___x_48_; uint8_t v___x_49_; 
v___x_47_ = lean_string_utf8_byte_size(v_rev_46_);
v___x_48_ = lean_unsigned_to_nat(40u);
v___x_49_ = lean_nat_dec_eq(v___x_47_, v___x_48_);
if (v___x_49_ == 0)
{
return v___x_49_;
}
else
{
uint8_t v___x_50_; 
v___x_50_ = l_Lake_isHex(v_rev_46_);
return v___x_50_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_GitRev_isFullSha1___boxed(lean_object* v_rev_51_){
_start:
{
uint8_t v_res_52_; lean_object* v_r_53_; 
v_res_52_ = l_Lake_GitRev_isFullSha1(v_rev_51_);
lean_dec_ref(v_rev_51_);
v_r_53_ = lean_box(v_res_52_);
return v_r_53_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRev_withRemote(lean_object* v_remote_55_, lean_object* v_rev_56_){
_start:
{
lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; 
v___x_57_ = ((lean_object*)(l_Lake_GitRev_withRemote___closed__0));
v___x_58_ = lean_string_append(v_remote_55_, v___x_57_);
v___x_59_ = lean_string_append(v___x_58_, v_rev_56_);
return v___x_59_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRev_withRemote___boxed(lean_object* v_remote_60_, lean_object* v_rev_61_){
_start:
{
lean_object* v_res_62_; 
v_res_62_ = l_Lake_GitRev_withRemote(v_remote_60_, v_rev_61_);
lean_dec_ref(v_rev_61_);
return v_res_62_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_instCoeFilePath___lam__0(lean_object* v_x_63_){
_start:
{
lean_inc_ref(v_x_63_);
return v_x_63_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_instCoeFilePath___lam__0___boxed(lean_object* v_x_64_){
_start:
{
lean_object* v_res_65_; 
v_res_65_ = l_Lake_GitRepo_instCoeFilePath___lam__0(v_x_64_);
lean_dec_ref(v_x_64_);
return v_res_65_;
}
}
LEAN_EXPORT uint8_t l_Lake_GitRepo_dirExists(lean_object* v_repo_71_){
_start:
{
uint8_t v___x_73_; 
v___x_73_ = l_System_FilePath_isDir(v_repo_71_);
return v___x_73_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_dirExists___boxed(lean_object* v_repo_74_, lean_object* v_a_75_){
_start:
{
uint8_t v_res_76_; lean_object* v_r_77_; 
v_res_76_ = l_Lake_GitRepo_dirExists(v_repo_74_);
lean_dec_ref(v_repo_74_);
v_r_77_ = lean_box(v_res_76_);
return v_r_77_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_captureGit(lean_object* v_args_82_, lean_object* v_repo_83_, lean_object* v_a_84_){
_start:
{
lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; uint8_t v___x_91_; uint8_t v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; 
v___x_86_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_87_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
v___x_88_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_88_, 0, v_repo_83_);
v___x_89_ = lean_unsigned_to_nat(0u);
v___x_90_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_91_ = 1;
v___x_92_ = 0;
v___x_93_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_93_, 0, v___x_86_);
lean_ctor_set(v___x_93_, 1, v___x_87_);
lean_ctor_set(v___x_93_, 2, v_args_82_);
lean_ctor_set(v___x_93_, 3, v___x_88_);
lean_ctor_set(v___x_93_, 4, v___x_90_);
lean_ctor_set_uint8(v___x_93_, sizeof(void*)*5, v___x_91_);
lean_ctor_set_uint8(v___x_93_, sizeof(void*)*5 + 1, v___x_92_);
v___x_94_ = l_Lake_captureProc_x27(v___x_93_, v_a_84_);
if (lean_obj_tag(v___x_94_) == 0)
{
lean_object* v_a_95_; lean_object* v_a_96_; lean_object* v___x_98_; uint8_t v_isShared_99_; uint8_t v_isSharedCheck_111_; 
v_a_95_ = lean_ctor_get(v___x_94_, 0);
v_a_96_ = lean_ctor_get(v___x_94_, 1);
v_isSharedCheck_111_ = !lean_is_exclusive(v___x_94_);
if (v_isSharedCheck_111_ == 0)
{
v___x_98_ = v___x_94_;
v_isShared_99_ = v_isSharedCheck_111_;
goto v_resetjp_97_;
}
else
{
lean_inc(v_a_96_);
lean_inc(v_a_95_);
lean_dec(v___x_94_);
v___x_98_ = lean_box(0);
v_isShared_99_ = v_isSharedCheck_111_;
goto v_resetjp_97_;
}
v_resetjp_97_:
{
lean_object* v_stdout_100_; lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v_str_104_; lean_object* v_startInclusive_105_; lean_object* v_endExclusive_106_; lean_object* v___x_107_; lean_object* v___x_109_; 
v_stdout_100_ = lean_ctor_get(v_a_95_, 0);
lean_inc_ref(v_stdout_100_);
lean_dec(v_a_95_);
v___x_101_ = lean_string_utf8_byte_size(v_stdout_100_);
v___x_102_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_102_, 0, v_stdout_100_);
lean_ctor_set(v___x_102_, 1, v___x_89_);
lean_ctor_set(v___x_102_, 2, v___x_101_);
v___x_103_ = l_String_Slice_trimAscii(v___x_102_);
v_str_104_ = lean_ctor_get(v___x_103_, 0);
lean_inc_ref(v_str_104_);
v_startInclusive_105_ = lean_ctor_get(v___x_103_, 1);
lean_inc(v_startInclusive_105_);
v_endExclusive_106_ = lean_ctor_get(v___x_103_, 2);
lean_inc(v_endExclusive_106_);
lean_dec_ref(v___x_103_);
v___x_107_ = lean_string_utf8_extract(v_str_104_, v_startInclusive_105_, v_endExclusive_106_);
lean_dec(v_endExclusive_106_);
lean_dec(v_startInclusive_105_);
lean_dec_ref(v_str_104_);
if (v_isShared_99_ == 0)
{
lean_ctor_set(v___x_98_, 0, v___x_107_);
v___x_109_ = v___x_98_;
goto v_reusejp_108_;
}
else
{
lean_object* v_reuseFailAlloc_110_; 
v_reuseFailAlloc_110_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_110_, 0, v___x_107_);
lean_ctor_set(v_reuseFailAlloc_110_, 1, v_a_96_);
v___x_109_ = v_reuseFailAlloc_110_;
goto v_reusejp_108_;
}
v_reusejp_108_:
{
return v___x_109_;
}
}
}
else
{
lean_object* v_a_112_; lean_object* v_a_113_; lean_object* v___x_115_; uint8_t v_isShared_116_; uint8_t v_isSharedCheck_120_; 
v_a_112_ = lean_ctor_get(v___x_94_, 0);
v_a_113_ = lean_ctor_get(v___x_94_, 1);
v_isSharedCheck_120_ = !lean_is_exclusive(v___x_94_);
if (v_isSharedCheck_120_ == 0)
{
v___x_115_ = v___x_94_;
v_isShared_116_ = v_isSharedCheck_120_;
goto v_resetjp_114_;
}
else
{
lean_inc(v_a_113_);
lean_inc(v_a_112_);
lean_dec(v___x_94_);
v___x_115_ = lean_box(0);
v_isShared_116_ = v_isSharedCheck_120_;
goto v_resetjp_114_;
}
v_resetjp_114_:
{
lean_object* v___x_118_; 
if (v_isShared_116_ == 0)
{
v___x_118_ = v___x_115_;
goto v_reusejp_117_;
}
else
{
lean_object* v_reuseFailAlloc_119_; 
v_reuseFailAlloc_119_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_119_, 0, v_a_112_);
lean_ctor_set(v_reuseFailAlloc_119_, 1, v_a_113_);
v___x_118_ = v_reuseFailAlloc_119_;
goto v_reusejp_117_;
}
v_reusejp_117_:
{
return v___x_118_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_captureGit___boxed(lean_object* v_args_121_, lean_object* v_repo_122_, lean_object* v_a_123_, lean_object* v_a_124_){
_start:
{
lean_object* v_res_125_; 
v_res_125_ = l_Lake_GitRepo_captureGit(v_args_121_, v_repo_122_, v_a_123_);
return v_res_125_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_captureGit_x3f(lean_object* v_args_126_, lean_object* v_repo_127_){
_start:
{
lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; uint8_t v___x_133_; uint8_t v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; 
v___x_129_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_130_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
v___x_131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_131_, 0, v_repo_127_);
v___x_132_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_133_ = 1;
v___x_134_ = 0;
v___x_135_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_135_, 0, v___x_129_);
lean_ctor_set(v___x_135_, 1, v___x_130_);
lean_ctor_set(v___x_135_, 2, v_args_126_);
lean_ctor_set(v___x_135_, 3, v___x_131_);
lean_ctor_set(v___x_135_, 4, v___x_132_);
lean_ctor_set_uint8(v___x_135_, sizeof(void*)*5, v___x_133_);
lean_ctor_set_uint8(v___x_135_, sizeof(void*)*5 + 1, v___x_134_);
v___x_136_ = l_Lake_captureProc_x3f(v___x_135_);
return v___x_136_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_captureGit_x3f___boxed(lean_object* v_args_137_, lean_object* v_repo_138_, lean_object* v_a_139_){
_start:
{
lean_object* v_res_140_; 
v_res_140_ = l_Lake_GitRepo_captureGit_x3f(v_args_137_, v_repo_138_);
return v_res_140_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_execGit(lean_object* v_args_141_, lean_object* v_repo_142_, lean_object* v_a_143_){
_start:
{
lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; uint8_t v___x_149_; uint8_t v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; 
v___x_145_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_146_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
v___x_147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_147_, 0, v_repo_142_);
v___x_148_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_149_ = 1;
v___x_150_ = 0;
v___x_151_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_151_, 0, v___x_145_);
lean_ctor_set(v___x_151_, 1, v___x_146_);
lean_ctor_set(v___x_151_, 2, v_args_141_);
lean_ctor_set(v___x_151_, 3, v___x_147_);
lean_ctor_set(v___x_151_, 4, v___x_148_);
lean_ctor_set_uint8(v___x_151_, sizeof(void*)*5, v___x_149_);
lean_ctor_set_uint8(v___x_151_, sizeof(void*)*5 + 1, v___x_150_);
v___x_152_ = l_Lake_proc(v___x_151_, v___x_149_, v_a_143_);
return v___x_152_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_execGit___boxed(lean_object* v_args_153_, lean_object* v_repo_154_, lean_object* v_a_155_, lean_object* v_a_156_){
_start:
{
lean_object* v_res_157_; 
v_res_157_ = l_Lake_GitRepo_execGit(v_args_153_, v_repo_154_, v_a_155_);
return v_res_157_;
}
}
LEAN_EXPORT uint8_t l_Lake_GitRepo_testGit(lean_object* v_args_158_, lean_object* v_repo_159_){
_start:
{
lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; uint8_t v___x_165_; uint8_t v___x_166_; lean_object* v___x_167_; uint8_t v___x_168_; 
v___x_161_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_162_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
v___x_163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_163_, 0, v_repo_159_);
v___x_164_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_165_ = 1;
v___x_166_ = 0;
v___x_167_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_167_, 0, v___x_161_);
lean_ctor_set(v___x_167_, 1, v___x_162_);
lean_ctor_set(v___x_167_, 2, v_args_158_);
lean_ctor_set(v___x_167_, 3, v___x_163_);
lean_ctor_set(v___x_167_, 4, v___x_164_);
lean_ctor_set_uint8(v___x_167_, sizeof(void*)*5, v___x_165_);
lean_ctor_set_uint8(v___x_167_, sizeof(void*)*5 + 1, v___x_166_);
v___x_168_ = l_Lake_testProc(v___x_167_);
return v___x_168_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_testGit___boxed(lean_object* v_args_169_, lean_object* v_repo_170_, lean_object* v_a_171_){
_start:
{
uint8_t v_res_172_; lean_object* v_r_173_; 
v_res_172_ = l_Lake_GitRepo_testGit(v_args_169_, v_repo_170_);
v_r_173_ = lean_box(v_res_172_);
return v_r_173_;
}
}
static lean_object* _init_l_Lake_GitRepo_clone___closed__1(void){
_start:
{
lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; 
v___x_175_ = ((lean_object*)(l_Lake_GitRepo_clone___closed__0));
v___x_176_ = lean_unsigned_to_nat(3u);
v___x_177_ = lean_mk_empty_array_with_capacity(v___x_176_);
v___x_178_ = lean_array_push(v___x_177_, v___x_175_);
return v___x_178_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_clone(lean_object* v_url_179_, lean_object* v_repo_180_, lean_object* v_a_181_){
_start:
{
lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; uint8_t v___x_190_; uint8_t v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; 
v___x_183_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_184_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
v___x_185_ = lean_obj_once(&l_Lake_GitRepo_clone___closed__1, &l_Lake_GitRepo_clone___closed__1_once, _init_l_Lake_GitRepo_clone___closed__1);
v___x_186_ = lean_array_push(v___x_185_, v_url_179_);
v___x_187_ = lean_array_push(v___x_186_, v_repo_180_);
v___x_188_ = lean_box(0);
v___x_189_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_190_ = 1;
v___x_191_ = 0;
v___x_192_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_192_, 0, v___x_183_);
lean_ctor_set(v___x_192_, 1, v___x_184_);
lean_ctor_set(v___x_192_, 2, v___x_187_);
lean_ctor_set(v___x_192_, 3, v___x_188_);
lean_ctor_set(v___x_192_, 4, v___x_189_);
lean_ctor_set_uint8(v___x_192_, sizeof(void*)*5, v___x_190_);
lean_ctor_set_uint8(v___x_192_, sizeof(void*)*5 + 1, v___x_191_);
v___x_193_ = l_Lake_proc(v___x_192_, v___x_190_, v_a_181_);
return v___x_193_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_clone___boxed(lean_object* v_url_194_, lean_object* v_repo_195_, lean_object* v_a_196_, lean_object* v_a_197_){
_start:
{
lean_object* v_res_198_; 
v_res_198_ = l_Lake_GitRepo_clone(v_url_194_, v_repo_195_, v_a_196_);
return v_res_198_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_quietInit(lean_object* v_repo_207_, lean_object* v_a_208_){
_start:
{
lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; uint8_t v___x_215_; uint8_t v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; 
v___x_210_ = ((lean_object*)(l_Lake_GitRepo_quietInit___closed__2));
v___x_211_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_212_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
v___x_213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_213_, 0, v_repo_207_);
v___x_214_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_215_ = 1;
v___x_216_ = 0;
v___x_217_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_217_, 0, v___x_211_);
lean_ctor_set(v___x_217_, 1, v___x_212_);
lean_ctor_set(v___x_217_, 2, v___x_210_);
lean_ctor_set(v___x_217_, 3, v___x_213_);
lean_ctor_set(v___x_217_, 4, v___x_214_);
lean_ctor_set_uint8(v___x_217_, sizeof(void*)*5, v___x_215_);
lean_ctor_set_uint8(v___x_217_, sizeof(void*)*5 + 1, v___x_216_);
v___x_218_ = l_Lake_proc(v___x_217_, v___x_215_, v_a_208_);
return v___x_218_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_quietInit___boxed(lean_object* v_repo_219_, lean_object* v_a_220_, lean_object* v_a_221_){
_start:
{
lean_object* v_res_222_; 
v_res_222_ = l_Lake_GitRepo_quietInit(v_repo_219_, v_a_220_);
return v_res_222_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_bareInit(lean_object* v_repo_232_, lean_object* v_a_233_){
_start:
{
lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; uint8_t v___x_240_; uint8_t v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; 
v___x_235_ = ((lean_object*)(l_Lake_GitRepo_bareInit___closed__1));
v___x_236_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_237_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
v___x_238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_238_, 0, v_repo_232_);
v___x_239_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_240_ = 1;
v___x_241_ = 0;
v___x_242_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_242_, 0, v___x_236_);
lean_ctor_set(v___x_242_, 1, v___x_237_);
lean_ctor_set(v___x_242_, 2, v___x_235_);
lean_ctor_set(v___x_242_, 3, v___x_238_);
lean_ctor_set(v___x_242_, 4, v___x_239_);
lean_ctor_set_uint8(v___x_242_, sizeof(void*)*5, v___x_240_);
lean_ctor_set_uint8(v___x_242_, sizeof(void*)*5 + 1, v___x_241_);
v___x_243_ = l_Lake_proc(v___x_242_, v___x_240_, v_a_233_);
return v___x_243_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_bareInit___boxed(lean_object* v_repo_244_, lean_object* v_a_245_, lean_object* v_a_246_){
_start:
{
lean_object* v_res_247_; 
v_res_247_ = l_Lake_GitRepo_bareInit(v_repo_244_, v_a_245_);
return v_res_247_;
}
}
LEAN_EXPORT uint8_t l_Lake_GitRepo_insideWorkTree(lean_object* v_repo_256_){
_start:
{
lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; uint8_t v___x_263_; uint8_t v___x_264_; lean_object* v___x_265_; uint8_t v___x_266_; 
v___x_258_ = ((lean_object*)(l_Lake_GitRepo_insideWorkTree___closed__2));
v___x_259_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_260_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
v___x_261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_261_, 0, v_repo_256_);
v___x_262_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_263_ = 1;
v___x_264_ = 0;
v___x_265_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_265_, 0, v___x_259_);
lean_ctor_set(v___x_265_, 1, v___x_260_);
lean_ctor_set(v___x_265_, 2, v___x_258_);
lean_ctor_set(v___x_265_, 3, v___x_261_);
lean_ctor_set(v___x_265_, 4, v___x_262_);
lean_ctor_set_uint8(v___x_265_, sizeof(void*)*5, v___x_263_);
lean_ctor_set_uint8(v___x_265_, sizeof(void*)*5 + 1, v___x_264_);
v___x_266_ = l_Lake_testProc(v___x_265_);
return v___x_266_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_insideWorkTree___boxed(lean_object* v_repo_267_, lean_object* v_a_268_){
_start:
{
uint8_t v_res_269_; lean_object* v_r_270_; 
v_res_269_ = l_Lake_GitRepo_insideWorkTree(v_repo_267_);
v_r_270_ = lean_box(v_res_269_);
return v_r_270_;
}
}
static lean_object* _init_l_Lake_GitRepo_fetch___closed__3(void){
_start:
{
lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; 
v___x_274_ = ((lean_object*)(l_Lake_GitRepo_fetch___closed__0));
v___x_275_ = lean_unsigned_to_nat(4u);
v___x_276_ = lean_mk_empty_array_with_capacity(v___x_275_);
v___x_277_ = lean_array_push(v___x_276_, v___x_274_);
return v___x_277_;
}
}
static lean_object* _init_l_Lake_GitRepo_fetch___closed__4(void){
_start:
{
lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; 
v___x_278_ = ((lean_object*)(l_Lake_GitRepo_fetch___closed__1));
v___x_279_ = lean_obj_once(&l_Lake_GitRepo_fetch___closed__3, &l_Lake_GitRepo_fetch___closed__3_once, _init_l_Lake_GitRepo_fetch___closed__3);
v___x_280_ = lean_array_push(v___x_279_, v___x_278_);
return v___x_280_;
}
}
static lean_object* _init_l_Lake_GitRepo_fetch___closed__5(void){
_start:
{
lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; 
v___x_281_ = ((lean_object*)(l_Lake_GitRepo_fetch___closed__2));
v___x_282_ = lean_obj_once(&l_Lake_GitRepo_fetch___closed__4, &l_Lake_GitRepo_fetch___closed__4_once, _init_l_Lake_GitRepo_fetch___closed__4);
v___x_283_ = lean_array_push(v___x_282_, v___x_281_);
return v___x_283_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_fetch(lean_object* v_repo_284_, lean_object* v_remote_285_, lean_object* v_a_286_){
_start:
{
lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; uint8_t v___x_294_; uint8_t v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; 
v___x_288_ = lean_obj_once(&l_Lake_GitRepo_fetch___closed__5, &l_Lake_GitRepo_fetch___closed__5_once, _init_l_Lake_GitRepo_fetch___closed__5);
v___x_289_ = lean_array_push(v___x_288_, v_remote_285_);
v___x_290_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_291_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
v___x_292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_292_, 0, v_repo_284_);
v___x_293_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_294_ = 1;
v___x_295_ = 0;
v___x_296_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_296_, 0, v___x_290_);
lean_ctor_set(v___x_296_, 1, v___x_291_);
lean_ctor_set(v___x_296_, 2, v___x_289_);
lean_ctor_set(v___x_296_, 3, v___x_292_);
lean_ctor_set(v___x_296_, 4, v___x_293_);
lean_ctor_set_uint8(v___x_296_, sizeof(void*)*5, v___x_294_);
lean_ctor_set_uint8(v___x_296_, sizeof(void*)*5 + 1, v___x_295_);
v___x_297_ = l_Lake_proc(v___x_296_, v___x_294_, v_a_286_);
return v___x_297_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_fetch___boxed(lean_object* v_repo_298_, lean_object* v_remote_299_, lean_object* v_a_300_, lean_object* v_a_301_){
_start:
{
lean_object* v_res_302_; 
v_res_302_ = l_Lake_GitRepo_fetch(v_repo_298_, v_remote_299_, v_a_300_);
return v_res_302_;
}
}
static lean_object* _init_l_Lake_GitRepo_addWorktreeDetach___closed__3(void){
_start:
{
lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; 
v___x_306_ = ((lean_object*)(l_Lake_GitRepo_addWorktreeDetach___closed__0));
v___x_307_ = lean_unsigned_to_nat(5u);
v___x_308_ = lean_mk_empty_array_with_capacity(v___x_307_);
v___x_309_ = lean_array_push(v___x_308_, v___x_306_);
return v___x_309_;
}
}
static lean_object* _init_l_Lake_GitRepo_addWorktreeDetach___closed__4(void){
_start:
{
lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; 
v___x_310_ = ((lean_object*)(l_Lake_GitRepo_addWorktreeDetach___closed__1));
v___x_311_ = lean_obj_once(&l_Lake_GitRepo_addWorktreeDetach___closed__3, &l_Lake_GitRepo_addWorktreeDetach___closed__3_once, _init_l_Lake_GitRepo_addWorktreeDetach___closed__3);
v___x_312_ = lean_array_push(v___x_311_, v___x_310_);
return v___x_312_;
}
}
static lean_object* _init_l_Lake_GitRepo_addWorktreeDetach___closed__5(void){
_start:
{
lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; 
v___x_313_ = ((lean_object*)(l_Lake_GitRepo_addWorktreeDetach___closed__2));
v___x_314_ = lean_obj_once(&l_Lake_GitRepo_addWorktreeDetach___closed__4, &l_Lake_GitRepo_addWorktreeDetach___closed__4_once, _init_l_Lake_GitRepo_addWorktreeDetach___closed__4);
v___x_315_ = lean_array_push(v___x_314_, v___x_313_);
return v___x_315_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_addWorktreeDetach(lean_object* v_path_316_, lean_object* v_rev_317_, lean_object* v_repo_318_, lean_object* v_a_319_){
_start:
{
lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; uint8_t v___x_328_; uint8_t v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; 
v___x_321_ = lean_obj_once(&l_Lake_GitRepo_addWorktreeDetach___closed__5, &l_Lake_GitRepo_addWorktreeDetach___closed__5_once, _init_l_Lake_GitRepo_addWorktreeDetach___closed__5);
v___x_322_ = lean_array_push(v___x_321_, v_path_316_);
v___x_323_ = lean_array_push(v___x_322_, v_rev_317_);
v___x_324_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_325_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
v___x_326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_326_, 0, v_repo_318_);
v___x_327_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_328_ = 1;
v___x_329_ = 0;
v___x_330_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_330_, 0, v___x_324_);
lean_ctor_set(v___x_330_, 1, v___x_325_);
lean_ctor_set(v___x_330_, 2, v___x_323_);
lean_ctor_set(v___x_330_, 3, v___x_326_);
lean_ctor_set(v___x_330_, 4, v___x_327_);
lean_ctor_set_uint8(v___x_330_, sizeof(void*)*5, v___x_328_);
lean_ctor_set_uint8(v___x_330_, sizeof(void*)*5 + 1, v___x_329_);
v___x_331_ = l_Lake_proc(v___x_330_, v___x_328_, v_a_319_);
return v___x_331_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_addWorktreeDetach___boxed(lean_object* v_path_332_, lean_object* v_rev_333_, lean_object* v_repo_334_, lean_object* v_a_335_, lean_object* v_a_336_){
_start:
{
lean_object* v_res_337_; 
v_res_337_ = l_Lake_GitRepo_addWorktreeDetach(v_path_332_, v_rev_333_, v_repo_334_, v_a_335_);
return v_res_337_;
}
}
static lean_object* _init_l_Lake_GitRepo_checkoutBranch___closed__2(void){
_start:
{
lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; 
v___x_340_ = ((lean_object*)(l_Lake_GitRepo_checkoutBranch___closed__0));
v___x_341_ = lean_unsigned_to_nat(3u);
v___x_342_ = lean_mk_empty_array_with_capacity(v___x_341_);
v___x_343_ = lean_array_push(v___x_342_, v___x_340_);
return v___x_343_;
}
}
static lean_object* _init_l_Lake_GitRepo_checkoutBranch___closed__3(void){
_start:
{
lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; 
v___x_344_ = ((lean_object*)(l_Lake_GitRepo_checkoutBranch___closed__1));
v___x_345_ = lean_obj_once(&l_Lake_GitRepo_checkoutBranch___closed__2, &l_Lake_GitRepo_checkoutBranch___closed__2_once, _init_l_Lake_GitRepo_checkoutBranch___closed__2);
v___x_346_ = lean_array_push(v___x_345_, v___x_344_);
return v___x_346_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_checkoutBranch(lean_object* v_branch_347_, lean_object* v_repo_348_, lean_object* v_a_349_){
_start:
{
lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; uint8_t v___x_357_; uint8_t v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; 
v___x_351_ = lean_obj_once(&l_Lake_GitRepo_checkoutBranch___closed__3, &l_Lake_GitRepo_checkoutBranch___closed__3_once, _init_l_Lake_GitRepo_checkoutBranch___closed__3);
v___x_352_ = lean_array_push(v___x_351_, v_branch_347_);
v___x_353_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_354_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
v___x_355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_355_, 0, v_repo_348_);
v___x_356_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_357_ = 1;
v___x_358_ = 0;
v___x_359_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_359_, 0, v___x_353_);
lean_ctor_set(v___x_359_, 1, v___x_354_);
lean_ctor_set(v___x_359_, 2, v___x_352_);
lean_ctor_set(v___x_359_, 3, v___x_355_);
lean_ctor_set(v___x_359_, 4, v___x_356_);
lean_ctor_set_uint8(v___x_359_, sizeof(void*)*5, v___x_357_);
lean_ctor_set_uint8(v___x_359_, sizeof(void*)*5 + 1, v___x_358_);
v___x_360_ = l_Lake_proc(v___x_359_, v___x_357_, v_a_349_);
return v___x_360_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_checkoutBranch___boxed(lean_object* v_branch_361_, lean_object* v_repo_362_, lean_object* v_a_363_, lean_object* v_a_364_){
_start:
{
lean_object* v_res_365_; 
v_res_365_ = l_Lake_GitRepo_checkoutBranch(v_branch_361_, v_repo_362_, v_a_363_);
return v_res_365_;
}
}
static lean_object* _init_l_Lake_GitRepo_checkoutDetach___closed__1(void){
_start:
{
lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; 
v___x_367_ = ((lean_object*)(l_Lake_GitRepo_checkoutBranch___closed__0));
v___x_368_ = lean_unsigned_to_nat(4u);
v___x_369_ = lean_mk_empty_array_with_capacity(v___x_368_);
v___x_370_ = lean_array_push(v___x_369_, v___x_367_);
return v___x_370_;
}
}
static lean_object* _init_l_Lake_GitRepo_checkoutDetach___closed__2(void){
_start:
{
lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; 
v___x_371_ = ((lean_object*)(l_Lake_GitRepo_addWorktreeDetach___closed__2));
v___x_372_ = lean_obj_once(&l_Lake_GitRepo_checkoutDetach___closed__1, &l_Lake_GitRepo_checkoutDetach___closed__1_once, _init_l_Lake_GitRepo_checkoutDetach___closed__1);
v___x_373_ = lean_array_push(v___x_372_, v___x_371_);
return v___x_373_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_checkoutDetach(lean_object* v_hash_374_, lean_object* v_repo_375_, lean_object* v_a_376_){
_start:
{
lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; uint8_t v___x_386_; uint8_t v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; 
v___x_378_ = ((lean_object*)(l_Lake_GitRepo_checkoutDetach___closed__0));
v___x_379_ = lean_obj_once(&l_Lake_GitRepo_checkoutDetach___closed__2, &l_Lake_GitRepo_checkoutDetach___closed__2_once, _init_l_Lake_GitRepo_checkoutDetach___closed__2);
v___x_380_ = lean_array_push(v___x_379_, v_hash_374_);
v___x_381_ = lean_array_push(v___x_380_, v___x_378_);
v___x_382_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_383_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
v___x_384_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_384_, 0, v_repo_375_);
v___x_385_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_386_ = 1;
v___x_387_ = 0;
v___x_388_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_388_, 0, v___x_382_);
lean_ctor_set(v___x_388_, 1, v___x_383_);
lean_ctor_set(v___x_388_, 2, v___x_381_);
lean_ctor_set(v___x_388_, 3, v___x_384_);
lean_ctor_set(v___x_388_, 4, v___x_385_);
lean_ctor_set_uint8(v___x_388_, sizeof(void*)*5, v___x_386_);
lean_ctor_set_uint8(v___x_388_, sizeof(void*)*5 + 1, v___x_387_);
v___x_389_ = l_Lake_proc(v___x_388_, v___x_386_, v_a_376_);
return v___x_389_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_checkoutDetach___boxed(lean_object* v_hash_390_, lean_object* v_repo_391_, lean_object* v_a_392_, lean_object* v_a_393_){
_start:
{
lean_object* v_res_394_; 
v_res_394_ = l_Lake_GitRepo_checkoutDetach(v_hash_390_, v_repo_391_, v_a_392_);
return v_res_394_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_clean(lean_object* v_repo_403_, lean_object* v_a_404_){
_start:
{
lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; uint8_t v___x_411_; uint8_t v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; 
v___x_406_ = ((lean_object*)(l_Lake_GitRepo_clean___closed__2));
v___x_407_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_408_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
v___x_409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_409_, 0, v_repo_403_);
v___x_410_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_411_ = 1;
v___x_412_ = 0;
v___x_413_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_413_, 0, v___x_407_);
lean_ctor_set(v___x_413_, 1, v___x_408_);
lean_ctor_set(v___x_413_, 2, v___x_406_);
lean_ctor_set(v___x_413_, 3, v___x_409_);
lean_ctor_set(v___x_413_, 4, v___x_410_);
lean_ctor_set_uint8(v___x_413_, sizeof(void*)*5, v___x_411_);
lean_ctor_set_uint8(v___x_413_, sizeof(void*)*5 + 1, v___x_412_);
v___x_414_ = l_Lake_proc(v___x_413_, v___x_411_, v_a_404_);
return v___x_414_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_clean___boxed(lean_object* v_repo_415_, lean_object* v_a_416_, lean_object* v_a_417_){
_start:
{
lean_object* v_res_418_; 
v_res_418_ = l_Lake_GitRepo_clean(v_repo_415_, v_a_416_);
return v_res_418_;
}
}
static lean_object* _init_l_Lake_GitRepo_resolveRevision_x3f___closed__2(void){
_start:
{
lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; 
v___x_421_ = ((lean_object*)(l_Lake_GitRepo_insideWorkTree___closed__0));
v___x_422_ = lean_unsigned_to_nat(4u);
v___x_423_ = lean_mk_empty_array_with_capacity(v___x_422_);
v___x_424_ = lean_array_push(v___x_423_, v___x_421_);
return v___x_424_;
}
}
static lean_object* _init_l_Lake_GitRepo_resolveRevision_x3f___closed__3(void){
_start:
{
lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; 
v___x_425_ = ((lean_object*)(l_Lake_GitRepo_resolveRevision_x3f___closed__0));
v___x_426_ = lean_obj_once(&l_Lake_GitRepo_resolveRevision_x3f___closed__2, &l_Lake_GitRepo_resolveRevision_x3f___closed__2_once, _init_l_Lake_GitRepo_resolveRevision_x3f___closed__2);
v___x_427_ = lean_array_push(v___x_426_, v___x_425_);
return v___x_427_;
}
}
static lean_object* _init_l_Lake_GitRepo_resolveRevision_x3f___closed__4(void){
_start:
{
lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; 
v___x_428_ = ((lean_object*)(l_Lake_GitRepo_resolveRevision_x3f___closed__1));
v___x_429_ = lean_obj_once(&l_Lake_GitRepo_resolveRevision_x3f___closed__3, &l_Lake_GitRepo_resolveRevision_x3f___closed__3_once, _init_l_Lake_GitRepo_resolveRevision_x3f___closed__3);
v___x_430_ = lean_array_push(v___x_429_, v___x_428_);
return v___x_430_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_resolveRevision_x3f(lean_object* v_rev_431_, lean_object* v_repo_432_){
_start:
{
lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; uint8_t v___x_440_; uint8_t v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; 
v___x_434_ = lean_obj_once(&l_Lake_GitRepo_resolveRevision_x3f___closed__4, &l_Lake_GitRepo_resolveRevision_x3f___closed__4_once, _init_l_Lake_GitRepo_resolveRevision_x3f___closed__4);
v___x_435_ = lean_array_push(v___x_434_, v_rev_431_);
v___x_436_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_437_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
v___x_438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_438_, 0, v_repo_432_);
v___x_439_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_440_ = 1;
v___x_441_ = 0;
v___x_442_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_442_, 0, v___x_436_);
lean_ctor_set(v___x_442_, 1, v___x_437_);
lean_ctor_set(v___x_442_, 2, v___x_435_);
lean_ctor_set(v___x_442_, 3, v___x_438_);
lean_ctor_set(v___x_442_, 4, v___x_439_);
lean_ctor_set_uint8(v___x_442_, sizeof(void*)*5, v___x_440_);
lean_ctor_set_uint8(v___x_442_, sizeof(void*)*5 + 1, v___x_441_);
v___x_443_ = l_Lake_captureProc_x3f(v___x_442_);
return v___x_443_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_resolveRevision_x3f___boxed(lean_object* v_rev_444_, lean_object* v_repo_445_, lean_object* v_a_446_){
_start:
{
lean_object* v_res_447_; 
v_res_447_ = l_Lake_GitRepo_resolveRevision_x3f(v_rev_444_, v_repo_445_);
return v_res_447_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_findCommit_x3f(lean_object* v_rev_449_, lean_object* v_repo_450_){
_start:
{
lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; uint8_t v___x_460_; uint8_t v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; 
v___x_452_ = ((lean_object*)(l_Lake_GitRepo_findCommit_x3f___closed__0));
v___x_453_ = lean_string_append(v_rev_449_, v___x_452_);
v___x_454_ = lean_obj_once(&l_Lake_GitRepo_resolveRevision_x3f___closed__4, &l_Lake_GitRepo_resolveRevision_x3f___closed__4_once, _init_l_Lake_GitRepo_resolveRevision_x3f___closed__4);
v___x_455_ = lean_array_push(v___x_454_, v___x_453_);
v___x_456_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_457_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
v___x_458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_458_, 0, v_repo_450_);
v___x_459_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_460_ = 1;
v___x_461_ = 0;
v___x_462_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_462_, 0, v___x_456_);
lean_ctor_set(v___x_462_, 1, v___x_457_);
lean_ctor_set(v___x_462_, 2, v___x_455_);
lean_ctor_set(v___x_462_, 3, v___x_458_);
lean_ctor_set(v___x_462_, 4, v___x_459_);
lean_ctor_set_uint8(v___x_462_, sizeof(void*)*5, v___x_460_);
lean_ctor_set_uint8(v___x_462_, sizeof(void*)*5 + 1, v___x_461_);
v___x_463_ = l_Lake_captureProc_x3f(v___x_462_);
return v___x_463_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_findCommit_x3f___boxed(lean_object* v_rev_464_, lean_object* v_repo_465_, lean_object* v_a_466_){
_start:
{
lean_object* v_res_467_; 
v_res_467_ = l_Lake_GitRepo_findCommit_x3f(v_rev_464_, v_repo_465_);
return v_res_467_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_resolveRevision(lean_object* v_rev_470_, lean_object* v_repo_471_, lean_object* v_a_472_){
_start:
{
uint8_t v___x_474_; 
v___x_474_ = l_Lake_GitRev_isFullSha1(v_rev_470_);
if (v___x_474_ == 0)
{
lean_object* v___x_475_; 
lean_inc_ref(v_repo_471_);
lean_inc_ref(v_rev_470_);
v___x_475_ = l_Lake_GitRepo_resolveRevision_x3f(v_rev_470_, v_repo_471_);
if (lean_obj_tag(v___x_475_) == 1)
{
lean_object* v_val_476_; lean_object* v___x_477_; 
lean_dec_ref(v_repo_471_);
lean_dec_ref(v_rev_470_);
v_val_476_ = lean_ctor_get(v___x_475_, 0);
lean_inc(v_val_476_);
lean_dec_ref(v___x_475_);
v___x_477_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_477_, 0, v_val_476_);
lean_ctor_set(v___x_477_, 1, v_a_472_);
return v___x_477_;
}
else
{
lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; uint8_t v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; 
lean_dec(v___x_475_);
v___x_478_ = ((lean_object*)(l_Lake_GitRepo_resolveRevision___closed__0));
v___x_479_ = lean_string_append(v_repo_471_, v___x_478_);
v___x_480_ = lean_string_append(v___x_479_, v_rev_470_);
lean_dec_ref(v_rev_470_);
v___x_481_ = ((lean_object*)(l_Lake_GitRepo_resolveRevision___closed__1));
v___x_482_ = lean_string_append(v___x_480_, v___x_481_);
v___x_483_ = 3;
v___x_484_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_484_, 0, v___x_482_);
lean_ctor_set_uint8(v___x_484_, sizeof(void*)*1, v___x_483_);
v___x_485_ = lean_array_get_size(v_a_472_);
v___x_486_ = lean_array_push(v_a_472_, v___x_484_);
v___x_487_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_487_, 0, v___x_485_);
lean_ctor_set(v___x_487_, 1, v___x_486_);
return v___x_487_;
}
}
else
{
lean_object* v___x_488_; 
lean_dec_ref(v_repo_471_);
v___x_488_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_488_, 0, v_rev_470_);
lean_ctor_set(v___x_488_, 1, v_a_472_);
return v___x_488_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_resolveRevision___boxed(lean_object* v_rev_489_, lean_object* v_repo_490_, lean_object* v_a_491_, lean_object* v_a_492_){
_start:
{
lean_object* v_res_493_; 
v_res_493_ = l_Lake_GitRepo_resolveRevision(v_rev_489_, v_repo_490_, v_a_491_);
return v_res_493_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_getHeadRevision_x3f(lean_object* v_repo_494_){
_start:
{
lean_object* v___x_496_; lean_object* v___x_497_; 
v___x_496_ = ((lean_object*)(l_Lake_GitRev_head___closed__0));
v___x_497_ = l_Lake_GitRepo_resolveRevision_x3f(v___x_496_, v_repo_494_);
return v___x_497_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_getHeadRevision_x3f___boxed(lean_object* v_repo_498_, lean_object* v_a_499_){
_start:
{
lean_object* v_res_500_; 
v_res_500_ = l_Lake_GitRepo_getHeadRevision_x3f(v_repo_498_);
return v_res_500_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_getHeadRevision(lean_object* v_repo_502_, lean_object* v_a_503_){
_start:
{
lean_object* v___x_505_; lean_object* v___x_506_; 
v___x_505_ = ((lean_object*)(l_Lake_GitRev_head___closed__0));
lean_inc_ref(v_repo_502_);
v___x_506_ = l_Lake_GitRepo_resolveRevision_x3f(v___x_505_, v_repo_502_);
if (lean_obj_tag(v___x_506_) == 1)
{
lean_object* v_val_507_; lean_object* v___x_508_; 
lean_dec_ref(v_repo_502_);
v_val_507_ = lean_ctor_get(v___x_506_, 0);
lean_inc(v_val_507_);
lean_dec_ref(v___x_506_);
v___x_508_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_508_, 0, v_val_507_);
lean_ctor_set(v___x_508_, 1, v_a_503_);
return v___x_508_;
}
else
{
lean_object* v___x_509_; lean_object* v___x_510_; uint8_t v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; 
lean_dec(v___x_506_);
v___x_509_ = ((lean_object*)(l_Lake_GitRepo_getHeadRevision___closed__0));
v___x_510_ = lean_string_append(v_repo_502_, v___x_509_);
v___x_511_ = 3;
v___x_512_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_512_, 0, v___x_510_);
lean_ctor_set_uint8(v___x_512_, sizeof(void*)*1, v___x_511_);
v___x_513_ = lean_array_get_size(v_a_503_);
v___x_514_ = lean_array_push(v_a_503_, v___x_512_);
v___x_515_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_515_, 0, v___x_513_);
lean_ctor_set(v___x_515_, 1, v___x_514_);
return v___x_515_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_getHeadRevision___boxed(lean_object* v_repo_516_, lean_object* v_a_517_, lean_object* v_a_518_){
_start:
{
lean_object* v_res_519_; 
v_res_519_ = l_Lake_GitRepo_getHeadRevision(v_repo_516_, v_a_517_);
return v_res_519_;
}
}
static lean_object* _init_l_Lake_GitRepo_fetchRevision_x3f___closed__2(void){
_start:
{
lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; 
v___x_522_ = ((lean_object*)(l_Lake_GitRepo_fetch___closed__0));
v___x_523_ = lean_unsigned_to_nat(7u);
v___x_524_ = lean_mk_empty_array_with_capacity(v___x_523_);
v___x_525_ = lean_array_push(v___x_524_, v___x_522_);
return v___x_525_;
}
}
static lean_object* _init_l_Lake_GitRepo_fetchRevision_x3f___closed__3(void){
_start:
{
lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; 
v___x_526_ = ((lean_object*)(l_Lake_GitRepo_fetch___closed__1));
v___x_527_ = lean_obj_once(&l_Lake_GitRepo_fetchRevision_x3f___closed__2, &l_Lake_GitRepo_fetchRevision_x3f___closed__2_once, _init_l_Lake_GitRepo_fetchRevision_x3f___closed__2);
v___x_528_ = lean_array_push(v___x_527_, v___x_526_);
return v___x_528_;
}
}
static lean_object* _init_l_Lake_GitRepo_fetchRevision_x3f___closed__4(void){
_start:
{
lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; 
v___x_529_ = ((lean_object*)(l_Lake_GitRepo_fetch___closed__2));
v___x_530_ = lean_obj_once(&l_Lake_GitRepo_fetchRevision_x3f___closed__3, &l_Lake_GitRepo_fetchRevision_x3f___closed__3_once, _init_l_Lake_GitRepo_fetchRevision_x3f___closed__3);
v___x_531_ = lean_array_push(v___x_530_, v___x_529_);
return v___x_531_;
}
}
static lean_object* _init_l_Lake_GitRepo_fetchRevision_x3f___closed__5(void){
_start:
{
lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; 
v___x_532_ = ((lean_object*)(l_Lake_GitRepo_fetchRevision_x3f___closed__0));
v___x_533_ = lean_obj_once(&l_Lake_GitRepo_fetchRevision_x3f___closed__4, &l_Lake_GitRepo_fetchRevision_x3f___closed__4_once, _init_l_Lake_GitRepo_fetchRevision_x3f___closed__4);
v___x_534_ = lean_array_push(v___x_533_, v___x_532_);
return v___x_534_;
}
}
static lean_object* _init_l_Lake_GitRepo_fetchRevision_x3f___closed__6(void){
_start:
{
lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; 
v___x_535_ = ((lean_object*)(l_Lake_GitRepo_fetchRevision_x3f___closed__1));
v___x_536_ = lean_obj_once(&l_Lake_GitRepo_fetchRevision_x3f___closed__5, &l_Lake_GitRepo_fetchRevision_x3f___closed__5_once, _init_l_Lake_GitRepo_fetchRevision_x3f___closed__5);
v___x_537_ = lean_array_push(v___x_536_, v___x_535_);
return v___x_537_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_fetchRevision_x3f(lean_object* v_repo_539_, lean_object* v_remote_540_, lean_object* v_rev_541_, lean_object* v_a_542_){
_start:
{
lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; uint8_t v___x_551_; uint8_t v___x_552_; lean_object* v___x_553_; uint8_t v___x_554_; 
v___x_544_ = lean_obj_once(&l_Lake_GitRepo_fetchRevision_x3f___closed__6, &l_Lake_GitRepo_fetchRevision_x3f___closed__6_once, _init_l_Lake_GitRepo_fetchRevision_x3f___closed__6);
v___x_545_ = lean_array_push(v___x_544_, v_remote_540_);
v___x_546_ = lean_array_push(v___x_545_, v_rev_541_);
v___x_547_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_548_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
lean_inc_ref(v_repo_539_);
v___x_549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_549_, 0, v_repo_539_);
v___x_550_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_551_ = 1;
v___x_552_ = 0;
v___x_553_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_553_, 0, v___x_547_);
lean_ctor_set(v___x_553_, 1, v___x_548_);
lean_ctor_set(v___x_553_, 2, v___x_546_);
lean_ctor_set(v___x_553_, 3, v___x_549_);
lean_ctor_set(v___x_553_, 4, v___x_550_);
lean_ctor_set_uint8(v___x_553_, sizeof(void*)*5, v___x_551_);
lean_ctor_set_uint8(v___x_553_, sizeof(void*)*5 + 1, v___x_552_);
v___x_554_ = l_Lake_testProc(v___x_553_);
if (v___x_554_ == 0)
{
lean_object* v___x_555_; lean_object* v___x_556_; 
lean_dec_ref(v_repo_539_);
v___x_555_ = lean_box(0);
v___x_556_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_556_, 0, v___x_555_);
lean_ctor_set(v___x_556_, 1, v_a_542_);
return v___x_556_;
}
else
{
lean_object* v___x_557_; lean_object* v___x_558_; 
v___x_557_ = ((lean_object*)(l_Lake_GitRev_fetchHead___closed__0));
lean_inc_ref(v_repo_539_);
v___x_558_ = l_Lake_GitRepo_resolveRevision_x3f(v___x_557_, v_repo_539_);
if (lean_obj_tag(v___x_558_) == 1)
{
lean_object* v___x_559_; 
lean_dec_ref(v_repo_539_);
v___x_559_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_559_, 0, v___x_558_);
lean_ctor_set(v___x_559_, 1, v_a_542_);
return v___x_559_;
}
else
{
lean_object* v___x_560_; lean_object* v___x_561_; uint8_t v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; 
lean_dec(v___x_558_);
v___x_560_ = ((lean_object*)(l_Lake_GitRepo_fetchRevision_x3f___closed__7));
v___x_561_ = lean_string_append(v_repo_539_, v___x_560_);
v___x_562_ = 3;
v___x_563_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_563_, 0, v___x_561_);
lean_ctor_set_uint8(v___x_563_, sizeof(void*)*1, v___x_562_);
v___x_564_ = lean_array_get_size(v_a_542_);
v___x_565_ = lean_array_push(v_a_542_, v___x_563_);
v___x_566_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_566_, 0, v___x_564_);
lean_ctor_set(v___x_566_, 1, v___x_565_);
return v___x_566_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_fetchRevision_x3f___boxed(lean_object* v_repo_567_, lean_object* v_remote_568_, lean_object* v_rev_569_, lean_object* v_a_570_, lean_object* v_a_571_){
_start:
{
lean_object* v_res_572_; 
v_res_572_ = l_Lake_GitRepo_fetchRevision_x3f(v_repo_567_, v_remote_568_, v_rev_569_, v_a_570_);
return v_res_572_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_GitRepo_getHeadRevisions_spec__0(lean_object* v_s_575_){
_start:
{
lean_object* v___x_576_; 
v___x_576_ = ((lean_object*)(l_String_Slice_splitToSubslice___at___00Lake_GitRepo_getHeadRevisions_spec__0___closed__0));
return v___x_576_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___at___00Lake_GitRepo_getHeadRevisions_spec__0___boxed(lean_object* v_s_577_){
_start:
{
lean_object* v_res_578_; 
v_res_578_ = l_String_Slice_splitToSubslice___at___00Lake_GitRepo_getHeadRevisions_spec__0(v_s_577_);
lean_dec_ref(v_s_577_);
return v_res_578_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_GitRepo_getHeadRevisions_spec__1___redArg(lean_object* v___x_579_, lean_object* v___x_580_, lean_object* v___x_581_, lean_object* v_a_582_, lean_object* v_b_583_){
_start:
{
lean_object* v_it_585_; lean_object* v_startInclusive_586_; lean_object* v_endExclusive_587_; 
if (lean_obj_tag(v_a_582_) == 0)
{
lean_object* v_currPos_592_; lean_object* v_searcher_593_; lean_object* v___x_595_; uint8_t v_isShared_596_; uint8_t v_isSharedCheck_619_; 
v_currPos_592_ = lean_ctor_get(v_a_582_, 0);
v_searcher_593_ = lean_ctor_get(v_a_582_, 1);
v_isSharedCheck_619_ = !lean_is_exclusive(v_a_582_);
if (v_isSharedCheck_619_ == 0)
{
v___x_595_ = v_a_582_;
v_isShared_596_ = v_isSharedCheck_619_;
goto v_resetjp_594_;
}
else
{
lean_inc(v_searcher_593_);
lean_inc(v_currPos_592_);
lean_dec(v_a_582_);
v___x_595_ = lean_box(0);
v_isShared_596_ = v_isSharedCheck_619_;
goto v_resetjp_594_;
}
v_resetjp_594_:
{
lean_object* v_startInclusive_597_; lean_object* v_endExclusive_598_; lean_object* v___x_599_; uint8_t v___x_600_; 
v_startInclusive_597_ = lean_ctor_get(v___x_580_, 1);
v_endExclusive_598_ = lean_ctor_get(v___x_580_, 2);
v___x_599_ = lean_nat_sub(v_endExclusive_598_, v_startInclusive_597_);
v___x_600_ = lean_nat_dec_eq(v_searcher_593_, v___x_599_);
lean_dec(v___x_599_);
if (v___x_600_ == 0)
{
uint32_t v___x_601_; uint32_t v___x_602_; uint8_t v___x_603_; 
v___x_601_ = 10;
v___x_602_ = lean_string_utf8_get_fast(v___x_579_, v_searcher_593_);
v___x_603_ = lean_uint32_dec_eq(v___x_602_, v___x_601_);
if (v___x_603_ == 0)
{
lean_object* v___x_604_; lean_object* v___x_606_; 
v___x_604_ = lean_string_utf8_next_fast(v___x_579_, v_searcher_593_);
lean_dec(v_searcher_593_);
if (v_isShared_596_ == 0)
{
lean_ctor_set(v___x_595_, 1, v___x_604_);
v___x_606_ = v___x_595_;
goto v_reusejp_605_;
}
else
{
lean_object* v_reuseFailAlloc_608_; 
v_reuseFailAlloc_608_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_608_, 0, v_currPos_592_);
lean_ctor_set(v_reuseFailAlloc_608_, 1, v___x_604_);
v___x_606_ = v_reuseFailAlloc_608_;
goto v_reusejp_605_;
}
v_reusejp_605_:
{
v_a_582_ = v___x_606_;
goto _start;
}
}
else
{
lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v_slice_612_; lean_object* v_nextIt_614_; 
v___x_609_ = lean_string_utf8_next_fast(v___x_579_, v_searcher_593_);
v___x_610_ = lean_nat_sub(v___x_609_, v_searcher_593_);
v___x_611_ = lean_nat_add(v_searcher_593_, v___x_610_);
lean_dec(v___x_610_);
v_slice_612_ = l_String_Slice_subslice_x21(v___x_580_, v_currPos_592_, v_searcher_593_);
lean_inc(v___x_611_);
if (v_isShared_596_ == 0)
{
lean_ctor_set(v___x_595_, 1, v___x_611_);
lean_ctor_set(v___x_595_, 0, v___x_611_);
v_nextIt_614_ = v___x_595_;
goto v_reusejp_613_;
}
else
{
lean_object* v_reuseFailAlloc_617_; 
v_reuseFailAlloc_617_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_617_, 0, v___x_611_);
lean_ctor_set(v_reuseFailAlloc_617_, 1, v___x_611_);
v_nextIt_614_ = v_reuseFailAlloc_617_;
goto v_reusejp_613_;
}
v_reusejp_613_:
{
lean_object* v_startInclusive_615_; lean_object* v_endExclusive_616_; 
v_startInclusive_615_ = lean_ctor_get(v_slice_612_, 0);
lean_inc(v_startInclusive_615_);
v_endExclusive_616_ = lean_ctor_get(v_slice_612_, 1);
lean_inc(v_endExclusive_616_);
lean_dec_ref(v_slice_612_);
v_it_585_ = v_nextIt_614_;
v_startInclusive_586_ = v_startInclusive_615_;
v_endExclusive_587_ = v_endExclusive_616_;
goto v___jp_584_;
}
}
}
else
{
lean_object* v___x_618_; 
lean_del_object(v___x_595_);
lean_dec(v_searcher_593_);
v___x_618_ = lean_box(1);
lean_inc(v___x_581_);
v_it_585_ = v___x_618_;
v_startInclusive_586_ = v_currPos_592_;
v_endExclusive_587_ = v___x_581_;
goto v___jp_584_;
}
}
}
else
{
lean_dec(v___x_581_);
lean_dec_ref(v___x_579_);
return v_b_583_;
}
v___jp_584_:
{
lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; 
lean_inc_ref(v___x_579_);
v___x_588_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_588_, 0, v___x_579_);
lean_ctor_set(v___x_588_, 1, v_startInclusive_586_);
lean_ctor_set(v___x_588_, 2, v_endExclusive_587_);
v___x_589_ = l_String_Slice_toString(v___x_588_);
lean_dec_ref(v___x_588_);
v___x_590_ = lean_array_push(v_b_583_, v___x_589_);
v_a_582_ = v_it_585_;
v_b_583_ = v___x_590_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_GitRepo_getHeadRevisions_spec__1___redArg___boxed(lean_object* v___x_620_, lean_object* v___x_621_, lean_object* v___x_622_, lean_object* v_a_623_, lean_object* v_b_624_){
_start:
{
lean_object* v_res_625_; 
v_res_625_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_GitRepo_getHeadRevisions_spec__1___redArg(v___x_620_, v___x_621_, v___x_622_, v_a_623_, v_b_624_);
lean_dec_ref(v___x_621_);
return v_res_625_;
}
}
static lean_object* _init_l_Lake_GitRepo_getHeadRevisions___closed__3(void){
_start:
{
lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; 
v___x_634_ = ((lean_object*)(l_Lake_GitRepo_getHeadRevisions___closed__2));
v___x_635_ = lean_unsigned_to_nat(2u);
v___x_636_ = lean_mk_empty_array_with_capacity(v___x_635_);
v___x_637_ = lean_array_push(v___x_636_, v___x_634_);
return v___x_637_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_getHeadRevisions(lean_object* v_repo_638_, lean_object* v_n_639_, lean_object* v_a_640_){
_start:
{
lean_object* v___y_643_; lean_object* v_args_689_; lean_object* v___x_690_; uint8_t v___x_691_; 
v_args_689_ = ((lean_object*)(l_Lake_GitRepo_getHeadRevisions___closed__1));
v___x_690_ = lean_unsigned_to_nat(0u);
v___x_691_ = lean_nat_dec_eq(v_n_639_, v___x_690_);
if (v___x_691_ == 0)
{
lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; 
v___x_692_ = l_Nat_reprFast(v_n_639_);
v___x_693_ = lean_obj_once(&l_Lake_GitRepo_getHeadRevisions___closed__3, &l_Lake_GitRepo_getHeadRevisions___closed__3_once, _init_l_Lake_GitRepo_getHeadRevisions___closed__3);
v___x_694_ = lean_array_push(v___x_693_, v___x_692_);
v___x_695_ = l_Array_append___redArg(v_args_689_, v___x_694_);
lean_dec_ref(v___x_694_);
v___y_643_ = v___x_695_;
goto v___jp_642_;
}
else
{
lean_dec(v_n_639_);
v___y_643_ = v_args_689_;
goto v___jp_642_;
}
v___jp_642_:
{
lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; uint8_t v___x_649_; uint8_t v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; 
v___x_644_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_645_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
v___x_646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_646_, 0, v_repo_638_);
v___x_647_ = lean_unsigned_to_nat(0u);
v___x_648_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_649_ = 1;
v___x_650_ = 0;
v___x_651_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_651_, 0, v___x_644_);
lean_ctor_set(v___x_651_, 1, v___x_645_);
lean_ctor_set(v___x_651_, 2, v___y_643_);
lean_ctor_set(v___x_651_, 3, v___x_646_);
lean_ctor_set(v___x_651_, 4, v___x_648_);
lean_ctor_set_uint8(v___x_651_, sizeof(void*)*5, v___x_649_);
lean_ctor_set_uint8(v___x_651_, sizeof(void*)*5 + 1, v___x_650_);
v___x_652_ = l_Lake_captureProc_x27(v___x_651_, v_a_640_);
if (lean_obj_tag(v___x_652_) == 0)
{
lean_object* v_a_653_; lean_object* v_a_654_; lean_object* v___x_656_; uint8_t v_isShared_657_; uint8_t v_isSharedCheck_679_; 
v_a_653_ = lean_ctor_get(v___x_652_, 0);
v_a_654_ = lean_ctor_get(v___x_652_, 1);
v_isSharedCheck_679_ = !lean_is_exclusive(v___x_652_);
if (v_isSharedCheck_679_ == 0)
{
v___x_656_ = v___x_652_;
v_isShared_657_ = v_isSharedCheck_679_;
goto v_resetjp_655_;
}
else
{
lean_inc(v_a_654_);
lean_inc(v_a_653_);
lean_dec(v___x_652_);
v___x_656_ = lean_box(0);
v_isShared_657_ = v_isSharedCheck_679_;
goto v_resetjp_655_;
}
v_resetjp_655_:
{
lean_object* v_stdout_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v_str_662_; lean_object* v_startInclusive_663_; lean_object* v_endExclusive_664_; lean_object* v___x_666_; uint8_t v_isShared_667_; uint8_t v_isSharedCheck_678_; 
v_stdout_658_ = lean_ctor_get(v_a_653_, 0);
lean_inc_ref(v_stdout_658_);
lean_dec(v_a_653_);
v___x_659_ = lean_string_utf8_byte_size(v_stdout_658_);
v___x_660_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_660_, 0, v_stdout_658_);
lean_ctor_set(v___x_660_, 1, v___x_647_);
lean_ctor_set(v___x_660_, 2, v___x_659_);
v___x_661_ = l_String_Slice_trimAscii(v___x_660_);
v_str_662_ = lean_ctor_get(v___x_661_, 0);
v_startInclusive_663_ = lean_ctor_get(v___x_661_, 1);
v_endExclusive_664_ = lean_ctor_get(v___x_661_, 2);
v_isSharedCheck_678_ = !lean_is_exclusive(v___x_661_);
if (v_isSharedCheck_678_ == 0)
{
v___x_666_ = v___x_661_;
v_isShared_667_ = v_isSharedCheck_678_;
goto v_resetjp_665_;
}
else
{
lean_inc(v_endExclusive_664_);
lean_inc(v_startInclusive_663_);
lean_inc(v_str_662_);
lean_dec(v___x_661_);
v___x_666_ = lean_box(0);
v_isShared_667_ = v_isSharedCheck_678_;
goto v_resetjp_665_;
}
v_resetjp_665_:
{
lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_671_; 
v___x_668_ = lean_string_utf8_extract(v_str_662_, v_startInclusive_663_, v_endExclusive_664_);
lean_dec(v_endExclusive_664_);
lean_dec(v_startInclusive_663_);
lean_dec_ref(v_str_662_);
v___x_669_ = lean_string_utf8_byte_size(v___x_668_);
lean_inc_ref(v___x_668_);
if (v_isShared_667_ == 0)
{
lean_ctor_set(v___x_666_, 2, v___x_669_);
lean_ctor_set(v___x_666_, 1, v___x_647_);
lean_ctor_set(v___x_666_, 0, v___x_668_);
v___x_671_ = v___x_666_;
goto v_reusejp_670_;
}
else
{
lean_object* v_reuseFailAlloc_677_; 
v_reuseFailAlloc_677_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_677_, 0, v___x_668_);
lean_ctor_set(v_reuseFailAlloc_677_, 1, v___x_647_);
lean_ctor_set(v_reuseFailAlloc_677_, 2, v___x_669_);
v___x_671_ = v_reuseFailAlloc_677_;
goto v_reusejp_670_;
}
v_reusejp_670_:
{
lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_675_; 
v___x_672_ = l_String_Slice_splitToSubslice___at___00Lake_GitRepo_getHeadRevisions_spec__0(v___x_671_);
v___x_673_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_GitRepo_getHeadRevisions_spec__1___redArg(v___x_668_, v___x_671_, v___x_669_, v___x_672_, v___x_648_);
lean_dec_ref(v___x_671_);
if (v_isShared_657_ == 0)
{
lean_ctor_set(v___x_656_, 0, v___x_673_);
v___x_675_ = v___x_656_;
goto v_reusejp_674_;
}
else
{
lean_object* v_reuseFailAlloc_676_; 
v_reuseFailAlloc_676_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_676_, 0, v___x_673_);
lean_ctor_set(v_reuseFailAlloc_676_, 1, v_a_654_);
v___x_675_ = v_reuseFailAlloc_676_;
goto v_reusejp_674_;
}
v_reusejp_674_:
{
return v___x_675_;
}
}
}
}
}
else
{
lean_object* v_a_680_; lean_object* v_a_681_; lean_object* v___x_683_; uint8_t v_isShared_684_; uint8_t v_isSharedCheck_688_; 
v_a_680_ = lean_ctor_get(v___x_652_, 0);
v_a_681_ = lean_ctor_get(v___x_652_, 1);
v_isSharedCheck_688_ = !lean_is_exclusive(v___x_652_);
if (v_isSharedCheck_688_ == 0)
{
v___x_683_ = v___x_652_;
v_isShared_684_ = v_isSharedCheck_688_;
goto v_resetjp_682_;
}
else
{
lean_inc(v_a_681_);
lean_inc(v_a_680_);
lean_dec(v___x_652_);
v___x_683_ = lean_box(0);
v_isShared_684_ = v_isSharedCheck_688_;
goto v_resetjp_682_;
}
v_resetjp_682_:
{
lean_object* v___x_686_; 
if (v_isShared_684_ == 0)
{
v___x_686_ = v___x_683_;
goto v_reusejp_685_;
}
else
{
lean_object* v_reuseFailAlloc_687_; 
v_reuseFailAlloc_687_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_687_, 0, v_a_680_);
lean_ctor_set(v_reuseFailAlloc_687_, 1, v_a_681_);
v___x_686_ = v_reuseFailAlloc_687_;
goto v_reusejp_685_;
}
v_reusejp_685_:
{
return v___x_686_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_getHeadRevisions___boxed(lean_object* v_repo_696_, lean_object* v_n_697_, lean_object* v_a_698_, lean_object* v_a_699_){
_start:
{
lean_object* v_res_700_; 
v_res_700_ = l_Lake_GitRepo_getHeadRevisions(v_repo_696_, v_n_697_, v_a_698_);
return v_res_700_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_GitRepo_getHeadRevisions_spec__1(lean_object* v___x_701_, lean_object* v___x_702_, lean_object* v___x_703_, lean_object* v_inst_704_, lean_object* v_R_705_, lean_object* v_a_706_, lean_object* v_b_707_){
_start:
{
lean_object* v___x_708_; 
v___x_708_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_GitRepo_getHeadRevisions_spec__1___redArg(v___x_701_, v___x_702_, v___x_703_, v_a_706_, v_b_707_);
return v___x_708_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_GitRepo_getHeadRevisions_spec__1___boxed(lean_object* v___x_709_, lean_object* v___x_710_, lean_object* v___x_711_, lean_object* v_inst_712_, lean_object* v_R_713_, lean_object* v_a_714_, lean_object* v_b_715_){
_start:
{
lean_object* v_res_716_; 
v_res_716_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_GitRepo_getHeadRevisions_spec__1(v___x_709_, v___x_710_, v___x_711_, v_inst_712_, v_R_713_, v_a_714_, v_b_715_);
lean_dec_ref(v___x_710_);
return v_res_716_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_resolveRemoteRevision(lean_object* v_rev_717_, lean_object* v_remote_718_, lean_object* v_repo_719_, lean_object* v_a_720_){
_start:
{
lean_object* v_rev_723_; lean_object* v___y_724_; uint8_t v___x_726_; 
v___x_726_ = l_Lake_GitRev_isFullSha1(v_rev_717_);
if (v___x_726_ == 0)
{
lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; 
v___x_727_ = ((lean_object*)(l_Lake_GitRev_withRemote___closed__0));
v___x_728_ = lean_string_append(v_remote_718_, v___x_727_);
v___x_729_ = lean_string_append(v___x_728_, v_rev_717_);
lean_inc_ref(v_repo_719_);
v___x_730_ = l_Lake_GitRepo_resolveRevision_x3f(v___x_729_, v_repo_719_);
if (lean_obj_tag(v___x_730_) == 1)
{
lean_object* v_val_731_; 
lean_dec_ref(v_repo_719_);
lean_dec_ref(v_rev_717_);
v_val_731_ = lean_ctor_get(v___x_730_, 0);
lean_inc(v_val_731_);
lean_dec_ref(v___x_730_);
v_rev_723_ = v_val_731_;
v___y_724_ = v_a_720_;
goto v___jp_722_;
}
else
{
lean_object* v___x_732_; 
lean_dec(v___x_730_);
lean_inc_ref(v_repo_719_);
lean_inc_ref(v_rev_717_);
v___x_732_ = l_Lake_GitRepo_resolveRevision_x3f(v_rev_717_, v_repo_719_);
if (lean_obj_tag(v___x_732_) == 1)
{
lean_object* v_val_733_; 
lean_dec_ref(v_repo_719_);
lean_dec_ref(v_rev_717_);
v_val_733_ = lean_ctor_get(v___x_732_, 0);
lean_inc(v_val_733_);
lean_dec_ref(v___x_732_);
v_rev_723_ = v_val_733_;
v___y_724_ = v_a_720_;
goto v___jp_722_;
}
else
{
lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; uint8_t v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; 
lean_dec(v___x_732_);
v___x_734_ = ((lean_object*)(l_Lake_GitRepo_resolveRevision___closed__0));
v___x_735_ = lean_string_append(v_repo_719_, v___x_734_);
v___x_736_ = lean_string_append(v___x_735_, v_rev_717_);
lean_dec_ref(v_rev_717_);
v___x_737_ = ((lean_object*)(l_Lake_GitRepo_resolveRevision___closed__1));
v___x_738_ = lean_string_append(v___x_736_, v___x_737_);
v___x_739_ = 3;
v___x_740_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_740_, 0, v___x_738_);
lean_ctor_set_uint8(v___x_740_, sizeof(void*)*1, v___x_739_);
v___x_741_ = lean_array_get_size(v_a_720_);
v___x_742_ = lean_array_push(v_a_720_, v___x_740_);
v___x_743_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_743_, 0, v___x_741_);
lean_ctor_set(v___x_743_, 1, v___x_742_);
return v___x_743_;
}
}
}
else
{
lean_object* v___x_744_; 
lean_dec_ref(v_repo_719_);
lean_dec_ref(v_remote_718_);
v___x_744_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_744_, 0, v_rev_717_);
lean_ctor_set(v___x_744_, 1, v_a_720_);
return v___x_744_;
}
v___jp_722_:
{
lean_object* v___x_725_; 
v___x_725_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_725_, 0, v_rev_723_);
lean_ctor_set(v___x_725_, 1, v___y_724_);
return v___x_725_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_resolveRemoteRevision___boxed(lean_object* v_rev_745_, lean_object* v_remote_746_, lean_object* v_repo_747_, lean_object* v_a_748_, lean_object* v_a_749_){
_start:
{
lean_object* v_res_750_; 
v_res_750_ = l_Lake_GitRepo_resolveRemoteRevision(v_rev_745_, v_remote_746_, v_repo_747_, v_a_748_);
return v_res_750_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_findRemoteRevision(lean_object* v_repo_751_, lean_object* v_rev_x3f_752_, lean_object* v_remote_753_, lean_object* v_a_754_){
_start:
{
lean_object* v___x_756_; 
lean_inc_ref(v_remote_753_);
lean_inc_ref(v_repo_751_);
v___x_756_ = l_Lake_GitRepo_fetch(v_repo_751_, v_remote_753_, v_a_754_);
if (lean_obj_tag(v___x_756_) == 0)
{
if (lean_obj_tag(v_rev_x3f_752_) == 0)
{
lean_object* v_a_757_; lean_object* v___x_758_; lean_object* v___x_759_; 
v_a_757_ = lean_ctor_get(v___x_756_, 1);
lean_inc(v_a_757_);
lean_dec_ref(v___x_756_);
v___x_758_ = ((lean_object*)(l_Lake_Git_upstreamBranch___closed__0));
v___x_759_ = l_Lake_GitRepo_resolveRemoteRevision(v___x_758_, v_remote_753_, v_repo_751_, v_a_757_);
return v___x_759_;
}
else
{
lean_object* v_a_760_; lean_object* v_val_761_; lean_object* v___x_762_; 
v_a_760_ = lean_ctor_get(v___x_756_, 1);
lean_inc(v_a_760_);
lean_dec_ref(v___x_756_);
v_val_761_ = lean_ctor_get(v_rev_x3f_752_, 0);
lean_inc(v_val_761_);
lean_dec_ref(v_rev_x3f_752_);
v___x_762_ = l_Lake_GitRepo_resolveRemoteRevision(v_val_761_, v_remote_753_, v_repo_751_, v_a_760_);
return v___x_762_;
}
}
else
{
lean_object* v_a_763_; lean_object* v_a_764_; lean_object* v___x_766_; uint8_t v_isShared_767_; uint8_t v_isSharedCheck_771_; 
lean_dec_ref(v_remote_753_);
lean_dec(v_rev_x3f_752_);
lean_dec_ref(v_repo_751_);
v_a_763_ = lean_ctor_get(v___x_756_, 0);
v_a_764_ = lean_ctor_get(v___x_756_, 1);
v_isSharedCheck_771_ = !lean_is_exclusive(v___x_756_);
if (v_isSharedCheck_771_ == 0)
{
v___x_766_ = v___x_756_;
v_isShared_767_ = v_isSharedCheck_771_;
goto v_resetjp_765_;
}
else
{
lean_inc(v_a_764_);
lean_inc(v_a_763_);
lean_dec(v___x_756_);
v___x_766_ = lean_box(0);
v_isShared_767_ = v_isSharedCheck_771_;
goto v_resetjp_765_;
}
v_resetjp_765_:
{
lean_object* v___x_769_; 
if (v_isShared_767_ == 0)
{
v___x_769_ = v___x_766_;
goto v_reusejp_768_;
}
else
{
lean_object* v_reuseFailAlloc_770_; 
v_reuseFailAlloc_770_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_770_, 0, v_a_763_);
lean_ctor_set(v_reuseFailAlloc_770_, 1, v_a_764_);
v___x_769_ = v_reuseFailAlloc_770_;
goto v_reusejp_768_;
}
v_reusejp_768_:
{
return v___x_769_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_findRemoteRevision___boxed(lean_object* v_repo_772_, lean_object* v_rev_x3f_773_, lean_object* v_remote_774_, lean_object* v_a_775_, lean_object* v_a_776_){
_start:
{
lean_object* v_res_777_; 
v_res_777_ = l_Lake_GitRepo_findRemoteRevision(v_repo_772_, v_rev_x3f_773_, v_remote_774_, v_a_775_);
return v_res_777_;
}
}
static lean_object* _init_l_Lake_GitRepo_branchExists___closed__2(void){
_start:
{
lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; 
v___x_780_ = ((lean_object*)(l_Lake_GitRepo_branchExists___closed__0));
v___x_781_ = lean_unsigned_to_nat(3u);
v___x_782_ = lean_mk_empty_array_with_capacity(v___x_781_);
v___x_783_ = lean_array_push(v___x_782_, v___x_780_);
return v___x_783_;
}
}
static lean_object* _init_l_Lake_GitRepo_branchExists___closed__3(void){
_start:
{
lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; 
v___x_784_ = ((lean_object*)(l_Lake_GitRepo_resolveRevision_x3f___closed__0));
v___x_785_ = lean_obj_once(&l_Lake_GitRepo_branchExists___closed__2, &l_Lake_GitRepo_branchExists___closed__2_once, _init_l_Lake_GitRepo_branchExists___closed__2);
v___x_786_ = lean_array_push(v___x_785_, v___x_784_);
return v___x_786_;
}
}
LEAN_EXPORT uint8_t l_Lake_GitRepo_branchExists(lean_object* v_rev_787_, lean_object* v_repo_788_){
_start:
{
lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; uint8_t v___x_798_; uint8_t v___x_799_; lean_object* v___x_800_; uint8_t v___x_801_; 
v___x_790_ = ((lean_object*)(l_Lake_GitRepo_branchExists___closed__1));
v___x_791_ = lean_string_append(v___x_790_, v_rev_787_);
v___x_792_ = lean_obj_once(&l_Lake_GitRepo_branchExists___closed__3, &l_Lake_GitRepo_branchExists___closed__3_once, _init_l_Lake_GitRepo_branchExists___closed__3);
v___x_793_ = lean_array_push(v___x_792_, v___x_791_);
v___x_794_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_795_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
v___x_796_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_796_, 0, v_repo_788_);
v___x_797_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_798_ = 1;
v___x_799_ = 0;
v___x_800_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_800_, 0, v___x_794_);
lean_ctor_set(v___x_800_, 1, v___x_795_);
lean_ctor_set(v___x_800_, 2, v___x_793_);
lean_ctor_set(v___x_800_, 3, v___x_796_);
lean_ctor_set(v___x_800_, 4, v___x_797_);
lean_ctor_set_uint8(v___x_800_, sizeof(void*)*5, v___x_798_);
lean_ctor_set_uint8(v___x_800_, sizeof(void*)*5 + 1, v___x_799_);
v___x_801_ = l_Lake_testProc(v___x_800_);
return v___x_801_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_branchExists___boxed(lean_object* v_rev_802_, lean_object* v_repo_803_, lean_object* v_a_804_){
_start:
{
uint8_t v_res_805_; lean_object* v_r_806_; 
v_res_805_ = l_Lake_GitRepo_branchExists(v_rev_802_, v_repo_803_);
lean_dec_ref(v_rev_802_);
v_r_806_ = lean_box(v_res_805_);
return v_r_806_;
}
}
static lean_object* _init_l_Lake_GitRepo_revisionExists___closed__0(void){
_start:
{
lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; 
v___x_807_ = ((lean_object*)(l_Lake_GitRepo_insideWorkTree___closed__0));
v___x_808_ = lean_unsigned_to_nat(3u);
v___x_809_ = lean_mk_empty_array_with_capacity(v___x_808_);
v___x_810_ = lean_array_push(v___x_809_, v___x_807_);
return v___x_810_;
}
}
static lean_object* _init_l_Lake_GitRepo_revisionExists___closed__1(void){
_start:
{
lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; 
v___x_811_ = ((lean_object*)(l_Lake_GitRepo_resolveRevision_x3f___closed__0));
v___x_812_ = lean_obj_once(&l_Lake_GitRepo_revisionExists___closed__0, &l_Lake_GitRepo_revisionExists___closed__0_once, _init_l_Lake_GitRepo_revisionExists___closed__0);
v___x_813_ = lean_array_push(v___x_812_, v___x_811_);
return v___x_813_;
}
}
LEAN_EXPORT uint8_t l_Lake_GitRepo_revisionExists(lean_object* v_rev_814_, lean_object* v_repo_815_){
_start:
{
lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; uint8_t v___x_825_; uint8_t v___x_826_; lean_object* v___x_827_; uint8_t v___x_828_; 
v___x_817_ = ((lean_object*)(l_Lake_GitRepo_findCommit_x3f___closed__0));
v___x_818_ = lean_string_append(v_rev_814_, v___x_817_);
v___x_819_ = lean_obj_once(&l_Lake_GitRepo_revisionExists___closed__1, &l_Lake_GitRepo_revisionExists___closed__1_once, _init_l_Lake_GitRepo_revisionExists___closed__1);
v___x_820_ = lean_array_push(v___x_819_, v___x_818_);
v___x_821_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_822_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
v___x_823_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_823_, 0, v_repo_815_);
v___x_824_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_825_ = 1;
v___x_826_ = 0;
v___x_827_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_827_, 0, v___x_821_);
lean_ctor_set(v___x_827_, 1, v___x_822_);
lean_ctor_set(v___x_827_, 2, v___x_820_);
lean_ctor_set(v___x_827_, 3, v___x_823_);
lean_ctor_set(v___x_827_, 4, v___x_824_);
lean_ctor_set_uint8(v___x_827_, sizeof(void*)*5, v___x_825_);
lean_ctor_set_uint8(v___x_827_, sizeof(void*)*5 + 1, v___x_826_);
v___x_828_ = l_Lake_testProc(v___x_827_);
return v___x_828_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_revisionExists___boxed(lean_object* v_rev_829_, lean_object* v_repo_830_, lean_object* v_a_831_){
_start:
{
uint8_t v_res_832_; lean_object* v_r_833_; 
v_res_832_ = l_Lake_GitRepo_revisionExists(v_rev_829_, v_repo_830_);
v_r_833_ = lean_box(v_res_832_);
return v_r_833_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_getTags(lean_object* v_repo_839_){
_start:
{
lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; uint8_t v___x_847_; uint8_t v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; 
v___x_841_ = ((lean_object*)(l_Lake_GitRepo_getTags___closed__1));
v___x_842_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_843_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
v___x_844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_844_, 0, v_repo_839_);
v___x_845_ = lean_unsigned_to_nat(0u);
v___x_846_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_847_ = 1;
v___x_848_ = 0;
v___x_849_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_849_, 0, v___x_842_);
lean_ctor_set(v___x_849_, 1, v___x_843_);
lean_ctor_set(v___x_849_, 2, v___x_841_);
lean_ctor_set(v___x_849_, 3, v___x_844_);
lean_ctor_set(v___x_849_, 4, v___x_846_);
lean_ctor_set_uint8(v___x_849_, sizeof(void*)*5, v___x_847_);
lean_ctor_set_uint8(v___x_849_, sizeof(void*)*5 + 1, v___x_848_);
v___x_850_ = l_Lake_captureProc_x3f(v___x_849_);
if (lean_obj_tag(v___x_850_) == 1)
{
lean_object* v_val_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; 
v_val_851_ = lean_ctor_get(v___x_850_, 0);
lean_inc_n(v_val_851_, 2);
lean_dec_ref(v___x_850_);
v___x_852_ = lean_string_utf8_byte_size(v_val_851_);
v___x_853_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_853_, 0, v_val_851_);
lean_ctor_set(v___x_853_, 1, v___x_845_);
lean_ctor_set(v___x_853_, 2, v___x_852_);
v___x_854_ = l_String_Slice_splitToSubslice___at___00Lake_GitRepo_getHeadRevisions_spec__0(v___x_853_);
v___x_855_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_GitRepo_getHeadRevisions_spec__1___redArg(v_val_851_, v___x_853_, v___x_852_, v___x_854_, v___x_846_);
lean_dec_ref(v___x_853_);
v___x_856_ = lean_array_to_list(v___x_855_);
return v___x_856_;
}
else
{
lean_object* v___x_857_; 
lean_dec(v___x_850_);
v___x_857_ = lean_box(0);
return v___x_857_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_getTags___boxed(lean_object* v_repo_858_, lean_object* v_a_859_){
_start:
{
lean_object* v_res_860_; 
v_res_860_ = l_Lake_GitRepo_getTags(v_repo_858_);
return v_res_860_;
}
}
static lean_object* _init_l_Lake_GitRepo_findTag_x3f___closed__2(void){
_start:
{
lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; 
v___x_863_ = ((lean_object*)(l_Lake_GitRepo_findTag_x3f___closed__0));
v___x_864_ = lean_unsigned_to_nat(4u);
v___x_865_ = lean_mk_empty_array_with_capacity(v___x_864_);
v___x_866_ = lean_array_push(v___x_865_, v___x_863_);
return v___x_866_;
}
}
static lean_object* _init_l_Lake_GitRepo_findTag_x3f___closed__3(void){
_start:
{
lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; 
v___x_867_ = ((lean_object*)(l_Lake_GitRepo_fetch___closed__1));
v___x_868_ = lean_obj_once(&l_Lake_GitRepo_findTag_x3f___closed__2, &l_Lake_GitRepo_findTag_x3f___closed__2_once, _init_l_Lake_GitRepo_findTag_x3f___closed__2);
v___x_869_ = lean_array_push(v___x_868_, v___x_867_);
return v___x_869_;
}
}
static lean_object* _init_l_Lake_GitRepo_findTag_x3f___closed__4(void){
_start:
{
lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; 
v___x_870_ = ((lean_object*)(l_Lake_GitRepo_findTag_x3f___closed__1));
v___x_871_ = lean_obj_once(&l_Lake_GitRepo_findTag_x3f___closed__3, &l_Lake_GitRepo_findTag_x3f___closed__3_once, _init_l_Lake_GitRepo_findTag_x3f___closed__3);
v___x_872_ = lean_array_push(v___x_871_, v___x_870_);
return v___x_872_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_findTag_x3f(lean_object* v_rev_873_, lean_object* v_repo_874_){
_start:
{
lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; uint8_t v___x_882_; uint8_t v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; 
v___x_876_ = lean_obj_once(&l_Lake_GitRepo_findTag_x3f___closed__4, &l_Lake_GitRepo_findTag_x3f___closed__4_once, _init_l_Lake_GitRepo_findTag_x3f___closed__4);
v___x_877_ = lean_array_push(v___x_876_, v_rev_873_);
v___x_878_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_879_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
v___x_880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_880_, 0, v_repo_874_);
v___x_881_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_882_ = 1;
v___x_883_ = 0;
v___x_884_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_884_, 0, v___x_878_);
lean_ctor_set(v___x_884_, 1, v___x_879_);
lean_ctor_set(v___x_884_, 2, v___x_877_);
lean_ctor_set(v___x_884_, 3, v___x_880_);
lean_ctor_set(v___x_884_, 4, v___x_881_);
lean_ctor_set_uint8(v___x_884_, sizeof(void*)*5, v___x_882_);
lean_ctor_set_uint8(v___x_884_, sizeof(void*)*5 + 1, v___x_883_);
v___x_885_ = l_Lake_captureProc_x3f(v___x_884_);
return v___x_885_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_findTag_x3f___boxed(lean_object* v_rev_886_, lean_object* v_repo_887_, lean_object* v_a_888_){
_start:
{
lean_object* v_res_889_; 
v_res_889_ = l_Lake_GitRepo_findTag_x3f(v_rev_886_, v_repo_887_);
return v_res_889_;
}
}
static lean_object* _init_l_Lake_GitRepo_getRemoteUrl_x3f___closed__2(void){
_start:
{
lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; 
v___x_892_ = ((lean_object*)(l_Lake_GitRepo_getRemoteUrl_x3f___closed__0));
v___x_893_ = lean_unsigned_to_nat(3u);
v___x_894_ = lean_mk_empty_array_with_capacity(v___x_893_);
v___x_895_ = lean_array_push(v___x_894_, v___x_892_);
return v___x_895_;
}
}
static lean_object* _init_l_Lake_GitRepo_getRemoteUrl_x3f___closed__3(void){
_start:
{
lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; 
v___x_896_ = ((lean_object*)(l_Lake_GitRepo_getRemoteUrl_x3f___closed__1));
v___x_897_ = lean_obj_once(&l_Lake_GitRepo_getRemoteUrl_x3f___closed__2, &l_Lake_GitRepo_getRemoteUrl_x3f___closed__2_once, _init_l_Lake_GitRepo_getRemoteUrl_x3f___closed__2);
v___x_898_ = lean_array_push(v___x_897_, v___x_896_);
return v___x_898_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_getRemoteUrl_x3f(lean_object* v_remote_899_, lean_object* v_repo_900_){
_start:
{
lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; uint8_t v___x_908_; uint8_t v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; 
v___x_902_ = lean_obj_once(&l_Lake_GitRepo_getRemoteUrl_x3f___closed__3, &l_Lake_GitRepo_getRemoteUrl_x3f___closed__3_once, _init_l_Lake_GitRepo_getRemoteUrl_x3f___closed__3);
v___x_903_ = lean_array_push(v___x_902_, v_remote_899_);
v___x_904_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_905_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
v___x_906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_906_, 0, v_repo_900_);
v___x_907_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_908_ = 1;
v___x_909_ = 0;
v___x_910_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_910_, 0, v___x_904_);
lean_ctor_set(v___x_910_, 1, v___x_905_);
lean_ctor_set(v___x_910_, 2, v___x_903_);
lean_ctor_set(v___x_910_, 3, v___x_906_);
lean_ctor_set(v___x_910_, 4, v___x_907_);
lean_ctor_set_uint8(v___x_910_, sizeof(void*)*5, v___x_908_);
lean_ctor_set_uint8(v___x_910_, sizeof(void*)*5 + 1, v___x_909_);
v___x_911_ = l_Lake_captureProc_x3f(v___x_910_);
return v___x_911_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_getRemoteUrl_x3f___boxed(lean_object* v_remote_912_, lean_object* v_repo_913_, lean_object* v_a_914_){
_start:
{
lean_object* v_res_915_; 
v_res_915_ = l_Lake_GitRepo_getRemoteUrl_x3f(v_remote_912_, v_repo_913_);
return v_res_915_;
}
}
static lean_object* _init_l_Lake_GitRepo_addRemote___closed__0(void){
_start:
{
lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; 
v___x_916_ = ((lean_object*)(l_Lake_GitRepo_getRemoteUrl_x3f___closed__0));
v___x_917_ = lean_unsigned_to_nat(4u);
v___x_918_ = lean_mk_empty_array_with_capacity(v___x_917_);
v___x_919_ = lean_array_push(v___x_918_, v___x_916_);
return v___x_919_;
}
}
static lean_object* _init_l_Lake_GitRepo_addRemote___closed__1(void){
_start:
{
lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; 
v___x_920_ = ((lean_object*)(l_Lake_GitRepo_addWorktreeDetach___closed__1));
v___x_921_ = lean_obj_once(&l_Lake_GitRepo_addRemote___closed__0, &l_Lake_GitRepo_addRemote___closed__0_once, _init_l_Lake_GitRepo_addRemote___closed__0);
v___x_922_ = lean_array_push(v___x_921_, v___x_920_);
return v___x_922_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_addRemote(lean_object* v_remote_923_, lean_object* v_url_924_, lean_object* v_repo_925_, lean_object* v_a_926_){
_start:
{
lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; uint8_t v___x_935_; uint8_t v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; 
v___x_928_ = lean_obj_once(&l_Lake_GitRepo_addRemote___closed__1, &l_Lake_GitRepo_addRemote___closed__1_once, _init_l_Lake_GitRepo_addRemote___closed__1);
v___x_929_ = lean_array_push(v___x_928_, v_remote_923_);
v___x_930_ = lean_array_push(v___x_929_, v_url_924_);
v___x_931_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_932_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
v___x_933_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_933_, 0, v_repo_925_);
v___x_934_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_935_ = 1;
v___x_936_ = 0;
v___x_937_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_937_, 0, v___x_931_);
lean_ctor_set(v___x_937_, 1, v___x_932_);
lean_ctor_set(v___x_937_, 2, v___x_930_);
lean_ctor_set(v___x_937_, 3, v___x_933_);
lean_ctor_set(v___x_937_, 4, v___x_934_);
lean_ctor_set_uint8(v___x_937_, sizeof(void*)*5, v___x_935_);
lean_ctor_set_uint8(v___x_937_, sizeof(void*)*5 + 1, v___x_936_);
v___x_938_ = l_Lake_proc(v___x_937_, v___x_935_, v_a_926_);
return v___x_938_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_addRemote___boxed(lean_object* v_remote_939_, lean_object* v_url_940_, lean_object* v_repo_941_, lean_object* v_a_942_, lean_object* v_a_943_){
_start:
{
lean_object* v_res_944_; 
v_res_944_ = l_Lake_GitRepo_addRemote(v_remote_939_, v_url_940_, v_repo_941_, v_a_942_);
return v_res_944_;
}
}
static lean_object* _init_l_Lake_GitRepo_setRemoteUrl___closed__1(void){
_start:
{
lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; 
v___x_946_ = ((lean_object*)(l_Lake_GitRepo_setRemoteUrl___closed__0));
v___x_947_ = lean_obj_once(&l_Lake_GitRepo_addRemote___closed__0, &l_Lake_GitRepo_addRemote___closed__0_once, _init_l_Lake_GitRepo_addRemote___closed__0);
v___x_948_ = lean_array_push(v___x_947_, v___x_946_);
return v___x_948_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_setRemoteUrl(lean_object* v_remote_949_, lean_object* v_url_950_, lean_object* v_repo_951_, lean_object* v_a_952_){
_start:
{
lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; uint8_t v___x_961_; uint8_t v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; 
v___x_954_ = lean_obj_once(&l_Lake_GitRepo_setRemoteUrl___closed__1, &l_Lake_GitRepo_setRemoteUrl___closed__1_once, _init_l_Lake_GitRepo_setRemoteUrl___closed__1);
v___x_955_ = lean_array_push(v___x_954_, v_remote_949_);
v___x_956_ = lean_array_push(v___x_955_, v_url_950_);
v___x_957_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_958_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
v___x_959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_959_, 0, v_repo_951_);
v___x_960_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_961_ = 1;
v___x_962_ = 0;
v___x_963_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_963_, 0, v___x_957_);
lean_ctor_set(v___x_963_, 1, v___x_958_);
lean_ctor_set(v___x_963_, 2, v___x_956_);
lean_ctor_set(v___x_963_, 3, v___x_959_);
lean_ctor_set(v___x_963_, 4, v___x_960_);
lean_ctor_set_uint8(v___x_963_, sizeof(void*)*5, v___x_961_);
lean_ctor_set_uint8(v___x_963_, sizeof(void*)*5 + 1, v___x_962_);
v___x_964_ = l_Lake_proc(v___x_963_, v___x_961_, v_a_952_);
return v___x_964_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_setRemoteUrl___boxed(lean_object* v_remote_965_, lean_object* v_url_966_, lean_object* v_repo_967_, lean_object* v_a_968_, lean_object* v_a_969_){
_start:
{
lean_object* v_res_970_; 
v_res_970_ = l_Lake_GitRepo_setRemoteUrl(v_remote_965_, v_url_966_, v_repo_967_, v_a_968_);
return v_res_970_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_getFilteredRemoteUrl_x3f(lean_object* v_remote_971_, lean_object* v_repo_972_){
_start:
{
lean_object* v___x_974_; 
v___x_974_ = l_Lake_GitRepo_getRemoteUrl_x3f(v_remote_971_, v_repo_972_);
if (lean_obj_tag(v___x_974_) == 0)
{
return v___x_974_;
}
else
{
lean_object* v_val_975_; lean_object* v___x_976_; 
v_val_975_ = lean_ctor_get(v___x_974_, 0);
lean_inc(v_val_975_);
lean_dec_ref(v___x_974_);
v___x_976_ = l_Lake_Git_filterUrl_x3f(v_val_975_);
return v___x_976_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_getFilteredRemoteUrl_x3f___boxed(lean_object* v_remote_977_, lean_object* v_repo_978_, lean_object* v_a_979_){
_start:
{
lean_object* v_res_980_; 
v_res_980_ = l_Lake_GitRepo_getFilteredRemoteUrl_x3f(v_remote_977_, v_repo_978_);
return v_res_980_;
}
}
LEAN_EXPORT uint8_t l_Lake_GitRepo_hasNoDiff(lean_object* v_repo_991_){
_start:
{
lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; uint8_t v___x_998_; uint8_t v___x_999_; lean_object* v___x_1000_; uint8_t v___x_1001_; 
v___x_993_ = ((lean_object*)(l_Lake_GitRepo_hasNoDiff___closed__2));
v___x_994_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__0));
v___x_995_ = ((lean_object*)(l_Lake_Git_filterUrl_x3f___closed__2));
v___x_996_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_996_, 0, v_repo_991_);
v___x_997_ = ((lean_object*)(l_Lake_GitRepo_captureGit___closed__1));
v___x_998_ = 1;
v___x_999_ = 0;
v___x_1000_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v___x_1000_, 0, v___x_994_);
lean_ctor_set(v___x_1000_, 1, v___x_995_);
lean_ctor_set(v___x_1000_, 2, v___x_993_);
lean_ctor_set(v___x_1000_, 3, v___x_996_);
lean_ctor_set(v___x_1000_, 4, v___x_997_);
lean_ctor_set_uint8(v___x_1000_, sizeof(void*)*5, v___x_998_);
lean_ctor_set_uint8(v___x_1000_, sizeof(void*)*5 + 1, v___x_999_);
v___x_1001_ = l_Lake_testProc(v___x_1000_);
return v___x_1001_;
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_hasNoDiff___boxed(lean_object* v_repo_1002_, lean_object* v_a_1003_){
_start:
{
uint8_t v_res_1004_; lean_object* v_r_1005_; 
v_res_1004_ = l_Lake_GitRepo_hasNoDiff(v_repo_1002_);
v_r_1005_ = lean_box(v_res_1004_);
return v_r_1005_;
}
}
LEAN_EXPORT uint8_t l_Lake_GitRepo_hasDiff(lean_object* v_repo_1006_){
_start:
{
uint8_t v___x_1008_; 
v___x_1008_ = l_Lake_GitRepo_hasNoDiff(v_repo_1006_);
if (v___x_1008_ == 0)
{
uint8_t v___x_1009_; 
v___x_1009_ = 1;
return v___x_1009_;
}
else
{
uint8_t v___x_1010_; 
v___x_1010_ = 0;
return v___x_1010_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_GitRepo_hasDiff___boxed(lean_object* v_repo_1011_, lean_object* v_a_1012_){
_start:
{
uint8_t v_res_1013_; lean_object* v_r_1014_; 
v_res_1013_ = l_Lake_GitRepo_hasDiff(v_repo_1011_);
v_r_1014_ = lean_box(v_res_1013_);
return v_r_1014_;
}
}
lean_object* runtime_initialize_Init_Data_ToString(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_Proc(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_TakeDrop(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Search(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_String(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Util_Git(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_ToString(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Util_Proc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Search(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Util_String(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_Util_Git(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_ToString(uint8_t builtin);
lean_object* initialize_Lake_Util_Proc(uint8_t builtin);
lean_object* initialize_Init_Data_String_TakeDrop(uint8_t builtin);
lean_object* initialize_Init_Data_String_Search(uint8_t builtin);
lean_object* initialize_Lake_Util_String(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Util_Git(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_ToString(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_Proc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Search(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_String(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Util_Git(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_Util_Git(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_Util_Git(builtin);
}
#ifdef __cplusplus
}
#endif
