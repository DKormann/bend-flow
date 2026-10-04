declare module "bend-infrastructure" {
  export type Span = { src: string; beg: number; end: number };
  export type Book = { hols: number; order: string[]; tlds: Record<string, any>; ctrs: Record<string, any> };
  export type LTerm = any;
  export type HTerm = any;
  export type Err = { $: "Err"; bok: Book; exp: any; obs?: any; ctx: any; def?: string; spn?: Span; nte?: string };
  export function book_nil(): Book;
  export function book_load(book: Book, file: string, namespace: string, seen: Map<string, string | null>, span?: Span): Promise<number>;
  export function book_valid(book: Book, done?: number): void;
  export function err_show(error: Err): string;
  export function term_lower(term: HTerm, depth?: number): LTerm;
  export function term_show(term: LTerm): string;
}
