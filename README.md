# Rush

A compiled language: Go-style single binaries, Haskell-style types, Rust-style ownership, Ruby-style syntax.
Design: `docs/superpowers/specs/2026-09-17-rush-stage1-design.md`.

## Taste

```ruby
enum Shape
  Circle(Float)
  Rect(Float, Float)
end

trait Area
  def area(&self) -> Float
  def describe(&self) -> String
    "area #{self.area}"
  end
end

impl Area for Shape
  def area(&self)
    case self
    in Circle(r) then 3.14159 * r * r
    in Rect(w, h) then w * h
    end
  end
end

def unwrap_or[T](o: Option[T], default: T) -> T
  case o
  in Some(v) then v
  in None then default
  end
end

def main
  puts(&Rect(2.0, 3.0).describe)
  puts("#{unwrap_or(Some(3), 0)} #{Some("x")}")
end
```

Values are owned and moved; borrows are explicit for named variables and automatic for
method receivers and temporaries; heap data is freed by compiler-inserted drops; `Gc[T]`
opts a value into the collector.

```ruby
struct Person
  derive Show, Eq, Clone
  name: String
  age: Int
end

impl Person
  def birthday(&mut self)
    @age += 1
  end
end

def main
  let mut p = Person { name: "Ann", age: 30 }
  p.birthday
  let q = p.clone
  let r = p                 # p is moved; using it again is a compile error
  puts("#{q == r} #{q}")    # true Person { name: "Ann", age: 31 }
  let shared = Gc.new(q)
  puts("#{shared.borrow.age}")
end
```

Borrows are checked: a place has one live `&mut` or any number of live `&`, and a borrow
ends at its last use. A function returning a reference borrows from `self` or its one
reference parameter.

```ruby
impl Person
  def name_ref(&self) -> &String   # the result borrows self
    &@name
  end
  def set_age(&mut self, a: Int)
    @age = a
  end
end

def main
  let mut p = Person { name: "Ann", age: 30 }
  let n = p.name_ref
  puts(n)                   # Ann
  p.set_age(p.age + 1)      # fine: n is dead, and the receiver is borrowed after the argument
  let r = &mut p
  # puts(&p.name)           # error: cannot borrow `p.name` as shared because it is mutably borrowed
  r.set_age(40)
  puts("#{p}")              # Person { name: "Ann", age: 40 }
end
```

## Build

    export PATH="$HOME/.cargo/bin:$PATH"   # Git Bash on Windows
    cargo build --release

Needs a C compiler on PATH (`cc`, `gcc`, `clang`, `tcc`, or `zig cc`) or `RUSH_CC="path/to/cc"`.

## Use

    rush build hello.rush     # writes hello(.exe) next to the source
    rush run hello.rush       # build and run
    rush build hello.rush --debug

## Test

    cargo test
