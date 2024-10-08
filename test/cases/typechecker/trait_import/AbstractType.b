module AbstractType

interface {
    type Abstr : Copy+Drop;
}

extern type Abstr : Move+Copy+Default+Drop;
