import Bf.Canons.DeadLoops
import Bf.Canons.Segments
import Bf.Canons.FirstSegment
import Bf.Canons.LastSegment
import Bf.Canons.Mirror

namespace Bf

def Canon.norm : Canon := deadLoops.comp (segments.comp (firstSeg.comp lastSeg))

def Canon.all : Canon := norm.comp mirror

end Bf
