package model.dao;

import model.beans.Utente;
import org.openjdk.jmh.annotations.*;
import org.openjdk.jmh.infra.Blackhole;

import java.sql.SQLException;
import java.util.concurrent.TimeUnit;

@State(Scope.Thread)
@BenchmarkMode(Mode.AverageTime)
@OutputTimeUnit(TimeUnit.MILLISECONDS)
@Warmup(iterations = 5, time = 1)
@Measurement(iterations = 5, time = 1)
@Fork(1)
public class WishListDAOBenchmark {

    private WishListDAO wishListDAO;

    @Setup(Level.Trial)
    public void setup() {
        wishListDAO = new WishListDAO();
    }

    @Benchmark
    public void benchmarkGetWishListWithNullUtente(Blackhole bh) {
        try {
            wishListDAO.getWishListByUser(null);
        } catch (IllegalArgumentException e) {
            bh.consume(e);
        } catch (SQLException e) {
            bh.consume(e);
        }
    }
    
    @Benchmark
    public void benchmarkGetWishListWithInvalidUtente(Blackhole bh) {
         try {
             Utente u = new Utente();
             u.setId(-1);
             wishListDAO.getWishListByUser(u);
         } catch (IllegalArgumentException e) {
             bh.consume(e);
         } catch (SQLException e) {
             bh.consume(e);
         }
     }
}
