package controller;

import model.beans.Prodotto;
import model.beans.Utente;
import model.beans.WishList;
import model.dao.ProdottoDAO;
import model.dao.WishListDAO;

import javax.servlet.*;
import javax.servlet.http.*;
import javax.servlet.annotation.*;
import java.io.IOException;
import java.sql.SQLException;

@WebServlet(name = "WishlistServlet", value = "/WishlistServlet")
public class WishlistServlet extends HttpServlet {
    @Override
    protected void doGet(HttpServletRequest request, HttpServletResponse response) throws ServletException, IOException {
        //aggiungo alla wishlist
        if(Integer.parseInt(request.getParameter("cod")) == 1){

            if(request.getSession().getAttribute("user") == null){
                response.sendRedirect( request.getServletContext().getContextPath()+"/login.jsp");
                return;
            }

            try {
                WishListDAO dao = new WishListDAO();
                int p = Integer.parseInt(request.getParameter("prodotto"));
                ProdottoDAO dao2 = new ProdottoDAO();
                Prodotto prodotto = dao2.getProdottoById(p);
                Utente u = (Utente)request.getSession().getAttribute("user");
                dao.addToWishList(u, prodotto);
                response.sendRedirect( request.getServletContext().getContextPath()+"/landingpage");

            } catch (SQLException throwables) {
                throwables.printStackTrace();
            }
        }
        //ottengo la wishlist
        else if(Integer.parseInt(request.getParameter("cod")) == 2){
            try {
                WishListDAO dao = new WishListDAO();
                Utente u = (Utente)request.getSession().getAttribute("user");
                WishList w = dao.getWishListByUser(u);
                request.setAttribute("wishlist", w);

                String address = "/wishlist.jsp";
                RequestDispatcher dispatcher = request.getRequestDispatcher(address);
                dispatcher.forward(request, response);

            } catch (SQLException throwables) {
                throwables.printStackTrace();
            }

        }
        //elimino dalla wishlist
        else if(Integer.parseInt(request.getParameter("cod")) == 3){
            try{
                WishListDAO dao = new WishListDAO();
                int id_utente = Integer.parseInt(request.getParameter("id_utente"));
                int id_prodotto = Integer.parseInt(request.getParameter("id_prodotto"));
                dao.removeFromWishList(id_utente, id_prodotto);
            } catch(SQLException throwables){
                throwables.printStackTrace();
            }
        }



    }

    @Override
    protected void doPost(HttpServletRequest request, HttpServletResponse response) throws ServletException, IOException {
        doGet(request, response);
    }
}
